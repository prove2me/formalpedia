-- Prove2me | solution 1 for LocalGroupLaw.exists_localExp_family_of_differentiableOn_of_comm_of_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/198fe856-5a1b-5a8c-b833-9a8b0ac2f8d0

import Mathlib
import Theorems.Thm_Complex_contDiffOn_infty_of_differentiableOn_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Topology Filter Metric Set

noncomputable section

namespace LocalGroupLawK3b

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def S (ρ : ℝ) : Set (E × E) := ball (0 : E) ρ ×ˢ ball (0 : E) ρ

theorem isOpen_S (ρ : ℝ) : IsOpen (S (E := E) ρ) := isOpen_ball.prod isOpen_ball

theorem mem_S {ρ : ℝ} {x y : E} (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) :
    (x, y) ∈ S ρ := ⟨hx, hy⟩

def uc (F : E → E → E) : E × E → E := fun p => F p.1 p.2

@[scoped simp] theorem uc_apply (F : E → E → E) (x y : E) : uc F (x, y) = F x y := rfl

def D1 (F : E → E → E) : E × E → (E × E →L[ℂ] E) := fun p => fderiv ℂ (uc F) p

def D2 (F : E → E → E) : E × E → (E × E →L[ℂ] (E × E →L[ℂ] E)) := fun p => fderiv ℂ (D1 F) p

def P2 (F : E → E → E) (p : E × E) : E →L[ℂ] E := (D1 F p).comp (ContinuousLinearMap.inr ℂ E E)

def P1 (F : E → E → E) (p : E × E) : E →L[ℂ] E := (D1 F p).comp (ContinuousLinearMap.inl ℂ E E)

def Φ (F : E → E → E) (u : E) : E →L[ℂ] E := P2 F (u, 0)

def ω (F : E → E → E) (u : E) : E →L[ℂ] E := Ring.inverse (Φ F u)

def ω' (F : E → E → E) (u : E) : E →L[ℂ] (E →L[ℂ] E) := fderiv ℂ (ω F) u

section regularity

variable {F : E → E → E} {ρ : ℝ}

theorem two_eq : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num

theorem differentiableOn_uc (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) :
    DifferentiableOn ℂ (uc F) (S ρ) :=
  hF2.differentiableOn (by norm_num)

theorem hasFDerivAt_uc (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {p : E × E} (hp : p ∈ S ρ) :
    HasFDerivAt (uc F) (D1 F p) p :=
  ((differentiableOn_uc hF2).differentiableAt ((isOpen_S ρ).mem_nhds hp)).hasFDerivAt

theorem contDiffOn_D1 (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) : ContDiffOn ℂ 1 (D1 F) (S ρ) := by
  have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := 1) (f := uc F) (isOpen_S ρ)).1
    (by rw [← two_eq]; exact hF2)
  exact h.2.2

theorem hasFDerivAt_D1 (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {p : E × E} (hp : p ∈ S ρ) :
    HasFDerivAt (D1 F) (D2 F p) p :=
  (((contDiffOn_D1 hF2).differentiableOn one_ne_zero).differentiableAt
    ((isOpen_S ρ).mem_nhds hp)).hasFDerivAt

theorem continuousOn_D1 (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) : ContinuousOn (D1 F) (S ρ) :=
  (contDiffOn_D1 hF2).continuousOn

theorem hasFDerivAt_right (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {x y : E}
    (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) :
    HasFDerivAt (fun y' => F x y') (P2 F (x, y)) y := by
  have h := (hasFDerivAt_uc hF2 (mem_S hx hy)).comp y (hasFDerivAt_prodMk_right (𝕜 := ℂ) x y)
  exact h

theorem hasFDerivAt_left (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {x y : E}
    (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) :
    HasFDerivAt (fun x' => F x' y) (P1 F (x, y)) x := by
  have h := (hasFDerivAt_uc hF2 (mem_S hx hy)).comp x (hasFDerivAt_prodMk_left (𝕜 := ℂ) x y)
  exact h

theorem zero_mem_ball (hρ : 0 < ρ) : (0 : E) ∈ ball (0 : E) ρ := mem_ball_self hρ

theorem Φ_zero (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v) : Φ F 0 = 1 := by
  have h1 : HasFDerivAt (fun y' => F 0 y') (Φ F 0) 0 :=
    hasFDerivAt_right hF2 (zero_mem_ball hρ) (zero_mem_ball hρ)
  have h2 : HasFDerivAt (fun y' : E => y') (Φ F 0) 0 := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) hρ] with v hv
    exact (hzero_left v hv).symm
  have h3 : HasFDerivAt (fun y' : E => y') (ContinuousLinearMap.id ℂ E) 0 := hasFDerivAt_id 0
  exact (h3.unique h2).symm ▸ rfl

end regularity

section units

variable {F : E → E → E} {ρ : ℝ}

theorem contDiffOn_Φ (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) : ContDiffOn ℂ 1 (Φ F) (ball (0 : E) ρ) := by
  have h1 : ContDiffOn ℂ 1 (fun u : E => D1 F (u, 0)) (ball (0 : E) ρ) := by
    refine (contDiffOn_D1 hF2).comp (contDiffOn_id.prodMk contDiffOn_const) ?_
    intro u hu
    exact mem_S hu (by simpa using (lt_of_le_of_lt (norm_nonneg u) (mem_ball_zero_iff.mp hu)))
  exact h1.clm_comp contDiffOn_const

theorem continuousOn_Φ (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) : ContinuousOn (Φ F) (ball (0 : E) ρ) :=
  (contDiffOn_Φ hF2).continuousOn

theorem isUnit_of_norm_sub_one_lt {A : E →L[ℂ] E} (h : ‖A - 1‖ < 1) : IsUnit A := by
  have := (Units.oneSub (1 - A) (by rw [norm_sub_rev]; exact h)).isUnit
  simpa using this

theorem exists_radius_isUnit (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ ρ ∧ ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u) := by
  have hc : ContinuousAt (Φ F) 0 :=
    (continuousOn_Φ hF2).continuousAt (ball_mem_nhds (0 : E) hρ)
  have hev : ∀ᶠ u in 𝓝 (0 : E), ‖Φ F u - 1‖ < 1 := by
    have : ∀ᶠ u in 𝓝 (0 : E), Φ F u ∈ ball (Φ F 0) 1 := hc.preimage_mem_nhds (ball_mem_nhds _ one_pos)
    filter_upwards [this] with u hu
    rw [Φ_zero hρ hF2 hzero_left] at hu
    simpa [dist_eq_norm] using hu
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min r ρ, lt_min hr hρ, min_le_right _ _, fun u hu => ?_⟩
  exact isUnit_of_norm_sub_one_lt (hball u (ball_subset_ball (min_le_left _ _) hu))

theorem ω_mul_Φ {u : E} (hu : IsUnit (Φ F u)) : ω F u * Φ F u = 1 :=
  Ring.inverse_mul_cancel _ hu

theorem Φ_mul_ω {u : E} (hu : IsUnit (Φ F u)) : Φ F u * ω F u = 1 :=
  Ring.mul_inverse_cancel _ hu

theorem Φ_ω_apply {u : E} (hu : IsUnit (Φ F u)) (a : E) : Φ F u (ω F u a) = a := by
  have := congrArg (fun T : E →L[ℂ] E => T a) (Φ_mul_ω hu)
  simpa using this

theorem ω_Φ_apply {u : E} (hu : IsUnit (Φ F u)) (a : E) : ω F u (Φ F u a) = a := by
  have := congrArg (fun T : E →L[ℂ] E => T a) (ω_mul_Φ hu)
  simpa using this

theorem ω_zero (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v) : ω F 0 = 1 := by
  simp [ω, Φ_zero hρ hF2 hzero_left]

theorem contDiffOn_ω (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {r₀ : ℝ} (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) : ContDiffOn ℂ 1 (ω F) (ball (0 : E) r₀) := by
  intro u hu
  have hΦ : ContDiffAt ℂ 1 (Φ F) u :=
    (contDiffOn_Φ hF2).contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball hr₀ hu))
  have hinv : ContDiffAt ℂ 1 Ring.inverse (Φ F u) := by
    have := contDiffAt_ringInverse ℂ (n := 1) (hunit u hu).unit
    rwa [IsUnit.unit_spec] at this
  exact (hinv.comp u hΦ).contDiffWithinAt

theorem hasFDerivAt_ω (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {r₀ : ℝ} (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) {u : E} (hu : u ∈ ball (0 : E) r₀) :
    HasFDerivAt (ω F) (ω' F u) u :=
  (((contDiffOn_ω hF2 hr₀ hunit).differentiableOn one_ne_zero).differentiableAt
    (isOpen_ball.mem_nhds hu)).hasFDerivAt

theorem continuousOn_ω (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {r₀ : ℝ} (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) : ContinuousOn (ω F) (ball (0 : E) r₀) :=
  (contDiffOn_ω hF2 hr₀ hunit).continuousOn

theorem continuousOn_ω' (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {r₀ : ℝ} (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) : ContinuousOn (ω' F) (ball (0 : E) r₀) :=
  (contDiffOn_ω hF2 hr₀ hunit).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl

end units

section assoc

variable {F : E → E → E} {ρ : ℝ}

theorem P2_comp_Φ (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {x y : E} (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) (hxy : F x y ∈ ball (0 : E) ρ) :
    (P2 F (x, y)).comp (Φ F y) = Φ F (F x y) := by

  have hin : HasFDerivAt (fun z => F y z) (Φ F y) 0 := hasFDerivAt_right hF2 hy (zero_mem_ball hρ)
  have hout : HasFDerivAt (fun q => F x q) (P2 F (x, y)) (F y 0) := by
    rw [hzero_right y hy]; exact hasFDerivAt_right hF2 hx hy
  have hcomp : HasFDerivAt (fun z => F x (F y z)) ((P2 F (x, y)).comp (Φ F y)) 0 := hout.comp 0 hin

  have hleft : HasFDerivAt (fun z => F (F x y) z) (Φ F (F x y)) 0 :=
    hasFDerivAt_right hF2 hxy (zero_mem_ball hρ)

  have hev : ∀ᶠ z in 𝓝 (0 : E), F (F x y) z = F x (F y z) := by
    have h1 : ∀ᶠ z in 𝓝 (0 : E), z ∈ ball (0 : E) ρ := ball_mem_nhds _ hρ
    have h2 : ∀ᶠ z in 𝓝 (0 : E), F y z ∈ ball (0 : E) ρ := by
      have hc : ContinuousAt (fun z => F y z) 0 := hin.continuousAt
      have : F y 0 ∈ ball (0 : E) ρ := by rw [hzero_right y hy]; exact hy
      exact hc.preimage_mem_nhds (isOpen_ball.mem_nhds this)
    filter_upwards [h1, h2] with z hz hyz
    exact hassoc x y z hx hy hz hxy hyz
  have hleft' : HasFDerivAt (fun z => F x (F y z)) (Φ F (F x y)) 0 :=
    hleft.congr_of_eventuallyEq (hev.mono fun z hz => hz.symm)
  exact hcomp.unique hleft'

theorem ω_comp_P2 (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {x y : E} (hx : x ∈ ball (0 : E) ρ) (hy : y ∈ ball (0 : E) ρ) (hxy : F x y ∈ ball (0 : E) ρ)
    (huy : IsUnit (Φ F y)) (huxy : IsUnit (Φ F (F x y))) :
    (ω F (F x y)).comp (P2 F (x, y)) = ω F y := by
  have h := P2_comp_Φ hρ hF2 hzero_right hassoc hx hy hxy

  have h2 : P2 F (x, y) = (Φ F (F x y)).comp (ω F y) := by
    have := congrArg (fun T : E →L[ℂ] E => T.comp (ω F y)) h
    simp only [ContinuousLinearMap.comp_assoc] at this
    rw [show (Φ F y).comp (ω F y) = 1 from Φ_mul_ω huy] at this
    exact this
  rw [h2, ← ContinuousLinearMap.comp_assoc, show (ω F (F x y)).comp (Φ F (F x y)) = 1 from ω_mul_Φ huxy]
  simp [ContinuousLinearMap.one_def]

end assoc

section symmetry

variable {F : E → E → E} {ρ : ℝ}

def Ψr : (E × E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ E (E × E) E).flip (ContinuousLinearMap.inr ℂ E E)

def Ψl : (E × E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ E (E × E) E).flip (ContinuousLinearMap.inl ℂ E E)

@[scoped simp] theorem Ψr_apply (L : E × E →L[ℂ] E) : Ψr L = L.comp (ContinuousLinearMap.inr ℂ E E) := by
  simp [Ψr]

@[scoped simp] theorem Ψl_apply (L : E × E →L[ℂ] E) : Ψl L = L.comp (ContinuousLinearMap.inl ℂ E E) := by
  simp [Ψl]

theorem Φ_eq_Ψr (u : E) : Φ F u = Ψr (D1 F (u, 0)) := by simp [Φ, P2]

theorem P1_eq_Ψl (p : E × E) : P1 F p = Ψl (D1 F p) := by simp [P1]

theorem D2_symm (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) {p : E × E} (hp : p ∈ S ρ) (v w : E × E) :
    D2 F p v w = D2 F p w v := by
  have hf : ∀ᶠ q in 𝓝 p, HasFDerivAt (uc F) (D1 F q) q := by
    filter_upwards [(isOpen_S ρ).mem_nhds hp] with q hq
    exact hasFDerivAt_uc hF2 hq
  exact second_derivative_symmetric_of_eventually hf (hasFDerivAt_D1 hF2 hp) v w

theorem Φ_eq_P1 (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v)
    {u : E} (hu : u ∈ ball (0 : E) ρ) : Φ F u = P1 F (0, u) := by
  have h1 : HasFDerivAt (fun y => F u y) (Φ F u) 0 := hasFDerivAt_right hF2 hu (zero_mem_ball hρ)
  have h2 : HasFDerivAt (fun y => F y u) (P1 F (0, u)) 0 := hasFDerivAt_left hF2 (zero_mem_ball hρ) hu
  have h3 : HasFDerivAt (fun y => F y u) (Φ F u) 0 := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) hρ] with y hy
    exact (hcomm u y hu hy).symm
  exact h3.unique h2

theorem hasFDerivAt_Φ_zero (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ)) :
    HasFDerivAt (Φ F) (Ψr.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E))) 0 := by
  have hc : HasFDerivAt (fun u : E => D1 F (u, 0)) ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E)) 0 :=
    HasFDerivAt.comp (f := fun u : E => (u, (0 : E))) 0
      (hasFDerivAt_D1 hF2 (mem_S (zero_mem_ball hρ) (zero_mem_ball hρ)))
      (hasFDerivAt_prodMk_left (𝕜 := ℂ) (0 : E) (0 : E))
  have h := (Ψr (E := E)).hasFDerivAt.comp 0 hc
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  show Φ F u = Ψr (D1 F (u, 0))
  exact Φ_eq_Ψr u

theorem hasFDerivAt_Φ_zero' (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v) :
    HasFDerivAt (Φ F) (Ψl.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inr ℂ E E))) 0 := by
  have hc : HasFDerivAt (fun u : E => D1 F (0, u)) ((D2 F (0, 0)).comp (ContinuousLinearMap.inr ℂ E E)) 0 :=
    HasFDerivAt.comp (f := fun u : E => ((0 : E), u)) 0
      (hasFDerivAt_D1 hF2 (mem_S (zero_mem_ball hρ) (zero_mem_ball hρ)))
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) (0 : E) (0 : E))
  have h := (Ψl (E := E)).hasFDerivAt.comp 0 hc
  have h' : HasFDerivAt (fun u : E => P1 F (0, u))
      (Ψl.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inr ℂ E E))) 0 := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show P1 F (0, u) = Ψl (D1 F (0, u))
    exact P1_eq_Ψl (0, u)
  refine h'.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds (0 : E) hρ] with u hu
  exact Φ_eq_P1 hρ hF2 hcomm hu

theorem DΦ_zero_symm (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v) (a b : E) :
    (Ψr.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E))) a b =
      (Ψr.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E))) b a := by
  have heq := (hasFDerivAt_Φ_zero hρ hF2).unique (hasFDerivAt_Φ_zero' hρ hF2 hcomm)
  conv_lhs => rw [heq]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Ψr_apply, Ψl_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  exact D2_symm hF2 (mem_S (zero_mem_ball hρ) (zero_mem_ball hρ)) _ _

theorem hasFDerivAt_ω_zero (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v) :
    HasFDerivAt (ω F) ((-ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) 1 1).comp
      (Ψr.comp ((D2 F (0, 0)).comp (ContinuousLinearMap.inl ℂ E E)))) 0 := by
  have hinv : HasFDerivAt (Ring.inverse : (E →L[ℂ] E) → (E →L[ℂ] E))
      (-ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) 1 1) (Φ F 0) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℂ) (1 : (E →L[ℂ] E)ˣ)
    rw [Φ_zero hρ hF2 hzero_left]
    simpa using this
  exact hinv.comp 0 (hasFDerivAt_Φ_zero hρ hF2)

theorem ω'_zero_symm (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v)
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v)
    {r₀ : ℝ} (hr₀p : 0 < r₀) (hr₀ : r₀ ≤ ρ) (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u)) (a b : E) :
    ω' F 0 a b = ω' F 0 b a := by
  have heq := (hasFDerivAt_ω hF2 hr₀ hunit (zero_mem_ball hr₀p)).unique
    (hasFDerivAt_ω_zero hρ hF2 hzero_left)
  rw [heq]
  have hs := DΦ_zero_symm hρ hF2 hcomm a b
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, one_mul, mul_one] at hs ⊢
  rw [hs]

theorem key_identity (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {r₀ : ℝ} (hr₀p : 0 < r₀) (hr₀ : r₀ ≤ ρ) (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u))
    {x : E} (hx : x ∈ ball (0 : E) r₀) (a b : E) :
    ω F x (D2 F (x, 0) (0, a) (0, b)) + ω' F x (Φ F x a) (Φ F x b) = ω' F 0 a b := by
  have hxρ : x ∈ ball (0 : E) ρ := ball_subset_ball hr₀ hx

  have hω : HasFDerivAt (ω F) (ω' F x) (F x 0) := by
    rw [hzero_right x hxρ]; exact hasFDerivAt_ω hF2 hr₀ hunit hx
  have hc : HasFDerivAt (fun y => ω F (F x y)) ((ω' F x).comp (Φ F x)) 0 :=
    hω.comp 0 (hasFDerivAt_right hF2 hxρ (zero_mem_ball hρ))

  have hd0 : HasFDerivAt (fun y : E => D1 F (x, y)) ((D2 F (x, 0)).comp (ContinuousLinearMap.inr ℂ E E)) 0 :=
    HasFDerivAt.comp (f := fun y : E => (x, y)) 0
      (hasFDerivAt_D1 hF2 (mem_S hxρ (zero_mem_ball hρ)))
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) x (0 : E))
  have hd1 := (Ψr (E := E)).hasFDerivAt.comp 0 hd0
  have hd : HasFDerivAt (fun y : E => P2 F (x, y))
      (Ψr.comp ((D2 F (x, 0)).comp (ContinuousLinearMap.inr ℂ E E))) 0 := by
    refine hd1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    show P2 F (x, y) = Ψr (D1 F (x, y))
    simp [P2]

  have hG := hc.clm_comp hd

  have hev : ∀ᶠ y in 𝓝 (0 : E), (ω F (F x y)).comp (P2 F (x, y)) = ω F y := by
    have h1 : ∀ᶠ y in 𝓝 (0 : E), y ∈ ball (0 : E) r₀ := ball_mem_nhds _ hr₀p
    have h2 : ∀ᶠ y in 𝓝 (0 : E), F x y ∈ ball (0 : E) r₀ := by
      have hcont : ContinuousAt (fun y => F x y) 0 :=
        (hasFDerivAt_right hF2 hxρ (zero_mem_ball hρ)).continuousAt
      have : F x 0 ∈ ball (0 : E) r₀ := by rw [hzero_right x hxρ]; exact hx
      exact hcont.preimage_mem_nhds (isOpen_ball.mem_nhds this)
    filter_upwards [h1, h2] with y hy hxy
    exact ω_comp_P2 hρ hF2 hzero_right hassoc hxρ (ball_subset_ball hr₀ hy)
      (ball_subset_ball hr₀ hxy) (hunit y hy) (hunit _ hxy)
  have hG' : HasFDerivAt (fun y => (ω F (F x y)).comp (P2 F (x, y))) (ω' F 0) 0 :=
    (hasFDerivAt_ω hF2 hr₀ hunit (zero_mem_ball hr₀p)).congr_of_eventuallyEq hev
  have heq := hG.unique hG'
  have key := congrArg (fun T : E →L[ℂ] (E →L[ℂ] E) => T a b) heq
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, Ψr_apply,
    ContinuousLinearMap.inr_apply, hzero_right x hxρ] at key

  simpa [Φ] using key

theorem ω'_symm (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v)
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {r₀ : ℝ} (hr₀p : 0 < r₀) (hr₀ : r₀ ≤ ρ) (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u))
    {x : E} (hx : x ∈ ball (0 : E) r₀) (a b : E) :
    ω' F x a b = ω' F x b a := by
  have hxρ : x ∈ ball (0 : E) ρ := ball_subset_ball hr₀ hx

  have main : ∀ a₀ b₀ : E, ω' F x (Φ F x a₀) (Φ F x b₀) = ω' F x (Φ F x b₀) (Φ F x a₀) := by
    intro a₀ b₀
    have k1 := key_identity hρ hF2 hzero_right hassoc hr₀p hr₀ hunit hx a₀ b₀
    have k2 := key_identity hρ hF2 hzero_right hassoc hr₀p hr₀ hunit hx b₀ a₀
    have s1 : D2 F (x, 0) (0, a₀) (0, b₀) = D2 F (x, 0) (0, b₀) (0, a₀) :=
      D2_symm hF2 (mem_S hxρ (zero_mem_ball hρ)) _ _
    have s2 := ω'_zero_symm hρ hF2 hzero_left hcomm hr₀p hr₀ hunit a₀ b₀
    rw [s1, s2] at k1
    have e1 := eq_sub_of_add_eq' k1
    have e2 := eq_sub_of_add_eq' k2
    rw [e1, e2]
  have ha : Φ F x (ω F x a) = a := Φ_ω_apply (hunit x hx) a
  have hb : Φ F x (ω F x b) = b := Φ_ω_apply (hunit x hx) b
  have := main (ω F x a) (ω F x b)
  rwa [ha, hb] at this

end symmetry

section poincare

theorem seg_mem {R : ℝ} {y : E} (hy : y ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    (t : ℂ) • y ∈ ball (0 : E) R := by
  rw [mem_ball_zero_iff] at hy ⊢
  calc ‖(t : ℂ) • y‖ = |t| * ‖y‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * ‖y‖ := by gcongr
    _ < R := by simpa using hy

theorem abs_le_one_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |t| ≤ 1 :=
  abs_le.mpr ⟨by linarith [ht.1], ht.2⟩

theorem abs_le_one_of_mem_uIoc {t : ℝ} (ht : t ∈ uIoc (0 : ℝ) 1) : |t| ≤ 1 := by
  rw [uIoc_of_le zero_le_one] at ht
  exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩

def lineInt (w : E → (E →L[ℂ] E)) (x : E) : E := ∫ t in (0 : ℝ)..1, w ((t : ℂ) • x) x

theorem lineInt_zero (w : E → (E →L[ℂ] E)) : lineInt w 0 = 0 := by
  simp [lineInt]

def lineInt' (w : E → (E →L[ℂ] E)) (w' : E → (E →L[ℂ] (E →L[ℂ] E))) (y : E) (t : ℝ) : E →L[ℂ] E :=
  (w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E) +
    ((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y

theorem continuousOn_path (y : E) (s : Set ℝ) : ContinuousOn (fun t : ℝ => (t : ℂ) • y) s :=
  (Complex.continuous_ofReal.smul continuous_const).continuousOn

theorem mapsTo_path {R : ℝ} {y : E} (hy : y ∈ ball (0 : E) R) :
    MapsTo (fun t : ℝ => (t : ℂ) • y) (Icc (0 : ℝ) 1) (ball (0 : E) R) :=
  fun _ ht => seg_mem hy (abs_le_one_of_mem_Icc ht)

theorem continuousOn_comp_path {X : Type*} [TopologicalSpace X] {w : E → X} {R : ℝ}
    (hwc : ContinuousOn w (ball (0 : E) R)) {y : E} (hy : y ∈ ball (0 : E) R) :
    ContinuousOn (fun t : ℝ => w ((t : ℂ) • y)) (Icc (0 : ℝ) 1) :=
  hwc.comp (continuousOn_path y _) (mapsTo_path hy)

theorem continuousOn_lineInt_integrand {w : E → (E →L[ℂ] E)} {R : ℝ}
    (hwc : ContinuousOn w (ball (0 : E) R)) {y : E} (hy : y ∈ ball (0 : E) R) :
    ContinuousOn (fun t : ℝ => w ((t : ℂ) • y) y) (Icc (0 : ℝ) 1) :=
  (continuousOn_comp_path hwc hy).clm_apply continuousOn_const

theorem continuousOn_lineInt' {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))} {R : ℝ}
    (hwc : ContinuousOn w (ball (0 : E) R)) (hw'c : ContinuousOn w' (ball (0 : E) R))
    {y : E} (hy : y ∈ ball (0 : E) R) :
    ContinuousOn (lineInt' w w' y) (Icc (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun t : ℝ => (w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E)) (Icc (0 : ℝ) 1) :=
    (continuousOn_comp_path hwc hy).clm_comp continuousOn_const
  have h2 : ContinuousOn (fun t : ℝ => (w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E))
      (Icc (0 : ℝ) 1) :=
    (continuousOn_comp_path hw'c hy).clm_comp
      ((Complex.continuous_ofReal.smul continuous_const).continuousOn)
  have h3 : ContinuousOn (fun t : ℝ =>
      ((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y) (Icc (0 : ℝ) 1) := by
    have hflip : ContinuousOn (fun t : ℝ =>
        ((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip) (Icc (0 : ℝ) 1) :=
      (ContinuousLinearMap.flipₗᵢ ℂ E E E).continuous.comp_continuousOn h2
    exact hflip.clm_apply continuousOn_const
  exact h1.add h3

theorem hasFDerivAt_lineInt_integrand {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R : ℝ} (hw : ∀ u ∈ ball (0 : E) R, HasFDerivAt w (w' u) u)
    {y : E} (hy : y ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    HasFDerivAt (fun y' : E => w ((t : ℂ) • y') y') (lineInt' w w' y t) y := by
  have hpath : HasFDerivAt (fun y' : E => (t : ℂ) • y') ((t : ℂ) • ContinuousLinearMap.id ℂ E) y :=
    (hasFDerivAt_id y).const_smul (t : ℂ)
  have hc : HasFDerivAt (fun y' : E => w ((t : ℂ) • y'))
      ((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)) y :=
    HasFDerivAt.comp (f := fun y' : E => (t : ℂ) • y') y (hw _ (seg_mem hy ht)) hpath
  exact hc.clm_apply (hasFDerivAt_id y)

theorem norm_lineInt'_le {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R C : ℝ} (hbw : ∀ u ∈ ball (0 : E) R, ‖w u‖ ≤ C) (hbw' : ∀ u ∈ ball (0 : E) R, ‖w' u‖ ≤ C)
    {y : E} (hy : y ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    ‖lineInt' w w' y t‖ ≤ C + C * R := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbw y hy)
  have hmem := seg_mem hy ht
  have hyR : ‖y‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hy)
  have h1 : ‖(w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E)‖ ≤ C := by
    calc ‖(w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E)‖
        ≤ ‖w ((t : ℂ) • y)‖ * ‖ContinuousLinearMap.id ℂ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := by gcongr; exacts [hbw _ hmem, ContinuousLinearMap.norm_id_le]
      _ = C := mul_one C
  have ht1 : ‖(t : ℂ) • ContinuousLinearMap.id ℂ E‖ ≤ 1 := by
    calc ‖(t : ℂ) • ContinuousLinearMap.id ℂ E‖ = ‖(t : ℂ)‖ * ‖ContinuousLinearMap.id ℂ E‖ := norm_smul _ _
      _ ≤ 1 * 1 := by
          gcongr
          · rw [Complex.norm_real, Real.norm_eq_abs]; exact ht
          · exact ContinuousLinearMap.norm_id_le
      _ = 1 := one_mul 1
  have h2 : ‖((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y‖ ≤ C * R := by
    calc ‖((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y‖
        ≤ ‖((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip‖ * ‖y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)‖ * ‖y‖ := by
          rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖w' ((t : ℂ) • y)‖ * ‖(t : ℂ) • ContinuousLinearMap.id ℂ E‖) * ‖y‖ := by
          gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * 1) * R := by gcongr; exact hbw' _ hmem
      _ = C * R := by ring
  calc ‖lineInt' w w' y t‖ ≤ ‖(w ((t : ℂ) • y)).comp (ContinuousLinearMap.id ℂ E)‖ +
        ‖((w' ((t : ℂ) • y)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ E)).flip y‖ := norm_add_le _ _
    _ ≤ C + C * R := add_le_add h1 h2

theorem hasFDerivAt_lineInt_aux {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R C : ℝ} (hw : ∀ u ∈ ball (0 : E) R, HasFDerivAt w (w' u) u)
    (hwc : ContinuousOn w (ball (0 : E) R)) (hw'c : ContinuousOn w' (ball (0 : E) R))
    (hbw : ∀ u ∈ ball (0 : E) R, ‖w u‖ ≤ C) (hbw' : ∀ u ∈ ball (0 : E) R, ‖w' u‖ ≤ C)
    {x : E} (hx : x ∈ ball (0 : E) R) :
    HasFDerivAt (lineInt w) (∫ t in (0 : ℝ)..1, lineInt' w w' x t) x := by

  set ε : ℝ := R - ‖x‖ with hε
  have hεpos : 0 < ε := by have := mem_ball_zero_iff.mp hx; linarith
  have hsub : ball x ε ⊆ ball (0 : E) R := by
    intro y hy
    rw [mem_ball_zero_iff]
    have h1 : ‖y - x‖ < ε := by simpa [dist_eq_norm] using hy
    calc ‖y‖ = ‖(y - x) + x‖ := by abel_nf
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ < ε + ‖x‖ := by linarith
      _ = R := by simp [hε]
  have hs : ball x ε ∈ 𝓝 x := ball_mem_nhds x hεpos
  have hIcc : ∀ t ∈ uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht; rw [uIoc_of_le zero_le_one] at ht; exact ⟨le_of_lt ht.1, ht.2⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := MeasureTheory.volume) (F := fun y t => w ((t : ℂ) • y) y) (F' := lineInt' w w')
    (bound := fun _ => C + C * R) hs ?_ ?_ ?_ ?_ ?_ ?_
  ·
    filter_upwards [hs] with y hy
    exact ((continuousOn_lineInt_integrand hwc (hsub hy)).mono (fun t ht => hIcc t ht)).aestronglyMeasurable
      measurableSet_uIoc
  ·
    exact ((continuousOn_lineInt_integrand hwc hx).mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  ·
    exact ((continuousOn_lineInt' hwc hw'c hx).mono (fun t ht => hIcc t ht)).aestronglyMeasurable
      measurableSet_uIoc
  ·
    refine Filter.Eventually.of_forall fun t ht y hy => ?_
    exact norm_lineInt'_le hbw hbw' (hsub hy) (abs_le_one_of_mem_uIoc ht)
  · exact intervalIntegrable_const
  ·
    refine Filter.Eventually.of_forall fun t ht y hy => ?_
    exact hasFDerivAt_lineInt_integrand hw (hsub hy) (abs_le_one_of_mem_uIoc ht)

theorem hasDerivAt_primitive {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R : ℝ} (hw : ∀ u ∈ ball (0 : E) R, HasFDerivAt w (w' u) u)
    {x : E} (hx : x ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    HasDerivAt (fun s : ℝ => (s : ℂ) • w ((s : ℂ) • x))
      ((t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x)) t := by
  have hc : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hpath : HasDerivAt (fun s : ℝ => (s : ℂ) • x) x t := by
    simpa using hc.smul_const x
  have hwt : HasFDerivAt w ((w' ((t : ℂ) • x)).restrictScalars ℝ) ((t : ℂ) • x) :=
    (hw _ (seg_mem hx ht)).restrictScalars ℝ
  have hf : HasDerivAt (fun s : ℝ => w ((s : ℂ) • x)) (w' ((t : ℂ) • x) x) t := by
    have := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s : ℂ) • x) t hwt hpath
    simp at this
    exact this
  exact hc.smul hf

theorem lineInt'_eq_of_symm {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R : ℝ} (hsymm : ∀ u ∈ ball (0 : E) R, ∀ a b : E, w' u a b = w' u b a)
    {x : E} (hx : x ∈ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    lineInt' w w' x t = (t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x) := by
  ext a
  have hs := hsymm _ (seg_mem hx ht) a x
  simp only [lineInt', ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, one_smul, map_smul]
  rw [hs, add_comm]

theorem hasFDerivAt_lineInt {w : E → (E →L[ℂ] E)} {w' : E → (E →L[ℂ] (E →L[ℂ] E))}
    {R C : ℝ} (hw : ∀ u ∈ ball (0 : E) R, HasFDerivAt w (w' u) u)
    (hwc : ContinuousOn w (ball (0 : E) R)) (hw'c : ContinuousOn w' (ball (0 : E) R))
    (hbw : ∀ u ∈ ball (0 : E) R, ‖w u‖ ≤ C) (hbw' : ∀ u ∈ ball (0 : E) R, ‖w' u‖ ≤ C)
    (hsymm : ∀ u ∈ ball (0 : E) R, ∀ a b : E, w' u a b = w' u b a)
    {x : E} (hx : x ∈ ball (0 : E) R) :
    HasFDerivAt (lineInt w) (w x) x := by
  have h := hasFDerivAt_lineInt_aux hw hwc hw'c hbw hbw' hx
  have hI : ∫ t in (0 : ℝ)..1, lineInt' w w' x t = w x := by
    have hcongr : ∫ t in (0 : ℝ)..1, lineInt' w w' x t =
        ∫ t in (0 : ℝ)..1, ((t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      exact lineInt'_eq_of_symm hsymm hx (abs_le_one_of_mem_Icc ht)
    rw [hcongr]
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => (s : ℂ) • w ((s : ℂ) • x))
        ((t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact hasDerivAt_primitive hw hx (abs_le_one_of_mem_Icc ht)
    have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) • (w' ((t : ℂ) • x) x) + (1 : ℂ) • w ((t : ℂ) • x))
        MeasureTheory.volume 0 1 := by
      refine (ContinuousOn.intervalIntegrable ?_)
      rw [uIcc_of_le zero_le_one]
      refine ContinuousOn.fun_add ?_ ?_
      · exact Complex.continuous_ofReal.continuousOn.fun_smul
          ((continuousOn_comp_path hw'c hx).clm_apply continuousOn_const)
      · exact continuousOn_const.fun_smul (continuousOn_comp_path hwc hx)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  rw [hI] at h
  exact h

end poincare

section logadd

variable {F : E → E → E} {ρ : ℝ}

theorem log_add (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w))
    {r₀ : ℝ} (hr₀ : r₀ ≤ ρ) (hunit : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ F u))
    {R : ℝ} (hRp : 0 < R) (hRr₀ : R ≤ r₀)
    {log : E → E} (hlog : ∀ x ∈ ball (0 : E) R, HasFDerivAt log (ω F x) x) (hlog0 : log 0 = 0)
    {a : ℝ} (hap : 0 < a)
    (hamul : ∀ x y : E, x ∈ ball (0 : E) a → y ∈ ball (0 : E) a → F x y ∈ ball (0 : E) R)
    {x y : E} (hx : x ∈ ball (0 : E) (min a R)) (hy : y ∈ ball (0 : E) (min a R)) :
    log (F x y) = log x + log y := by
  have hRρ : R ≤ ρ := le_trans hRr₀ hr₀
  have hsubR : ball (0 : E) R ⊆ ball (0 : E) r₀ := ball_subset_ball hRr₀
  have haR : ∀ {x : E}, x ∈ ball (0 : E) (min a R) → x ∈ ball (0 : E) R := fun hx =>
    ball_subset_ball (min_le_right _ _) hx
  have haa : ∀ {x : E}, x ∈ ball (0 : E) (min a R) → x ∈ ball (0 : E) a := fun hx =>
    ball_subset_ball (min_le_left _ _) hx
  have hxρ : x ∈ ball (0 : E) ρ := ball_subset_ball hRρ (haR hx)
  have hderiv : ∀ z ∈ ball (0 : E) (min a R),
      HasFDerivAt (fun z => log (F x z) - log z) (0 : E →L[ℂ] E) z := by
    intro z hz
    have hzρ : z ∈ ball (0 : E) ρ := ball_subset_ball hRρ (haR hz)
    have hxz : F x z ∈ ball (0 : E) R := hamul x z (haa hx) (haa hz)
    have h1 : HasFDerivAt (fun z => log (F x z)) ((ω F (F x z)).comp (P2 F (x, z))) z :=
      HasFDerivAt.comp (f := fun z => F x z) z (hlog _ hxz) (hasFDerivAt_right hF2 hxρ hzρ)
    have h2 := h1.sub (hlog z (haR hz))
    rwa [ω_comp_P2 hρ hF2 hzero_right hassoc hxρ hzρ (ball_subset_ball hRρ hxz)
      (hunit z (hsubR (haR hz))) (hunit _ (hsubR hxz)), sub_self] at h2
  have hconst := (convex_ball (0 : E) (min a R)).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
    (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by
      rw [fderivWithin_of_isOpen isOpen_ball hz]
      exact (hderiv z hz).fderiv)
    hy (mem_ball_self (lt_min hap hRp))
  simp only [hzero_right x hxρ, hlog0, sub_zero] at hconst
  rw [← hconst]; abel

end logadd

end LocalGroupLawK3b
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b"

namespace LocalGroupLawB1

open LocalGroupLawK3b

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def F3 (F : P → E → E → E) : P × (E × E) → E := fun q => F q.1 q.2.1 q.2.2

def N (z₀ : P) (σ ρ : ℝ) : Set (P × (E × E)) := ball z₀ σ ×ˢ S ρ

theorem isOpen_N (z₀ : P) (σ ρ : ℝ) : IsOpen (N (E := E) z₀ σ ρ) := isOpen_ball.prod (isOpen_S ρ)

theorem exists_ball_norm_le' {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y] {f : X → Y} {x₀ : X}
    (hf : ContinuousAt f x₀) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ ball x₀ ε, ‖f x‖ ≤ ‖f x₀‖ + 1 := by
  have hev : ∀ᶠ x in 𝓝 x₀, f x ∈ ball (f x₀) 1 := hf.preimage_mem_nhds (ball_mem_nhds _ one_pos)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε, hε, fun x hx => ?_⟩
  have h := hb x hx
  rw [mem_ball, dist_eq_norm] at h
  calc ‖f x‖ = ‖(f x - f x₀) + f x₀‖ := by abel_nf
    _ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_add_le _ _
    _ ≤ ‖f x₀‖ + 1 := by linarith

theorem mem_ball_prod {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {x₀ x : X} {y₀ y : Y}
    {ε : ℝ} (hx : x ∈ ball x₀ ε) (hy : y ∈ ball y₀ ε) : ((x, y) : X × Y) ∈ ball ((x₀, y₀) : X × Y) ε := by
  rw [mem_ball, Prod.dist_eq]
  exact max_lt hx hy

theorem mem_ball_of_prod_left {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {x₀ x : X} {y₀ y : Y}
    {ε : ℝ} (h : ((x, y) : X × Y) ∈ ball ((x₀, y₀) : X × Y) ε) : x ∈ ball x₀ ε := by
  rw [mem_ball, Prod.dist_eq] at h; exact lt_of_le_of_lt (le_max_left _ _) h

theorem mem_ball_of_prod_right {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {x₀ x : X} {y₀ y : Y}
    {ε : ℝ} (h : ((x, y) : X × Y) ∈ ball ((x₀, y₀) : X × Y) ε) : y ∈ ball y₀ ε := by
  rw [mem_ball, Prod.dist_eq] at h; exact lt_of_le_of_lt (le_max_right _ _) h

section fibre

variable {F : P → E → E → E} {z₀ : P} {σ ρ : ℝ}

theorem contDiffOn_fibre (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {z : P} (hz : z ∈ ball z₀ σ) :
    ContDiffOn ℂ 2 (uc (F z)) (S ρ) := by
  have h : ContDiffOn ℂ 2 (F3 F ∘ fun p : E × E => (z, p)) (S ρ) :=
    hF3.comp (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => ⟨hz, hp⟩)
  exact h

theorem D1_fibre (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {z : P} (hz : z ∈ ball z₀ σ)
    {p : E × E} (hp : p ∈ S ρ) :
    D1 (F z) p = (fderiv ℂ (F3 F) (z, p)).comp (ContinuousLinearMap.inr ℂ P (E × E)) := by
  have h3 : HasFDerivAt (F3 F) (fderiv ℂ (F3 F) (z, p)) (z, p) :=
    ((hF3.differentiableOn (by norm_num)).differentiableAt ((isOpen_N z₀ σ ρ).mem_nhds ⟨hz, hp⟩)).hasFDerivAt
  have h : HasFDerivAt (uc (F z)) ((fderiv ℂ (F3 F) (z, p)).comp (ContinuousLinearMap.inr ℂ P (E × E))) p :=
    HasFDerivAt.comp (f := fun p : E × E => (z, p)) p h3 (hasFDerivAt_prodMk_right (𝕜 := ℂ) z p)
  exact h.fderiv

def Φt (F : P → E → E → E) (q : P × E) : E →L[ℂ] E := Φ (F q.1) q.2

def ωt (F : P → E → E → E) (q : P × E) : E →L[ℂ] E := ω (F q.1) q.2

def ωt' (F : P → E → E → E) (q : P × E) : E →L[ℂ] (E →L[ℂ] E) := ω' (F q.1) q.2

@[scoped simp] theorem Φt_apply (F : P → E → E → E) (z : P) (u : E) : Φt F (z, u) = Φ (F z) u := rfl
@[scoped simp] theorem ωt_apply (F : P → E → E → E) (z : P) (u : E) : ωt F (z, u) = ω (F z) u := rfl
@[scoped simp] theorem ωt'_apply (F : P → E → E → E) (z : P) (u : E) : ωt' F (z, u) = ω' (F z) u := rfl

theorem Φt_eq (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {q : P × E}
    (hq : q ∈ ball z₀ σ ×ˢ ball (0 : E) ρ) :
    Φt F q = Ψr ((fderiv ℂ (F3 F) (q.1, (q.2, 0))).comp (ContinuousLinearMap.inr ℂ P (E × E))) := by
  show Φ (F q.1) q.2 = _
  rw [Φ_eq_Ψr, D1_fibre hF3 hq.1 (mem_S hq.2 (zero_mem_ball hρ))]

theorem contDiffOn_Φt (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) :
    ContDiffOn ℂ 1 (Φt F) (ball z₀ σ ×ˢ ball (0 : E) ρ) := by
  have hD : ContDiffOn ℂ 1 (fderiv ℂ (F3 F)) (N z₀ σ ρ) :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := 1) (f := F3 F) (isOpen_N z₀ σ ρ)).1
      (by rw [← two_eq]; exact hF3)).2.2
  have hι : ContDiffOn ℂ 1 (fun q : P × E => (q.1, (q.2, (0 : E)))) (ball z₀ σ ×ˢ ball (0 : E) ρ) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const)
  have hmaps : MapsTo (fun q : P × E => (q.1, (q.2, (0 : E)))) (ball z₀ σ ×ˢ ball (0 : E) ρ) (N z₀ σ ρ) :=
    fun q hq => ⟨hq.1, mem_S hq.2 (zero_mem_ball hρ)⟩
  have h1 : ContDiffOn ℂ 1 (fun q : P × E => fderiv ℂ (F3 F) (q.1, (q.2, (0 : E)))) (ball z₀ σ ×ˢ ball (0 : E) ρ) :=
    hD.comp hι hmaps
  have h2 : ContDiffOn ℂ 1 (fun q : P × E =>
      Ψr ((fderiv ℂ (F3 F) (q.1, (q.2, (0 : E)))).comp (ContinuousLinearMap.inr ℂ P (E × E))))
      (ball z₀ σ ×ˢ ball (0 : E) ρ) :=
    (Ψr (E := E)).contDiff.comp_contDiffOn (h1.clm_comp contDiffOn_const)
  exact h2.congr (fun q hq => Φt_eq hρ hF3 hq)

theorem exists_uniform_units (hσ : 0 < σ) (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ))
    (hzero_left : ∀ z ∈ ball z₀ σ, ∀ v ∈ ball (0 : E) ρ, F z 0 v = v) :
    ∃ σ₁ r₀ : ℝ, 0 < σ₁ ∧ σ₁ ≤ σ ∧ 0 < r₀ ∧ r₀ ≤ ρ ∧
      ∀ z ∈ ball z₀ σ₁, ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u) := by
  have hc : ContinuousAt (Φt F) (z₀, 0) :=
    (contDiffOn_Φt hρ hF3).continuousOn.continuousAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hσ, mem_ball_self hρ⟩)
  have h0 : Φt F (z₀, 0) = 1 := by
    rw [Φt_apply]
    exact Φ_zero hρ (contDiffOn_fibre hF3 (mem_ball_self hσ)) (hzero_left z₀ (mem_ball_self hσ))
  have hev : ∀ᶠ q in 𝓝 ((z₀, (0 : E)) : P × E), ‖Φt F q - 1‖ < 1 := by
    have : ∀ᶠ q in 𝓝 ((z₀, (0 : E)) : P × E), Φt F q ∈ ball (Φt F (z₀, 0)) 1 :=
      hc.preimage_mem_nhds (ball_mem_nhds _ one_pos)
    filter_upwards [this] with q hq
    rw [h0] at hq
    simpa [dist_eq_norm] using hq
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min ε σ, min ε ρ, lt_min hε hσ, min_le_right _ _, lt_min hε hρ, min_le_right _ _,
    fun z hz u hu => ?_⟩
  have hq : ((z, u) : P × E) ∈ ball ((z₀, (0 : E)) : P × E) ε :=
    mem_ball_prod (ball_subset_ball (min_le_left _ _) hz) (ball_subset_ball (min_le_left _ _) hu)
  have hb' := hb _ hq
  rw [Φt_apply] at hb'
  exact isUnit_of_norm_sub_one_lt hb'

theorem contDiffOn_ωt (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {σ₁ r₀ : ℝ}
    (hσ₁ : σ₁ ≤ σ) (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ z ∈ ball z₀ σ₁, ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u)) :
    ContDiffOn ℂ 1 (ωt F) (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) := by
  intro q hq
  have hq' : q ∈ ball z₀ σ ×ˢ ball (0 : E) ρ := ⟨ball_subset_ball hσ₁ hq.1, ball_subset_ball hr₀ hq.2⟩
  have hΦ : ContDiffAt ℂ 1 (Φt F) q :=
    (contDiffOn_Φt hρ hF3).contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds hq')
  have hinv : ContDiffAt ℂ 1 Ring.inverse (Φt F q) := by
    have := contDiffAt_ringInverse ℂ (n := 1) (hunit q.1 hq.1 q.2 hq.2).unit
    rwa [IsUnit.unit_spec] at this
  exact (hinv.comp q hΦ).contDiffWithinAt

theorem ωt'_eq (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {σ₁ r₀ : ℝ}
    (hσ₁ : σ₁ ≤ σ) (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ z ∈ ball z₀ σ₁, ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u))
    {q : P × E} (hq : q ∈ ball z₀ σ₁ ×ˢ ball (0 : E) r₀) :
    ωt' F q = (fderiv ℂ (ωt F) q).comp (ContinuousLinearMap.inr ℂ P E) := by
  have hd : HasFDerivAt (ωt F) (fderiv ℂ (ωt F) q) q :=
    (((contDiffOn_ωt hρ hF3 hσ₁ hr₀ hunit).differentiableOn one_ne_zero).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hq)).hasFDerivAt
  have h : HasFDerivAt (ω (F q.1)) ((fderiv ℂ (ωt F) q).comp (ContinuousLinearMap.inr ℂ P E)) q.2 :=
    HasFDerivAt.comp (f := fun u : E => (q.1, u)) q.2 hd (hasFDerivAt_prodMk_right (𝕜 := ℂ) q.1 q.2)
  exact h.fderiv

theorem continuousOn_ωt' (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ)) {σ₁ r₀ : ℝ}
    (hσ₁ : σ₁ ≤ σ) (hr₀ : r₀ ≤ ρ)
    (hunit : ∀ z ∈ ball z₀ σ₁, ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u)) :
    ContinuousOn (ωt' F) (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) := by
  have h : ContinuousOn (fun q : P × E => (fderiv ℂ (ωt F) q).comp (ContinuousLinearMap.inr ℂ P E))
      (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) :=
    ((contDiffOn_ωt hρ hF3 hσ₁ hr₀ hunit).continuousOn_fderiv_of_isOpen (isOpen_ball.prod isOpen_ball)
      le_rfl).clm_comp continuousOn_const
  exact h.congr (fun q hq => ωt'_eq hρ hF3 hσ₁ hr₀ hunit hq)

end fibre
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b"

section paramlog

variable {z₀ : P} {σ₂ R : ℝ}

def πt (t : ℝ) : P × E →L[ℂ] P × E :=
  (ContinuousLinearMap.fst ℂ P E).prod (0 : P × E →L[ℂ] E) +
    (t : ℂ) • ((0 : P × E →L[ℂ] P).prod (ContinuousLinearMap.snd ℂ P E))

@[scoped simp] theorem πt_apply (t : ℝ) (q : P × E) : πt t q = (q.1, (t : ℂ) • q.2) := by
  simp [πt]

theorem continuous_πt : Continuous (fun t : ℝ => (πt t : P × E →L[ℂ] P × E)) :=
  continuous_const.add (Complex.continuous_ofReal.smul continuous_const)

theorem norm_πt_le {t : ℝ} (ht : |t| ≤ 1) : ‖(πt t : P × E →L[ℂ] P × E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun q => ?_)
  rw [πt_apply, one_mul, Prod.norm_def, Prod.norm_def]
  apply max_le_max le_rfl
  calc ‖(t : ℂ) • q.2‖ = |t| * ‖q.2‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * ‖q.2‖ := by gcongr
    _ = ‖q.2‖ := one_mul _

theorem norm_sndL_le : ‖(ContinuousLinearMap.snd ℂ P E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using norm_snd_le x)

theorem seg_mem_prod {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    ((q.1, (t : ℂ) • q.2) : P × E) ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R :=
  ⟨hq.1, seg_mem hq.2 ht⟩

def LOG (W : P × E → (E →L[ℂ] E)) (q : P × E) : E := lineInt (fun x => W (q.1, x)) q.2

theorem LOG_apply (W : P × E → (E →L[ℂ] E)) (z : P) (x : E) :
    LOG W (z, x) = lineInt (fun x => W (z, x)) x := rfl

def LOG' (W : P × E → (E →L[ℂ] E)) (W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))) (q : P × E) (t : ℝ) :
    P × E →L[ℂ] E :=
  (W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E) +
    ((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2

theorem continuousOn_path_prod (q : P × E) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => ((q.1, (t : ℂ) • q.2) : P × E)) s :=
  (continuous_const.prodMk (Complex.continuous_ofReal.smul continuous_const)).continuousOn

theorem continuousOn_comp_path_prod {X : Type*} [TopologicalSpace X] {W : P × E → X}
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    ContinuousOn (fun t : ℝ => W (q.1, (t : ℂ) • q.2)) (Icc (0 : ℝ) 1) :=
  hWc.comp (continuousOn_path_prod q _) (fun _ ht => seg_mem_prod hq (abs_le_one_of_mem_Icc ht))

theorem continuousOn_LOG_integrand {W : P × E → (E →L[ℂ] E)}
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    ContinuousOn (fun t : ℝ => W (q.1, (t : ℂ) • q.2) q.2) (Icc (0 : ℝ) 1) :=
  (continuousOn_comp_path_prod hWc hq).clm_apply continuousOn_const

theorem continuousOn_LOG' {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))}
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) (hW'c : ContinuousOn W' (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    ContinuousOn (LOG' W W' q) (Icc (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun t : ℝ => (W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E)) (Icc (0 : ℝ) 1) :=
    (continuousOn_comp_path_prod hWc hq).clm_comp continuousOn_const
  have h2 : ContinuousOn (fun t : ℝ => (W' (q.1, (t : ℂ) • q.2)).comp (πt t)) (Icc (0 : ℝ) 1) :=
    (continuousOn_comp_path_prod hW'c hq).clm_comp continuous_πt.continuousOn
  have h3 : ContinuousOn (fun t : ℝ => ((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2) (Icc (0 : ℝ) 1) :=
    ((ContinuousLinearMap.flipₗᵢ ℂ (P × E) E E).continuous.comp_continuousOn h2).clm_apply continuousOn_const
  exact h1.add h3

theorem hasFDerivAt_LOG_integrand {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))}
    (hWd : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, HasFDerivAt W (W' q) q)
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    HasFDerivAt (fun q' : P × E => W (q'.1, (t : ℂ) • q'.2) q'.2) (LOG' W W' q t) q := by
  have hpath : HasFDerivAt (fun q' : P × E => ((q'.1, (t : ℂ) • q'.2) : P × E)) (πt t) q := by
    have h := (hasFDerivAt_fst (𝕜 := ℂ) (p := q)).prodMk ((hasFDerivAt_snd (𝕜 := ℂ) (p := q)).const_smul (t : ℂ))
    refine h.congr_fderiv ?_
    ext q' <;> simp [πt]
  have hc : HasFDerivAt (fun q' : P × E => W (q'.1, (t : ℂ) • q'.2)) ((W' (q.1, (t : ℂ) • q.2)).comp (πt t)) q :=
    HasFDerivAt.comp (f := fun q' : P × E => ((q'.1, (t : ℂ) • q'.2) : P × E)) q (hWd _ (seg_mem_prod hq ht)) hpath
  exact hc.clm_apply (hasFDerivAt_snd (𝕜 := ℂ) (p := q))

theorem norm_LOG'_le {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))} {C : ℝ}
    (hbW : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W q‖ ≤ C)
    (hbW' : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W' q‖ ≤ C)
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) {t : ℝ} (ht : |t| ≤ 1) :
    ‖LOG' W W' q t‖ ≤ C + C * R := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbW q hq)
  have hmem := seg_mem_prod hq ht
  have hqR : ‖q.2‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hq.2)
  have h1 : ‖(W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E)‖ ≤ C := by
    calc ‖(W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E)‖
        ≤ ‖W (q.1, (t : ℂ) • q.2)‖ * ‖ContinuousLinearMap.snd ℂ P E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := by gcongr; exacts [hbW _ hmem, norm_sndL_le]
      _ = C := mul_one C
  have h2 : ‖((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2‖ ≤ C * R := by
    calc ‖((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2‖
        ≤ ‖((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip‖ * ‖q.2‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖(W' (q.1, (t : ℂ) • q.2)).comp (πt t)‖ * ‖q.2‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖W' (q.1, (t : ℂ) • q.2)‖ * ‖(πt t : P × E →L[ℂ] P × E)‖) * ‖q.2‖ := by
          gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * 1) * R := by gcongr; exacts [hbW' _ hmem, norm_πt_le ht]
      _ = C * R := by ring
  calc ‖LOG' W W' q t‖ ≤ ‖(W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E)‖ +
        ‖((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2‖ := norm_add_le _ _
    _ ≤ C + C * R := add_le_add h1 h2

theorem hasFDerivAt_LOG {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))} {C : ℝ}
    (hWd : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, HasFDerivAt W (W' q) q)
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) (hW'c : ContinuousOn W' (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    (hbW : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W q‖ ≤ C)
    (hbW' : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W' q‖ ≤ C)
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    HasFDerivAt (LOG W) (∫ t in (0 : ℝ)..1, LOG' W W' q t) q := by
  obtain ⟨ε, hεpos, hsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.prod isOpen_ball) q hq
  have hs : ball q ε ∈ 𝓝 q := ball_mem_nhds q hεpos
  have hIcc : ∀ t ∈ uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht; rw [uIoc_of_le zero_le_one] at ht; exact ⟨le_of_lt ht.1, ht.2⟩
  show HasFDerivAt (fun q' : P × E => ∫ t in (0 : ℝ)..1, W (q'.1, (t : ℂ) • q'.2) q'.2)
    (∫ t in (0 : ℝ)..1, LOG' W W' q t) q
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := MeasureTheory.volume) (F := fun (q' : P × E) t => W (q'.1, (t : ℂ) • q'.2) q'.2) (F' := LOG' W W')
    (bound := fun _ => C + C * R) hs ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs] with q' hq'
    exact ((continuousOn_LOG_integrand hWc (hsub hq')).mono (fun t ht => hIcc t ht)).aestronglyMeasurable
      measurableSet_uIoc
  · exact ((continuousOn_LOG_integrand hWc hq).mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  · exact ((continuousOn_LOG' hWc hW'c hq).mono (fun t ht => hIcc t ht)).aestronglyMeasurable measurableSet_uIoc
  · refine Filter.Eventually.of_forall fun t ht q' hq' => ?_
    exact norm_LOG'_le hbW hbW' (hsub hq') (abs_le_one_of_mem_uIoc ht)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht q' hq' => ?_
    exact hasFDerivAt_LOG_integrand hWd (hsub hq') (abs_le_one_of_mem_uIoc ht)

theorem continuousOn_LOG'_param {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))}
    (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R)) (hW'c : ContinuousOn W' (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    {t : ℝ} (ht : |t| ≤ 1) :
    ContinuousOn (fun q : P × E => LOG' W W' q t) (ball z₀ σ₂ ×ˢ ball (0 : E) R) := by
  have hp : ContinuousOn (fun q : P × E => ((q.1, (t : ℂ) • q.2) : P × E)) (ball z₀ σ₂ ×ˢ ball (0 : E) R) :=
    (continuous_fst.prodMk (continuous_snd.const_smul (t : ℂ))).continuousOn
  have hmaps : MapsTo (fun q : P × E => ((q.1, (t : ℂ) • q.2) : P × E)) (ball z₀ σ₂ ×ˢ ball (0 : E) R)
      (ball z₀ σ₂ ×ˢ ball (0 : E) R) := fun q hq => seg_mem_prod hq ht
  have h1 : ContinuousOn (fun q : P × E => (W (q.1, (t : ℂ) • q.2)).comp (ContinuousLinearMap.snd ℂ P E))
      (ball z₀ σ₂ ×ˢ ball (0 : E) R) := (hWc.comp hp hmaps).clm_comp continuousOn_const
  have h2 : ContinuousOn (fun q : P × E => (W' (q.1, (t : ℂ) • q.2)).comp (πt t))
      (ball z₀ σ₂ ×ˢ ball (0 : E) R) := (hW'c.comp hp hmaps).clm_comp continuousOn_const
  have h3 : ContinuousOn (fun q : P × E => ((W' (q.1, (t : ℂ) • q.2)).comp (πt t)).flip q.2)
      (ball z₀ σ₂ ×ˢ ball (0 : E) R) :=
    ((ContinuousLinearMap.flipₗᵢ ℂ (P × E) E E).continuous.comp_continuousOn h2).clm_apply
      continuous_snd.continuousOn
  exact h1.add h3

theorem continuousAt_LOG'_integral {W : P × E → (E →L[ℂ] E)} {W' : P × E → (P × E →L[ℂ] (E →L[ℂ] E))}
    {C : ℝ} (hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    (hW'c : ContinuousOn W' (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    (hbW : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W q‖ ≤ C)
    (hbW' : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W' q‖ ≤ C)
    {q : P × E} (hq : q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R) :
    ContinuousAt (fun q' : P × E => ∫ t in (0 : ℝ)..1, LOG' W W' q' t) q := by
  obtain ⟨ε, hεpos, hsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.prod isOpen_ball) q hq
  have hs : ball q ε ∈ 𝓝 q := ball_mem_nhds q hεpos
  have hIcc : ∀ t ∈ uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht; rw [uIoc_of_le zero_le_one] at ht; exact ⟨le_of_lt ht.1, ht.2⟩
  refine intervalIntegral.continuousAt_of_dominated_interval (μ := MeasureTheory.volume)
    (bound := fun _ => C + C * R) ?_ ?_ ?_ ?_
  · filter_upwards [hs] with q' hq'
    exact ((continuousOn_LOG' hWc hW'c (hsub hq')).mono (fun t ht => hIcc t ht)).aestronglyMeasurable
      measurableSet_uIoc
  · filter_upwards [hs] with q' hq'
    exact Filter.Eventually.of_forall fun t ht => norm_LOG'_le hbW hbW' (hsub hq') (abs_le_one_of_mem_uIoc ht)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    exact (continuousOn_LOG'_param hWc hW'c (abs_le_one_of_mem_uIoc ht)).continuousAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hq)

theorem contDiffOn_LOG {W : P × E → (E →L[ℂ] E)} {C : ℝ}
    (hW : ContDiffOn ℂ 1 W (ball z₀ σ₂ ×ˢ ball (0 : E) R))
    (hbW : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖W q‖ ≤ C)
    (hbW' : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, ‖fderiv ℂ W q‖ ≤ C) :
    ContDiffOn ℂ 1 (LOG W) (ball z₀ σ₂ ×ˢ ball (0 : E) R) := by
  have hO : IsOpen (ball z₀ σ₂ ×ˢ ball (0 : E) R) := isOpen_ball.prod isOpen_ball
  have hWd : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R, HasFDerivAt W (fderiv ℂ W q) q := fun q hq =>
    (((hW.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hq))).hasFDerivAt
  have hWc : ContinuousOn W (ball z₀ σ₂ ×ˢ ball (0 : E) R) := hW.continuousOn
  have hW'c : ContinuousOn (fderiv ℂ W) (ball z₀ σ₂ ×ˢ ball (0 : E) R) := hW.continuousOn_fderiv_of_isOpen hO le_rfl
  have hL : ∀ q ∈ ball z₀ σ₂ ×ˢ ball (0 : E) R,
      HasFDerivAt (LOG W) (∫ t in (0 : ℝ)..1, LOG' W (fderiv ℂ W) q t) q := fun q hq =>
    hasFDerivAt_LOG hWd hWc hW'c hbW hbW' hq
  have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := 0) (f := LOG W) hO).mpr
    ⟨fun q hq => (hL q hq).differentiableAt.differentiableWithinAt,
     fun h => absurd h (by simp),
     contDiffOn_zero.mpr (ContinuousOn.congr
       (fun q hq => (continuousAt_LOG'_integral hWc hW'c hbW hbW' hq).continuousWithinAt)
       (fun q hq => (hL q hq).fderiv))⟩
  simpa using h

end paramlog
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b"

section main

variable {F : P → E → E → E} {z₀ : P} {σ ρ : ℝ}

theorem mem_ball_prod' {q : P × E} {ε : ℝ} (h1 : q.1 ∈ ball z₀ ε) (h2 : q.2 ∈ ball (0 : E) ε) :
    q ∈ ball ((z₀, (0 : E)) : P × E) ε := by
  rw [mem_ball, Prod.dist_eq]; exact max_lt h1 h2

theorem snd_mem_ball {q : P × E} {ε : ℝ} (h : q ∈ ball ((z₀, (0 : E)) : P × E) ε) : q.2 ∈ ball (0 : E) ε := by
  rw [mem_ball, Prod.dist_eq] at h; exact lt_of_le_of_lt (le_max_right _ _) h

theorem fst_mem_ball {q : P × E} {ε : ℝ} (h : q ∈ ball ((z₀, (0 : E)) : P × E) ε) : q.1 ∈ ball z₀ ε := by
  rw [mem_ball, Prod.dist_eq] at h; exact lt_of_le_of_lt (le_max_left _ _) h

theorem exists_uniform_mul_mem (hσ : 0 < σ) (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ))
    (hzero_left : ∀ z ∈ ball z₀ σ, ∀ v ∈ ball (0 : E) ρ, F z 0 v = v) {T : Set E} (hT : T ∈ 𝓝 (0 : E)) :
    ∃ a : ℝ, 0 < a ∧ a ≤ σ ∧ a ≤ ρ ∧
      ∀ z ∈ ball z₀ a, ∀ x y : E, x ∈ ball (0 : E) a → y ∈ ball (0 : E) a → F z x y ∈ T := by
  have hc : ContinuousAt (F3 F) (z₀, ((0 : E), (0 : E))) :=
    hF3.continuousOn.continuousAt ((isOpen_N z₀ σ ρ).mem_nhds
      ⟨mem_ball_self hσ, mem_S (zero_mem_ball hρ) (zero_mem_ball hρ)⟩)
  have h00 : F3 F (z₀, ((0 : E), (0 : E))) = 0 := by
    show F z₀ 0 0 = 0
    exact hzero_left z₀ (mem_ball_self hσ) 0 (zero_mem_ball hρ)
  rw [← h00] at hT
  obtain ⟨a, ha, hb⟩ := Metric.mem_nhds_iff.mp (hc.preimage_mem_nhds hT)
  refine ⟨min a (min σ ρ), lt_min ha (lt_min hσ hρ), le_trans (min_le_right _ _) (min_le_left _ _),
    le_trans (min_le_right _ _) (min_le_right _ _), fun z hz x y hx hy => ?_⟩
  have hz' := ball_subset_ball (min_le_left a (min σ ρ)) hz
  have hx' := ball_subset_ball (min_le_left a (min σ ρ)) hx
  have hy' := ball_subset_ball (min_le_left a (min σ ρ)) hy
  have hmem : ((z, (x, y)) : P × (E × E)) ∈ ball ((z₀, ((0 : E), (0 : E))) : P × (E × E)) a :=
    mem_ball_prod hz' (mem_ball_prod hx' hy')
  exact hb hmem

def Lam (W : P × E → (E →L[ℂ] E)) (q : P × E) : P × E := (q.1, LOG W q)

@[scoped simp] theorem Lam_fst (W : P × E → (E →L[ℂ] E)) (q : P × E) : (Lam W q).1 = q.1 := rfl
@[scoped simp] theorem Lam_snd (W : P × E → (E →L[ℂ] E)) (q : P × E) : (Lam W q).2 = LOG W q := rfl

theorem coreB1 (hσ : 0 < σ) (hρ : 0 < ρ) (hF3 : ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ))
    (hzero_left : ∀ z ∈ ball z₀ σ, ∀ v ∈ ball (0 : E) ρ, F z 0 v = v)
    (hzero_right : ∀ z ∈ ball z₀ σ, ∀ v ∈ ball (0 : E) ρ, F z v 0 = v)
    (hcomm : ∀ z ∈ ball z₀ σ, ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F z v w = F z w v)
    (hassoc : ∀ z ∈ ball z₀ σ, ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ →
      w ∈ ball (0 : E) ρ → F z u v ∈ ball (0 : E) ρ → F z v w ∈ ball (0 : E) ρ →
      F z (F z u v) w = F z u (F z v w)) :
    ∃ (σ' r δ : ℝ) (e ℓ : P → E → E), 0 < σ' ∧ σ' ≤ σ ∧ 0 < r ∧ 0 < δ ∧
      DifferentiableOn ℂ (fun q : P × E => e q.1 q.2) (ball z₀ σ' ×ˢ ball (0 : E) r) ∧
      DifferentiableOn ℂ (fun q : P × E => ℓ q.1 q.2) (ball z₀ σ' ×ˢ ball (0 : E) δ) ∧
      ∀ z ∈ ball z₀ σ',
        e z 0 = 0 ∧
        HasFDerivAt (e z) (ContinuousLinearMap.id ℂ E) 0 ∧
        InjOn (e z) (ball (0 : E) r) ∧
        MapsTo (e z) (ball (0 : E) r) (ball (0 : E) ρ) ∧
        (∀ v w : E, v ∈ ball (0 : E) r → w ∈ ball (0 : E) r → v + w ∈ ball (0 : E) r →
          e z (v + w) = F z (e z v) (e z w)) ∧
        (∀ x ∈ ball (0 : E) δ, ∃ v ∈ ball (0 : E) r, e z v = x) ∧
        (∀ v ∈ ball (0 : E) r, ℓ z (e z v) = v) ∧
        (∀ x ∈ ball (0 : E) δ, ℓ z x ∈ ball (0 : E) r ∧ e z (ℓ z x) = x) := by

  obtain ⟨σ₁, r₀, hσ₁p, hσ₁, hr₀p, hr₀, hunit⟩ := exists_uniform_units hσ hρ hF3 hzero_left
  have hfib : ∀ z ∈ ball z₀ σ, ContDiffOn ℂ 2 (uc (F z)) (S ρ) := fun z hz => contDiffOn_fibre hF3 hz
  have hωt : ContDiffOn ℂ 1 (ωt F) (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) := contDiffOn_ωt hρ hF3 hσ₁ hr₀ hunit
  have hO₁ : IsOpen (ball z₀ σ₁ ×ˢ ball (0 : E) r₀) := isOpen_ball.prod isOpen_ball
  have h0mem : ((z₀, (0 : E)) : P × E) ∈ ball z₀ σ₁ ×ˢ ball (0 : E) r₀ := ⟨mem_ball_self hσ₁p, mem_ball_self hr₀p⟩

  obtain ⟨ε₁, hε₁, hb₁⟩ := exists_ball_norm_le' (f := ωt F) (hωt.continuousOn.continuousAt (hO₁.mem_nhds h0mem))
  obtain ⟨ε₂, hε₂, hb₂⟩ := exists_ball_norm_le' (f := fderiv ℂ (ωt F))
    ((hωt.continuousOn_fderiv_of_isOpen hO₁ le_rfl).continuousAt (hO₁.mem_nhds h0mem))
  obtain ⟨ε₃, hε₃, hb₃⟩ := exists_ball_norm_le' (f := ωt' F)
    ((continuousOn_ωt' hρ hF3 hσ₁ hr₀ hunit).continuousAt (hO₁.mem_nhds h0mem))
  set R : ℝ := min (min ε₁ (min ε₂ ε₃)) (min σ₁ r₀) with hRdef
  have hRp : 0 < R := lt_min (lt_min hε₁ (lt_min hε₂ hε₃)) (lt_min hσ₁p hr₀p)
  have hRσ₁ : R ≤ σ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hRr₀ : R ≤ r₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hRε₁ : R ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRε₂ : R ≤ ε₂ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRε₃ : R ≤ ε₃ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hRρ : R ≤ ρ := le_trans hRr₀ hr₀
  have hRσ : R ≤ σ := le_trans hRσ₁ hσ₁
  set C : ℝ := max (max (‖ωt F (z₀, 0)‖ + 1) (‖fderiv ℂ (ωt F) (z₀, 0)‖ + 1)) (‖ωt' F (z₀, 0)‖ + 1) with hCdef
  have hsubO : ball z₀ R ×ˢ ball (0 : E) R ⊆ ball z₀ σ₁ ×ˢ ball (0 : E) r₀ :=
    prod_mono (ball_subset_ball hRσ₁) (ball_subset_ball hRr₀)
  have hbW : ∀ q ∈ ball z₀ R ×ˢ ball (0 : E) R, ‖ωt F q‖ ≤ C := fun q hq =>
    le_trans (hb₁ q (mem_ball_prod' (ball_subset_ball hRε₁ hq.1) (ball_subset_ball hRε₁ hq.2)))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hbW' : ∀ q ∈ ball z₀ R ×ˢ ball (0 : E) R, ‖fderiv ℂ (ωt F) q‖ ≤ C := fun q hq =>
    le_trans (hb₂ q (mem_ball_prod' (ball_subset_ball hRε₂ hq.1) (ball_subset_ball hRε₂ hq.2)))
      (le_trans (le_max_right _ _) (le_max_left _ _))
  have hbω' : ∀ q ∈ ball z₀ R ×ˢ ball (0 : E) R, ‖ωt' F q‖ ≤ C := fun q hq =>
    le_trans (hb₃ q (mem_ball_prod' (ball_subset_ball hRε₃ hq.1) (ball_subset_ball hRε₃ hq.2))) (le_max_right _ _)

  have hO : IsOpen (ball z₀ R ×ˢ ball (0 : E) R) := isOpen_ball.prod isOpen_ball
  have h0O : ((z₀, (0 : E)) : P × E) ∈ ball z₀ R ×ˢ ball (0 : E) R := ⟨mem_ball_self hRp, mem_ball_self hRp⟩
  have hLOG : ContDiffOn ℂ 1 (LOG (ωt F)) (ball z₀ R ×ˢ ball (0 : E) R) := contDiffOn_LOG (hωt.mono hsubO) hbW hbW'
  have hLOG0 : ∀ z : P, LOG (ωt F) (z, 0) = 0 := fun z => lineInt_zero _

  have hlogfib : ∀ z ∈ ball z₀ R, ∀ x ∈ ball (0 : E) R,
      HasFDerivAt (fun x => LOG (ωt F) (z, x)) (ω (F z) x) x := by
    intro z hz x hx
    have hzσ₁ : z ∈ ball z₀ σ₁ := ball_subset_ball hRσ₁ hz
    have hzσ : z ∈ ball z₀ σ := ball_subset_ball hσ₁ hzσ₁
    have hunitz : ∀ u ∈ ball (0 : E) r₀, IsUnit (Φ (F z) u) := hunit z hzσ₁
    show HasFDerivAt (lineInt (ω (F z))) (ω (F z) x) x
    exact hasFDerivAt_lineInt (R := R) (C := C) (w' := ω' (F z))
      (fun u hu => hasFDerivAt_ω (hfib z hzσ) hr₀ hunitz (ball_subset_ball hRr₀ hu))
      ((continuousOn_ω (hfib z hzσ) hr₀ hunitz).mono (ball_subset_ball hRr₀))
      ((continuousOn_ω' (hfib z hzσ) hr₀ hunitz).mono (ball_subset_ball hRr₀))
      (fun u hu => hbW (z, u) ⟨hz, hu⟩) (fun u hu => hbω' (z, u) ⟨hz, hu⟩)
      (fun u hu a b => ω'_symm hρ (hfib z hzσ) (hzero_left z hzσ) (hzero_right z hzσ) (hcomm z hzσ)
        (hassoc z hzσ) hr₀p hr₀ hunitz (ball_subset_ball hRr₀ hu) a b) hx

  obtain ⟨a, hap, haσ, haρ, hamul⟩ := exists_uniform_mul_mem hσ hρ hF3 hzero_left (ball_mem_nhds (0 : E) hRp)
  have hadd : ∀ z ∈ ball z₀ (min a R), ∀ x y : E, x ∈ ball (0 : E) (min a R) → y ∈ ball (0 : E) (min a R) →
      LOG (ωt F) (z, F z x y) = LOG (ωt F) (z, x) + LOG (ωt F) (z, y) := by
    intro z hz x y hx hy
    have hzR : z ∈ ball z₀ R := ball_subset_ball (min_le_right _ _) hz
    have hza : z ∈ ball z₀ a := ball_subset_ball (min_le_left _ _) hz
    have hzσ₁ : z ∈ ball z₀ σ₁ := ball_subset_ball hRσ₁ hzR
    have hzσ : z ∈ ball z₀ σ := ball_subset_ball hσ₁ hzσ₁
    exact log_add hρ (hfib z hzσ) (hzero_right z hzσ) (hassoc z hzσ) hr₀ (hunit z hzσ₁) hRp hRr₀
      (log := fun x => LOG (ωt F) (z, x)) (hlogfib z hzR) (hLOG0 z) hap
      (fun x y hx hy => hamul z hza x y hx hy) hx hy

  have hΛC : ContDiffAt ℂ 1 (Lam (ωt F)) (z₀, 0) := by
    show ContDiffAt ℂ 1 (fun q : P × E => (q.1, LOG (ωt F) q)) (z₀, 0)
    exact contDiffAt_fst.prodMk (hLOG.contDiffAt (hO.mem_nhds h0O))
  set L' : P × E →L[ℂ] E := fderiv ℂ (LOG (ωt F)) (z₀, 0) with hL'def
  have hL' : HasFDerivAt (LOG (ωt F)) L' (z₀, 0) :=
    (((hLOG.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds h0O))).hasFDerivAt
  have hL'inr : L'.comp (ContinuousLinearMap.inr ℂ P E) = 1 := by
    have h1 : HasFDerivAt (fun x : E => LOG (ωt F) (z₀, x)) (L'.comp (ContinuousLinearMap.inr ℂ P E)) 0 :=
      HasFDerivAt.comp (f := fun x : E => ((z₀, x) : P × E)) 0 hL' (hasFDerivAt_prodMk_right (𝕜 := ℂ) z₀ (0 : E))
    have h2 := hlogfib z₀ (mem_ball_self hRp) 0 (mem_ball_self hRp)
    rw [ω_zero hρ (hfib z₀ (mem_ball_self hσ)) (hzero_left z₀ (mem_ball_self hσ))] at h2
    exact h1.unique h2
  let D : (P × E) ≃L[ℂ] (P × E) :=
    (ContinuousLinearEquiv.refl ℂ P).skewProd (ContinuousLinearEquiv.refl ℂ E) (L'.comp (ContinuousLinearMap.inl ℂ P E))
  have hΛD : HasFDerivAt (Lam (ωt F)) (D : P × E →L[ℂ] P × E) (z₀, 0) := by
    show HasFDerivAt (fun q : P × E => (q.1, LOG (ωt F) q)) (D : P × E →L[ℂ] P × E) (z₀, 0)
    have h := (hasFDerivAt_fst (𝕜 := ℂ) (p := ((z₀, (0 : E)) : P × E))).prodMk hL'
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    rintro ⟨ζ, k⟩
    have hsplit : L' (ζ, k) = L' (ζ, 0) + L' (0, k) := by
      rw [← L'.map_add]; simp
    have hk : L' (0, k) = k := by
      have := congrArg (fun T : E →L[ℂ] E => T k) hL'inr
      simpa using this
    simp [D, hsplit, hk, add_comm]
  set H := hΛC.toOpenPartialHomeomorph (Lam (ωt F)) hΛD one_ne_zero with hHdef
  have hHcoe : (H : P × E → P × E) = Lam (ωt F) := rfl
  have hΛ0 : Lam (ωt F) (z₀, 0) = (z₀, 0) := Prod.ext rfl (hLOG0 z₀)
  have h0s : ((z₀, (0 : E)) : P × E) ∈ H.source := hΛC.mem_toOpenPartialHomeomorph_source hΛD one_ne_zero
  have h0t : ((z₀, (0 : E)) : P × E) ∈ H.target := by
    have := hΛC.image_mem_toOpenPartialHomeomorph_target hΛD one_ne_zero
    rwa [hΛ0] at this
  have hsymmC : ContDiffAt ℂ 1 H.symm (z₀, 0) := by
    have := hΛC.to_localInverse hΛD one_ne_zero
    rwa [hΛ0] at this
  have hsymm0 : H.symm (z₀, 0) = (z₀, 0) := by
    have := H.left_inv h0s
    rwa [hHcoe, hΛ0] at this

  have K1 : ∀ q ∈ H.target, (H.symm q).1 = q.1 := fun q hq => by
    have h := H.right_inv hq
    rw [hHcoe] at h
    have h2 := congrArg Prod.fst h
    rwa [Lam_fst] at h2
  have K2 : ∀ (z : P) (y : E), ((z, y) : P × E) ∈ H.target → LOG (ωt F) (z, (H.symm (z, y)).2) = y := fun z y hq => by
    have h := H.right_inv hq
    rw [hHcoe] at h
    have h1 : H.symm (z, y) = (z, (H.symm (z, y)).2) := Prod.ext (K1 _ hq) rfl
    rw [h1] at h
    have h2 := congrArg Prod.snd h
    rwa [Lam_snd] at h2
  have K3 : ∀ (z : P) (x : E), ((z, x) : P × E) ∈ H.source → (H.symm (z, LOG (ωt F) (z, x))).2 = x := fun z x hp => by
    have h := H.left_inv hp
    rw [hHcoe] at h
    exact congrArg Prod.snd h

  obtain ⟨ε₅, hε₅, hsrc⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds h0s)
  obtain ⟨b, hbp, hbσ, hbρ, hbmul⟩ := exists_uniform_mul_mem hσ hρ hF3 hzero_left (ball_mem_nhds (0 : E) hε₅)
  set b' : ℝ := min b (min a R) with hb'def
  have hb'p : 0 < b' := lt_min hbp (lt_min hap hRp)
  have hN : H.target ∩ H.source ∩ {q : P × E | ContDiffAt ℂ 1 H.symm q} ∩
      H.symm ⁻¹' ball ((z₀, (0 : E)) : P × E) b' ∈ 𝓝 ((z₀, (0 : E)) : P × E) := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (H.open_target.mem_nhds h0t)
      (H.open_source.mem_nhds h0s)) (hsymmC.eventually (by simp))) ?_
    exact hsymmC.continuousAt.preimage_mem_nhds (by rw [hsymm0]; exact ball_mem_nhds _ hb'p)
  obtain ⟨ε₆, hε₆, hsub6⟩ := Metric.mem_nhds_iff.mp hN
  set r : ℝ := min ε₆ R with hrdef
  have hrp : 0 < r := lt_min hε₆ hRp
  have hΛpre : (Lam (ωt F)) ⁻¹' ball ((z₀, (0 : E)) : P × E) r ∈ 𝓝 ((z₀, (0 : E)) : P × E) :=
    hΛC.continuousAt.preimage_mem_nhds (by rw [hΛ0]; exact ball_mem_nhds _ hrp)
  obtain ⟨ε₇, hε₇, hsub7⟩ := Metric.mem_nhds_iff.mp hΛpre
  set σ' : ℝ := min (min ε₆ ε₇) (min (min b ε₅) (min a R)) with hσ'def
  have hσ'p : 0 < σ' := lt_min (lt_min hε₆ hε₇) (lt_min (lt_min hbp hε₅) (lt_min hap hRp))
  have hσ'ε₆ : σ' ≤ ε₆ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hσ'ε₇ : σ' ≤ ε₇ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hσ'b : σ' ≤ b := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hσ'ε₅ : σ' ≤ ε₅ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hσ'aR : σ' ≤ min a R := le_trans (min_le_right _ _) (min_le_right _ _)
  have hσ'R : σ' ≤ R := le_trans hσ'aR (min_le_right _ _)
  have hσ'σ : σ' ≤ σ := le_trans hσ'R hRσ
  set δ : ℝ := min ε₇ r with hδdef
  have hδp : 0 < δ := lt_min hε₇ hrp
  have hδr : δ ≤ r := min_le_right _ _

  have hT₀ : ∀ z ∈ ball z₀ σ', ∀ y ∈ ball (0 : E) r,
      ((z, y) : P × E) ∈ H.target ∧ ((z, y) : P × E) ∈ H.source ∧ ContDiffAt ℂ 1 H.symm (z, y) ∧
        H.symm (z, y) ∈ ball ((z₀, (0 : E)) : P × E) b' := by
    intro z hz y hy
    have hmem : ((z, y) : P × E) ∈ ball ((z₀, (0 : E)) : P × E) ε₆ :=
      mem_ball_prod (ball_subset_ball hσ'ε₆ hz) (ball_subset_ball (min_le_left _ _) hy)
    have h := hsub6 hmem
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have heb' : ∀ z ∈ ball z₀ σ', ∀ y ∈ ball (0 : E) r, (H.symm (z, y)).2 ∈ ball (0 : E) b' := fun z hz y hy =>
    snd_mem_ball (hT₀ z hz y hy).2.2.2

  refine ⟨σ', r, δ, fun z y => (H.symm (z, y)).2, fun z x => LOG (ωt F) (z, x), hσ'p, hσ'σ, hrp, hδp,
    ?_, ?_, fun z hz => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro q hq
    have hcd : ContDiffAt ℂ 1 H.symm q := by
      have := (hT₀ q.1 hq.1 q.2 hq.2).2.2.1
      simpa using this
    exact ((hcd.differentiableAt (by simp)).snd).differentiableWithinAt
  ·
    refine ((hLOG.differentiableOn one_ne_zero).mono ?_).congr (fun q hq => rfl)
    exact prod_mono (ball_subset_ball hσ'R) (ball_subset_ball (le_trans hδr (min_le_right _ _)))
  ·
    have := K3 z 0 (hT₀ z hz 0 (mem_ball_self hrp)).2.1
    rwa [hLOG0] at this
  ·
    have hzR : z ∈ ball z₀ R := ball_subset_ball hσ'R hz
    have he0 : (H.symm (z, 0)).2 = 0 := by
      have := K3 z 0 (hT₀ z hz 0 (mem_ball_self hrp)).2.1
      rwa [hLOG0] at this
    have hg : ContinuousAt (fun y : E => (H.symm (z, y)).2) 0 := by
      have h1 : ContinuousAt (fun y : E => H.symm (z, y)) 0 :=
        ContinuousAt.comp (hT₀ z hz 0 (mem_ball_self hrp)).2.2.1.continuousAt
          (continuous_const.prodMk continuous_id).continuousAt
      exact h1.snd
    have hf : HasFDerivAt (fun x : E => LOG (ωt F) (z, x))
        ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) ((fun y : E => (H.symm (z, y)).2) 0) := by
      show HasFDerivAt (fun x : E => LOG (ωt F) (z, x)) _ (H.symm (z, 0)).2
      rw [he0]
      have := hlogfib z hzR 0 (mem_ball_self hRp)
      rw [ω_zero hρ (hfib z (ball_subset_ball hRσ hzR)) (hzero_left z (ball_subset_ball hRσ hzR)),
        ContinuousLinearMap.one_def] at this
      simpa using this
    have hfg : ∀ᶠ y in 𝓝 (0 : E), LOG (ωt F) (z, (H.symm (z, y)).2) = y := by
      filter_upwards [ball_mem_nhds (0 : E) hrp] with y hy
      exact K2 z y (hT₀ z hz y hy).1
    have := HasFDerivAt.of_local_left_inverse hg hf hfg
    simpa using this
  ·
    intro y hy y' hy' h
    have h1 := K2 z y (hT₀ z hz y hy).1
    have h2 := K2 z y' (hT₀ z hz y' hy').1
    have h' : (H.symm (z, y)).2 = (H.symm (z, y')).2 := h
    rw [← h1, ← h2, h']
  ·
    intro y hy
    exact ball_subset_ball (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hRρ) (heb' z hz y hy)
  ·
    intro v w hv hw hvw
    show (H.symm (z, v + w)).2 = F z (H.symm (z, v)).2 (H.symm (z, w)).2
    have hzaR : z ∈ ball z₀ (min a R) := ball_subset_ball hσ'aR hz
    have hev : (H.symm (z, v)).2 ∈ ball (0 : E) (min a R) := ball_subset_ball (min_le_right _ _) (heb' z hz v hv)
    have hew : (H.symm (z, w)).2 ∈ ball (0 : E) (min a R) := ball_subset_ball (min_le_right _ _) (heb' z hz w hw)
    have h1 : LOG (ωt F) (z, F z (H.symm (z, v)).2 (H.symm (z, w)).2) = v + w := by
      rw [hadd z hzaR _ _ hev hew, K2 z v (hT₀ z hz v hv).1, K2 z w (hT₀ z hz w hw).1]
    have h2 : LOG (ωt F) (z, (H.symm (z, v + w)).2) = v + w := K2 z (v + w) (hT₀ z hz _ hvw).1
    have hs1 : ((z, F z (H.symm (z, v)).2 (H.symm (z, w)).2) : P × E) ∈ H.source := by
      apply hsrc
      exact mem_ball_prod (ball_subset_ball hσ'ε₅ hz)
        (hbmul z (ball_subset_ball hσ'b hz) _ _ (ball_subset_ball (min_le_left _ _) (heb' z hz v hv))
          (ball_subset_ball (min_le_left _ _) (heb' z hz w hw)))
    have hs2 : ((z, (H.symm (z, v + w)).2) : P × E) ∈ H.source := by
      have hm := H.map_target (hT₀ z hz _ hvw).1
      have h1' : H.symm (z, v + w) = (z, (H.symm (z, v + w)).2) := Prod.ext (K1 _ (hT₀ z hz _ hvw).1) rfl
      rwa [h1'] at hm
    have heq : H (z, F z (H.symm (z, v)).2 (H.symm (z, w)).2) = H (z, (H.symm (z, v + w)).2) := by
      rw [hHcoe]
      exact Prod.ext rfl (h1.trans h2.symm)
    exact (congrArg Prod.snd (H.injOn hs1 hs2 heq)).symm
  ·
    intro x hx
    have hmem7 : ((z, x) : P × E) ∈ ball ((z₀, (0 : E)) : P × E) ε₇ :=
      mem_ball_prod (ball_subset_ball hσ'ε₇ hz) (ball_subset_ball (min_le_left _ _) hx)
    have hΛr : Lam (ωt F) (z, x) ∈ ball ((z₀, (0 : E)) : P × E) r := hsub7 hmem7
    exact ⟨LOG (ωt F) (z, x), snd_mem_ball hΛr, K3 z x (hT₀ z hz x (ball_subset_ball hδr hx)).2.1⟩
  ·
    intro v hv
    exact K2 z v (hT₀ z hz v hv).1
  ·
    intro x hx
    have hmem7 : ((z, x) : P × E) ∈ ball ((z₀, (0 : E)) : P × E) ε₇ :=
      mem_ball_prod (ball_subset_ball hσ'ε₇ hz) (ball_subset_ball (min_le_left _ _) hx)
    have hΛr : Lam (ωt F) (z, x) ∈ ball ((z₀, (0 : E)) : P × E) r := hsub7 hmem7
    exact ⟨snd_mem_ball hΛr, K3 z x (hT₀ z hz x (ball_subset_ball hδr hx)).2.1⟩

end main
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b"

section glue

open scoped ContDiff

theorem contDiffOn_two_of_differentiableOn_family {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {z₀ : P} {σ ρ : ℝ} (F : P → E → E → E)
    (hF : DifferentiableOn ℂ (fun q : P × (E × E) => F q.1 q.2.1 q.2.2)
      (Metric.ball z₀ σ ×ˢ (Metric.ball (0 : E) ρ ×ˢ Metric.ball (0 : E) ρ))) :
    ContDiffOn ℂ 2 (F3 F) (N z₀ σ ρ) := by
  set n : ℕ := Module.finrank ℂ (P × (E × E)) with hn
  have hrank : Module.finrank ℂ (P × (E × E)) = Module.finrank ℂ (Fin n → ℂ) := by
    rw [Module.finrank_fin_fun]
  let Λ : (P × (E × E)) ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofFinrankEq hrank
  set U' : Set (Fin n → ℂ) := Λ.symm ⁻¹' (N z₀ σ ρ) with hU'
  have hU'open : IsOpen U' := (isOpen_N z₀ σ ρ).preimage Λ.symm.continuous
  have hf' : DifferentiableOn ℂ (F3 F ∘ Λ.symm) U' :=
    DifferentiableOn.comp (hg := hF) Λ.symm.differentiableOn (fun u hu => hu)
  have hC : ContDiffOn ℂ ∞ (F3 F ∘ Λ.symm) U' :=
    Complex.contDiffOn_infty_of_differentiableOn_pi hU'open hf'
  have hC2 : ContDiffOn ℂ 2 (F3 F ∘ Λ.symm) U' := hC.of_le (WithTop.coe_le_coe.mpr le_top)
  have hback : ContDiffOn ℂ 2 ((F3 F ∘ Λ.symm) ∘ Λ) (N z₀ σ ρ) :=
    hC2.comp Λ.contDiff.contDiffOn (fun p hp => by
      show Λ.symm (Λ p) ∈ N z₀ σ ρ
      rw [Λ.symm_apply_apply]; exact hp)
  refine hback.congr fun p hp => ?_
  simp [Function.comp]

end glue
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b"

end LocalGroupLawB1
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawB1"

end
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.LocalGroupLawB1"

open LocalGroupLawK3b LocalGroupLawB1 in
theorem solution
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (z₀ : P) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (F : P → E → E → E)
    (hF : DifferentiableOn ℂ (fun q : P × (E × E) => F q.1 q.2.1 q.2.2)
      (Metric.ball z₀ σ ×ˢ (Metric.ball (0 : E) ρ ×ˢ Metric.ball (0 : E) ρ)))
    (hzero_left : ∀ z ∈ Metric.ball z₀ σ, ∀ v ∈ Metric.ball (0 : E) ρ, F z 0 v = v)
    (hzero_right : ∀ z ∈ Metric.ball z₀ σ, ∀ v ∈ Metric.ball (0 : E) ρ, F z v 0 = v)
    (hcomm : ∀ z ∈ Metric.ball z₀ σ, ∀ v w : E, v ∈ Metric.ball (0 : E) ρ → w ∈ Metric.ball (0 : E) ρ →
      F z v w = F z w v)
    (hassoc : ∀ z ∈ Metric.ball z₀ σ, ∀ u v w : E, u ∈ Metric.ball (0 : E) ρ → v ∈ Metric.ball (0 : E) ρ →
      w ∈ Metric.ball (0 : E) ρ → F z u v ∈ Metric.ball (0 : E) ρ → F z v w ∈ Metric.ball (0 : E) ρ →
      F z (F z u v) w = F z u (F z v w)) :
    ∃ (σ' r δ : ℝ) (e ℓ : P → E → E), 0 < σ' ∧ σ' ≤ σ ∧ 0 < r ∧ 0 < δ ∧
      DifferentiableOn ℂ (fun q : P × E => e q.1 q.2) (Metric.ball z₀ σ' ×ˢ Metric.ball (0 : E) r) ∧
      DifferentiableOn ℂ (fun q : P × E => ℓ q.1 q.2) (Metric.ball z₀ σ' ×ˢ Metric.ball (0 : E) δ) ∧
      ∀ z ∈ Metric.ball z₀ σ',
        e z 0 = 0 ∧
        HasFDerivAt (e z) (ContinuousLinearMap.id ℂ E) 0 ∧
        Set.InjOn (e z) (Metric.ball (0 : E) r) ∧
        Set.MapsTo (e z) (Metric.ball (0 : E) r) (Metric.ball (0 : E) ρ) ∧
        (∀ v w : E, v ∈ Metric.ball (0 : E) r → w ∈ Metric.ball (0 : E) r → v + w ∈ Metric.ball (0 : E) r →
          e z (v + w) = F z (e z v) (e z w)) ∧
        (∀ x ∈ Metric.ball (0 : E) δ, ∃ v ∈ Metric.ball (0 : E) r, e z v = x) ∧
        (∀ v ∈ Metric.ball (0 : E) r, ℓ z (e z v) = v) ∧
        (∀ x ∈ Metric.ball (0 : E) δ, ℓ z x ∈ Metric.ball (0 : E) r ∧ e z (ℓ z x) = x) := by
  haveI : CompleteSpace P := FiniteDimensional.complete ℂ P
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  exact coreB1 hσ hρ (contDiffOn_two_of_differentiableOn_family F hF) hzero_left hzero_right hcomm hassoc

end S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc
end P2MW
export P2MW.S_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc (solution)
