-- Prove2me | solution 1 for LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/098a7c61-c4ff-59cc-b39c-3eb41bdd4b40

import Mathlib
import Theorems.Thm_Complex_contDiffOn_infty_of_differentiableOn_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc

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
      refine ContinuousOn.add (f := fun t : ℝ => (t : ℂ) • (w' ((t : ℂ) • x) x))
        (g := fun t : ℝ => (1 : ℂ) • w ((t : ℂ) • x)) ?_ ?_
      · exact ContinuousOn.smul (f := fun t : ℝ => (t : ℂ)) (g := fun t : ℝ => w' ((t : ℂ) • x) x)
          Complex.continuous_ofReal.continuousOn
          ((continuousOn_comp_path hw'c hx).clm_apply continuousOn_const)
      · exact (continuousOn_comp_path hwc hx).const_smul (1 : ℂ)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  rw [hI] at h
  exact h

end poincare

section main

variable {F : E → E → E} {ρ : ℝ}

theorem exists_ball_norm_le {X : Type*} [NormedAddCommGroup X] {f : E → X} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (ball (0 : E) r)) :
    ∃ R : ℝ, 0 < R ∧ R ≤ r ∧ ∀ u ∈ ball (0 : E) R, ‖f u‖ ≤ ‖f 0‖ + 1 := by
  have hc : ContinuousAt f 0 := hf.continuousAt (ball_mem_nhds _ hr)
  have hev : ∀ᶠ u in 𝓝 (0 : E), f u ∈ ball (f 0) 1 := hc.preimage_mem_nhds (ball_mem_nhds _ one_pos)
  obtain ⟨R, hR, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min R r, lt_min hR hr, min_le_right _ _, fun u hu => ?_⟩
  have h := hb u (ball_subset_ball (min_le_left _ _) hu)
  rw [mem_ball, dist_eq_norm] at h
  calc ‖f u‖ = ‖(f u - f 0) + f 0‖ := by abel_nf
    _ ≤ ‖f u - f 0‖ + ‖f 0‖ := norm_add_le _ _
    _ ≤ ‖f 0‖ + 1 := by linarith

theorem exists_radius_mul_mem (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v) {T : Set E} (hT : T ∈ 𝓝 (0 : E)) :
    ∃ a : ℝ, 0 < a ∧ a ≤ ρ ∧ ∀ x y : E, x ∈ ball (0 : E) a → y ∈ ball (0 : E) a → F x y ∈ T := by
  have hc : ContinuousAt (uc F) ((0 : E), (0 : E)) :=
    (hasFDerivAt_uc hF2 (mem_S (zero_mem_ball hρ) (zero_mem_ball hρ))).continuousAt
  have h00 : uc F ((0 : E), (0 : E)) = 0 := by simp [hzero_left 0 (zero_mem_ball hρ)]
  rw [← h00] at hT
  have hev := hc.preimage_mem_nhds hT
  obtain ⟨a, ha, hb⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min a ρ, lt_min ha hρ, min_le_right _ _, fun x y hx hy => ?_⟩
  have hxy : ((x, y) : E × E) ∈ ball ((0 : E), (0 : E)) a := by
    have hx' := ball_subset_ball (min_le_left a ρ) hx
    have hy' := ball_subset_ball (min_le_left a ρ) hy
    rw [mem_ball_zero_iff] at hx' hy'
    rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt hx' hy'
  exact hb hxy

theorem core (hρ : 0 < ρ) (hF2 : ContDiffOn ℂ 2 (uc F) (S ρ))
    (hzero_left : ∀ v ∈ ball (0 : E) ρ, F 0 v = v)
    (hzero_right : ∀ v ∈ ball (0 : E) ρ, F v 0 = v)
    (hcomm : ∀ v w : E, v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ → F v w = F w v)
    (hassoc : ∀ u v w : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → w ∈ ball (0 : E) ρ →
      F u v ∈ ball (0 : E) ρ → F v w ∈ ball (0 : E) ρ → F (F u v) w = F u (F v w)) :
    ∃ (r : ℝ) (_ : 0 < r) (e : E → E),
      e 0 = 0 ∧
      DifferentiableOn ℂ e (ball (0 : E) r) ∧
      HasFDerivAt e (ContinuousLinearMap.id ℂ E) 0 ∧
      InjOn e (ball (0 : E) r) ∧
      MapsTo e (ball (0 : E) r) (ball (0 : E) ρ) ∧
      (∀ v w : E, v ∈ ball (0 : E) r → w ∈ ball (0 : E) r → v + w ∈ ball (0 : E) r →
        e (v + w) = F (e v) (e w)) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball (0 : E) δ, ∃ v ∈ ball (0 : E) r, e v = x) := by

  obtain ⟨r₀, hr₀p, hr₀, hunit⟩ := exists_radius_isUnit hρ hF2 hzero_left
  have hω := fun u (hu : u ∈ ball (0 : E) r₀) => hasFDerivAt_ω hF2 hr₀ hunit hu
  have hωc := continuousOn_ω hF2 hr₀ hunit
  have hω'c := continuousOn_ω' hF2 hr₀ hunit

  obtain ⟨R₁, hR₁p, hR₁, hb₁⟩ := exists_ball_norm_le (f := ω F) hr₀p hωc
  obtain ⟨R₂, hR₂p, hR₂, hb₂⟩ := exists_ball_norm_le (f := ω' F) hr₀p hω'c
  set R : ℝ := min R₁ R₂ with hRdef
  have hRp : 0 < R := lt_min hR₁p hR₂p
  have hRr₀ : R ≤ r₀ := le_trans (min_le_left _ _) hR₁
  have hRρ : R ≤ ρ := le_trans hRr₀ hr₀
  set C : ℝ := max (‖ω F 0‖ + 1) (‖ω' F 0‖ + 1) with hCdef
  have hbw : ∀ u ∈ ball (0 : E) R, ‖ω F u‖ ≤ C := fun u hu =>
    le_trans (hb₁ u (ball_subset_ball (min_le_left _ _) hu)) (le_max_left _ _)
  have hbw' : ∀ u ∈ ball (0 : E) R, ‖ω' F u‖ ≤ C := fun u hu =>
    le_trans (hb₂ u (ball_subset_ball (min_le_right _ _) hu)) (le_max_right _ _)
  have hsubR : ball (0 : E) R ⊆ ball (0 : E) r₀ := ball_subset_ball hRr₀

  set log : E → E := lineInt (ω F) with hlogdef
  have hlog : ∀ x ∈ ball (0 : E) R, HasFDerivAt log (ω F x) x := fun x hx =>
    hasFDerivAt_lineInt (fun u hu => hω u (hsubR hu)) (hωc.mono hsubR) (hω'c.mono hsubR) hbw hbw'
      (fun u hu a b => ω'_symm hρ hF2 hzero_left hzero_right hcomm hassoc hr₀p hr₀ hunit (hsubR hu) a b) hx
  have hlog0 : log 0 = 0 := lineInt_zero _

  obtain ⟨a, hap, haρ, hamul⟩ := exists_radius_mul_mem hρ hF2 hzero_left (ball_mem_nhds (0 : E) hRp)
  have haR : ∀ {x : E}, x ∈ ball (0 : E) (min a R) → x ∈ ball (0 : E) R := fun hx =>
    ball_subset_ball (min_le_right _ _) hx
  have haa : ∀ {x : E}, x ∈ ball (0 : E) (min a R) → x ∈ ball (0 : E) a := fun hx =>
    ball_subset_ball (min_le_left _ _) hx
  have hadd : ∀ x y : E, x ∈ ball (0 : E) (min a R) → y ∈ ball (0 : E) (min a R) →
      log (F x y) = log x + log y := by
    intro x y hx hy
    have hxρ : x ∈ ball (0 : E) ρ := ball_subset_ball hRρ (haR hx)

    have hderiv : ∀ z ∈ ball (0 : E) (min a R), HasFDerivAt (fun z => log (F x z) - log z) (0 : E →L[ℂ] E) z := by
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

  have hlogC1 : ContDiffOn ℂ 1 log (ball (0 : E) R) := by
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := 0) (f := log) isOpen_ball).mpr
      ⟨fun x hx => (hlog x hx).differentiableAt.differentiableWithinAt,
       fun h => absurd h (by simp),
       contDiffOn_zero.mpr ((hωc.mono hsubR).congr fun x hx => (hlog x hx).fderiv)⟩
    simpa using h
  have hlogCA : ContDiffAt ℂ 1 log 0 := hlogC1.contDiffAt (ball_mem_nhds _ hRp)
  have hf' : HasFDerivAt log ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) 0 := by
    have := hlog 0 (mem_ball_self hRp)
    rw [ω_zero hρ hF2 hzero_left, ContinuousLinearMap.one_def] at this
    simpa using this

  set H := hlogCA.toOpenPartialHomeomorph log hf' one_ne_zero with hHdef
  have hHcoe : (H : E → E) = log := rfl
  have h0s : (0 : E) ∈ H.source := hlogCA.mem_toOpenPartialHomeomorph_source hf' one_ne_zero
  have h0t : (0 : E) ∈ H.target := by
    have := hlogCA.image_mem_toOpenPartialHomeomorph_target hf' one_ne_zero
    rwa [hlog0] at this
  set e : E → E := ⇑H.symm with hedef
  have he_loc : hlogCA.localInverse hf' one_ne_zero = e := rfl
  have heC : ContDiffAt ℂ 1 e 0 := by
    have := hlogCA.to_localInverse hf' one_ne_zero
    rwa [hlog0, he_loc] at this
  have heD : HasFDerivAt e (ContinuousLinearMap.id ℂ E) 0 := by
    have := (hlogCA.hasStrictFDerivAt' hf' one_ne_zero).to_localInverse.hasFDerivAt
    rw [hlog0] at this
    simp at this
    exact this
  have he0 : e 0 = 0 := by
    have := H.left_inv h0s
    rwa [hHcoe, hlog0] at this

  obtain ⟨a', ha'p, -, ha'mul⟩ := exists_radius_mul_mem hρ hF2 hzero_left (H.open_source.mem_nhds h0s)
  set b : ℝ := min (min a R) a' with hbdef
  have hbp : 0 < b := lt_min (lt_min hap hRp) ha'p
  have hN : H.target ∩ {y | ContDiffAt ℂ 1 e y} ∩ e ⁻¹' ball (0 : E) b ∈ 𝓝 (0 : E) := by
    refine Filter.inter_mem (Filter.inter_mem (H.open_target.mem_nhds h0t) (heC.eventually (by simp))) ?_
    have hec : ContinuousAt e 0 := heC.continuousAt
    exact hec.preimage_mem_nhds (by rw [he0]; exact ball_mem_nhds _ hbp)
  obtain ⟨r, hrp, hrsub⟩ := Metric.mem_nhds_iff.mp hN
  have hrt : ∀ v ∈ ball (0 : E) r, v ∈ H.target := fun v hv => (hrsub hv).1.1
  have hrC : ∀ v ∈ ball (0 : E) r, ContDiffAt ℂ 1 e v := fun v hv => (hrsub hv).1.2
  have hrb : ∀ v ∈ ball (0 : E) r, e v ∈ ball (0 : E) b := fun v hv => (hrsub hv).2
  have hb1 : ∀ {u : E}, u ∈ ball (0 : E) b → u ∈ ball (0 : E) (min a R) := fun hu =>
    ball_subset_ball (min_le_left _ _) hu
  have hb2 : ∀ {u : E}, u ∈ ball (0 : E) b → u ∈ ball (0 : E) a' := fun hu =>
    ball_subset_ball (min_le_right _ _) hu
  have hloge : ∀ v ∈ ball (0 : E) r, log (e v) = v := fun v hv => by
    have := H.right_inv (hrt v hv); rwa [hHcoe] at this

  refine ⟨r, hrp, e, he0, ?_, heD, ?_, ?_, ?_, ?_⟩
  · exact fun v hv => ((hrC v hv).differentiableAt (by simp)).differentiableWithinAt
  · have : InjOn e H.target := by
      have := H.symm.injOn; rwa [OpenPartialHomeomorph.symm_source] at this
    exact this.mono fun v hv => hrt v hv
  · intro v hv
    exact ball_subset_ball (le_trans (le_trans (min_le_right _ _) hRρ) le_rfl) (hb1 (hrb v hv))
  · intro v w hv hw hvw
    have h1 : log (F (e v) (e w)) = log (e (v + w)) := by
      rw [hadd (e v) (e w) (hb1 (hrb v hv)) (hb1 (hrb w hw)), hloge v hv, hloge w hw, hloge _ hvw]
    have hs1 : F (e v) (e w) ∈ H.source := ha'mul _ _ (hb2 (hrb v hv)) (hb2 (hrb w hw))
    have hs2 : e (v + w) ∈ H.source := H.map_target (hrt _ hvw)
    rw [← hHcoe] at h1
    exact (H.injOn hs1 hs2 h1).symm
  · have hlc : ContinuousAt log 0 := (hlog 0 (mem_ball_self hRp)).continuousAt
    have hN' : H.source ∩ log ⁻¹' ball (0 : E) r ∈ 𝓝 (0 : E) :=
      Filter.inter_mem (H.open_source.mem_nhds h0s)
        (hlc.preimage_mem_nhds (by rw [hlog0]; exact ball_mem_nhds _ hrp))
    obtain ⟨δ, hδp, hδsub⟩ := Metric.mem_nhds_iff.mp hN'
    refine ⟨δ, hδp, fun x hx => ⟨log x, (hδsub hx).2, ?_⟩⟩
    have := H.left_inv (hδsub hx).1
    rwa [hHcoe] at this

end main

section glue

open scoped ContDiff

theorem contDiffOn_two_of_differentiableOn {g : ℕ} {ρ : ℝ} (F : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ))
    (hF : DifferentiableOn ℂ (fun p : (Fin g → ℂ) × (Fin g → ℂ) => F p.1 p.2)
      (Metric.ball (0 : Fin g → ℂ) ρ ×ˢ Metric.ball (0 : Fin g → ℂ) ρ)) :
    ContDiffOn ℂ 2 (uc F) (S ρ) := by

  have hrank : Module.finrank ℂ ((Fin g → ℂ) × (Fin g → ℂ)) = Module.finrank ℂ (Fin (g + g) → ℂ) := by
    simp [Module.finrank_prod]
  let Λ : ((Fin g → ℂ) × (Fin g → ℂ)) ≃L[ℂ] (Fin (g + g) → ℂ) := ContinuousLinearEquiv.ofFinrankEq hrank
  set U' : Set (Fin (g + g) → ℂ) := Λ.symm ⁻¹' (S ρ) with hU'
  have hU'open : IsOpen U' := (isOpen_S ρ).preimage Λ.symm.continuous
  have hf' : DifferentiableOn ℂ (uc F ∘ Λ.symm) U' :=
    DifferentiableOn.comp (hg := hF) Λ.symm.differentiableOn (fun u hu => hu)
  have hC : ContDiffOn ℂ ∞ (uc F ∘ Λ.symm) U' :=
    Complex.contDiffOn_infty_of_differentiableOn_pi hU'open hf'
  have hC2 : ContDiffOn ℂ 2 (uc F ∘ Λ.symm) U' := hC.of_le (WithTop.coe_le_coe.mpr le_top)
  have hback : ContDiffOn ℂ 2 ((uc F ∘ Λ.symm) ∘ Λ) (S ρ) :=
    hC2.comp Λ.contDiff.contDiffOn (fun p hp => by
      show Λ.symm (Λ p) ∈ S ρ
      rw [Λ.symm_apply_apply]; exact hp)
  refine hback.congr fun p hp => ?_
  simp [Function.comp]

end glue

end LocalGroupLawK3b
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b"

end
p2m_reactivate "P2MW.S_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc.LocalGroupLawK3b"

open LocalGroupLawK3b in
theorem solution
    {g : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (F : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ))
    (hF : DifferentiableOn ℂ (fun p : (Fin g → ℂ) × (Fin g → ℂ) => F p.1 p.2)
      (Metric.ball (0 : Fin g → ℂ) ρ ×ˢ Metric.ball (0 : Fin g → ℂ) ρ))
    (hzero_left : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) ρ, F 0 v = v)
    (hzero_right : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) ρ, F v 0 = v)
    (hcomm : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) ρ → w ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      F v w = F w v)
    (hassoc : ∀ u v w : Fin g → ℂ, u ∈ Metric.ball (0 : Fin g → ℂ) ρ → v ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      w ∈ Metric.ball (0 : Fin g → ℂ) ρ → F u v ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      F v w ∈ Metric.ball (0 : Fin g → ℂ) ρ → F (F u v) w = F u (F v w)) :
    ∃ (r : ℝ) (_ : 0 < r) (e : (Fin g → ℂ) → (Fin g → ℂ)),
      e 0 = 0 ∧
      DifferentiableOn ℂ e (Metric.ball (0 : Fin g → ℂ) r) ∧
      HasFDerivAt e (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
      Set.InjOn e (Metric.ball (0 : Fin g → ℂ) r) ∧
      Set.MapsTo e (Metric.ball (0 : Fin g → ℂ) r) (Metric.ball (0 : Fin g → ℂ) ρ) ∧
      (∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
        v + w ∈ Metric.ball (0 : Fin g → ℂ) r → e (v + w) = F (e v) (e w)) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.ball (0 : Fin g → ℂ) δ,
        ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, e v = x) :=
  core hρ (contDiffOn_two_of_differentiableOn F hF) hzero_left hzero_right hcomm hassoc

end S_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc
end P2MW
export P2MW.S_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc (solution)
