-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_oneParameterDeriv
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:02:13.556058+00:00
-- url     : https://prove2.me/submissions/1f2af2a6-4592-4ac6-aae5-b3bdee578a07

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_MasulloGRH_elemSchwartz_continuous_of_seminorm_bound

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_oneParameterDeriv

open MasulloGRH
open scoped ContDiff

/-- A continuous homomorphism `ℝ → ℝ/ℤ` is `t ↦ t w mod ℤ`. -/
theorem exists_lift (c : ℝ →+ UnitAddCircle) (hc : Continuous c) :
    ∃ w : ℝ, ∀ t : ℝ, ((t * w : ℝ) : UnitAddCircle) = c t := by
  let q : ℝ → UnitAddCircle := (↑)
  have hq : IsCoveringMap q := AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    (⟨c, hc⟩ : C(ℝ, UnitAddCircle)) 0 0 (by simp [q])
  have hLift (t : ℝ) : q (L t) = c t := congrFun hL t
  have hAdd (s t : ℝ) : L (s + t) = L s + L t := by
    have hAgree : q ∘ (fun p : ℝ × ℝ ↦ L (p.1 + p.2)) =
        q ∘ (fun p : ℝ × ℝ ↦ L p.1 + L p.2) := by
      funext p
      change q (L (p.1 + p.2)) = ((L p.1 + L p.2 : ℝ) : UnitAddCircle)
      rw [AddCircle.coe_add]
      change q (L (p.1 + p.2)) = q (L p.1) + q (L p.2)
      simp only [hLift, map_add]
    exact congrFun (hq.eq_of_comp_eq (L.continuous.comp (continuous_fst.add continuous_snd))
      ((L.continuous.comp continuous_fst).add (L.continuous.comp continuous_snd))
      hAgree (0, 0) (by simp [hL0])) (s, t)
  let L' : ℝ →+ ℝ := { toFun := L, map_zero' := hL0, map_add' := hAdd }
  refine ⟨L 1, fun t => ?_⟩
  have hLinear : L t = t * L 1 := by
    have h := map_real_smul L' L.continuous t (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at h
    exact h
  rw [← hLinear]
  exact hLift t

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- Structure of a continuous one-parameter subgroup of `ℝ^m × 𝕋^n × ℤ^r × F`. -/
theorem flow_structure (ψ : ℝ →+ ElemGroup m n r s d) (hψ : Continuous ψ) :
    ∃ u : (Fin m → ℝ) × (Fin n → ℝ), ∀ t : ℝ,
      (ψ t).1 = t • u.1 ∧ (∀ j, (ψ t).2.1 j = ((t * u.2 j : ℝ) : UnitAddCircle)) ∧
        (ψ t).2.2 = 0 := by
  have h1 : ∀ t : ℝ, (ψ t).1 = t • (ψ 1).1 := by
    intro t
    have := map_real_smul ((AddMonoidHom.fst _ _).comp ψ) (continuous_fst.comp hψ) t (1 : ℝ)
    simpa using this
  have h2 : ∀ j : Fin n, ∃ w : ℝ, ∀ t : ℝ, ((t * w : ℝ) : UnitAddCircle) = (ψ t).2.1 j :=
    fun j => exists_lift ((Pi.evalAddMonoidHom _ j).comp
      ((AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp ψ)))
      ((continuous_apply j).comp (continuous_fst.comp (continuous_snd.comp hψ)))
  choose w hw using h2
  have h3 : ∀ t : ℝ, (ψ t).2.2 = 0 := by
    intro t
    have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℝ)
      (continuous_snd.comp (continuous_snd.comp hψ)) (x := t) (y := 0)
    simpa using this
  exact ⟨((ψ 1).1, w), fun t => ⟨h1 t, fun j => (hw j t).symm, h3 t⟩⟩

/-- The derivative along a one-parameter subgroup `ψ` of a function on the elementary group. -/
noncomputable def elemDeriv (ψ : ℝ →+ ElemGroup m n r s d) (g : ElemGroup m n r s d → ℂ) :
    ElemGroup m n r s d → ℂ :=
  fun y => deriv (fun t : ℝ => g (y + ψ t)) 0

theorem flow_line (ψ : ℝ →+ ElemGroup m n r s d) (u : (Fin m → ℝ) × (Fin n → ℝ))
    (hu : ∀ t : ℝ, (ψ t).1 = t • u.1 ∧
      (∀ j, (ψ t).2.1 j = ((t * u.2 j : ℝ) : UnitAddCircle)) ∧ (ψ t).2.2 = 0)
    (g : ElemGroup m n r s d → ℂ) (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i))
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (t : ℝ) :
    g ((p.1, fun j => ((p.2 j : ℝ) : UnitAddCircle), a, b) + ψ t) =
      elemLift g a b (p + t • u) := by
  obtain ⟨h1, h2, h3⟩ := hu t
  unfold elemLift
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [h1]
  · funext j
    simp [h2 j]
  · simp [h3]


section deriv

variable (ψ : ℝ →+ ElemGroup m n r s d) (u : (Fin m → ℝ) × (Fin n → ℝ))
    (hu : ∀ t : ℝ, (ψ t).1 = t • u.1 ∧
      (∀ j, (ψ t).2.1 j = ((t * u.2 j : ℝ) : UnitAddCircle)) ∧ (ψ t).2.2 = 0)
include hu

theorem line_hasDerivAt (g : ElemGroup m n r s d → ℂ)
    (hg : ∀ a b, ContDiff ℝ ∞ (elemLift g a b)) (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i))
    (p : (Fin m → ℝ) × (Fin n → ℝ)) :
    HasDerivAt (fun t : ℝ => g ((p.1, fun j => ((p.2 j : ℝ) : UnitAddCircle), a, b) + ψ t))
      (fderiv ℝ (elemLift g a b) p u) 0 := by
  have hfun : (fun t : ℝ => g ((p.1, fun j => ((p.2 j : ℝ) : UnitAddCircle), a, b) + ψ t)) =
      (elemLift g a b) ∘ (fun t : ℝ => p + t • u) := by
    funext t
    exact flow_line ψ u hu g a b p t
  rw [hfun]
  have hl : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
  have hF : HasFDerivAt (elemLift g a b) (fderiv ℝ (elemLift g a b) p) p :=
    (((hg a b).differentiable (by simp)) p).hasFDerivAt
  exact hF.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

theorem elemLift_elemDeriv (g : ElemGroup m n r s d → ℂ)
    (hg : ∀ a b, ContDiff ℝ ∞ (elemLift g a b)) (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i)) :
    elemLift (elemDeriv ψ g) a b = fun p => fderiv ℝ (elemLift g a b) p u := by
  funext p
  exact (line_hasDerivAt ψ u hu g hg a b p).deriv

theorem elem_hasDerivAt (g : ElemGroup m n r s d → ℂ)
    (hg : ∀ a b, ContDiff ℝ ∞ (elemLift g a b)) (y : ElemGroup m n r s d) :
    HasDerivAt (fun t : ℝ => g (y + ψ t)) (elemDeriv ψ g y) 0 := by
  have hy : ∀ j, ∃ z : ℝ, (z : UnitAddCircle) = y.2.1 j := fun j =>
    QuotientAddGroup.mk_surjective (y.2.1 j)
  choose z hz using hy
  have hy' : y = ((y.1, z).1, fun j => (((y.1, z).2 j : ℝ) : UnitAddCircle), y.2.2.1, y.2.2.2) := by
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext j
    exact (hz j).symm
  have h := line_hasDerivAt ψ u hu g hg y.2.2.1 y.2.2.2 (y.1, z)
  rw [← hy'] at h
  exact h.differentiableAt.hasDerivAt

end deriv

/-- `‖D^k (x ↦ DF(x) u)‖ ≤ ‖u‖ ‖D^{k+1} F‖`. -/
theorem norm_iteratedFDeriv_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℂ) (hF : ContDiff ℝ ∞ F) (u : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ F y u) x‖ ≤ ‖u‖ * ‖iteratedFDeriv ℝ (k + 1) F x‖ := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := (contDiff_infty_iff_fderiv.mp hF).2
  have h := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ F) (c := u) (x := x) (n := k)
    h1.contDiffAt (by exact_mod_cast le_top)
  rwa [norm_iteratedFDeriv_fderiv] at h


section hom

variable (ψ : ℝ →+ ElemGroup m n r s d) (u : (Fin m → ℝ) × (Fin n → ℝ))
    (hu : ∀ t : ℝ, (ψ t).1 = t • u.1 ∧
      (∀ j, (ψ t).2.1 j = ((t * u.2 j : ℝ) : UnitAddCircle)) ∧ (ψ t).2.2 = 0)
include hu

theorem isRapidDecay_elemDeriv (g : ElemGroup m n r s d → ℂ) (hg : IsRapidDecay g) :
    IsRapidDecay (elemDeriv ψ g) := by
  refine ⟨fun a b => ?_, fun i j k => ?_⟩
  · rw [elemLift_elemDeriv ψ u hu g hg.1 a b]
    exact ((contDiff_infty_iff_fderiv.mp (hg.1 a b)).2).clm_apply contDiff_const
  · obtain ⟨C, hC⟩ := hg.2 i j (k + 1)
    refine ⟨‖u‖ * C, fun a b xt => ?_⟩
    rw [elemLift_elemDeriv ψ u hu g hg.1 a b]
    have h := norm_iteratedFDeriv_dir (elemLift g a b) (hg.1 a b) u k xt
    have hw : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i := by positivity
    calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ (elemLift g a b) y u) xt‖
        ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖u‖ * ‖iteratedFDeriv ℝ (k + 1) (elemLift g a b) xt‖) :=
          mul_le_mul_of_nonneg_left h hw
      _ = ‖u‖ * (‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ (k + 1) (elemLift g a b) xt‖) := by
          ring
      _ ≤ ‖u‖ * C := mul_le_mul_of_nonneg_left (hC a b xt) (norm_nonneg u)

theorem elemDeriv_add (g₁ g₂ : ElemGroup m n r s d → ℂ)
    (hg₁ : ∀ a b, ContDiff ℝ ∞ (elemLift g₁ a b)) (hg₂ : ∀ a b, ContDiff ℝ ∞ (elemLift g₂ a b)) :
    elemDeriv ψ (g₁ + g₂) = elemDeriv ψ g₁ + elemDeriv ψ g₂ := by
  funext y
  exact ((elem_hasDerivAt ψ u hu g₁ hg₁ y).add (elem_hasDerivAt ψ u hu g₂ hg₂ y)).deriv

/-- The derivative along `ψ` as an additive endomorphism of `S(ℝ^m × 𝕋^n × ℤ^r × F)`. -/
noncomputable def elemDerivHom : ElemSchwartz m n r s d →+ ElemSchwartz m n r s d where
  toFun g := ⟨elemDeriv ψ g.toFun, Submodule.subset_span
    (isRapidDecay_elemDeriv ψ u hu g.toFun (isRapidDecay_elemSchwartz_toFun g))⟩
  map_zero' := by
    apply Subtype.ext
    funext y
    show deriv (fun t : ℝ => (0 : ElemGroup m n r s d → ℂ) (y + ψ t)) 0 = 0
    simp
  map_add' g₁ g₂ := by
    apply Subtype.ext
    exact elemDeriv_add ψ u hu g₁.toFun g₂.toFun (isRapidDecay_elemSchwartz_toFun g₁).1
      (isRapidDecay_elemSchwartz_toFun g₂).1

theorem elemDerivHom_toFun (g : ElemSchwartz m n r s d) :
    (elemDerivHom ψ u hu g).toFun = elemDeriv ψ g.toFun := rfl

theorem elemDerivHom_continuous : Continuous (elemDerivHom ψ u hu) := by
  refine elemSchwartz_continuous_of_seminorm_bound _ fun p => ⟨{(p.1, p.2.1, p.2.2 + 1)}, ‖u‖,
    fun g M hM a b xt => ?_⟩
  have hg := isRapidDecay_elemSchwartz_toFun g
  rw [elemDerivHom_toFun, elemLift_elemDeriv ψ u hu g.toFun hg.1 a b]
  have h := norm_iteratedFDeriv_dir (elemLift g.toFun a b) (hg.1 a b) u p.2.2 xt
  have hw : 0 ≤ ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 := by positivity
  have hM' := hM (p.1, p.2.1, p.2.2 + 1) (Finset.mem_singleton_self _) a b xt
  calc ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 *
        ‖iteratedFDeriv ℝ p.2.2 (fun y => fderiv ℝ (elemLift g.toFun a b) y u) xt‖
      ≤ ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 *
          (‖u‖ * ‖iteratedFDeriv ℝ (p.2.2 + 1) (elemLift g.toFun a b) xt‖) :=
        mul_le_mul_of_nonneg_left h hw
    _ = ‖u‖ * (‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 *
          ‖iteratedFDeriv ℝ (p.2.2 + 1) (elemLift g.toFun a b) xt‖) := by ring
    _ ≤ ‖u‖ * M := mul_le_mul_of_nonneg_left hM' (norm_nonneg u)

end hom


section group

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of a one-parameter subgroup lies in every open subgroup. -/
theorem a_mem (a : Multiplicative ℝ →ₜ* G) (Γ : Subgroup G) (hΓ : IsOpen (Γ : Set G)) (t : ℝ) :
    a (Multiplicative.ofAdd t) ∈ Γ := by
  have hcont : Continuous (fun t : ℝ => a (Multiplicative.ofAdd t)) :=
    a.continuous.comp continuous_ofAdd
  exact (isPreconnected_range hcont).subset_isClopen ⟨Γ.isClosed_of_isOpen hΓ, hΓ⟩
    ⟨1, ⟨0, by simp⟩, Γ.one_mem⟩ ⟨t, rfl⟩

/-- The one-parameter subgroup `t ↦ π(a(t))` of the elementary group `Γ/k`. -/
noncomputable def flow (a : Multiplicative ℝ →ₜ* G) (Γ : Subgroup G) (hΓ : IsOpen (Γ : Set G))
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) : ℝ →+ ElemGroup m n r s d where
  toFun t := Multiplicative.toAdd (π ⟨a (Multiplicative.ofAdd t), a_mem a Γ hΓ t⟩)
  map_zero' := by
    have : (⟨a (Multiplicative.ofAdd 0), a_mem a Γ hΓ 0⟩ : Γ) = 1 := Subtype.ext (by simp)
    show Multiplicative.toAdd (π ⟨a (Multiplicative.ofAdd 0), a_mem a Γ hΓ 0⟩) = 0
    rw [this, map_one]
    rfl
  map_add' s t := by
    have : (⟨a (Multiplicative.ofAdd (s + t)), a_mem a Γ hΓ (s + t)⟩ : Γ) =
        ⟨a (Multiplicative.ofAdd s), a_mem a Γ hΓ s⟩ *
          ⟨a (Multiplicative.ofAdd t), a_mem a Γ hΓ t⟩ :=
      Subtype.ext (by simp [ofAdd_add, map_mul])
    rw [this, map_mul, toAdd_mul]

theorem flow_continuous (a : Multiplicative ℝ →ₜ* G) (Γ : Subgroup G) (hΓ : IsOpen (Γ : Set G))
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπ : Continuous π) :
    Continuous (flow a Γ hΓ π) :=
  continuous_toAdd.comp (hπ.comp ((a.continuous.comp continuous_ofAdd).subtype_mk _))

theorem stage_hasDerivAt (a : Multiplicative ℝ →ₜ* G) (Γ : Subgroup G) (hΓ : IsOpen (Γ : Set G))
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (g : ElemGroup m n r s d → ℂ)
    (hg : ∀ a b, ContDiff ℝ ∞ (elemLift g a b)) (u : (Fin m → ℝ) × (Fin n → ℝ))
    (hu : ∀ t : ℝ, (flow a Γ hΓ π t).1 = t • u.1 ∧
      (∀ j, (flow a Γ hΓ π t).2.1 j = ((t * u.2 j : ℝ) : UnitAddCircle)) ∧
        (flow a Γ hΓ π t).2.2 = 0) (x : G) :
    HasDerivAt (fun t : ℝ => extendPullback Γ π g (x * a (Multiplicative.ofAdd t)))
      (extendPullback Γ π (elemDeriv (flow a Γ hΓ π) g) x) 0 := by
  by_cases hx : x ∈ Γ
  · have hfun : (fun t : ℝ => extendPullback Γ π g (x * a (Multiplicative.ofAdd t))) =
        fun t : ℝ => g (Multiplicative.toAdd (π ⟨x, hx⟩) + flow a Γ hΓ π t) := by
      funext t
      have hmem : x * a (Multiplicative.ofAdd t) ∈ Γ := Γ.mul_mem hx (a_mem a Γ hΓ t)
      have hprod : (⟨x * a (Multiplicative.ofAdd t), hmem⟩ : Γ) =
          ⟨x, hx⟩ * ⟨a (Multiplicative.ofAdd t), a_mem a Γ hΓ t⟩ := rfl
      simp only [extendPullback, dif_pos hmem, hprod, map_mul, toAdd_mul]
      rfl
    have hval : extendPullback Γ π (elemDeriv (flow a Γ hΓ π) g) x =
        elemDeriv (flow a Γ hΓ π) g (Multiplicative.toAdd (π ⟨x, hx⟩)) := by
      simp only [extendPullback, dif_pos hx]
    rw [hfun, hval]
    exact elem_hasDerivAt _ u hu g hg _
  · have hfun : (fun t : ℝ => extendPullback Γ π g (x * a (Multiplicative.ofAdd t))) =
        fun _ => 0 := by
      funext t
      have hmem : x * a (Multiplicative.ofAdd t) ∉ Γ := fun h =>
        hx (by simpa using Γ.mul_mem h (Γ.inv_mem (a_mem a Γ hΓ t)))
      simp only [extendPullback, dif_neg hmem]
    have hval : extendPullback Γ π (elemDeriv (flow a Γ hΓ π) g) x = 0 := by
      simp only [extendPullback, dif_neg hx]
    rw [hfun, hval]
    exact hasDerivAt_const _ _


/-- The derivative along `a` of a function on `G`. -/
noncomputable def dd (a : Multiplicative ℝ →ₜ* G) (f : G → ℂ) : G → ℂ :=
  fun x => deriv (fun t : ℝ => f (x * a (Multiplicative.ofAdd t))) 0

theorem dd_extendPullback (a : Multiplicative ℝ →ₜ* G) (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemSchwartz m n r s d) :
    (∀ x, HasDerivAt (fun t : ℝ => extendPullback Γ π g.toFun (x * a (Multiplicative.ofAdd t)))
      (dd a (extendPullback Γ π g.toFun) x) 0) ∧
    ∃ u : (Fin m → ℝ) × (Fin n → ℝ), ∃ hu : (∀ t : ℝ, (flow a Γ hs.1 π t).1 = t • u.1 ∧
      (∀ j, (flow a Γ hs.1 π t).2.1 j = ((t * u.2 j : ℝ) : UnitAddCircle)) ∧
        (flow a Γ hs.1 π t).2.2 = 0),
      dd a (extendPullback Γ π g.toFun) =
        extendPullback Γ π (elemDerivHom (flow a Γ hs.1 π) u hu g).toFun := by
  obtain ⟨u, hu⟩ := flow_structure (flow a Γ hs.1 π) (flow_continuous a Γ hs.1 π hπ.2.1)
  have hg := (isRapidDecay_elemSchwartz_toFun g).1
  have hD := stage_hasDerivAt a Γ hs.1 π g.toFun hg u hu
  have hdd : dd a (extendPullback Γ π g.toFun) =
      extendPullback Γ π (elemDerivHom (flow a Γ hs.1 π) u hu g).toFun :=
    funext fun x => (hD x).deriv
  refine ⟨fun x => ?_, u, hu, hdd⟩
  rw [hdd]
  exact hD x

theorem key (a : Multiplicative ℝ →ₜ* G) (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    (∀ x, HasDerivAt (fun t : ℝ => f (x * a (Multiplicative.ofAdd t))) (dd a f x) 0) ∧
      dd a f ∈ schwartzBruhatSubmodule G := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hf
    obtain ⟨hD, u, hu, hdd⟩ := dd_extendPullback a Γ k π hs hπ g
    refine ⟨hD, ?_⟩
    rw [hdd]
    exact Submodule.subset_span ⟨Γ, k, m, n, r, s, d, π, _, hs, hπ, rfl⟩
  | zero =>
    have h0 : dd a (0 : G → ℂ) = 0 := by
      funext x
      show deriv (fun t : ℝ => (0 : G → ℂ) (x * a (Multiplicative.ofAdd t))) 0 = 0
      simp
    refine ⟨fun x => ?_, ?_⟩
    · rw [h0]
      exact hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · rw [h0]
      exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ =>
    have hx : ∀ x, HasDerivAt (fun t : ℝ => (f₁ + f₂) (x * a (Multiplicative.ofAdd t)))
        (dd a f₁ x + dd a f₂ x) 0 := fun x => (h₁.1 x).add (h₂.1 x)
    have hdd : dd a (f₁ + f₂) = dd a f₁ + dd a f₂ := funext fun x => (hx x).deriv
    refine ⟨fun x => ?_, ?_⟩
    · rw [hdd]
      exact hx x
    · rw [hdd]
      exact Submodule.add_mem _ h₁.2 h₂.2
  | smul c f _ h =>
    have hx : ∀ x, HasDerivAt (fun t : ℝ => (c • f) (x * a (Multiplicative.ofAdd t)))
        (c * dd a f x) 0 := fun x => (h.1 x).const_mul c
    have hdd : dd a (c • f) = c • dd a f := funext fun x => (hx x).deriv
    refine ⟨fun x => ?_, ?_⟩
    · rw [hdd]
      exact hx x
    · rw [hdd]
      exact Submodule.smul_mem _ c h.2

/-- The operator `∂_a` on `S(G)` as a linear map. -/
noncomputable def Dlin (a : Multiplicative ℝ →ₜ* G) :
    SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G where
  toFun f := ⟨dd a f.1, (key a f.1 f.2).2⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    funext x
    exact (((key a f₁.1 f₁.2).1 x).add ((key a f₂.1 f₂.2).1 x)).deriv
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact (((key a f.1 f.2).1 x).const_mul c).deriv


theorem Dlin_ofElem (a : Multiplicative ℝ →ₜ* G) (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) :
    ∃ L : ElemSchwartz m n r s d →+ ElemSchwartz m n r s d, Continuous L ∧
      (Dlin a) ∘ SchwartzBruhat.ofElem Γ k π hs hπ = SchwartzBruhat.ofElem Γ k π hs hπ ∘ L := by
  obtain ⟨u, hu⟩ := flow_structure (flow a Γ hs.1 π) (flow_continuous a Γ hs.1 π hπ.2.1)
  refine ⟨elemDerivHom (flow a Γ hs.1 π) u hu, elemDerivHom_continuous _ u hu, ?_⟩
  funext g
  apply Subtype.ext
  have hg := (isRapidDecay_elemSchwartz_toFun g).1
  have hD := stage_hasDerivAt a Γ hs.1 π g.toFun hg u hu
  exact funext fun x => (hD x).deriv

theorem Dlin_continuous (a : Multiplicative ℝ →ₜ* G) : Continuous (Dlin a) := by
  rw [continuous_iff_le_induced]
  change sInf {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
    ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat G) _ t
        (SchwartzBruhat.ofElem Γ k π hs hπ)} ≤ TopologicalSpace.induced (Dlin a)
    (sInf {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
    ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat G) _ t
        (SchwartzBruhat.ofElem Γ k π hs hπ)})
  rw [induced_sInf]
  refine le_sInf ?_
  rintro _ ⟨t, ht, rfl⟩
  apply sInf_le
  refine ⟨?_, ?_⟩
  · obtain ⟨ι, hι, p, hp⟩ := ht.1
    exact ⟨ι, hι, p.comp (Dlin a), @LinearMap.withSeminorms_induced ℂ ℂ (SchwartzBruhat G)
      (SchwartzBruhat G) ι _ _ _ _ _ _ (RingHom.id ℂ) _ t p hp (Dlin a)⟩
  · intro Γ k m n r s d π hs hπ
    rw [continuous_induced_rng]
    obtain ⟨L, hL, hcomm⟩ := Dlin_ofElem a Γ k π hs hπ
    rw [hcomm]
    exact (ht.2 Γ k m n r s d π hs hπ).comp hL

end group

end Sol_MasulloGRH_schwartzBruhat_oneParameterDeriv

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_oneParameterDeriv in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (a : Multiplicative ℝ →ₜ* G) :
    ∃ D : SchwartzBruhat G →L[ℂ] SchwartzBruhat G,
      ∀ (f : SchwartzBruhat G) (g : G),
        HasDerivAt (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) (D f g) 0 :=
  ⟨⟨Dlin a, Dlin_continuous a⟩, fun f g => (key a f.1 f.2).1 g⟩
