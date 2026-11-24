-- Prove2me | solution 1 for GlobalTheory.SharpObj.exists_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:28:42.563105+00:00
-- url     : https://prove2.me/submissions/e5530032-aa5c-4529-8b2e-3ec1b0eab573

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
import Theorems.Thm_GlobalTheory_SharpObj_im_hermForm_per
import Theorems.Thm_GlobalTheory_SharpObj_per_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}
variable {τ : Matrix (Fin h) (Fin h) ℂ}
namespace GlobalTheory.SharpObj
theorem _root_.solution (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    ∃ Ef : LinearMap.BilinForm ℤ (LinearMap.range (per τ)),
      (∀ a b : LinearMap.range (per τ), (Ef a b : ℝ) = (hermForm (imInv τ) a b).im) ∧ Function.Bijective Ef := by
  have hinj := (per_lattice hs hp).1
  set e := LinearEquiv.ofInjective (per τ) hinj with he
  have hpe : ∀ a : LinearMap.range (per τ), per τ (e.symm a) = a := fun a => by
    rw [← LinearEquiv.ofInjective_apply (per τ) (h := hinj) (e.symm a), ← he, e.apply_symm_apply]
  obtain ⟨ω, hω⟩ : ∃ ω : LinearMap.BilinForm ℤ (Fin h ⊕ Fin h → ℤ), ∀ x y, ω x y = omegaStd x y :=
    ⟨LinearMap.mk₂ ℤ omegaStd
      (fun x x' y => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun x y y' => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring), fun _ _ => rfl⟩
  refine ⟨ω.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, fun a b => ?_, ?_, ?_⟩
  · rw [LinearMap.compl₁₂_apply, hω, ← im_hermForm_per hs hp]
    erw [hpe, hpe]
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have hx : ∀ y, omegaStd (e.symm a) y = 0 := fun y => by
      have := LinearMap.congr_fun ha (e y)
      simpa [LinearMap.compl₁₂_apply, hω] using this
    have hz : e.symm a = 0 := by
      funext j
      cases j with
      | inl i =>
        have := hx (fun k => if Sum.inr i = k then 1 else 0)
        simpa [omegaStd] using this
      | inr i =>
        have := hx (fun k => if Sum.inl i = k then 1 else 0)
        simpa [omegaStd] using this
    simpa using congrArg e hz
  · intro φ
    set ψ := φ.comp e.toLinearMap with hψ
    refine ⟨e (Sum.elim (fun i => ψ (fun k => if Sum.inr i = k then 1 else 0))
      (fun i => -ψ (fun k => if Sum.inl i = k then 1 else 0))), ?_⟩
    ext a
    obtain ⟨y, rfl⟩ := e.surjective a
    rw [LinearMap.compl₁₂_apply, hω]
    erw [e.symm_apply_apply, e.symm_apply_apply]
    have : φ (e y) = ψ y := rfl
    rw [this, LinearMap.pi_apply_eq_sum_univ ψ y, Fintype.sum_sum_type]
    simp only [omegaStd, Sum.elim_inl, Sum.elim_inr, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.SharpObj
