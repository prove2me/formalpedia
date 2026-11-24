-- Prove2me | solution 1 for GlobalTheory.FrameFibre.herm_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:05.597863+00:00
-- url     : https://prove2.me/submissions/de9e5617-17d0-49a5-a55f-6c82af934af0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Theorems.Thm_GlobalTheory_FrameFibre_exists_smul_eq
import Theorems.Thm_GlobalTheory_FrameFibre_eq_zero_of_trace
import Theorems.Thm_GlobalTheory_FrameFibre_herm_smul_smul
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
variable [IsCMField E]
namespace GlobalTheory.FrameFibre
theorem _root_.solution {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hspan : Submodule.span E (Set.range φ) = ⊤) (G A : Matrix (Fin r) (Fin r) E) (ξ : E) (hξ : ξ ≠ 0)
    (h : ∀ v w, Algebra.trace ℚ E (ξ * FD.herm G (A *ᵥ φ v) (A *ᵥ φ w)) =
      Algebra.trace ℚ E (ξ * FD.herm G (φ v) (φ w))) (x y : Fin r → E) :
    FD.herm G (A *ᵥ x) (A *ᵥ y) = FD.herm G x y := by
  have h1 : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have key : ∀ v w, FD.herm G (A *ᵥ φ v) (A *ᵥ φ w) = FD.herm G (φ v) (φ w) := by
    intro v w
    apply mul_left_cancel₀ hξ
    rw [← sub_eq_zero]
    refine eq_zero_of_trace _ fun a => ?_
    have h2 := h (a • v) w
    have h3 : φ (a • v) = (a : E) • φ v := by rw [map_smul]; rfl
    have h4 := herm_smul_smul G (a : E) 1 (A *ᵥ φ v) (A *ᵥ φ w)
    have h5 := herm_smul_smul G (a : E) 1 (φ v) (φ w)
    rw [one_smul, h1, mul_one] at h4 h5
    rw [h3, Matrix.mulVec_smul, h4, h5] at h2
    rw [mul_sub, map_sub, mul_left_comm, h2, mul_left_comm, sub_self]
  obtain ⟨c, v, hc, hv⟩ := exists_smul_eq φ hspan x
  obtain ⟨d, w, hd, hw⟩ := exists_smul_eq φ hspan y
  have h2 := key v w
  rw [← hv, ← hw, Matrix.mulVec_smul, Matrix.mulVec_smul, herm_smul_smul, herm_smul_smul] at h2
  refine mul_left_cancel₀ (mul_ne_zero ?_ ?_) h2
  · simpa using hc
  · exact (map_ne_zero (IsCMField.complexConj E)).2 (by simpa using hd)
end GlobalTheory.FrameFibre
