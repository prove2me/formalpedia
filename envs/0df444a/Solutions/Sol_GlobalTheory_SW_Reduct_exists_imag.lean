-- Prove2me | solution 1 for GlobalTheory.SW.Reduct.exists_imag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:52.317862+00:00
-- url     : https://prove2.me/submissions/a735ea4c-ec4b-4d46-a0f3-1023634965ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Reduct
theorem _root_.solution : ∃ (ξ : E) (D : ℕ), ξ ≠ 0 ∧ cc ξ = -ξ ∧ 0 < D ∧ IsIntegral ℤ ((D : E) * ξ) ∧
    IsIntegral ℤ ((D : E) * ξ⁻¹) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, cc x ≠ x := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ ({x - cc x, (x - cc x)⁻¹} : Finset E)
  have key : ∀ t : E, IsIntegral ℤ (y • t) → IsIntegral ℤ ((y.natAbs : E) * t) := fun t ht => by
    rw [zsmul_eq_mul] at ht
    rcases Int.natAbs_eq y with e | e
    · rw [e] at ht; simpa using ht
    · rw [e] at ht; simpa using ht.neg
  refine ⟨x - cc x, y.natAbs, sub_ne_zero.2 hx.symm, by simp [cc], Int.natAbs_pos.2 hy,
    key _ (h _ (by simp)), key _ (h _ (by simp))⟩
end GlobalTheory.SW.Reduct
