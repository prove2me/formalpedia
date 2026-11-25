-- Prove2me | solution 1 for GlobalTheory.exists_addValuation_expNegTop_eq_nnnorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:34.964116+00:00
-- url     : https://prove2.me/submissions/bbb69a3c-9d49-4449-8399-3c79c010365b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNnrealValuationOfAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsAlgClosedAddValuationIsAdicComplete
import Theorems.Thm_GlobalTheory_expNegTop_inj_of_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped NNReal
namespace GlobalTheory
theorem _root_.solution {C : Type} [NormedField C] [IsUltrametricDist C]
    (h : ∀ x : C, ∃ t : WithTop ℚ, expNegTop t = ‖x‖₊) :
    ∃ v : AddValuation C (WithTop ℚ), ∀ x, expNegTop (v x) = ‖x‖₊ := by
  choose f hf using h
  refine ⟨AddValuation.of f ?_ ?_ ?_ ?_, hf⟩
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_zero, expNegTop_top]
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_one, expNegTop_zero]
  · intro x y
    rcases le_max_iff.1 (IsUltrametricDist.nnnorm_add_le_max x y) with h | h
    · exact min_le_of_left_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
    · exact min_le_of_right_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
  · intro x y
    apply expNegTop_inj_of_eq
    rw [expNegTop_add, hf, hf, hf, nnnorm_mul]
end GlobalTheory
