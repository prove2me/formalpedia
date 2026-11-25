-- Prove2me | solution 1 for GlobalTheory.T.exists_poly_annihilates_commuting_linear_combination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:20:13.224477+00:00
-- url     : https://prove2.me/submissions/ecdc6cd9-7a03-49d4-baec-4d934f3614da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolyAnnihilatesCommutingLinearCombination
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolyAnnihilatesCommutingLinearCombinationStatement
import Theorems.Thm_GlobalTheory_CommutingPoly_exists_poly_annihilates_linear_combination


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] (A : ι → Module.End ℂ M),
    (∀ i j, Commute (A i) (A j)) → ∀ (c : ι → ℂ) (P : ι → Polynomial ℂ), (∀ i, P i ≠ 0) →
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) →
        Polynomial.aeval (∑ i, c i • A i) p v = 0 := by
  first | exact @GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination | exact GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination | (intros; apply GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination <;> assumption)
end _root_.GlobalTheory.T
