-- Prove2me | solution 1 for GlobalTheory.CoeffWord.coeffWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:25.039925+00:00
-- url     : https://prove2.me/submissions/9d6c7af4-e71f-45cd-a293-9790822af40c

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_GlobalTheory_CoeffWord_eval_applyWord
import Theorems.Thm_GlobalTheory_CoeffWord_mem_positions
import Theorems.Thm_GlobalTheory_CoeffWord_wordOf_eq
import Theorems.Thm_GlobalTheory_CoeffWord_pairwise_positions
import Theorems.Thm_GlobalTheory_CoeffWord_eq_of_filter_eq
import Theorems.Thm_GlobalTheory_CoeffWord_unitri_monomial_of_lowerTri
import Theorems.Thm_GlobalTheory_CoeffWord_unitri_monomial_of_not
import Theorems.Thm_GlobalTheory_CoeffWord_weight_colW
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
namespace GlobalTheory.CoeffWord
theorem _root_.solution : Formalism.GradedWeylDivisibility.CoeffWord := by
  classical
  intro R _ r n ν F e hF he hν
  rw [wordOf_eq, eval_applyWord e _ (fun q hq => (mem_positions q).1 hq) pairwise_positions]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, coeff_sum, coeff_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (colW r n) m = ν := hF (mem_support_iff.1 hm)
  by_cases hl : LowerTri m
  · rw [unitri_monomial_of_lowerTri m hl, coeff_monomial, coeff_monomial]
    refine if_congr ⟨fun h => by rw [h], fun h => ?_⟩ rfl rfl
    refine eq_of_filter_eq m e hl he (fun s => by rw [← weight_colW, hw, hν]) fun v hv => ?_
    have := DFunLike.congr_fun h v
    simpa [Finsupp.filter_apply, mem_positions, hv] using this
  · rw [unitri_monomial_of_not m hl, coeff_monomial, if_neg (fun h : m = e => hl (h ▸ he)), coeff_zero]
end GlobalTheory.CoeffWord
