-- Prove2me | solution 1 for GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:50.736973+00:00
-- url     : https://prove2.me/submissions/a6751ec7-11f6-4c41-a80f-b3636f7203e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRootStatement
import Theorems.Thm_GlobalTheory_QNorm_evenNorms_one_add_four_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 → (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) → EvenNorms w (1 + 4 * ρ) := by
  first | exact @GlobalTheory.QNorm.evenNorms_one_add_four_mul | exact GlobalTheory.QNorm.evenNorms_one_add_four_mul | (intros; apply GlobalTheory.QNorm.evenNorms_one_add_four_mul <;> assumption)
end _root_.GlobalTheory.T
