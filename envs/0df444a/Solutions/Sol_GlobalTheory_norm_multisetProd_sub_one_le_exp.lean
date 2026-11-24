-- Prove2me | solution 1 for GlobalTheory.norm_multisetProd_sub_one_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:27.118421+00:00
-- url     : https://prove2.me/submissions/103b365e-68b7-43a7-9ff0-996d7ccf4ecf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
import Theorems.Thm_GlobalTheory_CuspFormEvaluationComplement_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (s : Multiset ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ t) : ‖s.prod - 1‖ ≤ Real.exp (s.card * t) - 1 := by
  first
  | exact @_root_.GlobalTheory.CuspFormEvaluationComplement.main
  | exact _root_.GlobalTheory.CuspFormEvaluationComplement.main
  | (apply _root_.GlobalTheory.CuspFormEvaluationComplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CuspFormEvaluationComplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CuspFormEvaluationComplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CuspFormEvaluationComplement.main ..)
end GlobalTheory
