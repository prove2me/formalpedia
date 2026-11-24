-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.contDiffOn_tsum_infty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:38.66046+00:00
-- url     : https://prove2.me/submissions/fd693f02-6590-4827-a485-65f38ca1a513

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_contDiffOn_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.SumGood
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] {ι : Type}
namespace GlobalTheory.HeckeTwo.SumGood
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) :
    ContDiffOn ℝ ∞ (fun y => ∑' i, f i y) U :=
  contDiffOn_infty.2 fun n => contDiffOn_tsum hU n hf
end GlobalTheory.HeckeTwo.SumGood
