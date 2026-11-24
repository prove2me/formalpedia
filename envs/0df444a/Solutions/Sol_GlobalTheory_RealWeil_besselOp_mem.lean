-- Prove2me | solution 1 for GlobalTheory.RealWeil.besselOp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:57.257803+00:00
-- url     : https://prove2.me/submissions/13cda72b-e00e-490b-b273-755da219a4f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_dRho_mem_weylAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution : besselOp l ∈ weylAlg l :=
  sub_mem (one_mem _) (Subalgebra.smul_mem _ (sum_mem fun _ _ => mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _)) _)
end GlobalTheory.RealWeil
