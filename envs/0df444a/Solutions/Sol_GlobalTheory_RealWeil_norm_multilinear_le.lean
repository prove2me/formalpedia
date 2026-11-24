-- Prove2me | solution 1 for GlobalTheory.RealWeil.norm_multilinear_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:49:59.456844+00:00
-- url     : https://prove2.me/submissions/f9a9bc3a-a652-46b9-9178-4335748781e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg

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
theorem _root_.solution {n : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ l) ℂ) :
    ‖m‖ ≤ ∑ r : Fin n → l, ‖m fun i => EuclideanSpace.single (r i) 1‖ := by
  refine m.opNorm_le_bound (by positivity) fun v => ?_
  have : v = fun i => ∑ j, v i j • (EuclideanSpace.single j 1 : EuclideanSpace ℝ l) := by
    funext i
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [this, m.map_sum]
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [m.map_smul_univ, norm_smul, mul_comm, norm_prod]
  gcongr with i
  exact PiLp.norm_apply_le _ _
end GlobalTheory.RealWeil
