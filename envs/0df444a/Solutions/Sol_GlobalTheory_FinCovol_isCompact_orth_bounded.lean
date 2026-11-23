-- Prove2me | solution 1 for GlobalTheory.FinCovol.isCompact_orth_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:09.391362+00:00
-- url     : https://prove2.me/submissions/978399b1-21cd-4a04-bc00-58111b259889

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsCompactOrthBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.FinCovol
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FinCovol
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by
  intro r X R
  have h1 : IsClosed {x : Frame X.Ψ r | IsOrth X x} := by
    simp only [IsOrth, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    refine continuous_matrix fun a b => ?_
    simp only [gram, hermC, col, mat, Matrix.of_apply]
    fun_prop
  have h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ?_ continuous_const
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_
  rintro x ⟨-, hx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro τ
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro b
  exact (hx τ a b).trans (le_abs_self R)
end GlobalTheory.FinCovol
