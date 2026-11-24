-- Prove2me | solution 1 for GlobalTheory.dense_mvPolynomial_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:02.225804+00:00
-- url     : https://prove2.me/submissions/7e5c15b7-589c-4d2a-b017-85fcf643b808

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DenseMvPolynomialEvalNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {D : ℕ} (q : MvPolynomial (Fin D) ℂ) (hq : q ≠ 0) :
    Dense {z : Fin D → ℂ | MvPolynomial.eval z q ≠ 0} := by
  rw [Metric.dense_iff]
  intro z₀ r hr
  by_contra hne
  apply hq
  refine MvPolynomial.funext_set (fun i => Metric.ball (z₀ i) r)
    (fun i => infinite_of_mem_nhds (z₀ i) (Metric.ball_mem_nhds _ hr)) (fun x hx => ?_)
  rw [map_zero]
  by_contra hx0
  apply hne
  refine ⟨x, ?_, hx0⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  exact fun i => hx i (Set.mem_univ i)
end GlobalTheory
