-- Prove2me | solution 1 for GlobalTheory.continuous_tsum_lattice_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:49.902979+00:00
-- url     : https://prove2.me/submissions/8f431fd5-33f2-448a-a6bb-2ba40a10c34d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ V] [DiscreteTopology L] [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x) :
    Continuous fun u : E ↦ ∑' x : L, f (x + u) := by
  refine continuous_iff_continuousAt.2 fun u ↦ ?_
  obtain ⟨g, hg, h⟩ := hdom (‖u‖ + 1)
  have : ContinuousOn (fun u : E ↦ ∑' x : L, f (x + u)) (Metric.ball 0 (‖u‖ + 1)) :=
    continuousOn_tsum (fun x ↦ by fun_prop) hg
      fun x v hv ↦ h x v (mem_ball_zero_iff.1 hv).le
  exact this.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
end GlobalTheory
