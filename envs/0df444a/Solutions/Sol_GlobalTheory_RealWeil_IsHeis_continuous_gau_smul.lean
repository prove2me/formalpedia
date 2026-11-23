-- Prove2me | solution 1 for GlobalTheory.RealWeil.IsHeis.continuous_gau_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:26.42103+00:00
-- url     : https://prove2.me/submissions/5cf5e8b2-b1b3-4122-8490-e5e4d18da9e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace B]
namespace GlobalTheory.RealWeil
namespace IsHeis
theorem _root_.solution (h : IsHeis om ρ) (f : B) : Continuous fun u => gau u • ρ u f :=
  continuous_gau.smul (h.2.2.2 f)
end IsHeis
end GlobalTheory.RealWeil
