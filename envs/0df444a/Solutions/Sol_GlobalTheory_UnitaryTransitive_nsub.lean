-- Prove2me | solution 1 for GlobalTheory.UnitaryTransitive.nsub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:14.893674+00:00
-- url     : https://prove2.me/submissions/a8a43593-cf90-43e6-a2dd-37215edb0035

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitaryTransitive
variable {E : Type} [NormedField E] [StarRing E]
namespace GlobalTheory.UnitaryTransitive
theorem _root_.solution [IsUltrametricDist E] (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]; simpa using IsUltrametricDist.norm_add_le_max a (-b)
end GlobalTheory.UnitaryTransitive
