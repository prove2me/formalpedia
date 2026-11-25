-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.cone_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:43:33.734125+00:00
-- url     : https://prove2.me/submissions/1ac9ed21-92c2-4a09-9c2f-56285224891b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
namespace GlobalTheory.HCXi.ConeOne
theorem _root_.solution (k r' : ℕ) : SFinite (coneMeas k r') := by
  rw [cone_def]; infer_instance
end GlobalTheory.HCXi.ConeOne
