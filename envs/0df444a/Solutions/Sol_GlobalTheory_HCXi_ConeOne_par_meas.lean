-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.par_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:19.081804+00:00
-- url     : https://prove2.me/submissions/bee2de2f-a0cb-4545-99d2-851188a1dba9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_parametrisation_eq_scaled_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_parametrisation_map_measurable
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898


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
theorem _root_.solution (k r' : ℕ) : Measurable (par k r') := by
  have : par k r' = Ψt k r' ∘ cm1Θ k r' := funext fun p => parametrisation_eq_scaled_sum p
  rw [this]
  exact Ψt_meas.comp parametrisation_map_measurable
end GlobalTheory.HCXi.ConeOne
