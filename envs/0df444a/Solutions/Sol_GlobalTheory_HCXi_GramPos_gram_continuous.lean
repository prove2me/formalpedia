-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.gram_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:01:04.048808+00:00
-- url     : https://prove2.me/submissions/3cea8eab-ca34-4ad7-a6e2-0f4de5bd6c45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.GramPos
namespace GlobalTheory.HCXi.GramPos
theorem _root_.solution (k r : ℕ) (a : Fin (r + 1)) : Continuous fun g : Mat k r => gram k r g a := by
  unfold gram
  have h : Continuous fun g : Mat k r => g * frame k r := continuous_id.matrix_mul continuous_const
  exact Complex.continuous_re.comp
    ((h.matrix_conjTranspose.matrix_mul h).matrix_submatrix _ _).matrix_det
end GlobalTheory.HCXi.GramPos
