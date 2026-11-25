-- Prove2me | solution 1 for GlobalTheory.HCXi.Funct.meas_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:10:22.865835+00:00
-- url     : https://prove2.me/submissions/5eac2b4c-f156-4182-868b-ac8ab96b7241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuousStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SphericalFunctionFunctionalEq
import Theorems.Thm_GlobalTheory_T_gram_positive_volume_continuous


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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.Funct
namespace GlobalTheory.HCXi.Funct
theorem _root_.solution {k r : ℕ} (hk : 1 ≤ k) {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {f : α → Mat k r} (hf : Continuous f) :
    Measurable fun t => ENNReal.ofReal (vHalf k r (f t)) := by
  have hm := (GlobalTheory.T.gram_positive_volume_continuous k r hk).2.2.1
  have hf' : Continuous (Y := Mt k r) fun t => Matrix.of.symm (f t) := hf
  exact ENNReal.measurable_ofReal.comp (hm.comp hf'.measurable)
end GlobalTheory.HCXi.Funct
