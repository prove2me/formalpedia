-- Prove2me | solution 1 for GlobalTheory.CoordScale.sigmaFinite_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:22:28.654855+00:00
-- url     : https://prove2.me/submissions/127ca3e0-fdb7-4e22-9593-a50791816c6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreimageReindexScaleComplexLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordScale
open MeasureTheory
namespace GlobalTheory.CoordScale
theorem _root_.solution {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ENNReal}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have h : c • μ = c.toNNReal • μ := by
    rw [ENNReal.smul_def, ENNReal.coe_toNNReal hc]
  rw [h]
  infer_instance
end GlobalTheory.CoordScale
