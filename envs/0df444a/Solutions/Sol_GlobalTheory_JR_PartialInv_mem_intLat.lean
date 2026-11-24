-- Prove2me | solution 1 for GlobalTheory.JR.PartialInv.mem_intLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:09:42.711905+00:00
-- url     : https://prove2.me/submissions/25ef6129-c819-482e-98d2-21d5e865a27e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PartialInv
namespace GlobalTheory.JR.PartialInv
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] {r : ℕ} (x : Fin r → F) :
    x ∈ intLat F r ↔ ∀ i, ‖x i‖ ≤ 1 := by
  change x ∈ Set.univ.pi (fun _ => Metric.closedBall (0 : F) 1) ↔ _
  simp [Set.mem_pi]
end GlobalTheory.JR.PartialInv
