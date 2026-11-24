-- Prove2me | solution 1 for GlobalTheory.JR.PartialInv.isTest_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:09:42.098641+00:00
-- url     : https://prove2.me/submissions/a0888601-649e-4a9c-995c-c8c5ab84fc2c

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
theorem _root_.solution {F : Type} [NormedField F] {r : ℕ} {f : Gl r F → ℂ} (hf : IsTest f)
    (A : Matrix (Fin r) (Fin r) F) (c : Fin r → F) (l : F) : IsTest fun v : Fin r → F => f (A, v, c, l) := by
  have hc : Continuous fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by fun_prop
  refine ⟨hf.1.comp_continuous hc, ?_⟩
  have he : IsClosedEmbedding fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun Y : Gl r F => Y.2.1) (fun _ => rfl) (by fun_prop) hc
  exact hf.2.comp_isClosedEmbedding he
end GlobalTheory.JR.PartialInv
