-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.continuous_hmon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:32.999117+00:00
-- url     : https://prove2.me/submissions/7372ebdc-d9a4-48a6-9417-2665aa6717d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution (m : ℤ) : Continuous (hmon m) := by
  unfold hmon; split_ifs <;> fun_prop
end GlobalTheory.HeckeTheta.Decay
