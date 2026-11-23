-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.gC_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:36.895887+00:00
-- url     : https://prove2.me/submissions/0e862af9-7240-4a39-b864-03ae7bb3059e

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
theorem _root_.solution (n : I → ℤ) : 0 ≤ gC n := Finset.prod_nonneg fun i _ => by positivity
end GlobalTheory.HeckeTheta.Decay
