-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedPairingPi_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:36.676421+00:00
-- url     : https://prove2.me/submissions/769751c2-34d7-4d03-9159-cbd0b3beede2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (x y : ι → mixedSpace K) :
    mixedPairingPi K x (-y) = -mixedPairingPi K x y := by
  simp only [mixedPairingPi, Pi.neg_apply, map_neg, Finset.sum_neg_distrib]
end GroundTheory.Automorphic.GJMatrix
