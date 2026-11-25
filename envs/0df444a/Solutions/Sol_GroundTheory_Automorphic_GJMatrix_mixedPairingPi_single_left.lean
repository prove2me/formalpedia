-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedPairingPi_single_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:37.9366+00:00
-- url     : https://prove2.me/submissions/585cc122-e632-4a83-92cd-d7ce2e35f823

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
variable {K}
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (i : ι) (x : mixedSpace K) (y : ι → mixedSpace K) :
    mixedPairingPi K (Pi.single i x) y = mixedTraceForm K x (y i) := by
  rw [mixedPairingPi, Finset.sum_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
    (by simp), Pi.single_eq_same]
end GroundTheory.Automorphic.GJMatrix
