-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedPairing2_single_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:06:09.108081+00:00
-- url     : https://prove2.me/submissions/f6b05ec6-bea1-4ca4-a71f-2dc40de86971

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution (i : Fin 2) (x : mixedSpace K) (y : Fin 2 → mixedSpace K) :
    mixedPairing2 K (Pi.single i x) y = mixedTraceForm K x (y i) := by
  rw [mixedPairing2, Fin.sum_univ_two]
  fin_cases i <;> simp
end GroundTheory.Automorphic.Adele2
