-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.embPi_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:06:12.469004+00:00
-- url     : https://prove2.me/submissions/f0d2ebd2-ab1c-45b0-b30d-f6143facfc5a

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
omit [NumberField K] [Fintype ι]
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution : embPi K (0 : ι → K) = 0 := by
  funext i
  simp [embPi]
end GroundTheory.Automorphic.GJMatrix
