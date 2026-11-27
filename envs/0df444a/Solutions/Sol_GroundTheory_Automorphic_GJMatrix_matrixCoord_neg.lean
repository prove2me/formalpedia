-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.matrixCoord_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:57.029849+00:00
-- url     : https://prove2.me/submissions/54407715-3931-4cce-a333-f42e7eacd5a6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open MeasureTheory Matrix
noncomputable section
variable {n X : Type*} [Fintype n]
omit [Fintype n]
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution [Neg X] (x : Matrix n n X) : matrixCoord (-x) = -matrixCoord x := rfl
end GroundTheory.Automorphic.GJMatrix
