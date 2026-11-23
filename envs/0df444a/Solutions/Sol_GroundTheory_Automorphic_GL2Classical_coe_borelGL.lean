-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.coe_borelGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:03.850395+00:00
-- url     : https://prove2.me/submissions/857b42b0-da2f-4d67-a653-3ae22895ef5d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix UpperHalfPlane
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution (z : ℍ) :
    (borelGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1] :=
  rfl
end GroundTheory.Automorphic.GL2Classical
