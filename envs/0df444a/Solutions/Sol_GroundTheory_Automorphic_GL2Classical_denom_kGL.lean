-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.denom_kGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:47.704061+00:00
-- url     : https://prove2.me/submissions/8222b719-a8bf-4141-b7ac-0818c0ac38cd

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
theorem _root_.solution (w : ℂ) (hw : w ≠ 0) : denom (kGL w hw) (I : ℂ) = w := by
  rw [denom]
  apply Complex.ext <;> simp
end GroundTheory.Automorphic.GL2Classical
