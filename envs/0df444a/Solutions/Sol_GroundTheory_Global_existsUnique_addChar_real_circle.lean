-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_addChar_real_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:43.764962+00:00
-- url     : https://prove2.me/submissions/150c4361-c65e-4c95-9f7e-1c23f9155feb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Theorems.Thm_GroundTheory_Global_existsUnique_circleExp_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution (χ : AddChar ℝ Circle) (hχ : Continuous χ) :
    ∃! τ : ℝ, ∀ t, χ t = Circle.exp (τ * t) :=
  existsUnique_circleExp_of_continuous χ hχ χ.map_add_eq_mul
end GroundTheory.Global
