-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_addChar_real_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:54.59695+00:00
-- url     : https://prove2.me/submissions/a0542513-8c7e-4646-934a-020a71c66478

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Theorems.Thm_GroundTheory_Global_existsUnique_exp_of_continuous


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
theorem _root_.solution (χ : AddChar ℝ ℂˣ) (hχ : Continuous χ) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) :=
  existsUnique_exp_of_continuous χ hχ χ.map_add_eq_mul
end GroundTheory.Global
