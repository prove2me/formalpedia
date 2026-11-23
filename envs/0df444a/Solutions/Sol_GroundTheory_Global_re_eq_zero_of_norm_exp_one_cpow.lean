-- Prove2me | solution 1 for GroundTheory.Global.re_eq_zero_of_norm_exp_one_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:58.858804+00:00
-- url     : https://prove2.me/submissions/1cc69737-6584-4774-be42-4ee26af6b870

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary

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
theorem _root_.solution {s : ℂ}
    (h : ‖((Real.exp 1 : ℝ) : ℂ) ^ s‖ = 1) : s.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 1), Real.exp_one_rpow] at h
  exact Real.exp_eq_one_iff _ |>.mp h
end GroundTheory.Global
