-- Prove2me | solution 1 for GroundTheory.LocalField.CongrData.zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:43.789544+00:00
-- url     : https://prove2.me/submissions/148234b7-80b5-4355-8e3b-65332de9c2c3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_CongrData_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
omit [Fintype G]
namespace GroundTheory.LocalField
namespace CongrData
theorem _root_.solution {f : G → ℂ} (hf : CongrData ζ N s a f) (n : ℤ) : CongrData ζ N s a (n • f) := by
  have := hf.smul (n : Algebra.adjoin ℤ ({ζ} : Set ℂ))
  rwa [show ((n : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) = (n : ℂ) by simp, Int.cast_smul_eq_zsmul] at this
end CongrData
end GroundTheory.LocalField
