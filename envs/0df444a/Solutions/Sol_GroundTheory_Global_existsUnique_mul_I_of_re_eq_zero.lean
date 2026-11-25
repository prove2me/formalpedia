-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_mul_I_of_re_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:44.928885+00:00
-- url     : https://prove2.me/submissions/d1a1855a-d24a-41d6-b2ee-4bf09d6eeca4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_circleToUnits



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution {P : ℂ → Prop} (h : ∃! s, P s)
    (hre : ∀ s, P s → s.re = 0) : ∃! τ : ℝ, P ((τ : ℂ) * I) := by
  obtain ⟨s, hs, hu⟩ := h
  have hs' : s = (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre s hs]
  refine ⟨s.im, by show P ((s.im : ℂ) * I); rw [← hs']; exact hs, fun τ hτ => ?_⟩
  have := congrArg Complex.im (hu _ hτ)
  simpa using this
end GroundTheory.Global
