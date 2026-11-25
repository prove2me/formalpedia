-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.isProj_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:08.617428+00:00
-- url     : https://prove2.me/submissions/ebd633d9-94aa-4c91-9dbe-1647e1c64c3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_conv_tens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution {ι : Type} [Fintype ι] {a : ι → G → ℂ} (h : ∀ v, IsProj (a v)) : IsProj (tens a) := by
  refine ⟨by rw [conv_tens]; simp only [fun v => (h v).1], fun x => ?_⟩
  simp only [tens, Pi.inv_apply, map_prod, fun v => (h v).2]
end GlobalTheory.BadShare.Basic
