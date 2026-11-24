-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.alg_dirac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:01.012738+00:00
-- url     : https://prove2.me/submissions/890efe99-1a86-4fc8-9d20-c2377a375553

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_coeff_alg

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
theorem _root_.solution : alg (dirac : G → ℂ) = 1 := by
  ext x
  rw [coeff_alg, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply, dirac]
  simp [eq_comm]
end GlobalTheory.BadShare.Basic
