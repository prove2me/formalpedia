-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.alg_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:14:40.784912+00:00
-- url     : https://prove2.me/submissions/0fa89590-0afd-4ca0-b338-311a056e688a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_coeff_alg
import Theorems.Thm_GlobalTheory_BadShare_Basic_coeff_mul_eq_conv

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
theorem _root_.solution (a b : G → ℂ) : alg (conv a b) = alg a * alg b := by
  ext x
  rw [coeff_mul_eq_conv, coeff_alg]
  simp only [coeff_alg]
end GlobalTheory.BadShare.Basic
