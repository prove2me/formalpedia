-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.chi_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:51.573738+00:00
-- url     : https://prove2.me/submissions/ed0d6d2c-1a69-4f0b-8733-e63fd7b91f5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial

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
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (L : Lev g N) {u : GG g N} (hu : L.Mem u) : L.chi u⁻¹ = (L.chi u)⁻¹ := by
  have := chi_mul L hu (mem_inv L hu)
  rw [mul_inv_cancel, chi_one] at this
  exact eq_inv_of_mul_eq_one_right this.symm
end GlobalTheory.BadShare.Basic
