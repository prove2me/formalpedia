-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.trace_op_reg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:10.355864+00:00
-- url     : https://prove2.me/submissions/17074586-7182-4853-b958-a3d2d47d10ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_op_reg

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
variable (G : Type) [Group G] [Fintype G]
variable {G}
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (e : G → ℂ) : LinearMap.trace ℂ _ (op (regFn G) e) = Fintype.card G * e 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace]
  have : ∀ x : G, Matrix.diag (LinearMap.toMatrix (Pi.basisFun ℂ G) (Pi.basisFun ℂ G) (op (regFn G) e)) x = e 1 := by
    intro x
    simp only [Matrix.diag, LinearMap.toMatrix_apply, op_reg, Pi.basisFun_apply, Pi.basisFun_repr, conv]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro y _ hy
      rw [Pi.single_eq_of_ne, mul_zero]
      simpa using hy
    · simp
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp
end GlobalTheory.BadShare.Basic
