-- Prove2me | solution 1 for GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_eq_of_finrank_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:05:35.74782+00:00
-- url     : https://prove2.me/submissions/0761e3d1-2439-4726-adc5-5226027a929c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Theorems.Thm_GlobalTheory_CuspGL_invariantSubspaceMobiusInverseRec_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (s : F[X] → ℂ) (n : ℕ) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V), Module.finrank F V < n → Module.finrank F V < m →
    invariantSubspaceMobiusInverseRec s n V g = invariantSubspaceMobiusInverseRec s m V g := by
  induction n with
  | zero => intro m V _ _ _ g h; omega
  | succ n ih =>
    intro m V _ _ _ g h h'
    cases m with
    | zero => omega
    | succ m =>
      rw [invariantSubspaceMobiusInverseRec_succ, invariantSubspaceMobiusInverseRec_succ]
      congr 1
      refine finsum_congr fun W => ?_
      have := Submodule.finrank_lt W.2.1
      exact ih m _ _ (by omega) (by omega)
end GlobalTheory.CuspGL
