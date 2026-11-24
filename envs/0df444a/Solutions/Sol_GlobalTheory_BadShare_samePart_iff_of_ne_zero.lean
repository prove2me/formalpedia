-- Prove2me | solution 1 for GlobalTheory.BadShare.samePart_iff_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:07.574205+00:00
-- url     : https://prove2.me/submissions/0eb2ab56-1409-41b7-910f-ab1712c144ee

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Theorems.Thm_GlobalTheory_BadShare_samePart_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
example : BB 7 1 3 := bb_of_dvd (d := 1) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num)
example : ¬ BB 7 1 6 := by
  rw [bb_iff]; norm_num
section part
variable {k : Type} [Field k] {l : ℕ}
end part
variable {g}
open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem isOfFinOrder_of_ne_zero_algebraicClosure_zmod {g : ℕ} [Fact g.Prime]
    {x : AlgebraicClosure (ZMod g)} (hx : x ≠ 0) : IsOfFinOrder x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (by simpa [y] using congrArg Subtype.val h)
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite (Units.mk0 y hy)).exists_pow_eq_one
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  have := congrArg (fun u : (IntermediateField.adjoin (ZMod g) {x})ˣ =>
    ((u : IntermediateField.adjoin (ZMod g) {x}) : AlgebraicClosure (ZMod g))) hpow
  simpa [y] using this
example : torusCard g X = g - 1 := by rw [torusCard_irreducible irreducible_X]; simp
end GlobalTheory.BadShare
end
end

set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution {l : ℕ} (hl : l.Prime) {x y : AlgebraicClosure (ZMod g)} (hx : x ≠ 0)
    (hy : y ≠ 0) : _root_.GlobalTheory.BadShare.SamePart l x y ↔ ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) :=
  _root_.GlobalTheory.BadShare.samePart_iff hl (isOfFinOrder_of_ne_zero_algebraicClosure_zmod hx)
    (isOfFinOrder_of_ne_zero_algebraicClosure_zmod hy)
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
