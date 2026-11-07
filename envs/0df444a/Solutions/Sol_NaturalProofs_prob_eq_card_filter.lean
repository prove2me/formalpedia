-- Prove2me | solution 1 for NaturalProofs.prob_eq_card_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:31:20.276024+00:00
-- url     : https://prove2.me/submissions/bbd8804e-5718-46b2-8de8-06c4a763426b

module
public import Mathlib
public import Definitions.Def_NaturalProofs_Prob

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open Finset
variable {Ω Ω' A B I X : Type} [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype B] [Fintype I]
  [Fintype X]
namespace NaturalProofs
theorem _root_.solution (p : Ω → Bool) :
    prob p = ((univ.filter (fun ω => p ω = true)).card : ℝ) / Fintype.card Ω := by
  simp only [prob, ind]
  rw [Finset.sum_boole]
end NaturalProofs
