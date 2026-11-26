-- Prove2me | solution 1 for MohP3.comp_X8_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:44:57.311428+00:00
-- url     : https://prove2.me/submissions/d59d37c3-fad2-458b-92b4-e3be7b972c2b

module
public import Mathlib
public import Definitions.Def_MohP3_Independence

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3
namespace MohP3
theorem _root_.solution {p : ℚ[X]} (hp : p ≠ 0) : p.comp (X^8) ≠ 0 := by
  rw [Ne, Polynomial.comp_eq_zero_iff]
  push_neg
  refine ⟨hp, fun _ hq => ?_⟩
  have := congrArg (fun r => r.natDegree) hq
  simp at this
end MohP3
