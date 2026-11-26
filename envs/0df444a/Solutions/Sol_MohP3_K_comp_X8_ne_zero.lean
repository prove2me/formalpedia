-- Prove2me | solution 1 for MohP3.K.comp_X8_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:01:15.876459+00:00
-- url     : https://prove2.me/submissions/8d0343de-c70c-49ec-8175-41aa8da1eeac

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}
namespace MohP3.K
theorem _root_.solution {p : Polynomial k} (hp : p ≠ 0) : p.comp (X ^ 8) ≠ 0 := by
  rw [Ne, Polynomial.comp_eq_zero_iff]
  push_neg
  refine ⟨hp, fun _ hq => ?_⟩
  have := congrArg (fun r => r.natDegree) hq
  simp at this
end MohP3.K
