-- Prove2me | solution 1 for Kirkman.sum_card_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:31.682663+00:00
-- url     : https://prove2.me/submissions/c53bc418-75ff-4b8b-b1d2-dbf62c9520af

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Instances
public import Definitions.Def_KirkmanLib_Kirkman

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
namespace Kirkman
theorem _root_.solution {v : ℕ} {𝒯 : Finset (Finset (Fin v))} (h : IsSTS 𝒯) :
    ∑ x : Fin v, #(𝒯.filter (fun T => x ∈ T)) = 3 * #𝒯 := by
  simp only [card_filter]
  rw [sum_comm]
  rw [card_eq_sum_ones, mul_sum, mul_one]
  refine sum_congr rfl fun T hT => ?_
  rw [← card_filter]
  have e : (univ : Finset (Fin v)).filter (fun i => i ∈ T) = T := by ext; simp
  rw [e, h.1 T hT]
end Kirkman
