-- Prove2me | solution 1 for GlobalTheory.diffElt_sub_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:47.276581+00:00
-- url     : https://prove2.me/submissions/93d8ce69-327c-4b8f-b0a0-9b8f5edf5c62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (s : Finset ι) (g : ι → G) (x : G) :
    diffElt (x - ∑ i ∈ s, g i) - (diffElt x - ∑ i ∈ s, diffElt (g i)) ∈ diffIdeal G ^ 2 := by
  let f : G →+ AddMonoidAlgebra ℤ G ⧸ diffIdeal G ^ 2 :=
    AddMonoidHom.mk' (fun g ↦ Ideal.Quotient.mk _ (diffElt g)) fun a b ↦ by
      rw [← map_add, Ideal.Quotient.eq, diffElt_add, sub_sub_cancel_left, neg_mem_iff, sq]
      exact Ideal.mul_mem_mul (diffElt_mem a) (diffElt_mem b)
  have hf : ∀ g, Ideal.Quotient.mk _ (diffElt g) = f g := fun _ ↦ rfl
  rw [← Ideal.Quotient.eq]
  simp only [map_sub, map_sum, hf]
end GlobalTheory
