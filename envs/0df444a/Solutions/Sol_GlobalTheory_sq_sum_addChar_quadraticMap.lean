-- Prove2me | solution 1 for GlobalTheory.sq_sum_addChar_quadraticMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:41.987696+00:00
-- url     : https://prove2.me/submissions/4c773bb1-0a3e-4b91-b9c1-597a5a945345

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_eq_zero_of_add_self_eq_zero_of_odd_card
import Theorems.Thm_GlobalTheory_sq_sum_bicharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [AddCommGroup A] [Fintype A]
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] (hodd : Odd (Fintype.card A))
    (q : QuadraticMap ℤ A M) (ψ : AddChar M ℂ)
    (hnd : ∀ x, (∀ y, ψ (QuadraticMap.polar q x y) = 1) → x = 0) :
    (∑ x, ψ (q x)) ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) := by
  let B : A → AddChar A ℂ := fun x => ψ.compAddMonoidHom (q.polarBilin (x + x)).toAddMonoidHom
  have hB : ∀ x y, B x y = ψ (QuadraticMap.polar q (x + x) y) := fun _ _ => rfl
  rw [← sq_sum_bicharacter hodd B]
  · congr 1
    have hφ : Function.Bijective fun x : A => x + x := by
      refine Finite.injective_iff_bijective.1 fun x y h => sub_eq_zero.1 ?_
      refine eq_zero_of_add_self_eq_zero_of_odd_card hodd ?_
      have h' : x + x = y + y := h
      rw [sub_add_sub_comm, h', sub_self]
    refine (Fintype.sum_bijective _ hφ _ _ fun x => ?_).symm
    rw [hB, QuadraticMap.polar_add_left, QuadraticMap.polar_self, QuadraticMap.map_add_self]
    congr 1
    module
  · intro x y
    rw [hB, hB, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left,
      QuadraticMap.polar_comm q x y]
  · intro x hx
    refine eq_zero_of_add_self_eq_zero_of_odd_card hodd (hnd _ fun y => ?_)
    rw [← hB, hx]; rfl
end GlobalTheory
