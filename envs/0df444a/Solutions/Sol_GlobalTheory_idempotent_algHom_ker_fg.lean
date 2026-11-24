-- Prove2me | solution 1 for GlobalTheory.idempotent_algHom_ker_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:00:13.644542+00:00
-- url     : https://prove2.me/submissions/7cb79b79-7fb2-4608-a7f8-091ef04a95ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothRangeOfIdempotentAlgHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (e : A →ₐ[R] A) (he : ∀ x, e (e x) = e x) :
    (RingHom.ker e.rangeRestrict.toRingHom).FG := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  refine ⟨s.image (fun x => x - e x), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨x, _, rfl⟩
    change e.rangeRestrict (x - e x) = 0
    apply Subtype.ext
    simp [he]
  · intro b hb
    have hb' : e b = 0 := by
      have := congrArg Subtype.val (show e.rangeRestrict b = 0 from hb)
      simpa using this
    have key : ∀ y : A, y - e y ∈ Ideal.span ((fun x => x - e x) '' (s : Set A)) := by
      intro y
      have hy : y ∈ Algebra.adjoin R (s : Set A) := by rw [hs]; exact Algebra.mem_top
      induction hy using Algebra.adjoin_induction with
      | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
      | algebraMap r => simp
      | add x y _ _ hx hy =>
        have h : x + y - e (x + y) = (x - e x) + (y - e y) := by rw [map_add]; ring
        rw [h]; exact Ideal.add_mem _ hx hy
      | mul x y _ _ hx hy =>
        have h : x * y - e (x * y) = x * (y - e y) + e y * (x - e x) := by rw [map_mul]; ring
        rw [h]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)
    simpa [hb'] using key b
end GlobalTheory
