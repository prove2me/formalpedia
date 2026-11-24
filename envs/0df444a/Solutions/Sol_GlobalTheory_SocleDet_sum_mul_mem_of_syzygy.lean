-- Prove2me | solution 1 for GlobalTheory.SocleDet.sum_mul_mem_of_syzygy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:53:32.906806+00:00
-- url     : https://prove2.me/submissions/9bb28947-ce9b-4a22-9e5f-706074b372ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SocleDet
theorem _root_.solution (I : Ideal R) (x C : n → R)
    (hx : ∀ (S : Finset n) (i : n), i ∉ S → ∀ p : R, p * x i ∈ Ideal.span (x '' S) →
      p ∈ Ideal.span (x '' S))
    (hC : ∀ j l, C j * x l - C l * x j ∈ I) (S : Finset n) :
    ∀ s : n → R, ∑ j ∈ S, s j * x j = 0 → ∑ j ∈ S, s j * C j ∈ I := by
  induction S using Finset.induction_on with
  | empty => intro s _; simp
  | insert i S hi ih =>
    intro s hs
    rw [Finset.sum_insert hi] at hs ⊢
    have h1 : s i * x i ∈ Ideal.span (x '' S) := by
      rw [eq_neg_of_add_eq_zero_left hs]
      exact neg_mem (Ideal.sum_mem _ fun j hj =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, hj, rfl⟩))
    obtain ⟨t, ht⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' R).1 (hx S i hi _ h1)
    simp only [smul_eq_mul] at ht
    have h2 := ih (fun j => s j + t j * x i) (by
      rw [← hs, ← ht, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring)
    have h3 : ∑ j ∈ S, t j * (C i * x j - C j * x i) ∈ I :=
      I.sum_mem fun j _ => I.mul_mem_left _ (hC i j)
    have h4 := I.add_mem h2 h3
    convert h4 using 1
    rw [← ht, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.SocleDet
