-- Prove2me | solution 1 for GlobalTheory.SocleDet.det_sub_det_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:44.055958+00:00
-- url     : https://prove2.me/submissions/e559ca4a-26a8-4f89-9a39-a7a3ccc34883

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Theorems.Thm_GlobalTheory_SocleDet_adjugate_updateRow
import Theorems.Thm_GlobalTheory_SocleDet_adjugate_cross_mem
import Theorems.Thm_GlobalTheory_SocleDet_sum_mul_mem_of_syzygy

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
theorem _root_.solution (I : Ideal R) (x : n → R)
    (hx : ∀ (S : Finset n) (i : n), i ∉ S → ∀ p : R, p * x i ∈ Ideal.span (x '' S) →
      p ∈ Ideal.span (x '' S))
    (c c' : Matrix n n R) (h : c *ᵥ x = c' *ᵥ x) (hI : ∀ r, (c *ᵥ x) r ∈ I) :
    c'.det - c.det ∈ I := by
  have key : ∀ S : Finset n, (Matrix.of (fun r j => if r ∈ S then c' r j else c r j)).det - c.det ∈ I := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : Matrix.of (fun r j => if r ∈ (∅ : Finset n) then c' r j else c r j) = c := by
        ext r j; simp
      rw [this]; simp
    | insert i S hi ih =>
      set M : Matrix n n R := Matrix.of (fun r j => if r ∈ S then c' r j else c r j) with hM
      have e1 : Matrix.of (fun r j => if r ∈ insert i S then c' r j else c r j)
          = M.updateRow i (c' i) := by
        ext r j
        by_cases hr : r = i
        · subst hr; simp
        · simp [hM, hr, updateRow_ne hr]
      have e2 : ∀ r, (M *ᵥ x) r = (c *ᵥ x) r := by
        intro r
        by_cases hr : r ∈ S
        · rw [h]
          simp [hM, mulVec, dotProduct, hr]
        · simp [hM, mulVec, dotProduct, hr]
      have h1 := sum_mul_mem_of_syzygy I x (fun j => M.adjugate j i) hx
        (fun j l => adjugate_cross_mem I M x i j l fun r _ => e2 r ▸ hI r) Finset.univ
        (fun j => c' i j - M i j) (by
          have a1 : ∑ j, c' i j * x j = (c *ᵥ x) i := by rw [h]; rfl
          have a2 : ∑ j, M i j * x j = (c *ᵥ x) i := by rw [← e2]; rfl
          simp only [sub_mul, Finset.sum_sub_distrib, a1, a2, sub_self])
      have h2 := I.add_mem h1 ih
      convert h2 using 1
      rw [e1, det_eq_sum_mul_adjugate_row (M.updateRow i (c' i)) i,
        det_eq_sum_mul_adjugate_row M i]
      simp only [adjugate_updateRow, updateRow_self, sub_mul, Finset.sum_sub_distrib]
      ring
  have := key Finset.univ
  have e : Matrix.of (fun r j => if r ∈ (Finset.univ : Finset n) then c' r j else c r j) = c' := by
    ext r j; simp
  rwa [e] at this
end GlobalTheory.SocleDet
