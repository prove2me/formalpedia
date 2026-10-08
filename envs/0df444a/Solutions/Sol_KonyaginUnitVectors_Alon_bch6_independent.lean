-- Prove2me | solution 1 for KonyaginUnitVectors.Alon.bch6_independent
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:10:43.559173+00:00
-- url     : https://prove2.me/submissions/f1bc1f16-77d0-44eb-9505-2c7035af1121

import Mathlib

set_option autoImplicit false

namespace KonyaginUnitVectors.Alon

/-- Lemma 3 (BCH, six columns): a nonempty set of at most six nonzero field elements cannot satisfy
`Σ x = Σ x³ = Σ x⁵ = 0` in characteristic 2 (any such field, finite or not). -/
theorem pk_bch6_independent {F : Type*} [Field F] [CharP F 2] (T : Finset F) (h0 : (0 : F) ∉ T)
    (hT : T.card ≤ 6) (h1 : ∑ x ∈ T, x = 0) (h3 : ∑ x ∈ T, x ^ 3 = 0) (h5 : ∑ x ∈ T, x ^ 5 = 0) :
    T = ∅ := by
  classical
  by_contra hne
  have hpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  -- in characteristic 2 the squares of the power sums are the power sums of the squares
  have hsq : ∀ g : F → F, (∑ x ∈ T, g x) ^ 2 = ∑ x ∈ T, g x ^ 2 := fun g => sum_pow_char 2 T g
  have h2 : ∑ x ∈ T, x ^ 2 = 0 := by
    rw [← hsq (fun x => x), h1]; norm_num
  have h4 : ∑ x ∈ T, x ^ 4 = 0 := by
    have := hsq (fun x => x ^ 2)
    simp only [← pow_mul] at this
    rw [← this, h2]; norm_num
  have h6 : ∑ x ∈ T, x ^ 6 = 0 := by
    have := hsq (fun x => x ^ 3)
    simp only [← pow_mul] at this
    rw [← this, h3]; norm_num
  have hp : ∀ n, 1 ≤ n → n ≤ 6 → ∑ x ∈ T, x ^ n = 0 := by
    intro n hn1 hn6
    interval_cases n <;> first | assumption | simpa using h1
  -- Vandermonde
  let f : Fin T.card → F := fun i => (T.equivFin.symm i : F)
  have hf : Function.Injective f := fun i j h => T.equivFin.symm.injective (Subtype.ext h)
  have hsum : ∀ g : F → F, ∑ j : Fin T.card, g (f j) = ∑ x ∈ T, g x := by
    intro g
    rw [← Finset.sum_coe_sort T g]
    exact Equiv.sum_comp T.equivFin.symm (fun x : T => g x)
  have hzero : f = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := f) (v := f) hf (fun i => ?_)
    have := hsum (fun x => x * x ^ (i : ℕ))
    simp only [f] at this ⊢
    rw [this]
    simp only [← pow_succ']
    exact hp _ (Nat.succ_le_succ (Nat.zero_le _)) (by have := i.2; omega)
  have hi : f ⟨0, hpos⟩ = 0 := congrFun hzero _
  exact h0 (hi ▸ (T.equivFin.symm ⟨0, hpos⟩).2)

end KonyaginUnitVectors.Alon

open KonyaginUnitVectors.Alon

theorem solution {F : Type*} [Field F] [CharP F 2] (T : Finset F) (h0 : (0 : F) ∉ T)
    (hT : T.card ≤ 6) (h1 : ∑ x ∈ T, x = 0) (h3 : ∑ x ∈ T, x ^ 3 = 0) (h5 : ∑ x ∈ T, x ^ 5 = 0) :
    T = ∅ :=
  pk_bch6_independent T h0 hT h1 h3 h5

#print axioms solution
