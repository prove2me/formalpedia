-- Prove2me | solution 1 for ModernConvex.Relaxations.sum_erase_eq_sum_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:00.424356+00:00
-- url     : https://prove2.me/submissions/c2f843b2-a5f2-4ecb-bfe1-66766f5b8d32

import Mathlib

open scoped BigOperators

/-- Sums over `univ.erase i` are sums over the complement subtype. -/
theorem sum_erase_eq_sum_subtype_proof {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    (∑ j ∈ Finset.univ.erase i, g j) = ∑ j : {j : Fin n // j ≠ i}, g j.1 :=
  Finset.sum_bij
    (fun (a : Fin n) (_ : a ∈ Finset.univ.erase i) =>
      (⟨a, Finset.ne_of_mem_erase ‹a ∈ Finset.univ.erase i›⟩ : {j : Fin n // j ≠ i}))
    (fun _ _ => Finset.mem_univ _)
    (fun a1 _ a2 _ heq => by simpa using heq)
    (fun b _ => ⟨b.1, Finset.mem_erase.mpr ⟨b.2, Finset.mem_univ _⟩, rfl⟩)
    (fun _ _ => rfl)

namespace ModernConvex.Relaxations
end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    (∑ j ∈ Finset.univ.erase i, g j) = ∑ j : {j : Fin n // j ≠ i}, g j.1 :=
  sum_erase_eq_sum_subtype_proof i g
