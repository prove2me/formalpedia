-- Prove2me | solution 1 for KellerTrotter2017.thm7_9_surjections_positive_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:02:23.076748+00:00
-- url     : https://prove2.me/submissions/b41979d9-c10a-4839-91a2-44be7c915550

import Mathlib

open Finset in
theorem solution (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (Fintype.card {f : Fin n → Fin m // Function.Surjective f} : ℤ) =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ k * (m.choose k : ℤ) * ((m - k : ℕ) : ℤ) ^ n := by
  classical
  let S : Fin m → Finset (Fin n → Fin m) := fun i => univ.filter (fun f => ∀ x, f x ≠ i)
  have hsurj : (univ : Finset (Fin m)).inf (fun i => (S i)ᶜ) =
      univ.filter (fun f : Fin n → Fin m => Function.Surjective f) := by
    ext f
    simp only [Finset.mem_inf, Finset.mem_univ, true_implies, Finset.mem_compl, S,
      Finset.mem_filter, true_and, not_forall, not_not]
    exact Iff.rfl
  have hinf : ∀ t : Finset (Fin m), t.inf S = Fintype.piFinset (fun _ : Fin n => tᶜ) := by
    intro t
    ext f
    simp only [Finset.mem_inf, S, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, Finset.mem_compl]
    constructor
    · intro h x hx; exact h _ hx x rfl
    · intro h i hi x hx; exact h x (hx ▸ hi)
  have hcard : ∀ t : Finset (Fin m), #(t.inf S) = (m - #t) ^ n := by
    intro t
    rw [hinf, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.card_compl, Fintype.card_fin]
  have := Finset.inclusion_exclusion_card_inf_compl (univ : Finset (Fin m)) S
  rw [hsurj] at this
  rw [Fintype.card_subtype, this]
  simp_rw [hcard]
  rw [Finset.sum_powerset_apply_card (f := fun k => (-1 : ℤ) ^ k * (((m - k : ℕ) ^ n : ℕ) : ℤ)),
    Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro k _
  simp only [nsmul_eq_mul]; push_cast; ring
