-- Prove2me | solution 1 for LevyStochCalc.Poisson.prod_sub_one_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T13:50:49.850184+00:00
-- url     : https://prove2.me/submissions/8c61d130-fa30-4f71-ab87-2a7b52a447a6

import Mathlib

open scoped Classical in
theorem solution {α : Type*} {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]
    (key : α → K) (z : α → M) :
    ∀ s : Finset α, Set.InjOn key (s : Set α) →
      (∏ p ∈ s, z p) - 1
        = ∑ p ∈ s, (∏ q ∈ s.filter (fun q => key q < key p), z q) * (z p - 1) := by
  intro s
  induction s using Finset.induction_on_max_value key with
  | empty => intro _; simp
  | insert a s ha hmax ih =>
    intro hinj
    have hinj' : Set.InjOn key (s : Set α) :=
      hinj.mono (by simp [Finset.coe_insert, Set.subset_insert])
    have hlt : ∀ x ∈ s, key x < key a := by
      intro x hx
      refine lt_of_le_of_ne (hmax x hx) ?_
      intro h
      have := hinj (by simp [hx]) (by simp) h
      exact ha (this ▸ hx)
    have hfa : (insert a s).filter (fun q => key q < key a) = s := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, h⟩
        · exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hlt x hx⟩
    have hfp : ∀ p ∈ s, (insert a s).filter (fun q => key q < key p)
        = s.filter (fun q => key q < key p) := by
      intro p hp
      rw [Finset.filter_insert, if_neg (not_lt.mpr (hmax p hp))]
    rw [Finset.sum_insert ha, Finset.prod_insert ha, hfa,
      Finset.sum_congr rfl (fun p hp => by rw [hfp p hp]), ← ih hinj']
    ring
