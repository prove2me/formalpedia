-- Prove2me | solution 1 for InterdepSOS.RSV.rsv_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:23:56.972518+00:00
-- url     : https://prove2.me/submissions/c7b10387-4ba8-497a-92a9-54905292c654

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting
set_option autoImplicit false
open InterdepSOS.RSV

theorem solution {n : ℕ} (I : Set (Finset (Fin n)))
    (v : Valuation n) (hv : IsValuation v)
    (sel : Finset (Fin n) → Allocation n) (hsel : IsRSVSelector I v sel)
    (B : Finset (Fin n)) : IsMonotoneAlloc (sel B) := by
  classical
  intro i s a b hab hia
  by_contra hib
  have hiB : i ∈ B := (hsel B _).2.1 hia
  -- weights of other agents do not depend on i's signal
  have hother : ∀ j, j ≠ i → rsvWeight v B (Function.update s i a) j = rsvWeight v B (Function.update s i b) j := by
    intro j hj
    unfold rsvWeight
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk
      have : k ∉ insert j Bᶜ := by simp [hiB, Ne.symm hj]
      simp [keepOn, this]
    · simp [keepOn, Function.update_of_ne hk]
  have hsame : ∀ S : Finset (Fin n), i ∉ S →
      ∑ j ∈ S, rsvWeight v B (Function.update s i a) j = ∑ j ∈ S, rsvWeight v B (Function.update s i b) j := by
    intro S hS
    apply Finset.sum_congr rfl
    intro j hj
    exact hother j (fun h => hS (h ▸ hj))
  rcases eq_or_lt_of_le hab with h | h
  · subst h; exact hib hia
  have hstrict : rsvWeight v B (Function.update s i a) i < rsvWeight v B (Function.update s i b) i := by
    unfold rsvWeight
    have key : ∀ x : NNReal, keepOn (insert i Bᶜ) (Function.update s i x) =
        Function.update (keepOn (insert i Bᶜ) s) i x := by
      intro x
      funext k
      by_cases hk : k = i
      · subst hk; simp [keepOn]
      · simp [keepOn, Function.update_of_ne hk]
    rw [key a, key b]
    exact hv.2.2 i _ a b h
  set Sa := sel B (Function.update s i a) with hSa
  set Sb := sel B (Function.update s i b) with hSb
  have h1 := (hsel B (Function.update s i b)).2.2 Sa (hsel B _).1 (hsel B _).2.1
  have h2 := (hsel B (Function.update s i a)).2.2 Sb (hsel B _).1 (hsel B _).2.1
  have hsb : i ∉ Sb := hib
  have e1 : ∑ j ∈ Sb, rsvWeight v B (Function.update s i a) j = ∑ j ∈ Sb, rsvWeight v B (Function.update s i b) j := hsame Sb hsb
  have e2 : ∑ j ∈ Sa, rsvWeight v B (Function.update s i b) j =
      ∑ j ∈ Sa.erase i, rsvWeight v B (Function.update s i a) j + rsvWeight v B (Function.update s i b) i := by
    rw [← Finset.add_sum_erase _ _ hia]
    rw [add_comm]
    congr 1
    exact (hsame (Sa.erase i) (by simp)).symm
  have e3 : ∑ j ∈ Sa, rsvWeight v B (Function.update s i a) j =
      ∑ j ∈ Sa.erase i, rsvWeight v B (Function.update s i a) j + rsvWeight v B (Function.update s i a) i := by
    rw [← Finset.add_sum_erase _ _ hia]; ring
  linarith
