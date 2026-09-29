-- Prove2me | solution 1 for LocalSearchFL.MultiSwap.exists_pi_property_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:06:47.997001+00:00
-- url     : https://prove2.me/submissions/d803cdef-4335-498d-9197-740e33ea346f

import Mathlib



namespace LocalSearchFL.MultiSwap

theorem pi_core {α β : Type} [DecidableEq β] (N : Finset α) (g : α → β) :
    ∃ π : Equiv.Perm α,
      (∀ j, π j ∈ N ↔ j ∈ N) ∧
      (∀ j, j ∉ N → π j = j) ∧
      ∀ j ∈ N, 2 * (N.filter (fun x => g x = g j)).card ≤ N.card → g (π j) ≠ g j := by
  classical
  set cs : List β := (N.image g).toList with hcs
  let key : α → ℕ := fun x => cs.idxOf (g x)
  let le : α → α → Bool := fun a b => decide (key a ≤ key b)
  set L := N.toList.mergeSort le with hL
  have hperm : L.Perm N.toList := List.mergeSort_perm _ _
  have hnd : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList N)
  have hmem : ∀ x, x ∈ L ↔ x ∈ N := fun x => by rw [hperm.mem_iff, Finset.mem_toList]
  have hsorted : L.Pairwise (fun a b => le a b = true) := List.pairwise_mergeSort (le := le) (fun a b c h1 h2 => show decide (key a ≤ key c) = true from
      decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
    (fun a b => by
      rcases Nat.le_total (key a) (key b) with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl (show decide (key a ≤ key b) = true from decide_eq_true h))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (show decide (key b ≤ key a) = true from decide_eq_true h))) N.toList
  have hlen : L.length = N.card := by rw [hperm.length_eq, Finset.length_toList]
  set n := L.length with hn
  have hsort' : ∀ a c (ha : a < n) (hc : c < n), a ≤ c → key L[a] ≤ key L[c] := by
    intro a c ha hc hac
    rcases Nat.lt_or_eq_of_le hac with h | h
    · have := List.pairwise_iff_getElem.mp hsorted a c ha hc h
      simpa [le] using this
    · subst h; exact le_rfl
  have hcsmem : ∀ x ∈ N, g x ∈ cs := fun x hx => by
    rw [hcs, Finset.mem_toList]; exact Finset.mem_image_of_mem g hx
  have hLN : ∀ m (hm : m < n), L[m] ∈ N := fun m hm => (hmem _).mp (List.getElem_mem hm)
  have hbetween : ∀ a m c (hc : c < n) (ham : a ≤ m) (hmc : m ≤ c),
      g (L[a]'(by omega)) = g L[c] →
      g (L[m]'(by omega)) = g (L[a]'(by omega)) := by
    intro a m c hc ham hmc hg
    have h1 := hsort' a m (by omega) (by omega) ham
    have h2 := hsort' m c (by omega) hc hmc
    have h3 : key L[a] = key L[c] := by simp only [key, hg]
    have h4 : key (L[m]'(by omega)) = key L[a] := by omega
    simp only [key] at h4
    exact (List.idxOf_inj (hcsmem _ (hLN _ _))).mp h4
  have hcount : ∀ a c (hc : c < n) (hac : a ≤ c), g (L[a]'(by omega)) = g L[c] →
      c + 1 - a ≤ (N.filter (fun x => g x = g (L[a]'(by omega)))).card := by
    intro a c hc hac hg
    let f : ℕ → α := fun m => L.getD m (L[a]'(by omega))
    have hsub : (Finset.Icc a c).image f ⊆ N.filter (fun x => g x = g (L[a]'(by omega))) := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_Icc] at hm
      have hmn : m < n := by omega
      simp only [f, List.getD_eq_getElem _ _ hmn, Finset.mem_filter]
      exact ⟨hLN _ _, hbetween a m c hc hm.1 hm.2 hg⟩
    have hinj : Set.InjOn f (Finset.Icc a c) := by
      intro m1 hm1 m2 hm2 he
      simp only [Finset.coe_Icc, Set.mem_Icc] at hm1 hm2
      simp only [f, List.getD_eq_getElem _ _ (show m1 < n by omega),
        List.getD_eq_getElem _ _ (show m2 < n by omega)] at he
      exact (hnd.getElem_inj_iff).mp he
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj, Nat.card_Icc] at this
  refine ⟨L.formPerm ^ (n / 2), ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ N
    · simp only [hj, iff_true]
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((hmem j).mpr hj)
      rw [List.formPerm_pow_apply_getElem _ hnd]
      exact hLN _ _
    · rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
        (List.formPerm_apply_of_notMem (fun h => hj ((hmem j).mp h))) _]
  · intro j hj
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
        (List.formPerm_apply_of_notMem (fun h => hj ((hmem j).mp h))) _
  · intro j hj hcard heq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((hmem j).mpr hj)
    rw [List.formPerm_pow_apply_getElem _ hnd] at heq
    rw [← hlen] at hcard
    obtain ⟨k, hk, hkg, hkeq⟩ : ∃ k, ∃ hk : k < n, g L[k] = g L[i] ∧ k = (i + n / 2) % n :=
      ⟨(i + n / 2) % n, Nat.mod_lt _ (by omega), heq, rfl⟩
    by_cases hlt : i + n / 2 < n
    · rw [Nat.mod_eq_of_lt hlt] at hkeq
      have := hcount i k hk (by omega) hkg.symm
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hkeq
      have := hcount k i hi (by omega) hkg
      simp only [hkg] at this
      omega

end LocalSearchFL.MultiSwap

open LocalSearchFL.MultiSwap


theorem solution {α β : Type} [DecidableEq β] (N : Finset α) (g : α → β) :
    ∃ π : Equiv.Perm α,
      (∀ j, π j ∈ N ↔ j ∈ N) ∧
      (∀ j, j ∉ N → π j = j) ∧
      ∀ j ∈ N, 2 * (N.filter (fun x => g x = g j)).card ≤ N.card → g (π j) ≠ g j := by
  exact pi_core N g
