-- Prove2me | solution 1 for KellerTrotter2017.thm16_8_erdos_ko_rado_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:59:44.72752+00:00
-- url     : https://prove2.me/submissions/7defaef6-ea58-482b-9c4a-925b7427c172

import Mathlib

theorem solution (n k : ℕ) (hk : 0 < k) (hn : 2 * k ≤ n) :
    IsGreatest {m : ℕ | ∃ 𝒜 : Finset (Finset (Fin n)),
        (∀ A ∈ 𝒜, A.card = k) ∧ (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty) ∧ 𝒜.card = m}
      ((n - 1).choose (k - 1)) := by
  constructor
  · -- the star at 0
    have hn0 : 0 < n := by omega
    let z : Fin n := ⟨0, hn0⟩
    let 𝒜 : Finset (Finset (Fin n)) := (Finset.univ.filter (fun A : Finset (Fin n) => z ∈ A ∧ A.card = k))
    refine ⟨𝒜, fun A hA => (Finset.mem_filter.mp hA).2.2, fun A hA B hB =>
      ⟨z, Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hA).2.1, (Finset.mem_filter.mp hB).2.1⟩⟩, ?_⟩
    -- bijection with (k-1)-subsets of the other n-1 points
    have : 𝒜 = ((Finset.univ.erase z).powersetCard (k - 1)).image (fun B => insert z B) := by
      ext A
      simp only [𝒜, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨hz, hc⟩
        refine ⟨A.erase z, ⟨fun x hx => ?_, ?_⟩, Finset.insert_erase hz⟩
        · simp only [Finset.mem_erase] at hx ⊢; exact ⟨hx.1, Finset.mem_univ _⟩
        · rw [Finset.card_erase_of_mem hz, hc]
      · rintro ⟨B, ⟨hB, hc⟩, rfl⟩
        have hzB : z ∉ B := fun h => by simpa using hB h
        exact ⟨Finset.mem_insert_self _ _, by rw [Finset.card_insert_of_notMem hzB, hc]; omega⟩
    rw [this, Finset.card_image_of_injOn, Finset.card_powersetCard, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    intro B hB C hC hBC
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hB hC
    have hzB : z ∉ B := fun h => by simpa using hB.1 h
    have hzC : z ∉ C := fun h => by simpa using hC.1 h
    simp only at hBC
    rw [← Finset.erase_insert hzB, hBC, Finset.erase_insert hzC]
  · rintro m ⟨𝒜, hsz, hint, rfl⟩
    apply Finset.erdos_ko_rado (r := k)
    · intro A hA B hB
      exact Finset.not_disjoint_iff_nonempty_inter.mpr (hint A hA B hB)
    · exact hsz
    · omega
