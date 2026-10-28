-- Prove2me | solution 1 for MultiLayerCake.LongKnives.counting_claim
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:39:49.613886+00:00
-- url     : https://prove2.me/submissions/6a8b37dc-996c-4fa0-b3f0-91b458cfdc2b

import Mathlib



theorem solution {N q : ℕ} (π : Fin (N + 1) → Fin q) (jStar : Fin q)
    (hb : π (Fin.last N) = jStar)
    (hstar : (Finset.univ.filter (fun i => π i = jStar)).card = N / q + 1)
    (hother : ∀ j, j ≠ jStar → N / q ≤ (Finset.univ.filter (fun i => π i = j)).card ∧
      (Finset.univ.filter (fun i => π i = j)).card ≤ ⌈(N : ℚ) / q⌉₊) :
    ∀ j, (N + 1) / q ≤ (Finset.univ.filter (fun i => π i = j)).card ∧
      (Finset.univ.filter (fun i => π i = j)).card ≤ ⌈((N + 1 : ℕ) : ℚ) / q⌉₊ := by
  have hq : 0 < q := Fin.pos jStar
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hA1 : N / q * q ≤ N := Nat.div_mul_le_self N q
  have hA2 : N < N / q * q + q := Nat.lt_div_mul_add hq
  have hK1 : (N + 1) / q * q ≤ N + 1 := Nat.div_mul_le_self (N + 1) q
  have hK2 : N + 1 < (N + 1) / q * q + q := Nat.lt_div_mul_add hq
  have hka : (N + 1) / q ≤ N / q + 1 := by
    by_contra h
    push_neg at h
    have : (N / q + 2) * q ≤ (N + 1) / q * q := Nat.mul_le_mul_right q h
    nlinarith
  have hak : N / q ≤ (N + 1) / q := Nat.div_le_div_right (by omega)
  have hupStar : N / q + 1 ≤ ⌈((N + 1 : ℕ) : ℚ) / q⌉₊ := by
    apply Nat.succ_le_of_lt
    rw [Nat.lt_ceil, lt_div_iff₀ hqQ]
    have : ((N / q * q : ℕ) : ℚ) ≤ N := by exact_mod_cast hA1
    push_cast at this ⊢
    linarith
  have hceilmono : ⌈(N : ℚ) / q⌉₊ ≤ ⌈((N + 1 : ℕ) : ℚ) / q⌉₊ := by
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hqQ.le
    push_cast; linarith
  intro j
  by_cases hj : j = jStar
  · subst hj
    rw [hstar]
    exact ⟨hka, hupStar⟩
  · refine ⟨?_, le_trans (hother j hj).2 hceilmono⟩
    by_cases hk : (N + 1) / q ≤ N / q
    · exact le_trans hk (hother j hj).1
    · push_neg at hk
      have hk' : (N + 1) / q = N / q + 1 := by omega
      have hNk : N < q * ((N + 1) / q) := by rw [hk']; nlinarith
      have hceil : ⌈(N : ℚ) / q⌉₊ ≤ (N + 1) / q := by
        rw [Nat.ceil_le, div_le_iff₀ hqQ]
        have : (N : ℚ) < ((q * ((N + 1) / q) : ℕ) : ℚ) := by exact_mod_cast hNk
        push_cast at this
        linarith
      have hle : ∀ i ∈ Finset.univ.erase j,
          (Finset.univ.filter (fun x => π x = i)).card ≤ (N + 1) / q := by
        intro i hi
        by_cases his : i = jStar
        · rw [his, hstar, hk']
        · exact le_trans (hother i his).2 hceil
      have hsum : N + 1 = ∑ i : Fin q, (Finset.univ.filter (fun x => π x = i)).card := by
        have := Finset.card_eq_sum_card_fiberwise (f := π) (s := Finset.univ) (t := Finset.univ)
          (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
        simpa using this
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsum
      have h2 := Finset.sum_le_sum hle
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] at h2
      have hqk : (q - 1) * ((N + 1) / q) + (N + 1) / q = q * ((N + 1) / q) := by
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      have hK1' : q * ((N + 1) / q) ≤ N + 1 := by rw [mul_comm]; exact hK1
      omega
