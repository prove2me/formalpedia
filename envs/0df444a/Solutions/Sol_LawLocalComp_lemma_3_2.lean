-- Prove2me | solution 1 for LawLocalComp.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-17T14:47:14.851195+00:00
-- url     : https://prove2.me/submissions/f52ee5c9-7636-406a-8f65-725e36b1108c

import Mathlib

private lemma card_filter_interval (N : ℕ) {a b : ℝ} (hab : a < b) :
    ((Finset.range N).filter (fun i : ℕ => a < (i : ℝ) ∧ (i : ℝ) < b)).card ≤ b - a + 1 := by
  classical
  by_cases hb0 : 0 ≤ b
  · set lo : ℕ := if 0 ≤ a then Nat.floor a + 1 else 0 with hlo_def
    set hi : ℕ := Nat.floor b with hhi_def
    have hsub : (Finset.range N).filter (fun i : ℕ => a < (i : ℝ) ∧ (i : ℝ) < b) ⊆
        Finset.Ico lo (hi + 1) := by
      intro i hi_mem
      rw [Finset.mem_filter] at hi_mem
      rw [Finset.mem_Ico]
      constructor
      · rw [hlo_def]
        split_ifs with ha
        · have hlt : Nat.floor a < i := (Nat.floor_lt ha).mpr hi_mem.2.1
          omega
        · exact Nat.zero_le i
      · have hb_lt : (b : ℝ) < (hi : ℝ) + 1 := by
          rw [hhi_def]
          exact Nat.lt_floor_add_one b
        have hlt : (i : ℝ) < (hi : ℝ) + 1 := lt_trans hi_mem.2.2 hb_lt
        exact_mod_cast hlt
    have hhi_le : (hi : ℝ) ≤ b := by
      rw [hhi_def]
      exact Nat.floor_le hb0
    have hnonneg : (0 : ℝ) ≤ b - a + 1 := by linarith
    have hcast : ((hi + 1 - lo : ℕ) : ℝ) ≤ b - a + 1 := by
      rw [hlo_def]
      split_ifs with ha
      · by_cases hle : Nat.floor a + 1 ≤ hi + 1
        · have hcast' : ((hi + 1 - (Nat.floor a + 1) : ℕ) : ℝ) =
              (hi : ℝ) + 1 - ((Nat.floor a : ℝ) + 1) := by
            rw [Nat.cast_sub hle]
            push_cast
            ring
          rw [hcast']
          have hlo_lt : a - 1 < (Nat.floor a : ℝ) := by
            linarith [Nat.lt_floor_add_one a]
          linarith
        · have hzero : hi + 1 - (Nat.floor a + 1) = 0 := by omega
          rw [hzero]
          simpa using hnonneg
      · have h1 : ((hi + 1 - 0 : ℕ) : ℝ) ≤ b + 1 := by
          rw [Nat.sub_zero]
          push_cast
          linarith
        have ha_neg : a < 0 := lt_of_not_ge ha
        linarith
    have h1 : (((Finset.range N).filter (fun i : ℕ => a < (i : ℝ) ∧ (i : ℝ) < b)).card : ℝ) ≤
        ((Finset.Ico lo (hi + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : ((Finset.Ico lo (hi + 1)).card : ℝ) = ((hi + 1 - lo : ℕ) : ℝ) := by
      rw [Nat.card_Ico]
    calc (((Finset.range N).filter (fun i : ℕ => a < (i : ℝ) ∧ (i : ℝ) < b)).card : ℝ)
        ≤ ((Finset.Ico lo (hi + 1)).card : ℝ) := h1
      _ = ((hi + 1 - lo : ℕ) : ℝ) := h2
      _ ≤ b - a + 1 := hcast
  · have hbneg : b < 0 := lt_of_not_ge hb0
    have hempty : (Finset.range N).filter (fun i : ℕ => a < (i : ℝ) ∧ (i : ℝ) < b) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i hi h
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith [h.2]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

theorem solution (m H : ℕ) (hm : 1 ≤ m) (hH : 1 ≤ H) (A : ℝ) (hA : 0 < A) (s : ℕ) (hs : 1 ≤ s)
    (c : Fin s → ℝ) (hc : ∀ j, 0 < c j) (hsmall : (s : ℝ) < m * H / 4) :
    (m * H : ℝ) / 2 ≤ ((Finset.range (m * H)).filter (fun i => ∀ j, (H : ℝ) / (16 * s) ≤
      |Real.log (A * (1 + 1 / (m : ℝ)) ^ i) - Real.log (c j)|)).card := by
  classical
  let N : ℕ := m * H
  let δ : ℝ := (H : ℝ) / (16 * s)
  let L : ℝ := Real.log (1 + 1 / (m : ℝ))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hbase : 0 < 1 + 1 / (m : ℝ) := by positivity
  have hLpos : 0 < L := by
    dsimp only [L]
    have hpos : 0 < 1 / (m : ℝ) := by positivity
    exact Real.log_pos (by linarith)
  have hLge : 1 / (2 * (m : ℝ)) ≤ L := by
    dsimp only [L]
    have h := Real.le_log_one_add_of_nonneg (x := 1 / (m : ℝ)) (by positivity)
    have h2 : (2 * (1 / (m : ℝ))) / ((1 / (m : ℝ)) + 2) = 2 / (1 + 2 * (m : ℝ)) := by
      field_simp
    rw [h2] at h
    have : 1 / (2 * (m : ℝ)) ≤ 2 / (1 + 2 * (m : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hm1]
    exact this.trans h
  have hδpos : 0 < δ := by
    dsimp only [δ]
    positivity
  let badj : Fin s → Finset ℕ := fun j => (Finset.range N).filter
    (fun i => |Real.log (A * (1 + 1 / (m : ℝ)) ^ i) - Real.log (c j)| < δ)
  let bad : Finset ℕ := (Finset.range N).filter
    (fun i => ∃ j, |Real.log (A * (1 + 1 / (m : ℝ)) ^ i) - Real.log (c j)| < δ)
  have hbad_card : ∀ j : Fin s, (badj j).card ≤ 2 * δ / L + 1 := by
    intro j
    let y : ℝ := Real.log (c j) - Real.log A
    let a : ℝ := (y - δ) / L
    let b : ℝ := (y + δ) / L
    have hab : a < b := by
      dsimp only [a, b]
      exact div_lt_div_of_pos_right (by linarith) hLpos
    have hsub : badj j ⊆ (Finset.range N).filter (fun i : ℕ => a < (i : ℝ) ∧ (i : ℝ) < b) := by
      intro i hi_mem
      rw [Finset.mem_filter] at hi_mem ⊢
      obtain ⟨hiN, hib⟩ := hi_mem
      refine ⟨hiN, ?_⟩
      have hlog : Real.log (A * (1 + 1 / (m : ℝ)) ^ i) = Real.log A + (i : ℝ) * L := by
        rw [Real.log_mul hA.ne' (pow_pos hbase i).ne', Real.log_pow]
      rw [hlog] at hib
      have hlt : |(i : ℝ) * L - y| < δ := by
        dsimp only [y]
        have : Real.log A + (i : ℝ) * L - Real.log (c j) =
            (i : ℝ) * L - (Real.log (c j) - Real.log A) := by ring
        rwa [this] at hib
      have hlt' := abs_lt.mp hlt
      constructor
      · dsimp only [a]
        rw [div_lt_iff₀ hLpos]
        linarith [hlt'.1]
      · dsimp only [b]
        rw [lt_div_iff₀ hLpos]
        linarith [hlt'.2]
    have hcard := Finset.card_le_card hsub
    have hbound := card_filter_interval N hab
    have hb_eq : b - a = 2 * δ / L := by
      dsimp only [a, b]
      field_simp
      ring
    have hcard' : ((badj j).card : ℝ) ≤
        (((Finset.range N).filter (fun i : ℕ => a < (i : ℝ) ∧ (i : ℝ) < b)).card : ℝ) := by
      exact_mod_cast hcard
    calc ((badj j).card : ℝ)
        ≤ (((Finset.range N).filter (fun i : ℕ => a < (i : ℝ) ∧ (i : ℝ) < b)).card : ℝ) := hcard'
      _ ≤ b - a + 1 := hbound
      _ = 2 * δ / L + 1 := by rw [hb_eq]
  have hbad_eq : bad = Finset.univ.biUnion badj := by
    ext i
    simp only [bad, badj, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hiN, j, hj⟩
      exact ⟨j, hiN, hj⟩
    · rintro ⟨j, hiN, hj⟩
      exact ⟨hiN, j, hj⟩
  have hbad_sum : (bad.card : ℝ) ≤ (s : ℝ) * (2 * δ / L + 1) := by
    have h1 : (Finset.univ.biUnion badj).card ≤ ∑ j, (badj j).card := by
      simpa using (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin s))) (t := badj))
    have h2 : (∑ j : Fin s, ((badj j).card : ℝ)) ≤ ∑ _j : Fin s, (2 * δ / L + 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact hbad_card j
    have h3 : (∑ _j : Fin s, (2 * δ / L + 1)) = (s : ℝ) * (2 * δ / L + 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (bad.card : ℝ) = ((Finset.univ.biUnion badj).card : ℝ) := by rw [hbad_eq]
      _ ≤ ((∑ j, (badj j).card : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (∑ j : Fin s, ((badj j).card : ℝ)) := by push_cast; rfl
      _ ≤ ∑ _j : Fin s, (2 * δ / L + 1) := h2
      _ = (s : ℝ) * (2 * δ / L + 1) := h3
  have hsmall' : (s : ℝ) * (2 * δ / L + 1) < (m * H : ℝ) / 2 := by
    have hfrac : 2 * δ / L = (H : ℝ) / (8 * (s : ℝ) * L) := by
      dsimp only [δ]
      field_simp
      ring
    rw [hfrac]
    have h_two_m_L : (1 : ℝ) ≤ 2 * (m : ℝ) * L := by
      have := hLge
      rw [div_le_iff₀ (by positivity : 0 < 2 * (m : ℝ))] at this
      linarith
    have hstep : (H : ℝ) / (8 * (s : ℝ) * L) ≤ (m : ℝ) * H / 4 := by
      rw [div_le_iff₀ (by positivity : 0 < 8 * (s : ℝ) * L)]
      have hHs : (0 : ℝ) < H * s := by positivity
      nlinarith [h_two_m_L, hHR, hs1]
    have hrewrite : (s : ℝ) * ((H : ℝ) / (8 * (s : ℝ) * L) + 1) =
        (H : ℝ) / (8 * L) + s := by
      field_simp
    rw [hrewrite]
    have hsmall'' : (s : ℝ) < (m : ℝ) * H / 4 := by
      simpa [Nat.cast_mul] using hsmall
    have hfrac2 : (H : ℝ) / (8 * L) ≤ (m : ℝ) * H / 4 := by
      rw [div_le_iff₀ (by positivity : 0 < 8 * L)]
      nlinarith [h_two_m_L, hHR, hm1]
    linarith
  have hbad_lt : (bad.card : ℝ) < (N : ℝ) / 2 := by
    calc (bad.card : ℝ) ≤ (s : ℝ) * (2 * δ / L + 1) := hbad_sum
      _ < (m * H : ℝ) / 2 := hsmall'
      _ = (N : ℝ) / 2 := by simp [N, Nat.cast_mul]
  let good : Finset ℕ := (Finset.range N).filter
    (fun i => ∀ j, δ ≤ |Real.log (A * (1 + 1 / (m : ℝ)) ^ i) - Real.log (c j)|)
  have hgood_eq : good = (Finset.range N) \ bad := by
    ext i
    constructor
    · intro hi
      dsimp only [good] at hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_sdiff]
      refine ⟨hi.1, ?_⟩
      intro hbad
      dsimp only [bad] at hbad
      rw [Finset.mem_filter] at hbad
      obtain ⟨-, j, hj⟩ := hbad
      exact absurd hj (not_lt.mpr (hi.2 j))
    · intro hi
      rw [Finset.mem_sdiff] at hi
      dsimp only [good]
      rw [Finset.mem_filter]
      refine ⟨hi.1, fun j => ?_⟩
      by_contra hlt
      exact hi.2 (by
        dsimp only [bad]
        rw [Finset.mem_filter]
        exact ⟨hi.1, j, lt_of_not_ge hlt⟩)
  have hgood_card : (good.card : ℝ) = (N : ℝ) - (bad.card : ℝ) := by
    rw [hgood_eq, Finset.card_sdiff]
    have hsub : bad ⊆ Finset.range N := by
      intro i hi
      dsimp only [bad] at hi
      rw [Finset.mem_filter] at hi
      exact hi.1
    have h1 : bad ∩ Finset.range N = bad := Finset.inter_eq_left.mpr hsub
    rw [h1, Finset.card_range]
    have hle : bad.card ≤ N := by
      calc bad.card ≤ (Finset.range N).card := Finset.card_le_card hsub
        _ = N := Finset.card_range N
    rw [Nat.cast_sub hle]
  have hfinal : (m * H : ℝ) / 2 ≤ (good.card : ℝ) := by
    rw [hgood_card]
    have hbad_lt' : (bad.card : ℝ) < (m * H : ℝ) / 2 := by
      simpa [N, Nat.cast_mul] using hbad_lt
    have hN : (N : ℝ) = (m * H : ℝ) := by simp [N, Nat.cast_mul]
    rw [hN]
    linarith
  dsimp only [good, δ, N] at hfinal ⊢
  exact hfinal

