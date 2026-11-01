-- Prove2me | solution 1 for InhomMJPStrong.J1.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:34:21.981256+00:00
-- url     : https://prove2.me/submissions/fbe164d8-92db-4abd-840c-4d9884989c38

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

open InhomMJPStrong.J1

namespace J1Eq14

lemma le_maxGap' (T U : ℕ → ℝ) {m l : ℕ} (hl1 : 1 ≤ l) (hlm : l ≤ m) :
    |T l - U l| ≤ maxGap T U m := by
  have hne : (Finset.Icc 1 m).Nonempty := ⟨l, Finset.mem_Icc.2 ⟨hl1, hlm⟩⟩
  rw [maxGap, dif_pos hne]
  exact Finset.le_sup' (fun l => |T l - U l|) (Finset.mem_Icc.2 ⟨hl1, hlm⟩)

lemma count_eq (χ : ℕ → ℝ) (hχ : StrictMono χ) {l : ℕ} {t : ℝ} (h1 : χ l ≤ t)
    (h2 : t < χ (l + 1)) : count χ t = l := by
  unfold count
  have : {j : ℕ | 1 ≤ j ∧ χ j ≤ t} = ↑(Finset.Icc 1 l) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.coe_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨hj1, hj2⟩
      refine ⟨hj1, ?_⟩
      have : χ j < χ (l + 1) := lt_of_le_of_lt hj2 h2
      have := hχ.lt_iff_lt.1 this
      omega
    · rintro ⟨hj1, hj2⟩
      exact ⟨hj1, le_trans (hχ.monotone hj2) h1⟩
  rw [this, Set.ncard_coe_finset, Nat.card_Icc]
  omega

end J1Eq14

open J1Eq14 in
theorem solution (χ θ : ℕ → ℝ) (m : ℕ)
    (hχ0 : χ 0 = 0) (hθ0 : θ 0 = 0)
    (hχ : StrictMono χ) (hm : 1 ≤ m) :
    IsGreatest
      ((fun t : ℝ => |timeChange χ θ m t - t|) '' Set.Ici (0 : ℝ))
      (maxGap θ χ m) := by
  have hM0 : 0 ≤ maxGap θ χ m := le_trans (abs_nonneg _) (le_maxGap' θ χ hm le_rfl)
  constructor
  · have hne : (Finset.Icc 1 m).Nonempty := ⟨m, Finset.mem_Icc.2 ⟨hm, le_rfl⟩⟩
    obtain ⟨l, hl, hleq⟩ := Finset.exists_mem_eq_sup' hne (fun l => |θ l - χ l|)
    rw [Finset.mem_Icc] at hl
    refine ⟨χ l, ?_, ?_⟩
    · rw [Set.mem_Ici, ← hχ0]; exact hχ.monotone (Nat.zero_le _)
    · have hval : timeChange χ θ m (χ l) = θ l := by
        unfold timeChange
        by_cases hlm : l = m
        · subst hlm; simp
        · have hlt : l < m := lt_of_le_of_ne hl.2 hlm
          rw [if_neg (not_le.2 (hχ hlt))]
          simp only
          rw [count_eq χ hχ le_rfl (hχ (Nat.lt_succ_self l))]
          simp
      simp only
      rw [hval, maxGap, dif_pos hne, hleq]
  · rintro y ⟨t, ht, rfl⟩
    rw [Set.mem_Ici] at ht
    simp only
    unfold timeChange
    split_ifs with htm
    · have := le_maxGap' θ χ hm le_rfl
      calc |θ m + (t - χ m) - t| = |θ m - χ m| := by ring_nf
        _ ≤ _ := this
    · push_neg at htm
      -- find the interval containing t
      have hex : ∃ j, t < χ (j + 1) := ⟨m - 1, by rw [Nat.sub_add_cancel hm]; exact htm⟩
      classical
      set l := Nat.find hex with hl
      have hl2 : t < χ (l + 1) := Nat.find_spec hex
      have hl1 : χ l ≤ t := by
        rcases Nat.eq_zero_or_pos l with h0 | hpos
        · rw [h0, hχ0]; exact ht
        · obtain ⟨j, hj⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
          have := Nat.find_min hex (show j < l by omega)
          rw [hj]; exact not_lt.1 this
      have hlm : l + 1 ≤ m := by
        have := Nat.find_min' hex (show t < χ (m - 1 + 1) by rw [Nat.sub_add_cancel hm]; exact htm)
        omega
      simp only
      rw [count_eq χ hχ hl1 hl2]
      have hd : 0 < χ (l + 1) - χ l := sub_pos.2 (hχ (Nat.lt_succ_self l))
      set lam := (t - χ l) / (χ (l + 1) - χ l) with hlam
      have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hd.le
      have hlam1 : lam ≤ 1 := (div_le_one hd).2 (by linarith)
      have hrepr : θ l + (t - χ l) * (θ (l + 1) - θ l) / (χ (l + 1) - χ l) - t
          = (1 - lam) * (θ l - χ l) + lam * (θ (l + 1) - χ (l + 1)) := by
        rw [hlam]; field_simp; ring
      have ha : |θ l - χ l| ≤ maxGap θ χ m := by
        rcases Nat.eq_zero_or_pos l with h0 | hpos
        · rw [h0, hθ0, hχ0]; simpa using hM0
        · exact le_maxGap' θ χ hpos (by omega)
      have hb : |θ (l + 1) - χ (l + 1)| ≤ maxGap θ χ m := le_maxGap' θ χ (by omega) hlm
      rw [hrepr]
      calc |(1 - lam) * (θ l - χ l) + lam * (θ (l + 1) - χ (l + 1))|
          ≤ |(1 - lam) * (θ l - χ l)| + |lam * (θ (l + 1) - χ (l + 1))| := abs_add_le _ _
        _ = (1 - lam) * |θ l - χ l| + lam * |θ (l + 1) - χ (l + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam), abs_of_nonneg hlam0]
        _ ≤ (1 - lam) * maxGap θ χ m + lam * maxGap θ χ m := by
          gcongr
        _ = maxGap θ χ m := by ring
