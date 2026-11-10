-- Prove2me | solution 1 for NontruthfulPA.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:34:05.99705+00:00
-- url     : https://prove2.me/submissions/4fb10d7c-9fc8-47ac-a931-4e28ff2fc7ed

import Mathlib
import Definitions.Def_NontruthfulPA_Model
import Definitions.Def_NontruthfulPA_GSPImage

open NontruthfulPA in
theorem solution {k n : ℕ} (hkn : k ≤ n) {α : ℕ → ℝ} (hα : IsPosVec k α) {b : Fin n → ℝ}
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b) :
    Antitone (gspImage k α b) ∧
      ∀ i : Fin n, payS α (padBids (gspImage k α b)) i = payV k α (padBids b) i := by
  obtain ⟨hαpos, hαmono, hαzero⟩ := hα
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = padBids b := ⟨_, rfl⟩
  have hcout : ∀ t, n ≤ t → c t = 0 := by
    intro t ht
    rw [hcdef]; unfold padBids
    rw [dif_neg (show ¬ (t < n) by omega)]
  have hc0 : ∀ t, 0 ≤ c t := by
    intro t
    rw [hcdef]; unfold padBids
    split_ifs
    · exact hb0 _
    · exact le_rfl
  have hcanti : ∀ s t, s ≤ t → c t ≤ c s := by
    intro s t hst
    rw [hcdef]; unfold padBids
    split_ifs with h1 h2 h2
    · exact hb (Fin.mk_le_mk.mpr hst)
    · omega
    · exact hb0 _
    · exact le_rfl
  have hα0 : ∀ j, 0 ≤ α j := by
    intro j
    rcases lt_or_ge j k with h | h
    · exact (hαpos j h).le
    · rw [hαzero j h]
  have hαs : ∀ j, α (j + 1) ≤ α j := by
    intro j
    rcases lt_or_ge (j + 1) k with h | h
    · exact hαmono j (j + 1) (by omega) h
    · rw [hαzero (j + 1) h]; exact hα0 j
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℝ, S = payV k α c := ⟨_, rfl⟩
  have hSexp : ∀ i, S i = ∑ j ∈ Finset.Ico i k, (α j - α (j + 1)) * c (j + 1) := by
    intro i; rw [hSdef]; rfl
  have hS0 : ∀ i, 0 ≤ S i := by
    intro i
    rw [hSexp]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by linarith [hαs j]) (hc0 _)
  have hrec : ∀ i, i < k → S i = (α i - α (i + 1)) * c (i + 1) + S (i + 1) := by
    intro i hi
    rw [hSexp, hSexp, Finset.sum_eq_sum_Ico_succ_bot hi]
  have hSk : ∀ i, k ≤ i → S i = 0 := by
    intro i hi
    rw [hSexp, Finset.Ico_eq_empty_of_le hi, Finset.sum_empty]
  have hP : ∀ d i, k - i = d → S i ≤ α i * c (i + 1) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      rw [hSk i (by omega), hαzero i (by omega), zero_mul]
    | succ d ih =>
      intro i hi
      have hik : i < k := by omega
      rw [hrec i hik]
      have h1 := ih (i + 1) (by omega)
      have h2 := mul_le_mul_of_nonneg_left (hcanti (i + 1) (i + 1 + 1) (by omega)) (hα0 (i + 1))
      linarith
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℝ, F = fun m =>
      if 1 ≤ m ∧ m ≤ k ∧ 0 < α (m - 1) then payV k α (padBids b) (m - 1) / α (m - 1) else 0 :=
    ⟨_, rfl⟩
  have hF : ∀ m, F m = if 1 ≤ m ∧ m ≤ k ∧ 0 < α (m - 1) then S (m - 1) / α (m - 1) else 0 := by
    intro m; rw [hFdef, hSdef, hcdef]
  have hg : ∀ i : Fin n, gspImage k α b i = F (if (i : ℕ) = 0 then 1 else i) := by
    intro i
    rw [hFdef]
    unfold gspImage
    dsimp only
    split_ifs <;> rfl
  have hFin : ∀ m, 1 ≤ m → m ≤ k → F m = S (m - 1) / α (m - 1) := by
    intro m h1 h2
    rw [hF, if_pos (And.intro h1 (And.intro h2 (hαpos (m - 1) (by omega))))]
  have hFout : ∀ m, k < m → F m = 0 := by
    intro m hm
    rw [hF, if_neg (show ¬(1 ≤ m ∧ m ≤ k ∧ 0 < α (m - 1)) from fun h => absurd h.2.1 (by omega))]
  have hF0 : ∀ m, 0 ≤ F m := by
    intro m
    rw [hF]
    split_ifs with h
    · exact div_nonneg (hS0 _) h.2.2.le
    · exact le_rfl
  have hFstep : ∀ m, 1 ≤ m → F (m + 1) ≤ F m := by
    intro m hm
    by_cases hmk : m + 1 ≤ k
    · obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
      have hai : 0 < α i := hαpos i (by omega)
      have hai1 : 0 < α (i + 1) := hαpos (i + 1) (by omega)
      rw [hFin (i + 1 + 1) (by omega) hmk, hFin (i + 1) (by omega) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [div_le_div_iff₀ hai1 hai]
      have hr := hrec i (by omega)
      have h1 := hP (k - (i + 1)) (i + 1) rfl
      have h2 := mul_le_mul_of_nonneg_left (hcanti (i + 1) (i + 1 + 1) (by omega)) (hα0 (i + 1))
      have h3 : S (i + 1) ≤ α (i + 1) * c (i + 1) := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith [hαs i] : (0:ℝ) ≤ α i - α (i + 1))
      rw [hr]
      nlinarith
    · rw [hFout (m + 1) (by omega)]
      exact hF0 m
  have hH : Antitone (fun t => F (t + 1)) := antitone_nat_of_succ_le (fun t => hFstep (t + 1) (by omega))
  have key : ∀ s t, 1 ≤ s → s ≤ t → F t ≤ F s := by
    intro s t hs hst
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    exact hH (show s' ≤ t' by omega)
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hg, hg]
    have hij' : (i : ℕ) ≤ j := hij
    apply key
    · split_ifs <;> omega
    · split_ifs <;> omega
  · show α i * padBids (gspImage k α b) (i + 1) = payV k α (padBids b) i
    rw [← hcdef, ← hSdef]
    unfold padBids
    split_ifs with h
    · rw [hg, if_neg (show ((⟨(i : ℕ) + 1, h⟩ : Fin n) : ℕ) ≠ 0 from Nat.add_one_ne_zero _)]
      show α i * F ((i : ℕ) + 1) = S i
      rcases lt_or_ge (i : ℕ) k with hik | hik
      · have hai : 0 < α i := hαpos i hik
        rw [hFin ((i : ℕ) + 1) (by omega) (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [mul_div_cancel₀ _ hai.ne']
      · rw [hαzero i hik, zero_mul, hSk i hik]
    · rw [mul_zero, hSexp]
      symm
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      rw [hcout (j + 1) (by omega), mul_zero]
