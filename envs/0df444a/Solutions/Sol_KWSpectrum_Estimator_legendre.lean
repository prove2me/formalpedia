-- Prove2me | solution 1 for KWSpectrum.Estimator.legendre
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:06:25.916143+00:00
-- url     : https://prove2.me/submissions/44b732b0-5452-48ef-b527-9c33b135205e

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

open QAlgorithms QAlgorithms.Schur KWSpectrum.Estimator

lemma kw_gibbs_term (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hsupp : 0 < s → 0 < q) :
    s - q ≤ s * Real.log (s / q) ∧ (s * Real.log (s / q) = s - q → s = q) := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨by simp [hq], fun h => ?_⟩
    simp at h; linarith
  · have hqp := hsupp hpos
    have hlog : Real.log (s / q) = - Real.log (q / s) := by
      rw [← Real.log_inv, inv_div]
    have h1 := Real.log_le_sub_one_of_pos (div_pos hqp hpos)
    have hmul : s * (q / s) = q := by field_simp
    refine ⟨?_, fun h => ?_⟩
    · rw [hlog]
      nlinarith
    · by_contra hne
      have h2 := Real.log_lt_sub_one_of_pos (div_pos hqp hpos)
        (by intro h'; rw [div_eq_one_iff_eq hpos.ne'] at h'; exact hne h'.symm)
      rw [hlog] at h
      nlinarith

lemma kw_gibbs {d : ℕ} (s q : Fin d → ℝ) (hs : ∀ j, 0 ≤ s j) (hq : ∀ j, 0 ≤ q j)
    (hsupp : ∀ j, 0 < s j → 0 < q j) (hsum : ∑ j, q j = ∑ j, s j) :
    0 ≤ ∑ j, s j * Real.log (s j / q j) ∧
      (∑ j, s j * Real.log (s j / q j) = 0 → s = q) := by
  have hterm := fun j => kw_gibbs_term (s j) (q j) (hs j) (hq j) (hsupp j)
  have hge : ∑ j, (s j - q j) ≤ ∑ j, s j * Real.log (s j / q j) :=
    Finset.sum_le_sum fun j _ => (hterm j).1
  have h0 : ∑ j, (s j - q j) = 0 := by rw [Finset.sum_sub_distrib, hsum, sub_self]
  refine ⟨by linarith, fun h => ?_⟩
  have hz : ∑ j, (s j * Real.log (s j / q j) - (s j - q j)) = 0 := by
    rw [Finset.sum_sub_distrib, h, h0, sub_self]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by linarith [(hterm j).1])] at hz
  funext j
  exact (hterm j).2 (by linarith [hz j (Finset.mem_univ _)])

lemma kw_Z_pos {d : ℕ} (r : Fin d → ℝ) (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∑ j, r j = 1)
    (η : Fin d → ℝ) : 0 < ∑ α, r α * Real.exp (η α) := by
  obtain ⟨a, ha⟩ : ∃ a, 0 < r a := by
    by_contra hc
    push Not at hc
    have : ∑ j, r j ≤ 0 := Finset.sum_nonpos fun j _ => hc j
    linarith
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hr0 j) (Real.exp_pos _).le)
    ⟨a, Finset.mem_univ _, mul_pos ha (Real.exp_pos _)⟩

theorem solution {d : ℕ} (r s : Fin d → ℝ) (hr : r ∈ SpectrumSet d) (hs : s ∈ SpectrumSet d) :
    rate r s = ⨆ η : Fin d → ℝ,
      (((∑ j : Fin d, η j * s j) - Real.log (∑ α : Fin d, r α * Real.exp (η α)) : ℝ) : EReal) := by
  obtain ⟨_, hr0, hr1⟩ := hr
  obtain ⟨_, hs0, hs1⟩ := hs
  unfold rate
  split_ifs with h
  · obtain ⟨j, hj, hrj⟩ := h
    symm
    rw [iSup_eq_top]
    intro b hb
    induction b using EReal.rec with
    | bot => exact ⟨0, EReal.bot_lt_coe _⟩
    | top => exact absurd hb (lt_irrefl _)
    | coe b =>
      refine ⟨fun k => if k = j then (|b| + 1) / s j else 0, ?_⟩
      have hZ : ∑ α : Fin d, r α * Real.exp ((fun k => if k = j then (|b| + 1) / s j else 0) α)
          = 1 := by
        rw [← hr1]
        apply Finset.sum_congr rfl
        intro α _
        by_cases hα : α = j
        · subst hα; simp [hrj]
        · simp [hα]
      rw [hZ, Real.log_one, sub_zero, EReal.coe_lt_coe_iff]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [div_mul_cancel₀ _ hj.ne']
      linarith [le_abs_self b]
  · push Not at h
    have hsupp : ∀ j, 0 < s j → 0 < r j := fun j hj =>
      lt_of_le_of_ne (hr0 j) (h j hj).symm
    set KL := ∑ j, s j * Real.log (s j / r j) with hKL
    apply le_antisymm
    · -- lower bound
      apply le_of_forall_lt
      intro c hc
      induction c using EReal.rec with
      | bot =>
        exact lt_of_lt_of_le (EReal.bot_lt_coe _)
          (le_iSup (fun η : Fin d → ℝ => (((∑ j : Fin d, η j * s j) -
            Real.log (∑ α : Fin d, r α * Real.exp (η α)) : ℝ) : EReal)) 0)
      | top => exact absurd hc (not_lt.mpr le_top)
      | coe c =>
        rw [EReal.coe_lt_coe_iff] at hc
        set δ := (KL - c) / 2 with hδ
        have hδpos : 0 < δ := by rw [hδ]; linarith
        let η : Fin d → ℝ := fun α => if 0 < s α then Real.log (s α / r α) else Real.log δ
        have hdot : ∑ j, η j * s j = KL := by
          rw [hKL]
          apply Finset.sum_congr rfl
          intro α _
          by_cases hα : 0 < s α
          · simp only [η, if_pos hα]; ring
          · have : s α = 0 := le_antisymm (not_lt.mp hα) (hs0 α)
            simp [this]
        have hZle : ∑ α, r α * Real.exp (η α) ≤ 1 + δ := by
          have : ∑ α, r α * Real.exp (η α) ≤ ∑ α, (s α + δ * r α) := by
            apply Finset.sum_le_sum
            intro α _
            by_cases hα : 0 < s α
            · simp only [η, if_pos hα]
              rw [Real.exp_log (div_pos hα (hsupp α hα)),
                mul_div_cancel₀ _ (hsupp α hα).ne']
              nlinarith [hr0 α]
            · have : s α = 0 := le_antisymm (not_lt.mp hα) (hs0 α)
              simp only [η, if_neg hα, Real.exp_log hδpos, this]
              linarith
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs1, hr1, mul_one] at this
          exact this
        have hZpos := kw_Z_pos r hr0 hr1 η
        have hlog : Real.log (∑ α, r α * Real.exp (η α)) ≤ δ := by
          calc Real.log (∑ α, r α * Real.exp (η α)) ≤ Real.log (1 + δ) :=
                Real.log_le_log hZpos hZle
            _ ≤ (1 + δ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
            _ = δ := by ring
        refine lt_of_lt_of_le ?_ (le_iSup _ η)
        rw [EReal.coe_lt_coe_iff, hdot]
        rw [hδ] at hlog
        linarith
    · -- upper bound
      apply iSup_le
      intro η
      rw [EReal.coe_le_coe_iff]
      set Z := ∑ α, r α * Real.exp (η α) with hZ
      have hZpos : 0 < Z := kw_Z_pos r hr0 hr1 η
      let q : Fin d → ℝ := fun α => r α * Real.exp (η α) / Z
      have hq0 : ∀ j, 0 ≤ q j := fun j =>
        div_nonneg (mul_nonneg (hr0 j) (Real.exp_pos _).le) hZpos.le
      have hqsupp : ∀ j, 0 < s j → 0 < q j := fun j hj =>
        div_pos (mul_pos (hsupp j hj) (Real.exp_pos _)) hZpos
      have hqsum : ∑ j, q j = ∑ j, s j := by
        rw [hs1]
        simp only [q, ← Finset.sum_div]
        rw [← hZ, div_self hZpos.ne']
      have hg := (kw_gibbs s q hs0 hq0 hqsupp hqsum).1
      have hexp : ∑ j, s j * Real.log (s j / q j) =
          KL - ∑ j, η j * s j + (∑ j, s j) * Real.log Z := by
        rw [hKL, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro α _
        by_cases hα : 0 < s α
        · have hrα := hsupp α hα
          simp only [q]
          rw [Real.log_div hα.ne' (div_pos (mul_pos hrα (Real.exp_pos _)) hZpos).ne',
            Real.log_div (mul_pos hrα (Real.exp_pos _)).ne' hZpos.ne',
            Real.log_mul hrα.ne' (Real.exp_pos _).ne', Real.log_exp,
            Real.log_div hα.ne' hrα.ne']
          ring
        · have : s α = 0 := le_antisymm (not_lt.mp hα) (hs0 α)
          simp [this]
      rw [hexp, hs1, one_mul] at hg
      linarith
