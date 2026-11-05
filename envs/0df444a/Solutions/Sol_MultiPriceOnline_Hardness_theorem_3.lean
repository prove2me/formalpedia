-- Prove2me | solution 1 for MultiPriceOnline.Hardness.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:52:29.700259+00:00
-- url     : https://prove2.me/submissions/60090c2f-9727-49b7-a22f-546d427f5c84

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Model
import Definitions.Def_MultiPriceOnline_Hardness_Instance
import Theorems.Thm_MultiPriceOnline_Hardness_lemma_4
import Theorems.Thm_MultiPriceOnline_Hardness_eq_25
import Theorems.Thm_MultiPriceOnline_Hardness_lemma_5
import Theorems.Thm_MultiPriceOnline_Hardness_eq_29
import Theorems.Thm_MultiPriceOnline_Hardness_proposition_4

open Finset MeasureTheory MultiPriceOnline.Hardness

theorem solution (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 1 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (α : ℕ → ℝ) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (ε : ℝ) (hε : 0 < ε) :
    ∃ n K : ℕ, ∃ w : Fin K → ℝ, ∃ A : Fin K → Arrival n,
      (∀ a, 0 ≤ w a) ∧ (∑ a, w a) = 1 ∧ (∀ a, IsDeterministic (A a)) ∧
      0 < ∑ a, w a * OPT k m r (A a) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (alg : Ω → OnlineAlg n),
        (∀ a, Measurable (fun ω => revenue k m r (alg ω) (A a))) →
        ∑ a, w a * ∫ ω, revenue k m r (alg ω) (A a) ∂μ
          ≤ (1 - Real.exp (-α 1) + ε) * ∑ a, w a * OPT k m r (A a) := by
  obtain ⟨⟨B, hB, hBm, hBdec⟩, -⟩ := proposition_4 hm hr hα
  -- monotonicity of prices and positivity/monotonicity of B
  have hrmono : ∀ d j : ℕ, 1 ≤ j → j + d ≤ m → r j ≤ r (j + d) := by
    intro d
    induction d with
    | zero => intro j _ _; simp
    | succ d ih =>
      intro j hj hjd
      have h1 := ih j hj (by omega)
      have h2 := hr.2 (j + d) (by omega) (by omega)
      rw [show j + (d + 1) = j + d + 1 by omega]; linarith
  have hr1 : ∀ j, 1 ≤ j → j ≤ m → r 1 ≤ r j := by
    intro j hj hjm
    have := hrmono (j - 1) 1 le_rfl (by omega)
    rwa [show 1 + (j - 1) = j by omega] at this
  have hBpos : ∀ d : ℕ, d ≤ m - 1 → 0 < B (m - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using hBm
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hBdec (m - d) (by omega) (by omega)
      rw [show m - (d + 1) = m - d - 1 by omega]; linarith
  have hBpos' : ∀ j, 1 ≤ j → j ≤ m → 0 < B j := by
    intro j hj hjm
    have := hBpos (m - j) (by omega)
    rwa [show m - (m - j) = j by omega] at this
  -- choose ε'
  have hr1pos : 0 < r 1 := hr.1
  obtain ⟨N₀, hN₀⟩ := lemma_4 hm hr hα hB k hk (ε * r 1) (mul_pos hε hr1pos)
  set n := max N₀ 1 with hn_def
  have hn1 : 1 ≤ n := le_max_right _ _
  have hnN : N₀ ≤ n := le_max_left _ _
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    simp [Fintype.card_perm]
  let e : Equiv.Perm (Fin n) ≃ Fin (Nat.factorial n) := Fintype.equivFinOfCardEq hcard
  -- OPT value independent of π
  set P : ℝ := (k : ℝ) * ∑ g : Fin n, r (phaseOf n m B g) with hP
  set L : ℝ := ∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * n * k with hL
  have hOPT : ∀ π, OPT k m r (hardInstance n k m B π) = P := fun π =>
    (eq_25 hm hr hα hB n k π).1
  have hLP : L ≤ P := by
    have := (eq_25 hm hr hα hB n k (Equiv.refl _)).2.1
    rwa [hOPT] at this
  have hphase : ∀ g : ℕ, 1 ≤ phaseOf n m B g ∧ phaseOf n m B g ≤ m := by
    intro g
    unfold phaseOf
    refine ⟨by omega, ?_⟩
    have := Finset.card_filter_le (Icc 2 m) (fun j => ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ g)
    simp at this
    omega
  have hPlow : (n : ℝ) * k * r 1 ≤ P := by
    have : ∑ _g : Fin n, r 1 ≤ ∑ g : Fin n, r (phaseOf n m B g) :=
      Finset.sum_le_sum (fun g _ => hr1 _ (hphase g).1 (hphase g).2)
    simp at this
    rw [hP]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hnk : (0 : ℝ) < (n : ℝ) * k := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have hPpos : 0 < P := lt_of_lt_of_le (mul_pos hnk hr1pos) hPlow
  have hfact : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  refine ⟨n, Nat.factorial n, fun _ => ((Nat.factorial n : ℝ))⁻¹,
    fun a => hardInstance n k m B (e.symm a), ?_, ?_, ?_, ?_, ?_⟩
  · intro a; positivity
  · simp [Finset.sum_const, Finset.card_univ]
    field_simp
  · intro a t i j
    simp only [hardInstance]
    split_ifs <;> simp
  · simp only [hOPT, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hfact.ne', one_mul]; exact hPpos
  · intro Ω _ μ _ alg hmeas
    have hmeas' : ∀ π : Equiv.Perm (Fin n),
        Measurable (fun ω => revenue k m r (alg ω) (hardInstance n k m B π)) := by
      intro π
      have := hmeas (e π)
      simpa using this
    have h4 := hN₀ n hnN μ alg hmeas'
    -- rewrite LHS
    have hLHS : ∑ a : Fin (Nat.factorial n), ((Nat.factorial n : ℝ))⁻¹ *
        ∫ ω, revenue k m r (alg ω) (hardInstance n k m B (e.symm a)) ∂μ =
        ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
          ∫ ω, revenue k m r (alg ω) (hardInstance n k m B π) ∂μ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Equiv.sum_comp e.symm (fun π => ∫ ω, revenue k m r (alg ω) (hardInstance n k m B π) ∂μ)
    have hRHS : ∑ a : Fin (Nat.factorial n), ((Nat.factorial n : ℝ))⁻¹ *
        OPT k m r (hardInstance n k m B (e.symm a)) = P := by
      simp only [hOPT, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hfact.ne', one_mul]
    rw [hLHS, hRHS]
    -- bound the sSup
    have h5 := lemma_5 hm hr hα hB n k hn1 hk 1 le_rfl hm 1 zero_le_one le_rfl (by
      intro l hl1 hlm
      have hA : Asum m α 1 = 1 := hα.2.1
      rw [hA, sub_self, zero_div]
      exact (hα.1 l hl1 hlm).le)
    have hA : Asum m α 1 = 1 := hα.2.1
    rw [hA, sub_self, zero_div] at h5
    simp only [add_zero] at h5
    have h29 := eq_29 hr hα B n k
    set M : ℝ := (n : ℝ) * k * ∑ l ∈ Icc 1 m, r l * B l * (1 - Real.exp (-α l)) with hM
    have hsup : sSup {v : ℝ | ∃ lam : ℕ → ℝ, (∀ j ∈ Icc 1 m, 0 ≤ lam j) ∧
                (∀ j ∈ Icc 1 (m - 1), lam j ≤ Real.log (B j / B (j + 1))) ∧
                (∑ j ∈ Icc 1 m, lam j) ≤ 1 ∧
                v = ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-lam j)) * k} ≤ M := by
      apply csSup_le
      · refine ⟨_, fun _ => 0, fun _ _ => le_rfl, ?_, by simp, rfl⟩
        intro j hj
        simp only [Finset.mem_Icc] at hj
        apply Real.log_nonneg
        have hb1 := hBpos' (j + 1) (by omega) (by omega)
        have hb2 := hBdec (j + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hb2
        rw [le_div_iff₀ hb1]; linarith
      · rintro v ⟨lam, h0, -, hs, rfl⟩
        exact h5.2 ⟨lam, h0, hs, rfl⟩
    have hF : 0 ≤ 1 - Real.exp (-α 1) := by
      have := Real.exp_le_one_iff.mpr (by linarith [hα.1 1 le_rfl hm] : -α 1 ≤ 0)
      linarith
    have hMP : M ≤ (1 - Real.exp (-α 1)) * P := by
      rw [h29]
      exact mul_le_mul_of_nonneg_left hLP hF
    have heps : ε * r 1 * n * k ≤ ε * P := by
      have := mul_le_mul_of_nonneg_left hPlow hε.le
      nlinarith
    calc ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
          ∫ ω, revenue k m r (alg ω) (hardInstance n k m B π) ∂μ
        ≤ M + ε * r 1 * n * k := by linarith
      _ ≤ (1 - Real.exp (-α 1) + ε) * P := by nlinarith
