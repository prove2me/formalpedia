-- Prove2me | solution 1 for GreedyColoringLCA969.LowerBound.Supplement.lemma_4_12
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:30:12.017398+00:00
-- url     : https://prove2.me/submissions/6b85c21a-7813-40bc-83dc-7bc476348665

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false
namespace GreedyColoringLCA969.LowerBound.Supplement

theorem lemma_4_12 (t : ℕ) (ht : 1 ≤ t) (a : ℝ) (ha : 1 ≤ a)
    (F : Fin t → Set.Ioc (0 : ℝ) (1 / 2) → ℕ+)
    (hmono : ∀ i, Antitone (F i))
    (hbase : ∀ (i : Fin t), i.val = 0 → ∀ ε, (F i ε : ℝ) ≤ a * log2 (1 / ε.val))
    (hrec : ∀ (i j : Fin t), j.val + 1 = i.val →
      ∀ (ε η : Set.Ioc (0 : ℝ) (1 / 2)), η.val = ε.val ^ a →
        (F i ε : ℝ) ≤ a * log2 (1 / ε.val) * (F j η : ℝ)) :
    ∀ (i : Fin t), i.val + 1 = t → ∀ ε,
      (F i ε : ℝ) ≤ a^(t * (t + 1) / 2) * (log2 (1 / ε.val))^t := by
  have hL1 : ∀ ε : Set.Ioc (0 : ℝ) (1 / 2), 1 ≤ log2 (1 / ε.val) := by
    intro ε
    obtain ⟨h0, h1⟩ := ε.2
    have h2 : (2 : ℝ) ≤ 1 / ε.val := by rw [le_div_iff₀ h0]; linarith
    unfold log2
    rw [le_div_iff₀ (Real.log_pos (by norm_num)), one_mul]
    exact Real.log_le_log (by norm_num) h2
  have hmem : ∀ ε : Set.Ioc (0 : ℝ) (1 / 2), ε.val ^ a ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    intro ε
    obtain ⟨h0, h1⟩ := ε.2
    refine ⟨Real.rpow_pos_of_pos h0 a, ?_⟩
    have : ε.val ^ a ≤ ε.val ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h0 (by linarith) ha
    rw [Real.rpow_one] at this
    linarith
  have hlog' : ∀ x : ℝ, 0 < x → log2 (1 / x ^ a) = a * log2 (1 / x) := by
    intro x h0
    unfold log2
    rw [one_div, Real.log_inv, Real.log_rpow h0, one_div x, Real.log_inv]
    ring
  have hlog : ∀ ε : Set.Ioc (0 : ℝ) (1 / 2), log2 (1 / ε.val ^ a) = a * log2 (1 / ε.val) :=
    fun ε => hlog' ε.val ε.2.1
  have key : ∀ k : ℕ, ∀ i : Fin t, i.val = k → ∀ ε,
      (F i ε : ℝ) ≤ a ^ ((k + 1) * (k + 2) / 2) * (log2 (1 / ε.val)) ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro i hi ε
      have := hbase i hi ε
      simpa using this
    | succ k ih =>
      intro i hi ε
      have hk : k < t := by have := i.isLt; omega
      set j : Fin t := ⟨k, hk⟩
      set η : Set.Ioc (0 : ℝ) (1 / 2) := ⟨ε.val ^ a, hmem ε⟩
      have h1 := hrec i j (by simp [j]; omega) ε η rfl
      have h2 := ih j rfl η
      have hη : log2 (1 / η.val) = a * log2 (1 / ε.val) := hlog ε
      rw [hη] at h2
      have hLpos : 0 ≤ a * log2 (1 / ε.val) := by
        have := hL1 ε; positivity
      have h3 : (F i ε : ℝ) ≤ a * log2 (1 / ε.val) *
          (a ^ ((k + 1) * (k + 2) / 2) * (a * log2 (1 / ε.val)) ^ (k + 1)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hLpos)
      have hexp : (k + 1 + 1) * (k + 1 + 2) / 2 = (k + 1) * (k + 2) / 2 + (k + 2) := by
        rw [show (k + 1 + 1) * (k + 1 + 2) = (k + 1) * (k + 2) + 2 * (k + 2) by ring,
          Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      rw [hexp]
      calc (F i ε : ℝ) ≤ _ := h3
        _ = a ^ ((k + 1) * (k + 2) / 2 + (k + 2)) * log2 (1 / ε.val) ^ (k + 1 + 1) := by
          rw [pow_add, mul_pow]; ring
  intro i hi ε
  have := key (t - 1) i (by omega) ε
  rwa [show t - 1 + 1 = t by omega, show t - 1 + 2 = t + 1 by omega] at this

end GreedyColoringLCA969.LowerBound.Supplement


open GreedyColoringLCA969.LowerBound GreedyColoringLCA969.LowerBound.Supplement in
theorem solution (t : ℕ) (ht : 1 ≤ t) (a : ℝ) (ha : 1 ≤ a)
    (F : Fin t → Set.Ioc (0 : ℝ) (1 / 2) → ℕ+)
    (hmono : ∀ i, Antitone (F i))
    (hbase : ∀ (i : Fin t), i.val = 0 → ∀ ε, (F i ε : ℝ) ≤ a * log2 (1 / ε.val))
    (hrec : ∀ (i j : Fin t), j.val + 1 = i.val →
      ∀ (ε η : Set.Ioc (0 : ℝ) (1 / 2)), η.val = ε.val ^ a →
        (F i ε : ℝ) ≤ a * log2 (1 / ε.val) * (F j η : ℝ)) :
    ∀ (i : Fin t), i.val + 1 = t → ∀ ε,
      (F i ε : ℝ) ≤ a^(t * (t + 1) / 2) * (log2 (1 / ε.val))^t :=
  GreedyColoringLCA969.LowerBound.Supplement.lemma_4_12 t ht a ha F hmono hbase hrec
