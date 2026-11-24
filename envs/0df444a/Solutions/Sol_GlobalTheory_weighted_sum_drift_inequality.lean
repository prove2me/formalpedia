-- Prove2me | solution 1 for GlobalTheory.weighted_sum_drift_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:47.193455+00:00
-- url     : https://prove2.me/submissions/301f0808-eea6-47a2-887e-3e4af456e738

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_WeightedSumDriftInequality
import Theorems.Thm_GlobalTheory_driftWeight_sq_le
import Theorems.Thm_GlobalTheory_mul_sqrt_le_of_weights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (Y σ : Type) [Fintype σ] (r : ℕ) (t : σ → Y → Y) (α : ℕ → Y → ℝ) (c C B : ℝ), 0 ≤ c → c < 1 → 0 ≤ C → (∀ i ≤ r, ∀ y, 0 ≤ α i y) → (∀ y, α 0 y ≤ B ∧ α r y ≤ B) → (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y)) → ∃ (e : ℕ → ℝ) (c' b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c' ∧ c' < 1 ∧ 0 ≤ b ∧ ∀ y, ∑ s, (∑ i ∈ Finset.Ioo 0 r, e i * α i (t s y)) ≤ Fintype.card σ * (c' * (∑ i ∈ Finset.Ioo 0 r, e i * α i y) + b)) := by
  intro Y σ _ r t α c C B hc0 hc1 hC hα hB halt
  have hrC : 0 ≤ (r : ℝ) * C := mul_nonneg (Nat.cast_nonneg r) hC
  obtain ⟨ε, hε0, hε1, hkey⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ (r : ℝ) * C * ε < 1 - c := by
    have hden : 0 < 2 * ((r : ℝ) * C + 1) := by linarith
    refine ⟨(1 - c) / (2 * ((r : ℝ) * C + 1)), div_pos (by linarith) hden, ?_, ?_⟩
    · rw [div_le_one hden]
      linarith
    · have hεe : (1 - c) / (2 * ((r : ℝ) * C + 1)) * (2 * ((r : ℝ) * C + 1)) = 1 - c :=
        div_mul_cancel₀ _ hden.ne'
      have hpos : 0 < (1 - c) / (2 * ((r : ℝ) * C + 1)) := div_pos (by linarith) hden
      nlinarith [mul_nonneg hrC hpos.le]
  refine ⟨fun i => ε ^ (i * (r - i)), c + (r : ℝ) * C * ε, 2 * (r : ℝ) * C * ε * max B 0,
    fun i => pow_pos hε0 _, add_nonneg hc0 (mul_nonneg hrC hε0.le), by linarith,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg r)) hC) hε0.le)
      (le_max_right _ _), ?_⟩
  intro y
  dsimp only
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = ∑ i ∈ Finset.Ioo 0 r, ε ^ (i * (r - i)) * α i y := ⟨_, rfl⟩
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦ]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (pow_nonneg hε0.le _) (hα i (Finset.mem_Ioo.1 hi).2.le y)
  have hB0 : 0 ≤ B := le_trans (hα 0 (Nat.zero_le _) y) (hB y).1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Φ + 2 * B := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hbd : ∀ k ≤ r, ε ^ (k * (r - k)) * α k y ≤ M := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, zero_mul, pow_zero, one_mul]
      linarith [(hB y).1]
    rcases eq_or_lt_of_le hk with hkr | hkr
    · rw [hkr, Nat.sub_self, mul_zero, pow_zero, one_mul]
      linarith [(hB y).2]
    · have h1 : ε ^ (k * (r - k)) * α k y ≤ Φ := by
        rw [hΦ]
        exact Finset.single_le_sum (f := fun i => ε ^ (i * (r - i)) * α i y)
          (fun i hi => mul_nonneg (pow_nonneg hε0.le _) (hα i (Finset.mem_Ioo.1 hi).2.le y))
          (Finset.mem_Ioo.2 ⟨hk0, hkr⟩)
      linarith
  have hterm : ∀ i ∈ Finset.Ioo 0 r, ∑ s, ε ^ (i * (r - i)) * α i (t s y) ≤
      (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) + (Fintype.card σ : ℝ) * (C * ε * M) := by
    intro i hi
    obtain ⟨hi0, hir⟩ := Finset.mem_Ioo.1 hi
    have hA : 0 ≤ (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 (mul_nonneg (pow_nonneg hε0.le _) (hα i hir.le y)))
    have hB' : 0 ≤ (Fintype.card σ : ℝ) * (C * ε * M) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC hε0.le) hM0)
    rcases halt y i hi0 hir with hcon | ⟨j, hj0, hji, hjr, hint⟩
    · rw [← Finset.mul_sum]
      calc ε ^ (i * (r - i)) * ∑ s, α i (t s y)
          ≤ ε ^ (i * (r - i)) * ((Fintype.card σ : ℝ) * (c * α i y)) :=
            mul_le_mul_of_nonneg_left hcon (pow_nonneg hε0.le _)
        _ = (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) := by ring
        _ ≤ _ := le_add_of_nonneg_right hB'
    · have hs : ∀ s, ε ^ (i * (r - i)) * α i (t s y) ≤ C * ε * M := by
        intro s
        have h1 := driftWeight_sq_le ε hε0.le hε1 r i j hj0 hji hjr
        have h2 := mul_sqrt_le_of_weights (ε ^ (i * (r - i))) (ε ^ ((i - j) * (r - (i - j))))
          (ε ^ ((i + j) * (r - (i + j)))) ε (α (i - j) y) (α (i + j) y) M (pow_nonneg hε0.le _)
          (pow_nonneg hε0.le _) (pow_nonneg hε0.le _) hε0.le (hα _ (by omega) y) (hα _ hjr y) h1
          (hbd _ (by omega)) (hbd _ hjr)
        calc ε ^ (i * (r - i)) * α i (t s y)
            ≤ ε ^ (i * (r - i)) * (C * Real.sqrt (α (i - j) y * α (i + j) y)) :=
              mul_le_mul_of_nonneg_left (hint s) (pow_nonneg hε0.le _)
          _ = C * (ε ^ (i * (r - i)) * Real.sqrt (α (i - j) y * α (i + j) y)) := by ring
          _ ≤ C * (ε * M) := mul_le_mul_of_nonneg_left h2 hC
          _ = C * ε * M := by ring
      calc ∑ s, ε ^ (i * (r - i)) * α i (t s y) ≤ ∑ _s : σ, C * ε * M :=
            Finset.sum_le_sum fun s _ => hs s
        _ = (Fintype.card σ : ℝ) * (C * ε * M) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ _ := le_add_of_nonneg_left hA
  have hcard : ((Finset.Ioo 0 r).card : ℝ) ≤ r := by
    exact_mod_cast (by rw [Nat.card_Ioo]; omega)
  rw [Finset.sum_comm]
  calc ∑ i ∈ Finset.Ioo 0 r, ∑ s, ε ^ (i * (r - i)) * α i (t s y)
      ≤ ∑ i ∈ Finset.Ioo 0 r, ((Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) +
          (Fintype.card σ : ℝ) * (C * ε * M)) := Finset.sum_le_sum hterm
    _ = (Fintype.card σ : ℝ) * (c * Φ) + ((Finset.Ioo 0 r).card : ℝ) * ((Fintype.card σ : ℝ) * (C * ε * M)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, hΦ]
    _ ≤ (Fintype.card σ : ℝ) * (c * Φ) + (r : ℝ) * ((Fintype.card σ : ℝ) * (C * ε * M)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC hε0.le) hM0)))
    _ = (Fintype.card σ : ℝ) * ((c + (r : ℝ) * C * ε) * Φ + 2 * (r : ℝ) * C * ε * max B 0) := by
        rw [max_eq_left hB0, hM]
        ring
    _ = _ := by rw [hΦ]
end GlobalTheory
