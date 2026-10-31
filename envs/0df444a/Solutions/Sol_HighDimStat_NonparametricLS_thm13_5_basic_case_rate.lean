-- Prove2me | solution 1 for HighDimStat.NonparametricLS.thm13_5_basic_case_rate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:43:52.618902+00:00
-- url     : https://prove2.me/submissions/ab788954-76da-49e1-807f-b744df85cc11

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core
import Theorems.Thm_HighDimStat_NonparametricLS_local_gaussian_complexity_tail_bound

namespace HighDimStat.NonparametricLS

open MeasureTheory

lemma empiricalNormSq_smul {X : Type*} {n : ℕ} (x : Fin n → X) (c : ℝ) (g : X → ℝ) :
    empiricalNormSq x (fun z => c * g z) = c ^ 2 * empiricalNormSq x g := by
  dsimp [empiricalNormSq]
  have h_term : ∀ i, (c * g (x i)) ^ 2 = c ^ 2 * (g (x i)) ^ 2 := by
    intro i
    ring
  simp_rw [h_term, ← Finset.mul_sum]
  ring

lemma empiricalNorm_smul {X : Type*} {n : ℕ} (x : Fin n → X) {c : ℝ} (hc : 0 ≤ c) (g : X → ℝ) :
    empiricalNorm x (fun z => c * g z) = c * empiricalNorm x g := by
  dsimp [empiricalNorm]
  rw [empiricalNormSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma bddAbove_range_local_gp {X Ω : Type*} {n : ℕ} (hn : 0 < n)
    (x : Fin n → X) (w : Fin n → Ω → ℝ) (H : Set (X → ℝ)) (δn : ℝ) (ω : Ω) :
    BddAbove (Set.range (fun h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn} =>
      |(∑ i, w i ω * h.1 (x i)) / n|)) := by
  let M := Real.sqrt ((∑ i, (w i ω) ^ 2) * (↑n * δn ^ 2)) / ↑n
  refine ⟨M, ?_⟩
  rintro _ ⟨h, rfl⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h_norm : empiricalNorm x h.1 ≤ δn := h.2.2
  by_cases hδn : 0 ≤ δn
  · have h_norm_sq_nonneg : 0 ≤ empiricalNormSq x h.1 := by
      dsimp [empiricalNormSq]
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro i _
        positivity
      · positivity
    have h_norm_sq_le : empiricalNormSq x h.1 ≤ δn ^ 2 := by
      have h1 : Real.sqrt (empiricalNormSq x h.1) ≤ δn := h_norm
      have h2 : (Real.sqrt (empiricalNormSq x h.1)) ^ 2 ≤ δn ^ 2 := by
        have : 0 ≤ Real.sqrt (empiricalNormSq x h.1) := Real.sqrt_nonneg _
        nlinarith
      rwa [Real.sq_sqrt h_norm_sq_nonneg] at h2
    have h_sum_sq_le : ∑ i, (h.1 (x i)) ^ 2 ≤ ↑n * δn ^ 2 := by
      calc
        ∑ i, (h.1 (x i)) ^ 2 = ↑n * ((∑ i, (h.1 (x i)) ^ 2) / ↑n) := by
          rw [mul_div_cancel₀ _ (ne_of_gt hn_pos)]
        _ = ↑n * empiricalNormSq x h.1 := rfl
        _ ≤ ↑n * δn ^ 2 := mul_le_mul_of_nonneg_left h_norm_sq_le hn_nonneg
    have h_cs : (∑ i, w i ω * h.1 (x i)) ^ 2 ≤ (∑ i, (w i ω) ^ 2) * (↑n * δn ^ 2) := by
      have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => w i ω) (fun i => h.1 (x i))
      have h_w_nonneg : 0 ≤ ∑ i, (w i ω) ^ 2 := by positivity
      exact le_trans cs (mul_le_mul_of_nonneg_left h_sum_sq_le h_w_nonneg)
    have h_abs : |∑ i, w i ω * h.1 (x i)| ≤ Real.sqrt ((∑ i, (w i ω) ^ 2) * (↑n * δn ^ 2)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h_cs
    dsimp [M]
    rw [abs_div, abs_of_pos hn_pos]
    exact div_le_div_of_nonneg_right h_abs hn_nonneg
  · have : 0 ≤ empiricalNorm x h.1 := Real.sqrt_nonneg _
    have : 0 ≤ δn := le_trans this h_norm
    contradiction

lemma least_squares_basic_inequality {X Ω : Type*} {n : ℕ} (hn : 0 < n)
    (x : Fin n → X) (w : Fin n → Ω → ℝ) (F : Set (X → ℝ)) (fStar : X → ℝ) (hFstar : fStar ∈ F)
    (σ : ℝ) (y : Ω → Fin n → ℝ) (hy : ∀ ω i, y ω i = fStar (x i) + σ * w i ω)
    (fHat : Ω → (X → ℝ)) (hfHat : ∀ ω, IsLeastSquaresEstimate x F (y ω) (fHat ω))
    (ω : Ω) :
    let Δ : X → ℝ := fun z => fHat ω z - fStar z
    empiricalNormSq x Δ ≤ 2 * σ * ((∑ i, w i ω * Δ (x i)) / n) := by
  intro Δ
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_ls := (hfHat ω).2 fStar hFstar
  have h_id1 : ∀ i, y ω i - fHat ω (x i) = σ * w i ω - Δ (x i) := by
    intro i
    dsimp [Δ]
    rw [hy ω i]
    ring
  have h_id2 : ∀ i, y ω i - fStar (x i) = σ * w i ω := by
    intro i
    rw [hy ω i]
    ring
  have h_sq1 : ∀ i, (y ω i - fHat ω (x i)) ^ 2 =
      (σ * w i ω) ^ 2 - 2 * σ * (w i ω * Δ (x i)) + (Δ (x i)) ^ 2 := by
    intro i
    rw [h_id1 i]
    ring
  have h_sq2 : ∀ i, (y ω i - fStar (x i)) ^ 2 = (σ * w i ω) ^ 2 := by
    intro i
    rw [h_id2 i]
  simp_rw [h_sq1, h_sq2] at h_ls
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h_ls
  rw [← Finset.mul_sum] at h_ls
  have h_diff : ∑ i, (Δ (x i)) ^ 2 ≤ 2 * σ * ∑ i, (w i ω * Δ (x i)) := by
    linarith
  dsimp [empiricalNormSq]
  calc
    (∑ i, (Δ (x i)) ^ 2) / ↑n ≤ (2 * σ * ∑ i, (w i ω * Δ (x i))) / ↑n :=
      div_le_div_of_nonneg_right h_diff hn_pos.le
    _ = 2 * σ * ((∑ i, w i ω * Δ (x i)) / ↑n) := by
      ring

lemma pointwise_bound {n : ℕ} (hn : 0 < n)
    {X : Type*} (x : Fin n → X) (w : Fin n → ℝ) (Δ : X → ℝ)
    (σ δn t : ℝ) (hσ : 0 < σ) (hδn : 0 < δn) (ht : δn ≤ t)
    (h_ls : empiricalNormSq x Δ ≤ 2 * σ * ((∑ i, w i * Δ (x i)) / n))
    (h_bound : 16 * t * δn ≤ empiricalNormSq x Δ) :
    let r := empiricalNorm x Δ
    let α := δn / r
    let h_scaled := fun z => α * Δ z
    2 / σ * δn * Real.sqrt (t * δn) ≤ |(∑ i, w i * h_scaled (x i)) / n| := by
  intro r α h_scaled
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ht_pos : 0 < t := lt_of_lt_of_le hδn ht
  have h16_pos : (0 : ℝ) < 16 := by norm_num
  have h_16tdn_pos : 0 < 16 * t * δn := mul_pos (mul_pos h16_pos ht_pos) hδn
  have h_bound_pos : 0 < empiricalNormSq x Δ := lt_of_lt_of_le h_16tdn_pos h_bound
  have hr_pos : 0 < r := by
    dsimp [r, empiricalNorm]
    exact Real.sqrt_pos.mpr h_bound_pos
  have hr_sq : r ^ 2 = empiricalNormSq x Δ := by
    dsimp [r, empiricalNorm]
    exact Real.sq_sqrt (le_of_lt h_bound_pos)
  have h_sqrt_le : Real.sqrt (16 * t * δn) ≤ r := by
    dsimp [r, empiricalNorm]
    exact Real.sqrt_le_sqrt h_bound
  have h16 : Real.sqrt (16 * t * δn) = 4 * Real.sqrt (t * δn) := by
    have h_assoc : (16 : ℝ) * t * δn = 16 * (t * δn) := by ring
    rw [h_assoc, Real.sqrt_mul (by norm_num) (t * δn)]
    have : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
  rw [h16] at h_sqrt_le
  have h_alpha_nonneg : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (le_of_lt hδn) (le_of_lt hr_pos)
  have h_sum_scaled : (∑ i, w i * h_scaled (x i)) / ↑n = α * ((∑ i, w i * Δ (x i)) / ↑n) := by
    dsimp [h_scaled]
    have : ∀ i, w i * (α * Δ (x i)) = α * (w i * Δ (x i)) := by
      intro i; ring
    simp_rw [this, ← Finset.mul_sum]
    ring
  rw [h_sum_scaled, abs_mul, abs_of_nonneg h_alpha_nonneg]
  have h_abs_le : ((∑ i, w i * Δ (x i)) / ↑n) ≤ |(∑ i, w i * Δ (x i)) / ↑n| := le_abs_self _
  have h_ls_abs : empiricalNormSq x Δ ≤ 2 * σ * |(∑ i, w i * Δ (x i)) / ↑n| := by
    apply le_trans h_ls
    have : 0 ≤ 2 * σ := by linarith
    exact mul_le_mul_of_nonneg_left h_abs_le this
  have h_alpha_normSq : α * empiricalNormSq x Δ ≤ α * (2 * σ * |(∑ i, w i * Δ (x i)) / ↑n|) :=
    mul_le_mul_of_nonneg_left h_ls_abs h_alpha_nonneg
  have h_alpha_calc : α * empiricalNormSq x Δ = δn * r := by
    dsimp [α]
    rw [← hr_sq]
    have : r ^ 2 = r * r := sq r
    rw [this, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hr_pos)]
  rw [h_alpha_calc] at h_alpha_normSq
  have h_lower : 4 * δn * Real.sqrt (t * δn) ≤ δn * r := by
    calc
      4 * δn * Real.sqrt (t * δn) = δn * (4 * Real.sqrt (t * δn)) := by ring
      _ ≤ δn * r := mul_le_mul_of_nonneg_left h_sqrt_le (le_of_lt hδn)
  have h_chain : 4 * δn * Real.sqrt (t * δn) ≤ 2 * σ * (α * |(∑ i, w i * Δ (x i)) / ↑n|) := by
    calc
      4 * δn * Real.sqrt (t * δn) ≤ δn * r := h_lower
      _ ≤ α * (2 * σ * |(∑ i, w i * Δ (x i)) / ↑n|) := h_alpha_normSq
      _ = 2 * σ * (α * |(∑ i, w i * Δ (x i)) / ↑n|) := by ring
  have h2σ_pos : 0 < 2 * σ := by linarith
  rw [mul_comm (2 * σ)] at h_chain
  have h_final := (div_le_iff₀ h2σ_pos).mpr h_chain
  calc
    2 / σ * δn * Real.sqrt (t * δn) = (4 * δn * Real.sqrt (t * δn)) / (2 * σ) := by
      have : σ ≠ 0 := ne_of_gt hσ
      field_simp; ring
    _ ≤ α * |(∑ i, w i * Δ (x i)) / ↑n| := h_final

theorem thm13_5_basic_case_rate {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (x : Fin n → X)
    (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (hw : IsIIDStdGaussian P w)
    (F : Set (X → ℝ)) (fStar : X → ℝ) (hFstar : fStar ∈ F)
    (hStar : IsStarShaped (shiftedClass F fStar))
    (σ : ℝ) (hσ : 0 < σ)
    (y : Ω → Fin n → ℝ) (hy : ∀ ω i, y ω i = fStar (x i) + σ * w i ω)
    (fHat : Ω → (X → ℝ)) (hfHat : ∀ ω, IsLeastSquaresEstimate x F (y ω) (fHat ω))
    (δn t : ℝ) (hδn : SatisfiesCriticalInequality x w P (shiftedClass F fStar) σ δn)
    (ht : δn ≤ t) :
    P.real {ω | 16 * t * δn ≤ empiricalNormSq x (fun z => fHat ω z - fStar z)} ≤
      Real.exp (-(↑n * t * δn) / (2 * σ ^ 2)) := by
  let H := shiftedClass F fStar
  have hH : H.Nonempty := ⟨fun z => fStar z - fStar z, ⟨fStar, hFstar, rfl⟩⟩
  have h_tail := (local_gaussian_complexity_tail_bound hn x w P hw H hStar hH σ δn t hσ hδn ht).1
  have h_subset : {ω | 16 * t * δn ≤ empiricalNormSq x (fun z => fHat ω z - fStar z)} ⊆
      {ω | 2 / σ * δn * Real.sqrt (t * δn) ≤
        ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn},
          |(∑ i, w i ω * h.1 (x i)) / n|} := by
    intro ω hω
    let Δ : X → ℝ := fun z => fHat ω z - fStar z
    have hΔ_in : Δ ∈ H := ⟨fHat ω, (hfHat ω).1, rfl⟩
    have h_ls := least_squares_basic_inequality hn x w F fStar hFstar σ y hy fHat hfHat ω
    let r := empiricalNorm x Δ
    let α := δn / r
    let h_scaled : X → ℝ := fun z => α * Δ z
    have hδn_pos : 0 < δn := hδn.1
    have ht_pos : 0 < t := lt_of_lt_of_le hδn_pos ht
    have h16_pos : (0 : ℝ) < 16 := by norm_num
    have h_16tdn_pos : 0 < 16 * t * δn := mul_pos (mul_pos h16_pos ht_pos) hδn_pos
    have h_bound_pos : 0 < empiricalNormSq x Δ := lt_of_lt_of_le h_16tdn_pos hω
    have hr_pos : 0 < r := by
      dsimp [r, empiricalNorm]
      exact Real.sqrt_pos.mpr h_bound_pos
    have h_sqrt_le : Real.sqrt (16 * t * δn) ≤ r := by
      dsimp [r, empiricalNorm]
      exact Real.sqrt_le_sqrt hω
    have h16 : Real.sqrt (16 * t * δn) = 4 * Real.sqrt (t * δn) := by
      have h_assoc : (16 : ℝ) * t * δn = 16 * (t * δn) := by ring
      rw [h_assoc, Real.sqrt_mul (by norm_num) (t * δn)]
      have : Real.sqrt 16 = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]
    rw [h16] at h_sqrt_le
    have h_dn_le_tdn : δn ^ 2 ≤ t * δn := by
      calc
        δn ^ 2 = δn * δn := sq δn
        _ ≤ t * δn := mul_le_mul_of_nonneg_right ht (le_of_lt hδn.1)
    have h_dn_le_sqrt : δn ≤ Real.sqrt (t * δn) := by
      have h := Real.sqrt_le_sqrt h_dn_le_tdn
      rwa [Real.sqrt_sq (le_of_lt hδn.1)] at h
    have h_dn_le_r : δn ≤ r := by
      calc
        δn ≤ Real.sqrt (t * δn) := h_dn_le_sqrt
        _ ≤ 4 * Real.sqrt (t * δn) := by
          have : 0 ≤ Real.sqrt (t * δn) := Real.sqrt_nonneg _
          linarith
        _ ≤ r := h_sqrt_le
    have h_alpha_icc : α ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · dsimp [α]
        exact div_nonneg (le_of_lt hδn.1) (le_of_lt hr_pos)
      · dsimp [α]
        exact (div_le_one hr_pos).mpr h_dn_le_r
    have h_scaled_in : h_scaled ∈ H := hStar Δ hΔ_in α h_alpha_icc
    have h_scaled_norm : empiricalNorm x h_scaled ≤ δn := by
      dsimp [h_scaled]
      rw [empiricalNorm_smul x h_alpha_icc.1]
      dsimp [α, r]
      rw [div_mul_cancel₀ _ (ne_of_gt hr_pos)]
    let h_sub : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn} := ⟨h_scaled, ⟨h_scaled_in, h_scaled_norm⟩⟩
    have h_pt := pointwise_bound hn x (fun i => w i ω) Δ σ δn t hσ hδn.1 ht h_ls hω
    have h_bdd := bddAbove_range_local_gp hn x w H δn ω
    have h_le_sup : |(∑ i, w i ω * h_scaled (x i)) / ↑n| ≤
        ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn}, |(∑ i, w i ω * h.1 (x i)) / ↑n| :=
      le_ciSup h_bdd h_sub
    exact le_trans h_pt h_le_sup
  have h_mono : P.real {ω | 16 * t * δn ≤ empiricalNormSq x (fun z => fHat ω z - fStar z)} ≤
      P.real {ω | 2 / σ * δn * Real.sqrt (t * δn) ≤
        ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn},
          |(∑ i, w i ω * h.1 (x i)) / n|} :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono h_subset)
  exact le_trans h_mono h_tail

abbrev solution := @thm13_5_basic_case_rate

end HighDimStat.NonparametricLS

abbrev solution := @HighDimStat.NonparametricLS.thm13_5_basic_case_rate

