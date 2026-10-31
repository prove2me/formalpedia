-- Prove2me | solution 1 for HighDimStat.NonparametricLS.thm13_13_oracle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:57:14.479982+00:00
-- url     : https://prove2.me/submissions/88865965-6dee-4e4c-b1b1-110d625d6ba7

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core
import Theorems.Thm_HighDimStat_NonparametricLS_local_gaussian_complexity_tail_bound

namespace HighDimStat.NonparametricLS

open MeasureTheory

lemma normSq_le_of_norm_le {X : Type*} {n : ℕ} (x : Fin n → X) (g : X → ℝ) (δ : ℝ)
    (h : empiricalNorm x g ≤ δ) : empiricalNormSq x g ≤ δ ^ 2 :=
  (Real.sqrt_le_iff.mp h).2

lemma bddAbove_range_empProcess {X : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → X)
    (w : Fin n → ℝ) (H : Set (X → ℝ)) (δ : ℝ) :
    BddAbove (Set.range (fun (g : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ}) =>
      |(∑ i, w i * g.1 (x i)) / n|)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  by_cases hne : Nonempty {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ}
  · let M : ℝ := 1 + (∑ i, w i ^ 2) * (max 0 δ) ^ 2 / n
    refine ⟨M, ?_⟩
    rintro y ⟨⟨g, hgH, hgδ⟩, rfl⟩
    have hδ_sq : empiricalNormSq x g ≤ (max 0 δ) ^ 2 := by
      have h1 := normSq_le_of_norm_le x g δ hgδ
      have h2 : δ ≤ max 0 δ := le_max_right 0 δ
      have h3 : 0 ≤ max 0 δ := le_max_left 0 δ
      have h4 : 0 ≤ Real.sqrt (empiricalNormSq x g) := Real.sqrt_nonneg _
      have hδ_nonneg : 0 ≤ δ := le_trans h4 hgδ
      nlinarith
    have hsum_g : ∑ i, (g (x i)) ^ 2 ≤ n * (max 0 δ) ^ 2 := by
      have hdef : empiricalNormSq x g = (∑ i, (g (x i)) ^ 2) / n := rfl
      rw [hdef] at hδ_sq
      have hmul := (div_le_iff₀ hn_pos).mp hδ_sq
      linarith
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun i => g (x i))
    have h_w_nonneg : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hCS2 : (∑ i, w i * g (x i)) ^ 2 ≤ (∑ i, w i ^ 2) * (n * (max 0 δ) ^ 2) := by
      nlinarith
    have h_abs_le : |(∑ i, w i * g (x i)) / n| ≤ 1 + ((∑ i, w i * g (x i)) / n) ^ 2 := by
      have hpos : 0 ≤ |(∑ i, w i * g (x i)) / n| := abs_nonneg _
      have hsq_nonneg : 0 ≤ (|(∑ i, w i * g (x i)) / n| - 1) ^ 2 := sq_nonneg _
      have hring : (|(∑ i, w i * g (x i)) / n| - 1) ^ 2 = (|(∑ i, w i * g (x i)) / n|) ^ 2 - 2 * |(∑ i, w i * g (x i)) / n| + 1 := by ring
      have h_sq : (|(∑ i, w i * g (x i)) / n|) ^ 2 = ((∑ i, w i * g (x i)) / n) ^ 2 := sq_abs _
      linarith
    have hdiv_sq : ((∑ i, w i * g (x i)) / n) ^ 2 ≤ (∑ i, w i ^ 2) * (max 0 δ) ^ 2 / n := by
      have h_le : (∑ i, w i * g (x i)) ^ 2 / (n ^ 2) ≤ ((∑ i, w i ^ 2) * (n * (max 0 δ) ^ 2)) / (n ^ 2) :=
        div_le_div_of_nonneg_right hCS2 (sq_nonneg _)
      have h_cancel : ((∑ i, w i ^ 2) * (n * (max 0 δ) ^ 2)) / (n ^ 2) = (∑ i, w i ^ 2) * (max 0 δ) ^ 2 / n := by
        have : (n : ℝ) ^ 2 = n * n := by ring
        rw [this]
        calc ((∑ i, w i ^ 2) * (n * (max 0 δ) ^ 2)) / (n * n)
          _ = (((∑ i, w i ^ 2) * (max 0 δ) ^ 2) * n) / (n * n) := by ring
          _ = ((∑ i, w i ^ 2) * (max 0 δ) ^ 2) / n := mul_div_mul_right _ _ hn_ne
      rw [div_pow]
      linarith
    linarith
  · rw [not_nonempty_iff] at hne
    have : (Set.range (fun (g : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ}) =>
      |(∑ i, w i * g.1 (x i)) / n|)) = ∅ := Set.range_eq_empty_iff.mpr hne
    rw [this]
    exact bddAbove_empty

lemma empiricalNorm_smul {X : Type*} {n : ℕ} (x : Fin n → X) (h : X → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    empiricalNorm x (fun z => α * h z) = α * empiricalNorm x h := by
  dsimp [empiricalNorm, empiricalNormSq]
  have hsum : ∑ i, (α * h (x i)) ^ 2 = α ^ 2 * ∑ i, (h (x i)) ^ 2 := by
    simp_rw [mul_pow, ← Finset.mul_sum]
  rw [hsum, mul_div_assoc, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα]

lemma abs_empProcess_smul {X : Type*} {n : ℕ} (w : Fin n → ℝ) (x : Fin n → X) (h : X → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    |(∑ i, w i * (α * h (x i))) / n| = α * |(∑ i, w i * h (x i)) / n| := by
  have hsum : ∑ i, w i * (α * h (x i)) = α * ∑ i, w i * h (x i) := by
    simp_rw [mul_left_comm (w _), ← Finset.mul_sum]
  rw [hsum, mul_div_assoc, abs_mul, abs_of_nonneg hα]

lemma basic_inequality {X : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → X)
    (fStar : X → ℝ) (σ : ℝ) (w : Fin n → ℝ) (y : Fin n → ℝ)
    (hy : ∀ i, y i = fStar (x i) + σ * w i)
    (fHat f : X → ℝ)
    (hLS : ∑ i, (y i - fHat (x i)) ^ 2 ≤ ∑ i, (y i - f (x i)) ^ 2) :
    empiricalNormSq x (fun z => fHat z - fStar z) ≤
      empiricalNormSq x (fun z => f z - fStar z) + 2 * σ * ((∑ i, w i * (fHat (x i) - f (x i))) / n) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  dsimp [empiricalNormSq]
  have h1 : ∀ i, (y i - fHat (x i)) ^ 2 =
      (σ * w i) ^ 2 - 2 * (σ * w i) * (fHat (x i) - fStar (x i)) + (fHat (x i) - fStar (x i)) ^ 2 := by
    intro i
    rw [hy i]
    ring
  have h2 : ∀ i, (y i - f (x i)) ^ 2 =
      (σ * w i) ^ 2 - 2 * (σ * w i) * (f (x i) - fStar (x i)) + (f (x i) - fStar (x i)) ^ 2 := by
    intro i
    rw [hy i]
    ring
  have hsum1 : ∑ i, (y i - fHat (x i)) ^ 2 =
      ∑ i, ((σ * w i) ^ 2 - 2 * (σ * w i) * (fHat (x i) - fStar (x i)) + (fHat (x i) - fStar (x i)) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => h1 i)
  have hsum2 : ∑ i, (y i - f (x i)) ^ 2 =
      ∑ i, ((σ * w i) ^ 2 - 2 * (σ * w i) * (f (x i) - fStar (x i)) + (f (x i) - fStar (x i)) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => h2 i)
  rw [hsum1, hsum2] at hLS
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hLS
  have hlin : (∑ i, (fHat (x i) - fStar (x i)) ^ 2) ≤
      (∑ i, (f (x i) - fStar (x i)) ^ 2) + 2 * σ * (∑ i, w i * (fHat (x i) - f (x i))) := by
    have hid : (∑ i, 2 * (σ * w i) * (fHat (x i) - fStar (x i))) - (∑ i, 2 * (σ * w i) * (f (x i) - fStar (x i))) =
        2 * σ * ∑ i, w i * (fHat (x i) - f (x i)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    linarith
  have hdiv := div_le_div_of_nonneg_right hlin (le_of_lt hn_pos)
  rw [add_div, mul_div_assoc] at hdiv
  exact hdiv

lemma process_bound_of_sup_bound {X : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → X)
    (w : Fin n → ℝ) (F : Set (X → ℝ)) (hStar : IsStarShaped (diffClass F))
    (σ δn t : ℝ) (hσ : 0 < σ) (hδn : 0 < δn) (ht : δn ≤ t)
    (h : X → ℝ) (hh_diff : h ∈ diffClass F)
    (hsup : ⨆ g : {h : X → ℝ // h ∈ diffClass F ∧ empiricalNorm x h ≤ δn},
        |(∑ i, w i * g.1 (x i)) / n| ≤ 2 / σ * δn * Real.sqrt (t * δn) ) :
    2 * σ * |(∑ i, w i * h (x i)) / n| ≤ 4 * t * δn + 4 * Real.sqrt (t * δn) * empiricalNorm x h := by
  have hb := bddAbove_range_empProcess hn x w (diffClass F) δn
  have ht_nonneg : 0 ≤ t := le_trans (le_of_lt hδn) ht
  have htdn_nonneg : 0 ≤ t * δn := mul_nonneg ht_nonneg (le_of_lt hδn)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (t * δn) := Real.sqrt_nonneg _
  have hnorm_nonneg : 0 ≤ empiricalNorm x h := Real.sqrt_nonneg _
  by_cases hle : empiricalNorm x h ≤ δn
  · let g : {h : X → ℝ // h ∈ diffClass F ∧ empiricalNorm x h ≤ δn} := ⟨h, ⟨hh_diff, hle⟩⟩
    have h_le_sup : |(∑ i, w i * h (x i)) / n| ≤
        ⨆ g : {h : X → ℝ // h ∈ diffClass F ∧ empiricalNorm x h ≤ δn}, |(∑ i, w i * g.1 (x i)) / n| :=
      le_ciSup hb g
    have h1 : |(∑ i, w i * h (x i)) / n| ≤ 2 / σ * δn * Real.sqrt (t * δn) :=
      le_trans h_le_sup hsup
    have h_mul : 2 * σ * |(∑ i, w i * h (x i)) / n| ≤ 2 * σ * (2 / σ * δn * Real.sqrt (t * δn)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h_simp : 2 * σ * (2 / σ * δn * Real.sqrt (t * δn)) = 4 * (δn * Real.sqrt (t * δn)) := by
      have : σ ≠ 0 := ne_of_gt hσ
      field_simp
      ring
    rw [h_simp] at h_mul
    have h_sq_le : δn ^ 2 ≤ t * δn := by nlinarith [ht, hδn]
    have h_dn_le : δn ≤ Real.sqrt (t * δn) := by
      calc δn = Real.sqrt (δn ^ 2) := (Real.sqrt_sq (le_of_lt hδn)).symm
        _ ≤ Real.sqrt (t * δn) := Real.sqrt_le_sqrt h_sq_le
    have h_prod : δn * Real.sqrt (t * δn) ≤ t * δn := by
      calc δn * Real.sqrt (t * δn)
        _ ≤ Real.sqrt (t * δn) * Real.sqrt (t * δn) :=
          mul_le_mul_of_nonneg_right h_dn_le hsqrt_nonneg
        _ = (Real.sqrt (t * δn)) ^ 2 := by ring
        _ = t * δn := Real.sq_sqrt htdn_nonneg
    have h_extra : 0 ≤ 4 * Real.sqrt (t * δn) * empiricalNorm x h := by positivity
    linarith
  · have hle_lt : δn < empiricalNorm x h := lt_of_not_ge hle
    have hr_pos : 0 < empiricalNorm x h := lt_trans hδn hle_lt
    have hr_ne : empiricalNorm x h ≠ 0 := ne_of_gt hr_pos
    let α : ℝ := δn / empiricalNorm x h
    have hα_pos : 0 < α := div_pos hδn hr_pos
    have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
    have hα_le1 : α ≤ 1 := (div_le_one hr_pos).mpr (le_of_lt hle_lt)
    have hα_mem : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα_nonneg, hα_le1⟩
    have h_scaled_diff : (fun z => α * h z) ∈ diffClass F := hStar h hh_diff α hα_mem
    have h_scaled_norm : empiricalNorm x (fun z => α * h z) ≤ δn := by
      rw [empiricalNorm_smul x h hα_nonneg]
      dsimp [α]
      rw [div_mul_cancel₀ _ hr_ne]
    let g : {h : X → ℝ // h ∈ diffClass F ∧ empiricalNorm x h ≤ δn} :=
      ⟨fun z => α * h z, ⟨h_scaled_diff, h_scaled_norm⟩⟩
    have h_le_sup : |(∑ i, w i * (α * h (x i))) / n| ≤
        ⨆ g : {h : X → ℝ // h ∈ diffClass F ∧ empiricalNorm x h ≤ δn}, |(∑ i, w i * g.1 (x i)) / n| :=
      le_ciSup hb g
    have h1 : |(∑ i, w i * (α * h (x i))) / n| ≤ 2 / σ * δn * Real.sqrt (t * δn) :=
      le_trans h_le_sup hsup
    rw [abs_empProcess_smul w x h hα_nonneg] at h1
    dsimp [α] at h1
    have h2 : |(∑ i, w i * h (x i)) / n| ≤ 2 / σ * Real.sqrt (t * δn) * empiricalNorm x h := by
      have hδn_ne : δn ≠ 0 := ne_of_gt hδn
      have : (δn / empiricalNorm x h) * |(∑ i, w i * h (x i)) / n| * (empiricalNorm x h / δn) ≤
          (2 / σ * δn * Real.sqrt (t * δn)) * (empiricalNorm x h / δn) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have hL : (δn / empiricalNorm x h) * |(∑ i, w i * h (x i)) / n| * (empiricalNorm x h / δn) =
          |(∑ i, w i * h (x i)) / n| := by field_simp
      have hR : (2 / σ * δn * Real.sqrt (t * δn)) * (empiricalNorm x h / δn) =
          2 / σ * Real.sqrt (t * δn) * empiricalNorm x h := by field_simp
      rw [hL, hR] at this
      exact this
    have h3 : 2 * σ * |(∑ i, w i * h (x i)) / n| ≤ 4 * Real.sqrt (t * δn) * empiricalNorm x h := by
      have : σ ≠ 0 := ne_of_gt hσ
      calc 2 * σ * |(∑ i, w i * h (x i)) / n|
        _ ≤ 2 * σ * (2 / σ * Real.sqrt (t * δn) * empiricalNorm x h) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = 4 * Real.sqrt (t * δn) * empiricalNorm x h := by
          field_simp
          ring
    have h_tdn : 0 ≤ 4 * t * δn := by linarith [htdn_nonneg]
    linarith

lemma empiricalNormSq_sub_le {X : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → X) (f g : X → ℝ) :
    empiricalNormSq x (fun z => f z - g z) ≤ 2 * empiricalNormSq x f + 2 * empiricalNormSq x g := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  dsimp [empiricalNormSq]
  have h_pt : ∀ i, (f (x i) - g (x i)) ^ 2 ≤ 2 * (f (x i)) ^ 2 + 2 * (g (x i)) ^ 2 := by
    intro i
    have : 0 ≤ (f (x i) + g (x i)) ^ 2 := sq_nonneg _
    linarith
  have h_sum : ∑ i, (f (x i) - g (x i)) ^ 2 ≤ 2 * ∑ i, (f (x i)) ^ 2 + 2 * ∑ i, (g (x i)) ^ 2 := by
    calc ∑ i, (f (x i) - g (x i)) ^ 2
      _ ≤ ∑ i, (2 * (f (x i)) ^ 2 + 2 * (g (x i)) ^ 2) := Finset.sum_le_sum (fun i _ => h_pt i)
      _ = 2 * ∑ i, (f (x i)) ^ 2 + 2 * ∑ i, (g (x i)) ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h_div := div_le_div_of_nonneg_right h_sum (le_of_lt hn_pos)
  rw [add_div, mul_div_assoc, mul_div_assoc] at h_div
  exact h_div

lemma young_inequality (u v γ : ℝ) (hγ : 0 < γ) :
    4 * u * v ≤ (γ / 2) * v ^ 2 + (8 / γ) * u ^ 2 := by
  have hsq : 0 ≤ (γ * v - 4 * u) ^ 2 := sq_nonneg _
  have hdiv := div_nonneg hsq (by linarith [hγ] : 0 ≤ 2 * γ)
  have h_calc : (γ * v - 4 * u) ^ 2 / (2 * γ) = (γ / 2) * v ^ 2 + (8 / γ) * u ^ 2 - 4 * u * v := by
    field_simp [ne_of_gt hγ]
    ring
  linarith

lemma oracle_algebraic_bound (E_hat E_Delta t_delta γ : ℝ)
    (hγ_pos : 0 < γ) (hγ_lt1 : γ < 1) (ht_delta : 0 ≤ t_delta)
    (h_ineq : (1 - γ) * E_hat ≤ (1 + γ) * E_Delta + (4 + 8 / γ) * t_delta) :
    E_hat ≤ (1 + γ) / (1 - γ) * E_Delta + 16 / (γ * (1 - γ)) * t_delta := by
  have h1γ_pos : 0 < 1 - γ := by linarith
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have h1γ_ne : 1 - γ ≠ 0 := ne_of_gt h1γ_pos
  have h_le8 : 4 ≤ 8 / γ := by
    rw [le_div_iff₀ hγ_pos]
    linarith
  have h_coeff : 4 + 8 / γ ≤ 16 / γ := by
    calc 4 + 8 / γ
      _ ≤ 8 / γ + 8 / γ := by linarith [h_le8]
      _ = 16 / γ := by ring
  have h_term : (4 + 8 / γ) * t_delta ≤ (16 / γ) * t_delta :=
    mul_le_mul_of_nonneg_right h_coeff ht_delta
  have h_id : (1 - γ) * ((1 + γ) / (1 - γ) * E_Delta + 16 / (γ * (1 - γ)) * t_delta) =
      (1 + γ) * E_Delta + (16 / γ) * t_delta := by field_simp
  rw [← mul_le_mul_iff_of_pos_left h1γ_pos]
  rw [h_id]
  linarith

theorem thm13_13_oracle_inequality :
    ∃ c0 c1 c2 : ℝ, 0 < c0 ∧ 0 < c1 ∧ 0 < c2 ∧
      ∀ {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ}, 0 < n →
      ∀ (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P],
        IsIIDStdGaussian P w →
      ∀ (F : Set (X → ℝ)) (fStar : X → ℝ), IsStarShaped (diffClass F) →
      ∀ (σ : ℝ), 0 < σ →
      ∀ (y : Ω → Fin n → ℝ), (∀ ω i, y ω i = fStar (x i) + σ * w i ω) →
      ∀ (fHat : Ω → (X → ℝ)), (∀ ω, IsLeastSquaresEstimate x F (y ω) (fHat ω)) →
      ∀ (δn t : ℝ), SatisfiesCriticalInequality x w P (diffClass F) σ δn → δn ≤ t →
        1 - c1 * Real.exp (-c2 * ↑n * t * δn / σ ^ 2) ≤
          P.real {ω | ∀ f ∈ F, empiricalNormSq x (fun z => fHat ω z - fStar z) ≤
              ⨅ γ : {r : ℝ // r ∈ Set.Ioo (0 : ℝ) 1},
                (1 + γ.1) / (1 - γ.1) * empiricalNormSq x (fun z => f z - fStar z)
                  + c0 / (γ.1 * (1 - γ.1)) * t * δn} := by
  use 16, 1, 1 / 2
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro X Ω instMS n hn x w P instP hw F fStar hStar σ hσ y hy fHat hfHat δn t hδn ht
  rcases isEmpty_or_nonempty Ω with hEmpty | hNonempty
  · exfalso
    have h1 : P Set.univ = 1 := measure_univ
    have h0 : (Set.univ : Set Ω) = ∅ := Set.univ_eq_empty_iff.mpr hEmpty
    rw [h0, measure_empty] at h1
    exact one_ne_zero h1.symm
  · obtain ⟨ω₀⟩ := hNonempty
    have hfHat0 := (hfHat ω₀).1
    have hDiff : (diffClass F).Nonempty :=
      ⟨fun _ => 0, fHat ω₀, hfHat0, fHat ω₀, hfHat0, by ext; ring⟩
    have htail := (local_gaussian_complexity_tail_bound hn x w P hw (diffClass F)
      hStar hDiff σ δn t hσ hδn ht).2
    have h_exp_eq : - (1 / 2 : ℝ) * ↑n * t * δn / σ ^ 2 = - (↑n * t * δn) / (2 * σ ^ 2) := by ring
    have h_lhs_eq : 1 - 1 * Real.exp (- (1 / 2 : ℝ) * ↑n * t * δn / σ ^ 2) =
        1 - Real.exp (- (↑n * t * δn) / (2 * σ ^ 2)) := by
      rw [one_mul, h_exp_eq]
    rw [h_lhs_eq]
    apply le_trans htail
    apply measureReal_mono _ (measure_ne_top P _)
    intro ω hsup
    dsimp at hsup ⊢
    intro f hf
    let Δhat := fun z => fHat ω z - fStar z
    let Δ := fun z => f z - fStar z
    let h := fun z => fHat ω z - f z
    have hh_diff : h ∈ diffClass F := ⟨fHat ω, (hfHat ω).1, f, hf, rfl⟩
    have hLS := (hfHat ω).2 f hf
    have h_basic := basic_inequality hn x fStar σ (w · ω) (y ω) (hy ω) (fHat ω) f hLS
    have h_le_abs : 2 * σ * ((∑ i, w i ω * (fHat ω (x i) - f (x i))) / n) ≤ 2 * σ * |(∑ i, w i ω * h (x i)) / n| := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have : (∑ i, w i ω * (fHat ω (x i) - f (x i))) = ∑ i, w i ω * h (x i) := rfl
      rw [this]
      exact le_abs_self _
    have h_basic2 : empiricalNormSq x Δhat ≤ empiricalNormSq x Δ + 2 * σ * |(∑ i, w i ω * h (x i)) / n| :=
      le_trans h_basic (by linarith)
    have h_proc := process_bound_of_sup_bound hn x (w · ω) F hStar σ δn t hσ hδn.1 ht h hh_diff hsup
    have h_comb : empiricalNormSq x Δhat ≤
        empiricalNormSq x Δ + 4 * t * δn + 4 * Real.sqrt (t * δn) * empiricalNorm x h := by
      linarith
    have h_t_nonneg : 0 ≤ t := le_trans (le_of_lt hδn.1) ht
    have h_tdn_nonneg : 0 ≤ t * δn := mul_nonneg h_t_nonneg (le_of_lt hδn.1)
    have : Nonempty {r : ℝ // r ∈ Set.Ioo (0 : ℝ) 1} := ⟨⟨1 / 2, by constructor <;> norm_num⟩⟩
    apply le_ciInf
    rintro ⟨γ, hγ_pos, hγ_lt1⟩
    dsimp
    have h_young := young_inequality (Real.sqrt (t * δn)) (empiricalNorm x h) γ hγ_pos
    have hu_sq : (Real.sqrt (t * δn)) ^ 2 = t * δn := Real.sq_sqrt h_tdn_nonneg
    have hv_sq : (empiricalNorm x h) ^ 2 = empiricalNormSq x h := by
      dsimp [empiricalNorm]
      have : 0 ≤ empiricalNormSq x h := by
        dsimp [empiricalNormSq]
        exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)
      exact Real.sq_sqrt this
    rw [hu_sq, hv_sq] at h_young
    have h_sub_id : (fun z => Δhat z - Δ z) = h := by
      ext z
      dsimp [Δhat, Δ, h]
      ring
    have h_sub_le : empiricalNormSq x h ≤ 2 * empiricalNormSq x Δhat + 2 * empiricalNormSq x Δ := by
      rw [← h_sub_id]
      exact empiricalNormSq_sub_le hn x Δhat Δ
    have h_scaled_sub : (γ / 2) * empiricalNormSq x h ≤
        γ * empiricalNormSq x Δhat + γ * empiricalNormSq x Δ := by
      calc (γ / 2) * empiricalNormSq x h
        _ ≤ (γ / 2) * (2 * empiricalNormSq x Δhat + 2 * empiricalNormSq x Δ) :=
          mul_le_mul_of_nonneg_left h_sub_le (by linarith)
        _ = γ * empiricalNormSq x Δhat + γ * empiricalNormSq x Δ := by ring
    have h_4uv : 4 * Real.sqrt (t * δn) * empiricalNorm x h ≤
        γ * empiricalNormSq x Δhat + γ * empiricalNormSq x Δ + (8 / γ) * (t * δn) := by
      linarith
    have h_ineq : (1 - γ) * empiricalNormSq x Δhat ≤
        (1 + γ) * empiricalNormSq x Δ + (4 + 8 / γ) * (t * δn) := by
      linarith
    have h_alg := oracle_algebraic_bound (empiricalNormSq x Δhat) (empiricalNormSq x Δ)
      (t * δn) γ hγ_pos hγ_lt1 h_tdn_nonneg h_ineq
    rw [mul_assoc]
    exact h_alg

abbrev solution := @thm13_13_oracle_inequality

end HighDimStat.NonparametricLS

abbrev solution := @HighDimStat.NonparametricLS.thm13_13_oracle_inequality

