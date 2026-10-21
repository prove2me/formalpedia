-- Prove2me | solution 1 for LimitedPriceChanges.LowerBound.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:18:50.854047+00:00
-- url     : https://prove2.me/submissions/684f750d-8eaa-4aef-8b9c-156670de4c0d

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Hierarchy

set_option autoImplicit false
open LimitedPriceChanges.LowerBound

noncomputable def dl (m T : ℕ) : ℝ := (T : ℝ) ^ (-(1 : ℝ) / (2 * ((m : ℝ) + 1)))

lemma eps_eq (m T : ℕ) (l : Fin (m + 1)) : eps m T l = (dl m T) ^ (l : ℕ) := by
  unfold eps dl
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg T)]
  congr 1
  ring

lemma dl_pos (m T : ℕ) (hT : 1 ≤ T) : 0 < dl m T :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hT) _

lemma dl_small (m : ℕ) : ∃ T1 : ℕ, 1 ≤ T1 ∧ ∀ T ≥ T1, dl m T ≤ 1 / 4 := by
  refine ⟨4 ^ (2 * (m + 1)), Nat.one_le_pow _ _ (by norm_num), fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (Nat.one_le_pow _ _ (by norm_num)) hT
  have hT0 : (0 : ℝ) < T := Nat.cast_pos.mpr hT1
  have h1 : (dl m T) ^ (2 * (m + 1)) = (T : ℝ)⁻¹ := by
    unfold dl
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    have : (-(1 : ℝ) / (2 * ((m : ℝ) + 1))) * ((2 * (m + 1) : ℕ) : ℝ) = -1 := by
      push_cast; field_simp
    rw [this, Real.rpow_neg_one]
  have h2 : (T : ℝ)⁻¹ ≤ ((1 : ℝ) / 4) ^ (2 * (m + 1)) := by
    rw [one_div, inv_pow]
    apply inv_anti₀ (by positivity)
    exact_mod_cast hT
  by_contra hc
  push_neg at hc
  have := pow_lt_pow_left₀ hc (by norm_num) (by omega : 2 * (m + 1) ≠ 0)
  linarith

/-- the sign sequence as a function on ℕ -/
noncomputable def sg (m : ℕ) (ζ : SignVector m) (k : ℕ) : ℝ :=
  if h : k < m + 1 then sign (ζ ⟨k, h⟩) else 0

lemma zz_eq (m T : ℕ) (ζ : SignVector m) :
    zz m T ζ = 1 / 2 + (1 / 4 : ℝ) * ∑ k ∈ Finset.range (m + 1), sg m ζ k * (dl m T) ^ k := by
  unfold zz
  congr 2
  rw [← Fin.sum_univ_eq_sum_range (fun k => sg m ζ k * (dl m T) ^ k)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [eps_eq]
  simp [sg, l.isLt]

lemma sign_abs (b : Bool) : |sign b| = 1 := by
  cases b <;> simp [sign]

lemma sg_abs (m : ℕ) (ζ : SignVector m) (k : ℕ) : |sg m ζ k| ≤ 1 := by
  unfold sg
  split_ifs
  · rw [sign_abs]
  · simp

lemma geom_bound (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 4) (a b : ℕ) :
    ∑ k ∈ Finset.Ico a b, δ ^ k ≤ δ ^ a * (4 / 3) := by
  have := geom_sum_Ico_le_of_lt_one h0 (by linarith : δ < 1) (m := a) (n := b)
  refine this.trans ?_
  rw [div_eq_mul_inv]
  gcongr
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

lemma zz_mem (m T : ℕ) (hT : 1 ≤ T) (hd : dl m T ≤ 1 / 4) (ζ : SignVector m) :
    zz m T ζ ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ) := by
  have hδ := dl_pos m T hT
  rw [zz_eq]
  have h : |∑ k ∈ Finset.range (m + 1), sg m ζ k * (dl m T) ^ k| ≤ 4 / 3 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range (m + 1), |sg m ζ k * (dl m T) ^ k|
        ≤ ∑ k ∈ Finset.range (m + 1), (dl m T) ^ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_pos (pow_pos hδ k)]
          calc |sg m ζ k| * dl m T ^ k ≤ 1 * dl m T ^ k := by
                gcongr; exact sg_abs m ζ k
            _ = _ := one_mul _
      _ = ∑ k ∈ Finset.Ico 0 (m + 1), (dl m T) ^ k := by rw [Finset.range_eq_Ico]
      _ ≤ (dl m T) ^ 0 * (4 / 3) := geom_bound _ hδ.le hd _ _
      _ = 4 / 3 := by simp
  rw [abs_le] at h
  constructor <;> nlinarith [h.1, h.2]

lemma regret_ge (z zh p : ℝ) (hz1 : 1 / 6 ≤ z) (hz2 : z ≤ 5 / 6) (hh1 : 1 / 6 ≤ zh)
    (hh2 : zh ≤ 5 / 6) (hp1 : 1 ≤ p) (hp2 : p ≤ 6) (hn : |zh⁻¹ - p| ≤ |z⁻¹ - p|) :
    (zh - z) ^ 2 / 64 ≤ Gstar z - rev p z := by
  have hz0 : 0 < z := by linarith
  have hh0 : 0 < zh := by linarith
  unfold Gstar rev nu
  rcases le_or_gt (p * z) 2 with hpz | hpz
  · rw [max_eq_right (by linarith)]
    set w := z⁻¹ - p with hw
    have hreg : 1 / (2 * z) - p * (1 - p * z / 2) = z / 2 * w ^ 2 := by
      rw [hw]; field_simp; ring
    rw [hreg]
    have hA : |zh⁻¹ - z⁻¹| ≤ 2 * |w| := by
      calc |zh⁻¹ - z⁻¹| = |(zh⁻¹ - p) - (z⁻¹ - p)| := by ring_nf
        _ ≤ |zh⁻¹ - p| + |z⁻¹ - p| := abs_sub _ _
        _ ≤ 2 * |w| := by rw [hw]; linarith
    have hA2 : (zh⁻¹ - z⁻¹) ^ 2 ≤ 4 * w ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hA 2
      rw [sq_abs, mul_pow, sq_abs] at this
      linarith
    have hrel : zh - z = -(zh⁻¹ - z⁻¹) * (zh * z) := by field_simp; ring
    have hprod : (zh * z) ^ 2 ≤ 1 := by
      have : zh * z ≤ 1 := by nlinarith
      have : 0 ≤ zh * z := by positivity
      nlinarith
    have h3 : (zh - z) ^ 2 ≤ 4 * w ^ 2 := by
      rw [hrel, mul_pow, neg_sq]
      calc (zh⁻¹ - z⁻¹) ^ 2 * (zh * z) ^ 2 ≤ (zh⁻¹ - z⁻¹) ^ 2 * 1 := by
            gcongr
        _ ≤ 4 * w ^ 2 := by linarith
    nlinarith [sq_nonneg w]
  · rw [max_eq_left (by linarith)]
    have h1 : 3 / 5 ≤ 1 / (2 * z) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    nlinarith

theorem solution (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T)
    (hvalid : ∀ ζ : SignVector m, zz m T ζ ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ))
    (zsel : ℝ → SignVector m) (hsel : IsNearest m T zsel)
    (p : ℝ) (hp : p ∈ Set.Icc (1 : ℝ) 6) (ζ : SignVector m) :
    |zz m T (zsel p) - zz m T ζ| ^ 2 / 64 ≤
      Gstar (zz m T ζ) - rev p (zz m T ζ) := by
  rw [sq_abs]
  exact regret_ge _ _ p (hvalid ζ).1 (hvalid ζ).2 (hvalid (zsel p)).1 (hvalid (zsel p)).2 hp.1 hp.2
    (hsel p ζ)
