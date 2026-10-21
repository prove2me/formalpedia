-- Prove2me | solution 1 for LimitedPriceChanges.LowerBound.separation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:16:30.824325+00:00
-- url     : https://prove2.me/submissions/4f074106-c92c-4008-b94d-192b859f6310

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

lemma sep_core (m T : ℕ) (hT : 1 ≤ T) (hd : dl m T ≤ 1 / 4) (ζ ζ' : SignVector m)
    (l : Fin (m + 1)) (h : ζ l ≠ ζ' l) :
    eps m T l / 8 ≤ |zz m T ζ - zz m T ζ'| := by
  classical
  have hδ := dl_pos m T hT
  set δ := dl m T with hδdef
  have hex : ∃ k : ℕ, ∃ hk : k < m + 1, ζ ⟨k, hk⟩ ≠ ζ' ⟨k, hk⟩ := ⟨l.val, l.isLt, h⟩
  set j := Nat.find hex with hjdef
  have hjl : j ≤ l.val := Nat.find_min' hex ⟨l.isLt, h⟩
  obtain ⟨hjm, hjne⟩ := Nat.find_spec hex
  have hbelow : ∀ k < j, sg m ζ k - sg m ζ' k = 0 := by
    intro k hk
    have := Nat.find_min hex hk
    unfold sg
    by_cases hkm : k < m + 1
    · simp only [hkm, dif_pos]
      push_neg at this
      rw [this hkm]; simp
    · simp [hkm]
  have hdj : |sg m ζ j - sg m ζ' j| = 2 := by
    have e1 : sg m ζ j = sign (ζ ⟨j, hjm⟩) := by unfold sg; rw [dif_pos hjm]
    have e2 : sg m ζ' j = sign (ζ' ⟨j, hjm⟩) := by unfold sg; rw [dif_pos hjm]
    rw [e1, e2]
    revert hjne
    generalize ζ ⟨j, hjm⟩ = a
    generalize ζ' ⟨j, hjm⟩ = b
    intro hab
    cases a <;> cases b <;> simp [sign] at hab ⊢ <;> norm_num
  have hdiff : zz m T ζ - zz m T ζ' =
      (1 / 4 : ℝ) * ∑ k ∈ Finset.range (m + 1), (sg m ζ k - sg m ζ' k) * δ ^ k := by
    rw [zz_eq, zz_eq]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hsplit : ∑ k ∈ Finset.range (m + 1), (sg m ζ k - sg m ζ' k) * δ ^ k =
      (sg m ζ j - sg m ζ' j) * δ ^ j +
        ∑ k ∈ Finset.Ico (j + 1) (m + 1), (sg m ζ k - sg m ζ' k) * δ ^ k := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ m + 1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : j < m + 1)]
    have : ∑ k ∈ Finset.range j, (sg m ζ k - sg m ζ' k) * δ ^ k = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [hbelow k (Finset.mem_range.mp hk)]; simp
    rw [this, zero_add]
  have hR : |∑ k ∈ Finset.Ico (j + 1) (m + 1), (sg m ζ k - sg m ζ' k) * δ ^ k| ≤
      2 * (δ ^ (j + 1) * (4 / 3)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.Ico (j + 1) (m + 1), |(sg m ζ k - sg m ζ' k) * δ ^ k|
        ≤ ∑ k ∈ Finset.Ico (j + 1) (m + 1), 2 * δ ^ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_pos (pow_pos hδ k)]
          have : |sg m ζ k - sg m ζ' k| ≤ 2 :=
            (abs_sub _ _).trans (by linarith [sg_abs m ζ k, sg_abs m ζ' k])
          gcongr
      _ = 2 * ∑ k ∈ Finset.Ico (j + 1) (m + 1), δ ^ k := by rw [Finset.mul_sum]
      _ ≤ 2 * (δ ^ (j + 1) * (4 / 3)) := by
          gcongr; exact geom_bound _ hδ.le hd _ _
  have hδj : 0 < δ ^ j := pow_pos hδ j
  have hS : (4 / 3) * δ ^ j ≤
      |∑ k ∈ Finset.range (m + 1), (sg m ζ k - sg m ζ' k) * δ ^ k| := by
    rw [hsplit]
    have h1 : |(sg m ζ j - sg m ζ' j) * δ ^ j| = 2 * δ ^ j := by
      rw [abs_mul, hdj, abs_of_pos hδj]
    have h2 := abs_sub_abs_le_abs_sub ((sg m ζ j - sg m ζ' j) * δ ^ j)
      (-∑ k ∈ Finset.Ico (j + 1) (m + 1), (sg m ζ k - sg m ζ' k) * δ ^ k)
    rw [abs_neg, sub_neg_eq_add] at h2
    have : δ ^ (j + 1) = δ ^ j * δ := pow_succ _ _
    nlinarith
  have hle : δ ^ (l : ℕ) ≤ δ ^ j := pow_le_pow_of_le_one hδ.le (by linarith) hjl
  rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), eps_eq]
  nlinarith

theorem solution (m : ℕ) (hm : 1 ≤ m) :
    ∃ T2 : ℕ, ∀ T ≥ T2, ∀ (ζ ζ' : SignVector m) (l : Fin (m + 1)),
      ζ l ≠ ζ' l → eps m T l / 8 ≤ |zz m T ζ - zz m T ζ'| := by
  obtain ⟨T1, h1, hT⟩ := dl_small m
  exact ⟨T1, fun T hTT ζ ζ' l h => sep_core m T (le_trans h1 hTT) (hT T hTT) ζ ζ' l h⟩
