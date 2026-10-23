-- Prove2me | solution 1 for NeedPersuasion.FirstBest.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:47:48.829661+00:00
-- url     : https://prove2.me/submissions/ed50f605-bb06-475b-9ffa-84c03b33e52e

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

open NeedPersuasion.FirstBest

set_option linter.unusedSectionVars false

namespace NPTP

/-! ## Möbius functions of one variable -/

lemma mob_diff (p0 p1 q0 q1 s t : ℝ) (hs : 0 < q0 + q1 * s) (ht : 0 < q0 + q1 * t) :
    (p0 + p1 * t) / (q0 + q1 * t) - (p0 + p1 * s) / (q0 + q1 * s) =
      (t - s) * (p1 * q0 - p0 * q1) / ((q0 + q1 * s) * (q0 + q1 * t)) := by
  rw [div_sub_div _ _ ht.ne' hs.ne',
    div_eq_div_iff (mul_ne_zero ht.ne' hs.ne') (mul_ne_zero hs.ne' ht.ne')]
  ring

/-! ## The weights of a threshold policy -/

noncomputable def tw (M : Model) (x : ℝ) (k : ℕ) : ℝ :=
  if k ≤ ⌊x⌋₊ then M.lam ^ k
  else M.lam ^ ⌊x⌋₊ * (M.lamH + Int.fract x * M.lamL) * M.lamH ^ (k - ⌊x⌋₊ - 1)

lemma tp_eq (M : Model) (x : ℝ) :
    thresholdPolicy M x = fun k => tw M x k / ∑' j, tw M x j := rfl

/-- `G u k = ∑_j λ_H^j u(k+j)`. -/
noncomputable def G (M : Model) (u : ℕ → ℝ) (k : ℕ) : ℝ := ∑' j, M.lamH ^ j * u (k + j)

/-- `S m = ∑_{k ≤ m} λ^k`. -/
noncomputable def S (M : Model) (m : ℕ) : ℝ := ∑ k ∈ Finset.range (m + 1), M.lam ^ k

/-- normalizer as a function of `ℓ = λ_H + a λ_L` -/
noncomputable def Zf (M : Model) (m : ℕ) (ℓ : ℝ) : ℝ := S M m + M.lam ^ m * ℓ / (1 - M.lamH)

/-- weighted sum `∑_k w_k u_k` as a function of `ℓ` -/
noncomputable def Nf (M : Model) (u : ℕ → ℝ) (m : ℕ) (ℓ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), M.lam ^ k * u k + M.lam ^ m * ℓ * G M u (m + 1)

/-- (LEAVE) numerator as a function of `ℓ` -/
noncomputable def NLf (M : Model) (m : ℕ) (ℓ : ℝ) : ℝ :=
  M.lam ^ m * (M.lam - ℓ) * M.uL m + M.lamL * M.lam ^ m * ℓ * G M M.uL (m + 1)

section
variable (M : Model) (hM : M.Standing)
include hM

lemma lamH0 : 0 ≤ M.lamH := hM.2.1
lemma lamH1 : M.lamH < 1 := by
  obtain ⟨h1, h2, h3, -⟩ := hM; unfold Model.lam at h3; linarith
lemma lamL0 : 0 < M.lamL := hM.1
lemma lam0 : 0 < M.lam := by
  obtain ⟨h1, h2, -⟩ := hM; unfold Model.lam; linarith
lemma lam1 : M.lam ≤ 1 := hM.2.2.1

lemma abs_uL_le (n : ℕ) : |M.uL n| ≤ |M.uL 0| + n * (M.uL 0 - M.uL 1) := by
  obtain ⟨-, -, -, -, -, -, -, hA, -, hC⟩ := hM
  have hD : 0 ≤ M.uL 0 - M.uL 1 := by have := hA (Nat.lt_succ_self 0); linarith
  have hup : M.uL n ≤ M.uL 0 := hA.antitone (Nat.zero_le n)
  have hlo : M.uL 0 - n * (M.uL 0 - M.uL 1) ≤ M.uL n := by
    induction n with
    | zero => simp
    | succ k ih =>
      have := hC (Nat.zero_le k); simp only at this
      push_cast
      linarith [ih (hA.antitone (Nat.zero_le k))]
  rw [abs_le]
  have h0 : (0 : ℝ) ≤ n * (M.uL 0 - M.uL 1) := mul_nonneg (Nat.cast_nonneg n) hD
  constructor
  · have := neg_abs_le (M.uL 0); linarith
  · have := le_abs_self (M.uL 0); linarith

lemma summ_uL (k : ℕ) : Summable (fun j => M.lamH ^ j * M.uL (k + j)) := by
  have h0 := lamH0 M hM
  have h1 := lamH1 M hM
  have hs1 : Summable (fun n : ℕ => M.lamH ^ n) := summable_geometric_of_lt_one h0 h1
  have hs2 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * M.lamH ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  refine Summable.of_norm_bounded
    ((hs1.mul_left (|M.uL 0| + k * (M.uL 0 - M.uL 1))).add (hs2.mul_left (M.uL 0 - M.uL 1)))
    (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 n)]
  have := mul_le_mul_of_nonneg_left (abs_uL_le M hM (k + n)) (pow_nonneg h0 n)
  push_cast at this
  simp only [pow_one]
  nlinarith

lemma summ_shift_pos (hH : 0 < M.lamH) (u : ℕ → ℝ) (hu : Summable (fun j => M.lamH ^ j * u j))
    (k : ℕ) : Summable (fun j => M.lamH ^ j * u (k + j)) := by
  have := ((summable_nat_add_iff k).mpr hu).mul_left (M.lamH ^ k)⁻¹
  refine this.congr (fun j => ?_)
  rw [pow_add, add_comm j k]
  field_simp

lemma G_succ (u : ℕ → ℝ) (k : ℕ) (hu : Summable (fun j => M.lamH ^ j * u (k + j))) :
    G M u k = u k + M.lamH * G M u (k + 1) := by
  unfold G
  rw [hu.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  congr 1; ext j
  rw [pow_succ, show k + (j + 1) = k + 1 + j by omega]; ring

lemma S_pos (m : ℕ) : 0 < S M m := by
  unfold S
  rw [Finset.sum_range_succ']
  have : 0 ≤ ∑ k ∈ Finset.range m, M.lam ^ (k + 1) :=
    Finset.sum_nonneg (fun k _ => pow_nonneg (lam0 M hM).le _)
  simp only [pow_zero]; linarith

lemma Zf_pos (m : ℕ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) : 0 < Zf M m ℓ := by
  unfold Zf
  have : 0 ≤ M.lam ^ m * ℓ / (1 - M.lamH) :=
    div_nonneg (mul_nonneg (pow_nonneg (lam0 M hM).le _) hℓ) (by linarith [lamH1 M hM])
  linarith [S_pos M hM m]

/-! ### Explicit sums for a threshold policy -/

lemma tw_head (x : ℝ) (k : ℕ) (hk : k ≤ ⌊x⌋₊) : tw M x k = M.lam ^ k := by
  unfold tw; rw [if_pos hk]

lemma tw_tail (x : ℝ) (j : ℕ) :
    tw M x (j + (⌊x⌋₊ + 1)) = M.lam ^ ⌊x⌋₊ * (M.lamH + Int.fract x * M.lamL) * M.lamH ^ j := by
  unfold tw; rw [if_neg (by omega), show j + (⌊x⌋₊ + 1) - ⌊x⌋₊ - 1 = j by omega]

lemma tw_summable (x : ℝ) : Summable (tw M x) := by
  apply (summable_nat_add_iff (⌊x⌋₊ + 1)).mp
  simp only [tw_tail M hM x]
  exact (summable_geometric_of_lt_one (lamH0 M hM) (lamH1 M hM)).mul_left _

lemma tw_tsum (x : ℝ) : ∑' k, tw M x k = Zf M ⌊x⌋₊ (M.lamH + Int.fract x * M.lamL) := by
  rw [← (tw_summable M hM x).sum_add_tsum_nat_add (⌊x⌋₊ + 1)]
  simp only [tw_tail M hM x]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (lamH0 M hM) (lamH1 M hM)]
  unfold Zf S
  congr 1
  · exact Finset.sum_congr rfl (fun k hk => tw_head M hM x k (by
      rw [Finset.mem_range] at hk; omega))

lemma tw_wsum (x : ℝ) (u : ℕ → ℝ) (hu : Summable (fun j => M.lamH ^ j * u (⌊x⌋₊ + 1 + j))) :
    Summable (fun k => tw M x k * u k) ∧
    ∑' k, tw M x k * u k = Nf M u ⌊x⌋₊ (M.lamH + Int.fract x * M.lamL) := by
  have htail : ∀ j, tw M x (j + (⌊x⌋₊ + 1)) * u (j + (⌊x⌋₊ + 1)) =
      M.lam ^ ⌊x⌋₊ * (M.lamH + Int.fract x * M.lamL) * (M.lamH ^ j * u (⌊x⌋₊ + 1 + j)) := by
    intro j; rw [tw_tail M hM x, add_comm j]; ring
  have hs : Summable (fun k => tw M x k * u k) := by
    apply (summable_nat_add_iff (⌊x⌋₊ + 1)).mp
    simp only [htail]
    exact hu.mul_left _
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add (⌊x⌋₊ + 1)]
  simp only [htail]
  rw [tsum_mul_left]
  unfold Nf G
  congr 1
  exact Finset.sum_congr rfl (fun k hk => by
    rw [tw_head M hM x k (by rw [Finset.mem_range] at hk; omega)])

lemma tw_leave (x : ℝ) :
    ∑' n, (M.lam * tw M x n - tw M x (n + 1)) * M.uL n =
      NLf M ⌊x⌋₊ (M.lamH + Int.fract x * M.lamL) := by
  set m := ⌊x⌋₊ with hm
  set ℓ := M.lamH + Int.fract x * M.lamL with hℓ
  have htail : ∀ j, (M.lam * tw M x (j + (m + 1)) - tw M x (j + (m + 1) + 1)) * M.uL (j + (m + 1)) =
      M.lamL * M.lam ^ m * ℓ * (M.lamH ^ j * M.uL (m + 1 + j)) := by
    intro j
    rw [tw_tail M hM x, show j + (m + 1) + 1 = (j + 1) + (m + 1) by omega, tw_tail M hM x,
      add_comm j (m + 1)]
    rw [pow_succ]; unfold Model.lam; ring
  have hs : Summable (fun n => (M.lam * tw M x n - tw M x (n + 1)) * M.uL n) := by
    apply (summable_nat_add_iff (m + 1)).mp
    simp only [htail]
    exact (summ_uL M hM (m + 1)).mul_left _
  rw [← hs.sum_add_tsum_nat_add (m + 1)]
  simp only [htail]
  rw [tsum_mul_left, Finset.sum_range_succ]
  have hz : ∑ n ∈ Finset.range m, (M.lam * tw M x n - tw M x (n + 1)) * M.uL n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_range] at hn
    rw [tw_head M hM x n (by omega), tw_head M hM x (n + 1) (by omega), pow_succ]; ring
  have h1 : tw M x (m + 1) = M.lam ^ m * ℓ := by
    have := tw_tail M hM x 0; simp only [zero_add, pow_zero, mul_one] at this; exact this
  rw [hz, tw_head M hM x m le_rfl, h1]
  unfold NLf G
  ring

/-! ### Representation on a closed unit interval -/

lemma floor_frac (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ico (m : ℝ) (m + 1)) :
    ⌊t⌋₊ = m ∧ Int.fract t = t - m := by
  have h0 : 0 ≤ t := le_trans (Nat.cast_nonneg m) ht.1
  have hfl : ⌊t⌋₊ = m := by rw [Nat.floor_eq_iff h0]; exact ht
  refine ⟨hfl, ?_⟩
  rw [Int.fract_eq_iff]
  exact ⟨by linarith [ht.1], by linarith [ht.2], m, by push_cast; ring⟩

lemma floor_frac_succ (m : ℕ) : ⌊((m : ℝ) + 1)⌋₊ = m + 1 ∧ Int.fract ((m : ℝ) + 1) = 0 := by
  constructor
  · have := Nat.floor_natCast (R := ℝ) (m + 1); push_cast at this; exact this
  · have := Int.fract_natCast (R := ℝ) (m + 1); push_cast at this; exact this

lemma Zf_succ (m : ℕ) : Zf M (m + 1) M.lamH = Zf M m M.lam := by
  unfold Zf S
  rw [Finset.sum_range_succ (fun k => M.lam ^ k) (m + 1), pow_succ]
  have : (1 - M.lamH) ≠ 0 := by linarith [lamH1 M hM]
  field_simp
  unfold Model.lam; ring

lemma NLf_succ (m : ℕ) : NLf M (m + 1) M.lamH = NLf M m M.lam := by
  unfold NLf
  rw [G_succ M hM M.uL (m + 1) (summ_uL M hM (m + 1)), pow_succ]
  unfold Model.lam; ring

lemma Nf_succ (u : ℕ → ℝ) (m : ℕ) (hu : Summable (fun j => M.lamH ^ j * u (m + 1 + j))) :
    Nf M u (m + 1) M.lamH = Nf M u m M.lam := by
  unfold Nf
  rw [G_succ M hM u (m + 1) hu, Finset.sum_range_succ (fun k => M.lam ^ k * u k) (m + 1), pow_succ]
  unfold Model.lam; ring

/-- `L(t)` on `[m, m+1]` -/
lemma leave_rep (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (m : ℝ) (m + 1)) :
    leaveValx M t = NLf M m (M.lamH + (t - m) * M.lamL) / Zf M m (M.lamH + (t - m) * M.lamL) := by
  have key : ∀ x : ℝ, leaveValx M x =
      NLf M ⌊x⌋₊ (M.lamH + Int.fract x * M.lamL) / Zf M ⌊x⌋₊ (M.lamH + Int.fract x * M.lamL) := by
    intro x
    unfold leaveValx leaveVal
    rw [tp_eq]
    simp only
    rw [← tw_tsum M hM x, ← tw_leave M hM x, ← tsum_div_const]
    congr 1; ext n; ring
  rcases ht.2.lt_or_eq with hlt | heq
  · obtain ⟨h1, h2⟩ := floor_frac M hM m t ⟨ht.1, hlt⟩
    rw [key, h1, h2]
  · obtain ⟨h1, h2⟩ := floor_frac_succ M hM m
    rw [key, heq, h1, h2, zero_mul, add_zero, Zf_succ M hM, NLf_succ M hM]
    congr 2 <;> · unfold Model.lam; ring

/-- `W_H(t)` on `[m, m+1]` -/
lemma WH_rep (hH : 0 < M.lamH) (hSumH : Summable (fun k => M.lamH ^ k * M.uH k))
    (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (m : ℝ) (m + 1)) :
    WHx M t = M.lamH * (Nf M M.uH m (M.lamH + (t - m) * M.lamL) /
      Zf M m (M.lamH + (t - m) * M.lamL)) := by
  have hsh := summ_shift_pos M hM hH M.uH hSumH
  have key : ∀ x : ℝ, WHx M x = M.lamH *
      (Nf M M.uH ⌊x⌋₊ (M.lamH + Int.fract x * M.lamL) /
        Zf M ⌊x⌋₊ (M.lamH + Int.fract x * M.lamL)) := by
    intro x
    unfold WHx WH
    rw [tp_eq]
    simp only
    rw [← tw_tsum M hM x, ← (tw_wsum M hM x M.uH (hsh _)).2, ← tsum_div_const]
    congr 2; ext n; ring
  rcases ht.2.lt_or_eq with hlt | heq
  · obtain ⟨h1, h2⟩ := floor_frac M hM m t ⟨ht.1, hlt⟩
    rw [key, h1, h2]
  · obtain ⟨h1, h2⟩ := floor_frac_succ M hM m
    rw [key, heq, h1, h2, zero_mul, add_zero, Zf_succ M hM, Nf_succ M hM M.uH m (hsh _)]
    congr 3 <;> · unfold Model.lam; ring

end

/-! ## Gluing strict antitonicity over unit intervals -/

lemma glue (f : ℝ → ℝ) (k : ℕ) (h1 : StrictAntiOn f (Set.Icc 0 (k : ℝ)))
    (h2 : StrictAntiOn f (Set.Icc (k : ℝ) (k + 1))) : StrictAntiOn f (Set.Icc 0 ((k : ℝ) + 1)) := by
  intro a ha b hb hab
  by_cases hbk : b ≤ k
  · exact h1 ⟨ha.1, le_trans hab.le hbk⟩ ⟨hb.1, hbk⟩ hab
  by_cases hak : (k : ℝ) ≤ a
  · exact h2 ⟨hak, ha.2⟩ ⟨le_trans hak hab.le, hb.2⟩ hab
  push Not at hbk hak
  have e1 := h2 ⟨le_rfl, by linarith⟩ ⟨hbk.le, hb.2⟩ hbk
  have e2 := h1 ⟨ha.1, hak.le⟩ ⟨Nat.cast_nonneg k, le_rfl⟩ hak
  linarith

lemma anti_upto (f : ℝ → ℝ) (m : ℕ) (h : ∀ k : ℕ, k ≤ m → StrictAntiOn f (Set.Icc (k : ℝ) (k + 1))) :
    StrictAntiOn f (Set.Icc 0 ((m : ℝ) + 1)) := by
  have : ∀ n : ℕ, n ≤ m + 1 → StrictAntiOn f (Set.Icc 0 (n : ℝ)) := by
    intro n hn
    induction n with
    | zero =>
      intro a ha b hb hab
      simp only [Nat.cast_zero, Set.mem_Icc] at ha hb
      linarith [ha.1, ha.2, hb.1, hb.2]
    | succ n ih =>
      push_cast
      exact glue f n (ih (by omega)) (h n (by omega))
  have := this (m + 1) le_rfl
  push_cast at this
  exact this

/-! ## Monotonicity of a Möbius function along `ℓ(t) = λ_H + (t - m) λ_L` -/

section mob
variable (M : Model) (hM : M.Standing)
include hM

lemma mob_interval (f : ℝ → ℝ) (m : ℕ) (p0 p1 q0 q1 : ℝ)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + 1), f t =
      (p0 + p1 * (M.lamH + (t - m) * M.lamL)) / (q0 + q1 * (M.lamH + (t - m) * M.lamL)))
    (hq : ∀ t ∈ Set.Icc (m : ℝ) (m + 1), 0 < q0 + q1 * (M.lamH + (t - m) * M.lamL)) :
    (p1 * q0 - p0 * q1 < 0 → StrictAntiOn f (Set.Icc (m : ℝ) (m + 1))) ∧
    (f (m + 1) < f m → p1 * q0 - p0 * q1 < 0) ∧
    (∀ t ∈ Set.Icc (m : ℝ) (m + 1), f t ≤ max (f m) (f (m + 1))) := by
  have hL := lamL0 M hM
  have hmI : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + 1) := ⟨le_rfl, by linarith⟩
  have hm1I : (m : ℝ) + 1 ∈ Set.Icc (m : ℝ) (m + 1) := ⟨by linarith, le_rfl⟩
  have key : ∀ s ∈ Set.Icc (m : ℝ) (m + 1), ∀ t ∈ Set.Icc (m : ℝ) (m + 1),
      f t - f s = ((t - s) * M.lamL) * (p1 * q0 - p0 * q1) /
        ((q0 + q1 * (M.lamH + (s - m) * M.lamL)) * (q0 + q1 * (M.lamH + (t - m) * M.lamL))) := by
    intro s hs t ht
    rw [hf t ht, hf s hs, mob_diff p0 p1 q0 q1 _ _ (hq s hs) (hq t ht)]
    congr 1; ring
  refine ⟨fun hD s hs t ht hst => ?_, fun hlt => ?_, fun t ht => ?_⟩
  · have := key s hs t ht
    have hden := mul_pos (hq s hs) (hq t ht)
    have hnum : (t - s) * M.lamL * (p1 * q0 - p0 * q1) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by linarith) hL) hD
    have : f t - f s < 0 := by rw [this]; exact div_neg_of_neg_of_pos hnum hden
    linarith
  · by_contra hc
    push Not at hc
    have := key m hmI (m + 1) hm1I
    have hden := mul_pos (hq m hmI) (hq (m + 1) hm1I)
    have : 0 ≤ f (m + 1) - f m := by
      rw [this]; apply div_nonneg _ hden.le
      exact mul_nonneg (mul_nonneg (by linarith) hL.le) hc
    linarith
  · rcases le_or_gt 0 (p1 * q0 - p0 * q1) with hD | hD
    · have := key t ht (m + 1) hm1I
      have hden := mul_pos (hq t ht) (hq (m + 1) hm1I)
      have : 0 ≤ f (m + 1) - f t := by
        rw [this]; apply div_nonneg _ hden.le
        exact mul_nonneg (mul_nonneg (by linarith [ht.2]) hL.le) hD
      exact le_max_of_le_right (by linarith)
    · have := key m hmI t ht
      have hden := mul_pos (hq m hmI) (hq t ht)
      have : f t - f m ≤ 0 := by
        rw [this]; apply div_nonpos_of_nonpos_of_nonneg _ hden.le
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith [ht.1]) hL.le) hD.le
      exact le_max_of_le_left (by linarith)

lemma ell_nonneg (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (m : ℝ) (m + 1)) :
    0 ≤ M.lamH + (t - m) * M.lamL :=
  add_nonneg (lamH0 M hM) (mul_nonneg (by linarith [ht.1]) (lamL0 M hM).le)

lemma Zf_lin (m : ℕ) (ℓ : ℝ) : Zf M m ℓ = S M m + M.lam ^ m / (1 - M.lamH) * ℓ := by
  unfold Zf; ring

end mob

/-! ## Lemma 5(1): W_H is strictly decreasing -/

section l51
variable (M : Model) (hM : M.Standing)
include hM

theorem lemma_5_1_main (hH : 0 < M.lamH) (hSumH : Summable (fun k => M.lamH ^ k * M.uH k)) :
    StrictAntiOn (WHx M) (Set.Ici 0) := by
  have h0 := lamH0 M hM
  have h1 := lamH1 M hM
  have hlam := lam0 M hM
  have hA : StrictAnti M.uH := hM.2.2.2.2.2.2.2.2.1
  have hsh := summ_shift_pos M hM hH M.uH hSumH
  have hint : ∀ m : ℕ, StrictAntiOn (WHx M) (Set.Icc (m : ℝ) (m + 1)) := by
    intro m
    set A := ∑ k ∈ Finset.range (m + 1), M.lam ^ k * M.uH k with hAdef
    set Gm := G M M.uH (m + 1) with hGm
    -- (1 - λ_H) G ≤ u_H(m+1)
    have hGle : (1 - M.lamH) * Gm ≤ M.uH (m + 1) := by
      have hs := hsh (m + 1)
      have hg : Summable (fun j : ℕ => M.lamH ^ j * M.uH (m + 1)) :=
        (summable_geometric_of_lt_one h0 h1).mul_right _
      have hle : Gm ≤ ∑' j : ℕ, M.lamH ^ j * M.uH (m + 1) :=
        Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left
          (hA.antitone (by omega)) (pow_nonneg h0 j)) hs hg
      rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1] at hle
      have hp : 0 < 1 - M.lamH := by linarith
      calc (1 - M.lamH) * Gm ≤ (1 - M.lamH) * ((1 - M.lamH)⁻¹ * M.uH (m + 1)) :=
            mul_le_mul_of_nonneg_left hle hp.le
        _ = M.uH (m + 1) := by field_simp
    have hAgt : (1 - M.lamH) * Gm * S M m < A := by
      unfold S
      rw [Finset.mul_sum, hAdef]
      apply Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩
      intro k hk
      rw [Finset.mem_range] at hk
      have : M.uH (m + 1) < M.uH k := hA (by omega)
      have hp := pow_pos hlam k
      nlinarith
    -- the WH-numerator divided by λ_H
    let f : ℝ → ℝ := fun t => WHx M t / M.lamH
    have hf : ∀ t ∈ Set.Icc (m : ℝ) (m + 1), f t =
        (A + M.lam ^ m * Gm * (M.lamH + (t - m) * M.lamL)) /
          (S M m + M.lam ^ m / (1 - M.lamH) * (M.lamH + (t - m) * M.lamL)) := by
      intro t ht
      simp only [f]
      rw [WH_rep M hM hH hSumH m t ht, Zf_lin M hM]
      unfold Nf
      rw [hAdef, hGm]
      field_simp
    have hq : ∀ t ∈ Set.Icc (m : ℝ) (m + 1),
        0 < S M m + M.lam ^ m / (1 - M.lamH) * (M.lamH + (t - m) * M.lamL) := by
      intro t ht
      rw [← Zf_lin M hM]; exact Zf_pos M hM m _ (ell_nonneg M hM m t ht)
    have hD : M.lam ^ m * Gm * S M m - A * (M.lam ^ m / (1 - M.lamH)) < 0 := by
      have hp : 0 < 1 - M.lamH := by linarith
      have hpm := pow_pos hlam m
      have e : M.lam ^ m * Gm * S M m - A * (M.lam ^ m / (1 - M.lamH)) =
          M.lam ^ m / (1 - M.lamH) * ((1 - M.lamH) * Gm * S M m - A) := by
        field_simp
      rw [e]
      exact mul_neg_of_pos_of_neg (div_pos hpm hp) (by linarith)
    have hanti := (mob_interval M hM f m A (M.lam ^ m * Gm) (S M m) (M.lam ^ m / (1 - M.lamH))
      hf hq).1 hD
    intro s hs t ht hst
    have := hanti hs ht hst
    simp only [f] at this
    exact (div_lt_div_iff_of_pos_right hH).mp this
  intro x hx y hy hxy
  have hy' : y ∈ Set.Icc 0 ((⌊y⌋₊ : ℝ) + 1) := ⟨hy, (Nat.lt_floor_add_one y).le⟩
  have hx' : x ∈ Set.Icc 0 ((⌊y⌋₊ : ℝ) + 1) := ⟨hx, by linarith [hy'.2]⟩
  exact anti_upto (WHx M) ⌊y⌋₊ (fun k _ => hint k) hx' hy' hxy

end l51

/-! ## Lemma 6: the (LEAVE) function -/

section l6
variable (M : Model) (hM : M.Standing)
include hM

lemma leave_int (k : ℕ) :
    leaveValx M k = M.lamL * (M.lam ^ k / Zf M k M.lamH) * G M M.uL k := by
  have := leave_rep M hM k k ⟨le_rfl, by linarith⟩
  rw [this, sub_self, zero_mul, add_zero]
  unfold NLf
  rw [G_succ M hM M.uL k (summ_uL M hM k)]
  unfold Model.lam
  ring

lemma F1_pos (k : ℕ) : 0 < M.lam ^ k / Zf M k M.lamH :=
  div_pos (pow_pos (lam0 M hM) k) (Zf_pos M hM k _ (lamH0 M hM))

lemma F1_lt (k : ℕ) : M.lam ^ (k + 1) / Zf M (k + 1) M.lamH < M.lam ^ k / Zf M k M.lamH := by
  have hlam := lam0 M hM
  have hlam1 := lam1 M hM
  have hp : 0 < 1 - M.lamH := by linarith [lamH1 M hM]
  rw [div_lt_div_iff₀ (Zf_pos M hM _ _ (lamH0 M hM)) (Zf_pos M hM _ _ (lamH0 M hM)), Zf_succ M hM]
  unfold Zf
  have hS := S_pos M hM k
  have e : M.lam ^ k * (S M k + M.lam ^ k * M.lam / (1 - M.lamH)) -
      M.lam ^ (k + 1) * (S M k + M.lam ^ k * M.lamH / (1 - M.lamH)) =
      M.lam ^ k * S M k * (1 - M.lam) + M.lam ^ (2 * k + 1) := by
    field_simp
    ring
  have : 0 < M.lam ^ k * S M k * (1 - M.lam) + M.lam ^ (2 * k + 1) := by
    have := mul_nonneg (mul_nonneg (pow_nonneg hlam.le k) hS.le) (by linarith : (0:ℝ) ≤ 1 - M.lam)
    have := pow_pos hlam (2 * k + 1)
    linarith
  linarith

lemma F2_lt (k : ℕ) : G M M.uL (k + 1) < G M M.uL k := by
  have hA : StrictAnti M.uL := hM.2.2.2.2.2.2.2.1
  unfold G
  refine Summable.tsum_lt_tsum (i := 0) (fun j => ?_) ?_ (summ_uL M hM (k + 1)) (summ_uL M hM k)
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg (lamH0 M hM) j)
    exact hA.antitone (by omega)
  · simp only [pow_zero, one_mul, add_zero]
    exact hA (by omega)

lemma int_I (k : ℕ) (h : 0 ≤ leaveValx M k) : leaveValx M ((k + 1 : ℕ) : ℝ) < leaveValx M k := by
  rw [leave_int M hM] at h ⊢
  rw [leave_int M hM]
  have hL := lamL0 M hM
  have f1 := F1_pos M hM k
  have f1' := F1_pos M hM (k + 1)
  have f1lt := F1_lt M hM k
  have f2lt := F2_lt M hM k
  have hG : 0 ≤ G M M.uL k := by
    by_contra hc; push Not at hc
    have : M.lamL * (M.lam ^ k / Zf M k M.lamH) * G M M.uL k < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hL f1) hc
    linarith
  rcases lt_or_ge (G M M.uL (k + 1)) 0 with hneg | hpos
  · have : M.lamL * (M.lam ^ (k + 1) / Zf M (k + 1) M.lamH) * G M M.uL (k + 1) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hL f1') hneg
    linarith
  · have : (M.lam ^ (k + 1) / Zf M (k + 1) M.lamH) * G M M.uL (k + 1) <
        (M.lam ^ k / Zf M k M.lamH) * G M M.uL k := by
      calc (M.lam ^ (k + 1) / Zf M (k + 1) M.lamH) * G M M.uL (k + 1)
          ≤ (M.lam ^ (k + 1) / Zf M (k + 1) M.lamH) * G M M.uL k :=
            mul_le_mul_of_nonneg_left f2lt.le f1'.le
        _ < (M.lam ^ k / Zf M k M.lamH) * G M M.uL k := by
            rcases hG.lt_or_eq with hG' | hG'
            · exact mul_lt_mul_of_pos_right f1lt hG'
            · exfalso; linarith
    have := mul_lt_mul_of_pos_left this hL
    linarith [this]

lemma int_II (k : ℕ) (h : leaveValx M k < 0) : leaveValx M ((k + 1 : ℕ) : ℝ) < 0 := by
  rw [leave_int M hM] at h ⊢
  have hL := lamL0 M hM
  have f1 := F1_pos M hM k
  have f1' := F1_pos M hM (k + 1)
  have hG : G M M.uL k < 0 := by
    by_contra hc; push Not at hc
    have : 0 ≤ M.lamL * (M.lam ^ k / Zf M k M.lamH) * G M M.uL k :=
      mul_nonneg (mul_pos hL f1).le hc
    linarith
  exact mul_neg_of_pos_of_neg (mul_pos hL f1') (lt_trans (F2_lt M hM k) hG)

lemma leave_mob (m : ℕ) :
    (leaveValx M ((m : ℝ) + 1) < leaveValx M m → StrictAntiOn (leaveValx M) (Set.Icc (m : ℝ) (m + 1))) ∧
    (∀ t ∈ Set.Icc (m : ℝ) (m + 1), leaveValx M t ≤ max (leaveValx M m) (leaveValx M ((m : ℝ) + 1))) := by
  have hf : ∀ t ∈ Set.Icc (m : ℝ) (m + 1), leaveValx M t =
      (M.lam ^ m * M.lam * M.uL m + M.lam ^ m * (M.lamL * G M M.uL (m + 1) - M.uL m) *
        (M.lamH + (t - m) * M.lamL)) /
      (S M m + M.lam ^ m / (1 - M.lamH) * (M.lamH + (t - m) * M.lamL)) := by
    intro t ht
    rw [leave_rep M hM m t ht, Zf_lin M hM]
    unfold NLf
    congr 1; ring
  have hq : ∀ t ∈ Set.Icc (m : ℝ) (m + 1),
      0 < S M m + M.lam ^ m / (1 - M.lamH) * (M.lamH + (t - m) * M.lamL) := by
    intro t ht
    rw [← Zf_lin M hM]; exact Zf_pos M hM m _ (ell_nonneg M hM m t ht)
  have H := mob_interval M hM (leaveValx M) m _ _ _ _ hf hq
  exact ⟨fun h => H.1 (H.2.1 h), H.2.2⟩

theorem lemma_6_main :
    (∀ x y : ℝ, 0 ≤ x → x < y → 0 ≤ leaveValx M y → leaveValx M y < leaveValx M x) ∧
    (∀ x y : ℝ, 0 ≤ x → x ≤ y → leaveValx M x < 0 → leaveValx M y < 0) ∧
    (∀ x : ℝ, 0 ≤ x →
      leaveValx M x ≤ max (sInf (leaveValx M '' Set.Icc 0 x)) 0) := by
  have cast1 : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := fun k => by push_cast; ring
  have hstay : ∀ k : ℕ, leaveValx M k < 0 → ∀ j : ℕ, k ≤ j → leaveValx M j < 0 := by
    intro k hk j hj
    induction j, hj using Nat.le_induction with
    | base => exact hk
    | succ j _ ih => exact int_II M hM j ih
  have P1 : ∀ x y : ℝ, 0 ≤ x → x < y → 0 ≤ leaveValx M y → leaveValx M y < leaveValx M x := by
    intro x y hx hxy hy
    have hy0 : 0 ≤ y := by linarith
    set m := ⌊y⌋₊ with hm
    have hyI : y ∈ Set.Icc (m : ℝ) (m + 1) := ⟨Nat.floor_le hy0, (Nat.lt_floor_add_one y).le⟩
    have hmpos : 0 ≤ leaveValx M m := by
      by_contra hc
      push Not at hc
      have h1 := int_II M hM m hc
      rw [cast1] at h1
      have := (leave_mob M hM m).2 y hyI
      have : max (leaveValx M m) (leaveValx M ((m : ℝ) + 1)) < 0 := max_lt hc h1
      linarith
    have hall : ∀ k : ℕ, k ≤ m → 0 ≤ leaveValx M k := by
      intro k hk
      by_contra hc
      push Not at hc
      have := hstay k hc m hk
      linarith
    have hint : ∀ k : ℕ, k ≤ m → StrictAntiOn (leaveValx M) (Set.Icc (k : ℝ) (k + 1)) := by
      intro k hk
      apply (leave_mob M hM k).1
      have := int_I M hM k (hall k hk)
      rw [cast1] at this
      exact this
    have hanti := anti_upto (leaveValx M) m hint
    exact hanti ⟨hx, by linarith [hyI.2]⟩ ⟨hy0, hyI.2⟩ hxy
  refine ⟨P1, ?_, ?_⟩
  · intro x y hx hxy hLx
    rcases hxy.lt_or_eq with h | h
    · by_contra hc
      push Not at hc
      have := P1 x y hx h hc
      linarith
    · rw [← h]; exact hLx
  · intro x hx
    rcases le_or_gt (leaveValx M x) 0 with h | h
    · exact le_max_of_le_right h
    · apply le_max_of_le_left
      apply le_csInf ((Set.nonempty_Icc.mpr hx).image _)
      rintro b ⟨u, hu, rfl⟩
      rcases hu.2.lt_or_eq with hlt | heq
      · exact (P1 u x hu.1 hlt h.le).le
      · rw [heq]

end l6

end NPTP

theorem solution (M : Model) (hM : M.Standing) :
    (∀ x y : ℝ, 0 ≤ x → x < y → 0 ≤ leaveValx M y → leaveValx M y < leaveValx M x) ∧
    (∀ x y : ℝ, 0 ≤ x → x ≤ y → leaveValx M x < 0 → leaveValx M y < 0) ∧
    (∀ x : ℝ, 0 ≤ x →
      leaveValx M x ≤ max (sInf (leaveValx M '' Set.Icc 0 x)) 0) :=
  NPTP.lemma_6_main M hM
