-- Prove2me | solution 1 for LL_SchoenfeldLiS76.liPV_two_ge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T23:57:09.624798+00:00
-- url     : https://prove2.me/submissions/172bcff5-2afc-4ba8-b810-cde1e4cab773

import Mathlib
import Definitions.Def_LL_SchoenfeldLiS76_liPart
import Definitions.Def_LL_SchoenfeldLiS76_liPV

open Real MeasureTheory Filter Topology Set intervalIntegral LL_SchoenfeldLiS76

section

private lemma mk_hasDerivAt {f g : ℝ → ℝ} {f' g' x : ℝ}
    (h : HasDerivAt f f' x) (hf : ∀ y, g y = f y) (hd : g' = f') : HasDerivAt g g' x := by
  have heq : g = f := funext hf
  rw [heq, hd]
  exact h

private lemma continuousAt_finset_sum_real {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a : ℝ}
    [DecidableEq ι] (hf : ∀ i ∈ s, ContinuousAt (f i) a) :
    ContinuousAt (fun x => ∑ i ∈ s, f i x) a := by
  induction s using Finset.induction_on with
  | empty => simp [continuousAt_const]
  | @insert j t hjt ih =>
    have hj : ContinuousAt (f j) a := hf j (Finset.mem_insert_self j t)
    have ht : ContinuousAt (fun x => ∑ i ∈ t, f i x) a :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x => ∑ i ∈ insert j t, f i x) = (fun x => f j x + ∑ i ∈ t, f i x) := by
      ext x; exact Finset.sum_insert hjt
    rw [heq]
    exact hj.add ht

private lemma log_ratio_bounds_3 {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    2 * u + 2 / 3 * u ^ 3 + 2 / 5 * u ^ 5 ≤ log ((1 + u) / (1 - u)) ∧
    log ((1 + u) / (1 - u)) ≤ 2 * u + 2 / 3 * u ^ 3 + 2 / 5 * u ^ 5 + 2 / 7 * u ^ 7 / (1 - u ^ 2) := by
  let φ : ℝ → ℝ := fun s => log (1 + s) - log (1 - s) - (2 * s + 2 / 3 * s ^ 3 + 2 / 5 * s ^ 5)
  let φ' : ℝ → ℝ := fun s => 2 * s ^ 6 / (1 - s ^ 2)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) u, HasDerivAt φ (φ' s) s := by
    intro s hs
    rw [uIcc_of_le hu0] at hs
    have hs1 : 0 < 1 + s := by linarith [hs.1]
    have hs2 : 0 < 1 - s := by linarith [hs.2]
    have hd1 : HasDerivAt (fun x => log (1 + x)) ((1 + s)⁻¹) s :=
      mk_hasDerivAt (((hasDerivAt_id s).const_add (1 : ℝ)).log hs1.ne') (fun _ => rfl) (by simp)
    have hd2 : HasDerivAt (fun x => log (1 - x)) (-(1 - s)⁻¹) s := by
      have hsub : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1) s :=
        (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
      exact mk_hasDerivAt (hsub.log hs2.ne') (fun _ => rfl) (by ring)
    have hd3 : HasDerivAt (fun x : ℝ => 2 * x + 2 / 3 * x ^ 3 + 2 / 5 * x ^ 5)
        (2 + 2 * s ^ 2 + 2 * s ^ 4) s := by
      have hp1 : HasDerivAt (fun x : ℝ => 2 * x) (2 * 1) s := (hasDerivAt_id s).const_mul (2 : ℝ)
      have hp3 : HasDerivAt (fun x : ℝ => 2 / 3 * x ^ 3) (2 / 3 * (↑(3 : ℕ) * s ^ (3 - 1))) s :=
        (hasDerivAt_pow 3 s).const_mul ((2 : ℝ) / 3)
      have hp5 : HasDerivAt (fun x : ℝ => 2 / 5 * x ^ 5) (2 / 5 * (↑(5 : ℕ) * s ^ (5 - 1))) s :=
        (hasDerivAt_pow 5 s).const_mul ((2 : ℝ) / 5)
      exact mk_hasDerivAt ((hp1.add hp3).add hp5) (fun _ => rfl) (by norm_num; ring)
    refine mk_hasDerivAt ((hd1.sub hd2).sub hd3) (fun _ => rfl) ?_
    have hne1 : 1 + s ≠ 0 := hs1.ne'
    have hne2 : 1 - s ≠ 0 := hs2.ne'
    have hne3 : 1 - s ^ 2 ≠ 0 := by nlinarith
    dsimp [φ']
    field_simp
    ring
  have hcont : ContinuousOn φ' (uIcc (0 : ℝ) u) := by
    rw [uIcc_of_le hu0]
    intro s hs
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_const.mul (continuousAt_id.pow 6)).div
      (continuousAt_const.sub (continuousAt_id.pow 2)) (by nlinarith [hs.1, hs.2])
  have hint_eq : ∫ s in (0 : ℝ)..u, φ' s =
      log ((1 + u) / (1 - u)) - (2 * u + 2 / 3 * u ^ 3 + 2 / 5 * u ^ 5) := by
    rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    have hφ0 : φ 0 = 0 := by simp [φ]
    rw [hφ0, sub_zero]
    simp only [φ]
    rw [← Real.log_div (by linarith) (by linarith)]
  have hlo : 0 ≤ ∫ s in (0 : ℝ)..u, φ' s := by
    calc (0 : ℝ) = ∫ _s in (0 : ℝ)..u, (0 : ℝ) := by simp
      _ ≤ ∫ s in (0 : ℝ)..u, φ' s := by
        refine integral_mono_on hu0 intervalIntegrable_const hcont.intervalIntegrable ?_
        intro s hs
        exact div_nonneg (by positivity) (by nlinarith [hs.1, hs.2])
  let ψ : ℝ → ℝ := fun s => 2 / 7 * s ^ 7 / (1 - u ^ 2)
  let ψ' : ℝ → ℝ := fun s => 2 * s ^ 6 / (1 - u ^ 2)
  have hψderiv : ∀ s ∈ uIcc (0 : ℝ) u, HasDerivAt ψ (ψ' s) s := by
    intro s _
    have h := ((hasDerivAt_pow 7 s).const_mul ((2 : ℝ) / 7)).div_const (1 - u ^ 2)
    exact mk_hasDerivAt h (fun _ => rfl) (by dsimp [ψ']; norm_num; ring)
  have hψcont : ContinuousOn ψ' (uIcc (0 : ℝ) u) :=
    ((continuous_const.mul (continuous_pow 6)).div_const (1 - u ^ 2)).continuousOn
  have hψint : ∫ s in (0 : ℝ)..u, ψ' s = 2 / 7 * u ^ 7 / (1 - u ^ 2) := by
    rw [integral_eq_sub_of_hasDerivAt hψderiv hψcont.intervalIntegrable]
    simp [ψ]
  have hhi : ∫ s in (0 : ℝ)..u, φ' s ≤ 2 / 7 * u ^ 7 / (1 - u ^ 2) := by
    rw [← hψint]
    refine integral_mono_on hu0 hcont.intervalIntegrable hψcont.intervalIntegrable ?_
    intro s hs
    exact div_le_div_of_nonneg_left (by positivity) (by nlinarith [hs.1, hs.2]) (by nlinarith [hs.1, hs.2])
  rw [hint_eq] at hlo hhi
  constructor <;> linarith

private lemma ln2_bounds_11 :
    (2166084939 / 3125000000 : ℝ) ≤ log 2 ∧ log 2 ≤ 8664339757 / 12500000000 := by
  have hprod : (2 : ℝ) = (16 / 15 : ℝ) ^ 7 * (25 / 24 : ℝ) ^ 5 * (81 / 80 : ℝ) ^ 3 := by norm_num
  have hlog : log 2 = 7 * log ((1 + (1 / 31 : ℝ)) / (1 - 1 / 31)) +
      5 * log ((1 + (1 / 49 : ℝ)) / (1 - 1 / 49)) +
      3 * log ((1 + (1 / 161 : ℝ)) / (1 - 1 / 161)) := by
    conv_lhs => rw [hprod]
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]
    have e1 : (16 / 15 : ℝ) = (1 + (1 / 31 : ℝ)) / (1 - 1 / 31) := by norm_num
    have e2 : (25 / 24 : ℝ) = (1 + (1 / 49 : ℝ)) / (1 - 1 / 49) := by norm_num
    have e3 : (81 / 80 : ℝ) = (1 + (1 / 161 : ℝ)) / (1 - 1 / 161) := by norm_num
    rw [e1, e2, e3]
    ring
  have b1 := log_ratio_bounds_3 (u := (1 / 31 : ℝ)) (by norm_num) (by norm_num)
  have b2 := log_ratio_bounds_3 (u := (1 / 49 : ℝ)) (by norm_num) (by norm_num)
  have b3 := log_ratio_bounds_3 (u := (1 / 161 : ℝ)) (by norm_num) (by norm_num)
  rw [hlog]
  constructor <;> linarith

private lemma continuousOn_inv_log_Icc {b : ℝ} (_hb0 : 0 ≤ b) (hb1 : b < 1) :
    ContinuousOn (fun t : ℝ => 1 / log t) (Icc 0 b) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    apply ContinuousAt.continuousWithinAt
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hlog := (Filter.tendsto_atBot.mp Real.tendsto_log_nhdsNE_zero) (-(1 / ε) - 1)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hlog
    obtain ⟨δ, hδ, hball⟩ := hlog
    refine ⟨δ, hδ, fun x hx => ?_⟩
    by_cases hx0 : x = 0
    · subst hx0; simp [hε]
    · have hle : log x ≤ -(1 / ε) - 1 := hball hx hx0
      have hneg : log x < 0 := by
        have : 0 < 1 / ε := by positivity
        linarith
      simp only [Real.log_zero, div_zero, dist_zero_right, Real.norm_eq_abs]
      rw [abs_of_neg (div_neg_of_pos_of_neg zero_lt_one hneg)]
      have hden : 1 / ε < -log x := by linarith
      have hlt_inv : 1 / (-log x) < 1 / (1 / ε) :=
        one_div_lt_one_div_of_lt (by positivity) hden
      have heq1 : -(1 / log x) = 1 / (-log x) := by ring
      have heq2 : 1 / (1 / ε) = ε := one_div_one_div ε
      linarith
  · apply ContinuousAt.continuousWithinAt
    have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hlt1 : t < 1 := lt_of_le_of_lt ht.2 hb1
    have hlne : log t ≠ 0 := (Real.log_neg hpos hlt1).ne
    exact continuousAt_const.div (Real.continuousAt_log ht0) hlne

private noncomputable def E (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp u - ∑ k ∈ Finset.range (n + 1), u ^ k / (k.factorial : ℝ)

private lemma E_zero_at_zero (n : ℕ) : E n 0 = 0 := by
  simp [E, Finset.sum_range_succ']

private lemma hasDerivAt_E (n : ℕ) (u : ℝ) : HasDerivAt (E (n + 1)) (E n u) u := by
  have hexp : HasDerivAt Real.exp (Real.exp u) u := Real.hasDerivAt_exp u
  have hd_terms : ∀ k ∈ Finset.range (n + 1),
      HasDerivAt (fun x : ℝ => x ^ (k + 1) / ((k + 1).factorial : ℝ))
        (u ^ k / (k.factorial : ℝ)) u := by
    intro k _
    refine mk_hasDerivAt ((hasDerivAt_pow (k + 1) u).div_const ((k + 1).factorial : ℝ))
      (fun _ => rfl) ?_
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    have hne : (k : ℝ) + 1 ≠ 0 := by positivity
    have hfne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
  have hsum_deriv : HasDerivAt
      (fun x : ℝ => ∑ k ∈ Finset.range (n + 2), x ^ k / (k.factorial : ℝ))
      (∑ k ∈ Finset.range (n + 1), u ^ k / (k.factorial : ℝ)) u := by
    refine mk_hasDerivAt ((hasDerivAt_const u (1 : ℝ)).add (HasDerivAt.sum hd_terms))
      (fun x => ?_) (by ring)
    rw [Finset.sum_range_succ']
    simp [Finset.sum_apply, add_comm]
  exact mk_hasDerivAt (hexp.sub hsum_deriv) (fun _ => rfl) rfl

private lemma E_signs : ∀ m : ℕ,
    (∀ u : ℝ, 0 ≤ E (2 * m + 1) u) ∧
    (∀ u : ℝ, (u ≤ 0 → E (2 * m + 2) u ≤ 0) ∧ (0 ≤ u → 0 ≤ E (2 * m + 2) u)) := by
  have step_even : ∀ n : ℕ, (∀ u : ℝ, 0 ≤ E n u) →
      (∀ u : ℝ, (u ≤ 0 → E (n + 1) u ≤ 0) ∧ (0 ≤ u → 0 ≤ E (n + 1) u)) := by
    intro n hnonneg u
    have hdiff : Differentiable ℝ (E (n + 1)) := fun x => (hasDerivAt_E n x).differentiableAt
    have hmono : Monotone (E (n + 1)) := by
      apply monotone_of_deriv_nonneg hdiff
      intro x
      rw [(hasDerivAt_E n x).deriv]
      exact hnonneg x
    constructor
    · intro hu; simpa [E_zero_at_zero] using hmono hu
    · intro hu; simpa [E_zero_at_zero] using hmono hu
  intro m
  induction m with
  | zero =>
    have h1 : ∀ u : ℝ, 0 ≤ E 1 u := by
      intro u
      simp only [E, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one]
      linarith [Real.add_one_le_exp u]
    exact ⟨h1, step_even 1 h1⟩
  | succ m ih =>
    have heven := ih.2
    have hodd : ∀ u : ℝ, 0 ≤ E (2 * (m + 1) + 1) u := by
      intro u
      have hidx : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
      rw [hidx]
      have hd : ∀ x : ℝ, HasDerivAt (E ((2 * m + 2) + 1)) (E (2 * m + 2) x) x :=
        hasDerivAt_E (2 * m + 2)
      rcases lt_trichotomy u 0 with hlt | rfl | hgt
      · obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope (E ((2 * m + 2) + 1)) (E (2 * m + 2)) hlt
          (fun x _ => (hd x).continuousAt.continuousWithinAt)
          (fun x _ => hd x)
        rw [E_zero_at_zero, zero_sub, zero_sub] at hc_eq
        have hc_le : E (2 * m + 2) c ≤ 0 := (heven c).1 hc.2.le
        have hu_ne : u ≠ 0 := hlt.ne
        have : E ((2 * m + 2) + 1) u = E (2 * m + 2) c * u := by
          field_simp [hu_ne] at hc_eq ⊢; linarith
        rw [this]; nlinarith
      · simp [E_zero_at_zero]
      · obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope (E ((2 * m + 2) + 1)) (E (2 * m + 2)) hgt
          (fun x _ => (hd x).continuousAt.continuousWithinAt)
          (fun x _ => hd x)
        rw [E_zero_at_zero, sub_zero, sub_zero] at hc_eq
        have hc_ge : 0 ≤ E (2 * m + 2) c := (heven c).2 hc.1.le
        have hpos : u ≠ 0 := by linarith
        have : E ((2 * m + 2) + 1) u = E (2 * m + 2) c * u := by
          field_simp [hpos] at hc_eq ⊢; linarith
        rw [this]; exact mul_nonneg hc_ge hgt.le
    exact ⟨hodd, step_even (2 * (m + 1) + 1) hodd⟩

private noncomputable def F20 (t : ℝ) : ℝ :=
  log (|log t|) + ∑ k ∈ Finset.Icc (1 : ℕ) 20, (log t) ^ k / ((k : ℝ) * (k.factorial : ℝ))

private noncomputable def F20' (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 21, (log t) ^ k / (k.factorial : ℝ)) / (t * log t)

private noncomputable def R20 (t : ℝ) : ℝ :=
  if t = 1 then 0 else E 20 (log t) / (t * log t)

private lemma hasDerivAt_F20 {t : ℝ} (ht0 : 0 < t) (ht1 : t ≠ 1) :
    HasDerivAt F20 (F20' t) t := by
  have hlne : log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht0 ht1
  have ht_ne : t ≠ 0 := ht0.ne'
  have hd_abs : HasDerivAt (fun x => log (|log x|)) ((t * log t)⁻¹) t := by
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hev : (fun x => log (|log x|)) =ᶠ[𝓝 t] (fun x => log (-log x)) := by
        filter_upwards [Ioo_mem_nhds ht0 hlt] with x hx
        rw [abs_of_neg (Real.log_neg hx.1 hx.2)]
      apply HasDerivAt.congr_of_eventuallyEq _ hev
      have hneg : -log t ≠ 0 := neg_ne_zero.mpr hlne
      exact mk_hasDerivAt (((Real.hasDerivAt_log ht_ne).neg).log hneg) (fun _ => rfl)
        (by simp only [Pi.neg_apply]; field_simp)
    · have hev : (fun x => log (|log x|)) =ᶠ[𝓝 t] (fun x => log (log x)) := by
        filter_upwards [Ioi_mem_nhds hgt] with x hx
        rw [abs_of_pos (Real.log_pos hx)]
      apply HasDerivAt.congr_of_eventuallyEq _ hev
      exact mk_hasDerivAt ((Real.hasDerivAt_log ht_ne).log hlne) (fun _ => rfl) (by field_simp)
  have hd_sum : ∀ k ∈ Finset.Icc (1 : ℕ) 20,
      HasDerivAt (fun x => (log x) ^ k / ((k : ℝ) * (k.factorial : ℝ)))
        ((log t) ^ k / ((k.factorial : ℝ) * (t * log t))) t := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hf_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hpow : HasDerivAt (fun x => (log x) ^ k) (↑k * (log t) ^ (k - 1) * t⁻¹) t :=
      mk_hasDerivAt ((hasDerivAt_pow k (log t)).comp t (Real.hasDerivAt_log ht_ne))
        (fun _ => rfl) (by ring)
    refine mk_hasDerivAt (hpow.div_const ((k : ℝ) * (k.factorial : ℝ))) (fun _ => rfl) ?_
    have hpow_eq : (log t) ^ k = (log t) ^ (k - 1) * log t := by
      conv_lhs => rw [← Nat.sub_add_cancel hk1, pow_succ]
    rw [hpow_eq]
    field_simp
  refine mk_hasDerivAt (hd_abs.add (HasDerivAt.sum hd_sum))
    (fun x => by dsimp [F20]; simp [Finset.sum_apply]) ?_
  simp only [F20']
  have hrange : Finset.range 21 = insert 0 (Finset.Icc (1 : ℕ) 20) := by decide
  rw [hrange, Finset.sum_insert (by decide)]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, add_div, Finset.sum_div]
  congr 1
  · field_simp
  · apply Finset.sum_congr rfl
    intro k _
    ring

private lemma inv_log_eq_F20'_add_R20 {t : ℝ} (ht0 : 0 < t) (ht1 : t ≠ 1) :
    1 / log t = F20' t + R20 t := by
  have hlne : log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht0 ht1
  have ht_ne : t ≠ 0 := ht0.ne'
  simp only [F20', R20, if_neg ht1, E, Real.exp_log ht0]
  field_simp
  ring

private lemma R20_nonneg {t : ℝ} (ht0 : 0 < t) : 0 ≤ R20 t := by
  by_cases ht1 : t = 1
  · simp [R20, ht1]
  · simp only [R20, if_neg ht1]
    have hs := (E_signs 9).2 (log t)
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hl : log t < 0 := Real.log_neg ht0 hlt
      have hE : E 20 (log t) ≤ 0 := hs.1 hl.le
      exact div_nonneg_of_nonpos hE (mul_nonpos_of_nonneg_of_nonpos ht0.le hl.le)
    · have hl : 0 < log t := Real.log_pos hgt
      have hE : 0 ≤ E 20 (log t) := hs.2 hl.le
      exact div_nonneg hE (by positivity)

private lemma continuousOn_R20 : ContinuousOn R20 (Icc (1 / 256 : ℝ) 2) := by
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  by_cases ht1 : t = 1
  · subst ht1
    let g : ℝ → ℝ := fun u =>
      (if u = 0 then 1 else (Real.exp u - 1) / u) - 1 -
        ∑ k ∈ Finset.Icc (2 : ℕ) 20, u ^ (k - 1) / (k.factorial : ℝ)
    have hg0 : g 0 = 0 := by
      have hsum0 : ∑ k ∈ Finset.Icc (2 : ℕ) 20, (0 : ℝ) ^ (k - 1) / (k.factorial : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        rw [zero_pow (by omega), zero_div]
      simp [g, hsum0]
    have hg_cont : ContinuousAt g 0 := by
      have hslope : ContinuousAt (fun u : ℝ => if u = 0 then (1 : ℝ) else (Real.exp u - 1) / u) 0 := by
        rw [continuousAt_iff_punctured_nhds]
        simp only [if_true]
        have hd := (Real.hasDerivAt_exp 0).tendsto_slope_zero
        rw [Real.exp_zero] at hd
        refine hd.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
        simp [hu, smul_eq_mul, div_eq_inv_mul]
      have hpoly : ContinuousAt
          (fun u : ℝ => ∑ k ∈ Finset.Icc (2 : ℕ) 20, u ^ (k - 1) / (k.factorial : ℝ)) 0 :=
        continuousAt_finset_sum_real _ (fun k _ => (continuousAt_id.pow (k - 1)).div_const _)
      exact (hslope.sub continuousAt_const).sub hpoly
    have hg_log : ContinuousAt (fun x : ℝ => g (log x)) 1 := by
      have hg_at : ContinuousAt g (log 1) := by rw [Real.log_one]; exact hg_cont
      exact ContinuousAt.comp hg_at (Real.continuousAt_log one_ne_zero)
    have hcomp : ContinuousAt (fun x : ℝ => g (log x) / x) 1 :=
      hg_log.div continuousAt_id one_ne_zero
    refine hcomp.congr (Filter.EventuallyEq.symm ?_)
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with x hx
    by_cases hx1 : x = 1
    · subst hx1; simp [R20, hg0]
    · have hlne : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
      have hx_ne : x ≠ 0 := hx.ne'
      simp only [R20, if_neg hx1, g, if_neg hlne, E]
      have hrange : Finset.range 21 = insert 0 (insert 1 (Finset.Icc (2 : ℕ) 20)) := by decide
      rw [hrange, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one]
      have hsum_mul : ∀ k ∈ Finset.Icc (2 : ℕ) 20,
          log x * ((log x) ^ (k - 1) / (k.factorial : ℝ)) = (log x) ^ k / (k.factorial : ℝ) := by
        intro k hk
        have hk1 : 1 ≤ k := le_trans (by decide : 1 ≤ 2) (Finset.mem_Icc.mp hk).1
        rw [mul_div_assoc', mul_comm (log x), ← pow_succ, Nat.sub_add_cancel hk1]
      field_simp
      rw [Finset.mul_sum]
      have hsc : ∑ k ∈ Finset.Icc (2 : ℕ) 20, log x * ((log x) ^ (k - 1) / (k.factorial : ℝ)) =
          ∑ k ∈ Finset.Icc (2 : ℕ) 20, (log x) ^ k / (k.factorial : ℝ) :=
        Finset.sum_congr rfl hsum_mul
      rw [hsc]
      ring
  · have hlne : log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht0 ht1
    have hev : R20 =ᶠ[𝓝 t] (fun x => E 20 (log x) / (x * log x)) := by
      filter_upwards [IsOpen.mem_nhds (isOpen_Ioi.inter isOpen_ne) ⟨ht0, ht1⟩] with x hx
      have hx1 : x ≠ 1 := hx.2
      simp [R20, hx1]
    apply ContinuousAt.congr _ hev.symm
    have hE_cont : ContinuousAt (E 20) (log t) :=
      (Real.continuous_exp.continuousAt).sub
        (continuousAt_finset_sum_real _ (fun k _ => (continuousAt_id.pow k).div_const _))
    exact (ContinuousAt.comp hE_cont (Real.continuousAt_log ht0.ne')).div
      (continuousAt_id.mul (Real.continuousAt_log ht0.ne')) (mul_ne_zero ht0.ne' hlne)

private lemma tendsto_F20_symm :
    Tendsto (fun e : ℝ => F20 (1 - e) - F20 (1 + e)) (𝓝[>] 0) (𝓝 0) := by
  have hd_minus : HasDerivAt (fun x : ℝ => -log (1 - x)) 1 0 := by
    have hsub : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1) 0 :=
      (hasDerivAt_const 0 (1 : ℝ)).sub (hasDerivAt_id 0)
    exact mk_hasDerivAt ((hsub.log (by norm_num)).neg) (fun _ => rfl) (by norm_num)
  have hd_plus : HasDerivAt (fun x : ℝ => log (1 + x)) 1 0 :=
    mk_hasDerivAt (((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)) (fun _ => rfl) (by norm_num)
  have ht_minus : Tendsto (fun e : ℝ => (-log (1 - e)) / e) (𝓝[>] 0) (𝓝 1) := by
    have h := hd_minus.tendsto_slope_zero_right
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have ht_plus : Tendsto (fun e : ℝ => log (1 + e) / e) (𝓝[>] 0) (𝓝 1) := by
    have h := hd_plus.tendsto_slope_zero_right
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have ht_ratio : Tendsto (fun e : ℝ => (-log (1 - e)) / log (1 + e)) (𝓝[>] 0) (𝓝 1) := by
    have hdiv := ht_minus.div ht_plus one_ne_zero
    rw [div_one] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with e he
    have he_ne : e ≠ 0 := he.1.ne'
    have hlp_ne : log (1 + e) ≠ 0 := (Real.log_pos (by linarith [he.1])).ne'
    simp only [Pi.div_apply]
    field_simp
  have ht_log_part : Tendsto (fun e : ℝ => log (|log (1 - e)|) - log (|log (1 + e)|))
      (𝓝[>] 0) (𝓝 0) := by
    have hlog_comp : Tendsto (fun e : ℝ => log ((-log (1 - e)) / log (1 + e))) (𝓝[>] 0) (𝓝 0) := by
      have hc := (Real.continuousAt_log one_ne_zero).tendsto.comp ht_ratio
      rw [Real.log_one] at hc
      exact hc
    refine hlog_comp.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with e he
    have h1 : log (1 - e) < 0 := Real.log_neg (by linarith [he.2]) (by linarith [he.1])
    have h2 : 0 < log (1 + e) := Real.log_pos (by linarith [he.1])
    rw [abs_of_neg h1, abs_of_pos h2, Real.log_div (by linarith) h2.ne']
  have ht_poly_minus : ContinuousAt
      (fun e : ℝ => ∑ k ∈ Finset.Icc (1 : ℕ) 20, (log (1 - e)) ^ k / ((k : ℝ) * (k.factorial : ℝ))) 0 := by
    apply continuousAt_finset_sum_real
    intro k _
    have hlog_c : ContinuousAt (fun e : ℝ => log (1 - e)) 0 :=
      ContinuousAt.comp (Real.continuousAt_log (by norm_num : (1 - (0 : ℝ)) ≠ 0))
        (continuousAt_const.sub continuousAt_id)
    exact (hlog_c.pow k).div_const _
  have ht_poly_plus : ContinuousAt
      (fun e : ℝ => ∑ k ∈ Finset.Icc (1 : ℕ) 20, (log (1 + e)) ^ k / ((k : ℝ) * (k.factorial : ℝ))) 0 := by
    apply continuousAt_finset_sum_real
    intro k _
    have hlog_c : ContinuousAt (fun e : ℝ => log (1 + e)) 0 :=
      ContinuousAt.comp (Real.continuousAt_log (by norm_num : (1 + (0 : ℝ)) ≠ 0))
        (continuousAt_const.add continuousAt_id)
    exact (hlog_c.pow k).div_const _
  have hsum0 : ∑ k ∈ Finset.Icc (1 : ℕ) 20, (0 : ℝ) ^ k / ((k : ℝ) * (k.factorial : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [zero_pow (by omega), zero_div]
  have ht_pm : Tendsto
      (fun e : ℝ => ∑ k ∈ Finset.Icc (1 : ℕ) 20, (log (1 - e)) ^ k / ((k : ℝ) * (k.factorial : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ht_poly_minus.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [hsum0] using h
  have ht_pp : Tendsto
      (fun e : ℝ => ∑ k ∈ Finset.Icc (1 : ℕ) 20, (log (1 + e)) ^ k / ((k : ℝ) * (k.factorial : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ht_poly_plus.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [hsum0] using h
  have hall := ht_log_part.add (ht_pm.sub ht_pp)
  rw [sub_zero, add_zero] at hall
  refine hall.congr (fun e => ?_)
  dsimp [F20]
  ring

private lemma liPart_two_tendsto :
    Tendsto (liPart 2) (𝓝[>] 0)
      (𝓝 ((∫ t in (0 : ℝ)..(1 / 256), 1 / log t) +
        (F20 2 - F20 (1 / 256)) +
        (∫ t in (1 / 256 : ℝ)..2, R20 t))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn continuousOn_R20
  have hC_pos : 0 < C + 1 := by
    have h1 := hC 1 ⟨by norm_num, by norm_num⟩
    linarith [norm_nonneg (R20 1)]
  have hR_int : ∀ a b : ℝ, 1 / 256 ≤ a → a ≤ b → b ≤ 2 → IntervalIntegrable R20 volume a b := by
    intro a b ha hab hb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_R20.mono (Icc_subset_Icc ha hb)
  have ht_R_left : Tendsto (fun e : ℝ => ∫ t in (1 / 256 : ℝ)..(1 - e), R20 t)
      (𝓝[>] 0) (𝓝 (∫ t in (1 / 256 : ℝ)..1, R20 t)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (255 / 256) (ε / (C + 1)) by positivity)] with e he
    have he0 : 0 < e := he.1
    have he1 : e < 255 / 256 := lt_of_lt_of_le he.2 (min_le_left _ _)
    have he2 : e < ε / (C + 1) := lt_of_lt_of_le he.2 (min_le_right _ _)
    have hsplit := integral_add_adjacent_intervals
      (hR_int (1 / 256) (1 - e) (by norm_num) (by linarith) (by linarith))
      (hR_int (1 - e) 1 (by linarith) (by linarith) (by norm_num))
    have hdiff : (∫ t in (1 / 256 : ℝ)..(1 - e), R20 t) - (∫ t in (1 / 256 : ℝ)..1, R20 t) =
        -(∫ t in (1 - e)..1, R20 t) := by linarith
    rw [dist_eq_norm, hdiff, norm_neg]
    have hbd : ‖∫ t in (1 - e)..1, R20 t‖ ≤ (C + 1) * |1 - (1 - e)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hx_mem : x ∈ Icc (1 / 256 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      linarith [hC x hx_mem]
    have habs : |1 - (1 - e)| = e := by
      have : 1 - (1 - e) = e := by ring
      rw [this, abs_of_pos he0]
    rw [habs] at hbd
    have hlt : (C + 1) * e < ε := (lt_div_iff₀' hC_pos).mp he2
    linarith
  have ht_R_right : Tendsto (fun e : ℝ => ∫ t in (1 + e)..2, R20 t)
      (𝓝[>] 0) (𝓝 (∫ t in (1 : ℝ)..2, R20 t)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (ε / (C + 1)) by positivity)] with e he
    have he0 : 0 < e := he.1
    have he1 : e < 1 := lt_of_lt_of_le he.2 (min_le_left _ _)
    have he2 : e < ε / (C + 1) := lt_of_lt_of_le he.2 (min_le_right _ _)
    have hsplit := integral_add_adjacent_intervals
      (hR_int 1 (1 + e) (by norm_num) (by linarith) (by linarith))
      (hR_int (1 + e) 2 (by linarith) (by linarith) (by norm_num))
    have hdiff : (∫ t in (1 + e)..2, R20 t) - (∫ t in (1 : ℝ)..2, R20 t) =
        -(∫ t in (1 : ℝ)..(1 + e), R20 t) := by linarith
    rw [dist_eq_norm, hdiff, norm_neg]
    have hbd : ‖∫ t in (1 : ℝ)..(1 + e), R20 t‖ ≤ (C + 1) * |1 + e - 1| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hx_mem : x ∈ Icc (1 / 256 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      linarith [hC x hx_mem]
    have habs : |1 + e - 1| = e := by
      have : 1 + e - 1 = e := by ring
      rw [this, abs_of_pos he0]
    rw [habs] at hbd
    have hlt : (C + 1) * e < ε := (lt_div_iff₀' hC_pos).mp he2
    linarith
  have hR_whole := integral_add_adjacent_intervals
    (hR_int (1 / 256) 1 (by norm_num) (by norm_num) (by norm_num))
    (hR_int 1 2 (by norm_num) (by norm_num) (by norm_num))
  have ht_comb := ((tendsto_const_nhds (x := (∫ t in (0 : ℝ)..(1 / 256), 1 / log t) +
      (F20 2 - F20 (1 / 256)))).add tendsto_F20_symm).add (ht_R_left.add ht_R_right)
  rw [add_zero, hR_whole] at ht_comb
  refine ht_comb.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 255 / 256)] with e he
  have he0 : 0 < e := he.1
  have he1 : e < 255 / 256 := he.2
  have hint_0_left : IntervalIntegrable (fun t => 1 / log t) volume 0 (1 / 256) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact continuousOn_inv_log_Icc (by norm_num) (by norm_num)
  have hint_mid_left : IntervalIntegrable (fun t => 1 / log t) volume (1 / 256) (1 - e) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact (continuousOn_inv_log_Icc (by linarith) (by linarith)).mono
      (Icc_subset_Icc (by norm_num) le_rfl)
  have hsplit0 := (integral_add_adjacent_intervals hint_0_left hint_mid_left).symm
  have hF'_left_cont : ContinuousOn F20' (uIcc (1 / 256 : ℝ) (1 - e)) := by
    rw [uIcc_of_le (by linarith)]
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : x < 1 := by linarith [hx.2]
    have hlne : log x ≠ 0 := (Real.log_neg hx0 hx1).ne
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_finset_sum_real _ (fun k _ => ((Real.continuousAt_log hx0.ne').pow k).div_const _)).div
      (continuousAt_id.mul (Real.continuousAt_log hx0.ne')) (mul_ne_zero hx0.ne' hlne)
  have hF_left_int : ∫ t in (1 / 256 : ℝ)..(1 - e), F20' t = F20 (1 - e) - F20 (1 / 256) := by
    apply integral_eq_sub_of_hasDerivAt _ hF'_left_cont.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact hasDerivAt_F20 (by linarith [hx.1]) (by linarith [hx.2])
  have hdecomp_left : ∫ t in (1 / 256 : ℝ)..(1 - e), 1 / log t =
      (F20 (1 - e) - F20 (1 / 256)) + ∫ t in (1 / 256 : ℝ)..(1 - e), R20 t := by
    have heq : EqOn (fun t => 1 / log t) (fun t => F20' t + R20 t) (uIcc (1 / 256 : ℝ) (1 - e)) := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      exact inv_log_eq_F20'_add_R20 (by linarith [hx.1]) (by linarith [hx.2])
    rw [integral_congr heq, integral_add hF'_left_cont.intervalIntegrable
      (hR_int (1 / 256) (1 - e) (by norm_num) (by linarith) (by linarith)), hF_left_int]
  have hF'_right_cont : ContinuousOn F20' (uIcc (1 + e) 2) := by
    rw [uIcc_of_le (by linarith)]
    intro x hx
    have hx1 : 1 < x := by linarith [hx.1]
    have hx0 : 0 < x := by linarith
    have hlne : log x ≠ 0 := (Real.log_pos hx1).ne'
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_finset_sum_real _ (fun k _ => ((Real.continuousAt_log hx0.ne').pow k).div_const _)).div
      (continuousAt_id.mul (Real.continuousAt_log hx0.ne')) (mul_ne_zero hx0.ne' hlne)
  have hF_right_int : ∫ t in (1 + e)..2, F20' t = F20 2 - F20 (1 + e) := by
    apply integral_eq_sub_of_hasDerivAt _ hF'_right_cont.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact hasDerivAt_F20 (by linarith [hx.1]) (by linarith [hx.1])
  have hdecomp_right : ∫ t in (1 + e)..2, 1 / log t =
      (F20 2 - F20 (1 + e)) + ∫ t in (1 + e)..2, R20 t := by
    have heq : EqOn (fun t => 1 / log t) (fun t => F20' t + R20 t) (uIcc (1 + e) 2) := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      exact inv_log_eq_F20'_add_R20 (by linarith [hx.1]) (by linarith [hx.1])
    rw [integral_congr heq, integral_add hF'_right_cont.intervalIntegrable
      (hR_int (1 + e) 2 (by linarith) (by linarith) (by norm_num)), hF_right_int]
  simp only [liPart]
  rw [hsplit0, hdecomp_left, hdecomp_right]
  ring

end

theorem solution : 1.045 ≤ liPV 2 := by
  have hne : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  have hlim : liPV 2 = (∫ t in (0 : ℝ)..(1 / 256), 1 / log t) +
      (F20 2 - F20 (1 / 256)) + (∫ t in (1 / 256 : ℝ)..2, R20 t) :=
    @Filter.Tendsto.limUnder_eq _ _ _ _ _ _ hne _ liPart_two_tendsto
  rw [hlim]
  have hln2 := ln2_bounds_11
  have hln2_pos : 0 < log 2 := by linarith [hln2.1]
  have hlog256 : log (256 : ℝ) = 8 * log 2 := by
    have : (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
    rw [this, Real.log_pow]; norm_num
  have hlog_inv256 : log (1 / 256 : ℝ) = -8 * log 2 := by
    rw [one_div, Real.log_inv, hlog256]; ring
  have htail : (1 / 256 : ℝ) / (-8 * log 2) ≤ ∫ t in (0 : ℝ)..(1 / 256), 1 / log t := by
    calc (1 / 256 : ℝ) / (-8 * log 2)
        = ∫ _t in (0 : ℝ)..(1 / 256), (1 / log (1 / 256 : ℝ)) := by
          rw [hlog_inv256, intervalIntegral.integral_const]
          simp [smul_eq_mul]; ring
      _ ≤ ∫ t in (0 : ℝ)..(1 / 256), 1 / log t := by
          refine integral_mono_on (by norm_num) intervalIntegrable_const
            (ContinuousOn.intervalIntegrable (by rw [uIcc_of_le (by norm_num)]; exact continuousOn_inv_log_Icc (by norm_num) (by norm_num))) ?_
          intro t ht
          by_cases ht0 : t = 0
          · subst ht0
            rw [Real.log_zero, div_zero, hlog_inv256]
            exact div_nonpos_of_nonneg_of_nonpos zero_le_one (by linarith)
          · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
            have hlt_log : log t ≤ log (1 / 256 : ℝ) := Real.log_le_log ht_pos ht.2
            have hlog256_neg : log (1 / 256 : ℝ) < 0 := by rw [hlog_inv256]; linarith
            have hlogt_neg : log t < 0 := lt_of_le_of_lt hlt_log hlog256_neg
            have hinv := (inv_le_inv_of_neg hlog256_neg hlogt_neg).mpr hlt_log
            simpa only [one_div] using hinv
  have hR_nonneg : 0 ≤ ∫ t in (1 / 256 : ℝ)..2, R20 t := by
    calc (0 : ℝ) = ∫ _t in (1 / 256 : ℝ)..2, (0 : ℝ) := by simp
      _ ≤ ∫ t in (1 / 256 : ℝ)..2, R20 t := by
          refine integral_mono_on (by norm_num) intervalIntegrable_const
            (ContinuousOn.intervalIntegrable (by rw [uIcc_of_le (by norm_num)]; exact continuousOn_R20)) ?_
          intro t ht
          exact R20_nonneg (by linarith [ht.1])
  have hF_diff : F20 2 - F20 (1 / 256) = -3 * log 2 +
      ∑ k ∈ Finset.Icc (1 : ℕ) 20, ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) * (log 2) ^ k := by
    dsimp only [F20]
    rw [hlog_inv256]
    have habs1 : |log 2| = log 2 := abs_of_pos hln2_pos
    have habs2 : |-8 * log 2| = 8 * log 2 := by
      rw [abs_of_neg (by linarith)]; ring
    have hlog8 : log (8 * log 2) = 3 * log 2 + log (log 2) := by
      rw [Real.log_mul (by norm_num) hln2_pos.ne']
      have : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      rw [this, Real.log_pow]; norm_num
    rw [habs1, habs2, hlog8]
    have hsum_eq : (∑ k ∈ Finset.Icc (1 : ℕ) 20, (log 2) ^ k / ((k : ℝ) * (k.factorial : ℝ))) -
        (∑ k ∈ Finset.Icc (1 : ℕ) 20, (-8 * log 2) ^ k / ((k : ℝ) * (k.factorial : ℝ))) =
        ∑ k ∈ Finset.Icc (1 : ℕ) 20, ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) * (log 2) ^ k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_pow]
      ring
    linarith
  rw [hF_diff]
  let L_lo : ℝ := 2166084939 / 3125000000
  let L_hi : ℝ := 8664339757 / 12500000000
  have hL_lo_pos : 0 < L_lo := by norm_num [L_lo]
  have htail_num : -(1 / 2048 : ℝ) / L_lo ≤ (1 / 256 : ℝ) / (-8 * log 2) := by
    have heq : (1 / 256 : ℝ) / (-8 * log 2) = -((1 / 2048 : ℝ) / log 2) := by ring
    have heq2 : -(1 / 2048 : ℝ) / L_lo = -((1 / 2048 : ℝ) / L_lo) := by ring
    rw [heq, heq2, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by norm_num) hL_lo_pos hln2.1
  have hterm_bd : ∀ k ∈ Finset.Icc (1 : ℕ) 20,
      ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) *
        (if Even k then L_hi ^ k else L_lo ^ k) ≤
      ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) * (log 2) ^ k := by
    intro k hk
    have hden_pos : 0 < (k : ℝ) * (k.factorial : ℝ) := by
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have : 0 < k.factorial := Nat.factorial_pos k
      positivity
    by_cases hev : Even k
    · simp only [if_pos hev]
      have hpow_neg8 : (-8 : ℝ) ^ k = (8 : ℝ) ^ k := hev.neg_pow 8
      have hnum_neg : (1 : ℝ) - (-8 : ℝ) ^ k ≤ 0 := by
        rw [hpow_neg8]
        have : (1 : ℝ) ≤ (8 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        linarith
      have hcoeff_nonpos : ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hnum_neg hden_pos.le
      exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hln2_pos.le hln2.2 k) hcoeff_nonpos
    · simp only [if_neg hev]
      have hodd : Odd k := Nat.not_even_iff_odd.mp hev
      have hpow_neg8 : (-8 : ℝ) ^ k = -((8 : ℝ) ^ k) := hodd.neg_pow 8
      have hnum_pos : 0 ≤ (1 : ℝ) - (-8 : ℝ) ^ k := by
        rw [hpow_neg8]
        have : (0 : ℝ) ≤ (8 : ℝ) ^ k := by positivity
        linarith
      have hcoeff_nonneg : 0 ≤ ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) :=
        div_nonneg hnum_pos hden_pos.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL_lo_pos.le hln2.1 k) hcoeff_nonneg
  have hsum_bd : ∑ k ∈ Finset.Icc (1 : ℕ) 20,
      ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) *
        (if Even k then L_hi ^ k else L_lo ^ k) ≤
      ∑ k ∈ Finset.Icc (1 : ℕ) 20, ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) * (log 2) ^ k :=
    Finset.sum_le_sum hterm_bd
  have hnum_eval : (1.045 : ℝ) ≤ -(1 / 2048 : ℝ) / L_lo - 3 * L_hi +
      ∑ k ∈ Finset.Icc (1 : ℕ) 20,
        ((1 : ℝ) - (-8 : ℝ) ^ k) / ((k : ℝ) * (k.factorial : ℝ)) *
          (if Even k then L_hi ^ k else L_lo ^ k) := by
    norm_num [L_lo, L_hi, Finset.sum_Icc_succ_top, Nat.factorial]
  linarith [hln2.2]
