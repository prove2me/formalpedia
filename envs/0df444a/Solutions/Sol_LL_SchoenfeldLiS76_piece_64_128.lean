-- Prove2me | solution 1 for LL_SchoenfeldLiS76.piece_64_128
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T00:02:51.146156+00:00
-- url     : https://prove2.me/submissions/4604d4f8-6266-4538-a7f6-0ec32be91f20

import Mathlib

open Real MeasureTheory intervalIntegral Set

section

private lemma mk_hasDerivAt {f g : ℝ → ℝ} {f' g' x : ℝ}
    (h : HasDerivAt f f' x) (hf : ∀ y, g y = f y) (hd : g' = f') : HasDerivAt g g' x := by
  have heq : g = f := funext hf
  rw [heq, hd]
  exact h

private lemma log_ratio_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    2 * u + 2 / 3 * u ^ 3 ≤ log ((1 + u) / (1 - u)) ∧
    log ((1 + u) / (1 - u)) ≤ 2 * u + 2 / 3 * u ^ 3 + 2 / 5 * u ^ 5 / (1 - u ^ 2) := by
  let φ : ℝ → ℝ := fun s => log (1 + s) - log (1 - s) - (2 * s + 2 / 3 * s ^ 3)
  let φ' : ℝ → ℝ := fun s => 2 * s ^ 4 / (1 - s ^ 2)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) u, HasDerivAt φ (φ' s) s := by
    intro s hs
    rw [uIcc_of_le hu0] at hs
    have hs1 : 0 < 1 + s := by linarith [hs.1]
    have hs2 : 0 < 1 - s := by linarith [hs.2]
    have hd1 : HasDerivAt (fun x => log (1 + x)) ((1 + s)⁻¹) s := by
      have h := ((hasDerivAt_id s).const_add (1 : ℝ)).log hs1.ne'
      exact mk_hasDerivAt h (fun _ => rfl) (by simp)
    have hd2 : HasDerivAt (fun x => log (1 - x)) (-(1 - s)⁻¹) s := by
      have hsub : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1) s :=
        (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
      exact mk_hasDerivAt (hsub.log hs2.ne') (fun _ => rfl) (by ring)
    have hd3 : HasDerivAt (fun x : ℝ => 2 * x + 2 / 3 * x ^ 3) (2 + 2 * s ^ 2) s := by
      have hp1 : HasDerivAt (fun x : ℝ => 2 * x) (2 * 1) s := (hasDerivAt_id s).const_mul (2 : ℝ)
      have hp3 : HasDerivAt (fun x : ℝ => 2 / 3 * x ^ 3) (2 / 3 * (↑(3 : ℕ) * s ^ (3 - 1))) s :=
        (hasDerivAt_pow 3 s).const_mul ((2 : ℝ) / 3)
      exact mk_hasDerivAt (hp1.add hp3) (fun _ => rfl) (by norm_num; ring)
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
    exact (continuousAt_const.mul (continuousAt_id.pow 4)).div
      (continuousAt_const.sub (continuousAt_id.pow 2)) (by nlinarith [hs.1, hs.2])
  have hint_eq : ∫ s in (0 : ℝ)..u, φ' s = log ((1 + u) / (1 - u)) - (2 * u + 2 / 3 * u ^ 3) := by
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
  let ψ : ℝ → ℝ := fun s => 2 / 5 * s ^ 5 / (1 - u ^ 2)
  let ψ' : ℝ → ℝ := fun s => 2 * s ^ 4 / (1 - u ^ 2)
  have hψderiv : ∀ s ∈ uIcc (0 : ℝ) u, HasDerivAt ψ (ψ' s) s := by
    intro s _
    have h := ((hasDerivAt_pow 5 s).const_mul ((2 : ℝ) / 5)).div_const (1 - u ^ 2)
    exact mk_hasDerivAt h (fun _ => rfl) (by dsimp [ψ']; norm_num; ring)
  have hψcont : ContinuousOn ψ' (uIcc (0 : ℝ) u) :=
    ((continuous_const.mul (continuous_pow 4)).div_const (1 - u ^ 2)).continuousOn
  have hψint : ∫ s in (0 : ℝ)..u, ψ' s = 2 / 5 * u ^ 5 / (1 - u ^ 2) := by
    rw [integral_eq_sub_of_hasDerivAt hψderiv hψcont.intervalIntegrable]
    simp [ψ]
  have hhi : ∫ s in (0 : ℝ)..u, φ' s ≤ 2 / 5 * u ^ 5 / (1 - u ^ 2) := by
    rw [← hψint]
    refine integral_mono_on hu0 hcont.intervalIntegrable hψcont.intervalIntegrable ?_
    intro s hs
    exact div_le_div_of_nonneg_left (by positivity) (by nlinarith [hs.1, hs.2]) (by nlinarith [hs.1, hs.2])
  rw [hint_eq] at hlo hhi
  constructor <;> linarith

private lemma ln2_bounds :
    (693147075 : ℝ) / 1000000000 ≤ log 2 ∧ log 2 ≤ 693147181 / 1000000000 := by
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
  have b1 := log_ratio_bounds (u := (1 / 31 : ℝ)) (by norm_num) (by norm_num)
  have b2 := log_ratio_bounds (u := (1 / 49 : ℝ)) (by norm_num) (by norm_num)
  have b3 := log_ratio_bounds (u := (1 / 161 : ℝ)) (by norm_num) (by norm_num)
  rw [hlog]
  constructor <;> linarith

private noncomputable def f0 (t : ℝ) : ℝ := (log t)⁻¹
private noncomputable def f1 (t : ℝ) : ℝ := -(t * (log t) ^ 2)⁻¹
private noncomputable def f2 (t : ℝ) : ℝ := (t ^ 2 * (log t) ^ 2)⁻¹ + 2 * (t ^ 2 * (log t) ^ 3)⁻¹
private noncomputable def f3 (t : ℝ) : ℝ :=
  -(2 * (t ^ 3 * (log t) ^ 2)⁻¹ + 6 * (t ^ 3 * (log t) ^ 3)⁻¹ + 6 * (t ^ 3 * (log t) ^ 4)⁻¹)

private lemma hasDerivAt_inv_pow_log (m k : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x => (x ^ m * (log x) ^ k)⁻¹)
      (-(↑m * (t ^ (m + 1) * (log t) ^ k)⁻¹ + ↑k * (t ^ (m + 1) * (log t) ^ (k + 1))⁻¹)) t := by
  have ht0 : 0 < t := by linarith
  have hlt0 : 0 < log t := Real.log_pos ht
  have hd1 : HasDerivAt (fun x => x ^ m) (↑m * t ^ (m - 1)) t := hasDerivAt_pow m t
  have hd2 : HasDerivAt (fun x => (log x) ^ k) (↑k * (log t) ^ (k - 1) * t⁻¹) t :=
    mk_hasDerivAt ((hasDerivAt_pow k (log t)).comp t (Real.hasDerivAt_log ht0.ne'))
      (fun _ => rfl) (by ring)
  have hmul : HasDerivAt (fun x => x ^ m * (log x) ^ k)
      (↑m * t ^ (m - 1) * (log t) ^ k + t ^ m * (↑k * (log t) ^ (k - 1) * t⁻¹)) t :=
    mk_hasDerivAt (hd1.mul hd2) (fun _ => rfl) rfl
  have hne : t ^ m * (log t) ^ k ≠ 0 := by positivity
  refine mk_hasDerivAt (hmul.inv hne) (fun _ => rfl) ?_
  have ht_ne : t ≠ 0 := ht0.ne'
  have hl_ne : log t ≠ 0 := hlt0.ne'
  cases m with
  | zero =>
    cases k with
    | zero => norm_num
    | succ k' =>
      simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul, zero_add, Nat.add_sub_cancel]
      field_simp
      ring
  | succ m' =>
    cases k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, mul_zero, pow_zero, mul_one, add_zero, Nat.add_sub_cancel]
      field_simp
      ring
    | succ k' =>
      simp only [Nat.add_sub_cancel]
      field_simp
      ring

private lemma hasDerivAt_f0 {t : ℝ} (ht : 1 < t) : HasDerivAt f0 (f1 t) t := by
  refine mk_hasDerivAt (hasDerivAt_inv_pow_log 0 1 ht) (fun x => by simp [f0]) ?_
  simp [f1]

private lemma hasDerivAt_f1 {t : ℝ} (ht : 1 < t) : HasDerivAt f1 (f2 t) t := by
  refine mk_hasDerivAt (hasDerivAt_inv_pow_log 1 2 ht).neg (fun x => by simp [f1]) ?_
  simp only [f2]
  norm_num

private lemma hasDerivAt_f2 {t : ℝ} (ht : 1 < t) : HasDerivAt f2 (f3 t) t := by
  have h1 := hasDerivAt_inv_pow_log 2 2 ht
  have h2 := (hasDerivAt_inv_pow_log 2 3 ht).const_mul 2
  refine mk_hasDerivAt (h1.add h2) (fun x => by simp [f2]) ?_
  simp only [f3]
  norm_num
  ring

private lemma f3_monotoneOn : MonotoneOn f3 (Ioi 1) := by
  intro x hx y hy hxy
  have hx1 : 1 < x := hx
  have hy1 : 1 < y := hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : 0 < log x := Real.log_pos hx1
  have hly : 0 < log y := Real.log_pos hy1
  have hlxy : log x ≤ log y := Real.log_le_log hx0 hxy
  have hp3 : x ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hx0.le hxy 3
  have hlp (k : ℕ) : (log x) ^ k ≤ (log y) ^ k := pow_le_pow_left₀ hlx.le hlxy k
  have hterm (k : ℕ) : (y ^ 3 * (log y) ^ k)⁻¹ ≤ (x ^ 3 * (log x) ^ k)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact mul_le_mul hp3 (hlp k) (by positivity) (by positivity)
  have t2 := hterm 2
  have t3 := hterm 3
  have t4 := hterm 4
  simp only [f3]
  linarith

private lemma hasDerivAt_poly3 (A B C D m x : ℝ) :
    HasDerivAt (fun y => A + B * (y - m) + C * (y - m) ^ 2 + D * (y - m) ^ 3)
      (B + 2 * C * (x - m) + 3 * D * (x - m) ^ 2) x := by
  have hsub : HasDerivAt (fun y => y - m) 1 x :=
    mk_hasDerivAt ((hasDerivAt_id x).sub_const m) (fun _ => rfl) rfl
  have hp0 : HasDerivAt (fun _ : ℝ => A) 0 x := hasDerivAt_const x A
  have hp1 : HasDerivAt (fun y => B * (y - m)) (B * 1) x := hsub.const_mul B
  have hp2 : HasDerivAt (fun y => C * (y - m) ^ 2) (C * (↑(2 : ℕ) * (x - m) ^ (2 - 1) * 1)) x :=
    mk_hasDerivAt (((hasDerivAt_pow 2 (x - m)).comp x hsub).const_mul C) (fun _ => rfl) rfl
  have hp3 : HasDerivAt (fun y => D * (y - m) ^ 3) (D * (↑(3 : ℕ) * (x - m) ^ (3 - 1) * 1)) x :=
    mk_hasDerivAt (((hasDerivAt_pow 3 (x - m)).comp x hsub).const_mul D) (fun _ => rfl) rfl
  exact mk_hasDerivAt (((hp0.add hp1).add hp2).add hp3) (fun _ => rfl) (by norm_num; ring)

private lemma hermite_lower_pointwise {m t : ℝ} (hm : 1 < m) (ht : 1 < t) :
    f0 m + f1 m * (t - m) + 1 / 2 * f2 m * (t - m) ^ 2 + 1 / 6 * f3 m * (t - m) ^ 3 ≤ f0 t := by
  let Δ0 : ℝ → ℝ := fun x =>
    f0 x - (f0 m + f1 m * (x - m) + 1 / 2 * f2 m * (x - m) ^ 2 + 1 / 6 * f3 m * (x - m) ^ 3)
  let Δ1 : ℝ → ℝ := fun x => f1 x - (f1 m + f2 m * (x - m) + 1 / 2 * f3 m * (x - m) ^ 2)
  let Δ2 : ℝ → ℝ := fun x => f2 x - (f2 m + f3 m * (x - m))
  let Δ3 : ℝ → ℝ := fun x => f3 x - f3 m
  have hd0 : ∀ x, 1 < x → HasDerivAt Δ0 (Δ1 x) x := by
    intro x hx
    have hp := hasDerivAt_poly3 (f0 m) (f1 m) (1 / 2 * f2 m) (1 / 6 * f3 m) m x
    exact mk_hasDerivAt ((hasDerivAt_f0 hx).sub hp) (fun _ => rfl) (by dsimp [Δ1]; ring)
  have hd1 : ∀ x, 1 < x → HasDerivAt Δ1 (Δ2 x) x := by
    intro x hx
    have hp := hasDerivAt_poly3 (f1 m) (f2 m) (1 / 2 * f3 m) 0 m x
    exact mk_hasDerivAt ((hasDerivAt_f1 hx).sub hp) (fun y => by dsimp [Δ1]; ring) (by dsimp [Δ2]; ring)
  have hd2 : ∀ x, 1 < x → HasDerivAt Δ2 (Δ3 x) x := by
    intro x hx
    have hp := hasDerivAt_poly3 (f2 m) (f3 m) 0 0 m x
    exact mk_hasDerivAt ((hasDerivAt_f2 hx).sub hp) (fun y => by dsimp [Δ2]; ring) (by dsimp [Δ3]; ring)
  suffices hΔ : 0 ≤ Δ0 t by simp only [Δ0] at hΔ; linarith
  rcases lt_trichotomy t m with hlt | rfl | hgt
  · obtain ⟨c1, hc1, hc1_eq⟩ := exists_hasDerivAt_eq_slope Δ0 Δ1 hlt
      (fun x hx => (hd0 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd0 x (by linarith [hx.1]))
    obtain ⟨c2, hc2, hc2_eq⟩ := exists_hasDerivAt_eq_slope Δ1 Δ2 hc1.2
      (fun x hx => (hd1 x (by linarith [hc1.1, hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd1 x (by linarith [hc1.1, hx.1]))
    obtain ⟨c3, hc3, hc3_eq⟩ := exists_hasDerivAt_eq_slope Δ2 Δ3 hc2.2
      (fun x hx => (hd2 x (by linarith [hc1.1, hc2.1, hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd2 x (by linarith [hc1.1, hc2.1, hx.1]))
    have h0m : Δ0 m = 0 := by simp [Δ0]
    have h1m : Δ1 m = 0 := by simp [Δ1]
    have h2m : Δ2 m = 0 := by simp [Δ2]
    have h3_le : Δ3 c3 ≤ 0 := by
      simp only [Δ3]
      linarith [f3_monotoneOn (show 1 < c3 by linarith [hc1.1, hc2.1, hc3.1]) hm hc3.2.le]
    have h2_ge : 0 ≤ Δ2 c2 := by
      rw [h2m, zero_sub, neg_div] at hc3_eq
      have : Δ2 c2 = -Δ3 c3 * (m - c2) := by
        have hpos : m - c2 ≠ 0 := by linarith [hc2.2]
        field_simp [hpos] at hc3_eq ⊢; linarith
      rw [this]; exact mul_nonneg (by linarith) (by linarith [hc2.2])
    have h1_le : Δ1 c1 ≤ 0 := by
      rw [h1m, zero_sub, neg_div] at hc2_eq
      have : Δ1 c1 = -Δ2 c2 * (m - c1) := by
        have hpos : m - c1 ≠ 0 := by linarith [hc1.2]
        field_simp [hpos] at hc2_eq ⊢; linarith
      rw [this]; nlinarith [hc1.2]
    rw [h0m, zero_sub, neg_div] at hc1_eq
    have : Δ0 t = -Δ1 c1 * (m - t) := by
      have hpos : m - t ≠ 0 := by linarith
      field_simp [hpos] at hc1_eq ⊢; linarith
    rw [this]; nlinarith
  · simp [Δ0]
  · obtain ⟨c1, hc1, hc1_eq⟩ := exists_hasDerivAt_eq_slope Δ0 Δ1 hgt
      (fun x hx => (hd0 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd0 x (by linarith [hx.1]))
    obtain ⟨c2, hc2, hc2_eq⟩ := exists_hasDerivAt_eq_slope Δ1 Δ2 hc1.1
      (fun x hx => (hd1 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd1 x (by linarith [hx.1]))
    obtain ⟨c3, hc3, hc3_eq⟩ := exists_hasDerivAt_eq_slope Δ2 Δ3 hc2.1
      (fun x hx => (hd2 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd2 x (by linarith [hx.1]))
    have h0m : Δ0 m = 0 := by simp [Δ0]
    have h1m : Δ1 m = 0 := by simp [Δ1]
    have h2m : Δ2 m = 0 := by simp [Δ2]
    have h3_ge : 0 ≤ Δ3 c3 := by
      simp only [Δ3]
      linarith [f3_monotoneOn hm (show 1 < c3 by linarith [hc3.1]) hc3.1.le]
    have h2_ge : 0 ≤ Δ2 c2 := by
      rw [h2m, sub_zero] at hc3_eq
      have : Δ2 c2 = Δ3 c3 * (c2 - m) := by
        have hpos : c2 - m ≠ 0 := by linarith [hc2.1]
        field_simp [hpos] at hc3_eq ⊢; linarith
      rw [this]; exact mul_nonneg h3_ge (by linarith [hc2.1])
    have h1_ge : 0 ≤ Δ1 c1 := by
      rw [h1m, sub_zero] at hc2_eq
      have : Δ1 c1 = Δ2 c2 * (c1 - m) := by
        have hpos : c1 - m ≠ 0 := by linarith [hc1.1]
        field_simp [hpos] at hc2_eq ⊢; linarith
      rw [this]; exact mul_nonneg h2_ge (by linarith [hc1.1])
    rw [h0m, sub_zero] at hc1_eq
    have : Δ0 t = Δ1 c1 * (t - m) := by
      have hpos : t - m ≠ 0 := by linarith
      field_simp [hpos] at hc1_eq ⊢; linarith
    rw [this]; exact mul_nonneg h1_ge (by linarith)

private lemma contradict_three_points {h2 h3 : ℝ → ℝ}
    (hmono : MonotoneOn h3 (Ioi 1))
    (hderiv : ∀ x, 1 < x → HasDerivAt h2 (h3 x) x)
    {b1 b2 b3 : ℝ} (hb1 : 1 < b1) (h12 : b1 < b2) (h23 : b2 < b3)
    (v1 : h2 b1 ≤ 0) (v2 : 0 < h2 b2) (v3 : h2 b3 ≤ 0) : False := by
  obtain ⟨c1, hc1, hc1_eq⟩ := exists_hasDerivAt_eq_slope h2 h3 h12
    (fun x hx => (hderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt)
    (fun x hx => hderiv x (by linarith [hx.1]))
  obtain ⟨c2, hc2, hc2_eq⟩ := exists_hasDerivAt_eq_slope h2 h3 h23
    (fun x hx => (hderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt)
    (fun x hx => hderiv x (by linarith [hx.1]))
  have hc1_pos : 0 < h3 c1 := by
    rw [hc1_eq]; exact div_pos (by linarith) (by linarith)
  have hc2_neg : h3 c2 < 0 := by
    rw [hc2_eq]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hle : h3 c1 ≤ h3 c2 :=
    hmono (show 1 < c1 by linarith [hc1.1]) (show 1 < c2 by linarith [hc2.1]) (by linarith [hc1.2, hc2.1])
  linarith

private lemma simpson_upper_pointwise {u v t : ℝ} (hu : 1 < u) (huv : u < v) (ht : t ∈ Icc u v) :
    let m := (u + v) / 2
    let h := (v - u) / 2
    f0 t ≤ f0 m + f1 m * (t - m) +
      (f0 u - 2 * f0 m + f0 v) / (2 * h ^ 2) * (t - m) ^ 2 +
      (f0 v - f0 u - 2 * h * f1 m) / (2 * h ^ 3) * (t - m) ^ 3 := by
  intro m h
  have hh : 0 < h := by simp only [h]; linarith
  have hm : 1 < m := by simp only [m]; linarith
  let C2 := (f0 u - 2 * f0 m + f0 v) / (2 * h ^ 2)
  let C3 := (f0 v - f0 u - 2 * h * f1 m) / (2 * h ^ 3)
  let E0 : ℝ → ℝ := fun x => f0 x - (f0 m + f1 m * (x - m) + C2 * (x - m) ^ 2 + C3 * (x - m) ^ 3)
  let E1 : ℝ → ℝ := fun x => f1 x - (f1 m + 2 * C2 * (x - m) + 3 * C3 * (x - m) ^ 2)
  let E2 : ℝ → ℝ := fun x => f2 x - (2 * C2 + 6 * C3 * (x - m))
  let E3 : ℝ → ℝ := fun x => f3 x - 6 * C3
  have hd0 : ∀ x, 1 < x → HasDerivAt E0 (E1 x) x := by
    intro x hx
    have hp := hasDerivAt_poly3 (f0 m) (f1 m) C2 C3 m x
    exact mk_hasDerivAt ((hasDerivAt_f0 hx).sub hp) (fun _ => rfl) rfl
  have hd1 : ∀ x, 1 < x → HasDerivAt E1 (E2 x) x := by
    intro x hx
    have hp := hasDerivAt_poly3 (f1 m) (2 * C2) (3 * C3) 0 m x
    exact mk_hasDerivAt ((hasDerivAt_f1 hx).sub hp) (fun y => by dsimp [E1]; ring) (by dsimp [E2]; ring)
  have hd2 : ∀ x, 1 < x → HasDerivAt E2 (E3 x) x := by
    intro x hx
    have hp := hasDerivAt_poly3 (2 * C2) (6 * C3) 0 0 m x
    exact mk_hasDerivAt ((hasDerivAt_f2 hx).sub hp) (fun y => by dsimp [E2]; ring) (by dsimp [E3]; ring)
  have hE3_mono : MonotoneOn E3 (Ioi 1) := by
    intro x hx y hy hxy
    simp only [E3]; linarith [f3_monotoneOn hx hy hxy]
  have hEu : E0 u = 0 := by
    simp only [E0, C2, C3, m, h]
    have hne : v - u ≠ 0 := by linarith
    field_simp; ring
  have hEm : E0 m = 0 := by simp [E0]
  have hE1m : E1 m = 0 := by simp [E1]
  have hEv : E0 v = 0 := by
    simp only [E0, C2, C3, m, h]
    have hne : v - u ≠ 0 := by linarith
    field_simp; ring
  suffices hle : E0 t ≤ 0 by simp only [E0] at hle; linarith
  by_contra hnotle
  have hpos : 0 < E0 t := lt_of_not_ge hnotle
  have htu : t ≠ u := by intro r; subst r; linarith
  have htm : t ≠ m := by intro r; subst r; linarith
  have htv : t ≠ v := by intro r; subst r; linarith
  have hum : u < m := by simp only [m]; linarith
  have hmv : m < v := by simp only [m]; linarith
  rcases lt_or_gt_of_ne htm with htm_lt | htm_gt
  · have hut : u < t := lt_of_le_of_ne ht.1 htu.symm
    obtain ⟨a1, ha1, ha1_eq⟩ := exists_hasDerivAt_eq_slope E0 E1 hut
      (fun x hx => (hd0 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd0 x (by linarith [hx.1]))
    obtain ⟨a2, ha2, ha2_eq⟩ := exists_hasDerivAt_eq_slope E0 E1 htm_lt
      (fun x hx => (hd0 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd0 x (by linarith [hx.1]))
    obtain ⟨a3, ha3, ha3_eq⟩ := exists_hasDerivAt_eq_slope E0 E1 hmv
      (fun x hx => (hd0 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd0 x (by linarith [hx.1]))
    have ha1_pos : 0 < E1 a1 := by rw [ha1_eq, hEu]; exact div_pos (by linarith) (by linarith)
    have ha2_neg : E1 a2 < 0 := by rw [ha2_eq, hEm]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
    have ha3_zero : E1 a3 = 0 := by rw [ha3_eq, hEv, hEm, sub_self, zero_div]
    obtain ⟨b1, hb1, hb1_eq⟩ := exists_hasDerivAt_eq_slope E1 E2 (show a1 < a2 by linarith [ha1.2, ha2.1])
      (fun x hx => (hd1 x (by linarith [ha1.1, hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd1 x (by linarith [ha1.1, hx.1]))
    obtain ⟨b2, hb2, hb2_eq⟩ := exists_hasDerivAt_eq_slope E1 E2 ha2.2
      (fun x hx => (hd1 x (by linarith [ha2.1, hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd1 x (by linarith [ha2.1, hx.1]))
    obtain ⟨b3, hb3, hb3_eq⟩ := exists_hasDerivAt_eq_slope E1 E2 ha3.1
      (fun x hx => (hd1 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd1 x (by linarith [hx.1]))
    have hb1_neg : E2 b1 ≤ 0 := by
      rw [hb1_eq]; exact le_of_lt (div_neg_of_neg_of_pos (by linarith) (by linarith [ha1.2, ha2.1]))
    have hb2_pos : 0 < E2 b2 := by
      rw [hb2_eq, hE1m]; exact div_pos (by linarith) (by linarith [ha2.2])
    have hb3_zero : E2 b3 ≤ 0 := by
      rw [hb3_eq, ha3_zero, hE1m, sub_self, zero_div]
    exact contradict_three_points hE3_mono hd2 (by linarith [ha1.1, hb1.1])
      (by linarith [hb1.2, hb2.1]) (by linarith [hb2.2, hb3.1]) hb1_neg hb2_pos hb3_zero
  · have htv' : t < v := lt_of_le_of_ne ht.2 htv
    obtain ⟨a0, ha0, ha0_eq⟩ := exists_hasDerivAt_eq_slope E0 E1 hum
      (fun x hx => (hd0 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd0 x (by linarith [hx.1]))
    obtain ⟨a1, ha1, ha1_eq⟩ := exists_hasDerivAt_eq_slope E0 E1 htm_gt
      (fun x hx => (hd0 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd0 x (by linarith [hx.1]))
    obtain ⟨a2, ha2, ha2_eq⟩ := exists_hasDerivAt_eq_slope E0 E1 htv'
      (fun x hx => (hd0 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd0 x (by linarith [hx.1]))
    have ha0_zero : E1 a0 = 0 := by rw [ha0_eq, hEm, hEu, sub_self, zero_div]
    have ha1_pos : 0 < E1 a1 := by rw [ha1_eq, hEm]; exact div_pos (by linarith) (by linarith)
    have ha2_neg : E1 a2 < 0 := by rw [ha2_eq, hEv]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
    obtain ⟨b1, hb1, hb1_eq⟩ := exists_hasDerivAt_eq_slope E1 E2 ha0.2
      (fun x hx => (hd1 x (by linarith [ha0.1, hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd1 x (by linarith [ha0.1, hx.1]))
    obtain ⟨b2, hb2, hb2_eq⟩ := exists_hasDerivAt_eq_slope E1 E2 ha1.1
      (fun x hx => (hd1 x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd1 x (by linarith [hx.1]))
    obtain ⟨b3, hb3, hb3_eq⟩ := exists_hasDerivAt_eq_slope E1 E2 (show a1 < a2 by linarith [ha1.2, ha2.1])
      (fun x hx => (hd1 x (by linarith [ha1.1, hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hd1 x (by linarith [ha1.1, hx.1]))
    have hb1_zero : E2 b1 ≤ 0 := by
      rw [hb1_eq, hE1m, ha0_zero, sub_self, zero_div]
    have hb2_pos : 0 < E2 b2 := by
      rw [hb2_eq, hE1m]; exact div_pos (by linarith) (by linarith [ha1.1])
    have hb3_neg : E2 b3 ≤ 0 := by
      rw [hb3_eq]; exact le_of_lt (div_neg_of_neg_of_pos (by linarith) (by linarith [ha1.2, ha2.1]))
    exact contradict_three_points hE3_mono hd2 (by linarith [ha0.1, hb1.1])
      (by linarith [hb1.2, hb2.1]) (by linarith [hb2.2, hb3.1]) hb1_zero hb2_pos hb3_neg

private lemma integral_cubic_mid (A B C D u v : ℝ) :
    ∫ t in u..v, (A + B * (t - (u + v) / 2) + C * (t - (u + v) / 2) ^ 2 + D * (t - (u + v) / 2) ^ 3)
      = A * (v - u) + C / 12 * (v - u) ^ 3 := by
  let m := (u + v) / 2
  let P : ℝ → ℝ := fun t => A * (t - m) + B / 2 * (t - m) ^ 2 + C / 3 * (t - m) ^ 3 + D / 4 * (t - m) ^ 4
  let P' : ℝ → ℝ := fun t => A + B * (t - m) + C * (t - m) ^ 2 + D * (t - m) ^ 3
  have hd : ∀ t ∈ uIcc u v, HasDerivAt P (P' t) t := by
    intro t _
    have hsub : HasDerivAt (fun x => x - m) 1 t :=
      mk_hasDerivAt ((hasDerivAt_id t).sub_const m) (fun _ => rfl) rfl
    have h1 : HasDerivAt (fun x => A * (x - m)) (A * 1) t := hsub.const_mul A
    have h2 : HasDerivAt (fun x => B / 2 * (x - m) ^ 2) (B / 2 * (↑(2 : ℕ) * (t - m) ^ (2 - 1) * 1)) t :=
      mk_hasDerivAt (((hasDerivAt_pow 2 (t - m)).comp t hsub).const_mul (B / 2)) (fun _ => rfl) rfl
    have h3 : HasDerivAt (fun x => C / 3 * (x - m) ^ 3) (C / 3 * (↑(3 : ℕ) * (t - m) ^ (3 - 1) * 1)) t :=
      mk_hasDerivAt (((hasDerivAt_pow 3 (t - m)).comp t hsub).const_mul (C / 3)) (fun _ => rfl) rfl
    have h4 : HasDerivAt (fun x => D / 4 * (x - m) ^ 4) (D / 4 * (↑(4 : ℕ) * (t - m) ^ (4 - 1) * 1)) t :=
      mk_hasDerivAt (((hasDerivAt_pow 4 (t - m)).comp t hsub).const_mul (D / 4)) (fun _ => rfl) rfl
    exact mk_hasDerivAt (((h1.add h2).add h3).add h4) (fun _ => rfl) (by dsimp [P']; norm_num; ring)
  have hc : Continuous P' := by dsimp [P']; continuity
  rw [integral_eq_sub_of_hasDerivAt hd hc.continuousOn.intervalIntegrable]
  simp only [P, m]
  ring

private lemma subinterval_enclosure {u m v lu_lo lm_lo lm_hi lv_lo : ℝ}
    (hu : 1 < u) (huv : u < v) (hm_eq : m = (u + v) / 2)
    (hlu_pos : 0 < lu_lo) (hlm_pos : 0 < lm_lo) (hlv_pos : 0 < lv_lo)
    (hlu : lu_lo ≤ log u)
    (hlm_lo : lm_lo ≤ log m) (hlm_hi : log m ≤ lm_hi)
    (hlv : lv_lo ≤ log v) :
    (v - u) / lm_hi + (v - u) ^ 3 / 24 *
        (1 / (m ^ 2 * lm_hi ^ 2) + 2 / (m ^ 2 * lm_hi ^ 3))
      ≤ (∫ t in u..v, 1 / log t) ∧
    (∫ t in u..v, 1 / log t) ≤
      (v - u) / 6 * (1 / lu_lo + 4 / lm_lo + 1 / lv_lo) := by
  subst hm_eq
  let m0 := (u + v) / 2
  let h := (v - u) / 2
  have hm : 1 < m0 := by simp only [m0]; linarith
  have hf_int : IntervalIntegrable (fun t => 1 / log t) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv.le]
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    exact (continuousAt_const.div (Real.continuousAt_log ht0.ne') (Real.log_pos ht1).ne').continuousWithinAt
  let Plow : ℝ → ℝ := fun t => f0 m0 + f1 m0 * (t - m0) + (1 / 2 * f2 m0) * (t - m0) ^ 2 + (1 / 6 * f3 m0) * (t - m0) ^ 3
  let Pup : ℝ → ℝ := fun t => f0 m0 + f1 m0 * (t - m0) +
    ((f0 u - 2 * f0 m0 + f0 v) / (2 * h ^ 2)) * (t - m0) ^ 2 +
    ((f0 v - f0 u - 2 * h * f1 m0) / (2 * h ^ 3)) * (t - m0) ^ 3
  have hPlow_cont : Continuous Plow := by dsimp [Plow]; continuity
  have hPup_cont : Continuous Pup := by dsimp [Pup]; continuity
  have h_int_low : (v - u) * f0 m0 + (v - u) ^ 3 / 24 * f2 m0 ≤ ∫ t in u..v, 1 / log t := by
    have hi : ∫ t in u..v, Plow t ≤ ∫ t in u..v, 1 / log t := by
      refine integral_mono_on huv.le hPlow_cont.continuousOn.intervalIntegrable hf_int ?_
      intro t ht
      have hpw := hermite_lower_pointwise hm (by linarith [ht.1] : 1 < t)
      simpa [Plow, f0, one_div, mul_assoc] using hpw
    have heq := integral_cubic_mid (f0 m0) (f1 m0) (1 / 2 * f2 m0) (1 / 6 * f3 m0) u v
    linarith
  have h_int_up : ∫ t in u..v, 1 / log t ≤ (v - u) / 6 * (f0 u + 4 * f0 m0 + f0 v) := by
    have hi : ∫ t in u..v, 1 / log t ≤ ∫ t in u..v, Pup t := by
      refine integral_mono_on huv.le hf_int hPup_cont.continuousOn.intervalIntegrable ?_
      intro t ht
      have hpw := simpson_upper_pointwise hu huv ht
      simpa [Pup, m0, h, f0, one_div, mul_assoc] using hpw
    have heq := integral_cubic_mid (f0 m0) (f1 m0)
      ((f0 u - 2 * f0 m0 + f0 v) / (2 * h ^ 2)) ((f0 v - f0 u - 2 * h * f1 m0) / (2 * h ^ 3)) u v
    have hsimp : f0 m0 * (v - u) + (f0 u - 2 * f0 m0 + f0 v) / (2 * h ^ 2) / 12 * (v - u) ^ 3 =
        (v - u) / 6 * (f0 u + 4 * f0 m0 + f0 v) := by
      simp only [h]
      have hne : v - u ≠ 0 := by linarith
      field_simp; ring
    linarith
  have hlm_hi_pos : 0 < lm_hi := by linarith
  have hlogm_pos : 0 < log m0 := Real.log_pos hm
  have hf0_m_lo : 1 / lm_hi ≤ f0 m0 := by
    simp only [f0, one_div]
    exact inv_anti₀ hlogm_pos hlm_hi
  have hf2_m_lo : 1 / (m0 ^ 2 * lm_hi ^ 2) + 2 / (m0 ^ 2 * lm_hi ^ 3) ≤ f2 m0 := by
    have h1 : (m0 ^ 2 * lm_hi ^ 2)⁻¹ ≤ (m0 ^ 2 * (log m0) ^ 2)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogm_pos.le hlm_hi 2) (by positivity)
    have h2 : (m0 ^ 2 * lm_hi ^ 3)⁻¹ ≤ (m0 ^ 2 * (log m0) ^ 3)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogm_pos.le hlm_hi 3) (by positivity)
    simp only [f2, div_eq_mul_inv, one_mul]
    linarith
  have hf0_u_hi : f0 u ≤ 1 / lu_lo := by
    simp only [f0, one_div]; exact inv_anti₀ hlu_pos hlu
  have hf0_m_hi : f0 m0 ≤ 1 / lm_lo := by
    simp only [f0, one_div]; exact inv_anti₀ hlm_pos hlm_lo
  have hf0_v_hi : f0 v ≤ 1 / lv_lo := by
    simp only [f0, one_div]; exact inv_anti₀ hlv_pos hlv
  have hvu_pos : 0 ≤ v - u := by linarith
  have hvu3_pos : 0 ≤ (v - u) ^ 3 / 24 := by positivity
  have hvu6_pos : 0 ≤ (v - u) / 6 := by linarith
  constructor
  · have p1 : (v - u) * (1 / lm_hi) ≤ (v - u) * f0 m0 := mul_le_mul_of_nonneg_left hf0_m_lo hvu_pos
    have p2 : (v - u) ^ 3 / 24 * (1 / (m0 ^ 2 * lm_hi ^ 2) + 2 / (m0 ^ 2 * lm_hi ^ 3)) ≤
        (v - u) ^ 3 / 24 * f2 m0 := mul_le_mul_of_nonneg_left hf2_m_lo hvu3_pos
    have eq1 : (v - u) / lm_hi = (v - u) * (1 / lm_hi) := by ring
    dsimp only [m0] at p1 p2 h_int_low
    linarith
  · have hsum_le : f0 u + 4 * f0 m0 + f0 v ≤ 1 / lu_lo + 4 / lm_lo + 1 / lv_lo := by
      have eq4 : 4 / lm_lo = 4 * (1 / lm_lo) := by ring
      rw [eq4]
      linarith
    have p3 : (v - u) / 6 * (f0 u + 4 * f0 m0 + f0 v) ≤
        (v - u) / 6 * (1 / lu_lo + 4 / lm_lo + 1 / lv_lo) :=
      mul_le_mul_of_nonneg_left hsum_le hvu6_pos
    linarith

end

theorem solution : 14.1078 ≤ (∫ t in (64 : ℝ)..128, 1 / log t) ∧
    (∫ t in (64 : ℝ)..128, 1 / log t) ≤ 14.1080 := by
  have hln2 := ln2_bounds
  have hx0 : log (64 : ℝ) = 6 * log 2 := by
    have heq : (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
    rw [heq, Real.log_pow]; norm_num
  have hlog0 : (83177649 / 20000000 : ℝ) ≤ log (64 : ℝ) ∧ log (64 : ℝ) ≤ (2079441543 / 500000000 : ℝ) := by
    rw [hx0]; constructor <;> linarith
  have hlog1 : (4276665203 / 1000000000 : ℝ) ≤ log (72 : ℝ) ∧ log (72 : ℝ) ≤ (2138333061 / 500000000 : ℝ) := by
    have hstep : log (72 : ℝ) = log (64 : ℝ) + log ((1 + (1 / 17 : ℝ)) / (1 - (1 / 17 : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1; norm_num
    have hr := log_ratio_bounds (u := (1 / 17 : ℝ)) (by norm_num) (by norm_num)
    rw [hstep]; constructor <;> linarith [hlog0.1, hlog0.2, hr.1, hr.2]
  have hlog2 : (1095506389 / 250000000 : ℝ) ≤ log (80 : ℝ) ∧ log (80 : ℝ) ≤ (2191013319 / 500000000 : ℝ) := by
    have hstep : log (80 : ℝ) = log (72 : ℝ) + log ((1 + (1 / 19 : ℝ)) / (1 - (1 / 19 : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1; norm_num
    have hr := log_ratio_bounds (u := (1 / 19 : ℝ)) (by norm_num) (by norm_num)
    rw [hstep]; constructor <;> linarith [hlog1.1, hlog1.2, hr.1, hr.2]
  have hlog3 : (4477335637 / 1000000000 : ℝ) ≤ log (88 : ℝ) ∧ log (88 : ℝ) ≤ (2238668409 / 500000000 : ℝ) := by
    have hstep : log (88 : ℝ) = log (80 : ℝ) + log ((1 + (1 / 21 : ℝ)) / (1 - (1 / 21 : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1; norm_num
    have hr := log_ratio_bounds (u := (1 / 21 : ℝ)) (by norm_num) (by norm_num)
    rw [hstep]; constructor <;> linarith [hlog2.1, hlog2.2, hr.1, hr.2]
  have hlog4 : (4564346951 / 1000000000 : ℝ) ≤ log (96 : ℝ) ∧ log (96 : ℝ) ≤ (1141087049 / 250000000 : ℝ) := by
    have hstep : log (96 : ℝ) = log (88 : ℝ) + log ((1 + (1 / 23 : ℝ)) / (1 - (1 / 23 : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1; norm_num
    have hr := log_ratio_bounds (u := (1 / 23 : ℝ)) (by norm_num) (by norm_num)
    rw [hstep]; constructor <;> linarith [hlog3.1, hlog3.2, hr.1, hr.2]
  have hlog5 : (4644389617 / 1000000000 : ℝ) ≤ log (104 : ℝ) ∧ log (104 : ℝ) ≤ (580548863 / 125000000 : ℝ) := by
    have hstep : log (104 : ℝ) = log (96 : ℝ) + log ((1 + (1 / 25 : ℝ)) / (1 - (1 / 25 : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1; norm_num
    have hr := log_ratio_bounds (u := (1 / 25 : ℝ)) (by norm_num) (by norm_num)
    rw [hstep]; constructor <;> linarith [hlog4.1, hlog4.2, hr.1, hr.2]
  have hlog6 : (4718497561 / 1000000000 : ℝ) ≤ log (112 : ℝ) ∧ log (112 : ℝ) ≤ (4718498877 / 1000000000 : ℝ) := by
    have hstep : log (112 : ℝ) = log (104 : ℝ) + log ((1 + (1 / 27 : ℝ)) / (1 - (1 / 27 : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1; norm_num
    have hr := log_ratio_bounds (u := (1 / 27 : ℝ)) (by norm_num) (by norm_num)
    rw [hstep]; constructor <;> linarith [hlog5.1, hlog5.2, hr.1, hr.2]
  have hlog7 : (1196872603 / 250000000 : ℝ) ≤ log (120 : ℝ) ∧ log (120 : ℝ) ≤ (4787491749 / 1000000000 : ℝ) := by
    have hstep : log (120 : ℝ) = log (112 : ℝ) + log ((1 + (1 / 29 : ℝ)) / (1 - (1 / 29 : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1; norm_num
    have hr := log_ratio_bounds (u := (1 / 29 : ℝ)) (by norm_num) (by norm_num)
    rw [hstep]; constructor <;> linarith [hlog6.1, hlog6.2, hr.1, hr.2]
  have hlog8 : (4852028919 / 1000000000 : ℝ) ≤ log (128 : ℝ) ∧ log (128 : ℝ) ≤ (4852030271 / 1000000000 : ℝ) := by
    have hstep : log (128 : ℝ) = log (120 : ℝ) + log ((1 + (1 / 31 : ℝ)) / (1 - (1 / 31 : ℝ))) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1; norm_num
    have hr := log_ratio_bounds (u := (1 / 31 : ℝ)) (by norm_num) (by norm_num)
    rw [hstep]; constructor <;> linarith [hlog7.1, hlog7.2, hr.1, hr.2]
  have hsub0 := subinterval_enclosure (u := (64 : ℝ)) (m := (72 : ℝ)) (v := (80 : ℝ))
    (lu_lo := (83177649 / 20000000 : ℝ)) (lm_lo := (4276665203 / 1000000000 : ℝ)) (lm_hi := (2138333061 / 500000000 : ℝ)) (lv_lo := (1095506389 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog0.1 hlog1.1 hlog1.2 hlog2.1
  have hsub1 := subinterval_enclosure (u := (80 : ℝ)) (m := (88 : ℝ)) (v := (96 : ℝ))
    (lu_lo := (1095506389 / 250000000 : ℝ)) (lm_lo := (4477335637 / 1000000000 : ℝ)) (lm_hi := (2238668409 / 500000000 : ℝ)) (lv_lo := (4564346951 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog2.1 hlog3.1 hlog3.2 hlog4.1
  have hsub2 := subinterval_enclosure (u := (96 : ℝ)) (m := (104 : ℝ)) (v := (112 : ℝ))
    (lu_lo := (4564346951 / 1000000000 : ℝ)) (lm_lo := (4644389617 / 1000000000 : ℝ)) (lm_hi := (580548863 / 125000000 : ℝ)) (lv_lo := (4718497561 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog4.1 hlog5.1 hlog5.2 hlog6.1
  have hsub3 := subinterval_enclosure (u := (112 : ℝ)) (m := (120 : ℝ)) (v := (128 : ℝ))
    (lu_lo := (4718497561 / 1000000000 : ℝ)) (lm_lo := (1196872603 / 250000000 : ℝ)) (lm_hi := (4787491749 / 1000000000 : ℝ)) (lv_lo := (4852028919 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog6.1 hlog7.1 hlog7.2 hlog8.1
  have hint_on : ∀ u v : ℝ, (64 : ℝ) ≤ u → u ≤ v → IntervalIntegrable (fun t => 1 / log t) volume u v := by
    intro u v hau huv
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    exact (continuousAt_const.div (Real.continuousAt_log ht0.ne') (Real.log_pos ht1).ne').continuousWithinAt
  have hsplit : (∫ t in (64 : ℝ)..128, 1 / log t) = (∫ t in (64 : ℝ)..(80 : ℝ), 1 / log t) + (∫ t in (80 : ℝ)..(96 : ℝ), 1 / log t) + (∫ t in (96 : ℝ)..(112 : ℝ), 1 / log t) + (∫ t in (112 : ℝ)..(128 : ℝ), 1 / log t) := by
    have ha0 := integral_add_adjacent_intervals (hint_on (64 : ℝ) (80 : ℝ) (by norm_num) (by norm_num)) (hint_on (80 : ℝ) (96 : ℝ) (by norm_num) (by norm_num))
    have ha1 := integral_add_adjacent_intervals (hint_on (64 : ℝ) (96 : ℝ) (by norm_num) (by norm_num)) (hint_on (96 : ℝ) (112 : ℝ) (by norm_num) (by norm_num))
    have ha2 := integral_add_adjacent_intervals (hint_on (64 : ℝ) (112 : ℝ) (by norm_num) (by norm_num)) (hint_on (112 : ℝ) (128 : ℝ) (by norm_num) (by norm_num))
    linarith
  rw [hsplit]
  constructor
  · linarith [hsub0.1, hsub1.1, hsub2.1, hsub3.1]
  · linarith [hsub0.2, hsub1.2, hsub2.2, hsub3.2]
