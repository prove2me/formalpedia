-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff32.contract32
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:21:17.614976+00:00
-- url     : https://prove2.me/submissions/d75400b0-5a0e-4167-8192-7fd299469c2e

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff32_SlabRadius
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff32

open HlawkaSchatten.DiagonalConstruction

/-! ## Elementary power inequalities -/

/-- Increments of `x ↦ x ^ p` over intervals of equal length grow to the right. -/
theorem rpow_swap_le {p : ℝ} (hp : 1 ≤ p) {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hc : 0 ≤ c) : (x + c) ^ p + y ^ p ≤ x ^ p + (y + c) ^ p := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ y - x + c by linarith) with h | h
  · have hc0 : c = 0 := by linarith
    have hy : y = x := by linarith
    subst hc0 hy; simp
  · have hconv := (convexOn_rpow hp).2
    have hxm : x ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 hx
    have hym : y + c ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith)
    have hl : 0 ≤ (y - x) / (y - x + c) := div_nonneg (by linarith) h.le
    have hm : 0 ≤ c / (y - x + c) := div_nonneg hc h.le
    have hs : (y - x) / (y - x + c) + c / (y - x + c) = 1 := by
      rw [← add_div, div_self h.ne']
    have h1 := hconv hxm hym hl hm hs
    have h2 := hconv hxm hym hm hl (by linarith)
    simp only [smul_eq_mul] at h1 h2
    have e1 : (y - x) / (y - x + c) * x + c / (y - x + c) * (y + c) = x + c := by
      field_simp; ring
    have e2 : c / (y - x + c) * x + (y - x) / (y - x + c) * (y + c) = y := by
      field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    calc (x + c) ^ p + y ^ p ≤ _ := add_le_add h1 h2
      _ = ((y - x) / (y - x + c) + c / (y - x + c)) * (x ^ p + (y + c) ^ p) := by ring
      _ = _ := by rw [hs, one_mul]

/-- Power mean for two terms. -/
theorem add_rpow_le_two {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u + v) ^ p ≤ 2 ^ p / 2 * (u ^ p + v ^ p) := by
  have h := (convexOn_rpow hp).2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 hv)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1/2 * u + 1/2 * v = (u + v) / 2 := by ring
  rw [e, Real.div_rpow (by linarith) (by norm_num)] at h
  have h2p : 0 < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  rw [div_le_iff₀ h2p] at h
  calc (u + v) ^ p ≤ _ := h
    _ = _ := by ring

/-- The two-coordinate constant `2 ^ (1 - 1/p)`. -/
noncomputable def cp (p : ℝ) : ℝ := 2 * (1/2 : ℝ) ^ (1/p)

theorem cp_pos (p : ℝ) : 0 < cp p := by unfold cp; positivity

theorem cp_rpow {p : ℝ} (hp : 0 < p) : cp p ^ p = 2 ^ p / 2 := by
  unfold cp
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num),
    one_div_mul_cancel hp.ne', Real.rpow_one]; ring

theorem sum_div_cp_rpow_le {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((u + v) / cp p) ^ p ≤ u ^ p + v ^ p := by
  have hp0 : 0 < p := by linarith
  rw [Real.div_rpow (by linarith) (cp_pos p).le, cp_rpow hp0, div_le_iff₀ (by positivity)]
  rw [mul_comm]; exact add_rpow_le_two hp hu hv

theorem sum_le_cp_mul {p : ℝ} (hp : 1 ≤ p) {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hS : 0 ≤ S) (h : u ^ p + v ^ p ≤ S ^ p) : u + v ≤ cp p * S := by
  have hp0 : 0 < p := by linarith
  have h1 := (sum_div_cp_rpow_le hp hu hv).trans h
  have h2 : (u + v) / cp p ≤ S :=
    (Real.rpow_le_rpow_iff (div_nonneg (by linarith) (cp_pos p).le) hS hp0).1 h1
  rw [div_le_iff₀ (cp_pos p)] at h2; linarith

/-- Diagonal certificate: a row with nearly extremal two-coordinate mass has a small
diagonal entry. -/
theorem diag_cert {p : ℝ} (hp : 1 ≤ p) {a w c N D δ U Ab : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hrow : a ^ p + (w / c) ^ p ≤ N ^ p) (hw : c * N - D ≤ w) (hDc : D / c ≤ δ)
    (hδ : 0 ≤ δ) (hδN : δ ≤ N) (hNU : N ≤ U) (hU : 0 < U) (hAb : 0 ≤ Ab)
    (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p) : a ≤ Ab := by
  have hp0 : 0 < p := by linarith
  have h1 : N - δ ≤ w / c := by
    have e : w / c = N - D / c + (w - (c * N - D)) / c := by field_simp; ring
    rw [e]
    have : 0 ≤ (w - (c * N - D)) / c := div_nonneg (by linarith) hc.le
    linarith
  have h2 : (N - δ) ^ p ≤ (w / c) ^ p := Real.rpow_le_rpow (by linarith) h1 hp0.le
  have h3 := rpow_swap_le hp (x := N - δ) (y := U - δ) (c := δ) (by linarith) (by linarith) hδ
  rw [sub_add_cancel, sub_add_cancel] at h3
  have h4 : U ^ p ≤ Ab ^ p + (U - δ) ^ p := by
    have e : 1 - δ / U = (U - δ) / U := by field_simp
    rw [e, Real.div_rpow hAb hU.le, Real.div_rpow (by linarith) hU.le, ← add_div,
      le_div_iff₀ (by positivity), one_mul] at hcert
    exact hcert
  have h5 : a ^ p ≤ Ab ^ p := by linarith
  exact (Real.rpow_le_rpow_iff ha hAb hp0).1 h5

/-- Two-dimensional Minkowski inequality in power form. -/
theorem mink2 {p : ℝ} (hp : 1 ≤ p) {x1 y1 x2 y2 N1 N2 : ℝ} (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1)
    (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (h1 : x1 ^ p + y1 ^ p ≤ N1 ^ p) (h2 : x2 ^ p + y2 ^ p ≤ N2 ^ p) :
    (x1 + x2) ^ p + (y1 + y2) ^ p ≤ (N1 + N2) ^ p := by
  have hp0 : 0 < p := by linarith
  have hM := Real.Lp_add_le (Finset.univ : Finset (Fin 2)) ![x1, y1] ![x2, y2] hp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hM
  rw [abs_of_nonneg (by linarith : 0 ≤ x1 + x2), abs_of_nonneg (by linarith : 0 ≤ y1 + y2),
    abs_of_nonneg hx1, abs_of_nonneg hy1, abs_of_nonneg hx2, abs_of_nonneg hy2] at hM
  have hr1 : (x1 ^ p + y1 ^ p) ^ (1/p) ≤ N1 := by
    calc (x1 ^ p + y1 ^ p) ^ (1/p) ≤ (N1 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = N1 := by rw [one_div, Real.rpow_rpow_inv hN1 hp0.ne']
  have hr2 : (x2 ^ p + y2 ^ p) ^ (1/p) ≤ N2 := by
    calc (x2 ^ p + y2 ^ p) ^ (1/p) ≤ (N2 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h2 (by positivity)
      _ = N2 := by rw [one_div, Real.rpow_rpow_inv hN2 hp0.ne']
  have h3 : ((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p) ≤ N1 + N2 := by linarith
  have hS : 0 ≤ (x1 + x2) ^ p + (y1 + y2) ^ p := by positivity
  calc (x1 + x2) ^ p + (y1 + y2) ^ p
      = (((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p)) ^ p := by
        rw [← Real.rpow_mul hS, one_div_mul_cancel hp0.ne', Real.rpow_one]
    _ ≤ (N1 + N2) ^ p := Real.rpow_le_rpow (by positivity) h3 hp0.le

/-- Ratio lower bound from a convexity certificate. -/
theorem ratio_lower {p x y s τ : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s)
    (hc : 1 < τ ^ p + (s - τ) ^ p) : τ < x := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have h1 := rpow_swap_le hp (x := x) (y := s - τ) (c := τ - x) hx (by linarith) (by linarith)
  have e1 : x + (τ - x) = τ := by ring
  have e2 : s - τ + (τ - x) = s - x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-- Ratio upper bound from a convexity certificate. -/
theorem ratio_upper {p x y s σ : ℝ} (hp : 1 ≤ p) (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hc : 1 < σ ^ p + (s - σ) ^ p) : x < σ := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have hx1 : x ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < x ^ p := Real.one_lt_rpow h hp0
    have : 0 ≤ y ^ p := Real.rpow_nonneg hy p
    linarith
  have h1 := rpow_swap_le hp (x := s - x) (y := σ) (c := x - σ) (by linarith) (by linarith)
    (by linarith)
  have e1 : s - x + (x - σ) = s - σ := by ring
  have e2 : σ + (x - σ) = x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-! ## Turning integer-power checks into real-exponent certificates -/

theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)

theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'

theorem cert_le {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 ≤ X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 ≤ x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith

theorem cert_lt {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 < X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 < x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith

/-! ## Monotonicity of the deficit majorant and the tail estimate -/

theorem mono_t {α p : ℝ} (hα : 0 < α) (hαp : α ≤ p) :
    6 * (1/2 : ℝ) ^ (1/p) + 2000 / (448 * p) ≤ 6 * (1/2 : ℝ) ^ (1/α) + 2000 / (448 * α) := by
  have hp : 0 < p := by linarith
  have hL : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : ∀ r : ℝ, (1/2 : ℝ) ^ r = Real.exp (-(Real.log 2 * r)) := by
    intro r
    rw [Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]; ring_nf
  rw [e, e]
  have huw : 1/p ≤ 1/α := one_div_le_one_div_of_le hα hαp
  have hu : 0 < 1/p := by positivity
  set u := 1/p with hu_def
  set w := 1/α with hw_def
  set L := Real.log 2
  have h1 : Real.exp (-(L * w)) = Real.exp (-(L * u)) * Real.exp (-(L * (w - u))) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : 1 - L * (w - u) ≤ Real.exp (-(L * (w - u))) := by
    have := Real.add_one_le_exp (-(L * (w - u))); linarith
  have h3 : Real.exp (-(L * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h4 : 0 < Real.exp (-(L * u)) := Real.exp_pos _
  have g1 : 2000 / (448 * p) = 2000 / 448 * u := by rw [hu_def]; field_simp
  have g2 : 2000 / (448 * α) = 2000 / 448 * w := by rw [hw_def]; field_simp
  rw [g1, g2, h1]
  have hwu : 0 ≤ w - u := by linarith
  nlinarith [mul_nonneg h4.le (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3)
    (mul_nonneg hL0.le hwu)]

theorem tail_bound {p S y1 y2 : ℝ} (hp : 32 ≤ p) (hS : 158/100 ≤ S) (hS3 : S ≤ 3)
    (hy1 : |y1| ≤ 603/1000) (hy2 : |y2| ≤ 603/1000) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1/p) ≤ S + 1/10^10 := by
  have hp0 : 0 < p := by linarith
  have hS0 : 0 < S := by linarith
  rw [abs_of_pos hS0]
  set ρ : ℝ := 603/1580 with hρdef
  have hρ : ρ ^ p ≤ ρ ^ (32:ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num [ρ]) (by norm_num [ρ])
      (by exact_mod_cast hp)
  have hC : ∀ y : ℝ, |y| ≤ 603/1000 → |y| ^ p ≤ ρ ^ (32:ℕ) * S ^ p := by
    intro y hy
    have e : (603/1000 : ℝ) = ρ * (158/100) := by norm_num [ρ]
    calc |y| ^ p ≤ (603/1000 : ℝ) ^ p := Real.rpow_le_rpow (abs_nonneg _) hy hp0.le
      _ = ρ ^ p * (158/100 : ℝ) ^ p := by
          rw [e, Real.mul_rpow (by norm_num [ρ]) (by norm_num)]
      _ ≤ ρ ^ (32:ℕ) * S ^ p := by
          apply mul_le_mul hρ (Real.rpow_le_rpow (by norm_num) hS hp0.le)
            (by positivity) (by positivity)
  have hSp : 0 < S ^ p := by positivity
  set ε : ℝ := 1/10^10 with hεdef
  have hε0 : 0 < ε := by norm_num [ε]
  have hB : 1 + p * (ε / S) ≤ (1 + ε / S) ^ p := by
    apply one_add_mul_self_le_rpow_one_add _ (by linarith)
    have : 0 ≤ ε / S := by positivity
    linarith
  have hq3 : ε / 3 ≤ ε / S := div_le_div_of_nonneg_left hε0.le hS0 hS3
  have hpe : 32 * (ε / 3) ≤ p * (ε / S) := mul_le_mul hp hq3 (by positivity) (by linarith)
  have hnum : 2 * ρ ^ (32:ℕ) ≤ 32 * (ε / 3) := by norm_num [ρ, ε]
  have hE : (S + ε) ^ p = S ^ p * (1 + ε / S) ^ p := by
    rw [← Real.mul_rpow hS0.le (by positivity)]; congr 1; field_simp
  have k1 : 2 * ρ ^ (32:ℕ) * S ^ p ≤ p * (ε / S) * S ^ p :=
    mul_le_mul_of_nonneg_right (hnum.trans hpe) hSp.le
  have k2 := mul_le_mul_of_nonneg_left hB hSp.le
  have c1 := hC y1 hy1
  have c2 := hC y2 hy2
  have hsum : S ^ p + |y1| ^ p + |y2| ^ p ≤ (S + ε) ^ p := by
    rw [hE]; linear_combination c1 + c2 + k1 + k2
  calc (S ^ p + |y1| ^ p + |y2| ^ p) ^ (1/p) ≤ ((S + ε) ^ p) ^ (1/p) :=
        Real.rpow_le_rpow (by positivity) hsum (by positivity)
    _ = S + ε := by rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne']

/-! ## Coordinates of `Fin 3` vectors -/

/-- The coarse coordinate box (hypothesis (B0)). -/
def coarseBox (X : Triple) : Prop :=
  ∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
    else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)

/-- The final coordinate box. -/
def finalBox (X : Triple) : Prop :=
  ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
    else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ)

theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem others (i : Fin 3) : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases i <;> decide

theorem third {i j : Fin 3} (h : i ≠ j) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

theorem offperm (X : Triple) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (X i j + X i k) + (X j i + X j k) + (X k i + X k j) =
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem lpNorm_nonneg3 (p : ℝ) (x : Fin 3 → ℝ) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_pow3 {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ) :
    lpNorm p x ^ p = ∑ l, |x l| ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    one_div_mul_cancel hp.ne', Real.rpow_one]
  simp [Real.norm_eq_abs]

theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]

theorem coord_le {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : |x i| ≤ lpNorm p x := by
  have h := lpNorm_pow3 hp x
  rw [sum3 _ hij hik hjk] at h
  have : |x i| ^ p ≤ lpNorm p x ^ p := by
    rw [h]; have := Real.rpow_nonneg (abs_nonneg (x j)) p
    have := Real.rpow_nonneg (abs_nonneg (x k)) p; linarith
  exact (Real.rpow_le_rpow_iff (abs_nonneg _) (lpNorm_nonneg3 p x) hp).1 this

theorem two_coord_le {p : ℝ} (hp : 1 ≤ p) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : |x j| + |x k| ≤ cp p * lpNorm p x := by
  have hp0 : 0 < p := by linarith
  have h := lpNorm_pow3 hp0 x
  rw [sum3 _ hij hik hjk] at h
  apply sum_le_cp_mul hp (abs_nonneg _) (abs_nonneg _) (lpNorm_nonneg3 p x)
  rw [h]; have := Real.rpow_nonneg (abs_nonneg (x i)) p; linarith

/-! ## The facts used by the contractor -/

/-- Everything the contraction rounds use about a triple at a fixed exponent. -/
structure Facts (p c D δ h A cmax tlo : ℝ) (X : Triple) : Prop where
  hp : 1 ≤ p
  hc : 0 < c
  hcm : c ≤ cmax
  hct : 2 * tlo ≤ c
  hDc : D / c ≤ δ
  hA : 0 < A
  diag : ∀ i, 0 ≤ -X i i
  off : ∀ i j, i ≠ j → 79/100 ≤ X i j
  nsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    lpNorm p (X i) + lpNorm p (X j) + lpNorm p (X k) = 3
  rowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + X i j ^ p + X i k ^ p = lpNorm p (X i) ^ p
  row : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + ((X i j + X i k) / c) ^ p ≤ lpNorm p (X i) ^ p
  wD : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → c * lpNorm p (X i) - D ≤ X i j + X i k
  wD2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    c * (lpNorm p (X j) + lpNorm p (X k)) - D ≤ (X j i + X j k) + (X k i + X k j)
  offsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    6 - h < (X i j + X i k) + (X j i + X j k) + (X k i + X k j)
  T1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i i + X j i + X k i < A
  T2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (X i j + X j j + X k j) + (X i k + X j k + X k k) < cmax * A

theorem facts_of {p α β tlo thia thib D δ h q : ℝ} {X : Triple} (hα : 0 < α) (hαp : α ≤ p)
    (hpβ : p ≤ β) (hp32 : 32 ≤ p) (htlo0 : 0 < tlo) (htlo : tlo ≤ (1/2 : ℝ) ^ (1/α))
    (hthia : (1/2 : ℝ) ^ (1/α) ≤ thia) (hthib : (1/2 : ℝ) ^ (1/β) ≤ thib)
    (hD : 2000 / (448 * α) + 3 / 10^10 - 6 * (1 - thia) ≤ D) (hD0 : 0 ≤ D)
    (hδ : D / (2 * tlo) ≤ δ) (hh : 2000 / (448 * α) + 3 / 10^10 ≤ h) (hq : 0 < q)
    (hB : coarseBox X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < 3 * q)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p)) :
    Facts p (cp p) D δ h (3 * q) (2 * thib) tlo X := by
  have hp : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hdiag : ∀ i, -(1158/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(555/1000 : ℝ) := fun i ↦ by
    simpa using hB i i
  have hoff : ∀ i j, i ≠ j → (79/100 : ℝ) ≤ X i j ∧ X i j ≤ 1158/1000 := fun i j h ↦ by
    have := hB i j; rwa [if_neg h] at this
  have hrowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (-X i i) ^ p + X i j ^ p + X i k ^ p = lpNorm p (X i) ^ p := by
    intro i j k hij hik hjk
    rw [lpNorm_pow3 hp0, sum3 _ hij hik hjk, abs_of_neg (by linarith [(hdiag i).2]),
      abs_of_pos (by linarith [(hoff i j hij).1]), abs_of_pos (by linarith [(hoff i k hik).1])]
  have hdn : ∀ i, 0 ≤ -X i i := fun i ↦ by linarith [(hdiag i).2]
  have hrow : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (-X i i) ^ p + ((X i j + X i k) / cp p) ^ p ≤ lpNorm p (X i) ^ p := by
    intro i j k hij hik hjk
    have := sum_div_cp_rpow_le hp (u := X i j) (v := X i k) (by linarith [(hoff i j hij).1])
      (by linarith [(hoff i k hik).1])
    have := hrowfull i j k hij hik hjk
    linarith
  have hwle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j + X i k ≤ cp p * lpNorm p (X i) := by
    intro i j k hij hik hjk
    apply sum_le_cp_mul hp (by linarith [(hoff i j hij).1]) (by linarith [(hoff i k hik).1])
      (lpNorm_nonneg3 p _)
    have := hrowfull i j k hij hik hjk
    have := Real.rpow_nonneg (hdn i) p
    linarith
  have htail : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ (X j i + X k i) + 1/10^10 := by
    intro i j k hij hik hjk
    rw [lpNorm_eq3 p _ hij hik hjk]
    simp only [Pi.add_apply]
    have h1 := hoff j i (Ne.symm hij)
    have h2 := hoff k i (Ne.symm hik)
    have h3 := hoff k j (Ne.symm hjk)
    have h4 := hoff j k hjk
    have h5 := hdiag j
    have h6 := hdiag k
    apply tail_bound hp32 (by linarith) (by linarith)
      (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)
  have hoffsum0 : 6 - 2000 / (448 * p) - 3 / 10^10 <
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    unfold pairGapSum pairGap at hG
    have t01 := htail 2 0 1 (by decide) (by decide) (by decide)
    have t02 := htail 1 0 2 (by decide) (by decide) (by decide)
    have t12 := htail 0 1 2 (by decide) (by decide) (by decide)
    have e : 2 / ((448/1000) * p) = 2000 / (448 * p) := by field_simp; norm_num
    rw [e] at hG
    linarith
  have hg : 2000 / (448 * p) ≤ 2000 / (448 * α) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hmono := mono_t hα hαp
  have hct : 2 * tlo ≤ cp p := by
    unfold cp
    have : (1/2 : ℝ) ^ (1/α) ≤ (1/2 : ℝ) ^ (1/p) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (one_div_le_one_div_of_le hα hαp)
    linarith
  have hcm : cp p ≤ 2 * thib := by
    unfold cp
    have : (1/2 : ℝ) ^ (1/p) ≤ (1/2 : ℝ) ^ (1/β) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (one_div_le_one_div_of_le hp0 hpβ)
    linarith
  have hnsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X i) + lpNorm p (X j) + lpNorm p (X k) = 3 := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ lpNorm p (X l)) hij hik hjk
    rw [Fin.sum_univ_three] at this
    linarith
  have hoffperm : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (X i j + X i k) + (X j i + X j k) + (X k i + X k j) =
        X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    intro i j k hij hik hjk
    exact offperm X hij hik hjk
  have key : cp p * 3 - (X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) < D := by
    unfold cp; linarith
  have hcN : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      cp p * lpNorm p (X i) + cp p * lpNorm p (X j) + cp p * lpNorm p (X k) = cp p * 3 := by
    intro i j k hij hik hjk
    rw [← hnsum i j k hij hik hjk]; ring
  have hcpos := cp_pos p
  set v : Fin 3 → ℝ := X 0 + X 1 + X 2 with hv
  have hvc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → v i = X i i + X j i + X k i := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ X l i) hij hik hjk
    rw [Fin.sum_univ_three] at this
    simp only [hv, Pi.add_apply]
    linarith
  refine ⟨hp, hcpos, hcm, hct, ?_, by linarith, hdn, fun i j h ↦ (hoff i j h).1, hnsum,
    hrowfull, hrow, ?_, ?_, ?_, ?_, ?_⟩
  · calc D / cp p ≤ D / (2 * tlo) := div_le_div_of_nonneg_left hD0 (by positivity) hct
      _ ≤ δ := hδ
  · intro i j k hij hik hjk
    have := hwle j i k (Ne.symm hij) hjk hik
    have := hwle k i j (Ne.symm hik) (Ne.symm hjk) hij
    have := hcN i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    linarith
  · intro i j k hij hik hjk
    have := hwle i j k hij hik hjk
    have := hcN i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    rw [mul_add]
    linarith
  · intro i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    linarith
  · intro i j k hij hik hjk
    have h1 := coord_le hp0 v hij hik hjk
    rw [hvc i j k hij hik hjk] at h1
    linarith [le_abs_self (X i i + X j i + X k i)]
  · intro i j k hij hik hjk
    have h1 := two_coord_le hp v hij hik hjk
    rw [hvc j i k (Ne.symm hij) hjk hik, hvc k i j (Ne.symm hik) (Ne.symm hjk) hij] at h1
    have h2 : cp p * lpNorm p v < cp p * (3 * q) := mul_lt_mul_of_pos_left hT hcpos
    have h3 : cp p * (3 * q) ≤ 2 * thib * (3 * q) :=
      mul_le_mul_of_nonneg_right hcm (by linarith)
    have := le_abs_self (X j j + X i j + X k j)
    have := le_abs_self (X k k + X i k + X j k)
    linarith

/-! ## Contraction rounds -/

section Rounds

variable {p c D δ h A cmax tlo : ℝ} {X : Triple}

theorem ratio_round (F : Facts p c D δ h A cmax tlo X) {n s τ σ : ℝ}
    (hn : ∀ i, n ≤ lpNorm p (X i)) (hn0 : 0 < n) (hD0 : 0 ≤ D) (hs : s ≤ 2 * tlo - D / n)
    (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hτc : 1 < τ ^ p + (s - τ) ^ p) (hσc : 1 < σ ^ p + (s - σ) ^ p) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * lpNorm p (X i) < X i j ∧ X i j < σ * lpNorm p (X i) := by
  intro i j k hij hik hjk
  have hp0 : 0 < p := by linarith [F.hp]
  have hN : 0 < lpNorm p (X i) := lt_of_lt_of_le hn0 (hn i)
  set N := lpNorm p (X i) with hNdef
  have hbj := F.off i j hij
  have hbk := F.off i k hik
  have hxy : (X i j / N) ^ p + (X i k / N) ^ p ≤ 1 := by
    rw [Real.div_rpow (by linarith) hN.le, Real.div_rpow (by linarith) hN.le, ← add_div,
      div_le_one (by positivity)]
    have := F.rowfull i j k hij hik hjk
    have := Real.rpow_nonneg (F.diag i) p
    linarith
  have hsum : s ≤ X i j / N + X i k / N := by
    rw [← add_div, le_div_iff₀ hN]
    have a1 : s * N ≤ (2 * tlo - D / n) * N := mul_le_mul_of_nonneg_right hs hN.le
    have a2 : D ≤ D / n * N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn0]; exact mul_le_mul_of_nonneg_left (hn i) hD0
    have a3 : 2 * tlo * N ≤ c * N := mul_le_mul_of_nonneg_right F.hct hN.le
    have a4 := F.wD i j k hij hik hjk
    have e : (2 * tlo - D / n) * N = 2 * tlo * N - D / n * N := by ring
    linarith
  have h1 := ratio_lower F.hp (by positivity) (by positivity) hxy hsum hτ0 hτs hτc
  have h2 := ratio_upper F.hp (by positivity) (by positivity) hxy hsum hs1 hσs hσc
  exact ⟨(lt_div_iff₀ hN).1 h1, (div_lt_iff₀ hN).1 h2⟩

theorem lower_round (F : Facts p c D δ h A cmax tlo X) {n τ n' Ab : ℝ}
    (hn : ∀ i, n ≤ lpNorm p (X i)) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → τ * lpNorm p (X i) < X i j)
    (hn'0 : 0 < n') (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / n') ^ p + (1 - δ / n') ^ p)
    (hchk : A ≤ τ * (3 - n') - Ab) : ∀ i, n' ≤ lpNorm p (X i) := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  by_contra hlt
  push Not at hlt
  have ha := diag_cert F.hp (F.diag i) F.hc (F.row i j k hij hik hjk) (F.wD i j k hij hik hjk)
    F.hDc hδ0 (hδn.trans (hn i)) hlt.le hn'0 hAb hcert
  have t1 := F.T1 i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have ns := F.nsum i j k hij hik hjk
  have m1 : τ * (3 - n') ≤ τ * (lpNorm p (X j) + lpNorm p (X k)) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ0
  rw [mul_add] at m1
  linarith

theorem upper_round (F : Facts p c D δ h A cmax tlo X) {n σ U Ab : ℝ}
    (hn : ∀ i, n ≤ lpNorm p (X i)) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j < σ * lpNorm p (X i))
    (hU3 : U < 3) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / (3 - U)) ^ p + (1 - δ / (3 - U)) ^ p)
    (hchk : cmax * A ≤ 6 - h - σ * (3 - U) - Ab) : ∀ i, lpNorm p (X i) ≤ U := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  by_contra hlt
  push Not at hlt
  have ns := F.nsum i j k hij hik hjk
  have rj := F.row j i k (Ne.symm hij) hjk hik
  have rk := F.row k i j (Ne.symm hik) (Ne.symm hjk) hij
  have hbji := F.off j i (Ne.symm hij)
  have hbjk := F.off j k hjk
  have hbki := F.off k i (Ne.symm hik)
  have hbkj := F.off k j (Ne.symm hjk)
  have hm := mink2 F.hp (F.diag j) (div_nonneg (by linarith) F.hc.le) (F.diag k)
    (div_nonneg (by linarith) F.hc.le) (lpNorm_nonneg3 p _) (lpNorm_nonneg3 p _) rj rk
  rw [← add_div] at hm
  have hNj := hn j
  have hNk := hn k
  have ha := diag_cert F.hp (by linarith [F.diag j, F.diag k]) F.hc hm (F.wD2 i j k hij hik hjk)
    F.hDc hδ0 (by linarith) (by linarith : lpNorm p (X j) + lpNorm p (X k) ≤ 3 - U)
    (by linarith) hAb hcert
  have t2 := F.T2 i j k hij hik hjk
  have os := F.offsum i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have m1 : σ * (lpNorm p (X j) + lpNorm p (X k)) ≤ σ * (3 - U) :=
    mul_le_mul_of_nonneg_left (by linarith) hσ0
  rw [mul_add] at m1
  linarith

theorem final_round (F : Facts p c D δ h A cmax tlo X) {n U τ σ Ab : ℝ}
    (hn : ∀ i, n ≤ lpNorm p (X i)) (hU : ∀ i, lpNorm p (X i) ≤ U) (hδn : δ ≤ n)
    (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * lpNorm p (X i) < X i j ∧ X i j < σ * lpNorm p (X i))
    (hU0 : 0 < U) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p)
    (h1 : 849/1000 ≤ τ * n) (h2 : σ * U ≤ 1121/1000) (h3 : Ab ≤ 1065/1000)
    (h4 : 625/1000 ≤ τ * (3 - U) - A) : finalBox X := by
  intro j i
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    obtain ⟨k, l, hjk, hjl, hkl⟩ := others j
    have ha := diag_cert F.hp (F.diag j) F.hc (F.row j k l hjk hjl hkl)
      (F.wD j k l hjk hjl hkl) F.hDc hδ0 (hδn.trans (hn j)) (hU j) hU0 hAb hcert
    have t1 := F.T1 j k l hjk hjl hkl
    have r1 := (hr k j l (Ne.symm hjk) hkl hjl).1
    have r2 := (hr l j k (Ne.symm hjl) (Ne.symm hkl) hjk).1
    have ns := F.nsum j k l hjk hjl hkl
    have m1 : τ * (3 - U) ≤ τ * (lpNorm p (X k) + lpNorm p (X l)) :=
      mul_le_mul_of_nonneg_left (by linarith [hU j]) hτ0
    rw [mul_add] at m1
    constructor <;> linarith
  · rw [if_neg hji]
    obtain ⟨k, hjk, hik⟩ := third hji
    have r := hr j i k hji hjk hik
    have m1 : τ * n ≤ τ * lpNorm p (X j) := mul_le_mul_of_nonneg_left (hn j) hτ0
    have m2 : σ * lpNorm p (X j) ≤ σ * U := mul_le_mul_of_nonneg_left (hU j) hσ0
    constructor <;> linarith [r.1, r.2]

end Rounds

/-! ## The generic slab theorem (two contraction rounds) -/

theorem slab_generic {α β tlo thia thib D δ h q s1 τ1 σ1 n1 A1 s2 τ2 σ2 n2 A2 U2 B2 Af : ℝ}
    (hα : 0 < α) (htlo0 : 0 < tlo) (htlo : tlo ≤ (1/2 : ℝ) ^ (1/α))
    (hthia : (1/2 : ℝ) ^ (1/α) ≤ thia) (hthib : (1/2 : ℝ) ^ (1/β) ≤ thib)
    (hD : 2000 / (448 * α) + 3 / 10^10 - 6 * (1 - thia) ≤ D) (hD0 : 0 ≤ D)
    (hδ : D / (2 * tlo) ≤ δ) (hh : 2000 / (448 * α) + 3 / 10^10 ≤ h) (hq : 0 < q)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 79/100)
    -- round 1
    (hs1 : s1 ≤ 2 * tlo - D / (79/100)) (hτ1 : 0 ≤ τ1) (hτs1 : 2 * τ1 ≤ s1) (hs11 : 1 ≤ s1)
    (hσs1 : s1 ≤ 2 * σ1)
    (cτ1 : ∀ p : ℝ, 0 ≤ p → p ≤ β → 1 < τ1 ^ p + (s1 - τ1) ^ p)
    (cσ1 : ∀ p : ℝ, 0 ≤ p → p ≤ β → 1 < σ1 ^ p + (s1 - σ1) ^ p)
    (hn1 : 0 < n1) (hA1 : 0 ≤ A1) (cA1 : ∀ p : ℝ, 0 ≤ p → p ≤ β → 1 ≤ (A1 / n1) ^ p + (1 - δ / n1) ^ p)
    (kA1 : 3 * q ≤ τ1 * (3 - n1) - A1)
    -- round 2
    (hδn1 : δ ≤ n1)
    (hs2 : s2 ≤ 2 * tlo - D / n1) (hτ2 : 0 ≤ τ2) (hτs2 : 2 * τ2 ≤ s2) (hs21 : 1 ≤ s2)
    (hσs2 : s2 ≤ 2 * σ2) (hσ2 : 0 ≤ σ2)
    (cτ2 : ∀ p : ℝ, 0 ≤ p → p ≤ β → 1 < τ2 ^ p + (s2 - τ2) ^ p)
    (cσ2 : ∀ p : ℝ, 0 ≤ p → p ≤ β → 1 < σ2 ^ p + (s2 - σ2) ^ p)
    (hn2 : 0 < n2) (hA2 : 0 ≤ A2) (cA2 : ∀ p : ℝ, 0 ≤ p → p ≤ β → 1 ≤ (A2 / n2) ^ p + (1 - δ / n2) ^ p)
    (kA2 : 3 * q ≤ τ2 * (3 - n2) - A2)
    (hU2 : U2 < 3) (hB2 : 0 ≤ B2)
    (cB2 : ∀ p : ℝ, 0 ≤ p → p ≤ β → 1 ≤ (B2 / (3 - U2)) ^ p + (1 - δ / (3 - U2)) ^ p)
    (kB2 : 2 * thib * (3 * q) ≤ 6 - h - σ2 * (3 - U2) - B2)
    -- final
    (hδn2 : δ ≤ n2) (hU20 : 0 < U2) (hAf : 0 ≤ Af)
    (cAf : ∀ p : ℝ, 0 ≤ p → p ≤ β → 1 ≤ (Af / U2) ^ p + (1 - δ / U2) ^ p)
    (f1 : 849/1000 ≤ τ2 * n2) (f2 : σ2 * U2 ≤ 1121/1000) (f3 : Af ≤ 1065/1000)
    (f4 : 625/1000 ≤ τ2 * (3 - U2) - 3 * q) :
    ∀ p : ℝ, 32 ≤ p → α ≤ p → p ≤ β → ∀ X : Triple, coarseBox X →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < 3 * q →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X := by
  intro p hp32 hαp hpβ X hB hS hT hG
  have F := facts_of hα hαp hpβ hp32 htlo0 htlo hthia hthib hD hD0 hδ hh hq hB hS hT hG
  have hp0 : 0 ≤ p := by linarith
  have hn0 : ∀ i, (79/100 : ℝ) ≤ lpNorm p (X i) := by
    intro i
    obtain ⟨j, k, hij, hik, hjk⟩ := others i
    have := F.rowfull i j k hij hik hjk
    have h1 := F.off i j hij
    have h2 : X i j ^ p ≤ lpNorm p (X i) ^ p := by
      have := Real.rpow_nonneg (F.diag i) p
      have := Real.rpow_nonneg (show (0:ℝ) ≤ X i k by linarith [F.off i k hik]) p
      linarith
    have := (Real.rpow_le_rpow_iff (by linarith) (lpNorm_nonneg3 p _) (by linarith)).1 h2
    linarith
  have R1 := ratio_round F hn0 (by norm_num) hD0 hs1 hτ1 hτs1 hs11 hσs1
    (cτ1 p hp0 hpβ) (cσ1 p hp0 hpβ)
  have L1 := lower_round F hn0 hδ1 hδ0 hτ1 (fun i j k a b c ↦ (R1 i j k a b c).1) hn1 hA1
    (cA1 p hp0 hpβ) kA1
  have R2 := ratio_round F L1 hn1 hD0 hs2 hτ2 hτs2 hs21 hσs2
    (cτ2 p hp0 hpβ) (cσ2 p hp0 hpβ)
  have L2 := lower_round F L1 hδn1 hδ0 hτ2 (fun i j k a b c ↦ (R2 i j k a b c).1) hn2 hA2
    (cA2 p hp0 hpβ) kA2
  have V2 := upper_round F L1 hδn1 hδ0 hσ2 (fun i j k a b c ↦ (R2 i j k a b c).2) hU2 hB2
    (cB2 p hp0 hpβ) kB2
  exact final_round F L2 V2 hδn2 hδ0 hτ2 hσ2 R2 hU20 hAf (cAf p hp0 hpβ) f1 f2 f3 f4

/-! ## Per-sub-slab instances (rational data from the schedule) -/

theorem sub_32_129_4 : ∀ p : ℝ, 32 ≤ p → (32 : ℝ) ≤ p → p ≤ (129/4 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3851/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (32 : ℝ)) (β := (129/4 : ℝ)) (tlo := (244643/250000 : ℝ)) (thia := (978573/1000000 : ℝ)) (thib := (978737/1000000 : ℝ)) (D := (1368366109/125000000000 : ℝ)) (δ := (2797/500000 : ℝ)) (h := (17438616109/125000000000 : ℝ)) (q := (3851/10000 : ℝ)) (s1 := (2429/1250 : ℝ)) (τ1 := (1187/1250 : ℝ)) (σ1 := (621/625 : ℝ)) (n1 := (223/250 : ℝ)) (A1 := (529/625 : ℝ)) (s2 := (2431/1250 : ℝ)) (τ2 := (4759/5000 : ℝ)) (σ2 := (993/1000 : ℝ)) (n2 := (1789/2000 : ℝ)) (A2 := (8487/10000 : ℝ)) (U2 := (1409/1250 : ℝ)) (B2 := (17393/10000 : ℝ)) (Af := (17/16 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (244643/250000 : ℝ)) (by norm_num) 1 32 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (978573/1000000 : ℝ)) (by norm_num) (by norm_num) 1 32 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (978737/1000000 : ℝ)) (by norm_num) (by norm_num) 4 129 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (943317/5000000 : ℝ)) (Y := (8129681/10000000 : ℝ)) 129 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8129681/10000000 : ℝ)) (Y := (943317/5000000 : ℝ)) 129 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (115061/625000 : ℝ)) (Y := (816371/1000000 : ℝ)) 129 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (2032819/10000000 : ℝ)) (Y := (7972843/10000000 : ℝ)) 129 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (7972843/10000000 : ℝ)) (Y := (2032819/10000000 : ℝ)) 129 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1835933/10000000 : ℝ)) (Y := (1633671/2000000 : ℝ)) 129 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (115117/1250000 : ℝ)) (Y := (1816067/2000000 : ℝ)) 129 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1486197/10000000 : ℝ)) (Y := (8517631/10000000 : ℝ)) 129 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_129_4_65_2 : ∀ p : ℝ, 32 ≤ p → (129/4 : ℝ) ≤ p → p ≤ (65/2 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3851/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (129/4 : ℝ)) (β := (65/2 : ℝ)) (tlo := (61171/62500 : ℝ)) (thia := (978737/1000000 : ℝ)) (thib := (978899/1000000 : ℝ)) (D := (10849464309/1000000000000 : ℝ)) (δ := (5543/1000000 : ℝ)) (h := (138427464309/1000000000000 : ℝ)) (q := (3851/10000 : ℝ)) (s1 := (19437/10000 : ℝ)) (τ1 := (9501/10000 : ℝ)) (σ1 := (621/625 : ℝ)) (n1 := (2231/2500 : ℝ)) (A1 := (8471/10000 : ℝ)) (s2 := (19453/10000 : ℝ)) (τ2 := (9523/10000 : ℝ)) (σ2 := (993/1000 : ℝ)) (n2 := (2237/2500 : ℝ)) (A2 := (8493/10000 : ℝ)) (U2 := (11273/10000 : ℝ)) (B2 := (17401/10000 : ℝ)) (Af := (1063/1000 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (61171/62500 : ℝ)) (by norm_num) 4 129 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (978737/1000000 : ℝ)) (by norm_num) (by norm_num) 4 129 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (978899/1000000 : ℝ)) (by norm_num) (by norm_num) 2 65 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (378907/2000000 : ℝ)) (Y := (4058321/5000000 : ℝ)) 65 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (4058321/5000000 : ℝ)) (Y := (378907/2000000 : ℝ)) 65 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (229933/1250000 : ℝ)) (Y := (51043/62500 : ℝ)) 65 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (2042433/10000000 : ℝ)) (Y := (3979427/5000000 : ℝ)) 65 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (3979427/5000000 : ℝ)) (Y := (2042433/10000000 : ℝ)) 65 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (183397/1000000 : ℝ)) (Y := (8171331/10000000 : ℝ)) 65 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (919273/10000000 : ℝ)) (Y := (4540779/5000000 : ℝ)) 65 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (741339/5000000 : ℝ)) (Y := (1703949/2000000 : ℝ)) 65 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_65_2_131_4 : ∀ p : ℝ, 32 ≤ p → (65/2 : ℝ) ≤ p → p ≤ (131/4 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3851/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (65/2 : ℝ)) (β := (131/4 : ℝ)) (tlo := (489449/500000 : ℝ)) (thia := (978899/1000000 : ℝ)) (thib := (489529/500000 : ℝ)) (D := (10756637663/1000000000000 : ℝ)) (δ := (1099/200000 : ℝ)) (h := (137362637663/1000000000000 : ℝ)) (q := (3851/10000 : ℝ)) (s1 := (19441/10000 : ℝ)) (τ1 := (1901/2000 : ℝ)) (σ1 := (621/625 : ℝ)) (n1 := (8927/10000 : ℝ)) (A1 := (2119/2500 : ℝ)) (s2 := (19457/10000 : ℝ)) (τ2 := (4763/5000 : ℝ)) (σ2 := (9931/10000 : ℝ)) (n2 := (179/200 : ℝ)) (A2 := (4249/5000 : ℝ)) (U2 := (451/400 : ℝ)) (B2 := (1088/625 : ℝ)) (Af := (2659/2500 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (489449/500000 : ℝ)) (by norm_num) 2 65 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (978899/1000000 : ℝ)) (by norm_num) (by norm_num) 2 65 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (489529/500000 : ℝ)) (by norm_num) (by norm_num) 4 131 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (237051/1250000 : ℝ)) (Y := (64829/80000 : ℝ)) 131 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (64829/80000 : ℝ)) (Y := (237051/1250000 : ℝ)) 131 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (915413/5000000 : ℝ)) (Y := (1021149/1250000 : ℝ)) 131 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (40771/200000 : ℝ)) (Y := (3985567/5000000 : ℝ)) 131 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (3985567/5000000 : ℝ)) (Y := (40771/200000 : ℝ)) 131 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (183197/1000000 : ℝ)) (Y := (8173451/10000000 : ℝ)) 131 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (917721/10000000 : ℝ)) (Y := (454119/500000 : ℝ)) 131 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (739849/5000000 : ℝ)) (Y := (2130357/2500000 : ℝ)) 131 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_131_4_33 : ∀ p : ℝ, 32 ≤ p → (131/4 : ℝ) ≤ p → p ≤ (33 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3851/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (131/4 : ℝ)) (β := (33 : ℝ)) (tlo := (979057/1000000 : ℝ)) (thia := (489529/500000 : ℝ)) (thib := (195843/200000 : ℝ)) (D := (1332758489/125000000000 : ℝ)) (δ := (2723/500000 : ℝ)) (h := (17039258489/125000000000 : ℝ)) (q := (3851/10000 : ℝ)) (s1 := (9723/5000 : ℝ)) (τ1 := (9509/10000 : ℝ)) (σ1 := (9937/10000 : ℝ)) (n1 := (893/1000 : ℝ)) (A1 := (4241/5000 : ℝ)) (s2 := (19461/10000 : ℝ)) (τ2 := (9529/10000 : ℝ)) (σ2 := (2483/2500 : ℝ)) (n2 := (1119/1250 : ℝ)) (A2 := (8503/10000 : ℝ)) (U2 := (5639/5000 : ℝ)) (B2 := (3483/2000 : ℝ)) (Af := (10643/10000 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (979057/1000000 : ℝ)) (by norm_num) 4 131 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (489529/500000 : ℝ)) (by norm_num) (by norm_num) 4 131 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (195843/200000 : ℝ)) (by norm_num) (by norm_num) 1 33 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (118667/625000 : ℝ)) (Y := (4058771/5000000 : ℝ)) 33 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (4058771/5000000 : ℝ)) (Y := (118667/625000 : ℝ)) 33 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1829551/10000000 : ℝ)) (Y := (4086013/5000000 : ℝ)) 33 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (2034987/10000000 : ℝ)) (Y := (7983833/10000000 : ℝ)) 33 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (7983833/10000000 : ℝ)) (Y := (2034987/10000000 : ℝ)) 33 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (114393/625000 : ℝ)) (Y := (4088047/5000000 : ℝ)) 33 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (918017/10000000 : ℝ)) (Y := (9083433/10000000 : ℝ)) 33 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1477253/10000000 : ℝ)) (Y := (532729/625000 : ℝ)) 33 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_33_67_2 : ∀ p : ℝ, 32 ≤ p → (33 : ℝ) ≤ p → p ≤ (67/2 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3839/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (33 : ℝ)) (β := (67/2 : ℝ)) (tlo := (489607/500000 : ℝ)) (thia := (195843/200000 : ℝ)) (thib := (489761/500000 : ℝ)) (D := (5285692791/500000000000 : ℝ)) (δ := (2699/500000 : ℝ)) (h := (67640692791/500000000000 : ℝ)) (q := (3839/10000 : ℝ)) (s1 := (389/200 : ℝ)) (τ1 := (9511/10000 : ℝ)) (σ1 := (9939/10000 : ℝ)) (n1 := (8947/10000 : ℝ)) (A1 := (4253/5000 : ℝ)) (s2 := (9733/5000 : ℝ)) (τ2 := (2383/2500 : ℝ)) (σ2 := (4967/5000 : ℝ)) (n2 := (897/1000 : ℝ)) (A2 := (8527/10000 : ℝ)) (U2 := (2813/2500 : ℝ)) (B2 := (873/500 : ℝ)) (Af := (1063/1000 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (489607/500000 : ℝ)) (by norm_num) 1 33 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (195843/200000 : ℝ)) (by norm_num) (by norm_num) 1 33 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (489761/500000 : ℝ)) (by norm_num) (by norm_num) 2 67 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1864563/10000000 : ℝ)) (Y := (814667/1000000 : ℝ)) 67 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (814667/1000000 : ℝ)) (Y := (1864563/10000000 : ℝ)) 67 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (919551/5000000 : ℝ)) (Y := (8165003/10000000 : ℝ)) 67 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (250943/1250000 : ℝ)) (Y := (2002623/2500000 : ℝ)) 67 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (2002623/2500000 : ℝ)) (Y := (250943/1250000 : ℝ)) 67 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (916427/5000000 : ℝ)) (Y := (8169261/10000000 : ℝ)) 67 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (921491/10000000 : ℝ)) (Y := (567453/625000 : ℝ)) 67 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (59529/400000 : ℝ)) (Y := (8512081/10000000 : ℝ)) 67 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_67_2_34 : ∀ p : ℝ, 32 ≤ p → (67/2 : ℝ) ≤ p → p ≤ (34 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3839/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (67/2 : ℝ)) (β := (34 : ℝ)) (tlo := (979521/1000000 : ℝ)) (thia := (489761/500000 : ℝ)) (thib := (48991/50000 : ℝ)) (D := (2598565107/250000000000 : ℝ)) (δ := (2653/500000 : ℝ)) (h := (33315565107/250000000000 : ℝ)) (q := (3839/10000 : ℝ)) (s1 := (9729/5000 : ℝ)) (τ1 := (4759/5000 : ℝ)) (σ1 := (497/500 : ℝ)) (n1 := (1119/1250 : ℝ)) (A1 := (2129/2500 : ℝ)) (s2 := (9737/5000 : ℝ)) (τ2 := (477/500 : ℝ)) (σ2 := (4967/5000 : ℝ)) (n2 := (561/625 : ℝ)) (A2 := (8539/10000 : ℝ)) (U2 := (5627/5000 : ℝ)) (B2 := (699/400 : ℝ)) (Af := (133/125 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (979521/1000000 : ℝ)) (by norm_num) 2 67 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (489761/500000 : ℝ)) (by norm_num) (by norm_num) 2 67 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (48991/50000 : ℝ)) (by norm_num) (by norm_num) 1 34 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1864463/10000000 : ℝ)) (Y := (4074807/5000000 : ℝ)) 34 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (4074807/5000000 : ℝ)) (Y := (1864463/10000000 : ℝ)) 34 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (915587/5000000 : ℝ)) (Y := (8169941/10000000 : ℝ)) 34 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (403343/2000000 : ℝ)) (Y := (3992007/5000000 : ℝ)) 34 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (3992007/5000000 : ℝ)) (Y := (403343/2000000 : ℝ)) 34 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (916203/5000000 : ℝ)) (Y := (8174371/10000000 : ℝ)) 34 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (918949/10000000 : ℝ)) (Y := (9081257/10000000 : ℝ)) 34 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (2969/20000 : ℝ)) (Y := (1703127/2000000 : ℝ)) 34 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_34_35 : ∀ p : ℝ, 32 ≤ p → (34 : ℝ) ≤ p → p ≤ (35 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3827/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (34 : ℝ)) (β := (35 : ℝ)) (tlo := (979819/1000000 : ℝ)) (thia := (48991/50000 : ℝ)) (thib := (980391/1000000 : ℝ)) (D := (10222521309/1000000000000 : ℝ)) (δ := (5217/1000000 : ℝ)) (h := (131302521309/1000000000000 : ℝ)) (q := (3827/10000 : ℝ)) (s1 := (9733/5000 : ℝ)) (τ1 := (4761/5000 : ℝ)) (σ1 := (1243/1250 : ℝ)) (n1 := (8967/10000 : ℝ)) (A1 := (1709/2000 : ℝ)) (s2 := (9741/5000 : ℝ)) (τ2 := (9543/10000 : ℝ)) (σ2 := (9939/10000 : ℝ)) (n2 := (8991/10000 : ℝ)) (A2 := (8567/10000 : ℝ)) (U2 := (281/250 : ℝ)) (B2 := (17529/10000 : ℝ)) (Af := (1331/1250 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (979819/1000000 : ℝ)) (by norm_num) 1 34 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (48991/50000 : ℝ)) (by norm_num) (by norm_num) 1 34 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (980391/1000000 : ℝ)) (by norm_num) (by norm_num) 1 35 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (360177/2000000 : ℝ)) (Y := (1643119/2000000 : ℝ)) 35 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (1643119/2000000 : ℝ)) (Y := (360177/2000000 : ℝ)) 35 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (231303/1250000 : ℝ)) (Y := (1019099/1250000 : ℝ)) 35 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (486309/2500000 : ℝ)) (Y := (8072241/10000000 : ℝ)) 35 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8072241/10000000 : ℝ)) (Y := (486309/2500000 : ℝ)) 35 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (368771/2000000 : ℝ)) (Y := (32629/40000 : ℝ)) 35 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (232429/2500000 : ℝ)) (Y := (2267829/2500000 : ℝ)) 35 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1505083/10000000 : ℝ)) (Y := (4248681/5000000 : ℝ)) 35 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_35_71_2 : ∀ p : ℝ, 32 ≤ p → (35 : ℝ) ≤ p → p ≤ (71/2 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3827/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (35 : ℝ)) (β := (71/2 : ℝ)) (tlo := (98039/100000 : ℝ)) (thia := (980391/1000000 : ℝ)) (thib := (196133/200000 : ℝ)) (D := (9897020709/1000000000000 : ℝ)) (δ := (631/125000 : ℝ)) (h := (127551020709/1000000000000 : ℝ)) (q := (3827/10000 : ℝ)) (s1 := (9741/5000 : ℝ)) (τ1 := (477/500 : ℝ)) (σ1 := (4971/5000 : ℝ)) (n1 := (8987/10000 : ℝ)) (A1 := (1713/2000 : ℝ)) (s2 := (19497/10000 : ℝ)) (τ2 := (239/250 : ℝ)) (σ2 := (9937/10000 : ℝ)) (n2 := (9009/10000 : ℝ)) (A2 := (4293/5000 : ℝ)) (U2 := (5613/5000 : ℝ)) (B2 := (351/200 : ℝ)) (Af := (5319/5000 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (98039/100000 : ℝ)) (by norm_num) 1 35 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (980391/1000000 : ℝ)) (by norm_num) (by norm_num) 1 35 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (196133/200000 : ℝ)) (by norm_num) (by norm_num) 2 71 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (75167/400000 : ℝ)) (Y := (8134267/10000000 : ℝ)) 71 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8134267/10000000 : ℝ)) (Y := (75167/400000 : ℝ)) 71 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1813419/10000000 : ℝ)) (Y := (2046897/2500000 : ℝ)) 71 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (126513/625000 : ℝ)) (Y := (3995147/5000000 : ℝ)) 71 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (3995147/5000000 : ℝ)) (Y := (126513/625000 : ℝ)) 71 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1813667/10000000 : ℝ)) (Y := (4095799/5000000 : ℝ)) 71 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (91321/1000000 : ℝ)) (Y := (9088439/10000000 : ℝ)) 71 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (29619/200000 : ℝ)) (Y := (8521497/10000000 : ℝ)) 71 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_71_2_36 : ∀ p : ℝ, 32 ≤ p → (71/2 : ℝ) ≤ p → p ≤ (36 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3827/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (71/2 : ℝ)) (β := (36 : ℝ)) (tlo := (122583/125000 : ℝ)) (thia := (196133/200000 : ℝ)) (thib := (980931/1000000 : ℝ)) (D := (9744527463/1000000000000 : ℝ)) (δ := (4969/1000000 : ℝ)) (h := (125754527463/1000000000000 : ℝ)) (q := (3827/10000 : ℝ)) (s1 := (19489/10000 : ℝ)) (τ1 := (4773/5000 : ℝ)) (σ1 := (9943/10000 : ℝ)) (n1 := (8991/10000 : ℝ)) (A1 := (4287/5000 : ℝ)) (s2 := (1219/625 : ℝ)) (τ2 := (4783/5000 : ℝ)) (σ2 := (4969/5000 : ℝ)) (n2 := (9013/10000 : ℝ)) (A2 := (1719/2000 : ℝ)) (U2 := (11229/10000 : ℝ)) (B2 := (8781/5000 : ℝ)) (Af := (1331/1250 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (122583/125000 : ℝ)) (by norm_num) 2 71 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (196133/200000 : ℝ)) (by norm_num) (by norm_num) 2 71 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (980931/1000000 : ℝ)) (by norm_num) (by norm_num) 1 36 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1877463/10000000 : ℝ)) (Y := (8140063/10000000 : ℝ)) 36 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8140063/10000000 : ℝ)) (Y := (1877463/10000000 : ℝ)) 36 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (113083/625000 : ℝ)) (Y := (8191313/10000000 : ℝ)) 36 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (2024387/10000000 : ℝ)) (Y := (999249/1250000 : ℝ)) 36 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (999249/1250000 : ℝ)) (Y := (2024387/10000000 : ℝ)) 36 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (904741/5000000 : ℝ)) (Y := (1639063/2000000 : ℝ)) 36 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (227539/2500000 : ℝ)) (Y := (908987/1000000 : ℝ)) 36 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (738483/5000000 : ℝ)) (Y := (1704869/2000000 : ℝ)) 36 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_36_37 : ∀ p : ℝ, 32 ≤ p → (36 : ℝ) ≤ p → p ≤ (37 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (1903/5000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (36 : ℝ)) (β := (37 : ℝ)) (tlo := (98093/100000 : ℝ)) (thia := (980931/1000000 : ℝ)) (thib := (981441/1000000 : ℝ)) (D := (1199242101/125000000000 : ℝ)) (δ := (4891/1000000 : ℝ)) (h := (15500992101/125000000000 : ℝ)) (q := (1903/5000 : ℝ)) (s1 := (19497/10000 : ℝ)) (τ1 := (9551/10000 : ℝ)) (σ1 := (4973/5000 : ℝ)) (n1 := (4511/5000 : ℝ)) (A1 := (8617/10000 : ℝ)) (s2 := (2439/1250 : ℝ)) (τ2 := (9571/10000 : ℝ)) (σ2 := (9941/10000 : ℝ)) (n2 := (1809/2000 : ℝ)) (A2 := (4319/5000 : ℝ)) (U2 := (11183/10000 : ℝ)) (B2 := (17641/10000 : ℝ)) (Af := (664/625 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (98093/100000 : ℝ)) (by norm_num) 1 36 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (980931/1000000 : ℝ)) (by norm_num) (by norm_num) 1 36 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (981441/1000000 : ℝ)) (by norm_num) (by norm_num) 1 37 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1827289/10000000 : ℝ)) (Y := (127883/156250 : ℝ)) 37 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (127883/156250 : ℝ)) (Y := (1827289/10000000 : ℝ)) 37 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (913989/5000000 : ℝ)) (Y := (4089031/5000000 : ℝ)) 37 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (987167/5000000 : ℝ)) (Y := (4016823/5000000 : ℝ)) 37 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (4016823/5000000 : ℝ)) (Y := (987167/5000000 : ℝ)) 37 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (910209/5000000 : ℝ)) (Y := (8182257/10000000 : ℝ)) 37 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (11479/125000 : ℝ)) (Y := (9081939/10000000 : ℝ)) 37 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (299937/2000000 : ℝ)) (Y := (531431/625000 : ℝ)) 37 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_37_38 : ∀ p : ℝ, 32 ≤ p → (37 : ℝ) ≤ p → p ≤ (38 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (1903/5000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (37 : ℝ)) (β := (38 : ℝ)) (tlo := (3067/3125 : ℝ)) (thia := (981441/1000000 : ℝ)) (thib := (39277/40000 : ℝ)) (D := (9302370957/1000000000000 : ℝ)) (δ := (237/50000 : ℝ)) (h := (120656370957/1000000000000 : ℝ)) (q := (1903/5000 : ℝ)) (s1 := (19511/10000 : ℝ)) (τ1 := (2391/2500 : ℝ)) (σ1 := (9947/10000 : ℝ)) (n1 := (9031/10000 : ℝ)) (A1 := (1727/2000 : ℝ)) (s2 := (781/400 : ℝ)) (τ2 := (4791/5000 : ℝ)) (σ2 := (9943/10000 : ℝ)) (n2 := (2263/2500 : ℝ)) (A2 := (4327/5000 : ℝ)) (U2 := (2797/2500 : ℝ)) (B2 := (3533/2000 : ℝ)) (Af := (5321/5000 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (3067/3125 : ℝ)) (by norm_num) 1 37 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (981441/1000000 : ℝ)) (by norm_num) (by norm_num) 1 37 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (39277/40000 : ℝ)) (by norm_num) (by norm_num) 1 38 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (918911/5000000 : ℝ)) (Y := (326859/400000 : ℝ)) 38 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (326859/400000 : ℝ)) (Y := (918911/5000000 : ℝ)) 38 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (181973/1000000 : ℝ)) (Y := (409377/500000 : ℝ)) 38 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1973941/10000000 : ℝ)) (Y := (8047531/10000000 : ℝ)) 38 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8047531/10000000 : ℝ)) (Y := (1973941/10000000 : ℝ)) 38 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1811127/10000000 : ℝ)) (Y := (8191349/10000000 : ℝ)) 38 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (14309/156250 : ℝ)) (Y := (9085837/10000000 : ℝ)) 38 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (46681/312500 : ℝ)) (Y := (8510061/10000000 : ℝ)) 38 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_38_40 : ∀ p : ℝ, 32 ≤ p → (38 : ℝ) ≤ p → p ≤ (40 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (1893/5000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (38 : ℝ)) (β := (40 : ℝ)) (tlo := (245481/250000 : ℝ)) (thia := (39277/40000 : ℝ)) (thib := (982821/1000000 : ℝ)) (D := (2257800827/250000000000 : ℝ)) (δ := (4599/1000000 : ℝ)) (h := (29370300827/250000000000 : ℝ)) (q := (1893/5000 : ℝ)) (s1 := (4881/2500 : ℝ)) (τ1 := (9571/10000 : ℝ)) (σ1 := (9953/10000 : ℝ)) (n1 := (9059/10000 : ℝ)) (A1 := (2171/2500 : ℝ)) (s2 := (9769/5000 : ℝ)) (τ2 := (9589/10000 : ℝ)) (σ2 := (9949/10000 : ℝ)) (n2 := (9079/10000 : ℝ)) (A2 := (8703/10000 : ℝ)) (U2 := (279/250 : ℝ)) (B2 := (3551/2000 : ℝ)) (Af := (1331/1250 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (245481/250000 : ℝ)) (by norm_num) 1 38 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (39277/40000 : ℝ)) (by norm_num) (by norm_num) 1 38 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (982821/1000000 : ℝ)) (by norm_num) (by norm_num) 1 40 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (865491/5000000 : ℝ)) (Y := (331299/400000 : ℝ)) 40 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (331299/400000 : ℝ)) (Y := (865491/5000000 : ℝ)) 40 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1843241/10000000 : ℝ)) (Y := (4079/5000 : ℝ)) 40 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (186609/1000000 : ℝ)) (Y := (254699/312500 : ℝ)) 40 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (254699/312500 : ℝ)) (Y := (186609/1000000 : ℝ)) 40 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (230223/1250000 : ℝ)) (Y := (8161669/10000000 : ℝ)) 40 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (116547/1250000 : ℝ)) (Y := (56679/62500 : ℝ)) 40 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1528107/10000000 : ℝ)) (Y := (1059677/1250000 : ℝ)) 40 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_40_42 : ∀ p : ℝ, 32 ≤ p → (40 : ℝ) ≤ p → p ≤ (42 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (18841/50000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (40 : ℝ)) (β := (42 : ℝ)) (tlo := (49141/50000 : ℝ)) (thia := (982821/1000000 : ℝ)) (thib := (61477/62500 : ℝ)) (D := (4266571579/500000000000 : ℝ)) (δ := (2171/500000 : ℝ)) (h := (55803571579/500000000000 : ℝ)) (q := (18841/50000 : ℝ)) (s1 := (4887/2500 : ℝ)) (τ1 := (9593/10000 : ℝ)) (σ1 := (1991/2000 : ℝ)) (n1 := (4551/5000 : ℝ)) (A1 := (8741/10000 : ℝ)) (s2 := (9781/5000 : ℝ)) (τ2 := (9611/10000 : ℝ)) (σ2 := (9951/10000 : ℝ)) (n2 := (9123/10000 : ℝ)) (A2 := (219/250 : ℝ)) (U2 := (11111/10000 : ℝ)) (B2 := (17847/10000 : ℝ)) (Af := (664/625 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (49141/50000 : ℝ)) (by norm_num) 1 40 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (982821/1000000 : ℝ)) (by norm_num) (by norm_num) 1 40 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (61477/62500 : ℝ)) (by norm_num) (by norm_num) 1 42 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (174617/1000000 : ℝ)) (Y := (1654867/2000000 : ℝ)) 42 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (1654867/2000000 : ℝ)) (Y := (174617/1000000 : ℝ)) 42 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1827343/10000000 : ℝ)) (Y := (818047/1000000 : ℝ)) 42 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (188921/1000000 : ℝ)) (Y := (8135841/10000000 : ℝ)) 42 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8135841/10000000 : ℝ)) (Y := (188921/1000000 : ℝ)) 42 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1817147/10000000 : ℝ)) (Y := (4092131/5000000 : ℝ)) 42 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (230623/2500000 : ℝ)) (Y := (226967/250000 : ℝ)) 42 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1522181/10000000 : ℝ)) (Y := (1696719/2000000 : ℝ)) 42 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_42_45 : ∀ p : ℝ, 32 ≤ p → (42 : ℝ) ≤ p → p ≤ (45 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (469/1250 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (42 : ℝ)) (β := (45 : ℝ)) (tlo := (983631/1000000 : ℝ)) (thia := (61477/62500 : ℝ)) (thib := (196943/200000 : ℝ)) (D := (8084517307/1000000000000 : ℝ)) (δ := (411/100000 : ℝ)) (h := (106292517307/1000000000000 : ℝ)) (q := (469/1250 : ℝ)) (s1 := (1957/1000 : ℝ)) (τ1 := (961/1000 : ℝ)) (σ1 := (249/250 : ℝ)) (n1 := (9133/10000 : ℝ)) (A1 := (2199/2500 : ℝ)) (s2 := (1224/625 : ℝ)) (τ2 := (2407/2500 : ℝ)) (σ2 := (2489/2500 : ℝ)) (n2 := (9153/10000 : ℝ)) (A2 := (1763/2000 : ℝ)) (U2 := (11089/10000 : ℝ)) (B2 := (897/500 : ℝ)) (Af := (5319/5000 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (983631/1000000 : ℝ)) (by norm_num) 1 42 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (61477/62500 : ℝ)) (by norm_num) (by norm_num) 1 42 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (196943/200000 : ℝ)) (by norm_num) (by norm_num) 1 45 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1669369/10000000 : ℝ)) (Y := (8349687/10000000 : ℝ)) 45 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8349687/10000000 : ℝ)) (Y := (1669369/10000000 : ℝ)) 45 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (115109/625000 : ℝ)) (Y := (63774/78125 : ℝ)) 45 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (56751/312500 : ℝ)) (Y := (1640023/2000000 : ℝ)) 45 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (1640023/2000000 : ℝ)) (Y := (56751/312500 : ℝ)) 45 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (919641/5000000 : ℝ)) (Y := (4083351/5000000 : ℝ)) 45 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (233237/2500000 : ℝ)) (Y := (1813467/2000000 : ℝ)) 45 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (771813/5000000 : ℝ)) (Y := (8461177/10000000 : ℝ)) 45 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_45_47 : ∀ p : ℝ, 32 ≤ p → (45 : ℝ) ≤ p → p ≤ (47 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (373/1000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (45 : ℝ)) (β := (47 : ℝ)) (tlo := (492357/500000 : ℝ)) (thia := (196943/200000 : ℝ)) (thib := (985361/1000000 : ℝ)) (D := (7496349507/1000000000000 : ℝ)) (δ := (3807/1000000 : ℝ)) (h := (99206349507/1000000000000 : ℝ)) (q := (373/1000 : ℝ)) (s1 := (19599/10000 : ℝ)) (τ1 := (241/250 : ℝ)) (σ1 := (9959/10000 : ℝ)) (n1 := (2299/2500 : ℝ)) (A1 := (554/625 : ℝ)) (s2 := (4903/2500 : ℝ)) (τ2 := (4829/5000 : ℝ)) (σ2 := (4977/5000 : ℝ)) (n2 := (576/625 : ℝ)) (A2 := (8883/10000 : ℝ)) (U2 := (2201/2000 : ℝ)) (B2 := (18047/10000 : ℝ)) (Af := (10571/10000 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (492357/500000 : ℝ)) (by norm_num) 1 45 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (196943/200000 : ℝ)) (by norm_num) (by norm_num) 1 45 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (985361/1000000 : ℝ)) (by norm_num) (by norm_num) 1 47 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1784927/10000000 : ℝ)) (Y := (8244027/10000000 : ℝ)) 47 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8244027/10000000 : ℝ)) (Y := (1784927/10000000 : ℝ)) 47 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (111001/625000 : ℝ)) (Y := (8228539/10000000 : ℝ)) 47 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1948491/10000000 : ℝ)) (Y := (2012931/2500000 : ℝ)) 47 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (2012931/2500000 : ℝ)) (Y := (1948491/10000000 : ℝ)) 47 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (886703/5000000 : ℝ)) (Y := (8232029/10000000 : ℝ)) 47 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (225387/2500000 : ℝ)) (Y := (1820033/2000000 : ℝ)) 47 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (754559/5000000 : ℝ)) (Y := (849701/1000000 : ℝ)) 47 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

theorem sub_47_50 : ∀ p : ℝ, 32 ≤ p → (47 : ℝ) ≤ p → p ≤ (50 : ℝ) → ∀ X : Triple, coarseBox X →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (373/1000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) → finalBox X :=
  slab_generic (α := (47 : ℝ)) (β := (50 : ℝ)) (tlo := (12317/12500 : ℝ)) (thia := (985361/1000000 : ℝ)) (thib := (986233/1000000 : ℝ)) (D := (1787700683/250000000000 : ℝ)) (δ := (3629/1000000 : ℝ)) (h := (23746200683/250000000000 : ℝ)) (q := (373/1000 : ℝ)) (s1 := (1226/625 : ℝ)) (τ1 := (9653/10000 : ℝ)) (σ1 := (9963/10000 : ℝ)) (n1 := (9199/10000 : ℝ)) (A1 := (8889/10000 : ℝ)) (s2 := (19629/10000 : ℝ)) (τ2 := (967/1000 : ℝ)) (σ2 := (9959/10000 : ℝ)) (n2 := (9217/10000 : ℝ)) (A2 := (4453/5000 : ℝ)) (U2 := (11029/10000 : ℝ)) (B2 := (3617/2000 : ℝ)) (Af := (5311/5000 : ℝ))
    (by norm_num)
    (by norm_num)
    (by have h := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (12317/12500 : ℝ)) (by norm_num) 1 47 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (985361/1000000 : ℝ)) (by norm_num) (by norm_num) 1 47 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (986233/1000000 : ℝ)) (by norm_num) (by norm_num) 1 50 (by norm_num) (by norm_num); convert h using 2; norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1710469/10000000 : ℝ)) (Y := (8308191/10000000 : ℝ)) 50 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (8308191/10000000 : ℝ)) (Y := (1710469/10000000 : ℝ)) 50 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1801417/10000000 : ℝ)) (Y := (4103327/5000000 : ℝ)) 50 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_lt (X := (1867771/10000000 : ℝ)) (Y := (25447/31250 : ℝ)) 50 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (fun p h0 h1 ↦ cert_lt (X := (25447/31250 : ℝ)) (Y := (1867771/10000000 : ℝ)) 50 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (1797443/10000000 : ℝ)) (Y := (2052457/2500000 : ℝ)) 50 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (457493/5000000 : ℝ)) (Y := (567939/625000 : ℝ)) 50 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (fun p h0 h1 ↦ cert_le (X := (381459/2500000 : ℝ)) (Y := (84807/100000 : ℝ)) 50 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) p h0 (h1.trans (by norm_num)))
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)

/-! ## The eight slabs and the combined statement -/

/-- Localization on the slab `[32, 33]` with `q = 3851/10000`. -/
theorem slab_32_33 : ∀ p : ℝ, 32 ≤ p → p ≤ 33 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3851/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  have h32 : (32 : ℝ) ≤ p := by linarith
  rcases le_total p (129/4 : ℝ) with c0 | c0
  · exact sub_32_129_4 p h32 (by linarith) c0 X hB hS (by linarith) hG
  rcases le_total p (65/2 : ℝ) with c1 | c1
  · exact sub_129_4_65_2 p h32 (by linarith) c1 X hB hS (by linarith) hG
  rcases le_total p (131/4 : ℝ) with c2 | c2
  · exact sub_65_2_131_4 p h32 (by linarith) c2 X hB hS (by linarith) hG
  exact sub_131_4_33 p h32 (by linarith) (by linarith) X hB hS (by linarith) hG

/-- Localization on the slab `[33, 34]` with `q = 3839/10000`. -/
theorem slab_33_34 : ∀ p : ℝ, 33 ≤ p → p ≤ 34 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3839/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  have h32 : (32 : ℝ) ≤ p := by linarith
  rcases le_total p (67/2 : ℝ) with c0 | c0
  · exact sub_33_67_2 p h32 (by linarith) c0 X hB hS (by linarith) hG
  exact sub_67_2_34 p h32 (by linarith) (by linarith) X hB hS (by linarith) hG

/-- Localization on the slab `[34, 36]` with `q = 3827/10000`. -/
theorem slab_34_36 : ∀ p : ℝ, 34 ≤ p → p ≤ 36 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3827/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  have h32 : (32 : ℝ) ≤ p := by linarith
  rcases le_total p (35 : ℝ) with c0 | c0
  · exact sub_34_35 p h32 (by linarith) c0 X hB hS (by linarith) hG
  rcases le_total p (71/2 : ℝ) with c1 | c1
  · exact sub_35_71_2 p h32 (by linarith) c1 X hB hS (by linarith) hG
  exact sub_71_2_36 p h32 (by linarith) (by linarith) X hB hS (by linarith) hG

/-- Localization on the slab `[36, 38]` with `q = 3806/10000`. -/
theorem slab_36_38 : ∀ p : ℝ, 36 ≤ p → p ≤ 38 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3806/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  have h32 : (32 : ℝ) ≤ p := by linarith
  rcases le_total p (37 : ℝ) with c0 | c0
  · exact sub_36_37 p h32 (by linarith) c0 X hB hS (by linarith) hG
  exact sub_37_38 p h32 (by linarith) (by linarith) X hB hS (by linarith) hG

/-- Localization on the slab `[38, 40]` with `q = 3786/10000`. -/
theorem slab_38_40 : ∀ p : ℝ, 38 ≤ p → p ≤ 40 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3786/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  have h32 : (32 : ℝ) ≤ p := by linarith
  exact sub_38_40 p h32 (by linarith) (by linarith) X hB hS (by linarith) hG

/-- Localization on the slab `[40, 42]` with `q = 37682/100000`. -/
theorem slab_40_42 : ∀ p : ℝ, 40 ≤ p → p ≤ 42 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (37682/100000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  have h32 : (32 : ℝ) ≤ p := by linarith
  exact sub_40_42 p h32 (by linarith) (by linarith) X hB hS (by linarith) hG

/-- Localization on the slab `[42, 45]` with `q = 3752/10000`. -/
theorem slab_42_45 : ∀ p : ℝ, 42 ≤ p → p ≤ 45 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3752/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  have h32 : (32 : ℝ) ≤ p := by linarith
  exact sub_42_45 p h32 (by linarith) (by linarith) X hB hS (by linarith) hG

/-- Localization on the slab `[45, 50]` with `q = 3730/10000`. -/
theorem slab_45_50 : ∀ p : ℝ, 45 ≤ p → p ≤ 50 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * (3730/10000 : ℝ) →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  have h32 : (32 : ℝ) ≤ p := by linarith
  rcases le_total p (47 : ℝ) with c0 | c0
  · exact sub_45_47 p h32 (by linarith) c0 X hB hS (by linarith) hG
  exact sub_47_50 p h32 (by linarith) (by linarith) X hB hS (by linarith) hG

/-- Uniform localization on `[32, 50]`. -/
theorem contract32 : ∀ p : ℝ, 32 ≤ p → p ≤ 50 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * slabRadius p →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  intro p h1 h2 X hB hS hT hG
  unfold slabRadius at hT
  split_ifs at hT with c1 c2 c3 c4 c5 c6 c7
  · exact slab_32_33 p h1 c1 X hB hS (by norm_num at hT ⊢; linarith) hG
  · exact slab_33_34 p (le_of_lt (not_le.1 c1)) c2 X hB hS (by norm_num at hT ⊢; linarith) hG
  · exact slab_34_36 p (le_of_lt (not_le.1 c2)) c3 X hB hS (by norm_num at hT ⊢; linarith) hG
  · exact slab_36_38 p (le_of_lt (not_le.1 c3)) c4 X hB hS (by norm_num at hT ⊢; linarith) hG
  · exact slab_38_40 p (le_of_lt (not_le.1 c4)) c5 X hB hS (by norm_num at hT ⊢; linarith) hG
  · exact slab_40_42 p (le_of_lt (not_le.1 c5)) c6 X hB hS (by norm_num at hT ⊢; linarith) hG
  · exact slab_42_45 p (le_of_lt (not_le.1 c6)) c7 X hB hS (by norm_num at hT ⊢; linarith) hG
  · exact slab_45_50 p (le_of_lt (not_le.1 c7)) h2 X hB hS (by norm_num at hT ⊢; linarith) hG

end HlawkaSchatten.DiagonalCutoff32

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem solution : ∀ p : ℝ, 32 ≤ p → p ≤ 50 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * slabRadius p →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff32.contract32
