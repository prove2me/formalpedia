-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.coarse_failure_window24
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:19:55.446512+00:00
-- url     : https://prove2.me/submissions/82558d11-10a3-4ae7-878f-c8d6126f1062

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Jensen
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Mathlib.Topology.Order.Compact

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction


/- Adapted from @bwdaugherty's accepted cutoff-32 contribution,
   submission d75400b0-5a0e-4167-8192-7fd299469c2e (2026-10-16),
   https://prove2.me/theorems/4e05427b-74d9-4e61-8d14-a52384a5ca10 .
   Public Prove2Me contribution under Apache-2.0; see sources/NOTICE.md.
   These generic lemmas do not assume p >= 32. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

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


end HlawkaSchatten.DiagonalRealBundle


/- Adapted from Yuxuan Xu's accepted cutoff-21 scalar proofs,
   submissions e696f6e8-38ad-49b3-b319-6be8f8688015 and
   9fd8db6a-6c52-470e-80a4-5fd66bab17f7, with the exponent cutoff
   changed to 16 and the resulting inequalities checked afresh. -/
open HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalRealBundle


/- Pair-tail bounds from Section 3 of the cutoff-16 paper. The finite
   numerical premise is an integer-power rational inequality, not an
   assumption that an external checker succeeded. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff16Scalar

theorem two_tail_norm_bound (m : ℕ) (hm : 1 ≤ m)
    {p S y1 y2 rho cap eps : ℝ}
    (hp : (m : ℝ) ≤ p) (hS : 0 ≤ S) (hScap : S ≤ cap) (hcap : 0 < cap)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (heps : 0 ≤ eps)
    (hy1 : |y1| ≤ rho * S) (hy2 : |y2| ≤ rho * S)
    (hcert : 2 * rho ^ m * cap ≤ (m : ℝ) * eps) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + eps := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 : 1 ≤ p := hm1.trans hp
  have hp0 : 0 < p := by linarith
  rcases eq_or_lt_of_le hS with hS0 | hSpos
  · have hzero : S = 0 := hS0.symm
    subst S
    have hy10 : y1 = 0 := abs_nonpos_iff.mp (by simpa using hy1)
    have hy20 : y2 = 0 := abs_nonpos_iff.mp (by simpa using hy2)
    subst y1 y2
    simpa [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')] using heps
  · rw [abs_of_pos hSpos]
    have hpow : rho ^ p ≤ rho ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hrho hrho1 (by positivity) hp
    have hy (y : ℝ) (hy : |y| ≤ rho * S) :
        |y| ^ p ≤ rho ^ m * S ^ p := by
      calc
        _ ≤ (rho * S) ^ p := Real.rpow_le_rpow (abs_nonneg _) hy hp0.le
        _ = rho ^ p * S ^ p := Real.mul_rpow hrho hSpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
    have hnum : 2 * rho ^ m ≤ p * (eps / S) := by
      have h1 : 2 * rho ^ m ≤ (m : ℝ) * eps / cap := (le_div_iff₀ hcap).2 hcert
      have h2 : eps / cap ≤ eps / S := div_le_div_of_nonneg_left heps hSpos hScap
      have h3 := mul_le_mul hp h2 (div_nonneg heps hcap.le) (by positivity : (0 : ℝ) ≤ p)
      calc
        _ ≤ (m : ℝ) * eps / cap := h1
        _ = (m : ℝ) * (eps / cap) := by ring
        _ ≤ p * (eps / S) := h3
    have hbern : 1 + p * (eps / S) ≤ (1 + eps / S) ^ p :=
      one_add_mul_self_le_rpow_one_add (by have := div_nonneg heps hSpos.le; linarith) hp1
    have heq : (S + eps) ^ p = S ^ p * (1 + eps / S) ^ p := by
      rw [← Real.mul_rpow hSpos.le (by positivity)]
      congr 1
      field_simp
    have h1 := hy y1 hy1
    have h2 := hy y2 hy2
    have h3 := mul_le_mul_of_nonneg_right hnum (show 0 ≤ S ^ p by positivity)
    have h4 := mul_le_mul_of_nonneg_left hbern (show 0 ≤ S ^ p by positivity)
    have hsum : S ^ p + |y1| ^ p + |y2| ^ p ≤ (S + eps) ^ p := by
      rw [heq]
      nlinarith
    calc
      _ ≤ ((S + eps) ^ p) ^ (1 / p) := Real.rpow_le_rpow (by positivity) hsum (by positivity)
      _ = S + eps := by rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne']

theorem half_tail16 {p S y1 y2 : ℝ} (hp : 16 ≤ p)
    (hS : 0 ≤ S) (hS3 : S ≤ 3) (hy1 : |y1| ≤ S / 2) (hy2 : |y2| ≤ S / 2) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000 := by
  apply two_tail_norm_bound 16 (by norm_num) hp hS hS3 (by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

end HlawkaSchatten.DiagonalCutoff16Scalar

/- This proves the upper-bound component of the paper's scalar targets
   directly, without assuming the stored interval-arithmetic reports. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace HlawkaSchatten.DiagonalCutoff16Scalar
open HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalRealBundle

theorem root_transfer_upper {m p B b A : ℝ} (hm : 0 < m) (hp : m ≤ p)
    (hB : 0 ≤ B) (hBb : B ≤ b) (hb : b ≤ A^m) (hA : 1 ≤ A) :
    B^(1/p) ≤ 1+(m/p)*(A-1) := by
  have hp0 : 0 < p := hm.trans_le hp
  have hmp : 0 ≤ m/p := div_nonneg hm.le hp0.le
  have hbase : 0 ≤ 1+(m/p)*(A-1) := by positivity
  have hratio : 1 ≤ p/m := (le_div_iff₀ hm).mpr (by simpa using hp)
  have hb0 := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ (m/p)*(A-1) by
      have hnon := mul_nonneg hmp (sub_nonneg.mpr hA)
      linarith) hratio
  have hroot : A ≤ (1+(m/p)*(A-1))^(p/m) := by
    convert hb0 using 1 <;> field_simp <;> ring
  have hpow : A^m ≤ (1+(m/p)*(A-1))^p := by
    have h := Real.rpow_le_rpow (by linarith : 0 ≤ A) hroot hm.le
    rw [← Real.rpow_mul hbase] at h
    convert h using 1 <;> field_simp
  calc
    _ ≤ ((1+(m/p)*(A-1))^p)^(1/p) :=
      Real.rpow_le_rpow hB (hBb.trans (hb.trans hpow)) (by positivity)
    _ = _ := by rw [one_div, Real.rpow_rpow_inv hbase hp0.ne']

theorem root_two_three_bounds {p : ℝ} (hp : 16 ≤ p) (hp32 : p ≤ 32) :
    1 + (693/1000 : ℝ) * (1/p) + (693/1000 : ℝ)^2 * (1/p)^2 / 2 ≤ (2 : ℝ)^(1/p) ∧
    (2 : ℝ)^(1/p) ≤ 1 + (71/100 : ℝ)/p ∧
    1 + 1/p ≤ (3 : ℝ)^(1/p) ∧
    (3 : ℝ)^(1/p) ≤ 3 := by
  have hp0 : 0 < p := by linarith
  have hu0 : 0 ≤ 1/p := by positivity
  have hu1 : 1/p ≤ 1 := (div_le_one hp0).mpr (by linarith)
  have hpu : p * (1/p) = 1 := mul_one_div_cancel hp0.ne'
  have hlog2 : (693/1000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hb : 1 + (693/1000 : ℝ) * (1/p) + (693/1000 : ℝ)^2 * (1/p)^2 / 2 ≤ (2 : ℝ)^(1/p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ (693/1000 : ℝ) * (1/p) by positivity)
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog2 hu0)
    nlinarith [he]
  have hbU : (2 : ℝ)^(1/p) ≤ 1 + (71/100 : ℝ)/p := by
    have h := root_transfer_upper (m := (16 : ℝ)) (B := (2 : ℝ))
      (b := (2 : ℝ)) (A := (1671/1600 : ℝ)) (by norm_num) hp
      (by norm_num) le_rfl (by norm_num [Real.rpow_natCast]) (by norm_num)
    convert h using 1 <;> ring
  have ha : 1 + 1/p ≤ (3 : ℝ)^(1/p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have h := Real.add_one_le_exp (Real.log 3 * (1/p))
    have hm := mul_le_mul_of_nonneg_right hlog3 hu0
    linarith
  have haU : (3 : ℝ)^(1/p) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hu1
    simpa using h
  exact ⟨hb,hbU,ha,haU⟩

theorem cyclicB_upper16 {p t : ℝ} (hp : 16 ≤ p)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : cyclicB p t ≤ 2 + 1/100000 := by
  have hy : |1-t| ≤ (2 : ℝ)/2 := abs_le.mpr ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩
  have h := half_tail16 (p := p) (S := 2) (y1 := 1-t) (y2 := 1-t)
    hp (by norm_num) (by norm_num) hy hy
  have he : (|2| ^ p + |1-t| ^ p + |1-t| ^ p : ℝ) = 2 * |1-t| ^ p + 2^p := by
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [he] at h
  exact h

theorem cyclicA_lower16 {p t : ℝ} (hp : 16 ≤ p)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) :
    (2 : ℝ)^(1/p) ≤ cyclicA p t ∧ t ≤ cyclicA p t := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  constructor
  · apply Real.rpow_le_rpow (by norm_num)
      (show (2 : ℝ) ≤ t^p+2 by linarith [Real.rpow_nonneg ht0 p]) (by positivity)
  · calc
      t = (t^p)^(1/p) := by rw [one_div, Real.rpow_rpow_inv ht0 hp0.ne']
      _ ≤ cyclicA p t := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

theorem cyclic_minimum_lower16 {p a b A t : ℝ} (hp : 16 ≤ p)
    (hb : 1 + (693/1000 : ℝ)*(1/p)+(693/1000 : ℝ)^2*(1/p)^2/2 ≤ b)
    (hbU : b ≤ 1+(71/100 : ℝ)/p) (ha : 1+1/p ≤ a) (haU : a ≤ 3)
    (hAb : b ≤ A) (hAt : t ≤ A) :
    2*p + 1/1000 ≤ 2*(p-1)*A + (2/3)*a*(2-t) := by
  have hp0 : 0 < p := by linarith
  set z := 1/p with hz
  have hbU' : b ≤ 1 + (71/100 : ℝ)*z := by
    simpa only [z, div_eq_mul_inv, one_mul] using hbU
  have hz0 : 0 ≤ z := by positivity
  have hz16 : z ≤ 1/16 := one_div_le_one_div_of_le (by norm_num) hp
  have hpz : p*z = 1 := mul_one_div_cancel hp0.ne'
  have hpz2 : p*z^2 = z := by
    calc
      _ = (p*z)*z := by ring
      _ = z := by rw [hpz]; ring
  have hz2 : z^2 ≤ (1/16 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1/16-z by linarith) (show 0 ≤ 1/16+z by linarith)]
  have hradial := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*(p-1) by linarith)
  have htail := mul_le_mul ha (show 1-(71/100 : ℝ)*z ≤ 2-b by linarith)
    (show 0 ≤ 1-(71/100 : ℝ)*z by linarith) (show 0 ≤ a by linarith)
  have hmin : 2*p+1/1000 ≤ 2*(p-1)*b+(2/3)*a*(2-b) := by
    nlinarith
  have hpm : 0 ≤ p-1 := by linarith
  have ha0 : 0 ≤ a := by linarith
  by_cases htb : t ≤ b
  · have h1 := mul_nonneg hpm (sub_nonneg.mpr hAb)
    have h2 := mul_nonneg ha0 (sub_nonneg.mpr htb)
    nlinarith
  · have h1 := mul_nonneg hpm (sub_nonneg.mpr hAt)
    have h2 := mul_nonneg (show 0 ≤ p-1-a/3 by linarith) (show 0 ≤ t-b by linarith)
    nlinarith

theorem cyclicRatio_upper16 {p t : ℝ} (hp : 16 ≤ p) (hp32 : p ≤ 32)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : cyclicRatio p t ≤ p/2 := by
  obtain ⟨hb,hbU,ha,haU⟩ := root_two_three_bounds hp hp32
  obtain ⟨hAb,hAt⟩ := cyclicA_lower16 hp ht
  have hB := cyclicB_upper16 hp ht
  have hm := cyclic_minimum_lower16 hp hb hbU ha haU hAb hAt
  have hp0 : 0 < p := by linarith
  have hu32 : (1/32 : ℝ) ≤ 1/p := one_div_le_one_div_of_le hp0 hp32
  have hB0 : 0 ≤ (2 : ℝ)^(1/p) := by positivity
  have hA : 1+1/64 ≤ cyclicA p t := by nlinarith [sq_nonneg (1/p)]
  have hden : 0 < 6*cyclicA p t-3*cyclicB p t := by linarith
  have hmB := mul_le_mul_of_nonneg_left hB hp0.le
  unfold cyclicRatio
  rw [abs_of_nonneg (show 0 ≤ 2-t by linarith [ht.2]), div_le_iff₀ hden]
  nlinarith

theorem cyclicConstant_upper16 {p : ℝ} (hp : 16 ≤ p) (hp32 : p ≤ 32) :
    cyclicConstant p ≤ p/2 := by
  unfold cyclicConstant
  apply csSup_le
  · exact ⟨cyclicRatio p 1, 1, by norm_num, rfl⟩
  · rintro y ⟨t,ht,rfl⟩
    exact cyclicRatio_upper16 hp hp32 ht

end HlawkaSchatten.DiagonalCutoff16Scalar


/- This is a kernel-checkable route to the remaining scalar lower bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace HlawkaSchatten.DiagonalCutoff16Scalar
open HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalRealBundle


theorem cyclic_denominator_positive16 {p t : ℝ} (hp : 16 ≤ p) (hp32 : p ≤ 32)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : 0 < 6*cyclicA p t-3*cyclicB p t := by
  obtain ⟨hb,_,_,_⟩ := root_two_three_bounds hp hp32
  have hAb := (cyclicA_lower16 hp ht).1
  have hB := cyclicB_upper16 hp ht
  have hp0 : 0 < p := by linarith
  have hu32 : (1/32 : ℝ) ≤ 1/p := one_div_le_one_div_of_le hp0 hp32
  have hA : 1+1/64 ≤ cyclicA p t := by nlinarith [sq_nonneg (1/p)]
  linarith

theorem cyclicB_lower_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  have h : (2 : ℝ)^p ≤ 2*|1-t|^p+2^p := by
    have := Real.rpow_nonneg (abs_nonneg (1-t)) p
    linarith
  calc
    (2 : ℝ) = (2^p)^(1/p) := by rw [one_div, Real.rpow_rpow_inv (by norm_num) hp.ne']
    _ ≤ cyclicB p t := Real.rpow_le_rpow (by positivity) h (by positivity)

theorem cyclicRatio_lower_endpoint {p alpha beta c t Aup aup : ℝ}
    (hp : 16 ≤ p) (hp32 : p ≤ 32) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hpb : p ≤ beta) (hc : 0 < c) (hcp : 1 ≤ 2*c*p)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hAup : 1 ≤ Aup) (haup : 1 ≤ aup)
    (hAend : t^alpha+2 ≤ Aup^alpha) (haend : (3 : ℝ) ≤ aup^alpha)
    (hH : 0 ≤ 3*(Aup-1)-(2-t)*(aup-1))
    (hcheck : 0 < 3-(2-t)+(alpha/beta)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) :
    c*p < cyclicRatio p t := by
  have hp0 : 0 < p := by linarith
  have htpos : 0 < t := by linarith
  have htp : t^p ≤ t^alpha := Real.rpow_le_rpow_of_exponent_ge htpos ht1 hap
  have hAp : cyclicA p t ≤ 1+(alpha/p)*(Aup-1) := by
    exact root_transfer_upper ha hap (by positivity) (by linarith) hAend hAup
  have hap' : (3 : ℝ)^(1/p) ≤ 1+(alpha/p)*(aup-1) :=
    root_transfer_upper ha hap (by norm_num) le_rfl haend haup
  have hB := cyclicB_lower_two (t := t) hp0
  have hden := cyclic_denominator_positive16 hp hp32 (show t ∈ Set.Icc (1/2 : ℝ) 2 by exact ⟨ht0,by linarith⟩)
  have hmono := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left ha.le hp0 hpb) hH
  have hpos : 0 < 3-(2-t)+(alpha/p)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hAp (show 0 ≤ 6*c*p-3 by linarith)
  have h2 := mul_le_mul_of_nonneg_left hap' (show 0 ≤ 2-t by linarith)
  have heq : (6*c*p-3)*(1+(alpha/p)*(Aup-1))+(2-t)*(1+(alpha/p)*(aup-1)) =
      6*c*p-(3-(2-t)+(alpha/p)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) := by
    field_simp
    ring
  have h3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*c*p by positivity)
  unfold cyclicRatio
  rw [abs_of_nonneg (show 0 ≤ 2-t by linarith), lt_div_iff₀ hden]
  nlinarith

theorem cyclicConstant_lower_endpoint {p alpha beta c t Aup aup : ℝ}
    (hp : 16 ≤ p) (hp32 : p ≤ 32) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hpb : p ≤ beta) (hc : 0 < c) (hcp : 1 ≤ 2*c*p)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hAup : 1 ≤ Aup) (haup : 1 ≤ aup)
    (hAend : t^alpha+2 ≤ Aup^alpha) (haend : (3 : ℝ) ≤ aup^alpha)
    (hH : 0 ≤ 3*(Aup-1)-(2-t)*(aup-1))
    (hcheck : 0 < 3-(2-t)+(alpha/beta)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) :
    c*p < cyclicConstant p := by
  have hratio := cyclicRatio_lower_endpoint hp hp32 ha hap hpb hc hcp ht0 ht1 hAup haup hAend haend hH hcheck
  have hbounded : BddAbove (cyclicRatio p '' Set.Icc (1/2 : ℝ) 2) := by
    refine ⟨p/2, ?_⟩
    rintro y ⟨s,hs,rfl⟩
    exact cyclicRatio_upper16 hp hp32 hs
  have ht : t ∈ Set.Icc (1/2 : ℝ) 2 := ⟨ht0,by linarith⟩
  exact hratio.trans_le (le_csSup hbounded (Set.mem_image_of_mem (cyclicRatio p) ht))

end HlawkaSchatten.DiagonalCutoff16Scalar



/- Bernoulli envelope transport, generalized from accepted submission 6ad9b901-e3db-45c8-84cd-c4345b3b35df (Yuxuan Xu, Apache-2.0) to real lower endpoints. -/
open HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff16Scalar
theorem bernoulli_scale (m : ℝ) (hm : 1 ≤ m) {p d : ℝ}
    (hp : m ≤ p) (hd : 0 ≤ d) (hdm : d < m) :
    (1-d/m)^m ≤ (1-d/p)^p := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hp0 : 0 < p := hm0.trans_le hp
  have hbase : 0 ≤ 1-d/p := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have he : (1 : ℝ) ≤ p/m := (le_div_iff₀ hm0).mpr (by simpa using hp)
  have hs : -1 ≤ -d/p := by
    have h := (div_le_one hp0).mpr (show d ≤ p by linarith)
    simpa only [neg_div] using neg_le_neg h
  have hb := one_add_mul_self_le_rpow_one_add hs he
  have hroot : 1-d/m ≤ (1-d/p)^(p/m) := by
    convert hb using 1 <;> field_simp <;> ring
  calc
    _ ≤ ((1-d/p)^(p/m))^m := Real.rpow_le_rpow
      (by apply sub_nonneg.mpr; exact (div_le_one hm0).mpr hdm.le) hroot hm0.le
    _ = (1-d/p)^p := by
      rw [← Real.rpow_mul hbase]
      congr 1
      field_simp

theorem envelope_linear_of_certificate (m : ℝ) (hm : 1 ≤ m)
    {p q c : ℝ} (hp : m ≤ p) (hq : 0 ≤ q) (hq1 : q < 1) (hc : 0 < c)
    (hdm : (1-q)/(2*c) < m)
    (hcert : (1+q^m)/2 < (1-((1-q)/(2*c))/m)^m) :
    scalarEnvelope p q < c*p := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hp0 : 0 < p := hm0.trans_le hp
  set d := (1-q)/(2*c) with hd_def
  have hd : 0 ≤ d := div_nonneg (by linarith) (by positivity)
  have hscale := bernoulli_scale m hm hp hd hdm
  have hqpow : q^p ≤ q^m := by
    exact Real.rpow_le_rpow_of_exponent_ge' hq hq1.le (by positivity) hp
  have hg0 : 0 ≤ scalarEnvelopeRoot p q := Real.rpow_nonneg (by positivity) _
  have hgpow : scalarEnvelopeRoot p q ^ p = (1+q^p)/2 := by
    unfold scalarEnvelopeRoot
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hb0 : 0 ≤ 1-d/p := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have hpow : scalarEnvelopeRoot p q ^ p < (1-d/p)^p := by
    rw [hgpow]
    exact (show (1+q^p)/2 < (1-d/m)^m by linarith).trans_le hscale
  have hg : scalarEnvelopeRoot p q < 1-d/p :=
    (Real.rpow_lt_rpow_iff hg0 hb0 hp0).mp hpow
  have hgap : 0 < 2*(1-scalarEnvelopeRoot p q) := by
    have := div_nonneg hd hp0.le
    linarith
  have hdp : d < p*(1-scalarEnvelopeRoot p q) := by
    have ht : d/p < 1-scalarEnvelopeRoot p q := by linarith
    have hm := (div_lt_iff₀ hp0).mp ht
    simpa only [mul_comm] using hm
  have hmul := mul_lt_mul_of_pos_left hdp (show 0 < 2*c by positivity)
  have heq : 2*c*d = 1-q := by rw [hd_def]; field_simp
  unfold scalarEnvelope
  apply (div_lt_iff₀ hgap).mpr
  nlinarith

end HlawkaSchatten.DiagonalCutoff16Scalar

/- Finite scalar certificates transported by Bernoulli.
Every rational power comparison is proved exactly by Lean. -/
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalCutoff16Scalar
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
namespace HlawkaSchatten.DiagonalCutoff16

theorem lower_w024_000 (p : ℝ) (hpa : (20 : ℝ) ≤ p) (hpb : p ≤ (321/16 : ℝ)) :
    (1741/4000 : ℝ)*p < cyclicConstant p := by

  have ht : (846494369/1000000000 : ℝ) ^ (20 : ℝ) ≤ (3568465229/100000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (846494369/1000000000 : ℝ)) (X := (3568465229/100000000000 : ℝ)) (by norm_num) (by norm_num) 20 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (203568465229/100000000000 : ℝ) ≤ (259045190689/250000000000 : ℝ) ^ (20 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (259045190689/250000000000 : ℝ)) (X := (203568465229/100000000000 : ℝ)) (by norm_num) 20 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (132058413569/125000000000 : ℝ) ^ (20 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (132058413569/125000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 20 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply cyclicConstant_lower_endpoint (alpha := (20 : ℝ)) (beta := (321/16 : ℝ))
    (t := (846494369/1000000000 : ℝ)) (Aup := (259045190689/250000000000 : ℝ)) (aup := (132058413569/125000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w024_001 (p : ℝ) (hpa : (321/16 : ℝ) ≤ p) (hpb : p ≤ (161/8 : ℝ)) :
    (1741/4000 : ℝ)*p < cyclicConstant p := by

  have ht : (846494369/1000000000 : ℝ) ^ (321/16 : ℝ) ≤ (17657449721/500000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (846494369/1000000000 : ℝ)) (X := (17657449721/500000000000 : ℝ)) (by norm_num) (by norm_num) 321 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (1017657449721/500000000000 : ℝ) ≤ (1036056660769/1000000000000 : ℝ) ^ (321/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1036056660769/1000000000000 : ℝ)) (X := (1017657449721/500000000000 : ℝ)) (by norm_num) 321 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (264071634433/250000000000 : ℝ) ^ (321/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (264071634433/250000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 321 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply cyclicConstant_lower_endpoint (alpha := (321/16 : ℝ)) (beta := (161/8 : ℝ))
    (t := (846494369/1000000000 : ℝ)) (Aup := (1036056660769/1000000000000 : ℝ)) (aup := (264071634433/250000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w024_002 (p : ℝ) (hpa : (161/8 : ℝ) ≤ p) (hpb : p ≤ (81/4 : ℝ)) :
    (1741/4000 : ℝ)*p < cyclicConstant p := by

  have ht : (846494369/1000000000 : ℝ) ^ (161/8 : ℝ) ≤ (17474488927/500000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (846494369/1000000000 : ℝ)) (X := (17474488927/500000000000 : ℝ)) (by norm_num) (by norm_num) 161 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (1017474488927/500000000000 : ℝ) ≤ (517966719771/500000000000 : ℝ) ^ (161/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (517966719771/500000000000 : ℝ)) (X := (1017474488927/500000000000 : ℝ)) (by norm_num) 161 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (211221384071/200000000000 : ℝ) ^ (161/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (211221384071/200000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 161 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply cyclicConstant_lower_endpoint (alpha := (161/8 : ℝ)) (beta := (81/4 : ℝ))
    (t := (846494369/1000000000 : ℝ)) (Aup := (517966719771/500000000000 : ℝ)) (aup := (211221384071/200000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w024_003 (p : ℝ) (hpa : (81/4 : ℝ) ≤ p) (hpb : p ≤ (41/2 : ℝ)) :
    (1741/4000 : ℝ)*p < cyclicConstant p := by

  have ht : (846494369/1000000000 : ℝ) ^ (81/4 : ℝ) ≤ (1369138803/40000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (846494369/1000000000 : ℝ)) (X := (1369138803/40000000000 : ℝ)) (by norm_num) (by norm_num) 81 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (81369138803/40000000000 : ℝ) ≤ (1035689602287/1000000000000 : ℝ) ^ (81/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1035689602287/1000000000000 : ℝ)) (X := (81369138803/40000000000 : ℝ)) (by norm_num) 81 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (527875551033/500000000000 : ℝ) ^ (81/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (527875551033/500000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply cyclicConstant_lower_endpoint (alpha := (81/4 : ℝ)) (beta := (41/2 : ℝ))
    (t := (846494369/1000000000 : ℝ)) (Aup := (1035689602287/1000000000000 : ℝ)) (aup := (527875551033/500000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w024_004 (p : ℝ) (hpa : (41/2 : ℝ) ≤ p) (hpb : p ≤ (21 : ℝ)) :
    (1741/4000 : ℝ)*p < cyclicConstant p := by

  have ht : (846494369/1000000000 : ℝ) ^ (41/2 : ℝ) ≤ (4103963779/125000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (846494369/1000000000 : ℝ)) (X := (4103963779/125000000000 : ℝ)) (by norm_num) (by norm_num) 41 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (254103963779/125000000000 : ℝ) ≤ (517606047991/500000000000 : ℝ) ^ (41/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (517606047991/500000000000 : ℝ)) (X := (254103963779/125000000000 : ℝ)) (by norm_num) 41 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (21101056639/20000000000 : ℝ) ^ (41/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (21101056639/20000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply cyclicConstant_lower_endpoint (alpha := (41/2 : ℝ)) (beta := (21 : ℝ))
    (t := (846494369/1000000000 : ℝ)) (Aup := (517606047991/500000000000 : ℝ)) (aup := (21101056639/20000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem scalar_lower_w024 (p : ℝ) (hpa : (20 : ℝ) ≤ p) (hpb : p ≤ (21 : ℝ)) :
    (1741/4000 : ℝ)*p < cyclicConstant p := by

  by_cases h0 : p ≤ (321/16 : ℝ)
  · exact lower_w024_000 p (by linarith) h0

  by_cases h1 : p ≤ (161/8 : ℝ)
  · exact lower_w024_001 p (by linarith) h1

  by_cases h2 : p ≤ (81/4 : ℝ)
  · exact lower_w024_002 p (by linarith) h2

  by_cases h3 : p ≤ (41/2 : ℝ)
  · exact lower_w024_003 p (by linarith) h3

  exact lower_w024_004 p (by linarith) hpb

theorem envelope_w024 (p : ℝ) (hp : (20 : ℝ) ≤ p) :
    scalarEnvelope p (4071/10000 : ℝ) < (1741/4000 : ℝ)*p := by

  have hq : (4071/10000 : ℝ) ^ (20 : ℝ) ≤ (3127/200000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (4071/10000 : ℝ)) (X := (3127/200000000000 : ℝ)) (by norm_num) (by norm_num) 20 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hb : (500088319143/1000000000000 : ℝ) ≤ (168171/174100 : ℝ) ^ (20 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (168171/174100 : ℝ)) (X := (500088319143/1000000000000 : ℝ)) (by norm_num) 20 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply envelope_linear_of_certificate (20 : ℝ) (by norm_num) hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : (1-((1-(4071/10000 : ℝ))/(2*(1741/4000 : ℝ)))/(20 : ℝ) : ℝ) = (168171/174100 : ℝ) := by norm_num
  rw [he]
  linarith only [hq, hb]

end HlawkaSchatten.DiagonalCutoff16

/- Generic proofs reused from accepted Prove2Me submissions 4753aff4-c621-4df6-9535-63c865f87fd0 and de577b6b-0253-45ac-9b17-ccf002bb69a6. Original authors Ezzeri Esa, bwdaugherty and Yuxuan Xu; Apache-2.0. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalFailureBundle
def coordinateBox (ell u v w : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w
end HlawkaSchatten.DiagonalFailureBundle

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Relabeling and normalization of a strict counterexample -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

/-- The deficit expressed in terms of gap functions. -/
theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

/-- The deficit is symmetric in the first two arguments. -/
theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

/-- The deficit is symmetric in the last two arguments. -/
theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

/-- Flipping to `(-(x+y+z), y, z)` exchanges the total norm with a singleton norm. -/
theorem lpNorm_flip_total (p : ℝ) (x y z : ι → ℝ) :
    lpNorm p (-(x + y + z) + y + z) = lpNorm p x := by
  have h : -(x + y + z) + y + z = -x := by abel
  rw [h, lpNorm_neg]

/-- The deficit of `(-(x+y+z), y, z)` differs from that of `(x, y, z)` by
`(2K - 2)(N(x+y+z) - N(x))`. -/
theorem hlawkaDeficit_flip (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (-(x + y + z)) y z = hlawkaDeficit p K x y z +
      (2 * K - 2) * (lpNorm p (x + y + z) - lpNorm p x) := by
  have hxy : -(x + y + z) + y = -(x + z) := by abel
  have hxz : -(x + y + z) + z = -(x + y) := by abel
  unfold hlawkaDeficit
  rw [lpNorm_flip_total, hxy, hxz]
  simp only [lpNorm_neg]
  ring

/-- A failed inequality can be relabeled so that its total norm is largest. -/
theorem exists_failure_total_largest {p K : ℝ} (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hfail : hlawkaDeficit p K x y z < 0) :
    ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p u ≤ lpNorm p (u + v + w) ∧
      lpNorm p v ≤ lpNorm p (u + v + w) ∧
      lpNorm p w ≤ lpNorm p (u + v + w) := by
  have hmax : ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p v ≤ lpNorm p u ∧ lpNorm p w ≤ lpNorm p u := by
    rcases le_total (lpNorm p y) (lpNorm p x) with hxy | hxy
    · rcases le_total (lpNorm p z) (lpNorm p x) with hxz | hxz
      · exact ⟨x, y, z, hfail, hxy, hxz⟩
      · refine ⟨z, x, y, ?_, hxz, hxy.trans hxz⟩
        rw [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]
        exact hfail
    · rcases le_total (lpNorm p z) (lpNorm p y) with hyz | hyz
      · refine ⟨y, x, z, ?_, hxy, hyz⟩
        rw [hlawkaDeficit_swap_left]
        exact hfail
      · refine ⟨z, x, y, ?_, hxy.trans hyz, hyz⟩
        rw [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]
        exact hfail
  obtain ⟨u, v, w, hf, hv, hw⟩ := hmax
  rcases le_total (lpNorm p u) (lpNorm p (u + v + w)) with hu | hu
  · exact ⟨u, v, w, hf, hu, hv.trans hu, hw.trans hu⟩
  · refine ⟨-(u + v + w), v, w, ?_, ?_, ?_, ?_⟩
    · rw [hlawkaDeficit_flip]
      have hprod := mul_nonpos_of_nonneg_of_nonpos
        (by linarith : 0 ≤ 2 * K - 2) (sub_nonpos.mpr hu)
      linarith
    · simpa only [lpNorm_neg, lpNorm_flip_total] using hu
    · simpa only [lpNorm_flip_total] using hv
    · simpa only [lpNorm_flip_total] using hw

/-- The deficit scales linearly with `|c|` under scalar multiplication. -/
theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

/-- A failure triple has positive norm sum. -/
theorem failure_sum_pos {p K : ℝ} (hp : 0 < p) (x y z : ι → ℝ)
    (hfail : hlawkaDeficit p K x y z < 0) :
    0 < lpNorm p x + lpNorm p y + lpNorm p z := by
  have hx := lpNorm_nonneg p x
  have hy := lpNorm_nonneg p y
  have hz := lpNorm_nonneg p z
  by_contra hn
  have hnx : lpNorm p x = 0 := by linarith
  have hny : lpNorm p y = 0 := by linarith
  have hnz : lpNorm p z = 0 := by linarith
  have hx0 := (lpNorm_eq_zero_iff hp x).mp hnx
  have hy0 := (lpNorm_eq_zero_iff hp y).mp hny
  have hz0 := (lpNorm_eq_zero_iff hp z).mp hnz
  subst x; subst y; subst z
  simp [hlawkaDeficit, lpNorm_zero hp] at hfail

/-- Normalize after relabeling. No positivity of a pair-gap denominator is assumed. -/
theorem exists_normalized_failure {p K : ℝ} (hp : 0 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hfail : hlawkaDeficit p K x y z < 0) :
    ∃ u v w : ι → ℝ, hlawkaDeficit p K u v w < 0 ∧
      lpNorm p u + lpNorm p v + lpNorm p w = 1 ∧
      lpNorm p u ≤ lpNorm p (u + v + w) ∧
      lpNorm p v ≤ lpNorm p (u + v + w) ∧
      lpNorm p w ≤ lpNorm p (u + v + w) := by
  obtain ⟨u, v, w, hf, hu, hv, hw⟩ := exists_failure_total_largest hK x y z hfail
  let s := lpNorm p u + lpNorm p v + lpNorm p w
  have hs : 0 < s := failure_sum_pos hp u v w hf
  refine ⟨s⁻¹ • u, s⁻¹ • v, s⁻¹ • w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlawkaDeficit_smul hp, abs_of_pos (inv_pos.mpr hs)]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hs) hf
  · simp only [lpNorm_smul hp, abs_of_pos (inv_pos.mpr hs)]
    rw [← mul_add, ← mul_add]
    exact inv_mul_cancel₀ hs.ne'
  all_goals
    simp only [← smul_add, lpNorm_smul hp, abs_of_pos (inv_pos.mpr hs)]
  · exact mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hs.le)
  · exact mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hs.le)
  · exact mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hs.le)

end HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

/-- The power sum is nonneg. -/
theorem powerSum_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ powerSum p v :=
  Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p

/-- The power sum equals the `p`-norm raised to `p`. -/
theorem powerSum_eq_lpNorm_rpow {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v = lpNorm p v ^ p := by
  rw [lpNorm_rpow hp]
  rfl

/-- The power sum is strictly positive for nonzero `v`. -/
theorem powerSum_pos {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < powerSum p v := by
  rw [powerSum_eq_lpNorm_rpow hp]
  exact Real.rpow_pos_of_pos (lpNorm_pos hp hv) p

omit [Fintype ι] in
private theorem abs_rpow_mul_sq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x| ^ q * x ^ 2 = |x| ^ (q + 2) := by
  by_cases hx : x = 0
  · simp [hx, hq.ne', show q + 2 ≠ 0 by linarith]
  · rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add (abs_pos.mpr hx)]

/-- The quadratic form at `h = v` equals the power sum. -/
theorem powerQuad_self {p : ℝ} (hp : 2 < p) (v : ι → ℝ) :
    powerQuad p v v = powerSum p v := by
  unfold powerQuad powerSum
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_add_cancel] using abs_rpow_mul_sq (by linarith : 0 < p - 2) (v i)

/-- The power residual decomposes into radial and tangential parts. -/
theorem powerResidual_eq {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerResidual p v h a = powerQuad p v h - 2 * a * powerPair p v h + a ^ 2 * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerResidual, powerQuad, powerPair, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The optimal radial coefficient minimizes the residual. -/
theorem powerResidual_radial {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) :
    powerResidual p v h (radialCoefficient p v h) =
      powerQuad p v h - powerPair p v h ^ 2 / powerSum p v := by
  rw [powerResidual_eq hp, radialCoefficient]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring

/-- The residual at the optimal coefficient is minimal. -/
theorem powerResidual_min {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    powerResidual p v h (radialCoefficient p v h) ≤ powerResidual p v h a := by
  have hS := powerSum_pos (by linarith : 0 < p) hv
  rw [powerResidual_radial hp v h hv, powerResidual_eq hp]
  have hn := mul_nonneg hS.le (sq_nonneg (a - powerPair p v h / powerSum p v))
  have hmul : powerSum p v * (powerPair p v h / powerSum p v) = powerPair p v h :=
    mul_div_cancel₀ _ hS.ne'
  have hmul2 : powerSum p v * (powerPair p v h / powerSum p v) ^ 2 =
      powerPair p v h ^ 2 / powerSum p v := by field_simp
  nlinarith [congrArg (fun x : ℝ ↦ a * x) hmul]

/-- The power residual is nonneg. -/
theorem powerResidual_nonneg (p : ℝ) (v h : ι → ℝ) (a : ℝ) : 0 ≤ powerResidual p v h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (Real.rpow_nonneg (abs_nonneg (v i)) (p - 2)) (sq_nonneg (h i - a * v i))

/-- The norm Hessian is nonneg for `p ≥ 1`. -/
theorem normHessian_nonneg {p : ℝ} (hp : 1 ≤ p) (v h : ι → ℝ) : 0 ≤ normHessian p v h :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (powerSum_nonneg p v) _))
    (powerResidual_nonneg p v h _)

/-- The norm Hessian is bounded by the power residual. -/
theorem normHessian_le_residual {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v h ≤ (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h a := by
  exact mul_le_mul_of_nonneg_left (powerResidual_min hp v h hv a)
    (mul_nonneg (by linarith) (Real.rpow_nonneg (powerSum_nonneg p v) _))

omit [Fintype ι] in
private theorem hasDerivAt_abs_power_slope {p : ℝ} (hp : 4 < p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ (p - 2) * x) ((p - 1) * |x| ^ (p - 2)) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p - 2)).mul (hasDerivAt_id x)
  have heq : ((p - 2) * |x| ^ (p - 2 - 2) * x) * x + |x| ^ (p - 2) * 1 =
      (p - 1) * |x| ^ (p - 2) := by
    have hh := abs_rpow_mul_sq (by linarith : 0 < p - 2 - 2) x
    have hcancel : p - 2 - 2 + 2 = p - 2 := by ring
    rw [hcancel] at hh
    nlinarith
  convert! h using 1
  simpa only [id_eq] using heq.symm

/-- Differentiability of the power sum along a line. -/
theorem hasDerivAt_powerSum_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerSum p (v + s • h))
      (p * powerPair p (v + t • h) h) t := by
  have hi (i : ι) : HasDerivAt (fun s : ℝ ↦ |v i + s * h i| ^ p)
      (p * |v i + t * h i| ^ (p - 2) * (v i + t * h i) * h i) t := by
    simpa only [one_mul, id_eq, Function.comp_def] using
      (hasDerivAt_abs_rpow _ hp).comp t (((hasDerivAt_id t).mul_const (h i)).const_add (v i))
  simpa only [powerSum, powerPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)

/-- Differentiability of the first-order form along a line. -/
theorem hasDerivAt_powerPair_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerPair p (v + s • h) h)
      ((p - 1) * powerQuad p (v + t • h) h) t := by
  have hi (i : ι) := ((hasDerivAt_abs_power_slope hp (v i + t * h i)).comp t
    (((hasDerivAt_id t).mul_const (h i)).const_add (v i))).mul_const (h i)
  simpa only [powerPair, powerQuad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    pow_two, mul_assoc, Function.comp_def, id_eq, one_mul] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)

/-- Differentiability of the `p`-norm along a line. -/
theorem hasDerivAt_lpNorm_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ lpNorm p (v + s • h)) (normSlope p (v + t • h) h) t := by
  have hp0 := zero_lt_one.trans hp
  have hh := (hasDerivAt_powerSum_line hp v h t).rpow_const (p := 1 / p)
    (Or.inl (powerSum_pos hp0 hv).ne')
  have he : p * powerPair p (v + t • h) h * (1 / p) * powerSum p (v + t • h) ^ (1 / p - 1) =
      normSlope p (v + t • h) h := by
    unfold normSlope
    field_simp
  convert hh using 1
  · rfl
  · exact he.symm

/-- Differentiability of the norm slope along a line. -/
theorem hasDerivAt_normSlope_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ normSlope p (v + s • h) h) (normHessian p (v + t • h) h) t := by
  have hp0 : 0 < p := by linarith
  have hS := powerSum_pos hp0 hv
  have hh := ((hasDerivAt_powerSum_line (by linarith) v h t).rpow_const (p := 1 / p - 1)
    (Or.inl hS.ne')).mul (hasDerivAt_powerPair_line hp v h t)
  have hpow : powerSum p (v + t • h) ^ (1 / p - 1 - 1) =
      powerSum p (v + t • h) ^ (1 / p - 1) / powerSum p (v + t • h) := by
    rw [Real.rpow_sub hS, Real.rpow_one]
  have he : (p * powerPair p (v + t • h) h * (1 / p - 1) *
      powerSum p (v + t • h) ^ (1 / p - 1 - 1)) * powerPair p (v + t • h) h +
      powerSum p (v + t • h) ^ (1 / p - 1) * ((p - 1) * powerQuad p (v + t • h) h) =
        normHessian p (v + t • h) h := by
    rw [normHessian, powerResidual_radial (by linarith) _ _ hv, hpow]
    field_simp
    ring
  rwa [he] at hh

/-- The first-order form with a radial correction. -/
theorem powerPair_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerPair p v (h - a • v) = powerPair p v h - a * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerPair, powerQuad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The norm Hessian with a radial correction. -/
theorem normHessian_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v (h - a • v) = normHessian p v h := by
  simp only [normHessian, powerResidual_radial hp v _ hv, powerPair_sub_smul hp]
  congr 1
  have hquad : powerQuad p v (h - a • v) = powerResidual p v h a := rfl
  rw [hquad, powerResidual_eq hp]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring

/-- The `(p-1)/p`-th power of the power sum root. -/
theorem powerSum_root_pred {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v ^ (1 / p - 1) = (lpNorm p v ^ (p - 1))⁻¹ := by
  rw [powerSum_eq_lpNorm_rpow hp, ← Real.rpow_mul (lpNorm_nonneg p v),
    show p * (1 / p - 1) = -(p - 1) by field_simp; ring,
    Real.rpow_neg (lpNorm_nonneg p v)]

/-- The norm Hessian as a ratio of quadratic form to power sum. -/
theorem normHessian_eq_div {p : ℝ} (hp : 0 < p) (v h : ι → ℝ) :
    normHessian p v h = (p - 1) / lpNorm p v ^ (p - 1) *
      powerResidual p v h (radialCoefficient p v h) := by
  rw [normHessian, powerSum_root_pred hp]
  rfl

end HlawkaSchatten.DiagonalConstruction

/- Generic proofs reused from accepted Prove2Me submissions 4753aff4-c621-4df6-9535-63c865f87fd0 and de577b6b-0253-45ac-9b17-ccf002bb69a6. Original authors Ezzeri Esa, bwdaugherty and Yuxuan Xu; Apache-2.0. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction

private theorem weighted_jensen {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) (x y : ℝ) :
    (a + b) * f ((a * x + b * y) / (a + b)) ≤ a * f x + b * f y := by
  have h := hf.2 (Set.mem_univ x) (Set.mem_univ y)
    (div_nonneg ha hab.le) (div_nonneg hb hab.le)
    (show a / (a + b) + b / (a + b) = 1 by field_simp)
  simp only [smul_eq_mul] at h
  have he : a / (a + b) * x + b / (a + b) * y =
      (a * x + b * y) / (a + b) := by ring
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_left h hab.le
  have h1 : (a + b) * (a / (a + b)) = a := mul_div_cancel₀ a hab.ne'
  have h2 : (a + b) * (b / (a + b)) = b := mul_div_cancel₀ b hab.ne'
  simpa only [mul_add, ← mul_assoc, h1, h2] using hm

private theorem convex_chord {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {x z u : ℝ} (hxz : x < z) (hxu : x ≤ u) (huz : u ≤ z) :
    (z - x) * f u ≤ (z - u) * f x + (u - x) * f z := by
  have h := weighted_jensen hf (sub_nonneg.mpr huz) (sub_nonneg.mpr hxu)
    (by linarith : 0 < (z - u) + (u - x)) x z
  have he : ((z - u) * x + (u - x) * z) / ((z - u) + (u - x)) = u := by
    apply (div_eq_iff (by linarith : (z - u) + (u - x) ≠ 0)).mpr
    ring
  rw [he] at h
  convert h using 1
  ring

private theorem two_chords {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {x z u v A B a b : ℝ} (hxz : x < z)
    (hxu : x ≤ u) (huz : u ≤ z) (hxv : x ≤ v) (hvz : v ≤ z)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmass : A + B = a + b) (hmoment : A * u + B * v = a * x + b * z) :
    A * f u + B * f v ≤ a * f x + b * f z := by
  have hu := mul_le_mul_of_nonneg_left (convex_chord hf hxz hxu huz) hA
  have hv := mul_le_mul_of_nonneg_left (convex_chord hf hxz hxv hvz) hB
  have hleft : A * (z - u) + B * (z - v) = (z - x) * a := by
    linear_combination z * hmass - hmoment
  have hright : A * (u - x) + B * (v - x) = (z - x) * b := by
    linear_combination hmoment - x * hmass
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hxz)).mp
  calc
    (z - x) * (A * f u + B * f v) ≤
        (A * (z - u) + B * (z - v)) * f x +
          (A * (u - x) + B * (v - x)) * f z := by nlinarith
    _ = (z - x) * (a * f x + b * f z) := by rw [hleft, hright]; ring

/-- The weighted pair-sum functional. -/
noncomputable def weightedPairs (f : ℝ → ℝ) (a b c x y z : ℝ) : ℝ :=
  (a + b) * f ((a * x + b * y) / (a + b)) +
    (a + c) * f ((a * x + c * z) / (a + c)) +
    (b + c) * f ((b * y + c * z) / (b + c))

/-- The weighted singleton and total functional. -/
noncomputable def weightedTotal (f : ℝ → ℝ) (a b c x y z : ℝ) : ℝ :=
  a * f x + b * f y + c * f z +
    (a + b + c) * f ((a * x + b * y + c * z) / (a + b + c))

private theorem weighted_convex_ordered {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {a b c x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hxy : x ≤ y) (hyz : y ≤ z) :
    weightedPairs f a b c x y z ≤ weightedTotal f a b c x y z := by
  have hab : 0 < a + b := add_pos ha hb
  have hac : 0 < a + c := add_pos ha hc
  have hbc : 0 < b + c := add_pos hb hc
  have hS : 0 < a + b + c := add_pos hab hc
  let m := (a * x + b * y + c * z) / (a + b + c)
  have hm : (a + b + c) * m = a * x + b * y + c * z := by
    dsimp [m]
    field_simp
  have hxz := hxy.trans hyz
  rcases eq_or_lt_of_le hxz with heq | hlt
  · have hyeq : y = z := le_antisymm hyz (heq ▸ hxy)
    subst x
    subst y
    have hmean (A B : ℝ) (hAB : 0 < A + B) :
        (A * z + B * z) / (A + B) = z := by
      apply (div_eq_iff hAB.ne').mpr
      ring
    simp only [weightedPairs, weightedTotal, hmean a b hab, hmean a c hac,
      hmean b c hbc]
    have hall : (a * z + b * z + c * z) / (a + b + c) = z := by
      apply (div_eq_iff hS.ne').mpr
      ring
    rw [hall]
    ring_nf
    rfl
  have hxm : x < m := by
    apply (lt_div_iff₀ hS).mpr
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hxy), mul_pos hc (sub_pos.mpr hlt)]
  have hmz : m < z := by
    apply (div_lt_iff₀ hS).mpr
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hyz), mul_pos ha (sub_pos.mpr hlt)]
  by_cases hym : y ≤ m
  · have hmv : m ≤ (a * x + c * z) / (a + c) := by
      apply (le_div_iff₀ hac).mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hym)]
    have hvz : (a * x + c * z) / (a + c) ≤ z := by
      apply (div_le_iff₀ hac).mpr
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxz)]
    have hmw : m ≤ (b * y + c * z) / (b + c) := by
      apply (le_div_iff₀ hbc).mpr
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxm.le)]
    have hwz : (b * y + c * z) / (b + c) ≤ z := by
      apply (div_le_iff₀ hbc).mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hyz)]
    have htwo := two_chords hf hmz hmv hvz hmw hwz hac.le hbc.le
      (show (a + c) + (b + c) = (a + b + c) + c by ring)
      (show (a + c) * ((a * x + c * z) / (a + c)) +
        (b + c) * ((b * y + c * z) / (b + c)) =
          (a + b + c) * m + c * z by
        rw [mul_div_cancel₀ _ hac.ne', mul_div_cancel₀ _ hbc.ne', hm]
        ring)
    have hone := weighted_jensen hf ha.le hb.le hab x y
    dsimp only [weightedPairs, weightedTotal]
    change _ ≤ a * f x + b * f y + c * f z + (a + b + c) * f m
    linarith
  · have hmy : m ≤ y := le_of_not_ge hym
    have hxu : x ≤ (a * x + b * y) / (a + b) := by
      apply (le_div_iff₀ hab).mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hxy)]
    have hum : (a * x + b * y) / (a + b) ≤ m := by
      apply (div_le_iff₀ hab).mpr
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hmz.le)]
    have hxv : x ≤ (a * x + c * z) / (a + c) := by
      apply (le_div_iff₀ hac).mpr
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hxz)]
    have hvm : (a * x + c * z) / (a + c) ≤ m := by
      apply (div_le_iff₀ hac).mpr
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hmy)]
    have htwo := two_chords hf hxm hxu hum hxv hvm hab.le hac.le
      (show (a + b) + (a + c) = a + (a + b + c) by ring)
      (show (a + b) * ((a * x + b * y) / (a + b)) +
        (a + c) * ((a * x + c * z) / (a + c)) =
          a * x + (a + b + c) * m by
        rw [mul_div_cancel₀ _ hab.ne', mul_div_cancel₀ _ hac.ne', hm]
        ring)
    have hone := weighted_jensen hf hb.le hc.le hbc y z
    dsimp only [weightedPairs, weightedTotal]
    change _ ≤ a * f x + b * f y + c * f z + (a + b + c) * f m
    linarith

private theorem weightedPairs_swap12 (f : ℝ → ℝ) (a b c x y z : ℝ) :
    weightedPairs f a b c x y z = weightedPairs f b a c y x z := by
  unfold weightedPairs
  ac_rfl

private theorem weightedPairs_swap23 (f : ℝ → ℝ) (a b c x y z : ℝ) :
    weightedPairs f a b c x y z = weightedPairs f a c b x z y := by
  unfold weightedPairs
  ac_rfl

private theorem weightedTotal_swap12 (f : ℝ → ℝ) (a b c x y z : ℝ) :
    weightedTotal f a b c x y z = weightedTotal f b a c y x z := by
  unfold weightedTotal
  ac_rfl

private theorem weightedTotal_swap23 (f : ℝ → ℝ) (a b c x y z : ℝ) :
    weightedTotal f a b c x y z = weightedTotal f a c b x z y := by
  unfold weightedTotal
  ac_rfl

/-- Weighted scalar Hlawka for a convex real function and positive weights. -/
theorem weighted_convex_hlawka {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x y z : ℝ) :
    weightedPairs f a b c x y z ≤ weightedTotal f a b c x y z := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact weighted_convex_ordered hf ha hb hc hxy hyz
    · rcases le_total x z with hxz | hzx
      · rw [weightedPairs_swap23, weightedTotal_swap23]
        exact weighted_convex_ordered hf ha hc hb hxz hzy
      · rw [weightedPairs_swap23, weightedTotal_swap23,
          weightedPairs_swap12, weightedTotal_swap12]
        exact weighted_convex_ordered hf hc ha hb hzx hxy
  · rcases le_total x z with hxz | hzx
    · rw [weightedPairs_swap12, weightedTotal_swap12]
      exact weighted_convex_ordered hf hb ha hc hyx hxz
    · rcases le_total y z with hyz | hzy
      · rw [weightedPairs_swap12, weightedTotal_swap12,
          weightedPairs_swap23, weightedTotal_swap23]
        exact weighted_convex_ordered hf hb hc ha hyz hzx
      · rw [weightedPairs_swap12, weightedTotal_swap12,
          weightedPairs_swap23, weightedTotal_swap23,
          weightedPairs_swap12, weightedTotal_swap12]
        exact weighted_convex_ordered hf hc hb ha hzy hyx

end HlawkaSchatten.DiagonalConstruction
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
namespace HlawkaSchatten
/-- Convexity of the scalar power potential before its positive rescaling. -/
theorem convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have hImage : (norm : ℝ → ℝ) '' Set.univ = Set.Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact norm_nonneg x
    · intro hy
      have hy' : 0 ≤ y := by simpa only [Set.mem_Ici] using hy
      exact ⟨y, Set.mem_univ y, by simp [abs_of_nonneg hy']⟩
  have hOuter : ConvexOn ℝ ((norm : ℝ → ℝ) '' Set.univ) (fun y : ℝ ↦ y ^ p) := by
    rw [hImage]
    exact convexOn_rpow hp
  have hMono : MonotoneOn (fun y : ℝ ↦ y ^ p) ((norm : ℝ → ℝ) '' Set.univ) := by
    rw [hImage]
    exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos (zero_lt_one.trans_le hp)).monotoneOn
  convert hOuter.comp convexOn_univ_norm hMono using 1
  ext x
  simp only [Function.comp_apply, Real.norm_eq_abs]


end HlawkaSchatten
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The weighted scalar estimate for arbitrary coordinate triples

The weights are the three input norms. Applying the scalar convexity
inequality coordinate by coordinate yields the dimension-independent power
estimate used to confine a hypothetical counterexample.
-/

namespace HlawkaSchatten.DiagonalConstruction

/-- Pulling a positive weight out of `|x/a|^p`. -/
theorem weighted_abs_rpow_div {a : ℝ} (ha : 0 < a) (p x : ℝ) :
    a * |x / a| ^ p = |x| ^ p / a ^ (p - 1) := by
  rw [abs_div, abs_of_pos ha, Real.div_rpow (abs_nonneg x) ha.le,
    Real.rpow_sub ha, Real.rpow_one]
  field_simp

/-- `a^p / a^(p-1) = a` for `p > 1`. -/
theorem rpow_div_pred {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    a ^ p / a ^ (p - 1) = a := by
  by_cases h : a = 0
  · subst a
    simp [ne_of_gt (zero_lt_one.trans hp), ne_of_gt (sub_pos.mpr hp)]
  · have ha0 := lt_of_le_of_ne ha (Ne.symm h)
    rw [Real.rpow_sub ha0, Real.rpow_one]
    field_simp

/-- The weighted scalar power inequality for three positive weights. -/
theorem weighted_scalar_power {p a b c : ℝ} (hp : 1 < p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x y z : ℝ) :
    |x + y| ^ p / (a + b) ^ (p - 1) +
      |x + z| ^ p / (a + c) ^ (p - 1) +
      |y + z| ^ p / (b + c) ^ (p - 1) ≤
    |x| ^ p / a ^ (p - 1) + |y| ^ p / b ^ (p - 1) + |z| ^ p / c ^ (p - 1) +
      |x + y + z| ^ p / (a + b + c) ^ (p - 1) := by
  have h := weighted_convex_hlawka (convexOn_abs_rpow hp.le) ha hb hc
    (x / a) (y / b) (z / c)
  simp only [weightedPairs, weightedTotal,
    mul_div_cancel₀ _ ha.ne', mul_div_cancel₀ _ hb.ne', mul_div_cancel₀ _ hc.ne'] at h
  simpa only [weighted_abs_rpow_div ha, weighted_abs_rpow_div hb,
    weighted_abs_rpow_div hc, weighted_abs_rpow_div (add_pos ha hb),
    weighted_abs_rpow_div (add_pos ha hc), weighted_abs_rpow_div (add_pos hb hc),
    weighted_abs_rpow_div (add_pos (add_pos ha hb) hc)] using h

variable {ι : Type*} [Fintype ι]

/-- The weighted `p`-power inequality for nonzero coordinate triples. -/
theorem weighted_lp_power_of_ne {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    lpNorm p (x + y) ^ p / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      lpNorm p (x + z) ^ p / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      lpNorm p (y + z) ^ p / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    lpNorm p x + lpNorm p y + lpNorm p z +
      lpNorm p (x + y + z) ^ p / (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    weighted_scalar_power hp (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hy)
      (lpNorm_pos hp0 hz) (x i) (y i) (z i))
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Real.norm_eq_abs] at h
  change
    (∑ i, ‖(x + y) i‖ ^ p) / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      (∑ i, ‖(x + z) i‖ ^ p) / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      (∑ i, ‖(y + z) i‖ ^ p) / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    (∑ i, ‖x i‖ ^ p) / lpNorm p x ^ (p - 1) +
      (∑ i, ‖y i‖ ^ p) / lpNorm p y ^ (p - 1) +
      (∑ i, ‖z i‖ ^ p) / lpNorm p z ^ (p - 1) +
      (∑ i, ‖(x + y + z) i‖ ^ p) /
        (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) at h
  simpa only [← lpNorm_rpow hp0, rpow_div_pred hp (lpNorm_nonneg p x),
    rpow_div_pred hp (lpNorm_nonneg p y), rpow_div_pred hp (lpNorm_nonneg p z)] using h

/-- The weighted `p`-power inequality for arbitrary coordinate triples. -/
theorem weighted_lp_power {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ) :
    lpNorm p (x + y) ^ p / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      lpNorm p (x + z) ^ p / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      lpNorm p (y + z) ^ p / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    lpNorm p x + lpNorm p y + lpNorm p z +
      lpNorm p (x + y + z) ^ p / (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  by_cases hx : x = 0
  · subst x
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p y),
      rpow_div_pred hp (lpNorm_nonneg p z)]
  by_cases hy : y = 0
  · subst y
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p x),
      rpow_div_pred hp (lpNorm_nonneg p z)]
    ring_nf
    rfl
  by_cases hz : z = 0
  · subst z
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p x),
      rpow_div_pred hp (lpNorm_nonneg p y)]
    ring_nf
    rfl
  exact weighted_lp_power_of_ne hp x y z hx hy hz

/-- `b^p / a^(p-1) ≤ b` when `b ≤ a`. -/
theorem normalized_power_le {p a b : ℝ} (hp : 1 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    b ^ p / a ^ (p - 1) ≤ b := by
  by_cases h : a = 0
  · have hb0 : b = 0 := le_antisymm (h ▸ hba) hb
    simp [h, hb0, (zero_lt_one.trans hp).ne']
  have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos ha0 (p - 1))).mpr
  have hpow := Real.rpow_le_rpow hb hba (sub_nonneg.mpr hp.le)
  have he : b ^ p = b * b ^ (p - 1) := by
    by_cases hb0 : b = 0
    · simp [hb0, (zero_lt_one.trans hp).ne']
    · rw [Real.rpow_sub (lt_of_le_of_ne hb (Ne.symm hb0)), Real.rpow_one]
      field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hpow hb

/-- The deficit `a - b^p/a^(p-1)` is at most `p(a - b)`. -/
theorem normalized_power_deficit_le {p a b : ℝ} (hp : 1 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    a - b ^ p / a ^ (p - 1) ≤ p * (a - b) := by
  by_cases h : a = 0
  · have hb0 : b = 0 := le_antisymm (h ▸ hba) hb
    simp [h, hb0, (zero_lt_one.trans hp).ne']
  have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
  have hbern := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ b / a - 1 by linarith [div_nonneg hb ha]) hp.le
  have habs : |b / a| = b / a := abs_of_nonneg (div_nonneg hb ha)
  have he := weighted_abs_rpow_div ha0 p b
  rw [habs, abs_of_nonneg hb] at he
  have hm := mul_le_mul_of_nonneg_left hbern ha
  have hr : a * (b / a) = b := mul_div_cancel₀ b ha0.ne'
  simp only [add_sub_cancel] at hm
  nlinarith

/-- A rough but uniform bound, also controlling triples with zero pair deficit. -/
theorem lp_hlawka_le_exponent {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ) :
    tripleGap (lpNorm p) x y z ≤ p * pairGapSum (lpNorm p) x y z := by
  have hx := lpNorm_nonneg p x
  have hy := lpNorm_nonneg p y
  have hz := lpNorm_nonneg p z
  have hxy := lpNorm_add hp.le x y
  have hxz := lpNorm_add hp.le x z
  have hyz := lpNorm_add hp.le y z
  have htotal : lpNorm p (x + y + z) ≤ lpNorm p x + lpNorm p y + lpNorm p z :=
    (lpNorm_add hp.le (x + y) z).trans (add_le_add hxy le_rfl)
  have h0 := weighted_lp_power hp x y z
  have h1 := normalized_power_deficit_le hp (add_nonneg hx hy)
    (lpNorm_nonneg p (x + y)) hxy
  have h2 := normalized_power_deficit_le hp (add_nonneg hx hz)
    (lpNorm_nonneg p (x + z)) hxz
  have h3 := normalized_power_deficit_le hp (add_nonneg hy hz)
    (lpNorm_nonneg p (y + z)) hyz
  have h4 := normalized_power_le hp (add_nonneg (add_nonneg hx hy) hz)
    (lpNorm_nonneg p (x + y + z)) htotal
  dsimp only [tripleGap, pairGapSum, pairGap]
  nlinarith

/-- Jensen's inequality for the weighted mean of `p`-th powers. -/
theorem weighted_mean_power_le {p : ℝ} (hp : 1 < p) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i) (hs : ∑ i, a i = 2) :
    ((∑ i, b i) / 2) ^ p ≤ (∑ i, b i ^ p / a i ^ (p - 1)) / 2 := by
  have h := (convexOn_abs_rpow hp.le).map_sum_le (t := Finset.univ)
    (w := fun i ↦ a i / 2) (p := fun i ↦ b i / a i)
    (fun i _ ↦ div_nonneg (ha i).le (by norm_num))
    (by rw [← Finset.sum_div, hs]; norm_num) (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul] at h
  have hmean (i : ι) : a i / 2 * (b i / a i) = b i / 2 := by
    field_simp [(ha i).ne']
  have hpower (i : ι) : a i / 2 * |b i / a i| ^ p =
      (b i ^ p / a i ^ (p - 1)) / 2 := by
    calc
      _ = (a i * |b i / a i| ^ p) / 2 := by ring
      _ = _ := by rw [weighted_abs_rpow_div (ha i), abs_of_nonneg (hb i)]
  have habs : |(∑ i, b i) / 2| = (∑ i, b i) / 2 :=
    abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun i _ ↦ hb i) (by norm_num))
  simpa only [hmean, hpower, ← Finset.sum_div, habs] using h

/-- The full total-norm-dependent envelope before dividing by the pair gap. -/
theorem normalized_pair_sum_le {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1) :
    lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z) ≤
      2 * scalarEnvelopeRoot p (lpNorm p (x + y + z)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  let a : Fin 3 → ℝ := ![lpNorm p x + lpNorm p y,
    lpNorm p x + lpNorm p z, lpNorm p y + lpNorm p z]
  let b : Fin 3 → ℝ := ![lpNorm p (x + y), lpNorm p (x + z), lpNorm p (y + z)]
  have ha : ∀ i, 0 < a i := by
    intro i
    fin_cases i
    · exact add_pos (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hy)
    · exact add_pos (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hz)
    · exact add_pos (lpNorm_pos hp0 hy) (lpNorm_pos hp0 hz)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i <;> exact lpNorm_nonneg p _
  have hsum : ∑ i, a i = 2 := by
    simp only [a, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linarith
  have hmean := weighted_mean_power_le hp a b ha hb hsum
  have hweighted := weighted_lp_power hp x y z
  rw [hS, Real.one_rpow, div_one] at hweighted
  simp only [a, b, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hmean
  have hpow : ((lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z)) / 2) ^ p ≤
      (1 + lpNorm p (x + y + z) ^ p) / 2 := by linarith
  have hbase : 0 ≤ (1 + lpNorm p (x + y + z) ^ p) / 2 :=
    div_nonneg (add_nonneg zero_le_one
      (Real.rpow_nonneg (lpNorm_nonneg p (x + y + z)) p)) (by norm_num)
  have hroot : scalarEnvelopeRoot p (lpNorm p (x + y + z)) ^ p =
      (1 + lpNorm p (x + y + z) ^ p) / 2 := by
    rw [scalarEnvelopeRoot, ← Real.rpow_mul hbase,
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  rw [← hroot] at hpow
  have h := (Real.rpow_le_rpow_iff
    (div_nonneg (add_nonneg (add_nonneg (lpNorm_nonneg p (x + y))
      (lpNorm_nonneg p (x + z))) (lpNorm_nonneg p (y + z))) (by norm_num))
    (Real.rpow_nonneg hbase _) hp0).mp hpow
  change (lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z)) / 2 ≤
    scalarEnvelopeRoot p (lpNorm p (x + y + z)) at h
  linarith

end HlawkaSchatten.DiagonalConstruction
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/


/-! # Monotonicity of the scalar envelope -/

namespace HlawkaSchatten.DiagonalConstruction

/-- The envelope root equals a scaled two-dimensional `p`-norm. -/
theorem scalarEnvelopeRoot_eq_lpNorm {p q : ℝ} (hq : 0 ≤ q) :
    scalarEnvelopeRoot p q = (1 / 2 : ℝ) ^ (1 / p) * lpNorm p ![1, q] := by
  simp only [scalarEnvelopeRoot, lpNorm, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.norm_eq_abs, abs_one, abs_of_nonneg hq, Real.one_rpow]
  rw [show (1 + q ^ p) / 2 = (1 / 2 : ℝ) * (1 + q ^ p) by ring,
    Real.mul_rpow (by norm_num) (by positivity)]

/-- The envelope root is convex on `[0, ∞)`. -/
theorem convexOn_scalarEnvelopeRoot {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ (Set.Ici 0) (scalarEnvelopeRoot p) := by
  refine ⟨convex_Ici _, ?_⟩
  intro q hq r hr a b ha hb hab
  have hqr : 0 ≤ a * q + b * r := add_nonneg (mul_nonneg ha hq) (mul_nonneg hb hr)
  have heq : ![1, a * q + b * r] = a • ![1, q] + b • ![1, r] := by
    ext i
    fin_cases i <;> simp [hab]
  have h := (convexOn_lpNorm (ι := Fin 2) (E := ℝ) hp).2
    (Set.mem_univ ![1, q]) (Set.mem_univ ![1, r]) ha hb hab
  simp only [smul_eq_mul]
  rw [scalarEnvelopeRoot_eq_lpNorm hqr, scalarEnvelopeRoot_eq_lpNorm hq,
    scalarEnvelopeRoot_eq_lpNorm hr, heq]
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / p))
  simpa only [smul_eq_mul, mul_add, mul_left_comm] using hm

/-- The envelope root at `q = 1` equals 1. -/
@[simp]
theorem scalarEnvelopeRoot_one (p : ℝ) : scalarEnvelopeRoot p 1 = 1 := by
  norm_num [scalarEnvelopeRoot]

/-- The envelope root is strictly below 1 when `q < 1`. -/
theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

/-- The denominator of the scalar envelope is strictly positive when `q < 1`. -/
theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

/-- The scalar envelope is nonincreasing on `[0, 1)`. -/
theorem antitoneOn_scalarEnvelope {p : ℝ} (hp : 1 ≤ p) :
    AntitoneOn (scalarEnvelope p) (Set.Ico 0 1) := by
  intro r hr q hq hrq
  have hp0 := zero_lt_one.trans_le hp
  have hrne : 1 - r ≠ 0 := by linarith [hr.2]
  let a := (1 - q) / (1 - r)
  let b := (q - r) / (1 - r)
  have ha : 0 ≤ a := div_nonneg (by linarith [hq.2]) (by linarith [hr.2])
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hrq) (by linarith [hr.2])
  have hab : a + b = 1 := by dsimp [a, b]; field_simp [hrne]; ring
  have hpoint : a • r + b • (1 : ℝ) = q := by
    dsimp [a, b, smul_eq_mul]
    field_simp [hrne]
    ring
  have hconv := (convexOn_scalarEnvelopeRoot hp).2 hr.1 (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    ha hb hab
  rw [hpoint, scalarEnvelopeRoot_one] at hconv
  simp only [smul_eq_mul] at hconv
  have hm := mul_le_mul_of_nonneg_left hconv (by linarith [hr.2] : 0 ≤ 1 - r)
  have heq : (1 - r) * (a * scalarEnvelopeRoot p r + b * 1) =
      (1 - q) * scalarEnvelopeRoot p r + (q - r) := by
    dsimp [a, b]
    field_simp [hrne]
  rw [heq] at hm
  rw [scalarEnvelope, scalarEnvelope,
    div_le_div_iff₀ (scalarEnvelope_denominator_pos hp0 hq.1 hq.2)
      (scalarEnvelope_denominator_pos hp0 hr.1 hr.2)]
  nlinarith

end HlawkaSchatten.DiagonalConstruction
/- Generic confinement adapted from @bwdaugherty, Apache-2.0,
   accepted cutoff-32 submission d5944a03-85b4-4962-b146-4e6c7e7e50c7.
   Original definitions and normalization by Ezzeri Esa. -/
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalFailureBundle.Failure
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
section Deficit
variable {ι : Type*} [Fintype ι]

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]

theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith

theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)

/-- The envelope hypothesis at `q` confines the normalized total below `q`. -/
theorem normalized_failure_total_lt_q {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    lpNorm p (x + y + z) < q := by
  have hT1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp hK x y z hS hf
  by_contra hn
  have hle : q ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp.le
    (show q ∈ Set.Ico 0 1 from ⟨hq0.le, hq1⟩)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hT1⟩) hle
  linarith

end Deficit

/-- Scaled normalization: singleton norms sum to 3, each at most the total,
and the total is below `3q`. -/
theorem scaled_failure {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    ∃ x y z : Fin 3 → ℝ, hlawkaDeficit p K x y z < 0 ∧
      lpNorm p x + lpNorm p y + lpNorm p z = 3 ∧
      lpNorm p x ≤ lpNorm p (x + y + z) ∧
      lpNorm p y ≤ lpNorm p (x + y + z) ∧
      lpNorm p z ≤ lpNorm p (x + y + z) ∧
      lpNorm p (x + y + z) < 3 * q := by
  have hp0 : 0 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ := exists_normalized_failure hp0 hK x y z hf
  have hT := normalized_failure_total_lt_q hp hK hq0 hq1 henvelope x y z hS hf
  have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
  have hsum : (3 : ℝ) • x + (3 : ℝ) • y + (3 : ℝ) • z = (3 : ℝ) • (x + y + z) := by
    rw [smul_add, smul_add]
  refine ⟨(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlawkaDeficit_smul hp0, h3]
    linarith
  · rw [lpNorm_smul hp0, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, h3]
    linarith


end HlawkaSchatten.DiagonalFailureBundle.Failure

/- Generic contraction lemmas adapted from accepted Prove2Me submission 3735254f-536b-45fe-a0c1-2ea9ffc9d938 (Yuxuan Xu, bwdaugherty; Apache-2.0). The gap budget is now an arbitrary certified bound. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle

theorem others (i : Fin 3) : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases i <;> decide

theorem third {i j : Fin 3} (h : i ≠ j) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

structure Facts (p c D δ h A cmax tlo : ℝ) (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ) : Prop where
  Nnonneg : ∀ i, 0 ≤ N i
  hp : 1 ≤ p
  hc : 0 < c
  hcm : c ≤ cmax
  hct : 2 * tlo ≤ c
  hDc : D / c ≤ δ
  hA : 0 < A
  diag : ∀ i, 0 ≤ -X i i
  off : ∀ i j, i ≠ j → 0 ≤ X i j
  nsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    N i + N j + N k = 3
  rowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + X i j ^ p + X i k ^ p = N i ^ p
  row : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + ((X i j + X i k) / c) ^ p ≤ N i ^ p
  wD : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → c * N i - D ≤ X i j + X i k
  wD2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    c * (N j + N k) - D ≤ (X j i + X j k) + (X k i + X k j)
  offsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    6 - h < (X i j + X i k) + (X j i + X j k) + (X k i + X k j)
  T1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i i + X j i + X k i < A
  T2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (X i j + X j j + X k j) + (X i k + X j k + X k k) < cmax * A

section Rounds

variable {p c D δ h A cmax tlo : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N : Fin 3 → ℝ}

theorem ratio_round (F : Facts p c D δ h A cmax tlo X N) {n s τ σ : ℝ}
    (hn : ∀ i, n ≤ N i) (hn0 : 0 < n) (hD0 : 0 ≤ D) (hs : s ≤ 2 * tlo - D / n)
    (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hτc : 1 < τ ^ p + (s - τ) ^ p) (hσc : 1 < σ ^ p + (s - σ) ^ p) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * N i < X i j ∧ X i j < σ * N i := by
  intro i j k hij hik hjk
  have hp0 : 0 < p := by linarith [F.hp]
  have hN : 0 < N i := lt_of_lt_of_le hn0 (hn i)
  set Ni := N i with hNdef
  have hbj := F.off i j hij
  have hbk := F.off i k hik
  have hxy : (X i j / Ni) ^ p + (X i k / Ni) ^ p ≤ 1 := by
    rw [Real.div_rpow (by linarith) hN.le, Real.div_rpow (by linarith) hN.le, ← add_div,
      div_le_one (by positivity)]
    have := F.rowfull i j k hij hik hjk
    have := Real.rpow_nonneg (F.diag i) p
    linarith
  have hsum : s ≤ X i j / Ni + X i k / Ni := by
    rw [← add_div, le_div_iff₀ hN]
    have a1 : s * Ni ≤ (2 * tlo - D / n) * Ni := mul_le_mul_of_nonneg_right hs hN.le
    have a2 : D ≤ D / n * Ni := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn0]; exact mul_le_mul_of_nonneg_left (hn i) hD0
    have a3 : 2 * tlo * Ni ≤ c * Ni := mul_le_mul_of_nonneg_right F.hct hN.le
    have a4 := F.wD i j k hij hik hjk
    have e : (2 * tlo - D / n) * Ni = 2 * tlo * Ni - D / n * Ni := by ring
    linarith
  have h1 := ratio_lower F.hp (by positivity) (by positivity) hxy hsum hτ0 hτs hτc
  have h2 := ratio_upper F.hp (by positivity) (by positivity) hxy hsum hs1 hσs hσc
  exact ⟨(lt_div_iff₀ hN).1 h1, (div_lt_iff₀ hN).1 h2⟩

theorem lower_round (F : Facts p c D δ h A cmax tlo X N) {n τ n' Ab : ℝ}
    (hn : ∀ i, n ≤ N i) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → τ * N i < X i j)
    (hn'0 : 0 < n') (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / n') ^ p + (1 - δ / n') ^ p)
    (hchk : A ≤ τ * (3 - n') - Ab) : ∀ i, n' ≤ N i := by
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
  have m1 : τ * (3 - n') ≤ τ * (N j + N k) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ0
  rw [mul_add] at m1
  linarith

theorem upper_round (F : Facts p c D δ h A cmax tlo X N) {n σ U Ab : ℝ}
    (hn : ∀ i, n ≤ N i) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j < σ * N i)
    (hU3 : U < 3) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / (3 - U)) ^ p + (1 - δ / (3 - U)) ^ p)
    (hchk : cmax * A ≤ 6 - h - σ * (3 - U) - Ab) : ∀ i, N i ≤ U := by
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
    (div_nonneg (by linarith) F.hc.le) (F.Nnonneg j) (F.Nnonneg k) rj rk
  rw [← add_div] at hm
  have hNj := hn j
  have hNk := hn k
  have ha := diag_cert F.hp (by linarith [F.diag j, F.diag k]) F.hc hm (F.wD2 i j k hij hik hjk)
    F.hDc hδ0 (by linarith) (by linarith : N j + N k ≤ 3 - U)
    (by linarith) hAb hcert
  have t2 := F.T2 i j k hij hik hjk
  have os := F.offsum i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have m1 : σ * (N j + N k) ≤ σ * (3 - U) :=
    mul_le_mul_of_nonneg_left (by linarith) hσ0
  rw [mul_add] at m1
  linarith

theorem final_round (F : Facts p c D δ h A cmax tlo X N) {n U τ σ Ab ell u v w : ℝ}
    (hn : ∀ i, n ≤ N i) (hU : ∀ i, N i ≤ U) (hδn : δ ≤ n)
    (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * N i < X i j ∧ X i j < σ * N i)
    (hU0 : 0 < U) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p)
    (h1 : v ≤ τ * n) (h2 : σ * U ≤ w) (h3 : Ab ≤ u)
    (h4 : ell ≤ τ * (3 - U) - A) : (∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w) := by
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
    have m1 : τ * (3 - U) ≤ τ * (N k + N l) :=
      mul_le_mul_of_nonneg_left (by linarith [hU j]) hτ0
    rw [mul_add] at m1
    constructor <;> linarith
  · rw [if_neg hji]
    obtain ⟨k, hjk, hik⟩ := third hji
    have r := hr j i k hji hjk hik
    have m1 : τ * n ≤ τ * N j := mul_le_mul_of_nonneg_left (hn j) hτ0
    have m2 : σ * N j ≤ σ * U := mul_le_mul_of_nonneg_left (hU j) hσ0
    constructor <;> linarith [r.1, r.2]

end Rounds


end HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction
abbrev Triple := Fin 3 → Fin 3 → ℝ

theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

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


end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

def coordinateBox (ell u v w : ℝ) (X : Triple) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w

theorem facts_of {p α β tlo thib D δ h A g eps ell u v w : ℝ} {X : Triple}
    (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β) (hp1 : 1 ≤ p)
    (hell : 0 < ell) (hv : 0 < v) (hA : 0 < A)
    (htlo0 : 0 < tlo) (htlo : tlo ≤ (1/2 : ℝ) ^ (1/α))
    (hthib : (1/2 : ℝ) ^ (1/β) ≤ thib)
    (hD : g + 3 * eps - 6 + 6 * thib ≤ D) (hD0 : 0 ≤ D)
    (hδ : D / (2 * tlo) ≤ δ) (hh : g + 3 * eps ≤ h)
    (hB : coordinateBox ell u v w X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < A)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < g)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ (X j i + X k i) + eps) :
    Facts p (cp p) D δ h A (2 * thib) tlo X (fun i ↦ lpNorm p (X i)) := by
  have hp : 1 ≤ p := hp1
  have hp0 : 0 < p := by linarith
  have hdiag : ∀ i, -(u : ℝ) ≤ X i i ∧ X i i ≤ -(ell : ℝ) := fun i ↦ by
    simpa using hB i i
  have hoff : ∀ i j, i ≠ j → (v : ℝ) ≤ X i j ∧ X i j ≤ w := fun i j h ↦ by
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
  have hoffsum0 : 6 - g - 3 * eps <
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    unfold pairGapSum pairGap at hG
    have t01 := htail 2 0 1 (by decide) (by decide) (by decide)
    have t02 := htail 1 0 2 (by decide) (by decide) (by decide)
    have t12 := htail 0 1 2 (by decide) (by decide) (by decide)
    linarith
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
    linarith only [hoffsum0, hcm, hD]
  have hcN : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      cp p * lpNorm p (X i) + cp p * lpNorm p (X j) + cp p * lpNorm p (X k) = cp p * 3 := by
    intro i j k hij hik hjk
    rw [← hnsum i j k hij hik hjk]; ring
  have hcpos := cp_pos p
  set vtotal : Fin 3 → ℝ := X 0 + X 1 + X 2 with hvtotal
  have hvc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → vtotal i = X i i + X j i + X k i := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ X l i) hij hik hjk
    rw [Fin.sum_univ_three] at this
    simp only [hvtotal, Pi.add_apply]
    linarith
  refine ⟨fun i ↦ lpNorm_nonneg3 p (X i), hp, hcpos, hcm, hct, ?_, by linarith, hdn, fun i j h ↦ hv.le.trans (hoff i j h).1, hnsum,
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
    have h1 := coord_le hp0 vtotal hij hik hjk
    rw [hvc i j k hij hik hjk] at h1
    linarith [le_abs_self (X i i + X j i + X k i)]
  · intro i j k hij hik hjk
    have h1 := two_coord_le hp vtotal hij hik hjk
    rw [hvc j i k (Ne.symm hij) hjk hik, hvc k i j (Ne.symm hik) (Ne.symm hjk) hij] at h1
    have h2 : cp p * lpNorm p vtotal < cp p * (A) := mul_lt_mul_of_pos_left hT hcpos
    have h3 : cp p * (A) ≤ 2 * thib * (A) :=
      mul_le_mul_of_nonneg_right hcm (by linarith)
    have := le_abs_self (X j j + X i j + X k j)
    have := le_abs_self (X k k + X i k + X j k)
    linarith


end HlawkaSchatten.DiagonalRealBundle



set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle

theorem coordinateBox_weaken {ell u v w ell' u' v' w' : ℝ} {X : Triple}
    (hB : coordinateBox ell' u' v' w' X)
    (hell : ell ≤ ell') (hu : u' ≤ u) (hv : v ≤ v') (hw : w' ≤ w) :
    coordinateBox ell u v w X := by
  intro j i
  have hh := hB j i
  by_cases hji : j = i
  · rw [if_pos hji] at hh ⊢
    constructor <;> linarith
  · rw [if_neg hji] at hh ⊢
    constructor <;> linarith

end HlawkaSchatten.DiagonalRealBundle

/- Adapted from accepted Prove2Me submission 4753aff4-c621-4df6-9535-63c865f87fd0. Generic proofs by Ezzeri Esa and bwdaugherty, cutoff-21 implementation by Yuxuan Xu; Apache-2.0. All cutoff-specific constants are explicit parameters. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalFailureBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem lpNorm_le_three_root_mul_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h

theorem inverse_three_root_deficit (p : ℝ) :
    1 - ((3 : ℝ) ^ (1 / p))⁻¹ ≤ Real.log 3 / p := by
  have h := Real.add_one_le_exp (-(Real.log 3 / p))
  have he : ((3 : ℝ) ^ (1 / p))⁻¹ = Real.exp (-(Real.log 3 / p)) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  linarith


theorem exists_signed_coord_bound {p m B E : ℝ} (hm : 0 < m) (hp : m ≤ p)
    (hBE : (1099 / (1000 * m)) * B ≤ E) (v : Fin 3 → ℝ) (hv : lpNorm p v ≤ B) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ lpNorm p v - E ≤ s * v i := by
  have hp0 : 0 < p := hm.trans_le hp
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |v i|) Finset.univ_nonempty
  have hmax := lpNorm_le_three_root_mul_max hp0 v i (fun j ↦ hi j (Finset.mem_univ _))
  set c := ((3 : ℝ) ^ (1 / p))⁻¹ with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hmax' : c * lpNorm p v ≤ |v i| := by
    have hh := mul_le_mul_of_nonneg_left hmax hc0.le
    have he : c * ((3 : ℝ) ^ (1 / p) * |v i|) = |v i| := by
      rw [hcdef, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rwa [he] at hh
  have hd : 1 - c ≤ Real.log 3 / p := inverse_three_root_deficit p
  have hlog3 : Real.log 3 < 1099 / 1000 := by linarith [Real.log_three_lt_d9]
  have hr : 0 ≤ (1099 : ℝ) / (1000 * m) := by positivity
  have he : (1099 : ℝ) / (1000 * m) * m = 1099 / 1000 := by field_simp
  have hlogp : Real.log 3 / p ≤ 1099 / (1000 * m) := by
    rw [div_le_iff₀ hp0]
    have hh := mul_le_mul_of_nonneg_left hp hr
    rw [he] at hh
    linarith
  have hn0 := lpNorm_nonneg p v
  have h1 := mul_le_mul_of_nonneg_right (hd.trans hlogp) hn0
  have h2 := mul_le_mul_of_nonneg_left hv hr
  have hbound : lpNorm p v - |v i| ≤ E := by nlinarith
  by_cases hi0 : 0 ≤ v i
  · rw [abs_of_nonneg hi0] at hbound
    exact ⟨i, 1, Or.inl rfl, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hi0)] at hbound
    exact ⟨i, -1, Or.inr rfl, by linarith⟩

theorem signed_conflict_bound {a b c Na Nb Nc P1 P2 T G E s r : ℝ}
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ha : |a| ≤ Na) (hb : |b| ≤ Nb) (hc : |c| ≤ Nc) (hcol : |a + b + c| ≤ T)
    (h1 : P1 - E ≤ s * a + s * b) (h2 : P2 - E ≤ r * a + r * c)
    (hP1 : Na + Nb - P1 ≤ G) (hP2 : Na + Nc - P2 ≤ G)
    (hNa : G + E < Na) (hS : Na + Nb + Nc = 3) (hT : T < 3 - 2 * (G + E)) :
    False := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hcol' := abs_le.mp hcol
  rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> linarith

theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _

theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e

theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]


end HlawkaSchatten.DiagonalFailureBundle

namespace HlawkaSchatten.DiagonalCutoff16
open HlawkaSchatten.DiagonalFailureBundle

structure OrientedData (p q c α E : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop where
  sum : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3
  norm_le_total : ∀ i, lpNorm p (X i) ≤ lpNorm p (X 0 + X 1 + X 2)
  total_one : 1 ≤ lpNorm p (X 0 + X 1 + X 2)
  total_cap : lpNorm p (X 0 + X 1 + X 2) < 3*q
  main0 : lpNorm p (X 1 + X 2) - (X 1 0 + X 2 0) ≤ E
  main1 : lpNorm p (X 0 + X 2) - (X 0 1 + X 2 1) ≤ E
  main2 : lpNorm p (X 0 + X 1) - (X 0 2 + X 1 2) ≤ E
  linear_failure : lpNorm p (X 0 + X 1 + X 2) - (c*α) *
    (lpNorm p (X 1 + X 2) + lpNorm p (X 0 + X 2) + lpNorm p (X 0 + X 1)) ≤ 3 - 6*(c*α)
  failure : tripleDeficit p (cyclicConstant p) X < 0

theorem exists_oriented_failure {p α c q E g : ℝ}
    (hα : 1 < α) (hαp : α ≤ p) (hc : 0 < c) (hcα : 1 < c*α)
    (hlinear : c*p < cyclicConstant p) (hq0 : 0 < q) (hq1 : q < 1)
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (hBE : (1099 / (1000 * α)) * (6*q) ≤ E)
    (hgap : 2/(c*α) ≤ g) (hsep : g+E < 3-6*q) (hTsep : 3*q ≤ 3-2*(g+E))
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ, OrientedData p q c α E X := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  set K := cyclicConstant p with hKdef
  have hK : c * α < K := by
    have := mul_le_mul_of_nonneg_left hαp hc.le
    linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT, hTq⟩ :=
    Failure.scaled_failure hp1 (by linarith) hq0 (by linarith) henvelope x y z hf
  set T := lpNorm p (x + y + z) with hTdef
  have hT : T < 3*q := by linarith
  -- Failure gives `K G < 3 - T`.
  have hG0 := pairGapSum_nonneg hp1.le x y z
  have hKG : K * pairGapSum (lpNorm p) x y z < 3 - T := by
    have h := hf
    rw [hlawkaDeficit_eq, tripleGap, hS] at h
    linarith
  have hG : (c * α) * pairGapSum (lpNorm p) x y z + T < 3 := by
    have := mul_le_mul_of_nonneg_right hK.le hG0
    linarith
  have hTone : 1 ≤ T := by linarith
  have hGp : pairGapSum (lpNorm p) x y z < 2 / (c * p) := by
    rw [lt_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hlinear.le hG0
    nlinarith
  have hxy0 := pairGap_nonneg hp1.le x y
  have hxz0 := pairGap_nonneg hp1.le x z
  have hyz0 := pairGap_nonneg hp1.le y z
  have hGapCap : pairGapSum (lpNorm p) x y z < g := by
    have hb : pairGapSum (lpNorm p) x y z < 2 / (c * α) := by
      apply (lt_div_iff₀ (by positivity)).2
      nlinarith only [hG, hTone]
    exact hb.trans_le hgap
  have hGsplit := hGapCap
  dsimp only [pairGapSum, pairGap] at hGsplit hxy0 hxz0 hyz0
  -- Pass 0.
  have hNx := lpNorm_nonneg p x
  have hNy := lpNorm_nonneg p y
  have hNz := lpNorm_nonneg p z
  obtain ⟨i, s, hs, hsxy⟩ := exists_signed_coord_bound (m := α) (B := (6*q)) (E := E) (by linarith) hαp hBE (x + y)
    (by linarith [lpNorm_add hp1.le x y])
  obtain ⟨j, r, hr, hrxz⟩ := exists_signed_coord_bound (m := α) (B := (6*q)) (E := E) (by linarith) hαp hBE (x + z)
    (by linarith [lpNorm_add hp1.le x z])
  obtain ⟨k, t, ht, htyz⟩ := exists_signed_coord_bound (m := α) (B := (6*q)) (E := E) (by linarith) hαp hBE (y + z)
    (by linarith [lpNorm_add hp1.le y z])
  simp only [Pi.add_apply, mul_add] at hsxy hrxz htyz
  have hxa (l : Fin 3) : |x l| ≤ lpNorm p x := norm_apply_le_lpNorm hp1.le x l
  have hya (l : Fin 3) : |y l| ≤ lpNorm p y := norm_apply_le_lpNorm hp1.le y l
  have hza (l : Fin 3) : |z l| ≤ lpNorm p z := norm_apply_le_lpNorm hp1.le z l
  have habs (l : Fin 3) : |x l + y l + z l| ≤ T := norm_apply_le_lpNorm hp1.le (x + y + z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    exact signed_conflict_bound (G := g) (E := E) hs hr (hxa i) (hya i) (hza i) (habs i) hsxy hrxz
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hik : i ≠ k := by
    intro heq
    subst k
    have hcol : |y i + x i + z i| ≤ T := by
      rw [show y i + x i + z i = x i + y i + z i by ring]; exact habs i
    exact signed_conflict_bound (G := g) (E := E) (P1 := lpNorm p (x + y)) hs ht (hya i) (hxa i) (hza i) hcol (by linarith) htyz
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hjk : j ≠ k := by
    intro heq
    subst k
    have hcol : |z j + x j + y j| ≤ T := by
      rw [show z j + x j + y j = x j + y j + z j by ring]; exact habs j
    exact signed_conflict_bound (G := g) (E := E) (P1 := lpNorm p (x + z)) (P2 := lpNorm p (y + z)) hr ht (hza j) (hxa j) (hya j) hcol (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  -- Orientation.
  let f : Fin 3 → Fin 3 := ![k, j, i]
  have hfInj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hfInj.bijective_of_finite
  let signs : Fin 3 → ℝ := ![t, r, s]
  have hsigns : ∀ l, |signs l| = 1 := by
    intro l
    fin_cases l
    · rcases ht with rfl | rfl <;> norm_num [signs]
    · rcases hr with rfl | rfl <;> norm_num [signs]
    · rcases hs with rfl | rfl <;> norm_num [signs]
  let u := orient e signs x
  let v := orient e signs y
  let w := orient e signs z
  have hu : lpNorm p u = lpNorm p x := lpNorm_orient p e signs x hsigns
  have hv : lpNorm p v = lpNorm p y := lpNorm_orient p e signs y hsigns
  have hw : lpNorm p w = lpNorm p z := lpNorm_orient p e signs z hsigns
  have hsumNorm : lpNorm p (u + v + w) = T := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have huv : lpNorm p (u + v) = lpNorm p (x + y) := by
    dsimp [u, v]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have huw : lpNorm p (u + w) = lpNorm p (x + z) := by
    dsimp [u, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hvw : lpNorm p (v + w) = lpNorm p (y + z) := by
    dsimp [v, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hpgs : pairGapSum (lpNorm p) u v w = pairGapSum (lpNorm p) x y z := by
    simp only [pairGapSum, pairGap, hu, hv, hw, huv, huw, hvw]
  have e0 : v 0 + w 0 = t * y k + t * z k := by simp [v, w, orient, e, f, signs]
  have e1 : u 1 + w 1 = r * x j + r * z j := by simp [u, w, orient, e, f, signs]
  have e2 : u 2 + v 2 = s * x i + s * y i := by simp [u, v, orient, e, f, signs]
  let X : Fin 3 → Fin 3 → ℝ := ![u, v, w]
  have hNX : ∀ l, lpNorm p (X l) ≤ T := by
    intro l
    fin_cases l
    · change lpNorm p u ≤ T
      rw [hu]; exact hxT
    · change lpNorm p v ≤ T
      rw [hv]; exact hyT
    · change lpNorm p w ≤ T
      rw [hw]; exact hzT
  have hlin : T - (c*α) * (lpNorm p (v + w) + lpNorm p (u + w) + lpNorm p (u + v)) ≤
      3 - 6 * (c*α) := by
    have hgf : pairGapSum (lpNorm p) u v w =
        6 - (lpNorm p (v + w) + lpNorm p (u + w) + lpNorm p (u + v)) := by
      dsimp only [pairGapSum, pairGap]
      rw [hu, hv, hw]
      linarith
    rw [← hpgs, hgf] at hG
    linarith
  refine ⟨![u, v, w], ?_⟩
  constructor
  · change lpNorm p u + lpNorm p v + lpNorm p w = 3
    rw [hu, hv, hw]; exact hS
  · intro l
    change lpNorm p (X l) ≤ lpNorm p (u + v + w)
    rw [hsumNorm]
    exact hNX l
  · change 1 ≤ lpNorm p (u + v + w)
    rw [hsumNorm]; exact hTone
  · change lpNorm p (u + v + w) < 3*q
    rw [hsumNorm]; exact hTq
  · change lpNorm p (v+w) - (v 0+w 0) ≤ E
    rw [hvw, e0]; linarith
  · change lpNorm p (u+w) - (u 1+w 1) ≤ E
    rw [huw, e1]; linarith
  · change lpNorm p (u+v) - (u 2+v 2) ≤ E
    rw [huv, e2]; linarith
  · change lpNorm p (u+v+w) - (c*α) * (lpNorm p (v+w)+lpNorm p (u+w)+lpNorm p (u+v)) ≤ _
    rw [hsumNorm]; exact hlin
  · change hlawkaDeficit p K u v w < 0
    dsimp [u, v, w]
    rwa [hlawkaDeficit_orient p K e signs x y z hsigns]

end HlawkaSchatten.DiagonalCutoff16

/- Exact LP implications, with original coordinate norms throughout.
The proof layout follows accepted submission 4753aff4-c621-4df6-9535-63c865f87fd0
(Yuxuan Xu, bwdaugherty and Ezzeri Esa; Apache-2.0). -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalCutoff16Scalar
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace HlawkaSchatten.DiagonalCutoff16
theorem coarse_stage0_w024 (v : Fin 16 → ℝ)
    (h0 : ((-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h1 : ((1 : ℝ) * v 9 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h2 : ((-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h3 : ((1 : ℝ) * v 10 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h4 : ((-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h5 : ((1 : ℝ) * v 11 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h6 : ((-1 : ℝ) * v 15) ≤ (-1 : ℝ))
    (h7 : ((1 : ℝ) * v 15) ≤ (12213/10000 : ℝ))
    (h8 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h9 : ((1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h10 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h11 : ((1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h12 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h13 : ((1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h14 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h15 : ((1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h16 : ((-1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h17 : ((1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h18 : ((-1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h19 : ((1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h20 : ((-1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h21 : ((1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h22 : ((-1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h23 : ((1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h24 : ((-1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h25 : ((1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h26 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h27 : ((1 : ℝ) * v 0 + (1 : ℝ) * v 3 + (1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h28 : ((-1 : ℝ) * v 12) ≤ (0 : ℝ))
    (h29 : ((-1 : ℝ) * v 10 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 12) ≤ (0 : ℝ))
    (h30 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (27/200 : ℝ))
    (h31 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 4 + (-1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h32 : ((1 : ℝ) * v 1 + (1 : ℝ) * v 4 + (1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h33 : ((-1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h34 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h35 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (27/200 : ℝ))
    (h36 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (-1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h37 : ((1 : ℝ) * v 2 + (1 : ℝ) * v 5 + (1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h38 : ((-1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h39 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 10 + (1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h40 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (27/200 : ℝ))
    (h41 : ((-1741/200 : ℝ) * v 12 + (-1741/200 : ℝ) * v 13 + (-1741/200 : ℝ) * v 14 + (1 : ℝ) * v 15) ≤ (-4923/100 : ℝ))
    (heq : ((1 : ℝ) * v 9 + (1 : ℝ) * v 10 + (1 : ℝ) * v 11) = (3 : ℝ)) :
    (0 : ℝ) ≤ ((1 : ℝ) * v 3 + (1 : ℝ) * v 6) ∧
    (-3 : ℝ) ≤ ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6) ∧
    (0 : ℝ) ≤ ((1/2 : ℝ) * v 3 + (-1 : ℝ) * v 4 + (1/2 : ℝ) * v 6 + (-1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1/2 : ℝ) * v 3 + (1 : ℝ) * v 4 + (1/2 : ℝ) * v 6 + (1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1/2 : ℝ) * v 3 + (-1 : ℝ) * v 5 + (1/2 : ℝ) * v 6 + (-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1/2 : ℝ) * v 3 + (1 : ℝ) * v 5 + (1/2 : ℝ) * v 6 + (1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 1 + (1 : ℝ) * v 7) ∧
    (-3 : ℝ) ≤ ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 0 + (1/2 : ℝ) * v 1 + (-1 : ℝ) * v 6 + (1/2 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 0 + (1/2 : ℝ) * v 1 + (1 : ℝ) * v 6 + (1/2 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1/2 : ℝ) * v 1 + (-1 : ℝ) * v 2 + (1/2 : ℝ) * v 7 + (-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1/2 : ℝ) * v 1 + (1 : ℝ) * v 2 + (1/2 : ℝ) * v 7 + (1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 2 + (1 : ℝ) * v 5) ∧
    (-3 : ℝ) ≤ ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 0 + (1/2 : ℝ) * v 2 + (-1 : ℝ) * v 3 + (1/2 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 0 + (1/2 : ℝ) * v 2 + (1 : ℝ) * v 3 + (1/2 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 1 + (1/2 : ℝ) * v 2 + (-1 : ℝ) * v 4 + (1/2 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 1 + (1/2 : ℝ) * v 2 + (1 : ℝ) * v 4 + (1/2 : ℝ) * v 5) := by
  repeat' constructor
  · linarith only [h1, h7, h30, h34, h39, h41, heq]
  · linarith only [h7, h8, h15, h21, h27, heq]
  · linarith only [h7, h8, h23, h27, h29, h30, h32, h35, h39, h41, heq]
  · linarith only [h3, h7, h11, h16, h24, h29, h30, h35, h37, h39, h40, h41, heq]
  · linarith only [h7, h8, h19, h27, h29, h30, h34, h37, h40, h41, heq]
  · linarith only [h5, h7, h13, h16, h24, h29, h30, h32, h34, h35, h40, h41, heq]
  · linarith only [h3, h7, h29, h35, h39, h41, heq]
  · linarith only [h7, h11, h16, h23, h32, heq]
  · linarith only [h7, h16, h21, h27, h30, h32, h34, h35, h39, h41, heq]
  · linarith only [h1, h7, h8, h15, h24, h30, h34, h35, h37, h39, h40, h41, heq]
  · linarith only [h7, h13, h16, h29, h32, h34, h35, h37, h40, h41, heq]
  · linarith only [h5, h7, h8, h19, h24, h27, h29, h30, h34, h35, h40, h41, heq]
  · linarith only [h5, h7, h29, h34, h40, h41, heq]
  · linarith only [h7, h13, h19, h24, h37, heq]
  · linarith only [h7, h15, h24, h27, h30, h34, h37, h39, h40, h41, heq]
  · linarith only [h1, h7, h8, h16, h21, h30, h32, h34, h35, h39, h40, h41, heq]
  · linarith only [h7, h11, h24, h29, h32, h35, h37, h39, h40, h41, heq]
  · linarith only [h3, h7, h8, h16, h23, h27, h29, h30, h35, h39, h40, h41, heq]
theorem coarse_stage1_w024 (v : Fin 16 → ℝ)
    (h0 : ((-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h1 : ((1 : ℝ) * v 9 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h2 : ((-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h3 : ((1 : ℝ) * v 10 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h4 : ((-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h5 : ((1 : ℝ) * v 11 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h6 : ((-1 : ℝ) * v 15) ≤ (-1 : ℝ))
    (h7 : ((1 : ℝ) * v 15) ≤ (12213/10000 : ℝ))
    (h8 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h9 : ((1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h10 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h11 : ((1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h12 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h13 : ((1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h14 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h15 : ((1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h16 : ((-1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h17 : ((1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h18 : ((-1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h19 : ((1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h20 : ((-1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h21 : ((1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h22 : ((-1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h23 : ((1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h24 : ((-1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h25 : ((1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h26 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h27 : ((1 : ℝ) * v 0 + (1 : ℝ) * v 3 + (1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h28 : ((-1 : ℝ) * v 12) ≤ (0 : ℝ))
    (h29 : ((-1 : ℝ) * v 10 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 12) ≤ (0 : ℝ))
    (h30 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (27/200 : ℝ))
    (h31 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 4 + (-1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h32 : ((1 : ℝ) * v 1 + (1 : ℝ) * v 4 + (1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h33 : ((-1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h34 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h35 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (27/200 : ℝ))
    (h36 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (-1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h37 : ((1 : ℝ) * v 2 + (1 : ℝ) * v 5 + (1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h38 : ((-1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h39 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 10 + (1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h40 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (27/200 : ℝ))
    (h41 : ((-1741/200 : ℝ) * v 12 + (-1741/200 : ℝ) * v 13 + (-1741/200 : ℝ) * v 14 + (1 : ℝ) * v 15) ≤ (-4923/100 : ℝ))
    (h42 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (1/100000 : ℝ))
    (h43 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (1/100000 : ℝ))
    (h44 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (1/100000 : ℝ))
    (heq : ((1 : ℝ) * v 9 + (1 : ℝ) * v 10 + (1 : ℝ) * v 11) = (3 : ℝ)) :
    (-12213/10000 : ℝ) ≤ ((1 : ℝ) * v 0) ∧
    (353/1000 : ℝ) ≤ ((-1 : ℝ) * v 0) ∧
    (137/200 : ℝ) ≤ ((1 : ℝ) * v 1) ∧
    (-12213/10000 : ℝ) ≤ ((-1 : ℝ) * v 1) ∧
    (137/200 : ℝ) ≤ ((1 : ℝ) * v 2) ∧
    (-12213/10000 : ℝ) ≤ ((-1 : ℝ) * v 2) ∧
    (137/200 : ℝ) ≤ ((1 : ℝ) * v 3) ∧
    (-12213/10000 : ℝ) ≤ ((-1 : ℝ) * v 3) ∧
    (-12213/10000 : ℝ) ≤ ((1 : ℝ) * v 4) ∧
    (353/1000 : ℝ) ≤ ((-1 : ℝ) * v 4) ∧
    (137/200 : ℝ) ≤ ((1 : ℝ) * v 5) ∧
    (-12213/10000 : ℝ) ≤ ((-1 : ℝ) * v 5) ∧
    (137/200 : ℝ) ≤ ((1 : ℝ) * v 6) ∧
    (-12213/10000 : ℝ) ≤ ((-1 : ℝ) * v 6) ∧
    (137/200 : ℝ) ≤ ((1 : ℝ) * v 7) ∧
    (-12213/10000 : ℝ) ≤ ((-1 : ℝ) * v 7) ∧
    (-12213/10000 : ℝ) ≤ ((1 : ℝ) * v 8) ∧
    (353/1000 : ℝ) ≤ ((-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1/3 : ℝ) * v 3 + (-1 : ℝ) * v 4 + (1/3 : ℝ) * v 6 + (-1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1/3 : ℝ) * v 3 + (1 : ℝ) * v 4 + (1/3 : ℝ) * v 6 + (1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1/3 : ℝ) * v 3 + (-1 : ℝ) * v 5 + (1/3 : ℝ) * v 6 + (-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1/3 : ℝ) * v 3 + (1 : ℝ) * v 5 + (1/3 : ℝ) * v 6 + (1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 0 + (1/3 : ℝ) * v 1 + (-1 : ℝ) * v 6 + (1/3 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 0 + (1/3 : ℝ) * v 1 + (1 : ℝ) * v 6 + (1/3 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1/3 : ℝ) * v 1 + (-1 : ℝ) * v 2 + (1/3 : ℝ) * v 7 + (-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1/3 : ℝ) * v 1 + (1 : ℝ) * v 2 + (1/3 : ℝ) * v 7 + (1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 0 + (1/3 : ℝ) * v 2 + (-1 : ℝ) * v 3 + (1/3 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 0 + (1/3 : ℝ) * v 2 + (1 : ℝ) * v 3 + (1/3 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 1 + (1/3 : ℝ) * v 2 + (-1 : ℝ) * v 4 + (1/3 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 1 + (1/3 : ℝ) * v 2 + (1 : ℝ) * v 4 + (1/3 : ℝ) * v 5) := by
  repeat' constructor
  · linarith only [h1, h7, h8]
  · linarith only [h1, h7, h27, h34, h39, h41, h42, heq]
  · linarith only [h7, h8, h23, h27, h29, h39, h41, h42, h43, heq]
  · linarith only [h1, h7, h11]
  · linarith only [h7, h8, h19, h27, h29, h34, h41, h42, h44, heq]
  · linarith only [h1, h7, h13]
  · linarith only [h7, h16, h21, h32, h34, h39, h41, h42, h43, heq]
  · linarith only [h3, h7, h15]
  · linarith only [h3, h7, h16]
  · linarith only [h3, h7, h29, h32, h39, h41, h43, heq]
  · linarith only [h7, h13, h16, h29, h32, h34, h41, h43, h44, heq]
  · linarith only [h3, h7, h19]
  · linarith only [h7, h15, h24, h34, h37, h39, h41, h42, h44, heq]
  · linarith only [h5, h7, h21]
  · linarith only [h7, h11, h24, h29, h37, h39, h41, h43, h44, heq]
  · linarith only [h5, h7, h23]
  · linarith only [h5, h7, h24]
  · linarith only [h5, h7, h29, h34, h37, h41, h44, heq]
  · linarith only [h7, h8, h23, h27, h29, h32, h39, h41, h42, h43, heq]
  · linarith only [h3, h7, h11, h16, h24, h29, h37, h39, h41, h42, h43, h44, heq]
  · linarith only [h7, h8, h19, h27, h29, h34, h37, h41, h42, h44, heq]
  · linarith only [h5, h7, h13, h16, h24, h29, h32, h34, h41, h42, h43, h44, heq]
  · linarith only [h7, h16, h21, h27, h32, h34, h39, h41, h42, h43, heq]
  · linarith only [h1, h7, h8, h15, h24, h34, h37, h39, h41, h42, h43, h44, heq]
  · linarith only [h7, h13, h16, h29, h32, h34, h37, h41, h43, h44, heq]
  · linarith only [h5, h7, h8, h19, h24, h27, h29, h34, h41, h42, h43, h44, heq]
  · linarith only [h7, h15, h24, h27, h34, h37, h39, h41, h42, h44, heq]
  · linarith only [h1, h7, h8, h16, h21, h32, h34, h39, h41, h42, h43, h44, heq]
  · linarith only [h7, h11, h24, h29, h32, h37, h39, h41, h43, h44, heq]
  · linarith only [h3, h7, h8, h16, h23, h27, h29, h39, h41, h42, h43, h44, heq]
theorem coarse_oriented_w024 (p : ℝ) (hp : (16 : ℝ) ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (N P : Fin 3 → ℝ) (T : ℝ)
    (hNdef : ∀ i, N i = lpNorm p (X i))
    (hP0 : P 0 = lpNorm p (X 1 + X 2))
    (hP1 : P 1 = lpNorm p (X 0 + X 2))
    (hP2 : P 2 = lpNorm p (X 0 + X 1))
    (hTdef : T = lpNorm p (X 0 + X 1 + X 2))
    (hS : N 0 + N 1 + N 2 = 3) (hNT : ∀ i, N i ≤ T)
    (hT1 : 1 ≤ T) (hTcap : T ≤ (12213/10000 : ℝ))
    (hmain0 : P 0 - (X 1 0 + X 2 0) ≤ (27/200 : ℝ))
    (hmain1 : P 1 - (X 0 1 + X 2 1) ≤ (27/200 : ℝ))
    (hmain2 : P 2 - (X 0 2 + X 1 2) ≤ (27/200 : ℝ))
    (hfail : T - (1741/200 : ℝ) * (P 0 + P 1 + P 2) ≤ 3 - 6 * (1741/200 : ℝ)) :
    coordinateBox (353/1000 : ℝ) (12213/10000 : ℝ) (137/200 : ℝ) (12213/10000 : ℝ) X ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j + X k) ≤ X j i + X k i + 1/100000000) := by
  have hp1 : 1 ≤ p := by linarith
  have hpn : 0 < p := by linarith
  have hp16 : 16 ≤ p := by linarith
  have hnpos (i : Fin 3) : 0 ≤ N i := by rw [hNdef]; exact lpNorm_nonneg p (X i)
  have hcoord (j i : Fin 3) : -N j ≤ X j i ∧ X j i ≤ N j := by
    have hc := norm_apply_le_lpNorm hp1 (X j) i
    rw [Real.norm_eq_abs, ← hNdef] at hc
    exact abs_le.mp hc
  have hn0 := hnpos 0
  rcases hcoord 0 0 with ⟨hx00l, hx00u⟩
  rcases hcoord 0 1 with ⟨hx01l, hx01u⟩
  rcases hcoord 0 2 with ⟨hx02l, hx02u⟩
  have hn1 := hnpos 1
  rcases hcoord 1 0 with ⟨hx10l, hx10u⟩
  rcases hcoord 1 1 with ⟨hx11l, hx11u⟩
  rcases hcoord 1 2 with ⟨hx12l, hx12u⟩
  have hn2 := hnpos 2
  rcases hcoord 2 0 with ⟨hx20l, hx20u⟩
  rcases hcoord 2 1 with ⟨hx21l, hx21u⟩
  rcases hcoord 2 2 with ⟨hx22l, hx22u⟩
  have hnt0 := hNT 0
  have ht0 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 0
  rw [Real.norm_eq_abs, ← hTdef] at ht0
  simp only [Pi.add_apply] at ht0
  rcases abs_le.mp ht0 with ⟨ht0l, ht0u⟩
  have hnt1 := hNT 1
  have ht1 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 1
  rw [Real.norm_eq_abs, ← hTdef] at ht1
  simp only [Pi.add_apply] at ht1
  rcases abs_le.mp ht1 with ⟨ht1l, ht1u⟩
  have hnt2 := hNT 2
  have ht2 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 2
  rw [Real.norm_eq_abs, ← hTdef] at ht2
  simp only [Pi.add_apply] at ht2
  rcases abs_le.mp ht2 with ⟨ht2l, ht2u⟩
  have hp0n : 0 ≤ P 0 := by rw [hP0]; exact lpNorm_nonneg p _
  have hp0u : P 0 ≤ N 1 + N 2 := by rw [hP0, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  have hp1n : 0 ≤ P 1 := by rw [hP1]; exact lpNorm_nonneg p _
  have hp1u : P 1 ≤ N 0 + N 2 := by rw [hP1, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  have hp2n : 0 ≤ P 2 := by rw [hP2]; exact lpNorm_nonneg p _
  have hp2u : P 2 ≤ N 0 + N 1 := by rw [hP2, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  let v : Fin 16 → ℝ := fun z ↦ match z.val with
    | 0 => X 0 0
    | 1 => X 0 1
    | 2 => X 0 2
    | 3 => X 1 0
    | 4 => X 1 1
    | 5 => X 1 2
    | 6 => X 2 0
    | 7 => X 2 1
    | 8 => X 2 2
    | 9 => N 0
    | 10 => N 1
    | 11 => N 2
    | 12 => P 0
    | 13 => P 1
    | 14 => P 2
    | 15 => T
    | _ => 0
  have h0 : ((-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn0]
  have h1 : ((1 : ℝ) * v 9 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt0]
  have h2 : ((-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn1]
  have h3 : ((1 : ℝ) * v 10 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt1]
  have h4 : ((-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn2]
  have h5 : ((1 : ℝ) * v 11 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt2]
  have h6 : ((-1 : ℝ) * v 15) ≤ (-1 : ℝ) := by norm_num [v]; linarith only [hT1]
  have h7 : ((1 : ℝ) * v 15) ≤ (12213/10000 : ℝ) := by norm_num [v]; linarith only [hTcap]
  have h8 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx00l]
  have h9 : ((1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx00u]
  have h10 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx01l]
  have h11 : ((1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx01u]
  have h12 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx02l]
  have h13 : ((1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx02u]
  have h14 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx10l]
  have h15 : ((1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx10u]
  have h16 : ((-1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx11l]
  have h17 : ((1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx11u]
  have h18 : ((-1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx12l]
  have h19 : ((1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx12u]
  have h20 : ((-1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx20l]
  have h21 : ((1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx20u]
  have h22 : ((-1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx21l]
  have h23 : ((1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx21u]
  have h24 : ((-1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx22l]
  have h25 : ((1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx22u]
  have h26 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht0l]
  have h27 : ((1 : ℝ) * v 0 + (1 : ℝ) * v 3 + (1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht0u]
  have h28 : ((-1 : ℝ) * v 12) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp0n]
  have h29 : ((-1 : ℝ) * v 10 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 12) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp0u]
  have h30 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (27/200 : ℝ) := by norm_num [v]; linarith only [hmain0]
  have h31 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 4 + (-1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht1l]
  have h32 : ((1 : ℝ) * v 1 + (1 : ℝ) * v 4 + (1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht1u]
  have h33 : ((-1 : ℝ) * v 13) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp1n]
  have h34 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 13) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp1u]
  have h35 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (27/200 : ℝ) := by norm_num [v]; linarith only [hmain1]
  have h36 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (-1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht2l]
  have h37 : ((1 : ℝ) * v 2 + (1 : ℝ) * v 5 + (1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht2u]
  have h38 : ((-1 : ℝ) * v 14) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp2n]
  have h39 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 10 + (1 : ℝ) * v 14) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp2u]
  have h40 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (27/200 : ℝ) := by norm_num [v]; linarith only [hmain2]
  have h41 : ((-1741/200 : ℝ) * v 12 + (-1741/200 : ℝ) * v 13 + (-1741/200 : ℝ) * v 14 + (1 : ℝ) * v 15) ≤ (-4923/100 : ℝ) := by norm_num [v]; linarith only [hfail]
  have heq : ((1 : ℝ) * v 9 + (1 : ℝ) * v 10 + (1 : ℝ) * v 11) = (3 : ℝ) := by norm_num [v]; linarith only [hS]
  have first := coarse_stage0_w024 v h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 heq
  norm_num [v] at first
  rcases first with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
  have tail0 : P 0 ≤ X 1 0 + X 2 0 + 1/100000 := by
    rw [hP0, lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply half_tail16 hp16 (by linarith only [a0]) (by linarith only [a1])
      (abs_le.mpr ⟨by linarith only [a3], by linarith only [a2]⟩)
      (abs_le.mpr ⟨by linarith only [a5], by linarith only [a4]⟩)
  have tail1 : P 1 ≤ X 0 1 + X 2 1 + 1/100000 := by
    rw [hP1, lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply half_tail16 hp16 (by linarith only [a6]) (by linarith only [a7])
      (abs_le.mpr ⟨by linarith only [a9], by linarith only [a8]⟩)
      (abs_le.mpr ⟨by linarith only [a11], by linarith only [a10]⟩)
  have tail2 : P 2 ≤ X 0 2 + X 1 2 + 1/100000 := by
    rw [hP2, lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply half_tail16 hp16 (by linarith only [a12]) (by linarith only [a13])
      (abs_le.mpr ⟨by linarith only [a15], by linarith only [a14]⟩)
      (abs_le.mpr ⟨by linarith only [a17], by linarith only [a16]⟩)
  have h42 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (1 / 100000 : ℝ) := by norm_num [v]; linarith only [tail0]
  have h43 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (1 / 100000 : ℝ) := by norm_num [v]; linarith only [tail1]
  have h44 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (1 / 100000 : ℝ) := by norm_num [v]; linarith only [tail2]
  have second := coarse_stage1_w024 v h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 heq
  norm_num [v] at second
  rcases second with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29⟩
  have refined0 : P 0 ≤ X 1 0 + X 2 0 + 1/100000000 := by
    rw [hP0, lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 16 (by norm_num) hp16
      (by linarith only [a0]) (by linarith only [a1]) (by norm_num)
      (show (0 : ℝ) ≤ 1/3 by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [b19], by linarith only [b18]⟩
    · exact abs_le.mpr ⟨by linarith only [b21], by linarith only [b20]⟩
    · norm_num
  rw [hP0] at refined0
  have refined1 : P 1 ≤ X 0 1 + X 2 1 + 1/100000000 := by
    rw [hP1, lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 16 (by norm_num) hp16
      (by linarith only [a6]) (by linarith only [a7]) (by norm_num)
      (show (0 : ℝ) ≤ 1/3 by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [b23], by linarith only [b22]⟩
    · exact abs_le.mpr ⟨by linarith only [b25], by linarith only [b24]⟩
    · norm_num
  rw [hP1] at refined1
  have refined2 : P 2 ≤ X 0 2 + X 1 2 + 1/100000000 := by
    rw [hP2, lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 16 (by norm_num) hp16
      (by linarith only [a12]) (by linarith only [a13]) (by norm_num)
      (show (0 : ℝ) ≤ 1/3 by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [b27], by linarith only [b26]⟩
    · exact abs_le.mpr ⟨by linarith only [b29], by linarith only [b28]⟩
    · norm_num
  rw [hP2] at refined2
  constructor
  ·
    intro j i
    fin_cases j <;> fin_cases i
    · rw [if_pos rfl]
      change -(12213/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(353/1000 : ℝ)
      constructor <;> linarith only [b0, b1]
    · change (137/200 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (12213/10000 : ℝ)
      constructor <;> linarith only [b2, b3]
    · change (137/200 : ℝ) ≤ X 0 2 ∧ X 0 2 ≤ (12213/10000 : ℝ)
      constructor <;> linarith only [b4, b5]
    · change (137/200 : ℝ) ≤ X 1 0 ∧ X 1 0 ≤ (12213/10000 : ℝ)
      constructor <;> linarith only [b6, b7]
    · rw [if_pos rfl]
      change -(12213/10000 : ℝ) ≤ X 1 1 ∧ X 1 1 ≤ -(353/1000 : ℝ)
      constructor <;> linarith only [b8, b9]
    · change (137/200 : ℝ) ≤ X 1 2 ∧ X 1 2 ≤ (12213/10000 : ℝ)
      constructor <;> linarith only [b10, b11]
    · change (137/200 : ℝ) ≤ X 2 0 ∧ X 2 0 ≤ (12213/10000 : ℝ)
      constructor <;> linarith only [b12, b13]
    · change (137/200 : ℝ) ≤ X 2 1 ∧ X 2 1 ≤ (12213/10000 : ℝ)
      constructor <;> linarith only [b14, b15]
    · rw [if_pos rfl]
      change -(12213/10000 : ℝ) ≤ X 2 2 ∧ X 2 2 ≤ -(353/1000 : ℝ)
      constructor <;> linarith only [b16, b17]
  · intro i j k hij hik hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
    · change lpNorm p (X 1 + X 2) ≤ X 1 0 + X 2 0 + 1/100000000
      simpa only [add_comm, add_left_comm, add_assoc] using refined0
    · change lpNorm p (X 2 + X 1) ≤ X 2 0 + X 1 0 + 1/100000000
      simpa only [add_comm, add_left_comm, add_assoc] using refined0
    · change lpNorm p (X 0 + X 2) ≤ X 0 1 + X 2 1 + 1/100000000
      simpa only [add_comm, add_left_comm, add_assoc] using refined1
    · change lpNorm p (X 2 + X 0) ≤ X 2 1 + X 0 1 + 1/100000000
      simpa only [add_comm, add_left_comm, add_assoc] using refined1
    · change lpNorm p (X 0 + X 1) ≤ X 0 2 + X 1 2 + 1/100000000
      simpa only [add_comm, add_left_comm, add_assoc] using refined2
    · change lpNorm p (X 1 + X 0) ≤ X 1 2 + X 0 2 + 1/100000000
      simpa only [add_comm, add_left_comm, add_assoc] using refined2

theorem coarse_w024 (p : ℝ) (hp : (20 : ℝ) ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (d : OrientedData p (4071/10000 : ℝ) (1741/4000 : ℝ) (20 : ℝ) (27/200 : ℝ) X) :
    coordinateBox (353/1000 : ℝ) (12213/10000 : ℝ) (137/200 : ℝ) (12213/10000 : ℝ) X ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j + X k) ≤ X j i + X k i + 1/100000000) := by
  exact coarse_oriented_w024 p (by linarith) X (fun i ↦ lpNorm p (X i))
    ![lpNorm p (X 1 + X 2), lpNorm p (X 0 + X 2), lpNorm p (X 0 + X 1)]
    (lpNorm p (X 0 + X 1 + X 2)) (fun _ ↦ rfl) rfl rfl rfl rfl
    d.sum d.norm_le_total d.total_one (by have h := d.total_cap; linarith) d.main0 d.main1 d.main2
    (by convert d.linear_failure using 1 <;> norm_num <;> rfl)

end HlawkaSchatten.DiagonalCutoff16

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option maxHeartbeats 4000000
theorem HlawkaSchatten.DiagonalCutoff16.coarse_failure_window24 (p : ℝ) (hpa : (20 : ℝ) ≤ p) (hpb : p ≤ (21 : ℝ))
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ,
      ((1741/4000 : ℝ)*p ≤ cyclicConstant p) ∧ (cyclicConstant p ≤ p/2) ∧
      (∀ j i, if j = i then -(12213/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(353/1000 : ℝ)
        else (137/200 : ℝ) ≤ X j i ∧ X j i ≤ (12213/10000 : ℝ)) ∧
      (lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3) ∧
      (1 ≤ lpNorm p (X 0 + X 1 + X 2)) ∧
      (lpNorm p (X 0 + X 1 + X 2) < (12213/10000 : ℝ)) ∧
      (((1741/4000 : ℝ)*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j + X k) ≤ X j i + X k i + (1/100000000 : ℝ)) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by
  have hk := HlawkaSchatten.DiagonalCutoff16.scalar_lower_w024 p hpa hpb
  have he := (HlawkaSchatten.DiagonalCutoff16.envelope_w024 p hpa).trans hk
  obtain ⟨X,hX⟩ := HlawkaSchatten.DiagonalCutoff16.exists_oriented_failure
    (α := (20 : ℝ)) (c := (1741/4000 : ℝ)) (q := (4071/10000 : ℝ)) (E := (27/200 : ℝ)) (g := (400/1741 : ℝ))
    (by norm_num) hpa (by norm_num) (by norm_num) hk (by norm_num) (by norm_num)
    he (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y z hf
  have hc := HlawkaSchatten.DiagonalCutoff16.coarse_w024 p (by linarith) X hX
  have hfailure : ((1741/4000 : ℝ)*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3 := by
    have hneg := hX.failure
    change hlawkaDeficit p (cyclicConstant p) (X 0) (X 1) (X 2) < 0 at hneg
    rw [hlawkaDeficit_eq, tripleGap, hX.sum] at hneg
    have hcmp := mul_le_mul_of_nonneg_right hk.le (pairGapSum_nonneg (p := p) (by linarith) (X 0) (X 1) (X 2))
    linarith
  refine ⟨X,hk.le,HlawkaSchatten.DiagonalCutoff16Scalar.cyclicConstant_upper16 (by linarith) (by linarith),
    hc.1,hX.sum,hX.total_one,?_,hfailure,hc.2,hX.failure⟩
  have ht := hX.total_cap
  linarith


theorem solution (p : ℝ) (hpa : (20 : ℝ) ≤ p) (hpb : p ≤ (21 : ℝ))
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ,
      ((1741/4000 : ℝ)*p ≤ cyclicConstant p) ∧ (cyclicConstant p ≤ p/2) ∧
      (∀ j i, if j = i then -(12213/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(353/1000 : ℝ)
        else (137/200 : ℝ) ≤ X j i ∧ X j i ≤ (12213/10000 : ℝ)) ∧
      (lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3) ∧
      (1 ≤ lpNorm p (X 0 + X 1 + X 2)) ∧
      (lpNorm p (X 0 + X 1 + X 2) < (12213/10000 : ℝ)) ∧
      (((1741/4000 : ℝ)*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j + X k) ≤ X j i + X k i + (1/100000000 : ℝ)) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by
  have hk := HlawkaSchatten.DiagonalCutoff16.scalar_lower_w024 p hpa hpb
  have he := (HlawkaSchatten.DiagonalCutoff16.envelope_w024 p hpa).trans hk
  obtain ⟨X,hX⟩ := HlawkaSchatten.DiagonalCutoff16.exists_oriented_failure
    (α := (20 : ℝ)) (c := (1741/4000 : ℝ)) (q := (4071/10000 : ℝ)) (E := (27/200 : ℝ)) (g := (400/1741 : ℝ))
    (by norm_num) hpa (by norm_num) (by norm_num) hk (by norm_num) (by norm_num)
    he (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y z hf
  have hc := HlawkaSchatten.DiagonalCutoff16.coarse_w024 p (by linarith) X hX
  have hfailure : ((1741/4000 : ℝ)*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3 := by
    have hneg := hX.failure
    change hlawkaDeficit p (cyclicConstant p) (X 0) (X 1) (X 2) < 0 at hneg
    rw [hlawkaDeficit_eq, tripleGap, hX.sum] at hneg
    have hcmp := mul_le_mul_of_nonneg_right hk.le (pairGapSum_nonneg (p := p) (by linarith) (X 0) (X 1) (X 2))
    linarith
  refine ⟨X,hk.le,HlawkaSchatten.DiagonalCutoff16Scalar.cyclicConstant_upper16 (by linarith) (by linarith),
    hc.1,hX.sum,hX.total_one,?_,hfailure,hc.2,hX.failure⟩
  have ht := hX.total_cap
  linarith

#print axioms solution
