-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_34
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T14:37:13.011197+00:00
-- url     : https://prove2.me/submissions/cb78b6c0-06b8-4121-9d41-25a03631d5ca

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


/- The contraction rounds of @bwdaugherty's cutoff-32 proof, generalized
   to arbitrary nonnegative singleton sizes and rational output boxes.
   Source: submission d75400b0-5a0e-4167-8192-7fd299469c2e, Apache-2.0.
   Paper Section 4: diagonal/ratio bounds, lower update, upper update,
   and final box. N will be instantiated with the original lpNorm. -/
set_option autoImplicit false

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



/- Coordinate lemmas adapted from the attributed cutoff-32 implementation;
   original lpNorm definition by Ezzeri Esa, Apache-2.0. -/
set_option autoImplicit false

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


/- Residual-budget monotonicity from paper Section 4, with the coefficient
   generalized from the attributed cutoff-32 implementation. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

theorem mono_deficit {c alpha p : ℝ} (hc : 0 < c) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hcrit : 6 * Real.log 2 ≤ 2 / c) :
    6 * (1 / 2 : ℝ) ^ (1 / p) + 2 / (c * p) ≤
      6 * (1 / 2 : ℝ) ^ (1 / alpha) + 2 / (c * alpha) := by
  have hp : 0 < p := ha.trans_le hap
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e (r : ℝ) : (1 / 2 : ℝ) ^ r = Real.exp (-(Real.log 2 * r)) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]
    ring_nf
  rw [e, e]
  have huw : 1 / p ≤ 1 / alpha := one_div_le_one_div_of_le ha hap
  set u := 1 / p with hu_def
  set w := 1 / alpha with hw_def
  set L := Real.log 2
  have h1 : Real.exp (-(L * w)) = Real.exp (-(L * u)) * Real.exp (-(L * (w - u))) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : 1 - L * (w - u) ≤ Real.exp (-(L * (w - u))) := by
    have := Real.add_one_le_exp (-(L * (w - u)))
    linarith
  have h3 : Real.exp (-(L * u)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have hLu : 0 ≤ L * u := mul_nonneg hL0.le (by positivity)
    linarith)
  have h4 := Real.exp_pos (-(L * u))
  have g1 : 2 / (c * p) = 2 / c * u := by rw [hu_def]; field_simp
  have g2 : 2 / (c * alpha) = 2 / c * w := by rw [hw_def]; field_simp
  rw [g1, g2, h1]
  have hwu : 0 ≤ w - u := sub_nonneg.mpr huw
  have h5 : 0 ≤ (2 / c - 6 * L) * (w - u) :=
    mul_nonneg (sub_nonneg.mpr hcrit) hwu
  have h6 : 0 ≤ 6 * L * (w - u) * (1 - Real.exp (-(L * u))) :=
    mul_nonneg (mul_nonneg (by positivity) hwu) (sub_nonneg.mpr h3)
  have h7 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 6 * Real.exp (-(L * u)) by positivity)
  nlinarith

theorem residual_budget {c alpha p eps D thia W : ℝ}
    (hc : 0 < c) (ha : 0 < alpha) (hap : alpha ≤ p)
    (hcrit : 6 * Real.log 2 ≤ 2 / c)
    (hthia : (1 / 2 : ℝ) ^ (1 / alpha) ≤ thia)
    (hW : 6 - 2 / (c * p) - 3 * eps < W)
    (hD : 2 / (c * alpha) + 3 * eps - 6 * (1 - thia) ≤ D) :
    cp p * 3 - W < D := by
  have hm := mono_deficit hc ha hap hcrit
  unfold cp
  linarith

end HlawkaSchatten.DiagonalRealBundle



/- Normalized norm data imply every premise used by the contraction rounds.
   Adapted from @bwdaugherty's cutoff-32 facts_of; all cutoff, box, gap and
   tail constants are parameters, with the original lpNorm unchanged. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

def coordinateBox (ell u v w : ℝ) (X : Triple) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w

theorem facts_of {p α β tlo thia thib D δ h A c eps ell u v w : ℝ} {X : Triple}
    (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β) (hp1 : 1 ≤ p)
    (hc0 : 0 < c) (hcrit : 6 * Real.log 2 ≤ 2 / c)
    (hell : 0 < ell) (hv : 0 < v) (hA : 0 < A)
    (htlo0 : 0 < tlo) (htlo : tlo ≤ (1/2 : ℝ) ^ (1/α))
    (hthia : (1/2 : ℝ) ^ (1/α) ≤ thia) (hthib : (1/2 : ℝ) ^ (1/β) ≤ thib)
    (hD : 2 / (c * α) + 3 * eps - 6 * (1 - thia) ≤ D) (hD0 : 0 ≤ D)
    (hδ : D / (2 * tlo) ≤ δ) (hh : 2 / (c * α) + 3 * eps ≤ h)
    (hB : coordinateBox ell u v w X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < A)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / (c * p))
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
  have hoffsum0 : 6 - 2 / (c * p) - 3 * eps <
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    unfold pairGapSum pairGap at hG
    have t01 := htail 2 0 1 (by decide) (by decide) (by decide)
    have t02 := htail 1 0 2 (by decide) (by decide) (by decide)
    have t12 := htail 0 1 2 (by decide) (by decide) (by decide)
    linarith
  have hg : 2 / (c * p) ≤ 2 / (c * α) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hαp hc0.le)
  have hmono := mono_deficit hc0 hα hαp hcrit
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


/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 134, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab134 (p : ℝ) (hpa : (403/16 : ℝ) ≤ p) (hpb : p ≤ (807/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (520421178191/27504750000000 : ℝ) (1944907/200000000 : ℝ) (2000000330057/11001900000000 : ℝ) (3033/2500 : ℝ) (972888897/500000000 : ℝ) (24321393/25000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194075709/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2793/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(933/2000 : ℝ)
      else (3907/5000 : ℝ) ≤ X j i ∧ X j i ≤ (5929/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (520421178191/27504750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1944907/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (184895129/200000000 : ℝ) ^ p + (994128147/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (184895129/200000000 : ℝ)) (y := (994128147/1000000000 : ℝ)) (X := (13801506446123/100000000000000 : ℝ)) (Y := (17239702642647/20000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994128147/1000000000 : ℝ) ^ p + (184895129/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (994128147/1000000000 : ℝ)) (y := (184895129/200000000 : ℝ)) (X := (17239702642647/20000000000000 : ℝ)) (Y := (13801506446123/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (119912737/62500000 : ℝ)) (τ := (184895129/200000000 : ℝ)) (σ := (994128147/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (263226561/277832114 : ℝ) ^ p + (823771807/833496342 : ℝ) ^ p := by
    exact cert_lt (x := (263226561/277832114 : ℝ)) (y := (823771807/833496342 : ℝ)) (X := (12809181482727/50000000000000 : ℝ)) (Y := (14876327605493/20000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (184895129/200000000 : ℝ)) (n' := (416748171/500000000 : ℝ)) (Ab := (789679683/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (464948907/500000000 : ℝ) ^ p + (9931127/10000000 : ℝ) ^ p := by
    exact cert_lt (x := (464948907/500000000 : ℝ)) (y := (9931127/10000000 : ℝ)) (X := (15994691767227/100000000000000 : ℝ)) (Y := (84005326208873/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (9931127/10000000 : ℝ) ^ p + (464948907/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (9931127/10000000 : ℝ)) (y := (464948907/500000000 : ℝ)) (X := (84005326208873/100000000000000 : ℝ)) (Y := (15994691767227/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (961505257/500000000 : ℝ)) (τ := (464948907/500000000 : ℝ)) (σ := (9931127/10000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (795505247/839864337 : ℝ) ^ p + (830139802/839864337 : ℝ) ^ p := by
    exact cert_lt (x := (795505247/839864337 : ℝ)) (y := (830139802/839864337 : ℝ)) (X := (795321356907/3125000000000 : ℝ)) (Y := (18637429462131/25000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (464948907/500000000 : ℝ)) (n' := (839864337/1000000000 : ℝ)) (Ab := (795505247/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (186022811/200000000 : ℝ) ^ p + (993068581/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (186022811/200000000 : ℝ)) (y := (993068581/1000000000 : ℝ)) (X := (8044378125391/50000000000000 : ℝ)) (Y := (83911262112347/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993068581/1000000000 : ℝ) ^ p + (186022811/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993068581/1000000000 : ℝ)) (y := (186022811/200000000 : ℝ)) (X := (83911262112347/100000000000000 : ℝ)) (Y := (8044378125391/50000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (480795659/250000000 : ℝ)) (τ := (186022811/200000000 : ℝ)) (σ := (993068581/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795736847/840117542 : ℝ) ^ p + (830393007/840117542 : ℝ) ^ p := by
    exact cert_lt (x := (795736847/840117542 : ℝ)) (y := (830393007/840117542 : ℝ)) (X := (5088728997257/20000000000000 : ℝ)) (Y := (74556355859393/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (186022811/200000000 : ℝ)) (n' := (420058771/500000000 : ℝ)) (Ab := (795736847/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (930122593/1000000000 : ℝ) ^ p + (993066833/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (930122593/1000000000 : ℝ)) (y := (993066833/1000000000 : ℝ)) (X := (2011560143451/12500000000000 : ℝ)) (Y := (83907537365687/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993066833/1000000000 : ℝ) ^ p + (930122593/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993066833/1000000000 : ℝ)) (y := (930122593/1000000000 : ℝ)) (X := (83907537365687/100000000000000 : ℝ)) (Y := (2011560143451/12500000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (961594713/500000000 : ℝ)) (τ := (930122593/1000000000 : ℝ)) (σ := (993066833/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (397872995/420063769 : ℝ) ^ p + (17668149/17875054 : ℝ) ^ p := by
    exact cert_lt (x := (397872995/420063769 : ℝ)) (y := (17668149/17875054 : ℝ)) (X := (12721691483241/50000000000000 : ℝ)) (Y := (74556617843623/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (930122593/1000000000 : ℝ)) (n' := (420063769/500000000 : ℝ)) (Ab := (79574599/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (93012293/100000000 : ℝ) ^ p + (248266691/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (93012293/100000000 : ℝ)) (y := (248266691/250000000 : ℝ)) (X := (16092628188517/100000000000000 : ℝ)) (Y := (83907390339471/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248266691/250000000 : ℝ) ^ p + (93012293/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (248266691/250000000 : ℝ)) (y := (93012293/100000000 : ℝ)) (X := (83907390339471/100000000000000 : ℝ)) (Y := (16092628188517/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961594847/500000000 : ℝ)) (τ := (93012293/100000000 : ℝ)) (σ := (248266691/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (795746352/840127933 : ℝ) ^ p + (830403398/840127933 : ℝ) ^ p := by
    exact cert_lt (x := (795746352/840127933 : ℝ)) (y := (830403398/840127933 : ℝ)) (X := (5088674636563/20000000000000 : ℝ)) (Y := (74556628196031/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (93012293/100000000 : ℝ)) (n' := (840127933/1000000000 : ℝ)) (Ab := (49734147/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (14533171/15625000 : ℝ) ^ p + (993066761/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (14533171/15625000 : ℝ)) (y := (993066761/1000000000 : ℝ)) (X := (16092634297069/100000000000000 : ℝ)) (Y := (83907383947033/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993066761/1000000000 : ℝ) ^ p + (14533171/15625000 : ℝ) ^ p := by
    exact cert_lt (x := (993066761/1000000000 : ℝ)) (y := (14533171/15625000 : ℝ)) (X := (83907383947033/100000000000000 : ℝ)) (Y := (16092634297069/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795746366/840127949 : ℝ) ^ p + (830403414/840127949 : ℝ) ^ p := by
    exact cert_lt (x := (795746366/840127949 : ℝ)) (y := (830403414/840127949 : ℝ)) (X := (2544337225167/10000000000000 : ℝ)) (Y := (74556628615369/100000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (n' := (840127949/1000000000 : ℝ)) (Ab := (397873183/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (384637941/200000000 : ℝ)) (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1664191994/1805924291 : ℝ) ^ p + (1796199756/1805924291 : ℝ) ^ p := by
    exact cert_lt (x := (1664191994/1805924291 : ℝ)) (y := (1796199756/1805924291 : ℝ)) (X := (3182529617131/25000000000000 : ℝ)) (Y := (8726988179951/10000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1117115264/1194075709 : ℝ) ^ p + (1184351174/1194075709 : ℝ) ^ p := by
    exact cert_lt (x := (1117115264/1194075709 : ℝ)) (y := (1184351174/1194075709 : ℝ)) (X := (18634758670113/100000000000000 : ℝ)) (Y := (16273048380961/20000000000000 : ℝ)) 807 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993066761/1000000000 : ℝ)) (U := (1194075709/1000000000 : ℝ)) (Ab := (832095997/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (14533171/15625000 : ℝ)) (σ := (993066761/1000000000 : ℝ)) (Ab := (8727463/7812500 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Norm laws from @bwdaugherty's accepted cutoff-32 coarse localization,
   submission d5944a03-85b4-4962-b146-4e6c7e7e50c7, Apache-2.0,
   based on Ezzeri Esa's original coordinate lpNorm definition. -/
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

section Basic
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end Basic

end HlawkaSchatten.DiagonalRealBundle


/- Pair-tail bounds from Section 3 of the cutoff-21 paper. The finite
   numerical premise is an integer-power rational inequality, not an
   assumption that an external checker succeeded. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

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

theorem half_tail21 {p S y1 y2 : ℝ} (hp : 21 ≤ p)
    (hS : 0 ≤ S) (hS3 : S ≤ 3) (hy1 : |y1| ≤ S / 2) (hy2 : |y2| ≤ S / 2) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000 := by
  apply two_tail_norm_bound 21 (by norm_num) hp hS hS3 (by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem refined_tail21 {p S y1 y2 : ℝ} (hp : 21 ≤ p)
    (hS : 349 / 250 ≤ S) (hS3 : S ≤ 3)
    (hy1 : |y1| ≤ 129 / 250) (hy2 : |y2| ≤ 129 / 250) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000000 := by
  apply two_tail_norm_bound 21 (by norm_num) hp (by linarith) hS3 (by norm_num)
    (show (0 : ℝ) ≤ 129 / 349 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem refined_tail26 {p S y1 y2 : ℝ} (hp : 26 ≤ p)
    (hS : 3 / 2 ≤ S) (hS3 : S ≤ 3)
    (hy1 : |y1| ≤ 353 / 500) (hy2 : |y2| ≤ 353 / 500) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000000 := by
  apply two_tail_norm_bound 26 (by norm_num) hp (by linarith) hS3 (by norm_num)
    (show (0 : ℝ) ≤ 353 / 750 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem clip_pair_tail {ell u v w A diagonal off total excluded y : ℝ}
    (hd : -u ≤ diagonal ∧ diagonal ≤ -ell) (ho : v ≤ off ∧ off ≤ w)
    (hV : total ≤ A) (hx : v ≤ excluded)
    (hpair : y = diagonal + off) (hclip : y = total - excluded) :
    v - u ≤ y ∧ y ≤ min (w - ell) (A - v) := by
  constructor
  · linarith [hd.1, ho.1]
  · apply le_min <;> linarith [hd.2, ho.2]

end HlawkaSchatten.DiagonalRealBundle



/- Paper Section 3.2: the actual pair norm, rather than an independent
   scalar surrogate, has a uniformly small non-main contribution. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction

theorem total_coordinate_perm {p A : ℝ} (hp : 1 ≤ p) (X : Triple)
    (hT : lpNorm p (X 0 + X 1 + X 2) ≤ A)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : Fin 3) :
    X i r + X j r + X k r ≤ A := by
  have hc := norm_apply_le_lpNorm hp (X 0 + X 1 + X 2) r
  simp only [Pi.add_apply, Real.norm_eq_abs] at hc
  have hs := sum3 (fun l ↦ X l r) hij hik hjk
  rw [Fin.sum_univ_three] at hs
  linarith [le_abs_self (X 0 r + X 1 r + X 2 r)]

theorem refined_pair_tail21 {p : ℝ} (hp : 21 ≤ p) (X : Triple)
    (hB : coordinateBox (189/500) (607/500) (349/500) (607/500) X)
    (hT : lpNorm p (X 0 + X 1 + X 2) ≤ 3033/2500) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + 1/100000000 := by
  have hp1 : 1 ≤ p := by linarith
  have hd (i : Fin 3) : -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ) := by
    simpa [coordinateBox] using hB i i
  have ho (j i : Fin 3) (hji : j ≠ i) : (349/500 : ℝ) ≤ X j i ∧ X j i ≤ 607/500 := by
    simpa [coordinateBox, hji] using hB j i
  intro i j k hij hik hjk
  have hji := ho j i hij.symm
  have hki := ho k i hik.symm
  have hkj := ho k j hjk.symm
  have hjk' := ho j k hjk
  have hij' := ho i j hij
  have hik' := ho i k hik
  have hvj := total_coordinate_perm hp1 X hT hij hik hjk j
  have hvk := total_coordinate_perm hp1 X hT hij hik hjk k
  have hj := hd j
  have hk := hd k
  rw [lpNorm_eq3 p _ hij hik hjk]
  simp only [Pi.add_apply]
  apply refined_tail21 hp (by linarith) (by linarith)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem refined_pair_tail26 {p : ℝ} (hp : 26 ≤ p) (X : Triple)
    (hB : coordinateBox (477/1000) (1183/1000) (3/4) (1183/1000) X) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + 1/100000000 := by
  have hd (i : Fin 3) : -(1183/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(477/1000 : ℝ) := by
    simpa [coordinateBox] using hB i i
  have ho (j i : Fin 3) (hji : j ≠ i) : (3/4 : ℝ) ≤ X j i ∧ X j i ≤ 1183/1000 := by
    simpa [coordinateBox, hji] using hB j i
  intro i j k hij hik hjk
  have hji := ho j i hij.symm
  have hki := ho k i hik.symm
  have hkj := ho k j hjk.symm
  have hjk' := ho j k hjk
  have hj := hd j
  have hk := hd k
  rw [lpNorm_eq3 p _ hij hik hjk]
  simp only [Pi.add_apply]
  apply refined_tail26 hp (by linarith) (by linarith)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem initial_norm_lower {p ell u v w : ℝ} (hp : 1 ≤ p) (X : Triple)
    (hB : coordinateBox ell u v w X) : ∀ i, v ≤ lpNorm p (X i) := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  have hx : v ≤ X i j := by
    have h : v ≤ X i j ∧ X i j ≤ w := by simpa [coordinateBox, hij] using hB i j
    exact h.1
  have hc := norm_apply_le_lpNorm hp (X i) j
  rw [Real.norm_eq_abs] at hc
  exact hx.trans ((le_abs_self _).trans hc)

end HlawkaSchatten.DiagonalRealBundle



/- The linear pair and offsum floors retained in the convex domain.
   They follow from the original norms, not from independent certificates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem pairGapSum_perm (p : ℝ) (X : Triple) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pairGapSum (lpNorm p) (X i) (X j) (X k) =
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) := by
  have h10 : lpNorm p (X 1 + X 0) = lpNorm p (X 0 + X 1) := by rw [add_comm]
  have h20 : lpNorm p (X 2 + X 0) = lpNorm p (X 0 + X 2) := by rw [add_comm]
  have h21 : lpNorm p (X 2 + X 1) = lpNorm p (X 1 + X 2) := by rw [add_comm]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  all_goals simp only [pairGapSum, pairGap, h10, h20, h21]; ring

theorem pair_floor_of_norm_data {p a c U eps : ℝ} (hp : 1 ≤ p)
    (ha : 0 < a) (hap : a ≤ p) (hc : 0 < c) (X : Triple)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hU : ∀ i, lpNorm p (X i) ≤ U)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / (c * p))
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + eps) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      3 - U - 2 / (c * a) - eps ≤ X j i + X k i := by
  intro i j k hij hik hjk
  have hperm := pairGapSum_perm p X hij hik hjk
  have hg := hG
  rw [← hperm] at hg
  have h1 := pairGap_nonneg hp (X i) (X j)
  have h2 := pairGap_nonneg hp (X i) (X k)
  have hsum := sum3 (fun l ↦ lpNorm p (X l)) hij hik hjk
  rw [Fin.sum_univ_three] at hsum
  have hratio : 2 / (c * p) ≤ 2 / (c * a) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hap hc.le)
  have ht := htail i j k hij hik hjk
  have hi := hU i
  dsimp only [pairGapSum, pairGap] at hg h1 h2
  linarith

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab134 (p : ℝ) (hpa : (403/16 : ℝ) ≤ p) (hpb : p ≤ (807/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1194075709/1000000000 : ℝ)) ∧ coordinateBox (933/2000 : ℝ) (2793/2500 : ℝ) (3907/5000 : ℝ) (5929/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (178685983471339/110019000000000 : ℝ) ≤ X j i + X k i) ∧
    (64011399669943/11001900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (24321393/25000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(403/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (24321393/25000000 : ℝ))
      (by norm_num) 16 403 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(403/16 : ℝ)) ≤ (972855721/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (972855721/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 403 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(807/32 : ℝ)) ≤ (972888897/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (972888897/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 807 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (520421178191/27504750000000 : ℝ) (1944907/200000000 : ℝ) (2000000330057/11001900000000 : ℝ) (3033/2500 : ℝ) (972888897/500000000 : ℝ) (24321393/25000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (403/16 : ℝ)) (β := (807/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (520421178191/27504750000000 : ℝ)) (δ := (1944907/200000000 : ℝ)) (h := (2000000330057/11001900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (24321393/25000000 : ℝ)) (thia := (972855721/1000000000 : ℝ)) (thib := (972888897/1000000000 : ℝ))
      (ell := (189/500 : ℝ)) (u := (607/500 : ℝ))
      (v := (349/500 : ℝ)) (w := (607/500 : ℝ))
      (by norm_num) hpa hpb hp1 (by norm_num) hcrit
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) htlo hthia hthib
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hB hS hT hG htail
    norm_num at facts
    exact facts
  have hn0 := initial_norm_lower hp1 X hB
  have hh := contract21_slab134 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 135, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab135 (p : ℝ) (hpa : (807/32 : ℝ) ≤ p) (hpb : p ≤ (101/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1040690332783/55077750000000 : ℝ) (1942147/200000000 : ℝ) (4000000660933/22031100000000 : ℝ) (3033/2500 : ℝ) (121615249/62500000 : ℝ) (15201389/15625000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (37315261/31250000 : ℝ)) ∧
    (∀ j i, if j = i then -(11173/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(2333/5000 : ℝ)
      else (1563/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11859/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1040690332783/55077750000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (1942147/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (924573711/1000000000 : ℝ) ^ p + (497066989/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (924573711/1000000000 : ℝ)) (y := (497066989/500000000 : ℝ)) (X := (6902301202149/50000000000000 : ℝ)) (Y := (86195415785447/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497066989/500000000 : ℝ) ^ p + (924573711/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (497066989/500000000 : ℝ)) (y := (924573711/1000000000 : ℝ)) (X := (86195415785447/100000000000000 : ℝ)) (Y := (6902301202149/50000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1918707689/1000000000 : ℝ)) (τ := (924573711/1000000000 : ℝ)) (σ := (497066989/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (789809323/833585920 : ℝ) ^ p + (164775037/166717184 : ℝ) ^ p := by
    exact cert_lt (x := (789809323/833585920 : ℝ)) (y := (164775037/166717184 : ℝ)) (X := (3201475050543/12500000000000 : ℝ)) (Y := (743882012121/1000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (924573711/1000000000 : ℝ)) (n' := (651239/781250 : ℝ)) (Ab := (789809323/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (464995807/500000000 : ℝ) ^ p + (99311913/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (464995807/500000000 : ℝ)) (y := (99311913/100000000 : ℝ)) (X := (7999550286509/50000000000000 : ℝ)) (Y := (84000916903023/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (99311913/100000000 : ℝ) ^ p + (464995807/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (99311913/100000000 : ℝ)) (y := (464995807/500000000 : ℝ)) (X := (84000916903023/100000000000000 : ℝ)) (Y := (7999550286509/50000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (240388843/125000000 : ℝ)) (τ := (464995807/500000000 : ℝ)) (σ := (99311913/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (113661437/119992572 : ℝ) ^ p + (830237269/839948004 : ℝ) ^ p := by
    exact cert_lt (x := (113661437/119992572 : ℝ)) (y := (830237269/839948004 : ℝ)) (X := (25443930257421/100000000000000 : ℝ)) (Y := (18639017823467/25000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (464995807/500000000 : ℝ)) (n' := (209987001/250000000 : ℝ)) (Ab := (795630059/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (232551831/250000000 : ℝ) ^ p + (993075109/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232551831/250000000 : ℝ)) (y := (993075109/1000000000 : ℝ)) (X := (3218613285767/20000000000000 : ℝ)) (Y := (41953475469887/50000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993075109/1000000000 : ℝ) ^ p + (232551831/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993075109/1000000000 : ℝ)) (y := (232551831/250000000 : ℝ)) (X := (41953475469887/50000000000000 : ℝ)) (Y := (3218613285767/20000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1923282433/1000000000 : ℝ)) (τ := (232551831/250000000 : ℝ)) (σ := (993075109/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795861081/840200552 : ℝ) ^ p + (830489817/840200552 : ℝ) ^ p := by
    exact cert_lt (x := (795861081/840200552 : ℝ)) (y := (830489817/840200552 : ℝ)) (X := (5087462197757/20000000000000 : ℝ)) (Y := (14912538002013/20000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (232551831/250000000 : ℝ)) (n' := (105025069/125000000 : ℝ)) (Ab := (795861081/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (465107913/500000000 : ℝ) ^ p + (124134171/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (465107913/500000000 : ℝ)) (y := (124134171/125000000 : ℝ)) (X := (4024195209329/25000000000000 : ℝ)) (Y := (41951618363561/50000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (124134171/125000000 : ℝ) ^ p + (465107913/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (124134171/125000000 : ℝ)) (y := (465107913/500000000 : ℝ)) (X := (41951618363561/50000000000000 : ℝ)) (Y := (4024195209329/25000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (961644597/500000000 : ℝ)) (τ := (465107913/500000000 : ℝ)) (σ := (124134171/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (795870186/840210505 : ℝ) ^ p + (166099954/168042101 : ℝ) ^ p := by
    exact cert_lt (x := (795870186/840210505 : ℝ)) (y := (166099954/168042101 : ℝ)) (X := (12718525258217/50000000000000 : ℝ)) (Y := (74562950785913/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (465107913/500000000 : ℝ)) (n' := (168042101/200000000 : ℝ)) (Ab := (397935093/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (465108081/500000000 : ℝ) ^ p + (993073299/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465108081/500000000 : ℝ)) (y := (993073299/1000000000 : ℝ)) (X := (1609692764807/10000000000000 : ℝ)) (Y := (1310985773863/1562500000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993073299/1000000000 : ℝ) ^ p + (465108081/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993073299/1000000000 : ℝ)) (y := (465108081/500000000 : ℝ)) (X := (1310985773863/1562500000000 : ℝ)) (Y := (1609692764807/10000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1923289461/1000000000 : ℝ)) (τ := (465108081/500000000 : ℝ)) (σ := (993073299/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (795870545/840210898 : ℝ) ^ p + (830500163/840210898 : ℝ) ^ p := by
    exact cert_lt (x := (795870545/840210898 : ℝ)) (y := (830500163/840210898 : ℝ)) (X := (5087407963021/20000000000000 : ℝ)) (Y := (74562961082691/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (465108081/500000000 : ℝ)) (n' := (420105449/500000000 : ℝ)) (Ab := (159174109/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (465108087/500000000 : ℝ) ^ p + (993073297/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465108087/500000000 : ℝ)) (y := (993073297/1000000000 : ℝ)) (X := (3219386578267/20000000000000 : ℝ)) (Y := (20975771315143/25000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993073297/1000000000 : ℝ) ^ p + (465108087/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993073297/1000000000 : ℝ)) (y := (465108087/500000000 : ℝ)) (X := (20975771315143/25000000000000 : ℝ)) (Y := (3219386578267/20000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1923289471/1000000000 : ℝ)) (τ := (465108087/500000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (44215031/46678384 : ℝ) ^ p + (830500177/840210912 : ℝ) ^ p := by
    exact cert_lt (x := (44215031/46678384 : ℝ)) (y := (830500177/840210912 : ℝ)) (X := (25437039604327/100000000000000 : ℝ)) (Y := (74562961449497/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (465108087/500000000 : ℝ)) (n' := (26256591/31250000 : ℝ)) (Ab := (397935279/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (37208647/40000000 : ℝ) ^ p + (993073297/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (37208647/40000000 : ℝ)) (y := (993073297/1000000000 : ℝ)) (X := (16096933328273/100000000000000 : ℝ)) (Y := (20975771315143/25000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993073297/1000000000 : ℝ) ^ p + (37208647/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (993073297/1000000000 : ℝ)) (y := (37208647/40000000 : ℝ)) (X := (20975771315143/25000000000000 : ℝ)) (Y := (16096933328273/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (795870559/840210913 : ℝ) ^ p + (830500178/840210913 : ℝ) ^ p := by
    exact cert_lt (x := (795870559/840210913 : ℝ)) (y := (830500178/840210913 : ℝ)) (X := (6359259911729/25000000000000 : ℝ)) (Y := (74562961475697/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (n' := (840210913/1000000000 : ℝ)) (Ab := (795870559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (n' := (840210913/1000000000 : ℝ)) (Ab := (795870559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (n' := (840210913/1000000000 : ℝ)) (Ab := (795870559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (n' := (840210913/1000000000 : ℝ)) (Ab := (795870559/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (15025699/7812500 : ℝ)) (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1664337707/1805911648 : ℝ) ^ p + (1796200913/1805911648 : ℝ) ^ p := by
    exact cert_lt (x := (1664337707/1805911648 : ℝ)) (y := (1796200913/1805911648 : ℝ)) (X := (636399864481/5000000000000 : ℝ)) (Y := (872720030849/1000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1117211313/1194088352 : ℝ) ^ p + (1184377617/1194088352 : ℝ) ^ p := by
    exact cert_lt (x := (1117211313/1194088352 : ℝ)) (y := (1184377617/1194088352 : ℝ)) (X := (18631434165539/100000000000000 : ℝ)) (Y := (81368566596637/100000000000000 : ℝ)) 101 4
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993073297/1000000000 : ℝ)) (U := (37315261/31250000 : ℝ)) (Ab := (1664337707/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (37208647/40000000 : ℝ)) (σ := (993073297/1000000000 : ℝ)) (Ab := (1117211313/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab135 (p : ℝ) (hpa : (807/32 : ℝ) ≤ p) (hpb : p ≤ (101/4 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (37315261/31250000 : ℝ)) ∧ coordinateBox (2333/5000 : ℝ) (11173/10000 : ℝ) (1563/2000 : ℝ) (11859/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (178931099439709/110155500000000 : ℝ) ≤ X j i + X k i) ∧
    (128186599339067/22031100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (15201389/15625000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(807/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (15201389/15625000 : ℝ))
      (by norm_num) 32 807 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(807/32 : ℝ)) ≤ (972888897/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (972888897/1000000000 : ℝ))
      (by norm_num) (by norm_num) 32 807 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(101/4 : ℝ)) ≤ (121615249/125000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (121615249/125000000 : ℝ))
      (by norm_num) (by norm_num) 4 101 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (1040690332783/55077750000000 : ℝ) (1942147/200000000 : ℝ) (4000000660933/22031100000000 : ℝ) (3033/2500 : ℝ) (121615249/62500000 : ℝ) (15201389/15625000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (807/32 : ℝ)) (β := (101/4 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1040690332783/55077750000000 : ℝ)) (δ := (1942147/200000000 : ℝ)) (h := (4000000660933/22031100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (15201389/15625000 : ℝ)) (thia := (972888897/1000000000 : ℝ)) (thib := (121615249/125000000 : ℝ))
      (ell := (189/500 : ℝ)) (u := (607/500 : ℝ))
      (v := (349/500 : ℝ)) (w := (607/500 : ℝ))
      (by norm_num) hpa hpb hp1 (by norm_num) hcrit
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) htlo hthia hthib
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hB hS hT hG htail
    norm_num at facts
    exact facts
  have hn0 := initial_norm_lower hp1 X hB
  have hh := contract21_slab135 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 136, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab136 (p : ℝ) (hpa : (101/4 : ℝ) ≤ p) (hpb : p ≤ (809/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (260134669843/13786500000000 : ℝ) (4848487/500000000 : ℝ) (500000082719/2757300000000 : ℝ) (3033/2500 : ℝ) (486477503/250000000 : ℝ) (972921991/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (4664457/3906250 : ℝ)) ∧
    (∀ j i, if j = i then -(5587/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1167/2500 : ℝ)
      else (7817/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11859/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (260134669843/13786500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4848487/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (462335761/500000000 : ℝ) ^ p + (994139799/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (462335761/500000000 : ℝ)) (y := (994139799/1000000000 : ℝ)) (X := (13807690401913/100000000000000 : ℝ)) (Y := (17238465614441/20000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994139799/1000000000 : ℝ) ^ p + (462335761/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (994139799/1000000000 : ℝ)) (y := (462335761/500000000 : ℝ)) (X := (17238465614441/20000000000000 : ℝ)) (Y := (13807690401913/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1918811321/1000000000 : ℝ)) (τ := (462335761/500000000 : ℝ)) (σ := (994139799/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (789938635/833675234 : ℝ) ^ p + (58855590/59548231 : ℝ) ^ p := by
    exact cert_lt (x := (789938635/833675234 : ℝ)) (y := (58855590/59548231 : ℝ)) (X := (25605256481811/100000000000000 : ℝ)) (Y := (9299343104317/12500000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462335761/500000000 : ℝ)) (n' := (416837617/500000000 : ℝ)) (Ab := (157987727/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (930085161/1000000000 : ℝ) ^ p + (19862511/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (930085161/1000000000 : ℝ)) (y := (19862511/20000000 : ℝ)) (X := (1600349731109/10000000000000 : ℝ)) (Y := (83996520347321/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (19862511/20000000 : ℝ) ^ p + (930085161/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19862511/20000000 : ℝ)) (y := (930085161/1000000000 : ℝ)) (X := (83996520347321/100000000000000 : ℝ)) (Y := (1600349731109/10000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1923210711/1000000000 : ℝ)) (τ := (930085161/1000000000 : ℝ)) (σ := (19862511/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (795754547/840031413 : ℝ) ^ p + (830334439/840031413 : ℝ) ^ p := by
    exact cert_lt (x := (795754547/840031413 : ℝ)) (y := (830334439/840031413 : ℝ)) (X := (25437595956463/100000000000000 : ℝ)) (Y := (3728120280187/5000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (930085161/1000000000 : ℝ)) (n' := (840031413/1000000000 : ℝ)) (Ab := (795754547/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (930300341/1000000000 : ℝ) ^ p + (993081627/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (930300341/1000000000 : ℝ)) (y := (993081627/1000000000 : ℝ)) (X := (3219472862899/20000000000000 : ℝ)) (Y := (20975663252183/25000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993081627/1000000000 : ℝ) ^ p + (930300341/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993081627/1000000000 : ℝ)) (y := (930300341/1000000000 : ℝ)) (X := (20975663252183/25000000000000 : ℝ)) (Y := (3219472862899/20000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (120211373/62500000 : ℝ)) (τ := (930300341/1000000000 : ℝ)) (σ := (993081627/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (795984993/840283306 : ℝ) ^ p + (415293166/420141653 : ℝ) ^ p := by
    exact cert_lt (x := (795984993/840283306 : ℝ)) (y := (415293166/420141653 : ℝ)) (X := (12715498028733/50000000000000 : ℝ)) (Y := (37284502547489/50000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (930300341/1000000000 : ℝ)) (n' := (420141653/500000000 : ℝ)) (Ab := (795984993/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (116288601/125000000 : ℝ) ^ p + (993079893/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (116288601/125000000 : ℝ)) (y := (993079893/1000000000 : ℝ)) (X := (16101068627571/100000000000000 : ℝ)) (Y := (8389894936523/10000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993079893/1000000000 : ℝ) ^ p + (116288601/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (993079893/1000000000 : ℝ)) (y := (116288601/125000000 : ℝ)) (X := (8389894936523/10000000000000 : ℝ)) (Y := (16101068627571/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1923388701/1000000000 : ℝ)) (τ := (116288601/125000000 : ℝ)) (σ := (993079893/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (113713437/120041888 : ℝ) ^ p + (59328303/60020944 : ℝ) ^ p := by
    exact cert_lt (x := (113713437/120041888 : ℝ)) (y := (59328303/60020944 : ℝ)) (X := (25430736332357/100000000000000 : ℝ)) (Y := (14913852932681/20000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (116288601/125000000 : ℝ)) (n' := (26259163/31250000 : ℝ)) (Ab := (795994059/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (930309141/1000000000 : ℝ) ^ p + (39723193/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (930309141/1000000000 : ℝ)) (y := (39723193/40000000 : ℝ)) (X := (8050607165913/50000000000000 : ℝ)) (Y := (20974701031877/25000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (39723193/40000000 : ℝ) ^ p + (930309141/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (39723193/40000000 : ℝ)) (y := (930309141/1000000000 : ℝ)) (X := (20974701031877/25000000000000 : ℝ)) (Y := (8050607165913/50000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961694483/500000000 : ℝ)) (τ := (930309141/1000000000 : ℝ)) (σ := (39723193/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (397997208/420146803 : ℝ) ^ p + (415298316/420146803 : ℝ) ^ p := by
    exact cert_lt (x := (397997208/420146803 : ℝ)) (y := (415298316/420146803 : ℝ)) (X := (5086145256973/20000000000000 : ℝ)) (Y := (37284637439201/50000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (930309141/1000000000 : ℝ)) (n' := (420146803/500000000 : ℝ)) (Ab := (49749651/62500000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (186061831/200000000 : ℝ) ^ p + (496539911/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (186061831/200000000 : ℝ)) (y := (496539911/500000000 : ℝ)) (X := (8050610228779/50000000000000 : ℝ)) (Y := (83898797719967/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (496539911/500000000 : ℝ) ^ p + (186061831/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496539911/500000000 : ℝ)) (y := (186061831/200000000 : ℝ)) (X := (83898797719967/100000000000000 : ℝ)) (Y := (8050610228779/50000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (795994432/840293623 : ℝ) ^ p + (830596649/840293623 : ℝ) ^ p := by
    exact cert_lt (x := (795994432/840293623 : ℝ)) (y := (830596649/840293623 : ℝ)) (X := (25430726201041/100000000000000 : ℝ)) (Y := (74569275323671/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (n' := (840293623/1000000000 : ℝ)) (Ab := (12437413/15625000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1923388977/1000000000 : ℝ)) (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1664483075/1805899008 : ℝ) ^ p + (898101017/902949504 : ℝ) ^ p := by
    exact cert_lt (x := (1664483075/1805899008 : ℝ)) (y := (898101017/902949504 : ℝ)) (X := (12725882000609/100000000000000 : ℝ)) (Y := (87274118343191/100000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (62072621/66338944 : ℝ) ^ p + (84600287/85292928 : ℝ) ^ p := by
    exact cert_lt (x := (62072621/66338944 : ℝ)) (y := (84600287/85292928 : ℝ)) (X := (18628118224419/100000000000000 : ℝ)) (Y := (20342970637083/25000000000000 : ℝ)) 809 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (496539911/500000000 : ℝ)) (U := (4664457/3906250 : ℝ)) (Ab := (66579323/40000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (186061831/200000000 : ℝ)) (σ := (496539911/500000000 : ℝ)) (Ab := (558653589/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc19.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab136 (p : ℝ) (hpa : (101/4 : ℝ) ≤ p) (hpb : p ≤ (809/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (4664457/3906250 : ℝ)) ∧ coordinateBox (1167/2500 : ℝ) (5587/5000 : ℝ) (7817/10000 : ℝ) (11859/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (22397026535927/13786500000000 : ℝ) ≤ X j i + X k i) ∧
    (16043799917281/2757300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (972921991/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(101/4 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (972921991/1000000000 : ℝ))
      (by norm_num) 4 101 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(101/4 : ℝ)) ≤ (121615249/125000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (121615249/125000000 : ℝ))
      (by norm_num) (by norm_num) 4 101 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(809/32 : ℝ)) ≤ (486477503/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (486477503/500000000 : ℝ))
      (by norm_num) (by norm_num) 32 809 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (260134669843/13786500000000 : ℝ) (4848487/500000000 : ℝ) (500000082719/2757300000000 : ℝ) (3033/2500 : ℝ) (486477503/250000000 : ℝ) (972921991/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (101/4 : ℝ)) (β := (809/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (260134669843/13786500000000 : ℝ)) (δ := (4848487/500000000 : ℝ)) (h := (500000082719/2757300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (972921991/1000000000 : ℝ)) (thia := (121615249/125000000 : ℝ)) (thib := (486477503/500000000 : ℝ))
      (ell := (189/500 : ℝ)) (u := (607/500 : ℝ))
      (v := (349/500 : ℝ)) (w := (607/500 : ℝ))
      (by norm_num) hpa hpb hp1 (by norm_num) hcrit
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) htlo hthia hthib
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hB hS hT hG htail
    norm_num at facts
    exact facts
  have hn0 := initial_norm_lower hp1 X hB
  have hh := contract21_slab136 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 137, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab137 (p : ℝ) (hpa : (809/32 : ℝ) ≤ p) (hpb : p ≤ (405/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2080774593281/110428500000000 : ℝ) (38733/4000000 : ℝ) (4000000662571/22085700000000 : ℝ) (3033/2500 : ℝ) (48649397/25000000 : ℝ) (194591001/200000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597056811/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(447/400 : ℝ) ≤ X j i ∧ X j i ≤ -(467/1000 : ℝ)
      else (3909/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11859/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2080774593281/110428500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (38733/4000000 : ℝ) := by norm_num
  have pc0 : 1 < (924769083/1000000000 : ℝ) ^ p + (994145609/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (924769083/1000000000 : ℝ)) (y := (994145609/1000000000 : ℝ)) (X := (3452692995809/25000000000000 : ℝ)) (Y := (86189247796791/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (994145609/1000000000 : ℝ) ^ p + (924769083/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (994145609/1000000000 : ℝ)) (y := (924769083/1000000000 : ℝ)) (X := (86189247796791/100000000000000 : ℝ)) (Y := (3452692995809/25000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (479728673/250000000 : ℝ)) (τ := (924769083/1000000000 : ℝ)) (σ := (994145609/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (790067625/833764294 : ℝ) ^ p + (412040522/416882147 : ℝ) ^ p := by
    exact cert_lt (x := (790067625/833764294 : ℝ)) (y := (412040522/416882147 : ℝ)) (X := (5119745626103/20000000000000 : ℝ)) (Y := (37200636705557/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (924769083/1000000000 : ℝ)) (n' := (416882147/500000000 : ℝ)) (Ab := (6320541/8000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (46508923/50000000 : ℝ) ^ p + (993131959/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (46508923/50000000 : ℝ)) (y := (993131959/1000000000 : ℝ)) (X := (8003941879747/50000000000000 : ℝ)) (Y := (16798426863967/20000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993131959/1000000000 : ℝ) ^ p + (46508923/50000000 : ℝ) ^ p := by
    exact cert_lt (x := (993131959/1000000000 : ℝ)) (y := (46508923/50000000 : ℝ)) (X := (16798426863967/20000000000000 : ℝ)) (Y := (8003941879747/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1923310419/1000000000 : ℝ)) (τ := (46508923/50000000 : ℝ)) (σ := (993131959/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (795878715/840114574 : ℝ) ^ p + (415215662/420057287 : ℝ) ^ p := by
    exact cert_lt (x := (795878715/840114574 : ℝ)) (y := (415215662/420057287 : ℝ)) (X := (1271563793603/5000000000000 : ℝ)) (Y := (7456872526733/10000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (46508923/50000000 : ℝ)) (n' := (420057287/500000000 : ℝ)) (Ab := (159175743/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (930393111/1000000000 : ℝ) ^ p + (496544067/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (930393111/1000000000 : ℝ)) (y := (496544067/500000000 : ℝ)) (X := (16101651697483/100000000000000 : ℝ)) (Y := (8389836609963/10000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (496544067/500000000 : ℝ) ^ p + (930393111/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496544067/500000000 : ℝ)) (y := (930393111/1000000000 : ℝ)) (X := (8389836609963/10000000000000 : ℝ)) (Y := (16101651697483/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (384696249/200000000 : ℝ)) (τ := (930393111/1000000000 : ℝ)) (σ := (496544067/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (113729798/120052259 : ℝ) ^ p + (830682563/840365813 : ℝ) ^ p := by
    exact cert_lt (x := (113729798/120052259 : ℝ)) (y := (830682563/840365813 : ℝ)) (X := (6356173876547/25000000000000 : ℝ)) (Y := (37287652787997/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (930393111/1000000000 : ℝ)) (n' := (840365813/1000000000 : ℝ)) (Ab := (398054293/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (186080309/200000000 : ℝ) ^ p + (496543203/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (186080309/200000000 : ℝ)) (y := (496543203/500000000 : ℝ)) (X := (16105346748487/100000000000000 : ℝ)) (Y := (83894670922147/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496543203/500000000 : ℝ) ^ p + (186080309/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (496543203/500000000 : ℝ)) (y := (186080309/200000000 : ℝ)) (X := (83894670922147/100000000000000 : ℝ)) (Y := (16105346748487/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1923487951/1000000000 : ℝ)) (τ := (186080309/200000000 : ℝ)) (σ := (496543203/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (796117617/840375683 : ℝ) ^ p + (830692433/840375683 : ℝ) ^ p := by
    exact cert_lt (x := (796117617/840375683 : ℝ)) (y := (830692433/840375683 : ℝ)) (X := (6356109367661/25000000000000 : ℝ)) (Y := (74575564016469/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (186080309/200000000 : ℝ)) (n' := (840375683/1000000000 : ℝ)) (Ab := (796117617/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (232600469/250000000 : ℝ) ^ p + (496543169/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (232600469/250000000 : ℝ)) (y := (496543169/500000000 : ℝ)) (X := (4026372945183/25000000000000 : ℝ)) (Y := (83894525513267/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496543169/500000000 : ℝ) ^ p + (232600469/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (496543169/500000000 : ℝ)) (y := (232600469/250000000 : ℝ)) (X := (83894525513267/100000000000000 : ℝ)) (Y := (4026372945183/25000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (961744107/500000000 : ℝ)) (τ := (232600469/250000000 : ℝ)) (σ := (496543169/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (796117972/840376071 : ℝ) ^ p + (276897607/280125357 : ℝ) ^ p := by
    exact cert_lt (x := (796117972/840376071 : ℝ)) (y := (276897607/280125357 : ℝ)) (X := (5084885462519/20000000000000 : ℝ)) (Y := (74575574175927/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (232600469/250000000 : ℝ)) (n' := (840376071/1000000000 : ℝ)) (Ab := (199029493/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (29075059/31250000 : ℝ) ^ p + (7758487/7812500 : ℝ) ^ p := by
    exact cert_lt (x := (29075059/31250000 : ℝ)) (y := (7758487/7812500 : ℝ)) (X := (8052748519361/50000000000000 : ℝ)) (Y := (41947260618269/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (7758487/7812500 : ℝ) ^ p + (29075059/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (7758487/7812500 : ℝ)) (y := (29075059/31250000 : ℝ)) (X := (41947260618269/50000000000000 : ℝ)) (Y := (8052748519361/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (60109007/31250000 : ℝ)) (τ := (29075059/31250000 : ℝ)) (σ := (7758487/7812500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (796117984/840376085 : ℝ) ^ p + (166138567/168075217 : ℝ) ^ p := by
    exact cert_lt (x := (796117984/840376085 : ℝ)) (y := (166138567/168075217 : ℝ)) (X := (25424426291873/100000000000000 : ℝ)) (Y := (37287787271253/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (29075059/31250000 : ℝ)) (n' := (168075217/200000000 : ℝ)) (Ab := (24878687/31250000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (93040189/100000000 : ℝ) ^ p + (198617267/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (93040189/100000000 : ℝ)) (y := (198617267/200000000 : ℝ)) (X := (8052748957527/50000000000000 : ℝ)) (Y := (41947259549087/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (198617267/200000000 : ℝ) ^ p + (93040189/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (198617267/200000000 : ℝ)) (y := (93040189/100000000 : ℝ)) (X := (41947259549087/50000000000000 : ℝ)) (Y := (8052748957527/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (796117986/840376087 : ℝ) ^ p + (830692837/840376087 : ℝ) ^ p := by
    exact cert_lt (x := (796117986/840376087 : ℝ)) (y := (830692837/840376087 : ℝ)) (X := (12712213188509/50000000000000 : ℝ)) (Y := (37287787297437/50000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (n' := (840376087/1000000000 : ℝ)) (Ab := (398058993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (n' := (840376087/1000000000 : ℝ)) (Ab := (398058993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (n' := (840376087/1000000000 : ℝ)) (Ab := (398058993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (n' := (840376087/1000000000 : ℝ)) (Ab := (398058993/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (76939529/40000000 : ℝ)) (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (832314047/902943189 : ℝ) ^ p + (299367188/300981063 : ℝ) ^ p := by
    exact cert_lt (x := (832314047/902943189 : ℝ)) (y := (299367188/300981063 : ℝ)) (X := (12723770335939/100000000000000 : ℝ)) (Y := (17455245980553/20000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (558701423/597056811 : ℝ) ^ p + (197405062/199018937 : ℝ) ^ p := by
    exact cert_lt (x := (558701423/597056811 : ℝ)) (y := (197405062/199018937 : ℝ)) (X := (18624807845897/100000000000000 : ℝ)) (Y := (81375192888689/100000000000000 : ℝ)) 405 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (198617267/200000000 : ℝ)) (U := (597056811/500000000 : ℝ)) (Ab := (832314047/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (93040189/100000000 : ℝ)) (σ := (198617267/200000000 : ℝ)) (Ab := (558701423/500000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HlawkaSchatten.DiagonalRealBundle



/- Original p-norm hypotheses imply all premises of the complete
   contraction schedule. Three rational root certificates are checked
   as integer-power inequalities; no numerical validity predicate
   or abstract Facts hypothesis remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem localize21_slab137 (p : ℝ) (hpa : (809/32 : ℝ) ≤ p) (hpb : p ≤ (405/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (597056811/500000000 : ℝ)) ∧ coordinateBox (467/1000 : ℝ) (447/400 : ℝ) (3909/5000 : ℝ) (11859/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (11213832674293/6901781250000 : ℝ) ≤ X j i + X k i) ∧
    (128514199337429/22085700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (194591001/200000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(809/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (194591001/200000000 : ℝ))
      (by norm_num) 32 809 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(809/32 : ℝ)) ≤ (486477503/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (486477503/500000000 : ℝ))
      (by norm_num) (by norm_num) 32 809 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(405/16 : ℝ)) ≤ (48649397/50000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (48649397/50000000 : ℝ))
      (by norm_num) (by norm_num) 16 405 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (2080774593281/110428500000000 : ℝ) (38733/4000000 : ℝ) (4000000662571/22085700000000 : ℝ) (3033/2500 : ℝ) (48649397/25000000 : ℝ) (194591001/200000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (809/32 : ℝ)) (β := (405/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (2080774593281/110428500000000 : ℝ)) (δ := (38733/4000000 : ℝ)) (h := (4000000662571/22085700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (194591001/200000000 : ℝ)) (thia := (486477503/500000000 : ℝ)) (thib := (48649397/50000000 : ℝ))
      (ell := (189/500 : ℝ)) (u := (607/500 : ℝ))
      (v := (349/500 : ℝ)) (w := (607/500 : ℝ))
      (by norm_num) hpa hpb hp1 (by norm_num) hcrit
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) htlo hthia hthib
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hB hS hT hG htail
    norm_num at facts
    exact facts
  have hn0 := initial_norm_lower hp1 X hB
  have hh := contract21_slab137 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



set_option autoImplicit false
set_option maxHeartbeats 200000000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem bounds_localized_domain4_21_34 (p : ℝ) (hpa : (403/16 : ℝ) ≤ p)
    (hpb : p ≤ (405/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  rcases le_total p (101/4 : ℝ) with hl | hr
  ·
    rcases le_total p (807/32 : ℝ) with hll | hlr
    ·
      have hh := localize21_slab134 p (by linarith) (by linarith) X hB hS hT hG
      have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
        coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        simpa [coordinateBox] using hBx j j
      · intro j i hji
        simpa [coordinateBox, hji] using hBx j i
      · intro j
        exact (hh.1 j).trans (by norm_num)
      · intro i j k hij hik hjk
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (178685983471339/110019000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (64011399669943/11001900000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      have hh := localize21_slab135 p (by linarith) (by linarith) X hB hS hT hG
      have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
        coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        simpa [coordinateBox] using hBx j j
      · intro j i hji
        simpa [coordinateBox, hji] using hBx j i
      · intro j
        exact (hh.1 j).trans (by norm_num)
      · intro i j k hij hik hjk
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (178931099439709/110155500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (128186599339067/22031100000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (809/32 : ℝ) with hrl | hrr
    ·
      have hh := localize21_slab136 p (by linarith) (by linarith) X hB hS hT hG
      have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
        coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        simpa [coordinateBox] using hBx j j
      · intro j i hji
        simpa [coordinateBox, hji] using hBx j i
      · intro j
        exact (hh.1 j).trans (by norm_num)
      · intro i j k hij hik hjk
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (22397026535927/13786500000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (16043799917281/2757300000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      have hh := localize21_slab137 p (by linarith) (by linarith) X hB hS hT hG
      have hBx : coordinateBox (4577/10000 : ℝ) (2239/2000 : ℝ) (3863/5000 : ℝ) (1483/1250 : ℝ) X :=
        coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        simpa [coordinateBox] using hBx j j
      · intro j i hji
        simpa [coordinateBox, hji] using hBx j i
      · intro j
        exact (hh.1 j).trans (by norm_num)
      · intro i j k hij hik hjk
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (11213832674293/6901781250000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (128514199337429/22085700000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalRealBundle
theorem solution :
    ∀ p : ℝ, (403/16 : ℝ) ≤ p → p ≤ (405/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : HlawkaSchatten.DiagonalRealBundle.coordinateBox (189/500 : ℝ) (607/500 : ℝ)
      (349/500 : ℝ) (607/500 : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [HlawkaSchatten.DiagonalRealBundle.coordinateBox] using hd i
    · simpa [HlawkaSchatten.DiagonalRealBundle.coordinateBox, hji] using ho j i hji
  exact HlawkaSchatten.DiagonalRealBundle.bounds_localized_domain4_21_34 p hp hpmax X hB hS hT hG

#print axioms solution
