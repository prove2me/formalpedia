-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.localized_domain2_21_08_part1
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T14:08:57.751352+00:00
-- url     : https://prove2.me/submissions/41798d2b-63e7-4090-b86b-94a130787afe

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
   cutoff21/contractor.json, slab 34, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab034 (p : ℝ) (hpa : (353/16 : ℝ) ≤ p) (hpb : p ≤ (707/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (1058200634683/48184500000000 : ℝ) (11331179/1000000000 : ℝ) (2000000289107/9636900000000 : ℝ) (3033/2500 : ℝ) (242278507/125000000 : ℝ) (969070963/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192809927/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2213/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2241/5000 : ℝ)
      else (7633/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11837/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (1058200634683/48184500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (11331179/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (182638957/200000000 : ℝ) ^ p + (99348377/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (182638957/200000000 : ℝ)) (y := (99348377/100000000 : ℝ)) (X := (6724625829629/50000000000000 : ℝ)) (Y := (86550764754611/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (99348377/100000000 : ℝ) ^ p + (182638957/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (99348377/100000000 : ℝ)) (y := (182638957/200000000 : ℝ)) (X := (86550764754611/100000000000000 : ℝ)) (Y := (6724625829629/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (381335711/200000000 : ℝ)) (τ := (182638957/200000000 : ℝ)) (σ := (99348377/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (154965861/164599028 : ℝ) ^ p + (811663961/822995140 : ℝ) ^ p := by
    exact cert_lt (x := (154965861/164599028 : ℝ)) (y := (811663961/822995140 : ℝ)) (X := (3297975809717/12500000000000 : ℝ)) (Y := (18404048738763/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (182638957/200000000 : ℝ)) (n' := (41149757/50000000 : ℝ)) (Ab := (154965861/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (459522037/500000000 : ℝ) ^ p + (496206543/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (459522037/500000000 : ℝ)) (y := (496206543/500000000 : ℝ)) (X := (3097363932443/20000000000000 : ℝ)) (Y := (84513196865727/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (496206543/500000000 : ℝ) ^ p + (459522037/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496206543/500000000 : ℝ)) (y := (459522037/500000000 : ℝ)) (X := (84513196865727/100000000000000 : ℝ)) (Y := (3097363932443/20000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (47786429/25000000 : ℝ)) (τ := (459522037/500000000 : ℝ)) (σ := (496206543/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (390572971/414988856 : ℝ) ^ p + (818646533/829977712 : ℝ) ^ p := by
    exact cert_lt (x := (390572971/414988856 : ℝ)) (y := (818646533/829977712 : ℝ)) (X := (3274068008863/12500000000000 : ℝ)) (Y := (36903728476563/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (459522037/500000000 : ℝ)) (n' := (51873607/62500000 : ℝ)) (Ab := (390572971/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (459662109/500000000 : ℝ) ^ p + (3101117/3125000 : ℝ) ^ p := by
    exact cert_lt (x := (459662109/500000000 : ℝ)) (y := (3101117/3125000 : ℝ)) (X := (3897863455219/25000000000000 : ℝ)) (Y := (4220428073479/5000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (3101117/3125000 : ℝ) ^ p + (459662109/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (3101117/3125000 : ℝ)) (y := (459662109/500000000 : ℝ)) (X := (4220428073479/5000000000000 : ℝ)) (Y := (3897863455219/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (955840829/500000000 : ℝ)) (τ := (459662109/500000000 : ℝ)) (σ := (3101117/3125000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (781447423/830311043 : ℝ) ^ p + (818979864/830311043 : ℝ) ^ p := by
    exact cert_lt (x := (781447423/830311043 : ℝ)) (y := (818979864/830311043 : ℝ)) (X := (26183482666269/100000000000000 : ℝ)) (Y := (1476330372651/2000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (459662109/500000000 : ℝ)) (n' := (830311043/1000000000 : ℝ)) (Ab := (781447423/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (919337487/1000000000 : ℝ) ^ p + (496177397/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (919337487/1000000000 : ℝ)) (y := (496177397/500000000 : ℝ)) (X := (3899106628487/25000000000000 : ℝ)) (Y := (84403589076757/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496177397/500000000 : ℝ) ^ p + (919337487/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (496177397/500000000 : ℝ)) (y := (919337487/1000000000 : ℝ)) (X := (84403589076757/100000000000000 : ℝ)) (Y := (3899106628487/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1911692281/1000000000 : ℝ)) (τ := (919337487/1000000000 : ℝ)) (σ := (496177397/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (781461699/830326828 : ℝ) ^ p + (818995649/830326828 : ℝ) ^ p := by
    exact cert_lt (x := (781461699/830326828 : ℝ)) (y := (818995649/830326828 : ℝ)) (X := (26183053272687/100000000000000 : ℝ)) (Y := (36908473798643/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (919337487/1000000000 : ℝ)) (n' := (207581707/250000000 : ℝ)) (Ab := (781461699/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (459669057/500000000 : ℝ) ^ p + (992354669/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459669057/500000000 : ℝ)) (y := (992354669/1000000000 : ℝ)) (X := (7798330763027/50000000000000 : ℝ)) (Y := (3376134167291/4000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992354669/1000000000 : ℝ) ^ p + (459669057/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992354669/1000000000 : ℝ)) (y := (459669057/500000000 : ℝ)) (X := (3376134167291/4000000000000 : ℝ)) (Y := (7798330763027/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1911692783/1000000000 : ℝ)) (τ := (459669057/500000000 : ℝ)) (σ := (992354669/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (130243729/138387929 : ℝ) ^ p + (818996395/830327574 : ℝ) ^ p := by
    exact cert_lt (x := (130243729/138387929 : ℝ)) (y := (818996395/830327574 : ℝ)) (X := (6545758303397/25000000000000 : ℝ)) (Y := (73816967869839/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (459669057/500000000 : ℝ)) (n' := (415163787/500000000 : ℝ)) (Ab := (390731187/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (28729317/31250000 : ℝ) ^ p + (992354663/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (28729317/31250000 : ℝ)) (y := (992354663/1000000000 : ℝ)) (X := (15596672770737/100000000000000 : ℝ)) (Y := (21100835726839/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992354663/1000000000 : ℝ) ^ p + (28729317/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (992354663/1000000000 : ℝ)) (y := (28729317/31250000 : ℝ)) (X := (21100835726839/25000000000000 : ℝ)) (Y := (15596672770737/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1911692807/1000000000 : ℝ)) (τ := (28729317/31250000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (260487469/276775870 : ℝ) ^ p + (818996431/830327610 : ℝ) ^ p := by
    exact cert_lt (x := (260487469/276775870 : ℝ)) (y := (818996431/830327610 : ℝ)) (X := (26183032561141/100000000000000 : ℝ)) (Y := (73816968848139/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (28729317/31250000 : ℝ)) (n' := (83032761/100000000 : ℝ)) (Ab := (781462407/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (183867629/200000000 : ℝ) ^ p + (992354663/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (183867629/200000000 : ℝ)) (y := (992354663/1000000000 : ℝ)) (X := (389916828639/2500000000000 : ℝ)) (Y := (21100835726839/25000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992354663/1000000000 : ℝ) ^ p + (183867629/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (992354663/1000000000 : ℝ)) (y := (183867629/200000000 : ℝ)) (X := (21100835726839/25000000000000 : ℝ)) (Y := (389916828639/2500000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (781462408/830327611 : ℝ) ^ p + (818996432/830327611 : ℝ) ^ p := by
    exact cert_lt (x := (781462408/830327611 : ℝ)) (y := (818996432/830327611 : ℝ)) (X := (5236606520941/20000000000000 : ℝ)) (Y := (36908484437657/50000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (n' := (830327611/1000000000 : ℝ)) (Ab := (97682801/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (n' := (830327611/1000000000 : ℝ)) (Ab := (97682801/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (n' := (830327611/1000000000 : ℝ)) (Ab := (97682801/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (n' := (830327611/1000000000 : ℝ)) (Ab := (97682801/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (238961601/125000000 : ℝ)) (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1647632392/1807190073 : ℝ) ^ p + (1795858894/1807190073 : ℝ) ^ p := by
    exact cert_lt (x := (1647632392/1807190073 : ℝ)) (y := (1795858894/1807190073 : ℝ)) (X := (2594832346781/20000000000000 : ℝ)) (Y := (17405167695807/20000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (368823728/397603309 : ℝ) ^ p + (1181478748/1192809927 : ℝ) ^ p := by
    exact cert_lt (x := (368823728/397603309 : ℝ)) (y := (1181478748/1192809927 : ℝ)) (X := (19013226470993/100000000000000 : ℝ)) (Y := (80986773988897/100000000000000 : ℝ)) 707 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992354663/1000000000 : ℝ)) (U := (1192809927/1000000000 : ℝ)) (Ab := (205954049/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (183867629/200000000 : ℝ)) (σ := (992354663/1000000000 : ℝ)) (Ab := (69154449/62500000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc22.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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

theorem localize21_slab034 (p : ℝ) (hpa : (353/16 : ℝ) ≤ p) (hpb : p ≤ (707/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1192809927/1000000000 : ℝ)) ∧ coordinateBox (2241/5000 : ℝ) (2213/2000 : ℝ) (7633/10000 : ℝ) (11837/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (154157099181247/96369000000000 : ℝ) ≤ X j i + X k i) ∧
    (55821399710893/9636900000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (969070963/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(353/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (969070963/1000000000 : ℝ))
      (by norm_num) 16 353 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(353/16 : ℝ)) ≤ (242267741/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (242267741/250000000 : ℝ))
      (by norm_num) (by norm_num) 16 353 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(707/32 : ℝ)) ≤ (242278507/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (242278507/250000000 : ℝ))
      (by norm_num) (by norm_num) 32 707 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (1058200634683/48184500000000 : ℝ) (11331179/1000000000 : ℝ) (2000000289107/9636900000000 : ℝ) (3033/2500 : ℝ) (242278507/125000000 : ℝ) (969070963/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (353/16 : ℝ)) (β := (707/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (1058200634683/48184500000000 : ℝ)) (δ := (11331179/1000000000 : ℝ)) (h := (2000000289107/9636900000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (969070963/1000000000 : ℝ)) (thia := (242267741/250000000 : ℝ)) (thib := (242278507/250000000 : ℝ))
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
  have hh := contract21_slab034 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 35, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab035 (p : ℝ) (hpa : (707/32 : ℝ) ≤ p) (hpb : p ≤ (177/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2116005870089/96505500000000 : ℝ) (2262507/200000000 : ℝ) (4000000579033/19301100000000 : ℝ) (3033/2500 : ℝ) (969156973/500000000 : ℝ) (969114027/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1192822353/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5533/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1121/2500 : ℝ)
      else (1527/2000 : ℝ) ≤ X j i ∧ X j i ≤ (5919/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2116005870089/96505500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2262507/200000000 : ℝ) := by norm_num
  have pc0 : 1 < (913324187/1000000000 : ℝ) ^ p + (993490869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (913324187/1000000000 : ℝ)) (y := (993490869/1000000000 : ℝ)) (X := (3363312531891/25000000000000 : ℝ)) (Y := (86546765894951/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (993490869/1000000000 : ℝ) ^ p + (913324187/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993490869/1000000000 : ℝ)) (y := (913324187/1000000000 : ℝ)) (X := (86546765894951/100000000000000 : ℝ)) (Y := (3363312531891/25000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (119175941/62500000 : ℝ)) (τ := (913324187/1000000000 : ℝ)) (σ := (993490869/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (774998981/823117803 : ℝ) ^ p + (270601756/274372601 : ℝ) ^ p := by
    exact cert_lt (x := (774998981/823117803 : ℝ)) (y := (270601756/274372601 : ℝ)) (X := (26374904384481/100000000000000 : ℝ)) (Y := (575196067931/781250000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (913324187/1000000000 : ℝ)) (n' := (823117803/1000000000 : ℝ)) (Ab := (774998981/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (229792329/250000000 : ℝ) ^ p + (124052583/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (229792329/250000000 : ℝ)) (y := (124052583/125000000 : ℝ)) (X := (1549265462879/10000000000000 : ℝ)) (Y := (84507361375513/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (124052583/125000000 : ℝ) ^ p + (229792329/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (124052583/125000000 : ℝ)) (y := (229792329/250000000 : ℝ)) (X := (84507361375513/100000000000000 : ℝ)) (Y := (1549265462879/10000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (95579499/50000000 : ℝ)) (τ := (229792329/250000000 : ℝ)) (σ := (124052583/125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (781310737/830094103 : ℝ) ^ p + (818781568/830094103 : ℝ) ^ p := by
    exact cert_lt (x := (781310737/830094103 : ℝ)) (y := (818781568/830094103 : ℝ)) (X := (26183895805927/100000000000000 : ℝ)) (Y := (14763221009947/20000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (229792329/250000000 : ℝ)) (n' := (830094103/1000000000 : ℝ)) (Ab := (781310737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (919448701/1000000000 : ℝ) ^ p + (31011411/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (919448701/1000000000 : ℝ)) (y := (31011411/31250000 : ℝ)) (X := (1559717756429/10000000000000 : ℝ)) (Y := (42201419132421/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (31011411/31250000 : ℝ) ^ p + (919448701/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (31011411/31250000 : ℝ)) (y := (919448701/1000000000 : ℝ)) (X := (42201419132421/50000000000000 : ℝ)) (Y := (1559717756429/10000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1911813853/1000000000 : ℝ)) (τ := (919448701/1000000000 : ℝ)) (σ := (31011411/31250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (781611383/830426469 : ℝ) ^ p + (273037978/276808823 : ℝ) ^ p := by
    exact cert_lt (x := (781611383/830426469 : ℝ)) (y := (273037978/276808823 : ℝ)) (X := (26174864347537/100000000000000 : ℝ)) (Y := (36912568349429/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (919448701/1000000000 : ℝ)) (n' := (830426469/1000000000 : ℝ)) (Ab := (781611383/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (229865477/250000000 : ℝ) ^ p + (992362517/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (229865477/250000000 : ℝ)) (y := (992362517/1000000000 : ℝ)) (X := (7801067584311/50000000000000 : ℝ)) (Y := (8439787991387/10000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (992362517/1000000000 : ℝ) ^ p + (229865477/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (992362517/1000000000 : ℝ)) (y := (229865477/250000000 : ℝ)) (X := (8439787991387/10000000000000 : ℝ)) (Y := (7801067584311/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (76472977/40000000 : ℝ)) (τ := (229865477/250000000 : ℝ)) (σ := (992362517/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (781625593/830442178 : ℝ) ^ p + (819129643/830442178 : ℝ) ^ p := by
    exact cert_lt (x := (781625593/830442178 : ℝ)) (y := (819129643/830442178 : ℝ)) (X := (26174437898131/100000000000000 : ℝ)) (Y := (73825563419351/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (229865477/250000000 : ℝ)) (n' := (415221089/500000000 : ℝ)) (Ab := (781625593/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (919462531/1000000000 : ℝ) ^ p + (992362393/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919462531/1000000000 : ℝ)) (y := (992362393/1000000000 : ℝ)) (X := (15602369065663/100000000000000 : ℝ)) (Y := (84397646586559/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (992362393/1000000000 : ℝ) ^ p + (919462531/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992362393/1000000000 : ℝ)) (y := (919462531/1000000000 : ℝ)) (X := (84397646586559/100000000000000 : ℝ)) (Y := (15602369065663/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (477956231/250000000 : ℝ)) (τ := (919462531/1000000000 : ℝ)) (σ := (992362393/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (781626263/830442919 : ℝ) ^ p + (819130384/830442919 : ℝ) ^ p := by
    exact cert_lt (x := (781626263/830442919 : ℝ)) (y := (819130384/830442919 : ℝ)) (X := (26174417566887/100000000000000 : ℝ)) (Y := (9228197943449/12500000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (919462531/1000000000 : ℝ)) (n' := (830442919/1000000000 : ℝ)) (Ab := (781626263/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (919462561/1000000000 : ℝ) ^ p + (992362387/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (919462561/1000000000 : ℝ)) (y := (992362387/1000000000 : ℝ)) (X := (15602380328847/100000000000000 : ℝ)) (Y := (84397635296543/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (992362387/1000000000 : ℝ) ^ p + (919462561/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (992362387/1000000000 : ℝ)) (y := (919462561/1000000000 : ℝ)) (X := (84397635296543/100000000000000 : ℝ)) (Y := (15602380328847/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (477956237/250000000 : ℝ)) (τ := (919462561/1000000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (781626296/830442955 : ℝ) ^ p + (163826084/166088591 : ℝ) ^ p := by
    exact cert_lt (x := (781626296/830442955 : ℝ)) (y := (163826084/166088591 : ℝ)) (X := (6543604228023/25000000000000 : ℝ)) (Y := (36912792262741/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (919462561/1000000000 : ℝ)) (n' := (166088591/200000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (459731281/500000000 : ℝ) ^ p + (992362387/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (459731281/500000000 : ℝ)) (y := (992362387/1000000000 : ℝ)) (X := (15602380704287/100000000000000 : ℝ)) (Y := (84397635296543/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (992362387/1000000000 : ℝ) ^ p + (459731281/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (992362387/1000000000 : ℝ)) (y := (459731281/500000000 : ℝ)) (X := (84397635296543/100000000000000 : ℝ)) (Y := (15602380704287/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (195406574/207610739 : ℝ) ^ p + (819130421/830442956 : ℝ) ^ p := by
    exact cert_lt (x := (195406574/207610739 : ℝ)) (y := (819130421/830442956 : ℝ)) (X := (13087208107371/50000000000000 : ℝ)) (Y := (14765116910529/20000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (n' := (207610739/250000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (n' := (207610739/250000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (n' := (207610739/250000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (n' := (207610739/250000000 : ℝ)) (Ab := (97703287/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1911824949/1000000000 : ℝ)) (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (549273369/602392549 : ℝ) ^ p + (598621704/602392549 : ℝ) ^ p := by
    exact cert_lt (x := (549273369/602392549 : ℝ)) (y := (598621704/602392549 : ℝ)) (X := (3242840333137/25000000000000 : ℝ)) (Y := (87028638907047/100000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1106588836/1192822353 : ℝ) ^ p + (393836606/397607451 : ℝ) ^ p := by
    exact cert_lt (x := (1106588836/1192822353 : ℝ)) (y := (393836606/397607451 : ℝ)) (X := (19008929232509/100000000000000 : ℝ)) (Y := (40495535671399/50000000000000 : ℝ)) 177 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (992362387/1000000000 : ℝ)) (U := (1192822353/1000000000 : ℝ)) (Ab := (1647820107/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (459731281/500000000 : ℝ)) (σ := (992362387/1000000000 : ℝ)) (Ab := (276647209/250000000 : ℝ))
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

theorem localize21_slab035 (p : ℝ) (hpa : (707/32 : ℝ) ≤ p) (hpb : p ≤ (177/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1192822353/1000000000 : ℝ)) ∧ coordinateBox (1121/2500 : ℝ) (5533/5000 : ℝ) (1527/2000 : ℝ) (5919/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (308805162895007/193011000000000 : ℝ) ≤ X j i + X k i) ∧
    (111806599420967/19301100000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (969114027/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(707/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (969114027/1000000000 : ℝ))
      (by norm_num) 32 707 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(707/32 : ℝ)) ≤ (242278507/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (242278507/250000000 : ℝ))
      (by norm_num) (by norm_num) 32 707 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(177/8 : ℝ)) ≤ (969156973/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (969156973/1000000000 : ℝ))
      (by norm_num) (by norm_num) 8 177 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (2116005870089/96505500000000 : ℝ) (2262507/200000000 : ℝ) (4000000579033/19301100000000 : ℝ) (3033/2500 : ℝ) (969156973/500000000 : ℝ) (969114027/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (707/32 : ℝ)) (β := (177/8 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (2116005870089/96505500000000 : ℝ)) (δ := (2262507/200000000 : ℝ)) (h := (4000000579033/19301100000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (969114027/1000000000 : ℝ)) (thia := (242278507/250000000 : ℝ)) (thib := (969156973/1000000000 : ℝ))
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
  have hh := contract21_slab035 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
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

theorem bounds_localized_domain2_21_08_part1 (p : ℝ) (hpa : (353/16 : ℝ) ≤ p)
    (hpb : p ≤ (177/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  rcases le_total p (707/32 : ℝ) with hl | hr
  ·
    have hh := localize21_slab034 p (by linarith) (by linarith) X hB hS hT hG
    have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
      coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      simpa [coordinateBox] using hBx j j
    · intro j i hji
      simpa [coordinateBox, hji] using hBx j i
    · intro j
      exact (hh.1 j).trans (by norm_num)
    · intro i j k hij hik hjk
      exact (show (1139124440087/716625000000 : ℝ) ≤ (154157099181247/96369000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
    · exact (show (3314799982801/573300000000 : ℝ) ≤ (55821399710893/9636900000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    have hh := localize21_slab035 p (by linarith) (by linarith) X hB hS hT hG
    have hBx : coordinateBox (881/2000 : ℝ) (5559/5000 : ℝ) (3779/5000 : ℝ) (11847/10000 : ℝ) X :=
      coordinateBox_weaken hh.2.1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      simpa [coordinateBox] using hBx j j
    · intro j i hji
      simpa [coordinateBox, hji] using hBx j i
    · intro j
      exact (hh.1 j).trans (by norm_num)
    · intro i j k hij hik hjk
      exact (show (1139124440087/716625000000 : ℝ) ≤ (308805162895007/193011000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
    · exact (show (3314799982801/573300000000 : ℝ) ≤ (111806599420967/19301100000000 : ℝ) by norm_num).trans hh.2.2.2.le
    

end HlawkaSchatten.DiagonalRealBundle
theorem solution :
    ∀ p : ℝ, (353/16 : ℝ) ≤ p → p ≤ (177/8 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  intro p hp hpmax X hd ho hS hT hG
  have hB : HlawkaSchatten.DiagonalRealBundle.coordinateBox (189/500 : ℝ) (607/500 : ℝ)
      (349/500 : ℝ) (607/500 : ℝ) X := by
    intro j i
    by_cases hji : j = i
    · subst j
      simpa [HlawkaSchatten.DiagonalRealBundle.coordinateBox] using hd i
    · simpa [HlawkaSchatten.DiagonalRealBundle.coordinateBox, hji] using ho j i hji
  exact HlawkaSchatten.DiagonalRealBundle.bounds_localized_domain2_21_08_part1 p hp hpmax X hB hS hT hG

#print axioms solution
