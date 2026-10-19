-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_37
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T14:42:31.22503+00:00
-- url     : https://prove2.me/submissions/d7b1d637-01af-4dbf-9f2e-9ec6d45c16d9

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
   cutoff21/contractor.json, slab 146, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab146 (p : ℝ) (hpa : (409/16 : ℝ) ≤ p) (hpb : p ≤ (819/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (259760512969/13957125000000 : ℝ) (9561443/1000000000 : ℝ) (2000000334971/11165700000000 : ℝ) (3033/2500 : ℝ) (486640387/250000000 : ℝ) (19464971/20000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194227119/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(11183/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4683/10000 : ℝ)
      else (979/1250 : ℝ) ≤ X j i ∧ X j i ≤ (11861/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (259760512969/13957125000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (9561443/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (462817957/500000000 : ℝ) ^ p + (248549351/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (462817957/500000000 : ℝ)) (y := (248549351/250000000 : ℝ)) (X := (13838173813581/100000000000000 : ℝ)) (Y := (43080922584053/50000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248549351/250000000 : ℝ) ^ p + (462817957/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (248549351/250000000 : ℝ)) (y := (462817957/500000000 : ℝ)) (X := (43080922584053/50000000000000 : ℝ)) (Y := (13838173813581/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (959916659/500000000 : ℝ)) (τ := (462817957/500000000 : ℝ)) (σ := (248549351/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (791214137/834554289 : ℝ) ^ p + (824992846/834554289 : ℝ) ^ p := by
    exact cert_lt (x := (791214137/834554289 : ℝ)) (y := (824992846/834554289 : ℝ)) (X := (12770401421363/50000000000000 : ℝ)) (Y := (37229599388819/50000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462817957/500000000 : ℝ)) (n' := (834554289/1000000000 : ℝ)) (Ab := (791214137/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931007021/1000000000 : ℝ) ^ p + (993189169/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931007021/1000000000 : ℝ)) (y := (993189169/1000000000 : ℝ)) (X := (4011711836071/25000000000000 : ℝ)) (Y := (16790634226977/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993189169/1000000000 : ℝ) ^ p + (931007021/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993189169/1000000000 : ℝ)) (y := (931007021/1000000000 : ℝ)) (X := (16790634226977/20000000000000 : ℝ)) (Y := (4011711836071/25000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (192419619/100000000 : ℝ)) (τ := (931007021/1000000000 : ℝ)) (σ := (993189169/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (796981990/840851757 : ℝ) ^ p + (831290314/840851757 : ℝ) ^ p := by
    exact cert_lt (x := (796981990/840851757 : ℝ)) (y := (831290314/840851757 : ℝ)) (X := (25375211569649/100000000000000 : ℝ)) (Y := (14924957876669/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931007021/1000000000 : ℝ)) (n' := (840851757/1000000000 : ℝ)) (Ab := (79698199/100000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (931216999/1000000000 : ℝ) ^ p + (993146211/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931216999/1000000000 : ℝ)) (y := (993146211/1000000000 : ℝ)) (X := (16139733166597/100000000000000 : ℝ)) (Y := (83860284733917/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993146211/1000000000 : ℝ) ^ p + (931216999/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993146211/1000000000 : ℝ)) (y := (931216999/1000000000 : ℝ)) (X := (83860284733917/100000000000000 : ℝ)) (Y := (16139733166597/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (192436321/100000000 : ℝ)) (τ := (931216999/1000000000 : ℝ)) (σ := (993146211/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797206779/841097224 : ℝ) ^ p + (831535781/841097224 : ℝ) ^ p := by
    exact cert_lt (x := (797206779/841097224 : ℝ)) (y := (831535781/841097224 : ℝ)) (X := (25368800076523/100000000000000 : ℝ)) (Y := (37315600389687/50000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (931216999/1000000000 : ℝ)) (n' := (105137153/125000000 : ℝ)) (Ab := (797206779/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (116403141/125000000 : ℝ) ^ p + (496572271/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (116403141/125000000 : ℝ)) (y := (496572271/500000000 : ℝ)) (X := (3228667895429/20000000000000 : ℝ)) (Y := (83856677914259/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (496572271/500000000 : ℝ) ^ p + (116403141/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (496572271/500000000 : ℝ)) (y := (116403141/125000000 : ℝ)) (X := (83856677914259/100000000000000 : ℝ)) (Y := (3228667895429/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (192436967/100000000 : ℝ)) (τ := (116403141/125000000 : ℝ)) (σ := (496572271/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (797215481/841106726 : ℝ) ^ p + (831545283/841106726 : ℝ) ^ p := by
    exact cert_lt (x := (797215481/841106726 : ℝ)) (y := (831545283/841106726 : ℝ)) (X := (25368552355707/100000000000000 : ℝ)) (Y := (74631448899199/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (116403141/125000000 : ℝ)) (n' := (420553363/500000000 : ℝ)) (Ab := (797215481/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (465612721/500000000 : ℝ) ^ p + (496572239/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (465612721/500000000 : ℝ)) (y := (496572239/500000000 : ℝ)) (X := (16143478794129/100000000000000 : ℝ)) (Y := (83856539608983/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (496572239/500000000 : ℝ) ^ p + (465612721/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (496572239/500000000 : ℝ)) (y := (465612721/500000000 : ℝ)) (X := (83856539608983/100000000000000 : ℝ)) (Y := (16143478794129/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (751707/390625 : ℝ)) (τ := (465612721/500000000 : ℝ)) (σ := (496572239/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797215817/841107093 : ℝ) ^ p + (831545650/841107093 : ℝ) ^ p := by
    exact cert_lt (x := (797215817/841107093 : ℝ)) (y := (831545650/841107093 : ℝ)) (X := (1268427135279/5000000000000 : ℝ)) (Y := (14926291696469/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (465612721/500000000 : ℝ)) (n' := (841107093/1000000000 : ℝ)) (Ab := (797215817/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (186245091/200000000 : ℝ) ^ p + (39725779/40000000 : ℝ) ^ p := by
    exact cert_lt (x := (186245091/200000000 : ℝ)) (y := (39725779/40000000 : ℝ)) (X := (3228696912411/20000000000000 : ℝ)) (Y := (83856533125929/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (39725779/40000000 : ℝ) ^ p + (186245091/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (39725779/40000000 : ℝ)) (y := (186245091/200000000 : ℝ)) (X := (83856533125929/100000000000000 : ℝ)) (Y := (3228696912411/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (797215831/841107108 : ℝ) ^ p + (831545665/841107108 : ℝ) ^ p := by
    exact cert_lt (x := (797215831/841107108 : ℝ)) (y := (831545665/841107108 : ℝ)) (X := (12684271264319/50000000000000 : ℝ)) (Y := (74631458874027/100000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (n' := (210276777/250000000 : ℝ)) (Ab := (797215831/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (192436993/100000000 : ℝ)) (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1665917969/1805772881 : ℝ) ^ p + (1796211438/1805772881 : ℝ) ^ p := by
    exact cert_lt (x := (1665917969/1805772881 : ℝ)) (y := (1796211438/1805772881 : ℝ)) (X := (3176254272729/25000000000000 : ℝ)) (Y := (43647491577929/50000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1118255634/1194227119 : ℝ) ^ p + (1184665676/1194227119 : ℝ) ^ p := by
    exact cert_lt (x := (1118255634/1194227119 : ℝ)) (y := (1184665676/1194227119 : ℝ)) (X := (18595379946951/100000000000000 : ℝ)) (Y := (16280924152189/20000000000000 : ℝ)) 819 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (39725779/40000000 : ℝ)) (U := (1194227119/1000000000 : ℝ)) (Ab := (1665917969/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (186245091/200000000 : ℝ)) (σ := (39725779/40000000 : ℝ)) (Ab := (559127817/500000000 : ℝ))
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

theorem localize21_slab146 (p : ℝ) (hpa : (409/16 : ℝ) ≤ p) (hpb : p ≤ (819/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1194227119/1000000000 : ℝ)) ∧ coordinateBox (4683/10000 : ℝ) (11183/10000 : ℝ) (979/1250 : ℝ) (11861/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (181627181457247/111657000000000 : ℝ) ≤ X j i + X k i) ∧
    (64994199665029/11165700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (19464971/20000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(409/16 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (19464971/20000000 : ℝ))
      (by norm_num) 16 409 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(409/16 : ℝ)) ≤ (973248551/1000000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (973248551/1000000000 : ℝ))
      (by norm_num) (by norm_num) 16 409 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(819/32 : ℝ)) ≤ (486640387/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (486640387/500000000 : ℝ))
      (by norm_num) (by norm_num) 32 819 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (259760512969/13957125000000 : ℝ) (9561443/1000000000 : ℝ) (2000000334971/11165700000000 : ℝ) (3033/2500 : ℝ) (486640387/250000000 : ℝ) (19464971/20000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (409/16 : ℝ)) (β := (819/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (259760512969/13957125000000 : ℝ)) (δ := (9561443/1000000000 : ℝ)) (h := (2000000334971/11165700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (19464971/20000000 : ℝ)) (thia := (973248551/1000000000 : ℝ)) (thib := (486640387/500000000 : ℝ))
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
  have hh := contract21_slab146 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 147, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab147 (p : ℝ) (hpa : (819/32 : ℝ) ≤ p) (hpb : p ≤ (205/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2077788602819/111793500000000 : ℝ) (4774047/500000000 : ℝ) (4000000670761/22358700000000 : ℝ) (3033/2500 : ℝ) (24332823/12500000 : ℝ) (973280773/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597119851/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(699/625 : ℝ) ≤ X j i ∧ X j i ≤ -(937/2000 : ℝ)
      else (3917/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11861/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2077788602819/111793500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4774047/500000000 : ℝ) := by norm_num
  have pc0 : 1 < (462865501/500000000 : ℝ) ^ p + (198840621/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (462865501/500000000 : ℝ)) (y := (198840621/200000000 : ℝ)) (X := (1384118294337/10000000000000 : ℝ)) (Y := (8615883654179/10000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (198840621/200000000 : ℝ) ^ p + (462865501/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (198840621/200000000 : ℝ)) (y := (462865501/500000000 : ℝ)) (X := (8615883654179/10000000000000 : ℝ)) (Y := (1384118294337/10000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1919934107/1000000000 : ℝ)) (τ := (462865501/500000000 : ℝ)) (σ := (198840621/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (79133995/83464081 : ℝ) ^ p + (412546358/417320405 : ℝ) ^ p := by
    exact cert_lt (x := (79133995/83464081 : ℝ)) (y := (412546358/417320405 : ℝ)) (X := (102137811319/400000000000 : ℝ)) (Y := (9308193568389/12500000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (462865501/500000000 : ℝ)) (n' := (83464081/100000000 : ℝ)) (Ab := (15826799/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931097869/1000000000 : ℝ) ^ p + (993195473/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931097869/1000000000 : ℝ)) (y := (993195473/1000000000 : ℝ)) (X := (4012780539319/25000000000000 : ℝ)) (Y := (83948896404509/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993195473/1000000000 : ℝ) ^ p + (931097869/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993195473/1000000000 : ℝ)) (y := (931097869/1000000000 : ℝ)) (X := (83948896404509/100000000000000 : ℝ)) (Y := (4012780539319/25000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (962146671/500000000 : ℝ)) (τ := (931097869/1000000000 : ℝ)) (σ := (993195473/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (4920389/5190941 : ℝ) ^ p + (138564058/140155407 : ℝ) ^ p := by
    exact cert_lt (x := (4920389/5190941 : ℝ)) (y := (138564058/140155407 : ℝ)) (X := (5073813406579/20000000000000 : ℝ)) (Y := (74630934430609/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931097869/1000000000 : ℝ)) (n' := (420466221/500000000 : ℝ)) (Ab := (398551509/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (116413417/125000000 : ℝ) ^ p + (99315261/100000000 : ℝ) ^ p := by
    exact cert_lt (x := (116413417/125000000 : ℝ)) (y := (99315261/100000000 : ℝ)) (X := (16143910406039/100000000000000 : ℝ)) (Y := (16771221504339/20000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (99315261/100000000 : ℝ) ^ p + (116413417/125000000 : ℝ) ^ p := by
    exact cert_lt (x := (99315261/100000000 : ℝ)) (y := (116413417/125000000 : ℝ)) (X := (16771221504339/20000000000000 : ℝ)) (Y := (16143910406039/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (962229973/500000000 : ℝ)) (τ := (116413417/125000000 : ℝ)) (σ := (99315261/100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797327253/841177280 : ℝ) ^ p + (415814593/420588640 : ℝ) ^ p := by
    exact cert_lt (x := (797327253/841177280 : ℝ)) (y := (415814593/420588640 : ℝ)) (X := (3170334255891/12500000000000 : ℝ)) (Y := (74637327460857/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (116413417/125000000 : ℝ)) (n' := (2628679/3125000 : ℝ)) (Ab := (797327253/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (931315431/1000000000 : ℝ) ^ p + (248287737/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (931315431/1000000000 : ℝ)) (y := (248287737/250000000 : ℝ)) (X := (807375329923/5000000000000 : ℝ)) (Y := (83852511646117/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (248287737/250000000 : ℝ) ^ p + (931315431/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (248287737/250000000 : ℝ)) (y := (931315431/1000000000 : ℝ)) (X := (83852511646117/100000000000000 : ℝ)) (Y := (807375329923/5000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924466379/1000000000 : ℝ)) (τ := (931315431/1000000000 : ℝ)) (σ := (248287737/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (797335917/841186741 : ℝ) ^ p + (831638647/841186741 : ℝ) ^ p := by
    exact cert_lt (x := (797335917/841186741 : ℝ)) (y := (831638647/841186741 : ℝ)) (X := (3170303301721/12500000000000 : ℝ)) (Y := (2332424201107/3125000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (931315431/1000000000 : ℝ)) (n' := (841186741/1000000000 : ℝ)) (Ab := (797335917/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (29103617/31250000 : ℝ) ^ p + (248287721/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (29103617/31250000 : ℝ)) (y := (248287721/250000000 : ℝ)) (X := (16147645663729/100000000000000 : ℝ)) (Y := (2620386661867/3125000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (248287721/250000000 : ℝ) ^ p + (29103617/31250000 : ℝ) ^ p := by
    exact cert_lt (x := (248287721/250000000 : ℝ)) (y := (29103617/31250000 : ℝ)) (X := (2620386661867/3125000000000 : ℝ)) (Y := (16147645663729/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (481116657/250000000 : ℝ)) (τ := (29103617/31250000 : ℝ)) (σ := (248287721/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (398668126/420593553 : ℝ) ^ p + (138606502/140197851 : ℝ) ^ p := by
    exact cert_lt (x := (398668126/420593553 : ℝ)) (y := (138606502/140197851 : ℝ)) (X := (3170302183739/12500000000000 : ℝ)) (Y := (74637583963467/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (29103617/31250000 : ℝ)) (n' := (420593553/500000000 : ℝ)) (Ab := (199334063/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (232828939/250000000 : ℝ) ^ p + (993150881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232828939/250000000 : ℝ)) (y := (993150881/1000000000 : ℝ)) (X := (126153523401/781250000000 : ℝ)) (Y := (41926183344569/50000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993150881/1000000000 : ℝ) ^ p + (232828939/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993150881/1000000000 : ℝ)) (y := (232828939/250000000 : ℝ)) (X := (41926183344569/50000000000000 : ℝ)) (Y := (126153523401/781250000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (1924466637/1000000000 : ℝ)) (τ := (232828939/250000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (159467253/168237424 : ℝ) ^ p + (415819513/420593560 : ℝ) ^ p := by
    exact cert_lt (x := (159467253/168237424 : ℝ)) (y := (415819513/420593560 : ℝ)) (X := (6340604312421/25000000000000 : ℝ)) (Y := (37318792164463/50000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (232828939/250000000 : ℝ)) (n' := (10514839/12500000 : ℝ)) (Ab := (159467253/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (931315757/1000000000 : ℝ) ^ p + (993150881/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931315757/1000000000 : ℝ)) (y := (993150881/1000000000 : ℝ)) (X := (4036912859907/25000000000000 : ℝ)) (Y := (41926183344569/50000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993150881/1000000000 : ℝ) ^ p + (931315757/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993150881/1000000000 : ℝ)) (y := (931315757/1000000000 : ℝ)) (X := (41926183344569/50000000000000 : ℝ)) (Y := (4036912859907/25000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (398668133/420593561 : ℝ) ^ p + (415819514/420593561 : ℝ) ^ p := by
    exact cert_lt (x := (398668133/420593561 : ℝ)) (y := (415819514/420593561 : ℝ)) (X := (25362416519563/100000000000000 : ℝ)) (Y := (37318792190567/50000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (n' := (420593561/500000000 : ℝ)) (Ab := (398668133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (n' := (420593561/500000000 : ℝ)) (Ab := (398668133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (n' := (420593561/500000000 : ℝ)) (Ab := (398668133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (n' := (420593561/500000000 : ℝ)) (Ab := (398668133/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962233319/500000000 : ℝ)) (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (833029802/902880149 : ℝ) ^ p + (898106102/902880149 : ℝ) ^ p := by
    exact cert_lt (x := (833029802/902880149 : ℝ)) (y := (898106102/902880149 : ℝ)) (X := (2540591677127/20000000000000 : ℝ)) (Y := (87297041821053/100000000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (1118349469/1194239702 : ℝ) ^ p + (592345804/597119851 : ℝ) ^ p := by
    exact cert_lt (x := (1118349469/1194239702 : ℝ)) (y := (592345804/597119851 : ℝ)) (X := (18592146834183/100000000000000 : ℝ)) (Y := (10175981720707/12500000000000 : ℝ)) 205 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993150881/1000000000 : ℝ)) (U := (597119851/500000000 : ℝ)) (Ab := (416514901/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (931315757/1000000000 : ℝ)) (σ := (993150881/1000000000 : ℝ)) (Ab := (1118349469/1000000000 : ℝ))
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

theorem localize21_slab147 (p : ℝ) (hpa : (819/32 : ℝ) ≤ p) (hpb : p ≤ (205/8 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (597119851/500000000 : ℝ)) ∧ coordinateBox (937/2000 : ℝ) (699/625 : ℝ) (3917/5000 : ℝ) (11861/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (11367016422283/6987093750000 : ℝ) ≤ X j i + X k i) ∧
    (130152199329239/22358700000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (973280773/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(819/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (973280773/1000000000 : ℝ))
      (by norm_num) 32 819 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(819/32 : ℝ)) ≤ (486640387/500000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (486640387/500000000 : ℝ))
      (by norm_num) (by norm_num) 32 819 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(205/8 : ℝ)) ≤ (24332823/25000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (24332823/25000000 : ℝ))
      (by norm_num) (by norm_num) 8 205 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (2077788602819/111793500000000 : ℝ) (4774047/500000000 : ℝ) (4000000670761/22358700000000 : ℝ) (3033/2500 : ℝ) (24332823/12500000 : ℝ) (973280773/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (819/32 : ℝ)) (β := (205/8 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (2077788602819/111793500000000 : ℝ)) (δ := (4774047/500000000 : ℝ)) (h := (4000000670761/22358700000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (973280773/1000000000 : ℝ)) (thia := (486640387/500000000 : ℝ)) (thib := (24332823/25000000 : ℝ))
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
  have hh := contract21_slab147 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 148, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab148 (p : ℝ) (hpa : (205/8 : ℝ) ≤ p) (hpb : p ≤ (821/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (4154988343/223860000000 : ℝ) (148981/15625000 : ℝ) (200000033579/1119300000000 : ℝ) (3033/2500 : ℝ) (243336247/125000000 : ℝ) (973312919/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (1194252287/1000000000 : ℝ)) ∧
    (∀ j i, if j = i then -(2237/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(2343/5000 : ℝ)
      else (1567/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11861/10000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (4154988343/223860000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (148981/15625000 : ℝ) := by norm_num
  have pc0 : 1 < (231456461/250000000 : ℝ) ^ p + (248552199/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (231456461/250000000 : ℝ)) (y := (248552199/250000000 : ℝ)) (X := (13844183484301/100000000000000 : ℝ)) (Y := (43077918296109/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (248552199/250000000 : ℝ) ^ p + (231456461/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (248552199/250000000 : ℝ)) (y := (231456461/250000000 : ℝ)) (X := (43077918296109/50000000000000 : ℝ)) (Y := (13844183484301/100000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (24000433/12500000 : ℝ)) (τ := (231456461/250000000 : ℝ)) (σ := (248552199/250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (395732725/417363537 : ℝ) ^ p + (412596145/417363537 : ℝ) ^ p := by
    exact cert_lt (x := (395732725/417363537 : ℝ)) (y := (412596145/417363537 : ℝ)) (X := (1595507862339/6250000000000 : ℝ)) (Y := (18617968798737/25000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (231456461/250000000 : ℝ)) (n' := (417363537/500000000 : ℝ)) (Ab := (15829309/20000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931188473/1000000000 : ℝ) ^ p + (993201767/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931188473/1000000000 : ℝ)) (y := (993201767/1000000000 : ℝ)) (X := (8027692082481/50000000000000 : ℝ)) (Y := (41972316710727/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (993201767/1000000000 : ℝ) ^ p + (931188473/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993201767/1000000000 : ℝ)) (y := (931188473/1000000000 : ℝ)) (X := (41972316710727/50000000000000 : ℝ)) (Y := (8027692082481/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (12027439/6250000 : ℝ)) (τ := (931188473/1000000000 : ℝ)) (σ := (993201767/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (797223737/841012878 : ℝ) ^ p + (415739047/420506439 : ℝ) ^ p := by
    exact cert_lt (x := (797223737/841012878 : ℝ)) (y := (415739047/420506439 : ℝ)) (X := (25362944020271/100000000000000 : ℝ)) (Y := (37318528422367/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931188473/1000000000 : ℝ)) (n' := (420506439/500000000 : ℝ)) (Ab := (797223737/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (931397431/1000000000 : ℝ) ^ p + (993158999/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931397431/1000000000 : ℝ)) (y := (993158999/1000000000 : ℝ)) (X := (1009254692877/6250000000000 : ℝ)) (Y := (16770388506729/20000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993158999/1000000000 : ℝ) ^ p + (931397431/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993158999/1000000000 : ℝ)) (y := (931397431/1000000000 : ℝ)) (X := (16770388506729/20000000000000 : ℝ)) (Y := (1009254692877/6250000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (192455643/100000000 : ℝ)) (τ := (931397431/1000000000 : ℝ)) (σ := (993158999/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797447419/841257088 : ℝ) ^ p + (1856523/1877806 : ℝ) ^ p := by
    exact cert_lt (x := (797447419/841257088 : ℝ)) (y := (1856523/1877806 : ℝ)) (X := (12678284847439/50000000000000 : ℝ)) (Y := (74643431552227/100000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (931397431/1000000000 : ℝ)) (n' := (6572321/7812500 : ℝ)) (Ab := (797447419/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (465702747/500000000 : ℝ) ^ p + (993157343/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465702747/500000000 : ℝ)) (y := (993157343/1000000000 : ℝ)) (X := (16151662007869/100000000000000 : ℝ)) (Y := (4192417773563/5000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993157343/1000000000 : ℝ) ^ p + (465702747/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993157343/1000000000 : ℝ)) (y := (465702747/500000000 : ℝ)) (X := (4192417773563/5000000000000 : ℝ)) (Y := (16151662007869/100000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924562837/1000000000 : ℝ)) (τ := (465702747/500000000 : ℝ)) (σ := (993157343/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (265818683/280422170 : ℝ) ^ p + (59409409/60090465 : ℝ) ^ p := by
    exact cert_lt (x := (265818683/280422170 : ℝ)) (y := (59409409/60090465 : ℝ)) (X := (25356323870173/100000000000000 : ℝ)) (Y := (18660919358661/25000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (465702747/500000000 : ℝ)) (n' := (84126651/100000000 : ℝ)) (Ab := (797456049/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (186281161/200000000 : ℝ) ^ p + (993157279/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (186281161/200000000 : ℝ)) (y := (993157279/1000000000 : ℝ)) (X := (4037950093817/25000000000000 : ℝ)) (Y := (83848216843789/100000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (993157279/1000000000 : ℝ) ^ p + (186281161/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993157279/1000000000 : ℝ)) (y := (186281161/200000000 : ℝ)) (X := (83848216843789/100000000000000 : ℝ)) (Y := (4037950093817/25000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (481140771/250000000 : ℝ)) (τ := (186281161/200000000 : ℝ)) (σ := (993157279/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797456381/841266873 : ℝ) ^ p + (831732089/841266873 : ℝ) ^ p := by
    exact cert_lt (x := (797456381/841266873 : ℝ)) (y := (831732089/841266873 : ℝ)) (X := (25356314002411/100000000000000 : ℝ)) (Y := (597149495261/800000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (186281161/200000000 : ℝ)) (n' := (841266873/1000000000 : ℝ)) (Ab := (797456381/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (931405817/1000000000 : ℝ) ^ p + (993157277/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (931405817/1000000000 : ℝ)) (y := (993157277/1000000000 : ℝ)) (X := (8075902857113/50000000000000 : ℝ)) (Y := (20962053127921/25000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993157277/1000000000 : ℝ) ^ p + (931405817/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (993157277/1000000000 : ℝ)) (y := (931405817/1000000000 : ℝ)) (X := (20962053127921/25000000000000 : ℝ)) (Y := (8075902857113/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (797456394/841266887 : ℝ) ^ p + (831732103/841266887 : ℝ) ^ p := by
    exact cert_lt (x := (797456394/841266887 : ℝ)) (y := (831732103/841266887 : ℝ)) (X := (6339078445349/25000000000000 : ℝ)) (Y := (37321843636487/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (n' := (841266887/1000000000 : ℝ)) (Ab := (398728197/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (962281547/500000000 : ℝ)) (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc18 : 1 < (1666200916/1805747713 : ℝ) ^ p + (256601847/257963959 : ℝ) ^ p := by
    exact cert_lt (x := (1666200916/1805747713 : ℝ)) (y := (256601847/257963959 : ℝ)) (X := (12700907884197/100000000000000 : ℝ)) (Y := (43649546173099/50000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (1118443140/1194252287 : ℝ) ^ p + (1184717503/1194252287 : ℝ) ^ p := by
    exact cert_lt (x := (1118443140/1194252287 : ℝ)) (y := (1184717503/1194252287 : ℝ)) (X := (9294462746063/50000000000000 : ℝ)) (Y := (3256443006633/4000000000000 : ℝ)) 821 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993157277/1000000000 : ℝ)) (U := (1194252287/1000000000 : ℝ)) (Ab := (416550229/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc18.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (931405817/1000000000 : ℝ)) (σ := (993157277/1000000000 : ℝ)) (Ab := (55922157/50000000 : ℝ))
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

theorem localize21_slab148 (p : ℝ) (hpa : (205/8 : ℝ) ≤ p) (hpb : p ≤ (821/32 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (1194252287/1000000000 : ℝ)) ∧ coordinateBox (2343/5000 : ℝ) (2237/2000 : ℝ) (1567/2000 : ℝ) (11861/10000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (18211734039679/11193000000000 : ℝ) ≤ X j i + X k i) ∧
    (6515799966421/1119300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (973312919/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(205/8 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (973312919/1000000000 : ℝ))
      (by norm_num) 8 205 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(205/8 : ℝ)) ≤ (24332823/25000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (24332823/25000000 : ℝ))
      (by norm_num) (by norm_num) 8 205 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(821/32 : ℝ)) ≤ (243336247/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (243336247/250000000 : ℝ))
      (by norm_num) (by norm_num) 32 821 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (4154988343/223860000000 : ℝ) (148981/15625000 : ℝ) (200000033579/1119300000000 : ℝ) (3033/2500 : ℝ) (243336247/125000000 : ℝ) (973312919/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (205/8 : ℝ)) (β := (821/32 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (4154988343/223860000000 : ℝ)) (δ := (148981/15625000 : ℝ)) (h := (200000033579/1119300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (973312919/1000000000 : ℝ)) (thia := (24332823/25000000 : ℝ)) (thib := (243336247/250000000 : ℝ))
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
  have hh := contract21_slab148 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
  refine ⟨hh.1, hh.2, ?_, ?_⟩
  · have hj := pair_floor_of_norm_data hp1 (by norm_num) hpa (by norm_num) X hS hh.1 hG htail
    norm_num at hj
    exact hj
  · have hw := FF.offsum 0 1 2 (by decide) (by decide) (by decide)
    linarith

end HlawkaSchatten.DiagonalRealBundle



/- Generated from the original ten-round rational contractor schedule.
   cutoff21/contractor.json, slab 149, paper Section 4.
   Every integer-power comparison below is checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 2048

namespace HlawkaSchatten.DiagonalRealBundle

theorem contract21_slab149 (p : ℝ) (hpa : (821/32 : ℝ) ≤ p) (hpb : p ≤ (411/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (2077199948207/112066500000000 : ℝ) (2380377/250000000 : ℝ) (4000000672399/22413300000000 : ℝ) (3033/2500 : ℝ) (48668849/25000000 : ℝ) (973344987/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (349/500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (597132429/500000000 : ℝ)) ∧
    (∀ j i, if j = i then -(5593/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(293/625 : ℝ)
      else (7837/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5931/5000 : ℝ)) := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (2077199948207/112066500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (2380377/250000000 : ℝ) := by norm_num
  have pc0 : 1 < (925920453/1000000000 : ℝ) ^ p + (497107237/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (925920453/1000000000 : ℝ)) (y := (497107237/500000000 : ℝ)) (X := (13847180095737/100000000000000 : ℝ)) (Y := (4307641927979/5000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc1 : 1 < (497107237/500000000 : ℝ) ^ p + (925920453/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (497107237/500000000 : ℝ)) (y := (925920453/1000000000 : ℝ)) (X := (4307641927979/5000000000000 : ℝ)) (Y := (13847180095737/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (1920134927/1000000000 : ℝ)) (τ := (925920453/1000000000 : ℝ)) (σ := (497107237/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (263863549/278271035 : ℝ) ^ p + (275097199/278271035 : ℝ) ^ p := by
    exact cert_lt (x := (263863549/278271035 : ℝ)) (y := (275097199/278271035 : ℝ)) (X := (510436219681/2000000000000 : ℝ)) (Y := (37239095313369/50000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (925920453/1000000000 : ℝ)) (n' := (166962621/200000000 : ℝ)) (Ab := (791590647/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (931278843/1000000000 : ℝ) ^ p + (19864161/20000000 : ℝ) ^ p := by
    exact cert_lt (x := (931278843/1000000000 : ℝ)) (y := (19864161/20000000 : ℝ)) (X := (16059637409743/100000000000000 : ℝ)) (Y := (83940379933853/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc4 : 1 < (19864161/20000000 : ℝ) ^ p + (931278843/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (19864161/20000000 : ℝ)) (y := (931278843/1000000000 : ℝ)) (X := (83940379933853/100000000000000 : ℝ)) (Y := (16059637409743/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1924486893/1000000000 : ℝ)) (τ := (931278843/1000000000 : ℝ)) (σ := (19864161/20000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (797344153/841093083 : ℝ) ^ p + (14588975/14756019 : ℝ) ^ p := by
    exact cert_lt (x := (797344153/841093083 : ℝ)) (y := (14588975/14756019 : ℝ)) (X := (25356833291153/100000000000000 : ℝ)) (Y := (74643168305469/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (931278843/1000000000 : ℝ)) (n' := (841093083/1000000000 : ℝ)) (Ab := (797344153/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (465743647/500000000 : ℝ) ^ p + (993165377/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465743647/500000000 : ℝ)) (y := (993165377/1000000000 : ℝ)) (X := (16152231274921/100000000000000 : ℝ)) (Y := (10480973440031/12500000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc7 : 1 < (993165377/1000000000 : ℝ) ^ p + (465743647/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993165377/1000000000 : ℝ)) (y := (465743647/500000000 : ℝ)) (X := (10480973440031/12500000000000 : ℝ)) (Y := (16152231274921/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1924652671/1000000000 : ℝ)) (τ := (465743647/500000000 : ℝ)) (σ := (993165377/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (797567282/841336667 : ℝ) ^ p + (831815159/841336667 : ℝ) ^ p := by
    exact cert_lt (x := (797567282/841336667 : ℝ)) (y := (831815159/841336667 : ℝ)) (X := (25350476193661/100000000000000 : ℝ)) (Y := (74649524756679/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (465743647/500000000 : ℝ)) (n' := (841336667/1000000000 : ℝ)) (Ab := (398783641/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (232873831/250000000 : ℝ) ^ p + (993163727/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (232873831/250000000 : ℝ)) (y := (993163727/1000000000 : ℝ)) (X := (16155808441693/100000000000000 : ℝ)) (Y := (524026308133/625000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc10 : 1 < (993163727/1000000000 : ℝ) ^ p + (232873831/250000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163727/1000000000 : ℝ)) (y := (232873831/250000000 : ℝ)) (X := (524026308133/625000000000 : ℝ)) (Y := (16155808441693/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R3 := ratio_round F L2 (by norm_num) hD0
    (s := (1924659051/1000000000 : ℝ)) (τ := (232873831/250000000 : ℝ)) (σ := (993163727/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (34677212/36580263 : ℝ) ^ p + (14593413/14760457 : ℝ) ^ p := by
    exact cert_lt (x := (34677212/36580263 : ℝ)) (y := (14593413/14760457 : ℝ)) (X := (20280185061/80000000000 : ℝ)) (Y := (1866244238041/2500000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L3 := lower_round F L2 (by norm_num) hd0
    (τ := (232873831/250000000 : ℝ)) (n' := (841346049/1000000000 : ℝ)) (Ab := (199393969/250000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R3 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  have pc12 : 1 < (931495633/1000000000 : ℝ) ^ p + (62072729/62500000 : ℝ) ^ p := by
    exact cert_lt (x := (931495633/1000000000 : ℝ)) (y := (62072729/62500000 : ℝ)) (X := (16155946108777/100000000000000 : ℝ)) (Y := (83844072681283/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc13 : 1 < (62072729/62500000 : ℝ) ^ p + (931495633/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (62072729/62500000 : ℝ)) (y := (931495633/1000000000 : ℝ)) (X := (83844072681283/100000000000000 : ℝ)) (Y := (16155946108777/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R4 := ratio_round F L3 (by norm_num) hD0
    (s := (1924659297/1000000000 : ℝ)) (τ := (931495633/1000000000 : ℝ)) (σ := (62072729/62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc12) (by norm_num; exact pc13)
  have pc14 : 1 < (797576207/841346410 : ℝ) ^ p + (21890129/22140695 : ℝ) ^ p := by
    exact cert_lt (x := (797576207/841346410 : ℝ)) (y := (21890129/22140695 : ℝ)) (X := (12675111083089/50000000000000 : ℝ)) (Y := (74649778939597/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L4 := lower_round F L3 (by norm_num) hd0
    (τ := (931495633/1000000000 : ℝ)) (n' := (84134641/100000000 : ℝ)) (Ab := (797576207/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R4 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc14.le) (by norm_num)
  have pc15 : 1 < (186299129/200000000 : ℝ) ^ p + (993163661/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (186299129/200000000 : ℝ)) (y := (993163661/1000000000 : ℝ)) (X := (8077975727547/50000000000000 : ℝ)) (Y := (41922033087787/50000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc16 : 1 < (993163661/1000000000 : ℝ) ^ p + (186299129/200000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163661/1000000000 : ℝ)) (y := (186299129/200000000 : ℝ)) (X := (41922033087787/50000000000000 : ℝ)) (Y := (8077975727547/50000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R5 := ratio_round F L4 (by norm_num) hD0
    (s := (962329653/500000000 : ℝ)) (τ := (186299129/200000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc15) (by norm_num; exact pc16)
  have pc17 : 1 < (797576221/841346425 : ℝ) ^ p + (831824917/841346425 : ℝ) ^ p := by
    exact cert_lt (x := (797576221/841346425 : ℝ)) (y := (831824917/841346425 : ℝ)) (X := (6337555496713/25000000000000 : ℝ)) (Y := (18662444832731/25000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L5 := lower_round F L4 (by norm_num) hd0
    (τ := (186299129/200000000 : ℝ)) (n' := (33653857/40000000 : ℝ)) (Ab := (797576221/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R5 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc17.le) (by norm_num)
  have pc18 : 1 < (465747823/500000000 : ℝ) ^ p + (993163661/1000000000 : ℝ) ^ p := by
    exact cert_lt (x := (465747823/500000000 : ℝ)) (y := (993163661/1000000000 : ℝ)) (X := (16155951900621/100000000000000 : ℝ)) (Y := (41922033087787/50000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc19 : 1 < (993163661/1000000000 : ℝ) ^ p + (465747823/500000000 : ℝ) ^ p := by
    exact cert_lt (x := (993163661/1000000000 : ℝ)) (y := (465747823/500000000 : ℝ)) (X := (41922033087787/50000000000000 : ℝ)) (Y := (16155951900621/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have R6 := ratio_round F L5 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc20 : 1 < (398788111/420673213 : ℝ) ^ p + (415912459/420673213 : ℝ) ^ p := by
    exact cert_lt (x := (398788111/420673213 : ℝ)) (y := (415912459/420673213 : ℝ)) (X := (25350222029327/100000000000000 : ℝ)) (Y := (74649779357013/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have L6 := lower_round F L5 (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (n' := (420673213/500000000 : ℝ)) (Ab := (398788111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R6 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R7 := ratio_round F L6 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L7 := lower_round F L6 (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (n' := (420673213/500000000 : ℝ)) (Ab := (398788111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R7 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R8 := ratio_round F L7 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L8 := lower_round F L7 (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (n' := (420673213/500000000 : ℝ)) (Ab := (398788111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R8 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have R9 := ratio_round F L8 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have L9 := lower_round F L8 (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (n' := (420673213/500000000 : ℝ)) (Ab := (398788111/500000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R9 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc20.le) (by norm_num)
  have Rf := ratio_round F L9 (by norm_num) hD0
    (s := (1924659307/1000000000 : ℝ)) (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc18) (by norm_num; exact pc19)
  have pc21 : 1 < (1666341889/1805735142 : ℝ) ^ p + (299368939/300955857 : ℝ) ^ p := by
    exact cert_lt (x := (1666341889/1805735142 : ℝ)) (y := (299368939/300955857 : ℝ)) (X := (2539771867741/20000000000000 : ℝ)) (Y := (2182528522531/2500000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have pc22 : 1 < (559268306/597132429 : ℝ) ^ p + (197457225/199044143 : ℝ) ^ p := by
    exact cert_lt (x := (559268306/597132429 : ℝ)) (y := (197457225/199044143 : ℝ)) (X := (9292853559907/50000000000000 : ℝ)) (Y := (81414293311441/100000000000000 : ℝ)) 411 16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) p hp0 (by norm_num at hpb ⊢; exact hpb)
  have V := upper_round F L9 (by norm_num) hd0
    (σ := (993163661/1000000000 : ℝ)) (U := (597132429/500000000 : ℝ)) (Ab := (1666341889/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc21.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L9 V (by norm_num) hd0
    (τ := (465747823/500000000 : ℝ)) (σ := (993163661/1000000000 : ℝ)) (Ab := (279634153/250000000 : ℝ))
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

theorem localize21_slab149 (p : ℝ) (hpa : (821/32 : ℝ) ≤ p) (hpb : p ≤ (411/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ) * p)) :
    (∀ i, lpNorm p (X i) ≤ (597132429/500000000 : ℝ)) ∧ coordinateBox (293/625 : ℝ) (5593/5000 : ℝ) (7837/10000 : ℝ) (5931/5000 : ℝ) X ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (91181208085139/56033250000000 : ℝ) ≤ X j i + X k i) ∧
    (130479799327601/22413300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  have hp1 : 1 ≤ p := by linarith
  have hpc : 21 ≤ p := by linarith
  have hcrit : 6 * Real.log 2 ≤ 2 / (273/625 : ℝ) := by
    have hh := Real.log_two_lt_d9
    norm_num
    linarith
  have htlo : (973344987/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(821/32 : ℝ)) := by
    have hh := le_rpow_of_pow_le (x := (1/2 : ℝ)) (X := (973344987/1000000000 : ℝ))
      (by norm_num) 32 821 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthia : (1/2 : ℝ) ^ (1/(821/32 : ℝ)) ≤ (243336247/250000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (243336247/250000000 : ℝ))
      (by norm_num) (by norm_num) 32 821 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have hthib : (1/2 : ℝ) ^ (1/(411/16 : ℝ)) ≤ (48668849/50000000 : ℝ) := by
    have hh := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (48668849/50000000 : ℝ))
      (by norm_num) (by norm_num) 16 411 (by norm_num) (by norm_num)
    norm_num at hh ⊢; exact hh
  have htail := refined_pair_tail21 hpc X hB hT.le
  have FF : Facts p (cp p) (2077199948207/112066500000000 : ℝ) (2380377/250000000 : ℝ) (4000000672399/22413300000000 : ℝ) (3033/2500 : ℝ) (48668849/25000000 : ℝ) (973344987/1000000000 : ℝ) X (fun i ↦ lpNorm p (X i)) := by
    have facts := facts_of (α := (821/32 : ℝ)) (β := (411/16 : ℝ)) (c := (273/625 : ℝ)) (eps := (1/100000000 : ℝ))
      (D := (2077199948207/112066500000000 : ℝ)) (δ := (2380377/250000000 : ℝ)) (h := (4000000672399/22413300000000 : ℝ)) (A := (3033/2500 : ℝ))
      (tlo := (973344987/1000000000 : ℝ)) (thia := (243336247/250000000 : ℝ)) (thib := (48668849/50000000 : ℝ))
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
  have hh := contract21_slab149 p hpa hpb X (fun i ↦ lpNorm p (X i)) FF hn0
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

theorem bounds_localized_domain4_21_37 (p : ℝ) (hpa : (409/16 : ℝ) ≤ p)
    (hpb : p ≤ (411/16 : ℝ)) (X : Triple)
    (hB : coordinateBox (189/500 : ℝ) (607/500 : ℝ) (349/500 : ℝ) (607/500 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ))
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p)) :
    (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  rcases le_total p (205/8 : ℝ) with hl | hr
  ·
    rcases le_total p (819/32 : ℝ) with hll | hlr
    ·
      have hh := localize21_slab146 p (by linarith) (by linarith) X hB hS hT hG
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
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (181627181457247/111657000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (64994199665029/11165700000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      have hh := localize21_slab147 p (by linarith) (by linarith) X hB hS hT hG
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
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (11367016422283/6987093750000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (130152199329239/22358700000000 : ℝ) by norm_num).trans hh.2.2.2.le
  ·
    rcases le_total p (821/32 : ℝ) with hrl | hrr
    ·
      have hh := localize21_slab148 p (by linarith) (by linarith) X hB hS hT hG
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
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (18211734039679/11193000000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (6515799966421/1119300000000 : ℝ) by norm_num).trans hh.2.2.2.le
    ·
      have hh := localize21_slab149 p (by linarith) (by linarith) X hB hS hT hG
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
        exact (show (82967765642843/51460500000000 : ℝ) ≤ (91181208085139/56033250000000 : ℝ) by norm_num).trans (hh.2.2.1 i j k hij hik hjk)
      · exact (show (59752599691237/10292100000000 : ℝ) ≤ (130479799327601/22413300000000 : ℝ) by norm_num).trans hh.2.2.2.le

end HlawkaSchatten.DiagonalRealBundle
theorem solution :
    ∀ p : ℝ, (409/16 : ℝ) ≤ p → p ≤ (411/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
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
  exact HlawkaSchatten.DiagonalRealBundle.bounds_localized_domain4_21_37 p hp hpmax X hB hS hT hG

#print axioms solution
