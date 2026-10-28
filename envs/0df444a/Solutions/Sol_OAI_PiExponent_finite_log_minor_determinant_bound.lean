-- Prove2me | solution 1 for OAI.PiExponent.finite_log_minor_determinant_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:10:31.156364+00:00
-- url     : https://prove2.me/submissions/417c1f05-1aa1-45e9-ae76-2e5fb7e46595

import Mathlib
import Definitions.Def_PiExponent_FiniteMinorComparison

section S_B1

open Real

namespace PiS36B

lemma log_le_div_e {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / Real.exp 1 := by
  have := Real.add_one_le_exp (Real.log t - 1)
  rw [Real.exp_sub, Real.exp_log ht] at this
  linarith

lemma small_case (n : ℕ) (hn : n ≤ 24) : (Nat.lcmUpto n : ℝ) ≤ 16 ^ (n + 1) := by
  have h1 : Nat.lcmUpto n ≤ n.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos n) (Nat.lcmUpto_dvd_factorial n)
  have h2 : n.factorial ≤ 16 ^ (n + 1) := by
    interval_cases n <;> decide
  exact_mod_cast h1.trans h2

lemma psi_bound (n : ℕ) : Real.log (Nat.lcmUpto n) ≤ 4 * Real.log 2 * ((n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  rcases le_or_gt n 24 with hn | hn
  · have := small_case n hn
    calc Real.log (Nat.lcmUpto n) ≤ Real.log (16 ^ (n + 1)) := Real.log_le_log hpos this
      _ = 4 * Real.log 2 * ((n : ℝ) + 1) := by
        rw [Real.log_pow, show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; push_cast; ring
  · rw [← Chebyshev.psi_eq_log_lcmUpto]
    have hx : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have h := Chebyshev.psi_le hx
    set x : ℝ := (n : ℝ) with hxdef
    have hx25 : (25:ℝ) ≤ x := by rw [hxdef]; exact_mod_cast (by omega : 25 ≤ n)
    set t : ℝ := Real.sqrt (Real.sqrt x)
    have ht0 : 0 < t := by positivity
    have hst : Real.sqrt x = t ^ 2 := by simp only [t]; rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
    have hxt : x = t ^ 4 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, ← hst, Real.sq_sqrt (by linarith)]
    have ht5 : (2.236 : ℝ) ≤ t := by
      have : Real.sqrt 25 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx25
      rw [show (25:ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num)] at this
      have h2 : Real.sqrt 5 ≤ t := by simp only [t]; exact Real.sqrt_le_sqrt this
      have : (2.236:ℝ) ≤ Real.sqrt 5 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      linarith
    have hlogx : Real.log x = 4 * Real.log t := by rw [hxt, Real.log_pow]; push_cast; ring
    have hlt := log_le_div_e ht0
    have he := Real.exp_one_gt_d9
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    have hl2 := Real.log_two_gt_d9
    -- 2 √x log x ≤ 8 t^3 / e ≤ log 4 * (x + 2)
    have key : 2 * Real.sqrt x * Real.log x ≤ Real.log 4 * (x + 2) := by
      rw [hst, hlogx]
      have hlt' : Real.log t * Real.exp 1 ≤ t := by
        have := hlt; rw [le_div_iff₀ (Real.exp_pos 1)] at this; exact this
      have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      have h8 : 8 ≤ Real.log 4 * t * Real.exp 1 := by
        rw [hl4]
        have : (2 * 0.6931471803 : ℝ) * 2.236 * 2.7182818283 ≤ 2 * Real.log 2 * t * Real.exp 1 := by
          gcongr
        nlinarith
      have : 2 * t ^ 2 * (4 * Real.log t) * Real.exp 1 ≤ Real.log 4 * t ^ 4 * Real.exp 1 := by
        have e1 : 2 * t ^ 2 * (4 * Real.log t) * Real.exp 1 = 8 * t ^ 2 * (Real.log t * Real.exp 1) := by ring
        rw [e1]
        calc 8 * t ^ 2 * (Real.log t * Real.exp 1) ≤ 8 * t ^ 2 * t := by gcongr
          _ ≤ (Real.log 4 * t * Real.exp 1) * t ^ 3 := by nlinarith [pow_pos ht0 3]
          _ = Real.log 4 * t ^ 4 * Real.exp 1 := by ring
      have hl4p : 0 < Real.log 4 := by rw [hl4]; linarith
      have := le_of_mul_le_mul_right this (Real.exp_pos 1)
      nlinarith
    rw [hl4] at key
    nlinarith
end PiS36B

end S_B1

section S_B2

open MvPolynomial

namespace PiS36B

lemma C_add_X_pow {σ A : Type*} [CommRing A] (c : A) (i : σ) (a : ℕ) :
    (C c + X i : MvPolynomial σ A) ^ a =
      ∑ k ∈ Finset.range (a + 1), monomial (Finsupp.single i k) ((a.choose k : A) * c ^ (a - k)) := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [X_pow_eq_monomial, ← C_pow, monomial_eq, monomial_eq]
  simp only [Finsupp.prod_single_index, pow_zero, C_mul, map_natCast, map_one, one_mul]
  ring

lemma coeff_prod_C_add_X {σ A : Type*} [Fintype σ] [DecidableEq σ] [CommRing A]
    (c : σ → A) (a : σ → ℕ) (b : σ →₀ ℕ) :
    (∏ i, (C (c i) + X i : MvPolynomial σ A) ^ (a i)).coeff b =
      ∏ i, (if b i ≤ a i then ((a i).choose (b i) : A) * c i ^ (a i - b i) else 0) := by
  simp_rw [C_add_X_pow]
  rw [Finset.prod_univ_sum]
  simp_rw [← monomial_sum_prod]
  rw [coeff_sum]
  simp_rw [coeff_monomial]
  have key : ∀ p : σ → ℕ, (∑ i, Finsupp.single i (p i) = b) ↔ p = ⇑b := by
    intro p
    rw [← Finsupp.equivFunOnFinite_symm_eq_sum]
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  by_cases hb : ∀ i, b i ≤ a i
  · rw [if_pos]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [if_pos (hb i)]
    · simp [Fintype.mem_piFinset, hb]
  · push Not at hb
    obtain ⟨i, hi⟩ := hb
    rw [if_neg, eq_comm]
    · exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg (by omega)])
    · simp only [Fintype.mem_piFinset, Finset.mem_range, not_forall]
      exact ⟨i, by omega⟩
end PiS36B

end S_B2

section S_B3

open MvPolynomial

namespace PiS36B

noncomputable abbrev ZP : Subring (Polynomial ℂ) := Polynomial.liftsRing GaussianInt.toComplex

lemma mem_ZP {P : Polynomial ℂ} : P ∈ ZP ↔ ∀ n, P.coeff n ∈ Set.range GaussianInt.toComplex := by
  show P ∈ Polynomial.lifts GaussianInt.toComplex ↔ _
  exact Polynomial.lifts_iff_coeff_lifts P

lemma C_mem_ZP {x : ℂ} (hx : x ∈ Set.range GaussianInt.toComplex) : Polynomial.C x ∈ ZP := by
  rw [mem_ZP]; intro n
  rw [Polynomial.coeff_C]; split_ifs
  · exact hx
  · exact ⟨0, by simp⟩

lemma X_mem_ZP : (Polynomial.X : Polynomial ℂ) ∈ ZP := by
  rw [mem_ZP]; intro n
  rw [Polynomial.coeff_X]; split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

lemma int_mem (k : ℤ) : (k : ℂ) ∈ Set.range GaussianInt.toComplex := ⟨k, by simp⟩

lemma logtrunc_mem (T L : ℕ) (hL : ∀ n, 1 ≤ n → n < T → n ∣ L) :
    Polynomial.C (L : ℂ) * PowerSeries.trunc T (PowerSeries.log ℂ) ∈ ZP := by
  rw [mem_ZP]; intro n
  rw [Polynomial.coeff_C_mul, PowerSeries.coeff_trunc]
  split_ifs with h
  · rw [PowerSeries.coeff_log]
    split_ifs with h0
    · exact ⟨0, by simp⟩
    · obtain ⟨k, hk⟩ := hL n (by omega) h
      refine ⟨((-1 : ℤ) ^ (n + 1) * k : ℤ), ?_⟩
      have hn : (n : ℂ) ≠ 0 := by exact_mod_cast h0
      simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]
      rw [hk]; push_cast
      field_simp
      simp [map_mul, map_pow, map_neg, map_one]
      ring
  · exact ⟨0, by simp⟩


open OAI.PiExponent.InterpolationMatrix OAI.PiExponent.MatrixArithmetic

lemma center_mem {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (L : Fin m → ℕ)
    (j : ℕ) (i : Fin m) :
    ((q i * L i : ℕ) : ℂ) * ((j : ℂ) * rationalCenters p q i) ∈ Set.range GaussianInt.toComplex := by
  refine ⟨⟨0, 2 * L i * j * p i⟩, ?_⟩
  have hqi : (q i : ℂ) ≠ 0 := by exact_mod_cast hq i
  simp [GaussianInt.toComplex_def, rationalCenters]
  field_simp

lemma factor_mem {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (T L : Fin m → ℕ)
    (hL : ∀ i n, 1 ≤ n → n < T i → n ∣ L i) (j : ℕ) (i : Fin m) :
    Polynomial.C ((q i * L i : ℕ) : ℂ) *
      (Polynomial.C ((j : ℂ) * rationalCenters p q i) + truncatedLog (T i)) ∈ ZP := by
  rw [mul_add, ← Polynomial.C_mul]
  refine ZP.add_mem (C_mem_ZP (center_mem p q hq L j i)) ?_
  have : Polynomial.C ((q i * L i : ℕ) : ℂ) * truncatedLog (T i) =
      Polynomial.C (q i : ℂ) * (Polynomial.C (L i : ℂ) * PowerSeries.trunc (T i) (PowerSeries.log ℂ)) := by
    rw [truncatedLog, ← mul_assoc, ← Polynomial.C_mul]; push_cast; rfl
  rw [this]
  exact ZP.mul_mem (C_mem_ZP (int_mem (q i))) (logtrunc_mem _ _ (hL i))

lemma entry_int {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (T L : Fin m → ℕ)
    (hL : ∀ i n, 1 ≤ n → n < T i → n ∣ L i) (j s h : ℕ) (b a : Fin m → ℕ) :
    ∃ z : GaussianInt,
      entry (rationalCenters p q) (fun i => truncatedLog (T i)) j s b h a *
          ∏ i, ((q i * L i : ℕ) : ℂ) ^ (a i) =
        GaussianInt.toComplex z * ∏ i, ((q i * L i : ℕ) : ℂ) ^ (b i) := by
  unfold entry monomialImage
  rw [MvPolynomial.coeff_C_mul, coeff_prod_C_add_X]
  have hev : ∀ i, (exponentVector b) i = b i := fun i => by simp [exponentVector]
  simp_rw [hev]
  by_cases hb : ∀ i, b i ≤ a i
  · simp_rw [if_pos (hb _)]
    set c : Fin m → Polynomial ℂ := fun i => Polynomial.C ((j : ℂ) * rationalCenters p q i) + truncatedLog (T i)
    set lam : Fin m → ℂ := fun i => ((q i * L i : ℕ) : ℂ)
    have hPm : (1 + Polynomial.X) ^ h * ∏ i, (((a i).choose (b i) : Polynomial ℂ) *
        (Polynomial.C (lam i) * c i) ^ (a i - b i)) ∈ ZP := by
      refine ZP.mul_mem (ZP.pow_mem (ZP.add_mem ZP.one_mem X_mem_ZP) _) ?_
      refine ZP.prod_mem fun i _ => ZP.mul_mem (natCast_mem ZP _) (ZP.pow_mem ?_ _)
      exact factor_mem p q hq T L hL j i
    obtain ⟨z, hz⟩ := (mem_ZP.1 hPm) s
    refine ⟨z, ?_⟩
    rw [hz]
    have hsplit : ∏ i, lam i ^ (a i) = (∏ i, lam i ^ (a i - b i)) * ∏ i, lam i ^ (b i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, Nat.sub_add_cancel (hb i)]
    rw [hsplit, ← mul_assoc]
    congr 1
    have : (1 + Polynomial.X) ^ h * ∏ i, (((a i).choose (b i) : Polynomial ℂ) *
        (Polynomial.C (lam i) * c i) ^ (a i - b i)) =
        Polynomial.C (∏ i, lam i ^ (a i - b i)) *
          ((1 + Polynomial.X) ^ h * ∏ i, (((a i).choose (b i) : Polynomial ℂ) * c i ^ (a i - b i))) := by
      rw [map_prod Polynomial.C, mul_left_comm, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_pow, Polynomial.C_pow]; ring
    rw [this, Polynomial.coeff_C_mul, mul_comm]
  · push Not at hb
    obtain ⟨i, hi⟩ := hb
    refine ⟨0, ?_⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg (by omega)])]
    simp

end PiS36B

end S_B3

section S_B4

open OAI.PiExponent OAI.PiExponent.InterpolationMatrix OAI.PiExponent.MatrixArithmetic

namespace PiS36B

lemma gauss_norm_ge_one (z : GaussianInt) (hz : z ≠ 0) : 1 ≤ ‖GaussianInt.toComplex z‖ := by
  have h1 : (1 : ℝ) ≤ (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    have : z.re ≠ 0 ∨ z.im ≠ 0 := by
      by_contra h; push Not at h; exact hz (Zsqrtd.ext h.1 h.2)
    have h2 : (1 : ℤ) ≤ z.re ^ 2 + z.im ^ 2 := by
      rcases this with h | h
      · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg z.im]
      · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg z.re]
    exact_mod_cast h2
  have : ‖GaussianInt.toComplex z‖ ^ 2 = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im]
    ring
  nlinarith [norm_nonneg (GaussianInt.toComplex z)]

lemma row_mem {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ} {x : Fin (m + 1) → ℕ}
    (hx : x ∈ strictWeightedSimplex (rowWeights v0 θ w) H) :
    v0 * x 0 + ∑ i, w i / θ * x i.succ < H := by
  simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter] at hx
  have := hx.2; rw [Fin.sum_univ_succ] at this; simpa [rowWeights] using this

lemma col_mem {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ} {x : Fin (m + 1) → ℕ}
    (hx : x ∈ realWeightedSimplex (columnWeights w0 w) H) :
    w0 * x 0 + ∑ i, w i * x i.succ ≤ H := by
  simp only [realWeightedSimplex, Finset.mem_filter] at hx
  have := hx.2; rw [Fin.sum_univ_succ] at this; simpa [columnWeights] using this

/-- Abstract determinant bound from the scaled integrality. -/
lemma det_lower {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : M.det ≠ 0)
    (nr dc : ι → ℝ) (hnr : ∀ i, 0 < nr i) (hdc : ∀ i, 0 < dc i)
    (hz : ∀ i j, ∃ z : GaussianInt, M i j * (dc j : ℂ) = GaussianInt.toComplex z * (nr i : ℂ)) :
    ∑ i, Real.log (nr i) - ∑ i, Real.log (dc i) ≤ Real.log ‖M.det‖ := by
  choose Z0 hZ using hz
  let Z : Matrix ι ι GaussianInt := Matrix.of Z0
  have hmat : M * Matrix.diagonal (fun j => (dc j : ℂ)) =
      Matrix.diagonal (fun i => (nr i : ℂ)) * (GaussianInt.toComplex.mapMatrix Z) := by
    ext i j
    simp [Z, Matrix.mul_diagonal, Matrix.diagonal_mul, hZ, mul_comm, RingHom.mapMatrix_apply]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    ← RingHom.map_det] at hdet
  have hZ0 : Z.det ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hdet
    have : (∏ j, (dc j : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by
      exact_mod_cast (hdc j).ne'
    exact mul_ne_zero hM this hdet
  have hn := congrArg norm hdet
  rw [norm_mul, norm_mul, norm_prod, norm_prod] at hn
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hnr _), abs_of_pos (hdc _)] at hn
  have hge := gauss_norm_ge_one _ hZ0
  have hP1 : 0 < ∏ j, dc j := Finset.prod_pos fun j _ => hdc j
  have hP2 : 0 < ∏ j, nr j := Finset.prod_pos fun j _ => hnr j
  have hle : ∏ j, nr j ≤ ‖M.det‖ * ∏ j, dc j := by rw [hn]; nlinarith
  have hdetpos : 0 < ‖M.det‖ := norm_pos_iff.2 hM
  have := Real.log_le_log hP2 hle
  rw [Real.log_mul hdetpos.ne' hP1.ne', Real.log_prod (fun j _ => (hdc j).ne'),
    Real.log_prod (fun j _ => (hnr j).ne')] at this
  linarith

end PiS36B

end S_B4

section S_B5
open OAI.PiExponent OAI.PiExponent.InterpolationMatrix OAI.PiExponent.MatrixArithmetic
open Filter Topology
open scoped BigOperators

namespace PiS36B

lemma log_lcm_le (T : ℕ) : Real.log (Nat.lcmUpto (T - 1)) ≤ 4 * Real.log 2 * T := by
  rcases Nat.eq_zero_or_pos T with h | h
  · subst h; simp [Nat.lcmUpto]
  · have := psi_bound (T - 1)
    have e : ((T - 1 : ℕ) : ℝ) + 1 = T := by
      rw [Nat.cast_sub h]; push_cast; ring
    rwa [e] at this

theorem main (m K : ℕ) (w0 v0 theta F wmin H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (hF : 0 ≤ F) (hmin : 0 < wmin)
    (hH : 0 < H) (hq : ∀ i, 2 ≤ q i)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection :
      OAI.PiExponent.InterpolationMatrix.Row K v0 theta
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H)
    (hdet : (OAI.PiExponent.MatrixArithmetic.selectedMinor K
      w0 v0 theta F H p q selection).det ≠ 0) :
    -(1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H) -
      OAI.PiExponent.FiniteMinorComparison.arithmeticError m v0 theta F wmin ≤
      Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K
        w0 v0 theta F H p q selection).det‖ /
        ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) := by

  have hq0 : ∀ i, q i ≠ 0 := fun i => by have := hq i; omega
  set T : Fin m → ℕ := truncationOrders q F v0 with hT
  set L : Fin m → ℕ := fun i => Nat.lcmUpto (T i - 1) with hLdef
  have hL : ∀ i n, 1 ≤ n → n < T i → n ∣ L i := fun i n h1 h2 =>
    Finset.dvd_lcm (s := Finset.Icc 1 (T i - 1)) (f := id) (Finset.mem_Icc.2 ⟨h1, by omega⟩)
  have hLpos : ∀ i, 0 < L i := fun i => Nat.lcmUpto_pos _
  have hlam : ∀ i, (0 : ℝ) < ((q i * L i : ℕ) : ℝ) := fun i => by
    have := hLpos i; have := hq0 i; positivity
  set M := selectedMinor K w0 v0 theta F H p q selection with hMdef
  let nr : Row K v0 theta (logWeights q) H → ℝ := fun ρ => ∏ i : Fin m, ((q i * L i : ℕ) : ℝ) ^ (ρ.2.1 i.succ)
  let dc : Row K v0 theta (logWeights q) H → ℝ := fun ρ' => ∏ i : Fin m, ((q i * L i : ℕ) : ℝ) ^ ((selection ρ').1 i.succ)
  have key := @det_lower _ _ _ M hdet nr dc (fun ρ => Finset.prod_pos fun i _ => pow_pos (hlam i) _)
    (fun ρ => Finset.prod_pos fun i _ => pow_pos (hlam i) _) (fun ρ ρ' => by
      obtain ⟨z, hz⟩ := entry_int p q hq0 T L hL ρ.1.val (ρ.2.1 0) ((selection ρ').1 0)
        (fun i : Fin m => ρ.2.1 i.succ) (fun i : Fin m => (selection ρ').1 i.succ)
      refine ⟨z, ?_⟩
      have hMe : M ρ ρ' = entry (rationalCenters p q) (fun i => truncatedLog (T i)) ρ.1.val (ρ.2.1 0)
          (fun i => ρ.2.1 i.succ) ((selection ρ').1 0) (fun i => (selection ρ').1 i.succ) := rfl
      rw [hMe]
      simp only [nr, dc]; push_cast
      push_cast at hz
      exact hz)
  -- logs of products
  have hlognr : ∀ ρ, Real.log (nr ρ) = ∑ i : Fin m, (ρ.2.1 i.succ : ℝ) * Real.log ((q i * L i : ℕ) : ℝ) := by
    intro ρ; simp only [nr]
    rw [Real.log_prod (fun i _ => (pow_pos (hlam i) _).ne')]
    simp [Real.log_pow]
  have hlogdc : ∀ ρ, Real.log (dc ρ) =
      ∑ i : Fin m, ((selection ρ).1 i.succ : ℝ) * Real.log ((q i * L i : ℕ) : ℝ) := by
    intro ρ; simp only [dc]
    rw [Real.log_prod (fun i _ => (pow_pos (hlam i) _).ne')]
    simp [Real.log_pow]
  have hlogq : ∀ i, 0 ≤ Real.log (q i) := fun i => Real.log_nonneg (by exact_mod_cast (by have := hq i; omega : 1 ≤ q i))
  have hlogL : ∀ i, 0 ≤ Real.log (L i) := fun i => Real.log_nonneg (by exact_mod_cast hLpos i)
  have hloglam : ∀ i, Real.log ((q i * L i : ℕ) : ℝ) = Real.log (q i) + Real.log (L i) := by
    intro i; push_cast
    exact Real.log_mul (by exact_mod_cast hq0 i) (by exact_mod_cast (hLpos i).ne')
  have hwq : ∀ i, logWeights q i - 1 ≤ Real.log (q i) := fun i => by
    have := Nat.ceil_lt_add_one (hlogq i); simp only [logWeights]; linarith
  have hwq' : ∀ i, Real.log (q i) ≤ logWeights q i := fun i => by simp only [logWeights]; exact Nat.le_ceil _
  have hwpos : ∀ i, 0 < logWeights q i := fun i => lt_of_lt_of_le hmin (hwmin i)
  -- row bound
  have hA : ∀ ρ : Row K v0 theta (logWeights q) H,
      (∑ i : Fin m, (ρ.2.1 i.succ : ℝ) * logWeights q i) - theta * H / wmin ≤ Real.log (nr ρ) := by
    intro ρ
    rw [hlognr]
    have hr := row_mem ρ.2.2
    have h0 : 0 ≤ v0 * (ρ.2.1 0 : ℝ) := by positivity
    have hs : ∑ i, logWeights q i * (ρ.2.1 i.succ : ℝ) < theta * H := by
      have : ∑ i, logWeights q i / theta * (ρ.2.1 i.succ : ℝ) = (∑ i, logWeights q i * (ρ.2.1 i.succ : ℝ)) / theta := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [this] at hr
      have : (∑ i, logWeights q i * (ρ.2.1 i.succ : ℝ)) / theta < H := by linarith
      rwa [div_lt_iff₀ htheta, mul_comm H] at this
    have hb : ∑ i : Fin m, (ρ.2.1 i.succ : ℝ) ≤ theta * H / wmin := by
      rw [le_div_iff₀ hmin, Finset.sum_mul]
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) hs.le
      rw [mul_comm (logWeights q i)]; exact mul_le_mul_of_nonneg_left (hwmin i) (by positivity)
    have : ∑ i, ((ρ.2.1 i.succ : ℝ) * logWeights q i - (ρ.2.1 i.succ : ℝ)) ≤
        ∑ i : Fin m, (ρ.2.1 i.succ : ℝ) * Real.log ((q i * L i : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hloglam]
      have := hwq i; have := hlogL i
      have hb0 : (0 : ℝ) ≤ ρ.2.1 i.succ := by positivity
      nlinarith
    rw [Finset.sum_sub_distrib] at this
    linarith
  -- column bound
  have hB : ∀ ρ : Row K v0 theta (logWeights q) H, Real.log (dc ρ) ≤
      H + 4 * Real.log 2 * (m * H * F / v0 + m * H / wmin) := by
    intro ρ
    rw [hlogdc]
    set a : Fin m → ℝ := fun i => ((selection ρ).1 i.succ : ℝ) with ha
    have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
    have hc := col_mem (selection ρ).2
    have hsum : ∑ i, logWeights q i * a i ≤ H := by
      have : 0 ≤ w0 * ((selection ρ).1 0 : ℝ) := by positivity
      simp only [ha]; linarith
    have hterm : ∀ i, logWeights q i * a i ≤ H := fun i => le_trans
      (Finset.single_le_sum (f := fun i => logWeights q i * a i) (fun j _ => mul_nonneg (hwpos j).le (ha0 j))
        (Finset.mem_univ i)) hsum
    have hai : ∀ i, a i ≤ H / wmin := fun i => by
      rw [le_div_iff₀ hmin]
      have := mul_le_mul_of_nonneg_left (hwmin i) (ha0 i)
      linarith [hterm i]
    have hTi : ∀ i, (T i : ℝ) ≤ F * logWeights q i / v0 + 1 := fun i => by
      have := Nat.ceil_lt_add_one (show 0 ≤ F * logWeights q i / v0 by
        have := hwpos i; positivity)
      simp only [hT, truncationOrders]; linarith
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hper : ∀ i, a i * Real.log ((q i * L i : ℕ) : ℝ) ≤
        logWeights q i * a i + 4 * Real.log 2 * (F / v0 * (logWeights q i * a i) + a i) := by
      intro i
      rw [hloglam]
      have h1 := hwq' i
      have h2 : Real.log (L i) ≤ 4 * Real.log 2 * T i := log_lcm_le (T i)
      have h3 := hTi i
      have : Real.log (q i) + Real.log (L i) ≤ logWeights q i + 4 * Real.log 2 * (F * logWeights q i / v0 + 1) := by
        nlinarith
      have h4 := mul_le_mul_of_nonneg_left this (ha0 i)
      have e : a i * (logWeights q i + 4 * Real.log 2 * (F * logWeights q i / v0 + 1)) =
          logWeights q i * a i + 4 * Real.log 2 * (F / v0 * (logWeights q i * a i) + a i) := by ring
      linarith
    calc ∑ i, a i * Real.log ((q i * L i : ℕ) : ℝ)
        ≤ ∑ i, (logWeights q i * a i + 4 * Real.log 2 * (F / v0 * (logWeights q i * a i) + a i)) :=
          Finset.sum_le_sum fun i _ => hper i
      _ = ∑ i, logWeights q i * a i + 4 * Real.log 2 * (F / v0 * ∑ i, logWeights q i * a i + ∑ i, a i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ H + 4 * Real.log 2 * (F / v0 * (m * H) + m * (H / wmin)) := by
          have e1 : ∑ i, logWeights q i * a i ≤ m * H := by
            have := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
            simpa using this
          have e2 : ∑ i, a i ≤ m * (H / wmin) := by
            have := Finset.sum_le_sum (s := Finset.univ) fun i _ => hai i
            simpa using this
          have : 0 ≤ F / v0 := by positivity
          gcongr
      _ = H + 4 * Real.log 2 * (m * H * F / v0 + m * H / wmin) := by ring
  -- assemble
  set N : ℕ := Fintype.card (Row K v0 theta (logWeights q) H) with hNdef
  have hN : 0 < N := by
    have h0 : (0 : Fin (m + 1) → ℕ) ∈ strictWeightedSimplex (rowWeights v0 theta (logWeights q)) H := by
      simp [strictWeightedSimplex, realWeightedSimplex, hH, hH.le]
    exact Fintype.card_pos_iff.2 ⟨(⟨0, hK⟩, ⟨0, h0⟩)⟩
  have hNH : (0 : ℝ) < N * H := by positivity
  have hsumA := Finset.sum_le_sum (s := Finset.univ) fun ρ _ => hA ρ
  have hsumB := Finset.sum_le_sum (s := Finset.univ) fun ρ _ => hB ρ
  rw [Finset.sum_sub_distrib] at hsumA
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumA hsumB
  rw [← hNdef] at hsumA hsumB
  have hrws : meanRowWeight K v0 theta q H * (N * H) =
      ∑ ρ : Row K v0 theta (logWeights q) H, ∑ i : Fin m, (ρ.2.1 i.succ : ℝ) * logWeights q i := by
    simp only [meanRowWeight, rowWeightedSum]
    rw [div_mul_cancel₀ _ hNH.ne']
  rw [le_div_iff₀ hNH]
  simp only [OAI.PiExponent.FiniteMinorComparison.arithmeticError]
  have e : (-(1 - meanRowWeight K v0 theta q H) -
      (4 * Real.log 2 * F * m / v0 + (4 * Real.log 2 * m + theta) / wmin)) * (N * H) =
      meanRowWeight K v0 theta q H * (N * H) - N * H -
        N * (4 * Real.log 2 * (m * H * F / v0 + m * H / wmin)) - N * (theta * H / wmin) := by
    field_simp; ring
  rw [e, hrws]
  linarith

end PiS36B

end S_B5

open OAI.PiExponent
open Filter Topology
open scoped BigOperators

theorem solution
    (m K : ℕ) (w0 v0 theta F wmin H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (hF : 0 ≤ F) (hmin : 0 < wmin)
    (hH : 0 < H) (hq : ∀ i, 2 ≤ q i)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection :
      OAI.PiExponent.InterpolationMatrix.Row K v0 theta
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H)
    (hdet : (OAI.PiExponent.MatrixArithmetic.selectedMinor K
      w0 v0 theta F H p q selection).det ≠ 0) :
    -(1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H) -
      OAI.PiExponent.FiniteMinorComparison.arithmeticError m v0 theta F wmin ≤
      Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K
        w0 v0 theta F H p q selection).det‖ /
        ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) :=
  PiS36B.main m K w0 v0 theta F wmin H p q hK hw0 hv0 htheta hF hmin hH hq hwmin selection hdet
