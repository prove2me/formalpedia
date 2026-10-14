-- Prove2me | solution 1 for IntMul.HvdH.Japprox_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T00:14:12.506836+00:00
-- url     : https://prove2.me/submissions/4680f876-db22-4997-91d1-5d672f5da9a2

import Definitions.Def_IntMul_HvdH_JApprox
import Theorems.Thm_IntMul_HvdH_Eapprox_bound

open Complex Real

namespace IntMul.HvdH.JPf
open IntMul.HvdH

/-- A pair of integers as a Gaussian integer in `ℂ`. -/
def toC (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

@[simp] lemma toC_re (p : ℤ × ℤ) : (toC p).re = p.1 := by simp [toC]
@[simp] lemma toC_im (p : ℤ × ℤ) : (toC p).im = p.2 := by simp [toC]

lemma norm_le_of_re_im {z : ℂ} {c : ℝ} (hre : |z.re| ≤ c) (him : |z.im| ≤ c) :
    ‖z‖ ≤ 3 / 2 * c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hre
  have h1 : z.re ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h2 : z.im ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have : ‖z‖ ^ 2 ≤ (3 / 2 * c) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this

lemma tdiv_err (m D : ℤ) (hD : 0 < D) : |((m.tdiv D : ℤ) : ℝ) - (m : ℝ) / D| ≤ 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 := Int.tmod_lt_of_pos m hD
  have h2 := Int.lt_tmod_of_pos m hD
  rw [Int.tmod_def] at h1 h2
  have h1' : (m : ℝ) - D * (m.tdiv D : ℤ) < D := by exact_mod_cast h1
  have h2' : -(D : ℝ) < m - D * (m.tdiv D : ℤ) := by exact_mod_cast h2
  have e : ((m.tdiv D : ℤ) : ℝ) - (m : ℝ) / D = -((m - D * (m.tdiv D : ℤ)) / D) := by
    field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos hD', div_le_one hD', abs_le]
  constructor <;> linarith

lemma hasSum_geom_int {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs) ((1 + r) / (1 - r)) := by
  have h1 : HasSum (fun n : ℕ => r ^ ((n : ℤ).natAbs)) (1 / (1 - r)) := by
    simpa [one_div] using hasSum_geometric_of_lt_one hr0 hr1
  have h2 : HasSum (fun n : ℕ => r ^ ((-((n : ℤ) + 1)).natAbs)) (r / (1 - r)) := by
    have e : (fun n : ℕ => r ^ ((-((n : ℤ) + 1)).natAbs)) = fun n : ℕ => r * r ^ n := by
      funext n; rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ, mul_comm]
    rw [e, div_eq_mul_inv]; exact (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have : 1 - r ≠ 0 := by linarith
  rw [show (1 + r) / (1 - r) = 1 / (1 - r) + r / (1 - r) by field_simp]
  exact h1.of_nat_of_neg_add_one h2

/-- If `0 ≤ f n ≤ C r^{|n|}` then `∑ f ≤ C (1+r)/(1-r)`. -/
lemma tsum_int_le_geom (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : ∀ n, f n ≤ C * r ^ n.natAbs) :
    Summable f ∧ ∑' n, f n ≤ C * ((1 + r) / (1 - r)) := by
  have hg := (hasSum_geom_int hr0 hr1).mul_left C
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hf hg.summable
  exact ⟨hs, hg.tsum_eq ▸ hs.tsum_le_tsum hf hg.summable⟩

/-- Variant excluding `n = 0`: if `f 0 = 0` and `0 ≤ f n ≤ C r^{|n|}` then `∑ f ≤ 2 C r/(1-r)`. -/
lemma tsum_int_le_geom' (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hz : f 0 = 0) {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hf : ∀ n, n ≠ 0 → f n ≤ C * r ^ n.natAbs) :
    Summable f ∧ ∑' n, f n ≤ 2 * C * r / (1 - r) := by
  have hC : ∀ n : ℤ, n ≠ 0 → 0 ≤ C * r ^ n.natAbs := fun n hn => (hf0 n).trans (hf n hn)
  set g : ℤ → ℝ := fun n => if n = 0 then 0 else C * r ^ n.natAbs
  have hg' := (hasSum_geom_int hr0 hr1).mul_left C
  have hg : HasSum g (C * ((1 + r) / (1 - r)) - C) := by
    have := hg'.update 0 0
    have hgu : g = Function.update (fun i : ℤ => C * r ^ i.natAbs) 0 0 := by
      funext n; by_cases h : n = 0 <;> simp [g, h]
    have e : C * ((1 + r) / (1 - r)) - C = 0 - C * r ^ Int.natAbs 0 + C * ((1 + r) / (1 - r)) := by
      simp only [Int.natAbs_zero, pow_zero, mul_one]; ring
    rw [hgu, e]; exact this
  have hfg : ∀ n, f n ≤ g n := by
    intro n; simp only [g]; split_ifs with h
    · rw [h, hz]
    · exact hf n h
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hfg hg.summable
  refine ⟨hs, (hs.tsum_le_tsum hfg hg.summable).trans (le_of_eq ?_)⟩
  rw [hg.tsum_eq]
  have : 1 - r ≠ 0 := by linarith
  field_simp; ring

/-- Key inequality of Lemma 4.6. -/
lemma key_ineq {q b1 b2 : ℝ} (hq : 1 ≤ q) (hb1 : |b1| ≤ 1 / 2) (hb2 : |b2| ≤ 1 / 2) {h : ℤ}
    (hh : h ≠ 0) : 2 * (q - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 ≤ (q * h + b1) ^ 2 - b2 ^ 2 := by
  have ha : 1 ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have hb2' : b2 ^ 2 ≤ 1 / 4 := by
    have := sq_abs b2 ▸ pow_le_pow_left₀ (abs_nonneg b2) hb2 2; nlinarith
  -- |q h + b1| ≥ q (|h| - 1/2)
  have h1 : q * (|(h : ℝ)| - 1 / 2) ≤ |q * h + b1| := by
    have e1 : |q * (h : ℝ)| = q * |(h : ℝ)| := by rw [abs_mul, abs_of_pos (by linarith)]
    have := abs_sub_abs_le_abs_sub (q * (h : ℝ)) (-b1)
    rw [sub_neg_eq_add, abs_neg, e1] at this
    nlinarith
  have h2 : 0 ≤ q * (|(h : ℝ)| - 1 / 2) := by nlinarith
  have h3 : (q * (|(h : ℝ)| - 1 / 2)) ^ 2 ≤ (q * h + b1) ^ 2 := by
    rw [← sq_abs (q * (h : ℝ) + b1)]; exact pow_le_pow_left₀ h2 h1 2
  rw [mul_pow] at h3
  set X := (|(h : ℝ)| - 1 / 2) ^ 2
  have e1 : 2 * q - 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have e2 : 1 / 4 ≤ X := by simp only [X]; nlinarith
  have e3 : (2 * q - 1) * X ≤ q ^ 2 * X := mul_le_mul_of_nonneg_right e1 (sq_nonneg _)
  nlinarith

lemma exp_neg_two_pi_le : Real.exp (-2 * π) ≤ 1 / 26 := by
  have hpi := Real.pi_gt_d2
  have h := Real.quadratic_le_exp_of_nonneg (x := 2 * π) (by positivity)
  rw [show -2 * π = -(2 * π) by ring, Real.exp_neg]
  rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  nlinarith

lemma exp_neg_pi_half_le : Real.exp (-π / 2) ≤ 1 / 4.3 := by
  have hpi := Real.pi_gt_d2
  have h := Real.quadratic_le_exp_of_nonneg (x := π / 4) (by positivity)
  have e : Real.exp (π / 2) = Real.exp (π / 4) * Real.exp (π / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hq : 2.09 ≤ Real.exp (π / 4) := by nlinarith
  have h2 : 4.3 ≤ Real.exp (π / 2) := by rw [e]; nlinarith
  rw [show -π / 2 = -(π / 2) by ring, Real.exp_neg, inv_eq_one_div,
    div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- Numerical inequality behind Lemma 4.6: for `x ≥ 1`,
`2 e^{-πx/2} / (1 - e^{-2πx}) < 2^{-x}`. -/
lemma numeric_E {x : ℝ} (hx : 1 ≤ x) :
    2 * Real.exp (-π * x / 2) / (1 - Real.exp (-2 * π * x)) < (2 : ℝ) ^ (-x) := by
  have hpi := Real.pi_gt_d2
  have hl := Real.log_two_lt_d9
  have hr : Real.exp (-2 * π * x) ≤ 1 / 26 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_two_pi_le
    nlinarith [Real.pi_pos]
  have hr0 := Real.exp_pos (-2 * π * x)
  set A := Real.exp (-x * Real.log 2) with hA
  have hApos : 0 < A := Real.exp_pos _
  have h2x : (2 : ℝ) ^ (-x) = A := by
    rw [Real.rpow_def_of_pos two_pos, hA]; ring_nf
  rw [h2x, div_lt_iff₀ (by linarith)]
  have hsplit : Real.exp (-π * x / 2) = A * Real.exp (-x * (π / 2 - Real.log 2)) := by
    rw [hA, ← Real.exp_add]; ring_nf
  have hmono : Real.exp (-x * (π / 2 - Real.log 2)) ≤ Real.exp (-(π / 2 - Real.log 2)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have hval : Real.exp (-(π / 2 - Real.log 2)) = 2 * Real.exp (-π / 2) := by
    rw [show -(π / 2 - Real.log 2) = Real.log 2 + -π / 2 by ring, Real.exp_add,
      Real.exp_log two_pos]
  have hb := exp_neg_pi_half_le
  have : Real.exp (-x * (π / 2 - Real.log 2)) ≤ 2 / 4.3 := by
    rw [hval] at hmono; linarith
  rw [hsplit]
  nlinarith


variable (s t α : ℕ)

/-- `x = α²θ = α²(t - s)/s`. -/
noncomputable def xθ : ℝ := ((α ^ 2 * (t - s) : ℕ) : ℝ) / s

lemma bOf_bounds (hs : 0 < s) (l : ℤ) :
    -(s : ℤ) ≤ 2 * bOf s t l ∧ 2 * bOf s t l < s := by
  have hs2 : (0 : ℤ) < 2 * s := by omega
  have h1 := Int.ediv_mul_le (2 * t * l + s) hs2.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (2 * t * l + s) hs2
  unfold bOf
  generalize (2 * (t : ℤ) * l + s) / (2 * s) = q at h1 h2 ⊢
  constructor <;> nlinarith

lemma abs_b_le (hs : 0 < s) (l : ℤ) : |(bOf s t l : ℝ) / s| ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := bOf_bounds s t hs l
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h1' : -(s : ℝ) ≤ 2 * bOf s t l := by exact_mod_cast h1
  have h2' : 2 * (bOf s t l : ℝ) ≤ s := by exact_mod_cast h2.le
  rw [abs_div, abs_of_pos hsR, div_le_iff₀ hsR, abs_le]
  constructor <;> linarith

lemma eEx_nonneg (l h : ℤ) : 0 ≤ eEx s t α l h := by
  unfold eEx; split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma eEx_le_gauss (hs : 0 < s) (hst : s ≤ t) (l h : ℤ) (hh : h ≠ 0) :
    eEx s t α l h ≤ Real.exp (-2 * π * xθ s t α * (|(h : ℝ)| - 1 / 2) ^ 2) := by
  unfold eEx; rw [if_neg hh]
  apply Real.exp_le_exp.2
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hq : 1 ≤ (t : ℝ) / s := by rw [one_le_div hsR]; exact_mod_cast hst
  have key := key_ineq hq (abs_b_le s t hs l) (abs_b_le s t hs (l + h)) hh
  have hK : (eKz s t l h : ℝ) / s ^ 2 =
      ((t : ℝ) / s * h + (bOf s t l : ℝ) / s) ^ 2 - ((bOf s t (l + h) : ℝ) / s) ^ 2 := by
    unfold eKz; push_cast; field_simp
  have hx : xθ s t α = α ^ 2 * ((t : ℝ) / s - 1) := by
    unfold xθ; rw [Nat.cast_mul, Nat.cast_sub hst]; push_cast; field_simp
  have hpa : (0 : ℝ) ≤ π * α ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left key hpa
  rw [← hK] at this
  rw [hx]
  have e : π * α ^ 2 * (eKz s t l h : ℝ) / s ^ 2 = π * α ^ 2 * ((eKz s t l h : ℝ) / s ^ 2) := by ring
  rw [e]; nlinarith

lemma eEx_sum (hs : 0 < s) (hst : s ≤ t) (hx : 1 ≤ xθ s t α) (l : ℤ) :
    Summable (eEx s t α l) ∧ ∑' h, eEx s t α l h ≤ (2 : ℝ) ^ (-xθ s t α) := by
  set x := xθ s t α
  have hx0 : 0 ≤ x := by linarith
  have hgeom := tsum_int_le_geom' (eEx s t α l) (eEx_nonneg s t α l) (by simp [eEx])
    (C := Real.exp (3 * π * x / 2)) (r := Real.exp (-2 * π * x)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])) (by
      intro h hh
      refine (eEx_le_gauss s t α hs hst l h hh).trans ?_
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ha : (h.natAbs : ℝ) = |(h : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [ha]
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hx0) (sq_nonneg (|(h : ℝ)| - 1))])
  refine ⟨hgeom.1, hgeom.2.trans (le_of_lt ?_)⟩
  have e : 2 * Real.exp (3 * π * x / 2) * Real.exp (-2 * π * x) = 2 * Real.exp (-π * x / 2) := by
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  rw [e]; exact numeric_E hx

section
variable {s t α}

/-- Bound and summability of the series defining `(E f)_ℓ` for bounded `f`. -/
lemma E_summ (hs : 0 < s) (hst : s ≤ t) (hx : 1 ≤ xθ s t α) {f : ℕ → ℂ} {M : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ M) (l : ℕ) :
    Summable (fun h : ℤ => ‖((eEx s t α l h : ℝ) : ℂ) * f ((l + h) % s).toNat‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun h => ?_)
    ((eEx_sum s t α hs hst hx l).1.mul_right M)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (eEx_nonneg s t α _ _)]
  exact mul_le_mul_of_nonneg_left (hf _) (eEx_nonneg s t α _ _)

lemma E_norm (hs : 0 < s) (hst : s ≤ t) (hx : 1 ≤ xθ s t α) {f : ℕ → ℂ} {M : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ M) (l : ℕ) :
    ‖Eexact s t α f l‖ ≤ (2 : ℝ) ^ (-xθ s t α) * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf 0)
  obtain ⟨hS, hT⟩ := eEx_sum s t α hs hst hx l
  unfold Eexact
  refine (norm_tsum_le_tsum_norm (E_summ hs hst hx hf l)).trans ?_
  calc ∑' h : ℤ, ‖((eEx s t α l h : ℝ) : ℂ) * f ((l + h) % s).toNat‖
      ≤ ∑' h : ℤ, eEx s t α l h * M := by
        refine (E_summ hs hst hx hf l).tsum_le_tsum (fun h => ?_) (hS.mul_right M)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (eEx_nonneg s t α _ _)]
        exact mul_le_mul_of_nonneg_left (hf _) (eEx_nonneg s t α _ _)
    _ = (∑' h : ℤ, eEx s t α l h) * M := tsum_mul_right
    _ ≤ (2 : ℝ) ^ (-xθ s t α) * M := mul_le_mul_of_nonneg_right hT hM

lemma E_sub (hs : 0 < s) (hst : s ≤ t) (hx : 1 ≤ xθ s t α) {f g : ℕ → ℂ} {M N : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ M) (hg : ∀ i, ‖g i‖ ≤ N) (l : ℕ) :
    Eexact s t α (fun i => f i - g i) l = Eexact s t α f l - Eexact s t α g l := by
  unfold Eexact
  rw [← (E_summ hs hst hx hf l).of_norm.tsum_sub (E_summ hs hst hx hg l).of_norm]
  congr 1; funext h; ring

/-- Iterates of `E`. -/
noncomputable def Eit (j : ℕ) (f : ℕ → ℂ) : ℕ → ℂ := (Eexact s t α)^[j] f

lemma Eit_bound (hs : 0 < s) (hst : s ≤ t) (hx : 1 ≤ xθ s t α) {f : ℕ → ℂ} {M : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ M) (j : ℕ) : ∀ i, ‖Eit (s := s) (t := t) (α := α) j f i‖ ≤ ((2 : ℝ) ^ (-xθ s t α)) ^ j * M := by
  induction j with
  | zero => simpa [Eit] using hf
  | succ j ih =>
    intro i
    have := E_norm hs hst hx ih i
    simp only [Eit, Function.iterate_succ_apply'] at this ⊢
    rw [pow_succ]; linarith [show (2 : ℝ) ^ (-xθ s t α) * (((2 : ℝ) ^ (-xθ s t α)) ^ j * M) =
      ((2 : ℝ) ^ (-xθ s t α)) ^ j * (2 : ℝ) ^ (-xθ s t α) * M by ring]

lemma Eit_sub (hs : 0 < s) (hst : s ≤ t) (hx : 1 ≤ xθ s t α) {f g : ℕ → ℂ} {M N : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ M) (hg : ∀ i, ‖g i‖ ≤ N) (j : ℕ) :
    Eit (s := s) (t := t) (α := α) j (fun i => f i - g i) =
      fun i => Eit (s := s) (t := t) (α := α) j f i - Eit (s := s) (t := t) (α := α) j g i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext i
    simp only [Eit, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]
    exact E_sub hs hst hx (Eit_bound hs hst hx hf j) (Eit_bound hs hst hx hg j) i

end

/-- `2^{-x} ≤ 1/2` for `x ≥ 1`. -/
lemma lam_le (x : ℝ) (hx : 1 ≤ x) : (2 : ℝ) ^ (-x) ≤ 1 / 2 := by
  have : (2 : ℝ) ^ (-x) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_neg_one] at this; linarith

/-- Lemma 4.12. -/
theorem Japprox_bound (p s t α : ℕ) (hs : 0 < s) (hx : s ≤ α ^ 2 * (t - s))
    (hpB : 2 * (10 * eWidth p α + 12) ≤ 2 ^ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖toC (U i)‖ ≤ 2 ^ p)
    (w : ℕ → ℂ) (hw : ∀ l, ‖w l‖ ≤ 1)
    (hJ : ∀ l, w l + Eexact s t α w l = toC (U l) / 2 ^ p / 2) (l : ℕ) :
    ‖toC (Japprox p s t α U l) - 2 ^ p * w l‖ ≤ jIter p s t α * (10 * eWidth p α + 12) + 1 := by
  have hD : 0 < α ^ 2 * (t - s) := by omega
  have hts : s < t := by
    rcases Nat.lt_or_ge s t with h | h
    · exact h
    · rw [Nat.sub_eq_zero_of_le h, mul_zero] at hD; omega
  have hα : 1 ≤ α := by
    rcases Nat.eq_zero_or_pos α with h | h
    · subst h; simp at hD
    · exact h
  have hst := hts.le
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hxR : 1 ≤ xθ s t α := by
    unfold xθ; rw [le_div_iff₀ hsR, one_mul]; exact_mod_cast hx
  set x := xθ s t α with hxdef
  set Λ : ℝ := (2 : ℝ) ^ (-x) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛ2 : Λ ≤ 1 / 2 := lam_le x hxR
  set m := eWidth p α
  set B : ℝ := 10 * m + 12 with hB
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hBp : 2 * B ≤ 2 ^ p := by
    have : ((2 * (10 * m + 12) : ℕ) : ℝ) ≤ ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast hpB
    push_cast at this; rw [hB]; linarith
  have hB0 : 0 ≤ B := by positivity
  set v : ℕ → ℂ := fun i => toC (U i) / 2 ^ p / 2 with hv
  have hvb : ∀ i, ‖v i‖ ≤ 1 / 2 := by
    intro i; simp only [hv]
    simp only [norm_div, norm_pow, Complex.norm_two]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), div_le_iff₀ hp]
    have := hU i; linarith
  -- errors of the iterates
  have herr : ∀ j, ∀ i, ‖toC (vIter p s t α U j i) - 2 ^ p * Eit (s := s) (t := t) (α := α) j v i‖ ≤ B := by
    intro j
    induction j with
    | zero =>
      intro i
      have h1 : ‖toC (halfFP U i) - toC (U i) / 2‖ ≤ 3 / 2 := by
        have h2C : (((2 : ℤ) : ℝ) : ℂ) = (2 : ℂ) := by push_cast; rfl
        refine (norm_le_of_re_im (c := 1) ?_ ?_).trans (by norm_num)
        · rw [← h2C, Complex.sub_re, Complex.div_ofReal_re, toC_re, toC_re]
          exact tdiv_err (U i).1 2 (by norm_num)
        · rw [← h2C, Complex.sub_im, Complex.div_ofReal_im, toC_im, toC_im]
          exact tdiv_err (U i).2 2 (by norm_num)
      have e : (2 : ℂ) ^ p * Eit (s := s) (t := t) (α := α) 0 v i = toC (U i) / 2 := by
        simp only [Eit, Function.iterate_zero, id, hv]
        field_simp
      simp only [vIter]; rw [e]; linarith
    | succ j ih =>
      intro i
      -- the input to Eapprox is bounded by 2^p
      have hin : ∀ k, ‖toC (vIter p s t α U j k)‖ ≤ 2 ^ p := by
        intro k
        have h1 := ih k
        have h2 := Eit_bound hs hst hxR hvb j k
        have hΛj : Λ ^ j ≤ 1 := pow_le_one₀ hΛ0 (by linarith)
        have h3 : ‖(2 : ℂ) ^ p * Eit (s := s) (t := t) (α := α) j v k‖ ≤ 2 ^ p * (1 / 2) := by
          rw [norm_mul, norm_pow, Complex.norm_two]
          apply mul_le_mul_of_nonneg_left _ hp.le
          calc _ ≤ Λ ^ j * (1 / 2) := h2
            _ ≤ 1 * (1 / 2) := by gcongr
            _ = 1 / 2 := by ring
        have := norm_le_insert' (toC (vIter p s t α U j k)) ((2 : ℂ) ^ p * Eit (s := s) (t := t) (α := α) j v k)
        linarith
      set a : ℕ → ℂ := fun k => toC (vIter p s t α U j k) / 2 ^ p with ha
      have hEa := Eapprox_bound p s t α i hs hst hα (vIter p s t α U j) hin
      change ‖toC (Eapprox p s t α (vIter p s t α U j) i) - 2 ^ p * Eexact s t α a i‖ ≤ 5 * m + 5 at hEa
      -- a - E^j v is small
      have hab : ∀ k, ‖a k - Eit (s := s) (t := t) (α := α) j v k‖ ≤ B / 2 ^ p := by
        intro k
        have e : a k - Eit (s := s) (t := t) (α := α) j v k =
            (toC (vIter p s t α U j k) - 2 ^ p * Eit (s := s) (t := t) (α := α) j v k) / 2 ^ p := by
          simp only [ha]; field_simp
        rw [e, norm_div, norm_pow, Complex.norm_two]
        exact div_le_div_of_nonneg_right (ih k) hp.le
      have hab' : ∀ k, ‖a k‖ ≤ 1 := by
        intro k; simp only [ha]
        rw [norm_div, norm_pow, Complex.norm_two, div_le_one hp]; exact hin k
      have hsub := E_sub hs hst hxR hab' (Eit_bound hs hst hxR hvb j) i
      have hEd := E_norm hs hst hxR hab i
      have hdiff : Eexact s t α a i - Eit (s := s) (t := t) (α := α) (j + 1) v i =
          Eexact s t α (fun k => a k - Eit (s := s) (t := t) (α := α) j v k) i := by
        rw [hsub]; simp only [Eit, Function.iterate_succ_apply']
      have hsplit : toC (vIter p s t α U (j + 1) i) - 2 ^ p * Eit (s := s) (t := t) (α := α) (j + 1) v i
          = (toC (Eapprox p s t α (vIter p s t α U j) i) - 2 ^ p * Eexact s t α a i)
            + 2 ^ p * (Eexact s t α a i - Eit (s := s) (t := t) (α := α) (j + 1) v i) := by
        simp only [vIter]; ring
      rw [hsplit, hdiff]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_pow, Complex.norm_two]
      have h4 : (2 : ℝ) ^ p * ‖Eexact s t α (fun k => a k - Eit (s := s) (t := t) (α := α) j v k) i‖ ≤ B / 2 := by
        calc _ ≤ 2 ^ p * (Λ * (B / 2 ^ p)) := mul_le_mul_of_nonneg_left hEd hp.le
          _ = Λ * B := by field_simp
          _ ≤ 1 / 2 * B := mul_le_mul_of_nonneg_right hΛ2 hB0
          _ = B / 2 := by ring
      have hmB : (5 * m + 5 : ℝ) + B / 2 ≤ B := by rw [hB]; linarith
      linarith
  -- telescoping identity
  have htel : ∀ n, w = fun i => ∑ j ∈ Finset.range n, (-1) ^ j * Eit (s := s) (t := t) (α := α) j v i
      + (-1) ^ n * Eit (s := s) (t := t) (α := α) n w i := by
    have hwv : w = fun i => v i - Eexact s t α w i := by
      funext i; have := hJ i; simp only [hv]; rw [← this]; ring
    have hEw : ∀ i, ‖Eexact s t α w i‖ ≤ Λ * 1 := fun i => E_norm hs hst hxR hw i
    intro n
    induction n with
    | zero => funext i; simp [Eit]
    | succ n ih =>
      have hstep : Eit (s := s) (t := t) (α := α) n w = fun i => Eit (s := s) (t := t) (α := α) n v i -
          Eit (s := s) (t := t) (α := α) (n + 1) w i := by
        conv_lhs => rw [hwv]
        rw [Eit_sub hs hst hxR hvb hEw n]
        funext i; simp only [Eit, Function.iterate_succ_apply]
      funext i
      have := congrFun ih i
      rw [this, Finset.sum_range_succ, hstep]
      simp only [pow_succ]; ring
  -- assemble
  set n := jIter p s t α with hn
  have hZ : toC (Japprox p s t α U l) = ∑ j ∈ Finset.range n, (-1) ^ j * toC (vIter p s t α U j l) := by
    simp only [Japprox, toC, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have hwl := congrFun (htel n) l
  have e : toC (Japprox p s t α U l) - 2 ^ p * w l =
      ∑ j ∈ Finset.range n, (-1) ^ j * (toC (vIter p s t α U j l) - 2 ^ p * Eit (s := s) (t := t) (α := α) j v l)
        - 2 ^ p * ((-1) ^ n * Eit (s := s) (t := t) (α := α) n w l) := by
    rw [hZ, hwl]; simp only [mul_sub, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
    ring_nf
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖∑ j ∈ Finset.range n, (-1) ^ j * (toC (vIter p s t α U j l) - 2 ^ p * Eit (s := s) (t := t) (α := α) j v l)‖
      ≤ n * B := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j ∈ Finset.range n, B := Finset.sum_le_sum (fun j _ => by
            rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]; exact herr j l)
      _ = n * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 : ‖(2 : ℂ) ^ p * ((-1) ^ n * Eit (s := s) (t := t) (α := α) n w l)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_two]
    have hb := Eit_bound hs hst hxR hw n l
    have hnx : (p : ℝ) ≤ x * n := by
      have hc : p * s ≤ n * (α ^ 2 * (t - s)) := by
        have := Nat.lt_mul_div_succ (p * s + α ^ 2 * (t - s) - 1) hD
        rw [hn, jIter]
        generalize (p * s + α ^ 2 * (t - s) - 1) / (α ^ 2 * (t - s)) = Q at this ⊢
        generalize α ^ 2 * (t - s) = D at this hD ⊢
        rw [mul_add, mul_one] at this
        rw [mul_comm Q D]
        generalize D * Q = P at this ⊢
        omega
      have hcR : ((p * s : ℕ) : ℝ) ≤ ((n * (α ^ 2 * (t - s)) : ℕ) : ℝ) := by exact_mod_cast hc
      rw [hxdef, xθ]
      rw [Nat.cast_mul, Nat.cast_mul] at hcR
      rw [div_mul_eq_mul_div, le_div_iff₀ hsR]; linarith
    have hΛn : Λ ^ n ≤ (2 : ℝ) ^ (-(p : ℝ)) := by
      rw [hΛ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hpp : (2 : ℝ) ^ p * (2 : ℝ) ^ (-(p : ℝ)) = 1 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; field_simp
    calc (2 : ℝ) ^ p * ‖Eit (s := s) (t := t) (α := α) n w l‖ ≤ 2 ^ p * (Λ ^ n * 1) :=
          mul_le_mul_of_nonneg_left hb hp.le
      _ ≤ 2 ^ p * (2 : ℝ) ^ (-(p : ℝ)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hΛn hp.le
      _ = 1 := hpp
  have : ((n : ℕ) : ℝ) * B = (n : ℝ) * (10 * m + 12) := by rw [hB]
  linarith

end IntMul.HvdH.JPf

open IntMul.HvdH in
theorem solution (p s t α : ℕ) (hs : 0 < s) (hx : s ≤ α ^ 2 * (t - s))
    (hpB : 2 * (10 * eWidth p α + 12) ≤ 2 ^ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I‖ ≤ 2 ^ p)
    (w : ℕ → ℂ) (hw : ∀ l, ‖w l‖ ≤ 1)
    (hJ : ∀ l, w l + Eexact s t α w l = (((U l).1 : ℂ) + ((U l).2 : ℂ) * Complex.I) / 2 ^ p / 2)
    (l : ℕ) :
    ‖(((Japprox p s t α U l).1 : ℂ) + ((Japprox p s t α U l).2 : ℂ) * Complex.I) - 2 ^ p * w l‖
      ≤ jIter p s t α * (10 * eWidth p α + 12) + 1 :=
  IntMul.HvdH.JPf.Japprox_bound p s t α hs hx hpB U hU w hw hJ l
