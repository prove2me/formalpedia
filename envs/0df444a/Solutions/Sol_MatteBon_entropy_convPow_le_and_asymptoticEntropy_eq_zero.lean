-- Prove2me | solution 1 for MatteBon.entropy_convPow_le_and_asymptoticEntropy_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T16:17:18.491507+00:00
-- url     : https://prove2.me/submissions/24739080-f94a-42b6-a1dd-340bfcaabefb

import Mathlib
import Definitions.Def_CantorSystems
import Definitions.Def_ErschlerZheng_Walks

section

/-!
# Matte Bon, GAFA 2014, Theorem 1.2

For a ℤ-subshift with dense non-periodic points and complexity `ρ(n) ≤ C n^α` (`α < 2`), every
finitely supported symmetric probability `μ` on `[[τ]]` has `H(μ^{*n}) ≤ C' n^{α/2} (log n)^{1+α/2}`
and zero asymptotic entropy.

Route (a variant of the paper's): instead of the Hebisch–Saloff-Coste Gaussian bound (MB Prop. 2.1)
and the reflection principle (MB Lemma 2.4), we use the Carne–Varopoulos bound
`p_n(a,b) ≤ 2 exp(-d(a,b)²/2n)`, proved here for a finite symmetric substochastic matrix via
its spectral decomposition and Chebyshev polynomials, together with a union bound over times
`j ≤ n` (the polynomial loss is absorbed by the choice of the cylinder depth).
-/

open CantorSystems ErschlerZheng

namespace MatteBon
namespace IETMB

open Finset Matrix Topology
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false


open Finset Matrix

/-! ## 1. A binomial (Hoeffding) tail -/

lemma sum_choose_exp (n : ℕ) (l : ℝ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) * Real.exp (l * (2 * (j : ℝ) - n)) =
      (2 * Real.cosh l) ^ n := by
  rw [show 2 * Real.cosh l = Real.exp l + Real.exp (-l) by rw [Real.cosh_eq]; ring, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, mul_comm]
  congr 2
  push_cast [Nat.cast_sub hj]
  ring

lemma binom_tail (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) * (if t ≤ |2 * (j : ℝ) - n| then 1 else 0)
      ≤ 2 * 2 ^ n * Real.exp (-(t ^ 2) / (2 * n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set l := t / n with hl_def
  have hl : 0 ≤ l := div_nonneg ht hn'.le
  calc ∑ j ∈ range (n + 1), (n.choose j : ℝ) * (if t ≤ |2 * (j : ℝ) - n| then 1 else 0)
      ≤ ∑ j ∈ range (n + 1), ((n.choose j : ℝ) * Real.exp (l * (2 * (j : ℝ) - n)) +
          (n.choose j : ℝ) * Real.exp ((-l) * (2 * (j : ℝ) - n))) * Real.exp (-(l * t)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← mul_add, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        split_ifs with h
        · set x := 2 * (j : ℝ) - n
          have h1 : Real.exp (l * |x|) ≤ Real.exp (l * x) + Real.exp (-l * x) := by
            rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
            · rw [hx]; linarith [Real.exp_pos (-l * x)]
            · rw [hx, show l * -x = -l * x by ring]; linarith [Real.exp_pos (l * x)]
          have h2 : Real.exp (l * t) ≤ Real.exp (l * |x|) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hl)
          rw [Real.exp_neg]
          rw [le_mul_inv_iff₀ (Real.exp_pos _), one_mul]
          linarith
        · positivity
    _ = ((2 * Real.cosh l) ^ n + (2 * Real.cosh (-l)) ^ n) * Real.exp (-(l * t)) := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, sum_choose_exp, sum_choose_exp]
    _ = 2 * (2 * Real.cosh l) ^ n * Real.exp (-(l * t)) := by rw [Real.cosh_neg]; ring
    _ ≤ 2 * (2 ^ n * Real.exp (n * (l ^ 2 / 2))) * Real.exp (-(l * t)) := by
        gcongr
        rw [mul_pow, Real.exp_nat_mul]
        gcongr
        exact Real.cosh_le_exp_half_sq l
    _ = 2 * 2 ^ n * Real.exp (-(t ^ 2) / (2 * n)) := by
        rw [mul_assoc (2 : ℝ) (2 ^ n), mul_assoc (2 : ℝ), mul_assoc ((2 : ℝ) ^ n),
          ← Real.exp_add]
        congr 3
        rw [hl_def]
        field_simp
        ring

/-! ## 2. The Carne–Varopoulos bound for a finite symmetric substochastic matrix -/

lemma two_cos_pow (n : ℕ) (θ : ℝ) :
    (2 * Real.cos θ) ^ n =
      ∑ j ∈ range (n + 1), (n.choose j : ℝ) * Real.cos ((2 * (j : ℝ) - n) * θ) := by
  have key : (((2 * Real.cos θ) ^ n : ℝ) : ℂ) =
      ∑ j ∈ range (n + 1), Complex.exp (((2 * (j : ℝ) - n) * θ : ℝ) * Complex.I) *
        ((n.choose j : ℝ) : ℂ) := by
    have : ((2 * Real.cos θ : ℝ) : ℂ) =
        Complex.exp (θ * Complex.I) + Complex.exp (-(θ * Complex.I)) := by
      push_cast
      rw [Complex.cos, show (-(↑θ * Complex.I)) = -↑θ * Complex.I by ring]
      ring
    rw [Complex.ofReal_pow, this, add_pow]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    push_cast [Nat.cast_sub hj]
    congr 2
    ring
  have := congrArg Complex.re key
  rw [Complex.ofReal_re, Complex.re_sum] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, mul_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An orthogonal matrix `U` together with a list of eigenvalues `lam`. -/
structure OrthDiag (ι : Type*) [Fintype ι] [DecidableEq ι] where
  U : Matrix ι ι ℝ
  lam : ι → ℝ
  hUU : U * Uᵀ = 1
  hUU' : Uᵀ * U = 1

namespace OrthDiag

variable (D : OrthDiag ι)

/-- `U diag(d) Uᵀ`. -/
def mat (d : ι → ℝ) : Matrix ι ι ℝ := D.U * diagonal d * D.Uᵀ

lemma mat_apply (d : ι → ℝ) (a b : ι) :
    D.mat d a b = ∑ i, D.U a i * d i * D.U b i := by
  simp only [mat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

lemma mat_mul (d e : ι → ℝ) : D.mat d * D.mat e = D.mat (d * e) := by
  unfold mat
  calc D.U * diagonal d * D.Uᵀ * (D.U * diagonal e * D.Uᵀ)
      = D.U * diagonal d * (D.Uᵀ * D.U) * diagonal e * D.Uᵀ := by
        simp only [Matrix.mul_assoc]
    _ = D.U * diagonal (d * e) * D.Uᵀ := by
        rw [D.hUU', Matrix.mul_one, Matrix.mul_assoc D.U, Matrix.diagonal_mul_diagonal]
        rfl

lemma mat_one : D.mat (fun _ => 1) = 1 := by
  unfold mat
  have : (diagonal fun _ : ι => (1 : ℝ)) = 1 := Matrix.diagonal_one
  rw [this, Matrix.mul_one, D.hUU]

lemma mat_pow (n : ℕ) : D.mat D.lam ^ n = D.mat (fun i => D.lam i ^ n) := by
  induction n with
  | zero => simp only [pow_zero]; exact D.mat_one.symm
  | succ n ih =>
    rw [pow_succ, ih, mat_mul]
    congr 1

lemma lam_eq (i : ι) : D.lam i = ∑ a, ∑ b, D.U a i * D.mat D.lam a b * D.U b i := by
  have h : D.Uᵀ * D.mat D.lam * D.U = diagonal D.lam := by
    unfold mat
    calc D.Uᵀ * (D.U * diagonal D.lam * D.Uᵀ) * D.U
        = (D.Uᵀ * D.U) * diagonal D.lam * (D.Uᵀ * D.U) := by simp only [Matrix.mul_assoc]
      _ = diagonal D.lam := by rw [D.hUU', Matrix.one_mul, Matrix.mul_one]
  have := congrFun (congrFun h i) i
  rw [Matrix.diagonal_apply_eq] at this
  rw [← this]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma sum_sq_col (i : ι) : ∑ a, D.U a i ^ 2 = 1 := by
  have := congrFun (congrFun D.hUU' i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
  rw [← this]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma sum_sq_row (a : ι) : ∑ i, D.U a i ^ 2 = 1 := by
  have := congrFun (congrFun D.hUU a) a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
  rw [← this]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma abs_mul_le_half (x y : ℝ) : |x| * |y| ≤ x ^ 2 / 2 + y ^ 2 / 2 := by
  have := two_mul_le_add_sq |x| |y|
  rw [sq_abs, sq_abs] at this
  linarith

lemma abs_lam_le (hs : (D.mat D.lam)ᵀ = D.mat D.lam) (hnn : ∀ a b, 0 ≤ D.mat D.lam a b)
    (hrow : ∀ a, ∑ b, D.mat D.lam a b ≤ 1) (i : ι) : |D.lam i| ≤ 1 := by
  set Q := D.mat D.lam with hQ
  rw [D.lam_eq i]
  have hcol : ∀ b, ∑ a, Q a b ≤ 1 := fun b => by
    calc ∑ a, Q a b = ∑ a, Q b a := Finset.sum_congr rfl fun a _ => by
            rw [← Matrix.transpose_apply Q a b, hs]
      _ ≤ 1 := hrow b
  calc |∑ a, ∑ b, D.U a i * Q a b * D.U b i|
      ≤ ∑ a, ∑ b, |D.U a i * Q a b * D.U b i| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, (D.U a i ^ 2 * Q a b / 2 + D.U b i ^ 2 * Q a b / 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hnn a b)]
        have h1 := abs_mul_le_half (D.U a i) (D.U b i)
        nlinarith [hnn a b]
    _ = (∑ a, D.U a i ^ 2 * ∑ b, Q a b) / 2 + (∑ b, D.U b i ^ 2 * ∑ a, Q a b) / 2 := by
        rw [Finset.sum_div, Finset.sum_div]
        simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
    _ ≤ (∑ a, D.U a i ^ 2 * 1) / 2 + (∑ b, D.U b i ^ 2 * 1) / 2 := by
        gcongr with a _ b _
        · exact hrow a
        · exact hcol b
    _ = 1 := by simp only [mul_one, D.sum_sq_col]; norm_num

/-- The "Chebyshev" matrices `T_m(Q) = U diag(cos(m θ_i)) Uᵀ`, `θ_i = arccos λ_i`. -/
noncomputable def cheb (m : ℤ) : Matrix ι ι ℝ :=
  D.mat (fun i => Real.cos (m * Real.arccos (D.lam i)))

lemma cheb_abs_le (m : ℤ) (a b : ι) : |D.cheb m a b| ≤ 1 := by
  unfold cheb
  rw [mat_apply]
  calc |∑ i, D.U a i * Real.cos (m * Real.arccos (D.lam i)) * D.U b i|
      ≤ ∑ i, |D.U a i * Real.cos (m * Real.arccos (D.lam i)) * D.U b i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (D.U a i ^ 2 / 2 + D.U b i ^ 2 / 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_mul]
        have h1 := abs_mul_le_half (D.U a i) (D.U b i)
        have h2 := Real.abs_cos_le_one (m * Real.arccos (D.lam i))
        calc |D.U a i| * |Real.cos (m * Real.arccos (D.lam i))| * |D.U b i|
            ≤ |D.U a i| * 1 * |D.U b i| := by gcongr
          _ ≤ _ := by rw [mul_one]; exact h1
    _ = 1 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, D.sum_sq_row,
          D.sum_sq_row]
        norm_num

lemma cheb_zero : D.cheb 0 = 1 := by
  unfold cheb
  simp only [Int.cast_zero, zero_mul, Real.cos_zero]
  exact D.mat_one

lemma cheb_one (hlam : ∀ i, |D.lam i| ≤ 1) : D.cheb 1 = D.mat D.lam := by
  unfold cheb
  congr 1
  funext i
  simp only [Int.cast_one, one_mul]
  exact Real.cos_arccos (abs_le.mp (hlam i)).1 (abs_le.mp (hlam i)).2

lemma cheb_rec (hlam : ∀ i, |D.lam i| ≤ 1) (m : ℤ) :
    D.cheb (m + 2) = (2 : ℝ) • (D.mat D.lam * D.cheb (m + 1)) - D.cheb m := by
  unfold cheb
  rw [mat_mul]
  ext a b
  rw [Matrix.sub_apply, Matrix.smul_apply, mat_apply, mat_apply, mat_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : Real.cos (Real.arccos (D.lam i)) = D.lam i :=
    Real.cos_arccos (abs_le.mp (hlam i)).1 (abs_le.mp (hlam i)).2
  simp only [Pi.mul_apply]
  set θ := Real.arccos (D.lam i)
  have key : Real.cos (((m + 2 : ℤ) : ℝ) * θ) =
      2 * Real.cos θ * Real.cos (((m + 1 : ℤ) : ℝ) * θ) - Real.cos ((m : ℝ) * θ) := by
    have h1 : ((m + 2 : ℤ) : ℝ) * θ = ((m + 1 : ℤ) : ℝ) * θ + θ := by push_cast; ring
    have h2 : (m : ℝ) * θ = ((m + 1 : ℤ) : ℝ) * θ - θ := by push_cast; ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]
    ring
  rw [key, hc]
  ring

lemma cheb_neg (m : ℤ) : D.cheb (-m) = D.cheb m := by
  unfold cheb
  congr 1
  funext i
  push_cast
  rw [neg_mul, Real.cos_neg]

lemma cheb_support (hlam : ∀ i, |D.lam i| ≤ 1) (φ : ι → ℤ) (K : ℕ)
    (hloc : ∀ a b, D.mat D.lam a b ≠ 0 → |φ a - φ b| ≤ K) :
    ∀ m : ℕ, ∀ a b, D.cheb m a b ≠ 0 → |φ a - φ b| ≤ K * m := by
  have key : ∀ m : ℕ, (∀ a b, D.cheb m a b ≠ 0 → |φ a - φ b| ≤ K * m) ∧
      (∀ a b, D.cheb (m + 1 : ℕ) a b ≠ 0 → |φ a - φ b| ≤ K * (m + 1 : ℕ)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun a b h => ?_, fun a b h => ?_⟩
      · simp only [Nat.cast_zero, D.cheb_zero, Matrix.one_apply] at h
        split_ifs at h with hab
        · subst hab; simp
        · exact absurd rfl h
      · simp only [zero_add, Nat.cast_one, D.cheb_one hlam] at h
        simpa using hloc a b h
    | succ m ih =>
      refine ⟨ih.2, fun a b h => ?_⟩
      have hr := D.cheb_rec hlam (m : ℤ)
      rw [show ((m + 1 + 1 : ℕ) : ℤ) = (m : ℤ) + 2 by push_cast; ring, hr] at h
      rw [Matrix.sub_apply, Matrix.smul_apply] at h
      by_cases h0 : D.cheb m a b = 0
      · rw [h0, sub_zero, smul_eq_mul] at h
        have h1 : (D.mat D.lam * D.cheb (m + 1)) a b ≠ 0 := by
          intro e; apply h; rw [e, mul_zero]
        rw [Matrix.mul_apply] at h1
        obtain ⟨c, _, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
        have hc1 := hloc a c (left_ne_zero_of_mul hc)
        have hc2 := ih.2 c b (by exact_mod_cast right_ne_zero_of_mul hc)
        calc |φ a - φ b| = |(φ a - φ c) + (φ c - φ b)| := by ring_nf
          _ ≤ |φ a - φ c| + |φ c - φ b| := abs_add_le _ _
          _ ≤ K + K * ((m + 1 : ℕ) : ℤ) := add_le_add hc1 hc2
          _ = K * ((m + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
      · have := ih.1 a b h0
        calc |φ a - φ b| ≤ K * m := this
          _ ≤ K * ((m + 1 + 1 : ℕ) : ℤ) := by
            push_cast
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact fun m => (key m).1

end OrthDiag

lemma exists_orthDiag (Q : Matrix ι ι ℝ) (hs : Qᵀ = Q) :
    ∃ D : OrthDiag ι, Q = D.mat D.lam := by
  have hH : Q.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hs]
  have h := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ)
  have hU := hH.eigenvectorUnitary.2
  have hst : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨⟨U, hH.eigenvalues, ?_, ?_⟩, ?_⟩
  · rw [← hst]; exact Matrix.mem_unitaryGroup_iff.mp hU
  · rw [← hst]; exact Matrix.mem_unitaryGroup_iff'.mp hU
  · refine h.trans ?_
    show U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U = U * diagonal hH.eigenvalues * Uᵀ
    rw [hst]
    rfl

/-- **Carne–Varopoulos** for a finite symmetric substochastic matrix whose nonzero entries
join points at `φ`-distance at most `K`. -/
theorem carne_varopoulos (Q : Matrix ι ι ℝ) (hs : Qᵀ = Q) (hnn : ∀ a b, 0 ≤ Q a b)
    (hrow : ∀ a, ∑ b, Q a b ≤ 1) (φ : ι → ℤ) (K : ℕ) (hK : 0 < K)
    (hloc : ∀ a b, Q a b ≠ 0 → |φ a - φ b| ≤ K) (n : ℕ) (hn : 1 ≤ n) (a b : ι) :
    (Q ^ n) a b ≤ 2 * Real.exp (-((((|φ a - φ b| : ℤ) : ℝ) / K) ^ 2) / (2 * n)) := by
  obtain ⟨D, rfl⟩ := exists_orthDiag Q hs
  have hlam := D.abs_lam_le hs hnn hrow
  have hsupp := D.cheb_support hlam φ K hloc
  set t : ℝ := (((|φ a - φ b| : ℤ) : ℝ) / K) with ht_def
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have ht : 0 ≤ t := div_nonneg (by exact_mod_cast abs_nonneg _) hKr.le
  have hexp : (D.mat D.lam ^ n) a b = (2 ^ n)⁻¹ * ∑ j ∈ range (n + 1),
      (n.choose j : ℝ) * D.cheb (2 * (j : ℤ) - n) a b := by
    rw [D.mat_pow, D.mat_apply]
    simp only [OrthDiag.cheb, D.mat_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : Real.cos (Real.arccos (D.lam i)) = D.lam i :=
      Real.cos_arccos (abs_le.mp (hlam i)).1 (abs_le.mp (hlam i)).2
    have hp : D.lam i ^ n = (2 ^ n)⁻¹ * (2 * Real.cos (Real.arccos (D.lam i))) ^ n := by
      rw [hc, mul_pow]; field_simp
    rw [hp, two_cos_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hexp]
  calc (2 ^ n : ℝ)⁻¹ * ∑ j ∈ range (n + 1), (n.choose j : ℝ) * D.cheb (2 * (j : ℤ) - n) a b
      ≤ (2 ^ n : ℝ)⁻¹ * ∑ j ∈ range (n + 1),
          (n.choose j : ℝ) * (if t ≤ |2 * (j : ℝ) - n| then 1 else 0) := by
        gcongr with j _
        split_ifs with hj
        · exact (abs_le.mp (D.cheb_abs_le _ a b)).2
        · by_contra hne
          push Not at hne
          have hne' : D.cheb ((2 * (j : ℤ) - n).natAbs : ℕ) a b ≠ 0 := by
            have : D.cheb ((2 * (j : ℤ) - n).natAbs : ℕ) = D.cheb (2 * (j : ℤ) - n) := by
              rcases Int.natAbs_eq (2 * (j : ℤ) - n) with h | h
              · rw [← h]
              · rw [show (((2 * (j : ℤ) - n).natAbs : ℕ) : ℤ) = -(2 * (j : ℤ) - n) by omega,
                  D.cheb_neg]
            rw [this]; exact hne.ne'
          have h1 := hsupp _ a b hne'
          apply hj
          rw [ht_def, div_le_iff₀ hKr]
          have h2 : ((|φ a - φ b| : ℤ) : ℝ) ≤ ((K * ((2 * (j : ℤ) - n).natAbs : ℕ) : ℤ) : ℝ) := by
            exact_mod_cast h1
          push_cast at h2
          rw [Int.cast_abs]
          push_cast
          linarith
    _ ≤ (2 ^ n : ℝ)⁻¹ * (2 * 2 ^ n * Real.exp (-(t ^ 2) / (2 * n))) := by
        gcongr
        exact binom_tail n hn t ht
    _ = 2 * Real.exp (-(t ^ 2) / (2 * n)) := by field_simp


open Finset
open scoped ENNReal Pointwise

/-! ## 3. Convolutions and entropy -/

section Walks

variable {G : Type*} [Group G]

lemma le_one_of_isProb {μ : G → ℝ} (hμ : IsProbability μ) (g : G) : μ g ≤ 1 :=
  le_hasSum hμ.2 g (fun j _ => hμ.1 j)

lemma tsum_ofReal_of_isProb {μ : G → ℝ} (hμ : IsProbability μ) :
    ∑' g, ENNReal.ofReal (μ g) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

lemma isProb_of_tsum_ofReal {f : G → ℝ} (h0 : ∀ g, 0 ≤ f g)
    (h : ∑' g, ENNReal.ofReal (f g) = 1) : IsProbability f := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal (f := fun g => ENNReal.ofReal (f g))
      (by rw [h]; exact ENNReal.one_ne_top)
    simpa [ENNReal.toReal_ofReal (h0 _)] using this
  refine ⟨h0, hs.hasSum_iff.mpr ?_⟩
  have := ENNReal.ofReal_tsum_of_nonneg h0 hs
  rw [h] at this
  exact ENNReal.ofReal_eq_one.mp this

lemma conv_summand_summable {μ ν : G → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : G) :
    Summable fun h => μ h * ν (h⁻¹ * g) := by
  refine Summable.of_nonneg_of_le (fun h => mul_nonneg (hμ.1 h) (hν.1 _)) (fun h => ?_)
    hμ.2.summable
  calc μ h * ν (h⁻¹ * g) ≤ μ h * 1 :=
        mul_le_mul_of_nonneg_left (le_one_of_isProb hν _) (hμ.1 h)
    _ = μ h := mul_one _

lemma conv_nonneg {μ ν : G → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : G) :
    0 ≤ conv μ ν g :=
  tsum_nonneg fun h => mul_nonneg (hμ.1 h) (hν.1 _)

lemma ofReal_conv {μ ν : G → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : G) :
    ENNReal.ofReal (conv μ ν g) =
      ∑' h, ENNReal.ofReal (μ h) * ENNReal.ofReal (ν (h⁻¹ * g)) := by
  unfold conv
  rw [ENNReal.ofReal_tsum_of_nonneg (fun h => mul_nonneg (hμ.1 h) (hν.1 _))
    (conv_summand_summable hμ hν g)]
  congr 1
  ext h
  rw [ENNReal.ofReal_mul (hμ.1 h)]

lemma tsum_mulLeft_eq (F : G → ℝ≥0∞) (k : G) : ∑' m, F (k * m) = ∑' h, F h :=
  (Equiv.mulLeft k).tsum_eq F

lemma isProb_conv {μ ν : G → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) :
    IsProbability (conv μ ν) := by
  refine isProb_of_tsum_ofReal (conv_nonneg hμ hν) ?_
  simp_rw [ofReal_conv hμ hν]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  have : ∀ h : G, ∑' g, ENNReal.ofReal (ν (h⁻¹ * g)) = 1 := fun h => by
    rw [tsum_mulLeft_eq (fun x => ENNReal.ofReal (ν x)) h⁻¹]
    exact tsum_ofReal_of_isProb hν
  simp_rw [this, mul_one]
  exact tsum_ofReal_of_isProb hμ

lemma isProb_convPow {μ : G → ℝ} (hμ : IsProbability μ) (n : ℕ) :
    IsProbability (convPow μ n) := by
  induction n with
  | zero =>
    classical
    refine ⟨fun g => ?_, ?_⟩
    · simp only [convPow]; split_ifs <;> norm_num
    · have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
        ext g; simp only [convPow]
      rw [this]
      convert hasSum_ite_eq (1 : G) (1 : ℝ) using 1
  | succ n ih => exact isProb_conv ih hμ

/-- Expectations under a convolution, for a `[0,1]`-valued function. -/
lemma tsum_conv_mul {ν μ : G → ℝ} (hν : IsProbability ν) (hμ : IsProbability μ) (f : G → ℝ)
    (hf0 : ∀ g, 0 ≤ f g) (hf1 : ∀ g, f g ≤ 1) :
    ∑' g, conv ν μ g * f g = ∑' s, μ s * ∑' h, ν h * f (h * s) := by
  have hc := isProb_conv hν hμ
  have hsumL : Summable fun g => conv ν μ g * f g :=
    Summable.of_nonneg_of_le (fun g => mul_nonneg (hc.1 g) (hf0 g))
      (fun g => mul_le_of_le_one_right (hc.1 g) (hf1 g)) hc.2.summable
  have hin : ∀ s, Summable fun h => ν h * f (h * s) := fun s =>
    Summable.of_nonneg_of_le (fun h => mul_nonneg (hν.1 h) (hf0 _))
      (fun h => mul_le_of_le_one_right (hν.1 h) (hf1 _)) hν.2.summable
  have hin1 : ∀ s, ∑' h, ν h * f (h * s) ≤ 1 := fun s => by
    calc ∑' h, ν h * f (h * s) ≤ ∑' h, ν h :=
          Summable.tsum_le_tsum (fun h => mul_le_of_le_one_right (hν.1 h) (hf1 _)) (hin s)
            hν.2.summable
      _ = 1 := hν.2.tsum_eq
  have hin0 : ∀ s, 0 ≤ ∑' h, ν h * f (h * s) := fun s =>
    tsum_nonneg fun h => mul_nonneg (hν.1 h) (hf0 _)
  have hsumR : Summable fun s => μ s * ∑' h, ν h * f (h * s) :=
    Summable.of_nonneg_of_le (fun s => mul_nonneg (hμ.1 s) (hin0 s))
      (fun s => mul_le_of_le_one_right (hμ.1 s) (hin1 s)) hμ.2.summable
  have hL0 : 0 ≤ ∑' g, conv ν μ g * f g := tsum_nonneg fun g => mul_nonneg (hc.1 g) (hf0 g)
  have hR0 : 0 ≤ ∑' s, μ s * ∑' h, ν h * f (h * s) :=
    tsum_nonneg fun s => mul_nonneg (hμ.1 s) (hin0 s)
  rw [← ENNReal.ofReal_eq_ofReal_iff hL0 hR0]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun g => mul_nonneg (hc.1 g) (hf0 g)) hsumL,
    ENNReal.ofReal_tsum_of_nonneg (fun s => mul_nonneg (hμ.1 s) (hin0 s)) hsumR]
  simp_rw [ENNReal.ofReal_mul (hc.1 _), ofReal_conv hν hμ, ENNReal.ofReal_mul (hμ.1 _),
    ENNReal.ofReal_tsum_of_nonneg (fun h => mul_nonneg (hν.1 h) (hf0 _)) (hin _),
    ENNReal.ofReal_mul (hν.1 _), ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  have : ∀ h : G, ∑' g, ENNReal.ofReal (ν h) * ENNReal.ofReal (μ (h⁻¹ * g)) *
      ENNReal.ofReal (f g) = ∑' s, ENNReal.ofReal (μ s) * (ENNReal.ofReal (ν h) *
        ENNReal.ofReal (f (h * s))) := fun h => by
    rw [← tsum_mulLeft_eq _ h]
    congr 1
    ext s
    rw [inv_mul_cancel_left]
    ring
  simp_rw [this]
  rw [ENNReal.tsum_comm]

lemma support_conv_subset (ν μ : G → ℝ) :
    Function.support (conv ν μ) ⊆ Function.support ν * Function.support μ := by
  intro g hg
  rw [Function.mem_support] at hg
  unfold conv at hg
  obtain ⟨h, hh⟩ : ∃ h, ν h * μ (h⁻¹ * g) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hg
    simp [hcon]
  exact ⟨h, left_ne_zero_of_mul hh, h⁻¹ * g, right_ne_zero_of_mul hh, by group⟩

lemma convPow_support (μ : G → ℝ) (F : Finset G) (hF : Function.support μ ⊆ F) (n : ℕ) :
    ∃ T : Finset G, T.card ≤ F.card ^ n ∧ Function.support (convPow μ n) ⊆ T := by
  classical
  induction n with
  | zero =>
    refine ⟨{1}, by simp, fun g hg => ?_⟩
    simp only [convPow, Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not] at hg
    simp [hg]
  | succ n ih =>
    obtain ⟨T, hT, hTs⟩ := ih
    refine ⟨T * F, ?_, ?_⟩
    · calc (T * F).card ≤ T.card * F.card := Finset.card_mul_le
        _ ≤ F.card ^ n * F.card := Nat.mul_le_mul_right _ hT
        _ = F.card ^ (n + 1) := (pow_succ _ _).symm
    · show Function.support (conv (convPow μ n) μ) ⊆ _
      rw [Finset.coe_mul]
      exact (support_conv_subset _ _).trans (Set.mul_subset_mul hTs hF)

/-- Jensen for `-x log x` on a finite set. -/
lemma sum_negMulLog_le {α : Type*} (B : Finset α) (x : α → ℝ) (hx : ∀ g ∈ B, 0 ≤ x g) :
    ∑ g ∈ B, Real.negMulLog (x g) ≤
      (∑ g ∈ B, x g) * Real.log B.card + Real.negMulLog (∑ g ∈ B, x g) := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  set p := ∑ g ∈ B, x g with hp
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := B) (w := fun _ => (B.card : ℝ)⁻¹)
    (p := x) (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun g hg => Set.mem_Ici.mpr (hx g hg))
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← hp] at hJ
  have h1 : ∑ g ∈ B, Real.negMulLog (x g) ≤ B.card * Real.negMulLog ((B.card : ℝ)⁻¹ * p) := by
    have := mul_le_mul_of_nonneg_left hJ hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  refine h1.trans (le_of_eq ?_)
  rcases eq_or_ne p 0 with h0 | h0
  · rw [h0]; simp
  · unfold Real.negMulLog
    rw [Real.log_mul (inv_ne_zero hc.ne') h0, Real.log_inv]
    field_simp
    ring

lemma sum_eq_one_of_support {ν : G → ℝ} (hν : IsProbability ν) (T : Finset G)
    (hT : Function.support ν ⊆ T) : ∑ g ∈ T, ν g = 1 := by
  have h : HasSum ν (∑ g ∈ T, ν g) := hasSum_sum_of_ne_finset_zero (fun b hb => by
    by_contra h; exact hb (hT h))
  exact h.unique hν.2

lemma entropy_eq_sum {ν : G → ℝ} (T : Finset G) (hT : Function.support ν ⊆ T) :
    entropy ν = ∑ g ∈ T, Real.negMulLog (ν g) := by
  unfold entropy
  refine tsum_eq_sum fun b hb => ?_
  have : ν b = 0 := by by_contra h; exact hb (hT h)
  simp [this]

lemma entropy_nonneg {ν : G → ℝ} (hν : IsProbability ν) : 0 ≤ entropy ν :=
  tsum_nonneg fun g => Real.negMulLog_nonneg (hν.1 g) (le_one_of_isProb hν g)

/-- The entropy bound used in Fact A.4: splitting the support into a good part and a bad part. -/
lemma entropy_le_split {ν : G → ℝ} (hν : IsProbability ν) (T : Finset G)
    (hT : Function.support ν ⊆ T) (P : G → Prop) [DecidablePred P] :
    entropy ν ≤ Real.log (T.filter P).card +
      (∑ g ∈ T, ν g * (if P g then 0 else 1)) * Real.log T.card + Real.log 2 := by
  rw [entropy_eq_sum T hT, ← Finset.sum_filter_add_sum_filter_not T P]
  set q := ∑ g ∈ T.filter P, ν g with hq
  set r := ∑ g ∈ T.filter (fun g => ¬ P g), ν g with hr
  have hr' : ∑ g ∈ T, ν g * (if P g then 0 else 1) = r := by
    rw [hr, Finset.sum_filter]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp
  rw [hr']
  have hqr : q + r = 1 := by
    rw [hq, hr, Finset.sum_filter_add_sum_filter_not]; exact sum_eq_one_of_support hν T hT
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun g _ => hν.1 g
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun g _ => hν.1 g
  have h1 := sum_negMulLog_le (T.filter P) ν (fun g _ => hν.1 g)
  have h2 := sum_negMulLog_le (T.filter fun g => ¬ P g) ν (fun g _ => hν.1 g)
  rw [← hq] at h1
  rw [← hr] at h2
  have hlogA : q * Real.log (T.filter P).card ≤ Real.log (T.filter P).card := by
    have := Real.log_natCast_nonneg (T.filter P).card
    nlinarith
  have hlogB : r * Real.log (T.filter fun g => ¬ P g).card ≤ r * Real.log T.card := by
    refine mul_le_mul_of_nonneg_left ?_ hr0
    rcases Nat.eq_zero_or_pos (T.filter fun g => ¬ P g).card with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Finset.card_filter_le _ _)
  have hbin : Real.negMulLog q + Real.negMulLog r ≤ Real.log 2 := by
    have := Real.binEntropy_le_log_two (p := q)
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      show 1 - q = r by linarith] at this
    exact this
  linarith

end Walks


open Topology

set_option linter.unusedSectionVars false

/-! ## 4. Locality of elements of `[[τ]]` and the orbit cocycle -/

section Topology

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] (S : Subshift ℤ A)

/-- `y` and `z` agree on the window `[-l, l]`. -/
def Agree (l : ℕ) (y z : ℤ → A) : Prop := ∀ i : ℤ, |i| ≤ l → y i = z i

lemma Agree.trans {l : ℕ} {x y z : ℤ → A} (h1 : Agree l x y) (h2 : Agree l y z) : Agree l x z :=
  fun i hi => (h1 i hi).trans (h2 i hi)

lemma Agree.mono {l l' : ℕ} {y z : ℤ → A} (h : Agree l' y z) (hl : l ≤ l') : Agree l y z :=
  fun i hi => h i (hi.trans (by exact_mod_cast hl))

lemma isOpen_agree (l : ℕ) (y : S) : IsOpen {z : S | Agree l (z : ℤ → A) y} := by
  have : {z : S | Agree l (z : ℤ → A) y} =
      ⋂ i ∈ Finset.Icc (-(l : ℤ)) l, (fun z : S => (z : ℤ → A) i) ⁻¹' {(y : ℤ → A) i} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Icc, Set.mem_preimage,
      Set.mem_singleton_iff, Agree, abs_le]
  rw [this]
  refine isOpen_biInter_finset fun i _ => ?_
  exact (isOpen_discrete _).preimage ((continuous_apply i).comp continuous_subtype_val)

/-- `g` acts, on each cylinder of depth `l`, as a shift by at most `l`. -/
def LocalAt (l : ℕ) (g : S ≃ₜ S) : Prop :=
  ∀ y : S, ∃ γ : ℤ, |γ| ≤ l ∧ ∀ z : S, Agree l (z : ℤ → A) y → g z = γ +ᵥ z

variable {S}

lemma LocalAt.mono {l l' : ℕ} {g : S ≃ₜ S} (h : LocalAt S l g) (hl : l ≤ l') :
    LocalAt S l' g := by
  intro y
  obtain ⟨γ, hγ, h⟩ := h y
  exact ⟨γ, hγ.trans (by exact_mod_cast hl), fun z hz => h z (hz.mono hl)⟩

lemma exists_localAt [Finite A] (g : S ≃ₜ S) (hg : g ∈ topologicalFullGroup ℤ S) :
    ∃ l, LocalAt S l g := by
  have : CompactSpace (ℤ → A) := Pi.compactSpace
  have : CompactSpace S := isCompact_iff_compactSpace.mp S.isSubshift.1.isCompact
  let O : ℕ → Set S := fun l => {y | ∃ γ : ℤ, |γ| ≤ l ∧ ∀ z : S, Agree l (z : ℤ → A) y →
    g z = γ +ᵥ z}
  have hO : ∀ l, IsOpen (O l) := by
    intro l
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    refine ⟨{z : S | Agree l (z : ℤ → A) y}, fun y' hy' => ?_, isOpen_agree S l y,
      fun i _ => rfl⟩
    obtain ⟨γ, hγ, h⟩ := hy
    exact ⟨γ, hγ, fun z hz => h z (hz.trans hy')⟩
  have hmono : ∀ l l', l ≤ l' → O l ⊆ O l' := by
    intro l l' hl y ⟨γ, hγ, h⟩
    exact ⟨γ, hγ.trans (by exact_mod_cast hl), fun z hz => h z (hz.mono hl)⟩
  have hcov : (Set.univ : Set S) ⊆ ⋃ l, O l := by
    intro y _
    obtain ⟨U, hU, γ, hγ⟩ := hg y
    rw [mem_nhds_subtype] at hU
    obtain ⟨u, hu, hus⟩ := hU
    rw [nhds_pi, Filter.mem_pi] at hu
    obtain ⟨I, hI, t, ht, hIt⟩ := hu
    obtain ⟨l₁, hl₁⟩ : ∃ l₁ : ℕ, ∀ i ∈ I, |i| ≤ l₁ := by
      refine ⟨hI.toFinset.sup Int.natAbs, fun i hi => ?_⟩
      rw [Int.abs_eq_natAbs]
      exact_mod_cast Finset.le_sup (f := Int.natAbs) (hI.mem_toFinset.mpr hi)
    refine Set.mem_iUnion.mpr ⟨max l₁ γ.natAbs, γ, ?_, fun z hz => hγ z (hus ?_)⟩
    · rw [Int.abs_eq_natAbs]; exact_mod_cast le_max_right _ _
    · refine hIt fun i hi => ?_
      rw [hz i ((hl₁ i hi).trans (by exact_mod_cast le_max_left _ _))]
      exact mem_of_mem_nhds (ht i)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  refine ⟨T.sup id, fun y => ?_⟩
  have hy := hT (Set.mem_univ y)
  simp only [Set.mem_iUnion] at hy
  obtain ⟨l, hl, hyl⟩ := hy
  exact hmono l _ (Finset.le_sup (f := id) hl) hyl

/-- A point is non-periodic. -/
def IsNP (x : S) : Prop := ∀ k : ℤ, k +ᵥ x = x → k = 0

lemma IsNP.vadd_inj {x : S} (hx : IsNP x) {a b : ℤ} (h : a +ᵥ x = b +ᵥ x) : a = b := by
  have : (-b + a) +ᵥ x = x := by rw [add_vadd, h, neg_vadd_vadd]
  have := hx _ this
  omega

lemma exists_pos (g : topologicalFullGroup ℤ S) (x : S) (a : ℤ) :
    ∃ p : ℤ, (g : S ≃ₜ S) (a +ᵥ x) = p +ᵥ x := by
  obtain ⟨U, hU, γ, hγ⟩ := g.2 (a +ᵥ x)
  exact ⟨γ + a, by rw [hγ _ (mem_of_mem_nhds hU), add_vadd]⟩

/-- The orbit cocycle at `x`, as a map on positions: `g (a +ᵥ x) = pos x g a +ᵥ x`. -/
noncomputable def pos (x : S) (g : topologicalFullGroup ℤ S) (a : ℤ) : ℤ :=
  Classical.choose (exists_pos g x a)

lemma pos_spec (x : S) (g : topologicalFullGroup ℤ S) (a : ℤ) :
    (g : S ≃ₜ S) (a +ᵥ x) = pos x g a +ᵥ x :=
  Classical.choose_spec (exists_pos g x a)

lemma pos_mul {x : S} (hx : IsNP x) (g h : topologicalFullGroup ℤ S) (a : ℤ) :
    pos x (g * h) a = pos x g (pos x h a) := by
  apply hx.vadd_inj
  rw [← pos_spec, ← pos_spec, Subgroup.coe_mul, Homeomorph.mul_apply, pos_spec]

lemma pos_one {x : S} (hx : IsNP x) (a : ℤ) : pos x 1 a = a := by
  apply hx.vadd_inj
  rw [← pos_spec]
  rfl

lemma pos_inv_eq_iff {x : S} (hx : IsNP x) (g : topologicalFullGroup ℤ S) (a b : ℤ) :
    pos x g⁻¹ b = a ↔ pos x g a = b := by
  constructor
  · rintro rfl
    rw [← pos_mul hx, mul_inv_cancel, pos_one hx]
  · rintro rfl
    rw [← pos_mul hx, inv_mul_cancel, pos_one hx]

lemma pos_sub_le {x : S} (hx : IsNP x) {l : ℕ} (g : topologicalFullGroup ℤ S)
    (hg : LocalAt S l (g : S ≃ₜ S)) (a : ℤ) : |pos x g a - a| ≤ l := by
  obtain ⟨γ, hγ, h⟩ := hg (a +ᵥ x)
  have h1 := h (a +ᵥ x) (fun _ _ => rfl)
  rw [pos_spec, ← add_vadd] at h1
  rw [hx.vadd_inj h1]
  simpa using hγ

end Topology

/-! ## 5. The walk seen from a non-periodic point (MB Lemma 3.2, Remark 3.3, Corollary 3.5) -/

section Walk

open scoped Classical

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {S : Subshift ℤ A}
  (μ : topologicalFullGroup ℤ S → ℝ) (F : Finset (topologicalFullGroup ℤ S)) (x₀ : S)

/-- The Markov operator of the walk on positions along the orbit of `x₀`. -/
noncomputable def Pop (f : ℤ → ℝ) : ℤ → ℝ := fun a => ∑ s ∈ F, μ s * f (pos x₀ s a)

/-- Indicator of leaving `[-M, M]`. -/
noncomputable def Iout (M : ℤ) : ℤ → ℝ := fun b => if M < |b| then 1 else 0

/-- `g` acts on the cylinder of depth `L` around `a +ᵥ x₀` as the shift that it applies to
`a +ᵥ x₀`, and that shift is at most `B`. -/
def GoodB (L : ℕ) (B : ℤ) (g : topologicalFullGroup ℤ S) (a : ℤ) : Prop :=
  (∀ y : S, Agree L (y : ℤ → A) x₀ → (g : S ≃ₜ S) (a +ᵥ y) = pos x₀ g a +ᵥ y) ∧
    |pos x₀ g a| ≤ B

/-- The probability that `μ^{*n}` is not good. -/
noncomputable def badE (L : ℕ) (B : ℤ) (n : ℕ) (a : ℤ) : ℝ :=
  ∑' g, convPow μ n g * (if GoodB x₀ L B g a then 0 else 1)

variable {μ F x₀}

lemma Pop_mono (hμ : IsProbability μ) {f f' : ℤ → ℝ} (h : ∀ a, f a ≤ f' a) (a : ℤ) :
    Pop μ F x₀ f a ≤ Pop μ F x₀ f' a :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h _) (hμ.1 s)

lemma Pop_nonneg (hμ : IsProbability μ) {f : ℤ → ℝ} (h : ∀ a, 0 ≤ f a) (a : ℤ) :
    0 ≤ Pop μ F x₀ f a :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hμ.1 s) (h _)

lemma Pop_sum (ι' : Finset ℕ) (f : ℕ → ℤ → ℝ) (a : ℤ) :
    Pop μ F x₀ (fun b => ∑ j ∈ ι', f j b) a = ∑ j ∈ ι', Pop μ F x₀ (f j) a := by
  unfold Pop
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- MB Lemma 3.2, one step: the cylinder of depth `L` is carried along by a generator as long as
the current position stays in `[-(L-l), L-l]`. -/
lemma goodB_mul (hx : IsNP x₀) {l L : ℕ} {B : ℤ} {s h : topologicalFullGroup ℤ S}
    (hs : LocalAt S l (s : S ≃ₜ S)) {a : ℤ} (ha : |a| + l ≤ L)
    (hh : GoodB x₀ L B h (pos x₀ s a)) : GoodB x₀ L B (h * s) a := by
  obtain ⟨γ, -, hγ⟩ := hs (a +ᵥ x₀)
  have hagree : ∀ y : S, Agree L (y : ℤ → A) x₀ →
      Agree l ((a +ᵥ y : S) : ℤ → A) (a +ᵥ x₀ : S) := by
    intro y hy i hi
    rw [Subshift.coe_vadd, Subshift.coe_vadd, shift_apply, shift_apply]
    refine hy _ ?_
    calc |i + a| ≤ |i| + |a| := abs_add_le _ _
      _ ≤ l + |a| := by linarith
      _ ≤ L := by linarith
  have hpos : pos x₀ s a = γ + a := by
    apply hx.vadd_inj
    rw [← pos_spec, hγ _ (fun _ _ => rfl), add_vadd]
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [Subgroup.coe_mul, Homeomorph.mul_apply, hγ _ (hagree y hy), ← add_vadd, ← hpos,
      hh.1 y hy, pos_mul hx]
  · rw [pos_mul hx]; exact hh.2

lemma badE_nonneg (hμ : IsProbability μ) (L : ℕ) (B : ℤ) (n : ℕ) (a : ℤ) :
    0 ≤ badE μ x₀ L B n a :=
  tsum_nonneg fun g => mul_nonneg ((isProb_convPow hμ n).1 g) (by split_ifs <;> norm_num)

lemma badE_le_one (hμ : IsProbability μ) (L : ℕ) (B : ℤ) (n : ℕ) (a : ℤ) :
    badE μ x₀ L B n a ≤ 1 := by
  have hp := isProb_convPow hμ n
  calc badE μ x₀ L B n a ≤ ∑' g, convPow μ n g :=
        Summable.tsum_le_tsum (fun g => mul_le_of_le_one_right (hp.1 g)
          (by split_ifs <;> norm_num))
          (Summable.of_nonneg_of_le (fun g => mul_nonneg (hp.1 g) (by split_ifs <;> norm_num))
            (fun g => mul_le_of_le_one_right (hp.1 g) (by split_ifs <;> norm_num)) hp.2.summable)
          hp.2.summable
    _ = 1 := hp.2.tsum_eq

lemma badE_succ_le (hμ : IsProbability μ) (hF : ∀ s, μ s ≠ 0 → s ∈ F) (hx : IsNP x₀) {l L : ℕ}
    (hloc : ∀ s ∈ F, LocalAt S l (s : S ≃ₜ S)) (B : ℤ) (n : ℕ) (a : ℤ) :
    badE μ x₀ L B (n + 1) a ≤ Iout ((L : ℤ) - l) a + Pop μ F x₀ (badE μ x₀ L B n) a := by
  by_cases ha : (L : ℤ) - l < |a|
  · have : Iout ((L : ℤ) - l) a = 1 := by unfold Iout; rw [if_pos ha]
    rw [this]
    have := Pop_nonneg (F := F) (x₀ := x₀) hμ (badE_nonneg (x₀ := x₀) hμ L B n) a
    linarith [badE_le_one (x₀ := x₀) hμ L B (n + 1) a]
  · have h0 : Iout ((L : ℤ) - l) a = 0 := by unfold Iout; rw [if_neg ha]
    rw [h0, zero_add]
    have ha' : |a| + l ≤ L := by push Not at ha; linarith
    have hp := isProb_convPow hμ n
    unfold badE
    show ∑' g, conv (convPow μ n) μ g * _ ≤ _
    rw [tsum_conv_mul hp hμ _ (fun g => by split_ifs <;> norm_num)
      (fun g => by split_ifs <;> norm_num)]
    rw [tsum_eq_sum (s := F) (fun s hs => by
      have : μ s = 0 := by by_contra h; exact hs (hF s h)
      rw [this, zero_mul])]
    refine Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left ?_ (hμ.1 s)
    have hsum : ∀ (P : topologicalFullGroup ℤ S → Prop) [DecidablePred P],
        Summable fun h => convPow μ n h * (if P h then (0 : ℝ) else 1) := fun P _ =>
      Summable.of_nonneg_of_le (fun g => mul_nonneg (hp.1 g) (by split_ifs <;> norm_num))
        (fun g => mul_le_of_le_one_right (hp.1 g) (by split_ifs <;> norm_num)) hp.2.summable
    refine Summable.tsum_le_tsum (fun h => mul_le_mul_of_nonneg_left ?_ (hp.1 h))
      (hsum (fun h => GoodB x₀ L B (h * s) a)) (hsum (fun h => GoodB x₀ L B h (pos x₀ s a)))
    by_cases hg : GoodB x₀ L B h (pos x₀ s a)
    · rw [if_pos (goodB_mul hx (hloc s hs) ha' hg), if_pos hg]
    · rw [if_neg hg]; split_ifs <;> norm_num

lemma badE_zero_le (hμ : IsProbability μ) (hx : IsNP x₀) (L l : ℕ) (B : ℤ)
    (hB : (L : ℤ) - l ≤ B) (a : ℤ) :
    badE μ x₀ L B 0 a ≤ Iout ((L : ℤ) - l) a := by
  by_cases ha : (L : ℤ) - l < |a|
  · have : Iout ((L : ℤ) - l) a = 1 := by unfold Iout; rw [if_pos ha]
    rw [this]; exact badE_le_one hμ L B 0 a
  · have h0 : Iout ((L : ℤ) - l) a = 0 := by unfold Iout; rw [if_neg ha]
    rw [h0]
    have hg : GoodB x₀ L B 1 a := by
      refine ⟨fun y _ => ?_, ?_⟩
      · rw [pos_one hx]; rfl
      · rw [pos_one hx]; push Not at ha; linarith
    unfold badE
    rw [tsum_eq_single 1]
    · rw [if_pos hg, mul_zero]
    · intro g hg1
      simp [convPow, hg1]

lemma badE_le_sum (hμ : IsProbability μ) (hF : ∀ s, μ s ≠ 0 → s ∈ F) (hx : IsNP x₀)
    {l L : ℕ} (hloc : ∀ s ∈ F, LocalAt S l (s : S ≃ₜ S)) (B : ℤ) (hB : (L : ℤ) - l ≤ B)
    (n : ℕ) : ∀ a, badE μ x₀ L B n a ≤
      ∑ j ∈ range (n + 1), (Pop μ F x₀)^[j] (Iout ((L : ℤ) - l)) a := by
  induction n with
  | zero => intro a; simpa using badE_zero_le hμ hx L l B hB a
  | succ n ih =>
    intro a
    refine (badE_succ_le hμ hF hx hloc B n a).trans ?_
    rw [Finset.sum_range_succ' _ (n + 1)]
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
    rw [add_comm]
    refine add_le_add_left ?_ _
    rw [← Pop_sum]
    exact Pop_mono hμ ih a

/-- The positions `[-R, R]`. -/
abbrev Box (R : ℤ) := ↥(Finset.Icc (-R) R)

variable (μ F x₀) in
/-- The transition matrix of the walk on positions, restricted to `[-R, R]`. -/
noncomputable def Qm (R : ℤ) : Matrix (Box R) (Box R) ℝ :=
  fun a b => ∑ s ∈ F, μ s * if pos x₀ s a.1 = b.1 then 1 else 0

lemma mem_box_iff {R b : ℤ} : b ∈ Finset.Icc (-R) R ↔ |b| ≤ R := by
  rw [Finset.mem_Icc, abs_le]

lemma sum_Qm_mul {R : ℤ} (a : Box R) (hin : ∀ s ∈ F, |pos x₀ s a.1| ≤ R) (H : ℤ → ℝ) :
    ∑ c, Qm μ F x₀ R a c * H c.1 = ∑ s ∈ F, μ s * H (pos x₀ s a.1) := by
  unfold Qm
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hmem : pos x₀ s a.1 ∈ Finset.Icc (-R) R := mem_box_iff.mpr (hin s hs)
  rw [Finset.sum_eq_single ⟨pos x₀ s a.1, hmem⟩]
  · simp
  · intro c _ hc
    have : pos x₀ s a.1 ≠ c.1 := fun h => hc (Subtype.ext h.symm)
    simp [this]
  · simp

lemma Qm_ne_zero {R : ℤ} (hx : IsNP x₀) {l : ℕ} (hloc : ∀ s ∈ F, LocalAt S l (s : S ≃ₜ S))
    (a c : Box R) (h : Qm μ F x₀ R a c ≠ 0) : |a.1 - c.1| ≤ l := by
  obtain ⟨s, hs, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h2 : pos x₀ s a.1 = c.1 := by
    by_contra h3; apply h1; simp [h3]
  have := pos_sub_le hx s (hloc s hs) a.1
  rw [h2] at this
  rw [abs_sub_comm]; exact this

lemma iterate_Pop_eq (hx : IsNP x₀) {l : ℕ} (hloc : ∀ s ∈ F, LocalAt S l (s : S ≃ₜ S))
    (R : ℤ) (j : ℕ) : ∀ (f : ℤ → ℝ) (a : Box R), |a.1| + l * j ≤ R →
      (Pop μ F x₀)^[j] f a.1 = ∑ b, (Qm μ F x₀ R ^ j) a b * f b.1 := by
  induction j with
  | zero =>
    intro f a _
    simp only [Function.iterate_zero, id_eq, pow_zero, Matrix.one_apply]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  | succ j ih =>
    intro f a ha
    rw [Function.iterate_succ_apply']
    have hin : ∀ s ∈ F, |pos x₀ s a.1| ≤ R := by
      intro s hs
      have := pos_sub_le hx s (hloc s hs) a.1
      have h2 : |pos x₀ s a.1| ≤ |a.1| + l := by
        calc |pos x₀ s a.1| = |(pos x₀ s a.1 - a.1) + a.1| := by ring_nf
          _ ≤ |pos x₀ s a.1 - a.1| + |a.1| := abs_add_le _ _
          _ ≤ l + |a.1| := by linarith
          _ = |a.1| + l := add_comm _ _
      push_cast at ha
      nlinarith [Int.natCast_nonneg l, Int.natCast_nonneg j]
    show (∑ s ∈ F, μ s * ((Pop μ F x₀)^[j] f) (pos x₀ s a.1)) = _
    rw [← sum_Qm_mul a hin ((Pop μ F x₀)^[j] f)]
    rw [pow_succ']
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : Qm μ F x₀ R a c = 0
    · simp [hc]
    · have hd := Qm_ne_zero hx hloc a c hc
      have hc' : |c.1| + l * j ≤ R := by
        have : |c.1| ≤ |a.1| + l := by
          calc |c.1| = |a.1 - (a.1 - c.1)| := by ring_nf
            _ ≤ |a.1| + |a.1 - c.1| := abs_sub _ _
            _ ≤ |a.1| + l := by linarith
        push_cast at ha
        linarith
      rw [ih f c hc', Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => by ring

lemma Qm_symm (hsymm : IsSymmetric μ) (hFinv : ∀ s ∈ F, s⁻¹ ∈ F) (hx : IsNP x₀) (R : ℤ) :
    (Qm μ F x₀ R)ᵀ = Qm μ F x₀ R := by
  ext a b
  rw [Matrix.transpose_apply]
  unfold Qm
  refine Finset.sum_nbij' (fun s => s⁻¹) (fun s => s⁻¹) (fun s hs => hFinv s hs)
    (fun s hs => hFinv s hs) (fun s _ => inv_inv s) (fun s _ => inv_inv s) fun s _ => ?_
  rw [hsymm s]
  congr 1
  have := pos_inv_eq_iff hx s b.1 a.1
  by_cases h : pos x₀ s b.1 = a.1
  · rw [if_pos h, if_pos (this.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mp h'))]

lemma Qm_nonneg (hμ : IsProbability μ) (R : ℤ) (a b : Box R) : 0 ≤ Qm μ F x₀ R a b :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hμ.1 s) (by split_ifs <;> norm_num)

lemma Qm_row (hμ : IsProbability μ) (R : ℤ) (a : Box R) : ∑ b, Qm μ F x₀ R a b ≤ 1 := by
  unfold Qm
  rw [Finset.sum_comm]
  calc ∑ s ∈ F, ∑ b : Box R, μ s * (if pos x₀ s a.1 = b.1 then 1 else 0)
      ≤ ∑ s ∈ F, μ s := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_of_le_one_right (hμ.1 s) ?_
        by_cases hp : pos x₀ s a.1 ∈ Finset.Icc (-R) R
        · rw [Finset.sum_eq_single ⟨pos x₀ s a.1, hp⟩]
          · simp
          · intro c _ hc
            have : pos x₀ s a.1 ≠ c.1 := fun h => hc (Subtype.ext h.symm)
            simp [this]
          · simp
        · rw [Finset.sum_eq_zero]
          · norm_num
          · intro c _
            have : pos x₀ s a.1 ≠ c.1 := fun h => hp (h ▸ c.2)
            simp [this]
    _ ≤ 1 := sum_le_hasSum F (fun s _ => hμ.1 s) hμ.2

/-- MB Corollary 3.5 (via Carne–Varopoulos and a union bound over times): the probability that
`μ^{*n}` does not act on the cylinder of depth `L` around `x₀` as a single shift of size at most
`L`. -/
theorem badE_bound (hμ : IsProbability μ) (hsymm : IsSymmetric μ)
    (hF : ∀ s, μ s ≠ 0 → s ∈ F) (hFinv : ∀ s ∈ F, s⁻¹ ∈ F) (hx : IsNP x₀) {l L : ℕ}
    (hl : 1 ≤ l) (hlL : l ≤ L) (hloc : ∀ s ∈ F, LocalAt S l (s : S ≃ₜ S)) (n : ℕ) (hn : 1 ≤ n) :
    badE μ x₀ L L n 0 ≤ (n + 1) * (2 * ((L : ℝ) + l * n) + 1) *
      (2 * Real.exp (-((((L : ℝ) - l) / l) ^ 2) / (2 * n))) := by
  set R : ℤ := L + l * n with hR
  set M : ℤ := (L : ℤ) - l with hM
  have hM0 : 0 ≤ M := by rw [hM]; omega
  have h1 := badE_le_sum hμ hF hx hloc (L := L) (L : ℤ) (by omega) n 0
  refine h1.trans ?_
  have h0 : (0 : ℤ) ∈ Finset.Icc (-R) R := mem_box_iff.mpr (by rw [abs_zero, hR]; positivity)
  set E : ℝ := 2 * Real.exp (-((((L : ℝ) - l) / l) ^ 2) / (2 * n)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hcard : (Fintype.card (Box R) : ℝ) = 2 * ((L : ℝ) + l * n) + 1 := by
    rw [Fintype.card_coe, Int.card_Icc]
    have : (0 : ℤ) ≤ R + 1 - -R := by
      rw [hR]; have : (0 : ℤ) ≤ (l : ℤ) * n := by positivity
      linarith [Int.natCast_nonneg L]
    rw [show ((R + 1 - -R).toNat : ℝ) = ((R + 1 - -R : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg this]
    rw [hR]; push_cast; ring
  rw [← hcard]
  have hterm : ∀ j ∈ range (n + 1), (Pop μ F x₀)^[j] (Iout M) 0 ≤ Fintype.card (Box R) * E := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have := iterate_Pop_eq (μ := μ) hx hloc R j (Iout M) ⟨0, h0⟩ (by
      simp only [abs_zero, zero_add, hR]
      have : (l : ℤ) * j ≤ l * n := by exact_mod_cast Nat.mul_le_mul_left l hj'
      linarith [Int.natCast_nonneg L])
    simp only at this
    rw [this]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp only [pow_zero, Matrix.one_apply]
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · simp only [if_true, one_mul]
        unfold Iout
        rw [if_neg (by simp [hM0])]
        positivity
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · rw [show (Fintype.card (Box R) : ℝ) * E = ∑ _b : Box R, E by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun b _ => ?_
      unfold Iout
      split_ifs with hb
      · rw [mul_one]
        have hcv := carne_varopoulos (Qm μ F x₀ R) (Qm_symm hsymm hFinv hx R)
          (Qm_nonneg hμ R) (Qm_row hμ R) (fun c => c.1) l (by omega)
          (fun a c h => Qm_ne_zero hx hloc a c h) j hjpos ⟨0, h0⟩ b
        refine hcv.trans ?_
        rw [hE]
        gcongr ?_ * Real.exp ?_
        have hlr : (0 : ℝ) < l := by exact_mod_cast hl
        have hjr : (0 : ℝ) < j := by exact_mod_cast hjpos
        have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj'
        have hbM : (M : ℝ) ≤ |(b.1 : ℝ)| := by
          have : M ≤ |b.1| := hb.le
          exact_mod_cast this
        have hMr : (M : ℝ) = (L : ℝ) - l := by rw [hM]; push_cast; ring
        have hM0r : (0 : ℝ) ≤ M := by exact_mod_cast hM0
        simp only [zero_sub, abs_neg]
        push_cast
        rw [neg_div, neg_div, neg_le_neg_iff, ← hMr]
        have hsq : ((M : ℝ) / l) ^ 2 ≤ (|(b.1 : ℝ)| / l) ^ 2 := by
          gcongr
        calc ((M : ℝ) / l) ^ 2 / (2 * n) ≤ (|(b.1 : ℝ)| / l) ^ 2 / (2 * n) := by gcongr
          _ ≤ (|(b.1 : ℝ)| / l) ^ 2 / (2 * j) := by gcongr
      · rw [mul_zero]; exact hE0
  calc ∑ j ∈ range (n + 1), (Pop μ F x₀)^[j] (Iout M) 0
      ≤ ∑ j ∈ range (n + 1), (Fintype.card (Box R) : ℝ) * E := Finset.sum_le_sum hterm
    _ = (n + 1) * Fintype.card (Box R) * E := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end Walk

/-! ## 6. Cylinders, counting and the entropy bound at a given depth (MB Def. 3.6, Lemmas 3.7,
3.8, Fact A.4) -/

section Assembly

open scoped Classical

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {S : Subshift ℤ A}

/-- The word of `y` on `[-L, L]`. -/
def win (L : ℕ) (y : S) : Fin (2 * L + 1) → A := fun j => (y : ℤ → A) ((j : ℤ) - L)

variable (S) in
/-- The words of length `2L+1` that occur in `S`. -/
def Words (L : ℕ) : Set (Fin (2 * L + 1) → A) :=
  {w | ∃ x ∈ (S : Set (ℤ → A)), ∃ i : ℤ, ∀ j : Fin (2 * L + 1), x (i + j) = w j}

lemma wordComplexity_eq (L : ℕ) :
    wordComplexity (S : Set (ℤ → A)) (2 * L + 1) = Nat.card (Words S L) := rfl

/-- `g` acts on every cylinder of depth `L` as a single shift of size at most `L`. -/
def GoodG (L : ℕ) (g : topologicalFullGroup ℤ S) : Prop :=
  ∃ c : (Fin (2 * L + 1) → A) → ℤ, (∀ w, |c w| ≤ L) ∧
    ∀ y : S, (g : S ≃ₜ S) y = c (win L y) +ᵥ y

/-- `g` acts on the cylinder of the word `w` as a single shift of size at most `L`. -/
def GoodW (L : ℕ) (w : Fin (2 * L + 1) → A) (g : topologicalFullGroup ℤ S) : Prop :=
  ∃ k : ℤ, |k| ≤ L ∧ ∀ y : S, win L y = w → (g : S ≃ₜ S) y = k +ᵥ y

lemma win_mem (L : ℕ) (y : S) : win L y ∈ Words S L :=
  ⟨y, y.2, -L, fun j => by simp only [win]; rw [neg_add_eq_sub]⟩

lemma agree_of_win_eq {L : ℕ} {y z : S} (h : win L y = win L z) :
    Agree L (y : ℤ → A) (z : ℤ → A) := by
  intro i hi
  rw [abs_le] at hi
  have hj : (i + L).toNat < 2 * L + 1 := by omega
  have := congrFun h ⟨(i + L).toNat, hj⟩
  simp only [win] at this
  rwa [show (((i + L).toNat : ℕ) : ℤ) - L = i by omega] at this

lemma win_eq_of_agree {L : ℕ} {y z : S} (h : Agree L (y : ℤ → A) (z : ℤ → A)) :
    win L y = win L z := by
  funext j
  simp only [win]
  apply h
  have := j.2
  rw [abs_le]; constructor <;> omega

lemma exists_np_of_word (hS : Dense {x : S | ∀ k : ℤ, k +ᵥ x = x → k = 0}) {L : ℕ}
    {w : Fin (2 * L + 1) → A} (hw : w ∈ Words S L) : ∃ x₀ : S, IsNP x₀ ∧ win L x₀ = w := by
  obtain ⟨x, hx, i, hi⟩ := hw
  set z : S := (i + L) +ᵥ (⟨x, hx⟩ : S)
  have hz : win L z = w := by
    funext j
    simp only [win, z, Subshift.coe_vadd, shift_apply]
    rw [← hi j]
    congr 1; ring
  obtain ⟨x₀, hx₀C, hx₀⟩ := hS.inter_open_nonempty {y : S | Agree L (y : ℤ → A) z}
    (isOpen_agree S L z) ⟨z, fun _ _ => rfl⟩
  exact ⟨x₀, hx₀, (win_eq_of_agree hx₀C).trans hz⟩

lemma goodW_of_goodB {L : ℕ} {x₀ : S} {w : Fin (2 * L + 1) → A} (hw : win L x₀ = w)
    {g : topologicalFullGroup ℤ S} (h : GoodB x₀ L L g 0) : GoodW L w g := by
  refine ⟨pos x₀ g 0, h.2, fun y hy => ?_⟩
  have := h.1 y (agree_of_win_eq (hy.trans hw.symm))
  rwa [zero_vadd] at this

lemma goodG_of_forall {L : ℕ} {g : topologicalFullGroup ℤ S}
    (h : ∀ w ∈ Words S L, GoodW L w g) : GoodG L g := by
  refine ⟨fun w => if hw : w ∈ Words S L then Classical.choose (h w hw) else 0, fun w => ?_,
    fun y => ?_⟩
  · dsimp only
    split_ifs with hw
    · exact (Classical.choose_spec (h w hw)).1
    · simp
  · dsimp only
    rw [dif_pos (win_mem L y)]
    exact (Classical.choose_spec (h _ (win_mem L y))).2 y rfl

lemma card_goodG_le [Finite A] (L : ℕ) (T : Finset (topologicalFullGroup ℤ S)) :
    (T.filter (GoodG L)).card ≤ (2 * L + 1) ^ Nat.card (Words S L) := by
  have hfin : (Words S L).Finite := Set.toFinite _
  have : Finite (Words S L) := hfin
  let Φ : (T.filter (GoodG L)) → (Words S L → Set.Icc (-(L : ℤ)) L) := fun g w =>
    ⟨Classical.choose (Finset.mem_filter.mp g.2).2 w,
      abs_le.mp ((Classical.choose_spec (Finset.mem_filter.mp g.2).2).1 w)⟩
  have hinj : Function.Injective Φ := by
    intro g g' he
    apply Subtype.ext
    apply Subtype.ext
    ext y
    have h1 := (Classical.choose_spec (Finset.mem_filter.mp g.2).2).2 y
    have h2 := (Classical.choose_spec (Finset.mem_filter.mp g'.2).2).2 y
    have h3 := congrArg Subtype.val (congrFun he ⟨win L y, win_mem L y⟩)
    simp only [Φ] at h3
    rw [h1, h2, h3]
  have := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] at this
  have hI : Nat.card (Set.Icc (-(L : ℤ)) L) = 2 * L + 1 := by
    rw [Nat.card_coe_set_eq, ← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]; omega
  rwa [hI] at this

/-- The entropy bound at depth `L` (MB (8), (9) and Fact A.4). -/
theorem entropy_le_depth [Finite A] (hS : Dense {x : S | ∀ k : ℤ, k +ᵥ x = x → k = 0})
    [Nonempty S]
    {μ : topologicalFullGroup ℤ S → ℝ} (hμ : IsProbability μ) (hsymm : IsSymmetric μ)
    {F : Finset (topologicalFullGroup ℤ S)} (hF : ∀ s, μ s ≠ 0 → s ∈ F)
    (hFinv : ∀ s ∈ F, s⁻¹ ∈ F) {l : ℕ} (hl : 1 ≤ l)
    (hloc : ∀ s ∈ F, LocalAt S l (s : S ≃ₜ S)) {L : ℕ} (hlL : l ≤ L) (n : ℕ) (hn : 1 ≤ n) :
    entropy (convPow μ n) ≤
      (wordComplexity (S : Set (ℤ → A)) (2 * L + 1) : ℝ) * Real.log (2 * L + 1) +
      (wordComplexity (S : Set (ℤ → A)) (2 * L + 1) : ℝ) * ((n + 1) * (2 * ((L : ℝ) + l * n) + 1) *
        (2 * Real.exp (-((((L : ℝ) - l) / l) ^ 2) / (2 * n)))) * (n * Real.log F.card) +
      Real.log 2 := by
  set ρ := wordComplexity (S : Set (ℤ → A)) (2 * L + 1) with hρ
  set E := (n + 1) * (2 * ((L : ℝ) + l * n) + 1) *
        (2 * Real.exp (-((((L : ℝ) - l) / l) ^ 2) / (2 * n))) with hE
  have hE0 : 0 ≤ E := by positivity
  have hp := isProb_convPow hμ n
  have hFsupp : Function.support μ ⊆ (F : Set _) := fun s hs => hF s hs
  obtain ⟨T, hTc, hTs⟩ := convPow_support μ F hFsupp n
  have hsplit := entropy_le_split hp T hTs (GoodG L)
  -- the good part
  have h1 : Real.log (T.filter (GoodG L)).card ≤ ρ * Real.log (2 * L + 1) := by
    have hc := card_goodG_le (S := S) L T
    rw [← wordComplexity_eq] at hc
    rcases Nat.eq_zero_or_pos (T.filter (GoodG L)).card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) L]))
    · calc Real.log (T.filter (GoodG L)).card ≤ Real.log (((2 * L + 1) ^ ρ : ℕ) : ℝ) :=
            Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hc)
        _ = ρ * Real.log (2 * L + 1) := by push_cast; rw [Real.log_pow]
  -- the support
  have h2 : Real.log T.card ≤ n * Real.log F.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    · calc Real.log T.card ≤ Real.log ((F.card ^ n : ℕ) : ℝ) :=
            Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hTc)
        _ = n * Real.log F.card := by push_cast; rw [Real.log_pow]
  -- the bad part
  have hW : (Words S L).Finite := Set.toFinite _
  have hWc : hW.toFinset.card = ρ := by
    rw [hρ, wordComplexity_eq, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hW]
  choose! xw hxw using fun w (hw : w ∈ Words S L) => exists_np_of_word hS hw
  have h3 : ∑ g ∈ T, convPow μ n g * (if GoodG L g then 0 else 1) ≤ ρ * E := by
    calc ∑ g ∈ T, convPow μ n g * (if GoodG L g then 0 else 1)
        ≤ ∑ g ∈ T, convPow μ n g * ∑ w ∈ hW.toFinset,
            (if GoodB (xw w) L L g 0 then 0 else 1) := by
          refine Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left ?_ (hp.1 g)
          by_cases hg : GoodG L g
          · rw [if_pos hg]
            exact Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num
          · rw [if_neg hg]
            have : ∃ w ∈ Words S L, ¬ GoodW L w g := by
              by_contra hcon; push Not at hcon; exact hg (goodG_of_forall hcon)
            obtain ⟨w, hw, hgw⟩ := this
            have hb : ¬ GoodB (xw w) L L g 0 := fun h => hgw (goodW_of_goodB (hxw w hw).2 h)
            calc (1 : ℝ) = if GoodB (xw w) L L g 0 then 0 else 1 := by rw [if_neg hb]
              _ ≤ _ := Finset.single_le_sum (f := fun w => if GoodB (xw w) L L g 0
                  then (0 : ℝ) else 1) (fun w _ => by split_ifs <;> norm_num)
                  (hW.mem_toFinset.mpr hw)
      _ = ∑ w ∈ hW.toFinset, badE μ (xw w) L L n 0 := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => ?_
          unfold badE
          rw [tsum_eq_sum (s := T)]
          intro g hg
          have : convPow μ n g = 0 := by by_contra h; exact hg (hTs h)
          rw [this, zero_mul]
      _ ≤ ∑ w ∈ hW.toFinset, E := by
          refine Finset.sum_le_sum fun w hw => ?_
          exact badE_bound hμ hsymm hF hFinv (hxw w (hW.mem_toFinset.mp hw)).1 hl hlL hloc n hn
      _ = ρ * E := by rw [Finset.sum_const, hWc, nsmul_eq_mul]
  have h3' : (∑ g ∈ T, convPow μ n g * (if GoodG L g then 0 else 1)) * Real.log T.card ≤
      (ρ * E) * (n * Real.log F.card) :=
    mul_le_mul h3 h2 (Real.log_natCast_nonneg _) (by positivity)
  linarith

end Assembly

/-! ## 7. Asymptotics -/

section Asymptotics

lemma term1_le {α C β x Lr : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hβ : 0 < β) (hx : 3 ≤ x)
    (hlog : 1 ≤ Real.log x) (hs : 1 ≤ Real.sqrt (β * x * Real.log x)) (hL0 : 0 ≤ Lr)
    (hLs : Lr < Real.sqrt (β * x * Real.log x) + 1) (hLx : Lr ≤ x) :
    C * (2 * Lr + 1) ^ α * Real.log (2 * Lr + 1) ≤
      2 * C * 5 ^ α * β ^ (α / 2) * x ^ (α / 2) * Real.log x ^ (1 + α / 2) := by
  set X := β * x * Real.log x with hX
  set s := Real.sqrt X with hs_def
  have hx0 : 0 < x := by linarith
  have hX0 : 0 ≤ X := by positivity
  have h1 : 2 * Lr + 1 ≤ 5 * s := by linarith
  have h2 : (2 * Lr + 1) ^ α ≤ (5 * s) ^ α := Real.rpow_le_rpow (by positivity) h1 hα
  have h3 : (5 * s) ^ α = 5 ^ α * β ^ (α / 2) * x ^ (α / 2) * Real.log x ^ (α / 2) := by
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hX0, hX, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hβ.le hx0.le]
    rw [show 1 / 2 * α = α / 2 by ring]
    ring
  have h4 : Real.log (2 * Lr + 1) ≤ 2 * Real.log x := by
    have : 2 * Lr + 1 ≤ x ^ 2 := by nlinarith
    calc Real.log (2 * Lr + 1) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have h5 : Real.log x ^ (1 + α / 2) = Real.log x * Real.log x ^ (α / 2) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hlog2 : 0 ≤ Real.log (2 * Lr + 1) := Real.log_nonneg (by linarith)
  calc C * (2 * Lr + 1) ^ α * Real.log (2 * Lr + 1)
      ≤ C * (5 * s) ^ α * (2 * Real.log x) := by gcongr
    _ = 2 * C * 5 ^ α * β ^ (α / 2) * x ^ (α / 2) * Real.log x ^ (1 + α / 2) := by
        rw [h3, h5]; ring

lemma term2_le {C l x ρ Lr e lF : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (_hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 9 * C * x ^ 2) (hL0 : 0 ≤ Lr) (hLx : Lr ≤ x) (hl : 0 ≤ l) (he0 : 0 ≤ e)
    (he : e ≤ (x ^ 6)⁻¹) (hF : 0 ≤ lF) :
    ρ * ((x + 1) * (2 * (Lr + l * x) + 1) * (2 * e)) * (x * lF) ≤ 36 * C * (3 + 2 * l) * lF := by
  have hx0 : 0 < x := by linarith
  calc ρ * ((x + 1) * (2 * (Lr + l * x) + 1) * (2 * e)) * (x * lF)
      ≤ (9 * C * x ^ 2) * ((2 * x) * ((3 + 2 * l) * x) * (2 * (x ^ 6)⁻¹)) * (x * lF) := by
        gcongr
        · linarith
        · nlinarith
    _ = 36 * C * (3 + 2 * l) * lF * x⁻¹ := by field_simp; ring
    _ ≤ 36 * C * (3 + 2 * l) * lF * 1 := by
        gcongr
        exact inv_le_one_of_one_le₀ hx
    _ = 36 * C * (3 + 2 * l) * lF := mul_one _

lemma exp_tail_le {Lr l x : ℝ} (hl : 0 < l) (hx : 1 ≤ x) (h2l : 2 * l ≤ Lr)
    (hL2 : 48 * l ^ 2 * x * Real.log x ≤ Lr ^ 2) (_hlog : 0 ≤ Real.log x) :
    Real.exp (-(((Lr - l) / l) ^ 2) / (2 * x)) ≤ (x ^ 6)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have h1 : 12 * x * Real.log x ≤ ((Lr - l) / l) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : 6 * Real.log x ≤ ((Lr - l) / l) ^ 2 / (2 * x) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  calc Real.exp (-(((Lr - l) / l) ^ 2) / (2 * x)) ≤ Real.exp (-(6 * Real.log x)) := by
        rw [neg_div]; exact Real.exp_le_exp.mpr (by linarith)
    _ = (x ^ 6)⁻¹ := by
        rw [Real.exp_neg, show (6 : ℝ) * Real.log x = ((6 : ℕ) : ℝ) * Real.log x by norm_num,
          Real.exp_nat_mul, Real.exp_log hx0]

end Asymptotics

/-! ## 8. Proof of Theorem 1.2 -/

section Final

variable {A : Type*} [Finite A] [TopologicalSpace A] [DiscreteTopology A] {S : Subshift ℤ A}

lemma one_le_wordComplexity [Nonempty S] (n : ℕ) :
    1 ≤ wordComplexity (S : Set (ℤ → A)) n := by
  obtain ⟨y⟩ := ‹Nonempty S›
  have hfin : ({w : Fin n → A | ∃ x ∈ (S : Set (ℤ → A)), ∃ i : ℤ,
      ∀ j : Fin n, x (i + j) = w j}).Finite := Set.toFinite _
  have : Finite {w : Fin n → A | ∃ x ∈ (S : Set (ℤ → A)), ∃ i : ℤ,
      ∀ j : Fin n, x (i + j) = w j} := hfin
  have hne : Nonempty {w : Fin n → A | ∃ x ∈ (S : Set (ℤ → A)), ∃ i : ℤ,
      ∀ j : Fin n, x (i + j) = w j} :=
    ⟨⟨fun j => (y : ℤ → A) j, y, y.2, 0, fun j => by rw [zero_add]⟩⟩
  exact Nat.card_pos

lemma alpha_nonneg [Nonempty S] {α C : ℝ}
    (hρ : ∀ n : ℕ, 1 ≤ n → (wordComplexity (S : Set (ℤ → A)) n : ℝ) ≤ C * (n : ℝ) ^ α) :
    0 ≤ α := by
  by_contra hα
  push Not at hα
  have ht : Filter.Tendsto (fun n : ℕ => C * (n : ℝ) ^ α) Filter.atTop (nhds (C * 0)) := by
    refine Filter.Tendsto.const_mul C ?_
    have := (tendsto_rpow_neg_atTop (y := -α) (by linarith)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def] using this
  rw [mul_zero] at ht
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds one_pos))
  have h1 := hρ (max N 1) (le_max_right _ _)
  have h2 := hN (max N 1) (le_max_left _ _)
  have h3 : (1 : ℝ) ≤ wordComplexity (S : Set (ℤ → A)) (max N 1) := by
    exact_mod_cast one_le_wordComplexity _
  linarith

lemma C_ge_one [Nonempty S] {α C : ℝ}
    (hρ : ∀ n : ℕ, 1 ≤ n → (wordComplexity (S : Set (ℤ → A)) n : ℝ) ≤ C * (n : ℝ) ^ α) :
    1 ≤ C := by
  have h1 := hρ 1 le_rfl
  have h3 : (1 : ℝ) ≤ wordComplexity (S : Set (ℤ → A)) 1 := by
    exact_mod_cast one_le_wordComplexity _
  simp at h1
  linarith

set_option maxHeartbeats 1000000 in
/-- The entropy bound for all large `n`. -/
theorem entropy_eventually_le [Nonempty S] (hS : Dense {x : S | ∀ k : ℤ, k +ᵥ x = x → k = 0})
    {α C : ℝ} (hα : α < 2)
    (hρ : ∀ n : ℕ, 1 ≤ n → (wordComplexity (S : Set (ℤ → A)) n : ℝ) ≤ C * (n : ℝ) ^ α)
    (μ : topologicalFullGroup ℤ S → ℝ) (hfin : (Function.support μ).Finite)
    (hμ : IsProbability μ) (hsymm : IsSymmetric μ) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      entropy (convPow μ n) ≤ K * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
  classical
  have hα0 := alpha_nonneg hρ
  have hC1 := C_ge_one hρ
  set F := hfin.toFinset with hF_def
  have hF : ∀ s, μ s ≠ 0 → s ∈ F := fun s hs => hfin.mem_toFinset.mpr hs
  have hFinv : ∀ s ∈ F, s⁻¹ ∈ F := fun s hs => by
    rw [hfin.mem_toFinset] at hs ⊢
    rw [Function.mem_support, hsymm]; exact hs
  have hex : ∀ s : topologicalFullGroup ℤ S, ∃ l, LocalAt S l (s : S ≃ₜ S) :=
    fun s => exists_localAt (s : S ≃ₜ S) s.2
  choose lf hlf using hex
  set l := max 1 (F.sup lf) with hl_def
  have hl : 1 ≤ l := le_max_left _ _
  have hloc : ∀ s ∈ F, LocalAt S l (s : S ≃ₜ S) := fun s hs =>
    (hlf s).mono ((Finset.le_sup hs).trans (le_max_right _ _))
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  set β : ℝ := 48 * (l : ℝ) ^ 2 with hβ
  have hβ0 : 0 < β := by positivity
  -- eventually `β log n ≤ n / 4`
  have hev : ∀ᶠ n : ℕ in Filter.atTop, β * Real.log n ≤ n / 4 := by
    have h := Real.isLittleO_log_id_atTop.bound (c := 1 / (4 * β)) (by positivity)
    have h' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
    filter_upwards [h', Filter.eventually_ge_atTop 1] with n hn hn1
    simp only [id, Real.norm_eq_abs] at hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [abs_of_nonneg hn0] at hn
    have := (le_abs_self (Real.log n)).trans hn
    rw [show 1 / (4 * β) * (n : ℝ) = (n / 4) / β by field_simp] at this
    rw [le_div_iff₀ hβ0] at this
    linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
  set lF := Real.log F.card
  have hlF : 0 ≤ lF := Real.log_natCast_nonneg _
  refine ⟨2 * C * 5 ^ α * β ^ (α / 2) + 36 * C * (3 + 2 * l) * lF + Real.log 2, max 3 N₁,
    fun n hn => ?_⟩
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hnN : N₁ ≤ n := (le_max_right _ _).trans hn
  have hx3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hx0 : (0 : ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  set X := β * n * Real.log n with hX
  have hX48 : 48 ≤ X := by
    have : (48 : ℝ) ≤ β := by rw [hβ]; nlinarith
    have : (3 : ℝ) ≤ n * Real.log n := by nlinarith
    rw [hX, mul_assoc]; nlinarith
  set s := Real.sqrt X with hs_def
  have hs2 : s ^ 2 = X := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : 1 ≤ s := by nlinarith
  set L := ⌈s⌉₊ with hL_def
  have hsL : s ≤ L := Nat.le_ceil s
  have hLs : (L : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0
  have hL2 : X ≤ (L : ℝ) ^ 2 := by nlinarith
  have h2l : (2 * l : ℝ) ≤ L := by
    have : 4 * (l : ℝ) ^ 2 ≤ X := by
      rw [hX, hβ]
      have : (3 : ℝ) ≤ n * Real.log n := by nlinarith
      nlinarith
    nlinarith
  have hlL : l ≤ L := by
    have : (l : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hLn : (L : ℝ) ≤ n := by
    have h1 := hN₁ n hnN
    have : X ≤ (n : ℝ) ^ 2 / 4 := by rw [hX]; nlinarith
    have : s ≤ n / 2 := by nlinarith
    linarith
  have hmain := entropy_le_depth hS hμ hsymm hF hFinv hl hloc hlL n (by omega)
  set ρ := (wordComplexity (S : Set (ℤ → A)) (2 * L + 1) : ℝ)
  have hρ1 : ρ ≤ C * (2 * L + 1 : ℝ) ^ α := by
    have := hρ (2 * L + 1) (by omega)
    push_cast at this
    exact this
  have hρ0 : 0 ≤ ρ := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hT1 : ρ * Real.log (2 * L + 1) ≤
      2 * C * 5 ^ α * β ^ (α / 2) * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
    calc ρ * Real.log (2 * L + 1) ≤ C * (2 * L + 1 : ℝ) ^ α * Real.log (2 * L + 1) :=
          mul_le_mul_of_nonneg_right hρ1 (Real.log_nonneg (by linarith))
      _ ≤ _ := term1_le hα0 (by linarith) hβ0 hx3 hlog1 hs1 hL0 hLs hLn
  have hρ9 : ρ ≤ 9 * C * (n : ℝ) ^ 2 := by
    calc ρ ≤ C * (2 * L + 1 : ℝ) ^ α := hρ1
      _ ≤ C * (2 * L + 1 : ℝ) ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hα.le)
            (by linarith)
      _ ≤ C * (3 * n) ^ (2 : ℝ) := by
          gcongr
          linarith
      _ = 9 * C * (n : ℝ) ^ 2 := by rw [Real.rpow_two]; ring
  have he := exp_tail_le (Lr := L) (l := l) (x := n) (by linarith) (by linarith) h2l
    (by rw [hX, hβ] at hL2; linarith) (by linarith)
  have hT2 := term2_le (C := C) (l := l) (x := n) (ρ := ρ) (Lr := L)
    (e := Real.exp (-((((L : ℝ) - l) / l) ^ 2) / (2 * n))) (lF := lF) (by linarith)
    (by linarith) hρ0 hρ9 hL0 hLn (by linarith) (Real.exp_pos _).le he hlF
  have hD : 1 ≤ (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
    have h1 : 1 ≤ (n : ℝ) ^ (α / 2) := Real.one_le_rpow (by linarith) (by linarith)
    have h2 : 1 ≤ Real.log n ^ (1 + α / 2) := Real.one_le_rpow hlog1 (by linarith)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hK2 : 0 ≤ 36 * C * (3 + 2 * (l : ℝ)) * lF := by
    have : 0 ≤ C := by linarith
    positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc entropy (convPow μ n)
      ≤ ρ * Real.log (2 * L + 1) + ρ * ((n + 1) * (2 * ((L : ℝ) + l * n) + 1) *
          (2 * Real.exp (-((((L : ℝ) - l) / l) ^ 2) / (2 * n)))) * (n * lF) + Real.log 2 :=
        hmain
    _ ≤ 2 * C * 5 ^ α * β ^ (α / 2) * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) +
          36 * C * (3 + 2 * l) * lF + Real.log 2 := by linarith
    _ ≤ (2 * C * 5 ^ α * β ^ (α / 2) + 36 * C * (3 + 2 * l) * lF + Real.log 2) *
          (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
        rw [mul_assoc _ ((n : ℝ) ^ (α / 2)), mul_assoc _ ((n : ℝ) ^ (α / 2))]
        nlinarith

end Final

end IETMB

open IETMB in
theorem chk_entropy_convPow_le_and_asymptoticEntropy_eq_zero
    {A : Type*} [Finite A] [TopologicalSpace A] [DiscreteTopology A] (S : Subshift ℤ A)
    (hS : Dense {x : S | ∀ k : ℤ, k +ᵥ x = x → k = 0})
    {α C : ℝ} (hα : α < 2)
    (hρ : ∀ n : ℕ, 1 ≤ n → (wordComplexity (S : Set (ℤ → A)) n : ℝ) ≤ C * (n : ℝ) ^ α)
    (μ : topologicalFullGroup ℤ S → ℝ) (hfin : (Function.support μ).Finite)
    (hμ : IsProbability μ) (hsymm : IsSymmetric μ) :
    (∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
      entropy (convPow μ n) ≤ C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2)) ∧
    asymptoticEntropy μ = 0 := by
  classical
  -- the bound for all `n ≥ 2`
  have hbound : ∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
      entropy (convPow μ n) ≤ C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
    rcases isEmpty_or_nonempty S with hSe | hSne
    · have hsub : ∀ g h : topologicalFullGroup ℤ S, g = h := fun g h =>
        Subtype.ext (Homeomorph.ext fun y => (IsEmpty.false y).elim)
      refine ⟨0, fun n _ => ?_⟩
      have hp := isProb_convPow hμ n
      have hT : Function.support (convPow μ n) ⊆
          (({1} : Finset (topologicalFullGroup ℤ S)) : Set (topologicalFullGroup ℤ S)) :=
        fun g _ => by
        simp [hsub g 1]
      have h1 := sum_eq_one_of_support hp _ hT
      rw [Finset.sum_singleton] at h1
      rw [entropy_eq_sum _ hT, Finset.sum_singleton, h1, Real.negMulLog_one]
      simp
    · obtain ⟨K, N₀, hK⟩ := entropy_eventually_le hS hα hρ μ hfin hμ hsymm
      set D : ℕ → ℝ := fun m => (m : ℝ) ^ (α / 2) * Real.log m ^ (1 + α / 2) with hD
      have hDpos : ∀ m : ℕ, 2 ≤ m → 0 < D m := by
        intro m hm
        have hm' : (1 : ℝ) < m := by exact_mod_cast hm
        exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
          (Real.rpow_pos_of_pos (Real.log_pos hm') _)
      have hH0 : ∀ m, 0 ≤ entropy (convPow μ m) := fun m => entropy_nonneg (isProb_convPow hμ m)
      have hq0 : ∀ m, 2 ≤ m → 0 ≤ entropy (convPow μ m) / D m := fun m h =>
        div_nonneg (hH0 m) (hDpos m h).le
      set R := (Finset.range N₀).filter (fun m => 2 ≤ m)
      refine ⟨|K| + ∑ m ∈ R, entropy (convPow μ m) / D m, fun n hn => ?_⟩
      have hDn := hDpos n hn
      have hsum0 : 0 ≤ ∑ m ∈ R, entropy (convPow μ m) / D m :=
        Finset.sum_nonneg fun m hm => hq0 m (Finset.mem_filter.mp hm).2
      rw [mul_assoc]
      show entropy (convPow μ n) ≤ (|K| + _) * D n
      rcases le_or_gt N₀ n with h | h
      · have := hK n h
        rw [mul_assoc] at this
        refine this.trans ?_
        exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hDn.le
      · have hle : entropy (convPow μ n) / D n ≤
            ∑ m ∈ R, entropy (convPow μ m) / D m :=
          Finset.single_le_sum (f := fun m => entropy (convPow μ m) / D m)
            (fun m hm => hq0 m (Finset.mem_filter.mp hm).2)
            (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hn⟩)
        calc entropy (convPow μ n) = entropy (convPow μ n) / D n * D n := by
              field_simp
          _ ≤ (|K| + ∑ m ∈ R, entropy (convPow μ m) / D m) * D n := by
              gcongr
              linarith [abs_nonneg K]
  refine ⟨hbound, ?_⟩
  obtain ⟨C', hC'⟩ := hbound
  unfold asymptoticEntropy
  apply Filter.Tendsto.limUnder_eq
  -- `C' n^{α/2} (log n)^{1+α/2} / n → 0`
  have hlo := (isLittleO_log_rpow_rpow_atTop (1 + α / 2) (s := 1 - α / 2) (by linarith)).tendsto_div_nhds_zero
  have hlo' := (hlo.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C'
  rw [mul_zero] at hlo'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlo' ?_ ?_
  · filter_upwards with n
    exact div_nonneg (entropy_nonneg (isProb_convPow hμ n)) (Nat.cast_nonneg n)
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    simp only [Function.comp_apply]
    have : C' * (Real.log n ^ (1 + α / 2) / (n : ℝ) ^ (1 - α / 2)) =
        C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) / n := by
      rw [Real.rpow_sub hn0, Real.rpow_one]
      have : (0 : ℝ) < (n : ℝ) ^ (α / 2) := Real.rpow_pos_of_pos hn0 _
      field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (hC' n hn) hn0.le

end MatteBon
end

open CantorSystems ErschlerZheng
theorem solution
    {A : Type*} [Finite A] [TopologicalSpace A] [DiscreteTopology A] (S : Subshift ℤ A)
    (hS : Dense {x : S | ∀ k : ℤ, k +ᵥ x = x → k = 0})
    {α C : ℝ} (hα : α < 2)
    (hρ : ∀ n : ℕ, 1 ≤ n → (wordComplexity (S : Set (ℤ → A)) n : ℝ) ≤ C * (n : ℝ) ^ α)
    (μ : topologicalFullGroup ℤ S → ℝ) (hfin : (Function.support μ).Finite)
    (hμ : IsProbability μ) (hsymm : IsSymmetric μ) :
    (∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
      entropy (convPow μ n) ≤ C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2)) ∧
    asymptoticEntropy μ = 0 :=
  MatteBon.chk_entropy_convPow_le_and_asymptoticEntropy_eq_zero S hS hα hρ μ hfin hμ hsymm
