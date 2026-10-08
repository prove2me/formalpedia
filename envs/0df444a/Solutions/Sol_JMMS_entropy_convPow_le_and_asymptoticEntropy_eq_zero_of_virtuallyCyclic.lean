-- Prove2me | solution 1 for JMMS.entropy_convPow_le_and_asymptoticEntropy_eq_zero_of_virtuallyCyclic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:08:13.753858+00:00
-- url     : https://prove2.me/submissions/ef59796d-833a-41e0-bff6-eea9a8d27012

import Mathlib
import Definitions.Def_CantorSystems
import Definitions.Def_ErschlerZheng_Walks

section

/-!
# Matte Bon's Theorem 1.2 for a virtually cyclic abelian group (JMMS §5.3)

Let `Γ` be an abelian group with an element `γ₀` of infinite order generating a subgroup of finite
index, `S` a `Γ`-subshift with dense points of trivial stabiliser, `T` a finite generating set and
`p` a clopen separating partition with `ρ_{T,p}(n) ≤ C n^α` (`α < 2`). Every finitely supported
symmetric probability `μ` on `[[Γ]]` has `H(μ^{*n}) ≤ C' n^{α/2} (log n)^{1+α/2}` and zero
asymptotic entropy.

This adapts `Solutions/IET/MatteBon.lean` (the case `Γ = ℤ`):
- positions along the orbit of a free point are elements of `Γ`, measured by a *height*
  `h : Γ → ℤ` (`a = σ([a]) + h(a) γ₀` for a section `σ` of `Γ → Γ/⟨γ₀⟩`), which is Lipschitz for
  the word metric of `T` and has finite level sets of linear size;
- cylinders are the pieces of the join `⋁_{|δ|_T ≤ L} δP`, counted by `ρ_{T,p}(L)`;
- every element of `[[Γ]]` acts on each such piece (for `L` large) as one translation, by
  compactness and separation (the analogue of `exists_localAt`).
The Carne–Varopoulos bound, the entropy split and the asymptotics are as in the `ℤ` case.
-/

open CantorSystems ErschlerZheng

namespace JMMS
namespace IETMBVC

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

/-! ## 4. Word balls and the height -/

section Balls

variable {Γ : Type*} [AddCommGroup Γ] (T : Finset Γ)

lemma zero_mem_ball (n : ℕ) : (0 : Γ) ∈ wordBall (T : Set Γ) n :=
  ⟨[], by simp, by simp, by simp⟩

lemma ball_mono {m n : ℕ} (h : m ≤ n) : wordBall (T : Set Γ) m ⊆ wordBall (T : Set Γ) n :=
  fun _ ⟨l, hl, hT, hs⟩ => ⟨l, hl.trans h, hT, hs⟩

lemma add_mem_ball {a b : Γ} {m n : ℕ} (ha : a ∈ wordBall (T : Set Γ) m)
    (hb : b ∈ wordBall (T : Set Γ) n) : a + b ∈ wordBall (T : Set Γ) (m + n) := by
  obtain ⟨l, hl, hT, rfl⟩ := ha
  obtain ⟨l', hl', hT', rfl⟩ := hb
  refine ⟨l ++ l', by simp; omega, fun t ht => ?_, by simp⟩
  rcases List.mem_append.mp ht with h | h
  · exact hT t h
  · exact hT' t h

lemma neg_mem_ball {a : Γ} {n : ℕ} (ha : a ∈ wordBall (T : Set Γ) n) :
    -a ∈ wordBall (T : Set Γ) n := by
  obtain ⟨l, hl, hT, rfl⟩ := ha
  refine ⟨l.map Neg.neg, by simpa using hl, fun t ht => ?_, ?_⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    rcases hT u hu with h | h
    · right; simpa using h
    · left; exact h
  · induction l with
    | nil => simp
    | cons u l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih (by simp at hl ⊢; omega) (fun t ht => hT t (List.mem_cons_of_mem _ ht))]
      abel

lemma gen_mem_ball {t : Γ} (ht : t ∈ T) : t ∈ wordBall (T : Set Γ) 1 :=
  ⟨[t], by simp, by simp [ht], by simp⟩

lemma zsmul_mem_ball {a : Γ} {c : ℕ} (ha : a ∈ wordBall (T : Set Γ) c) (m : ℤ) :
    m • a ∈ wordBall (T : Set Γ) (m.natAbs * c) := by
  have hnat : ∀ k : ℕ, (k : ℤ) • a ∈ wordBall (T : Set Γ) (k * c) := by
    intro k
    induction k with
    | zero => simpa using zero_mem_ball T 0
    | succ k ih =>
      have := add_mem_ball T ih ha
      rw [show (k + 1) * c = k * c + c by ring]
      simpa [add_smul] using this
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using hnat k
  · simpa using neg_mem_ball T (hnat k)

lemma exists_mem_ball (hT : AddSubgroup.closure (T : Set Γ) = ⊤) (γ : Γ) :
    ∃ n, γ ∈ wordBall (T : Set Γ) n := by
  have : γ ∈ AddSubgroup.closure (T : Set Γ) := hT ▸ AddSubgroup.mem_top γ
  induction this using AddSubgroup.closure_induction with
  | mem x hx => exact ⟨1, gen_mem_ball T hx⟩
  | zero => exact ⟨0, zero_mem_ball T 0⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy; exact ⟨m + n, add_mem_ball T hm hn⟩
  | neg x _ hx => obtain ⟨m, hm⟩ := hx; exact ⟨m, neg_mem_ball T hm⟩

lemma ball_finite (n : ℕ) : (wordBall (T : Set Γ) n).Finite := by
  classical
  induction n with
  | zero =>
    refine (Set.finite_singleton (0 : Γ)).subset ?_
    rintro _ ⟨l, hl, -, rfl⟩
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [this]
  | succ n ih =>
    refine (Set.Finite.image2 (· + ·) (insert 0 (T ∪ T.image Neg.neg)).finite_toSet ih).subset ?_
    rintro _ ⟨l, hl, hT, rfl⟩
    cases l with
    | nil => exact ⟨0, by simp, 0, zero_mem_ball T n, by simp⟩
    | cons t r =>
      refine ⟨t, ?_, r.sum, ⟨r, by simp at hl; omega, fun u hu => hT u (List.mem_cons_of_mem _ hu),
        rfl⟩, by simp⟩
      rcases hT t (by simp) with h | h
      · simp [h]
      · simp only [Finset.coe_insert, Finset.coe_union, Finset.coe_image, Set.mem_insert_iff,
          Set.mem_union, Finset.mem_coe, Set.mem_image]
        right; right; exact ⟨-t, h, neg_neg t⟩

lemma lip_of_gen (h : Γ → ℤ) (c : ℕ)
    (hc : ∀ a, ∀ t ∈ T, |h (a + t) - h a| ≤ c ∧ |h (a - t) - h a| ≤ c) :
    ∀ (n : ℕ) (a δ : Γ), δ ∈ wordBall (T : Set Γ) n → |h (a + δ) - h a| ≤ c * n := by
  have key : ∀ l : List Γ, (∀ t ∈ l, t ∈ (T : Set Γ) ∨ -t ∈ (T : Set Γ)) →
      ∀ a, |h (a + l.sum) - h a| ≤ c * l.length := by
    intro l
    induction l with
    | nil => intro _ a; simp
    | cons t r ih =>
      intro hl a
      have h1 := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu)) (a + t)
      have h2 : |h (a + t) - h a| ≤ c := by
        rcases hl t (by simp) with ht | ht
        · exact (hc a t ht).1
        · have := (hc a (-t) ht).2
          rwa [sub_neg_eq_add] at this
      rw [List.sum_cons, ← add_assoc, List.length_cons]
      calc |h (a + t + r.sum) - h a| = |(h (a + t + r.sum) - h (a + t)) + (h (a + t) - h a)| := by
            ring_nf
        _ ≤ |h (a + t + r.sum) - h (a + t)| + |h (a + t) - h a| := abs_add_le _ _
        _ ≤ c * r.length + c := add_le_add h1 h2
        _ = c * ((r.length + 1 : ℕ) : ℤ) := by push_cast; ring
  rintro n a _ ⟨l, hl, hT, rfl⟩
  refine (key l hT a).trans ?_
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl) (by positivity)

end Balls

/-- A height on `Γ`: a map `h : Γ → ℤ` with finite level sets of linear size, Lipschitz for the
word metric of `T`, and coarsely controlling the word length. -/
structure Height (Γ : Type*) [AddCommGroup Γ] (T : Finset Γ) where
  h : Γ → ℤ
  box : ℤ → Finset Γ
  mem_box : ∀ R a, a ∈ box R ↔ |h a| ≤ R
  k : ℕ
  card_box : ∀ R : ℕ, ((box R).card : ℝ) ≤ k * (2 * R + 1)
  h_zero : h 0 = 0
  c₀ : ℕ
  lip : ∀ (n : ℕ) (a δ : Γ), δ ∈ wordBall (T : Set Γ) n → |h (a + δ) - h a| ≤ c₀ * n
  c₁ : ℕ
  c₂ : ℕ
  coarse : ∀ a, a ∈ wordBall (T : Set Γ) (c₁ * (h a).natAbs + c₂)

section HeightConstr

variable {Γ : Type*} [AddCommGroup Γ] (T : Finset Γ)

theorem exists_height (hΓ : ∃ γ : Γ, addOrderOf γ = 0 ∧ (AddSubgroup.zmultiples γ).FiniteIndex)
    (hT : AddSubgroup.closure (T : Set Γ) = ⊤) : Nonempty (Height Γ T) := by
  classical
  obtain ⟨γ₀, hord, hfi⟩ := hΓ
  set H := AddSubgroup.zmultiples γ₀ with hH
  have := hfi
  let _ : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  have uniq : ∀ m m' : ℤ, m • γ₀ = m' • γ₀ → m = m' := by
    intro m m' he
    by_contra hne
    have h1 : (m - m') • γ₀ = 0 := by simp [sub_zsmul, he]
    have : IsOfFinAddOrder γ₀ :=
      isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨m - m', sub_ne_zero.mpr hne, h1⟩
    exact (addOrderOf_eq_zero_iff.mp hord) this
  have hex : ∀ a : Γ, ∃ m : ℤ, m • γ₀ = -(QuotientAddGroup.mk a : Γ ⧸ H).out + a := by
    intro a
    have : (QuotientAddGroup.mk (QuotientAddGroup.mk a : Γ ⧸ H).out : Γ ⧸ H) =
        QuotientAddGroup.mk a := QuotientAddGroup.out_eq' _
    rw [QuotientAddGroup.eq] at this
    exact AddSubgroup.mem_zmultiples_iff.mp this
  choose h₀ hh₀ using hex
  have hdec : ∀ a, a = (QuotientAddGroup.mk a : Γ ⧸ H).out + h₀ a • γ₀ := by
    intro a; rw [hh₀]; abel
  have hshift : ∀ b (m : ℤ), h₀ (b + m • γ₀) = h₀ b + m := by
    intro b m
    have hq : (QuotientAddGroup.mk (b + m • γ₀) : Γ ⧸ H) = QuotientAddGroup.mk b := by
      rw [QuotientAddGroup.eq]
      have : -(b + m • γ₀) + b = (-m) • γ₀ := by rw [neg_zsmul]; abel
      rw [this]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples γ₀) _
    apply uniq
    rw [hh₀, hq, add_zsmul, hh₀]; abel
  have hout : ∀ q : Γ ⧸ H, h₀ q.out = 0 := by
    intro q
    apply uniq
    rw [hh₀, QuotientAddGroup.out_eq', neg_add_cancel, zero_smul]
  set hf : Γ → ℤ := fun a => h₀ a - h₀ 0 with hf_def
  have hf_shift : ∀ b (m : ℤ), hf (b + m • γ₀) = hf b + m := by
    intro b m; simp only [hf, hshift]; ring
  have hstep : ∀ a t, hf (a + t) - hf a = h₀ ((QuotientAddGroup.mk a : Γ ⧸ H).out + t) := by
    intro a t
    have : a + t = ((QuotientAddGroup.mk a : Γ ⧸ H).out + t) + h₀ a • γ₀ := by
      conv_lhs => rw [hdec a]
      abel
    simp only [hf]; rw [this, hshift]; ring
  set c₀ : ℕ := ((Finset.univ : Finset (Γ ⧸ H)) ×ˢ T).sup (fun qt =>
    (h₀ (qt.1.out + qt.2)).natAbs + (h₀ (qt.1.out + -qt.2)).natAbs) with hc₀
  obtain ⟨c₁, hc₁⟩ := exists_mem_ball T hT γ₀
  have hN : ∀ q : Γ ⧸ H, ∃ N, q.out + h₀ 0 • γ₀ ∈ wordBall (T : Set Γ) N :=
    fun q => exists_mem_ball T hT _
  choose N hN using hN
  set c₂ : ℕ := (Finset.univ : Finset (Γ ⧸ H)).sup N with hc₂
  refine ⟨{ h := hf
            box := fun R => ((Finset.univ : Finset (Γ ⧸ H)) ×ˢ Finset.Icc (-R) R).image
              (fun qm => qm.1.out + (qm.2 + h₀ 0) • γ₀)
            mem_box := ?_
            k := Fintype.card (Γ ⧸ H)
            card_box := ?_
            h_zero := by simp [hf]
            c₀ := c₀
            lip := ?_
            c₁ := c₁
            c₂ := c₂
            coarse := ?_ }⟩
  · intro R a
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc,
      Prod.exists]
    constructor
    · rintro ⟨q, m, hm, rfl⟩
      have : hf (q.out + (m + h₀ 0) • γ₀) = m := by
        rw [hf_shift]; simp only [hf, hout]; ring
      rw [this, abs_le]; exact hm
    · intro ha
      refine ⟨QuotientAddGroup.mk a, hf a, abs_le.mp ha, ?_⟩
      simp only [hf, sub_add_cancel]; exact (hdec a).symm
  · intro R
    refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Finset.card_univ, Int.card_Icc]
    have : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
    rw [this]; push_cast; exact le_refl _
  · refine lip_of_gen T hf c₀ fun a t ht => ⟨?_, ?_⟩
    · rw [hstep]
      have hle := Finset.le_sup (f := fun qt : (Γ ⧸ H) × Γ =>
          (h₀ (qt.1.out + qt.2)).natAbs + (h₀ (qt.1.out + -qt.2)).natAbs)
          (s := (Finset.univ : Finset (Γ ⧸ H)) ×ˢ T) (b := ((QuotientAddGroup.mk a : Γ ⧸ H), t))
          (Finset.mem_product.mpr ⟨Finset.mem_univ _, ht⟩)
      have : (h₀ ((QuotientAddGroup.mk a : Γ ⧸ H).out + t)).natAbs ≤ c₀ := by
        rw [hc₀]; exact le_trans (Nat.le_add_right _ _) hle
      rw [Int.abs_eq_natAbs]; exact_mod_cast this
    · rw [show a - t = a + -t from sub_eq_add_neg a t, hstep]
      have hle := Finset.le_sup (f := fun qt : (Γ ⧸ H) × Γ =>
          (h₀ (qt.1.out + qt.2)).natAbs + (h₀ (qt.1.out + -qt.2)).natAbs)
          (s := (Finset.univ : Finset (Γ ⧸ H)) ×ˢ T) (b := ((QuotientAddGroup.mk a : Γ ⧸ H), t))
          (Finset.mem_product.mpr ⟨Finset.mem_univ _, ht⟩)
      have : (h₀ ((QuotientAddGroup.mk a : Γ ⧸ H).out + -t)).natAbs ≤ c₀ := by
        rw [hc₀]; exact le_trans (Nat.le_add_left _ _) hle
      rw [Int.abs_eq_natAbs]; exact_mod_cast this
  · intro a
    have he : a = ((QuotientAddGroup.mk a : Γ ⧸ H).out + h₀ 0 • γ₀) + hf a • γ₀ := by
      conv_lhs => rw [hdec a]
      simp only [hf]; rw [sub_zsmul]; abel
    have h1 := ball_mono T (Finset.le_sup (f := N) (Finset.mem_univ (QuotientAddGroup.mk a)))
      (hN (QuotientAddGroup.mk a))
    have h2 := add_mem_ball T h1 (zsmul_mem_ball T hc₁ (hf a))
    rw [← he] at h2
    exact ball_mono T (by rw [mul_comm]; omega) h2

end HeightConstr

/-! ## 5. Cylinders, locality of elements of `[[Γ]]` and the orbit cocycle -/

section Topology

variable {Γ A ι : Type*} [AddCommGroup Γ] [TopologicalSpace A] [DiscreteTopology A]
  {S : Subshift Γ A} (T : Finset Γ) (p : S → ι)

/-- The name of the piece of `⋁_{|δ|_T ≤ L} δP` containing `y`. -/
def win (L : ℕ) (y : S) : wordBall (T : Set Γ) L → ι := fun δ => p (-(δ : Γ) +ᵥ y)

lemma complexity_eq (L : ℕ) :
    complexity (T : Set Γ) p L = Nat.card (Set.range (win T p L)) := rfl

variable {T p}

lemma win_mono {L L' : ℕ} (hL : L ≤ L') {y z : S} (h : win T p L' y = win T p L' z) :
    win T p L y = win T p L z := by
  funext δ
  exact congrFun h ⟨δ.1, ball_mono T hL δ.2⟩

lemma continuous_vadd' (δ : Γ) : Continuous (fun z : S => δ +ᵥ z) := by
  have : Continuous (fun z : S => shift δ (z : Γ → A)) :=
    continuous_pi fun i => (continuous_apply (i + δ)).comp continuous_subtype_val
  exact this.subtype_mk (fun z => S.isSubshift.2 δ z z.2)

lemma cyl_eq (L : ℕ) (y : S) : {z : S | win T p L z = win T p L y} =
    ⋂ δ : wordBall (T : Set Γ) L, (fun z : S => -(δ : Γ) +ᵥ z) ⁻¹' (p ⁻¹' {win T p L y δ}) := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
    funext_iff]
  rfl

lemma isClosed_cyl (hp : IsClopenPartition p) (L : ℕ) (y : S) :
    IsClosed {z : S | win T p L z = win T p L y} := by
  rw [cyl_eq]
  exact isClosed_iInter fun δ => (hp _).1.preimage (continuous_vadd' _)

lemma isOpen_cyl (hp : IsClopenPartition p) (L : ℕ) (y : S) :
    IsOpen {z : S | win T p L z = win T p L y} := by
  rw [cyl_eq]
  have : Finite (wordBall (T : Set Γ) L) := (ball_finite T L).to_subtype
  exact isOpen_iInter_of_finite fun δ => (hp _).2.preimage (continuous_vadd' _)

lemma compactSpace_S [Finite A] : CompactSpace S := by
  have : CompactSpace (Γ → A) := Pi.compactSpace
  exact isCompact_iff_compactSpace.mp S.isSubshift.1.isCompact

/-- Small cylinders: by compactness and separation, every neighbourhood of `y` contains the piece
of `⋁_{|δ|_T ≤ L} δP` around `y`, for some `L`. -/
lemma exists_cyl_subset [Finite A] (hT : AddSubgroup.closure (T : Set Γ) = ⊤)
    (hp : IsClopenPartition p) (hsep : IsSeparatingPartition Γ p) (y : S) {U : Set S}
    (hU : U ∈ 𝓝 y) : ∃ L, {z : S | win T p L z = win T p L y} ⊆ U := by
  have := compactSpace_S (S := S)
  have hc : IsCompact (interior U)ᶜ := isOpen_interior.isClosed_compl.isCompact
  obtain ⟨L, hL⟩ := hc.elim_directed_family_closed (fun L : ℕ => {z : S | win T p L z = win T p L y})
    (fun L => isClosed_cyl hp L y) (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hall⟩
      rw [Set.mem_iInter] at hall
      apply hz
      have : z = y := hsep z y fun γ => by
        obtain ⟨n, hn⟩ := exists_mem_ball T hT (-γ)
        have := congrFun (hall n) ⟨-γ, hn⟩
        simpa [win] using this
      rw [this]; exact mem_interior_iff_mem_nhds.mpr hU)
    (fun L L' => ⟨max L L', fun z hz => win_mono (le_max_left _ _) hz,
      fun z hz => win_mono (le_max_right _ _) hz⟩)
  refine ⟨L, fun z hz => interior_subset ?_⟩
  by_contra hzU
  have : z ∈ (interior U)ᶜ ∩ {z : S | win T p L z = win T p L y} := ⟨hzU, hz⟩
  rw [hL] at this
  exact this

variable (T p) in
/-- `g` acts, on each piece of `⋁_{|δ|_T ≤ l} δP`, as a translation by an element of the
`l`-ball. -/
def LocalAt (l : ℕ) (g : S ≃ₜ S) : Prop :=
  ∀ y : S, ∃ γ ∈ wordBall (T : Set Γ) l, ∀ z : S, win T p l z = win T p l y → g z = γ +ᵥ z

lemma LocalAt.mono {l l' : ℕ} {g : S ≃ₜ S} (h : LocalAt T p l g) (hl : l ≤ l') :
    LocalAt T p l' g := by
  intro y
  obtain ⟨γ, hγ, h⟩ := h y
  exact ⟨γ, ball_mono T hl hγ, fun z hz => h z (win_mono hl hz)⟩

lemma exists_localAt [Finite A] (hT : AddSubgroup.closure (T : Set Γ) = ⊤)
    (hp : IsClopenPartition p) (hsep : IsSeparatingPartition Γ p)
    (g : S ≃ₜ S) (hg : g ∈ topologicalFullGroup Γ S) : ∃ l, LocalAt T p l g := by
  have := compactSpace_S (S := S)
  let O : ℕ → Set S := fun l => {y | ∃ γ ∈ wordBall (T : Set Γ) l, ∀ z : S,
    win T p l z = win T p l y → g z = γ +ᵥ z}
  have hO : ∀ l, IsOpen (O l) := by
    intro l
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    refine ⟨{z : S | win T p l z = win T p l y}, fun y' hy' => ?_, isOpen_cyl hp l y, rfl⟩
    obtain ⟨γ, hγ, h⟩ := hy
    exact ⟨γ, hγ, fun z hz => h z (hz.trans hy')⟩
  have hmono : ∀ l l', l ≤ l' → O l ⊆ O l' := by
    intro l l' hl y ⟨γ, hγ, h⟩
    exact ⟨γ, ball_mono T hl hγ, fun z hz => h z (win_mono hl hz)⟩
  have hcov : (Set.univ : Set S) ⊆ ⋃ l, O l := by
    intro y _
    obtain ⟨U, hU, γ, hγ⟩ := hg y
    obtain ⟨L, hL⟩ := exists_cyl_subset hT hp hsep y hU
    obtain ⟨n, hn⟩ := exists_mem_ball T hT γ
    refine Set.mem_iUnion.mpr ⟨max L n, γ, ball_mono T (le_max_right _ _) hn, fun z hz => ?_⟩
    exact hγ z (hL (win_mono (le_max_left _ _) hz))
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  refine ⟨F.sup id, fun y => ?_⟩
  have hy := hF (Set.mem_univ y)
  simp only [Set.mem_iUnion] at hy
  obtain ⟨l, hl, hyl⟩ := hy
  exact hmono l _ (Finset.le_sup (f := id) hl) hyl

/-- A point with trivial stabiliser. -/
def IsNP (x : S) : Prop := ∀ k : Γ, k +ᵥ x = x → k = 0

lemma IsNP.vadd_inj {x : S} (hx : IsNP x) {a b : Γ} (h : a +ᵥ x = b +ᵥ x) : a = b := by
  have : (-b + a) +ᵥ x = x := by rw [add_vadd, h, neg_vadd_vadd]
  have := hx _ this
  rw [← sub_eq_zero, sub_eq_neg_add]; exact this

lemma exists_pos (g : topologicalFullGroup Γ S) (x : S) (a : Γ) :
    ∃ q : Γ, (g : S ≃ₜ S) (a +ᵥ x) = q +ᵥ x := by
  obtain ⟨U, hU, γ, hγ⟩ := g.2 (a +ᵥ x)
  exact ⟨γ + a, by rw [hγ _ (mem_of_mem_nhds hU), add_vadd]⟩

/-- The orbit cocycle at `x`, as a map on positions: `g (a +ᵥ x) = pos x g a +ᵥ x`. -/
noncomputable def pos (x : S) (g : topologicalFullGroup Γ S) (a : Γ) : Γ :=
  Classical.choose (exists_pos g x a)

lemma pos_spec (x : S) (g : topologicalFullGroup Γ S) (a : Γ) :
    (g : S ≃ₜ S) (a +ᵥ x) = pos x g a +ᵥ x :=
  Classical.choose_spec (exists_pos g x a)

lemma pos_mul {x : S} (hx : IsNP x) (g h : topologicalFullGroup Γ S) (a : Γ) :
    pos x (g * h) a = pos x g (pos x h a) := by
  apply hx.vadd_inj
  rw [← pos_spec, ← pos_spec, Subgroup.coe_mul, Homeomorph.mul_apply, pos_spec]

lemma pos_one {x : S} (hx : IsNP x) (a : Γ) : pos x 1 a = a := by
  apply hx.vadd_inj
  rw [← pos_spec]
  rfl

lemma pos_inv_eq_iff {x : S} (hx : IsNP x) (g : topologicalFullGroup Γ S) (a b : Γ) :
    pos x g⁻¹ b = a ↔ pos x g a = b := by
  constructor
  · rintro rfl
    rw [← pos_mul hx, mul_inv_cancel, pos_one hx]
  · rintro rfl
    rw [← pos_mul hx, inv_mul_cancel, pos_one hx]

lemma pos_sub_mem {x : S} (hx : IsNP x) {l : ℕ} (g : topologicalFullGroup Γ S)
    (hg : LocalAt T p l (g : S ≃ₜ S)) (a : Γ) : pos x g a - a ∈ wordBall (T : Set Γ) l := by
  obtain ⟨γ, hγ, h⟩ := hg (a +ᵥ x)
  have h1 := h (a +ᵥ x) rfl
  rw [pos_spec, ← add_vadd] at h1
  rw [hx.vadd_inj h1]
  simpa using hγ

/-- Translating a piece: if `y` lies in the piece of depth `L` of `x₀` and `a` is in the `m`-ball
with `m + l ≤ L`, then `a +ᵥ y` lies in the piece of depth `l` of `a +ᵥ x₀`. -/
lemma win_vadd {L l m : ℕ} {y x₀ : S} (h : win T p L y = win T p L x₀) {a : Γ}
    (ha : a ∈ wordBall (T : Set Γ) m) (hml : m + l ≤ L) :
    win T p l (a +ᵥ y) = win T p l (a +ᵥ x₀) := by
  funext δ
  have hd : (δ : Γ) - a ∈ wordBall (T : Set Γ) L := by
    have := add_mem_ball T δ.2 (neg_mem_ball T ha)
    rw [← sub_eq_add_neg] at this
    exact ball_mono T (by omega) this
  have := congrFun h ⟨_, hd⟩
  simp only [win] at this ⊢
  rw [← add_vadd, ← add_vadd, show -(δ : Γ) + a = -((δ : Γ) - a) by abel]
  exact this

end Topology

/-! ## 6. The walk seen from a free point (MB Lemma 3.2, Remark 3.3, Corollary 3.5) -/

section Walk

open scoped Classical

variable {Γ A ι : Type*} [AddCommGroup Γ] [TopologicalSpace A] [DiscreteTopology A]
  {S : Subshift Γ A} {T : Finset Γ} {p : S → ι} (H : Height Γ T)
  (μ : topologicalFullGroup Γ S → ℝ) (F : Finset (topologicalFullGroup Γ S)) (x₀ : S)

/-- The Markov operator of the walk on positions along the orbit of `x₀`. -/
noncomputable def Pop (f : Γ → ℝ) : Γ → ℝ := fun a => ∑ s ∈ F, μ s * f (pos x₀ s a)

/-- Indicator of leaving the height window `[-M, M]`. -/
noncomputable def Iout (M : ℤ) : Γ → ℝ := fun b => if M < |H.h b| then 1 else 0

variable (T p) in
/-- `g` acts on the piece of depth `L` around `a +ᵥ x₀` as the translation that it applies to
`a +ᵥ x₀`, and the height of the new position is at most `B`. -/
def GoodB (L : ℕ) (B : ℤ) (g : topologicalFullGroup Γ S) (a : Γ) : Prop :=
  (∀ y : S, win T p L y = win T p L x₀ → (g : S ≃ₜ S) (a +ᵥ y) = pos x₀ g a +ᵥ y) ∧
    |H.h (pos x₀ g a)| ≤ B

variable (T p) in
/-- The probability that `μ^{*n}` is not good. -/
noncomputable def badE (L : ℕ) (B : ℤ) (n : ℕ) (a : Γ) : ℝ :=
  ∑' g, convPow μ n g * (if GoodB T p H x₀ L B g a then 0 else 1)

variable {μ F x₀}

lemma Pop_mono (hμ : IsProbability μ) {f f' : Γ → ℝ} (h : ∀ a, f a ≤ f' a) (a : Γ) :
    Pop μ F x₀ f a ≤ Pop μ F x₀ f' a :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h _) (hμ.1 s)

lemma Pop_nonneg (hμ : IsProbability μ) {f : Γ → ℝ} (h : ∀ a, 0 ≤ f a) (a : Γ) :
    0 ≤ Pop μ F x₀ f a :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hμ.1 s) (h _)

lemma Pop_sum (ι' : Finset ℕ) (f : ℕ → Γ → ℝ) (a : Γ) :
    Pop μ F x₀ (fun b => ∑ j ∈ ι', f j b) a = ∑ j ∈ ι', Pop μ F x₀ (f j) a := by
  unfold Pop
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- MB Lemma 3.2, one step: the piece of depth `L` is carried along by a generator as long as
the current position stays in the height window. -/
lemma goodB_mul (hx : IsNP x₀) {l L : ℕ} {B : ℤ} {s g : topologicalFullGroup Γ S}
    (hs : LocalAt T p l (s : S ≃ₜ S)) {a : Γ} {m : ℕ} (ha : a ∈ wordBall (T : Set Γ) m)
    (hml : m + l ≤ L)
    (hh : GoodB T p H x₀ L B g (pos x₀ s a)) : GoodB T p H x₀ L B (g * s) a := by
  obtain ⟨γ, -, hγ⟩ := hs (a +ᵥ x₀)
  have hpos : pos x₀ s a = γ + a := by
    apply hx.vadd_inj
    rw [← pos_spec, hγ _ rfl, add_vadd]
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [Subgroup.coe_mul, Homeomorph.mul_apply, hγ _ (win_vadd hy ha hml), ← add_vadd, ← hpos,
      hh.1 y hy, pos_mul hx]
  · rw [pos_mul hx]; exact hh.2

lemma badE_nonneg (hμ : IsProbability μ) (L : ℕ) (B : ℤ) (n : ℕ) (a : Γ) :
    0 ≤ badE T p H μ x₀ L B n a :=
  tsum_nonneg fun g => mul_nonneg ((isProb_convPow hμ n).1 g) (by split_ifs <;> norm_num)

lemma badE_le_one (hμ : IsProbability μ) (L : ℕ) (B : ℤ) (n : ℕ) (a : Γ) :
    badE T p H μ x₀ L B n a ≤ 1 := by
  have hp := isProb_convPow hμ n
  calc badE T p H μ x₀ L B n a ≤ ∑' g, convPow μ n g :=
        Summable.tsum_le_tsum (fun g => mul_le_of_le_one_right (hp.1 g)
          (by split_ifs <;> norm_num))
          (Summable.of_nonneg_of_le (fun g => mul_nonneg (hp.1 g) (by split_ifs <;> norm_num))
            (fun g => mul_le_of_le_one_right (hp.1 g) (by split_ifs <;> norm_num)) hp.2.summable)
          hp.2.summable
    _ = 1 := hp.2.tsum_eq

lemma badE_succ_le (hμ : IsProbability μ) (hF : ∀ s, μ s ≠ 0 → s ∈ F) (hx : IsNP x₀) {l L : ℕ}
    (hloc : ∀ s ∈ F, LocalAt T p l (s : S ≃ₜ S)) {M : ℤ}
    (hin : ∀ a : Γ, |H.h a| ≤ M → ∃ m : ℕ, a ∈ wordBall (T : Set Γ) m ∧ m + l ≤ L)
    (B : ℤ) (n : ℕ) (a : Γ) :
    badE T p H μ x₀ L B (n + 1) a ≤ Iout H M a + Pop μ F x₀ (badE T p H μ x₀ L B n) a := by
  by_cases ha : M < |H.h a|
  · have : Iout H M a = 1 := by unfold Iout; rw [if_pos ha]
    rw [this]
    have := Pop_nonneg (F := F) (x₀ := x₀) hμ (badE_nonneg H (p := p) (x₀ := x₀) hμ L B n) a
    linarith [badE_le_one H (p := p) (x₀ := x₀) hμ L B (n + 1) a]
  · have h0 : Iout H M a = 0 := by unfold Iout; rw [if_neg ha]
    rw [h0, zero_add]
    obtain ⟨m, ham, hml⟩ := hin a (not_lt.mp ha)
    have hp := isProb_convPow hμ n
    unfold badE
    show ∑' g, conv (convPow μ n) μ g * _ ≤ _
    rw [tsum_conv_mul hp hμ _ (fun g => by split_ifs <;> norm_num)
      (fun g => by split_ifs <;> norm_num)]
    rw [tsum_eq_sum (s := F) (fun s hs => by
      have : μ s = 0 := by by_contra h; exact hs (hF s h)
      rw [this, zero_mul])]
    refine Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left ?_ (hμ.1 s)
    have hsum : ∀ (P : topologicalFullGroup Γ S → Prop) [DecidablePred P],
        Summable fun h => convPow μ n h * (if P h then (0 : ℝ) else 1) := fun P _ =>
      Summable.of_nonneg_of_le (fun g => mul_nonneg (hp.1 g) (by split_ifs <;> norm_num))
        (fun g => mul_le_of_le_one_right (hp.1 g) (by split_ifs <;> norm_num)) hp.2.summable
    refine Summable.tsum_le_tsum (fun h => mul_le_mul_of_nonneg_left ?_ (hp.1 h))
      (hsum (fun h => GoodB T p H x₀ L B (h * s) a))
      (hsum (fun h => GoodB T p H x₀ L B h (pos x₀ s a)))
    by_cases hg : GoodB T p H x₀ L B h (pos x₀ s a)
    · rw [if_pos (goodB_mul H hx (hloc s hs) ham hml hg), if_pos hg]
    · rw [if_neg hg]; split_ifs <;> norm_num

lemma badE_zero_le (hμ : IsProbability μ) (hx : IsNP x₀) (L : ℕ) {M B : ℤ}
    (hB : M ≤ B) (a : Γ) :
    badE T p H μ x₀ L B 0 a ≤ Iout H M a := by
  by_cases ha : M < |H.h a|
  · have : Iout H M a = 1 := by unfold Iout; rw [if_pos ha]
    rw [this]; exact badE_le_one H (p := p) hμ L B 0 a
  · have h0 : Iout H M a = 0 := by unfold Iout; rw [if_neg ha]
    rw [h0]
    have hg : GoodB T p H x₀ L B 1 a := by
      refine ⟨fun y _ => ?_, ?_⟩
      · rw [pos_one hx]; rfl
      · rw [pos_one hx]; push Not at ha; linarith
    unfold badE
    rw [tsum_eq_single 1]
    · rw [if_pos hg, mul_zero]
    · intro g hg1
      simp [convPow, hg1]

lemma badE_le_sum (hμ : IsProbability μ) (hF : ∀ s, μ s ≠ 0 → s ∈ F) (hx : IsNP x₀)
    {l L : ℕ} (hloc : ∀ s ∈ F, LocalAt T p l (s : S ≃ₜ S)) {M : ℤ}
    (hin : ∀ a : Γ, |H.h a| ≤ M → ∃ m : ℕ, a ∈ wordBall (T : Set Γ) m ∧ m + l ≤ L)
    (n : ℕ) : ∀ a, badE T p H μ x₀ L M n a ≤
      ∑ j ∈ range (n + 1), (Pop μ F x₀)^[j] (Iout H M) a := by
  induction n with
  | zero => intro a; simpa using badE_zero_le H hμ hx L le_rfl a
  | succ n ih =>
    intro a
    refine (badE_succ_le H hμ hF hx hloc hin M n a).trans ?_
    rw [Finset.sum_range_succ' _ (n + 1)]
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
    rw [add_comm]
    refine add_le_add_left ?_ _
    rw [← Pop_sum]
    exact Pop_mono hμ ih a

/-- The positions of height at most `R`. -/
abbrev Box (R : ℤ) := ↥(H.box R)

variable (μ F x₀) in
/-- The transition matrix of the walk on positions, restricted to heights in `[-R, R]`. -/
noncomputable def Qm (R : ℤ) : Matrix (Box H R) (Box H R) ℝ :=
  fun a b => ∑ s ∈ F, μ s * if pos x₀ s a.1 = b.1 then 1 else 0

lemma sum_Qm_mul {R : ℤ} (a : Box H R) (hin : ∀ s ∈ F, |H.h (pos x₀ s a.1)| ≤ R)
    (G : Γ → ℝ) : ∑ c, Qm H μ F x₀ R a c * G c.1 = ∑ s ∈ F, μ s * G (pos x₀ s a.1) := by
  unfold Qm
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hmem : pos x₀ s a.1 ∈ H.box R := (H.mem_box _ _).mpr (hin s hs)
  rw [Finset.sum_eq_single ⟨pos x₀ s a.1, hmem⟩]
  · simp
  · intro c _ hc
    have : pos x₀ s a.1 ≠ c.1 := fun h => hc (Subtype.ext h.symm)
    simp [this]
  · simp

lemma Qm_ne_zero {R : ℤ} {K : ℕ} (hstep : ∀ s ∈ F, ∀ a, |H.h (pos x₀ s a) - H.h a| ≤ K)
    (a c : Box H R) (h : Qm H μ F x₀ R a c ≠ 0) : |H.h a.1 - H.h c.1| ≤ K := by
  obtain ⟨s, hs, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h2 : pos x₀ s a.1 = c.1 := by
    by_contra h3; apply h1; simp [h3]
  have := hstep s hs a.1
  rw [h2] at this
  rw [abs_sub_comm]; exact this

lemma iterate_Pop_eq {K : ℕ} (hstep : ∀ s ∈ F, ∀ a, |H.h (pos x₀ s a) - H.h a| ≤ K)
    (R : ℤ) (j : ℕ) : ∀ (f : Γ → ℝ) (a : Box H R), |H.h a.1| + K * j ≤ R →
      (Pop μ F x₀)^[j] f a.1 = ∑ b, (Qm H μ F x₀ R ^ j) a b * f b.1 := by
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
    have hin : ∀ s ∈ F, |H.h (pos x₀ s a.1)| ≤ R := by
      intro s hs
      have := hstep s hs a.1
      have h2 : |H.h (pos x₀ s a.1)| ≤ |H.h a.1| + K := by
        calc |H.h (pos x₀ s a.1)| = |(H.h (pos x₀ s a.1) - H.h a.1) + H.h a.1| := by ring_nf
          _ ≤ |H.h (pos x₀ s a.1) - H.h a.1| + |H.h a.1| := abs_add_le _ _
          _ ≤ K + |H.h a.1| := by linarith
          _ = |H.h a.1| + K := add_comm _ _
      push_cast at ha
      nlinarith [Int.natCast_nonneg K, Int.natCast_nonneg j]
    show (∑ s ∈ F, μ s * ((Pop μ F x₀)^[j] f) (pos x₀ s a.1)) = _
    rw [← sum_Qm_mul H a hin ((Pop μ F x₀)^[j] f)]
    rw [pow_succ']
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : Qm H μ F x₀ R a c = 0
    · simp [hc]
    · have hd := Qm_ne_zero H hstep a c hc
      have hc' : |H.h c.1| + K * j ≤ R := by
        have : |H.h c.1| ≤ |H.h a.1| + K := by
          calc |H.h c.1| = |H.h a.1 - (H.h a.1 - H.h c.1)| := by ring_nf
            _ ≤ |H.h a.1| + |H.h a.1 - H.h c.1| := abs_sub _ _
            _ ≤ |H.h a.1| + K := by linarith
        push_cast at ha
        linarith
      rw [ih f c hc', Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => by ring

lemma Qm_symm (hsymm : IsSymmetric μ) (hFinv : ∀ s ∈ F, s⁻¹ ∈ F) (hx : IsNP x₀) (R : ℤ) :
    (Qm H μ F x₀ R)ᵀ = Qm H μ F x₀ R := by
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

lemma Qm_nonneg (hμ : IsProbability μ) (R : ℤ) (a b : Box H R) : 0 ≤ Qm H μ F x₀ R a b :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hμ.1 s) (by split_ifs <;> norm_num)

lemma Qm_row (hμ : IsProbability μ) (R : ℤ) (a : Box H R) : ∑ b, Qm H μ F x₀ R a b ≤ 1 := by
  unfold Qm
  rw [Finset.sum_comm]
  calc ∑ s ∈ F, ∑ b : Box H R, μ s * (if pos x₀ s a.1 = b.1 then 1 else 0)
      ≤ ∑ s ∈ F, μ s := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_of_le_one_right (hμ.1 s) ?_
        by_cases hp : pos x₀ s a.1 ∈ H.box R
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
`μ^{*n}` does not act on the piece of depth `L` around `x₀` as a single translation of height at
most `M`. -/
theorem badE_bound (hμ : IsProbability μ) (hsymm : IsSymmetric μ)
    (hF : ∀ s, μ s ≠ 0 → s ∈ F) (hFinv : ∀ s ∈ F, s⁻¹ ∈ F) (hx : IsNP x₀) {K : ℕ} (hK : 1 ≤ K)
    (hstep : ∀ s ∈ F, ∀ a, |H.h (pos x₀ s a) - H.h a| ≤ K) {l L M : ℕ}
    (hloc : ∀ s ∈ F, LocalAt T p l (s : S ≃ₜ S))
    (hin : ∀ a : Γ, |H.h a| ≤ M → ∃ m : ℕ, a ∈ wordBall (T : Set Γ) m ∧ m + l ≤ L)
    (n : ℕ) (hn : 1 ≤ n) :
    badE T p H μ x₀ L M n 0 ≤ (n + 1) * ((H.box (M + K * n)).card : ℝ) *
      (2 * Real.exp (-(((M : ℝ) / K) ^ 2) / (2 * n))) := by
  set R : ℤ := M + K * n with hR
  have h1 := badE_le_sum H hμ hF hx hloc hin n 0
  refine h1.trans ?_
  have h0 : (0 : Γ) ∈ H.box R := (H.mem_box _ _).mpr (by rw [H.h_zero, abs_zero, hR]; positivity)
  set E : ℝ := 2 * Real.exp (-(((M : ℝ) / K) ^ 2) / (2 * n)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hcard : (Fintype.card (Box H R) : ℝ) = ((H.box (M + K * n)).card : ℝ) := by
    rw [Fintype.card_coe]
  rw [← hcard]
  have hterm : ∀ j ∈ range (n + 1),
      (Pop μ F x₀)^[j] (Iout H M) 0 ≤ Fintype.card (Box H R) * E := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have := iterate_Pop_eq H (μ := μ) hstep R j (Iout H M) ⟨0, h0⟩ (by
      simp only [H.h_zero, abs_zero, zero_add, hR]
      have : (K : ℤ) * j ≤ K * n := by exact_mod_cast Nat.mul_le_mul_left K hj'
      linarith [Int.natCast_nonneg M])
    simp only at this
    rw [this]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp only [pow_zero, Matrix.one_apply]
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · simp only [if_true, one_mul]
        unfold Iout
        rw [if_neg (by simp [H.h_zero])]
        positivity
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · rw [show (Fintype.card (Box H R) : ℝ) * E = ∑ _b : Box H R, E by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun b _ => ?_
      unfold Iout
      split_ifs with hb
      · rw [mul_one]
        have hcv := carne_varopoulos (Qm H μ F x₀ R) (Qm_symm H hsymm hFinv hx R)
          (Qm_nonneg H hμ R) (Qm_row H hμ R) (fun c => H.h c.1) K (by omega)
          (fun a c h => Qm_ne_zero H hstep a c h) j hjpos ⟨0, h0⟩ b
        refine hcv.trans ?_
        rw [hE]
        gcongr ?_ * Real.exp ?_
        have hKr : (0 : ℝ) < K := by exact_mod_cast hK
        have hjr : (0 : ℝ) < j := by exact_mod_cast hjpos
        have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj'
        have hbM : (M : ℝ) ≤ |((H.h b.1 : ℤ) : ℝ)| := by
          have : (M : ℤ) ≤ |H.h b.1| := hb.le
          rw [← Int.cast_abs]; exact_mod_cast this
        simp only [H.h_zero, zero_sub, abs_neg]
        push_cast
        rw [neg_div, neg_div, neg_le_neg_iff]
        have hsq : ((M : ℝ) / K) ^ 2 ≤ (|((H.h b.1 : ℤ) : ℝ)| / K) ^ 2 := by
          gcongr
        calc ((M : ℝ) / K) ^ 2 / (2 * n) ≤ (|((H.h b.1 : ℤ) : ℝ)| / K) ^ 2 / (2 * n) := by
              gcongr
          _ ≤ (|((H.h b.1 : ℤ) : ℝ)| / K) ^ 2 / (2 * j) := by gcongr
      · rw [mul_zero]; exact hE0
  calc ∑ j ∈ range (n + 1), (Pop μ F x₀)^[j] (Iout H M) 0
      ≤ ∑ j ∈ range (n + 1), (Fintype.card (Box H R) : ℝ) * E := Finset.sum_le_sum hterm
    _ = (n + 1) * Fintype.card (Box H R) * E := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end Walk

/-! ## 7. Pieces, counting and the entropy bound at a given depth (MB Def. 3.6, Lemmas 3.7,
3.8, Fact A.4) -/

section Assembly

open scoped Classical

variable {Γ A ι : Type*} [AddCommGroup Γ] [TopologicalSpace A] [DiscreteTopology A]
  {S : Subshift Γ A} {T : Finset Γ} {p : S → ι} (H : Height Γ T)

variable (T p) in
/-- `g` acts on every piece of `⋁_{|δ|_T ≤ L} δP` as a single translation of height at most
`B`. -/
def GoodG (L : ℕ) (B : ℤ) (g : topologicalFullGroup Γ S) : Prop :=
  ∃ c : (wordBall (T : Set Γ) L → ι) → Γ, (∀ w, c w ∈ H.box B) ∧
    ∀ y : S, (g : S ≃ₜ S) y = c (win T p L y) +ᵥ y

variable (T p) in
/-- `g` acts on the piece named `w` as a single translation of height at most `B`. -/
def GoodW (L : ℕ) (B : ℤ) (w : wordBall (T : Set Γ) L → ι) (g : topologicalFullGroup Γ S) :
    Prop :=
  ∃ k ∈ H.box B, ∀ y : S, win T p L y = w → (g : S ≃ₜ S) y = k +ᵥ y

lemma exists_np_of_word (hp : IsClopenPartition p)
    (hS : Dense {x : S | ∀ γ : Γ, γ +ᵥ x = x → γ = 0}) (L : ℕ) (z : S) :
    ∃ x₀ : S, IsNP x₀ ∧ win T p L x₀ = win T p L z := by
  obtain ⟨x₀, hx₀C, hx₀⟩ := hS.inter_open_nonempty {y : S | win T p L y = win T p L z}
    (isOpen_cyl hp L z) ⟨z, rfl⟩
  exact ⟨x₀, hx₀, hx₀C⟩

lemma goodW_of_goodB {L : ℕ} {B : ℤ} {x₀ : S} {g : topologicalFullGroup Γ S}
    (h : GoodB T p H x₀ L B g 0) : GoodW T p H L B (win T p L x₀) g := by
  refine ⟨pos x₀ g 0, (H.mem_box _ _).mpr h.2, fun y hy => ?_⟩
  have := h.1 y hy
  rwa [zero_vadd] at this

lemma goodG_of_forall {L : ℕ} {B : ℤ} (hB : 0 ≤ B) {g : topologicalFullGroup Γ S}
    (h : ∀ z : S, GoodW T p H L B (win T p L z) g) : GoodG T p H L B g := by
  have h0 : (0 : Γ) ∈ H.box B := (H.mem_box _ _).mpr (by rw [H.h_zero, abs_zero]; exact hB)
  refine ⟨fun w => if hw : ∃ z, win T p L z = w then Classical.choose (h (Classical.choose hw))
    else 0, fun w => ?_, fun y => ?_⟩
  · dsimp only
    split_ifs with hw
    · exact (Classical.choose_spec (h (Classical.choose hw))).1
    · exact h0
  · have hw : ∃ z, win T p L z = win T p L y := ⟨y, rfl⟩
    dsimp only
    rw [dif_pos hw]
    exact (Classical.choose_spec (h (Classical.choose hw))).2 y (Classical.choose_spec hw).symm

lemma card_goodG_le [Finite ι] (L : ℕ) (B : ℤ) (Tg : Finset (topologicalFullGroup Γ S)) :
    (Tg.filter (GoodG T p H L B)).card ≤
      (H.box B).card ^ Nat.card (Set.range (win T p L)) := by
  have : Finite (wordBall (T : Set Γ) L) := (ball_finite T L).to_subtype
  let Φ : (Tg.filter (GoodG T p H L B)) → (Set.range (win T p L) → H.box B) := fun g w =>
    ⟨Classical.choose (Finset.mem_filter.mp g.2).2 w,
      (Classical.choose_spec (Finset.mem_filter.mp g.2).2).1 w⟩
  have hinj : Function.Injective Φ := by
    intro g g' he
    apply Subtype.ext
    apply Subtype.ext
    ext y
    have h1 := (Classical.choose_spec (Finset.mem_filter.mp g.2).2).2 y
    have h2 := (Classical.choose_spec (Finset.mem_filter.mp g'.2).2).2 y
    have h3 := congrArg Subtype.val (congrFun he ⟨win T p L y, y, rfl⟩)
    simp only [Φ] at h3
    rw [h1, h2, h3]
  have := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card,
    Fintype.card_coe] at this
  exact this

/-- The entropy bound at depth `L` (MB (8), (9) and Fact A.4). -/
theorem entropy_le_depth [Finite ι] [Nonempty S] (hp : IsClopenPartition p)
    (hS : Dense {x : S | ∀ γ : Γ, γ +ᵥ x = x → γ = 0})
    {μ : topologicalFullGroup Γ S → ℝ} (hμ : IsProbability μ) (hsymm : IsSymmetric μ)
    {F : Finset (topologicalFullGroup Γ S)} (hF : ∀ s, μ s ≠ 0 → s ∈ F)
    (hFinv : ∀ s ∈ F, s⁻¹ ∈ F) {K : ℕ} (hK : 1 ≤ K)
    (hstep : ∀ x₀ : S, IsNP x₀ → ∀ s ∈ F, ∀ a, |H.h (pos x₀ s a) - H.h a| ≤ K) {l L M : ℕ}
    (hloc : ∀ s ∈ F, LocalAt T p l (s : S ≃ₜ S))
    (hin : ∀ a : Γ, |H.h a| ≤ M → ∃ m : ℕ, a ∈ wordBall (T : Set Γ) m ∧ m + l ≤ L)
    (n : ℕ) (hn : 1 ≤ n) :
    entropy (convPow μ n) ≤
      (complexity (T : Set Γ) p L : ℝ) * Real.log (H.box M).card +
      (complexity (T : Set Γ) p L : ℝ) * ((n + 1) * ((H.box (M + K * n)).card : ℝ) *
        (2 * Real.exp (-(((M : ℝ) / K) ^ 2) / (2 * n)))) * (n * Real.log F.card) +
      Real.log 2 := by
  set ρ := complexity (T : Set Γ) p L with hρ
  set E := (n + 1) * ((H.box (M + K * n)).card : ℝ) *
        (2 * Real.exp (-(((M : ℝ) / K) ^ 2) / (2 * n))) with hE
  have hE0 : 0 ≤ E := by positivity
  have hp' := isProb_convPow hμ n
  have hFsupp : Function.support μ ⊆ (F : Set _) := fun s hs => hF s hs
  obtain ⟨Tg, hTc, hTs⟩ := convPow_support μ F hFsupp n
  have hsplit := entropy_le_split hp' Tg hTs (GoodG T p H L M)
  have h0M : (0 : Γ) ∈ H.box M := (H.mem_box _ _).mpr (by rw [H.h_zero, abs_zero]; positivity)
  have hbox1 : 1 ≤ (H.box M).card := Finset.card_pos.mpr ⟨0, h0M⟩
  -- the good part
  have h1 : Real.log (Tg.filter (GoodG T p H L M)).card ≤ ρ * Real.log (H.box M).card := by
    have hc := card_goodG_le H (p := p) L M Tg
    rw [← complexity_eq] at hc
    rcases Nat.eq_zero_or_pos (Tg.filter (GoodG T p H L M)).card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    · calc Real.log (Tg.filter (GoodG T p H L M)).card
            ≤ Real.log ((((H.box M).card) ^ ρ : ℕ) : ℝ) :=
            Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hc)
        _ = ρ * Real.log (H.box M).card := by push_cast; rw [Real.log_pow]
  -- the support
  have h2 : Real.log Tg.card ≤ n * Real.log F.card := by
    rcases Nat.eq_zero_or_pos Tg.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    · calc Real.log Tg.card ≤ Real.log ((F.card ^ n : ℕ) : ℝ) :=
            Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hTc)
        _ = n * Real.log F.card := by push_cast; rw [Real.log_pow]
  -- the bad part
  have : Finite (wordBall (T : Set Γ) L) := (ball_finite T L).to_subtype
  have hW : (Set.range (win T p L)).Finite := Set.toFinite _
  have hWc : hW.toFinset.card = ρ := by
    rw [hρ, complexity_eq, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hW]
  have hex : ∀ w ∈ Set.range (win T p L), ∃ x₀ : S, IsNP x₀ ∧ win T p L x₀ = w := by
    rintro _ ⟨z, rfl⟩
    exact exists_np_of_word hp hS L z
  choose! xw hxw using hex
  have h3 : ∑ g ∈ Tg, convPow μ n g * (if GoodG T p H L M g then 0 else 1) ≤ ρ * E := by
    calc ∑ g ∈ Tg, convPow μ n g * (if GoodG T p H L M g then 0 else 1)
        ≤ ∑ g ∈ Tg, convPow μ n g * ∑ w ∈ hW.toFinset,
            (if GoodB T p H (xw w) L M g 0 then 0 else 1) := by
          refine Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left ?_ (hp'.1 g)
          by_cases hg : GoodG T p H L M g
          · rw [if_pos hg]
            exact Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num
          · rw [if_neg hg]
            have : ∃ z : S, ¬ GoodW T p H L M (win T p L z) g := by
              by_contra hcon; push Not at hcon
              exact hg (goodG_of_forall H (by positivity) hcon)
            obtain ⟨z, hgw⟩ := this
            have hw : win T p L z ∈ Set.range (win T p L) := ⟨z, rfl⟩
            have hb : ¬ GoodB T p H (xw (win T p L z)) L M g 0 := fun h => hgw (by
              have := goodW_of_goodB H h
              rwa [(hxw _ hw).2] at this)
            calc (1 : ℝ) = if GoodB T p H (xw (win T p L z)) L M g 0 then 0 else 1 := by
                  rw [if_neg hb]
              _ ≤ _ := Finset.single_le_sum (f := fun w => if GoodB T p H (xw w) L M g 0
                  then (0 : ℝ) else 1) (fun w _ => by split_ifs <;> norm_num)
                  (hW.mem_toFinset.mpr hw)
      _ = ∑ w ∈ hW.toFinset, badE T p H μ (xw w) L M n 0 := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => ?_
          unfold badE
          rw [tsum_eq_sum (s := Tg)]
          intro g hg
          have : convPow μ n g = 0 := by by_contra h; exact hg (hTs h)
          rw [this, zero_mul]
      _ ≤ ∑ w ∈ hW.toFinset, E := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hx := (hxw w (hW.mem_toFinset.mp hw)).1
          exact badE_bound H hμ hsymm hF hFinv hx hK (hstep _ hx) hloc hin n hn
      _ = ρ * E := by rw [Finset.sum_const, hWc, nsmul_eq_mul]
  have h3' : (∑ g ∈ Tg, convPow μ n g * (if GoodG T p H L M g then 0 else 1)) *
      Real.log Tg.card ≤ (ρ * E) * (n * Real.log F.card) :=
    mul_le_mul h3 h2 (Real.log_natCast_nonneg _) (by positivity)
  linarith

end Assembly

/-! ## 8. Asymptotics -/

section Asymptotics

lemma term1_le {α C β x Mr D kr : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hD : 0 ≤ D) (hβ : 0 < β)
    (hx : 3 ≤ x) (hlog : 1 ≤ Real.log x) (hM1 : 1 ≤ Mr)
    (hMs : Mr ≤ 2 * Real.sqrt (β * x * Real.log x)) (hMx : Mr ≤ x) (hk : 1 ≤ kr) :
    C * (D * Mr) ^ α * Real.log (kr * (2 * Mr + 1)) ≤
      C * (2 * D) ^ α * β ^ (α / 2) * (Real.log kr + 2) * x ^ (α / 2) *
        Real.log x ^ (1 + α / 2) := by
  set X := β * x * Real.log x with hX
  set s := Real.sqrt X with hs_def
  have hx0 : 0 < x := by linarith
  have hX0 : 0 ≤ X := by positivity
  have hDM : 0 ≤ D * Mr := mul_nonneg hD (by linarith)
  have h2 : (D * Mr) ^ α ≤ (2 * D * s) ^ α := by
    refine Real.rpow_le_rpow hDM ?_ hα
    have := mul_le_mul_of_nonneg_left hMs hD
    linarith
  have h3 : (2 * D * s) ^ α = (2 * D) ^ α * β ^ (α / 2) * x ^ (α / 2) * Real.log x ^ (α / 2) := by
    have e1 : (2 * D * s) ^ α = (2 * D) ^ α * s ^ α :=
      Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)
    have e2 : s ^ α = β ^ (α / 2) * x ^ (α / 2) * Real.log x ^ (α / 2) := by
      rw [hs_def, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0, hX,
        Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hβ.le hx0.le]
      rw [show 1 / 2 * α = α / 2 by ring]
    rw [e1, e2]; ring
  have h4 : Real.log (kr * (2 * Mr + 1)) ≤ (Real.log kr + 2) * Real.log x := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have : 2 * Mr + 1 ≤ x ^ 2 := by nlinarith
    have h5 : Real.log (2 * Mr + 1) ≤ 2 * Real.log x := by
      calc Real.log (2 * Mr + 1) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) this
        _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
    have hk0 : 0 ≤ Real.log kr := Real.log_nonneg hk
    nlinarith
  have h5 : Real.log x ^ (1 + α / 2) = Real.log x * Real.log x ^ (α / 2) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hlog2 : 0 ≤ Real.log (kr * (2 * Mr + 1)) := Real.log_nonneg (by nlinarith)
  calc C * (D * Mr) ^ α * Real.log (kr * (2 * Mr + 1))
      ≤ C * (2 * D * s) ^ α * ((Real.log kr + 2) * Real.log x) := by gcongr
    _ = _ := by rw [h3, h5]; ring

lemma term2_le {C D kr K x ρ cb e lF : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (_hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ C * D ^ 2 * x ^ 2) (hcb0 : 0 ≤ cb) (hcb : cb ≤ kr * (3 + 2 * K) * x)
    (hk0 : 0 ≤ kr) (hK0 : 0 ≤ K) (he0 : 0 ≤ e) (he : e ≤ (x ^ 6)⁻¹) (hF : 0 ≤ lF) :
    ρ * ((x + 1) * cb * (2 * e)) * (x * lF) ≤ 4 * C * D ^ 2 * kr * (3 + 2 * K) * lF := by
  have hx0 : 0 < x := by linarith
  calc ρ * ((x + 1) * cb * (2 * e)) * (x * lF)
      ≤ (C * D ^ 2 * x ^ 2) * ((2 * x) * (kr * (3 + 2 * K) * x) * (2 * (x ^ 6)⁻¹)) *
          (x * lF) := by
        gcongr; linarith
    _ = 4 * C * D ^ 2 * kr * (3 + 2 * K) * lF * x⁻¹ := by field_simp; ring
    _ ≤ 4 * C * D ^ 2 * kr * (3 + 2 * K) * lF * 1 := by
        gcongr
        exact inv_le_one_of_one_le₀ hx
    _ = _ := mul_one _

lemma exp_tail_le {Mr K x : ℝ} (hK : 0 < K) (hx : 1 ≤ x)
    (h : 12 * K ^ 2 * x * Real.log x ≤ Mr ^ 2) :
    Real.exp (-((Mr / K) ^ 2) / (2 * x)) ≤ (x ^ 6)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have h1 : 12 * x * Real.log x ≤ (Mr / K) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]; nlinarith
  have h2 : 6 * Real.log x ≤ (Mr / K) ^ 2 / (2 * x) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  calc Real.exp (-((Mr / K) ^ 2) / (2 * x)) ≤ Real.exp (-(6 * Real.log x)) := by
        rw [neg_div]; exact Real.exp_le_exp.mpr (by linarith)
    _ = (x ^ 6)⁻¹ := by
        rw [Real.exp_neg, show (6 : ℝ) * Real.log x = ((6 : ℕ) : ℝ) * Real.log x by norm_num,
          Real.exp_nat_mul, Real.exp_log hx0]

end Asymptotics

/-! ## 9. Proof of the theorem -/

section Final

variable {Γ A ι : Type*} [AddCommGroup Γ] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  {S : Subshift Γ A} {T : Finset Γ} [Finite ι] {p : S → ι}

lemma one_le_complexity [Nonempty S] (n : ℕ) : 1 ≤ complexity (T : Set Γ) p n := by
  have : Finite (wordBall (T : Set Γ) n) := (ball_finite T n).to_subtype
  rw [complexity_eq]
  obtain ⟨y⟩ := ‹Nonempty S›
  have : Nonempty (Set.range (win T p n)) := ⟨⟨_, y, rfl⟩⟩
  exact Nat.card_pos

lemma alpha_nonneg [Nonempty S] {α C : ℝ}
    (hρ : ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Γ) p n : ℝ) ≤ C * (n : ℝ) ^ α) :
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
  have h3 : (1 : ℝ) ≤ complexity (T : Set Γ) p (max N 1) := by
    exact_mod_cast one_le_complexity _
  linarith

lemma C_ge_one [Nonempty S] {α C : ℝ}
    (hρ : ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Γ) p n : ℝ) ≤ C * (n : ℝ) ^ α) :
    1 ≤ C := by
  have h1 := hρ 1 le_rfl
  have h3 : (1 : ℝ) ≤ complexity (T : Set Γ) p 1 := by
    exact_mod_cast one_le_complexity _
  simp at h1
  linarith

set_option maxHeartbeats 1000000 in
/-- The entropy bound for all large `n`. -/
theorem entropy_eventually_le [Nonempty S] (hT : AddSubgroup.closure (T : Set Γ) = ⊤)
    (hp : IsClopenPartition p) (hsep : IsSeparatingPartition Γ p) (H : Height Γ T)
    (hS : Dense {x : S | ∀ γ : Γ, γ +ᵥ x = x → γ = 0})
    {α C : ℝ} (hα : α < 2)
    (hρ : ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Γ) p n : ℝ) ≤ C * (n : ℝ) ^ α)
    (μ : topologicalFullGroup Γ S → ℝ) (hfin : (Function.support μ).Finite)
    (hμ : IsProbability μ) (hsymm : IsSymmetric μ) :
    ∃ K' : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      entropy (convPow μ n) ≤ K' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
  classical
  have hα0 := alpha_nonneg hρ
  have hC1 := C_ge_one hρ
  set F := hfin.toFinset with hF_def
  have hF : ∀ s, μ s ≠ 0 → s ∈ F := fun s hs => hfin.mem_toFinset.mpr hs
  have hFinv : ∀ s ∈ F, s⁻¹ ∈ F := fun s hs => by
    rw [hfin.mem_toFinset] at hs ⊢
    rw [Function.mem_support, hsymm]; exact hs
  have hex : ∀ s : topologicalFullGroup Γ S, ∃ l, LocalAt T p l (s : S ≃ₜ S) :=
    fun s => exists_localAt hT hp hsep (s : S ≃ₜ S) s.2
  choose lf hlf using hex
  set l := max 1 (F.sup lf) with hl_def
  have hl : 1 ≤ l := le_max_left _ _
  have hloc : ∀ s ∈ F, LocalAt T p l (s : S ≃ₜ S) := fun s hs =>
    (hlf s).mono ((Finset.le_sup hs).trans (le_max_right _ _))
  set K : ℕ := max 1 (H.c₀ * l) with hK_def
  have hK : 1 ≤ K := le_max_left _ _
  have hcK : H.c₀ * l ≤ K := le_max_right _ _
  have hstep : ∀ x₀ : S, IsNP x₀ → ∀ s ∈ F, ∀ a, |H.h (pos x₀ s a) - H.h a| ≤ K := by
    intro x₀ hx s hs a
    have hmem := pos_sub_mem hx s (hloc s hs) a
    have := H.lip l a _ hmem
    rw [show a + (pos x₀ s a - a) = pos x₀ s a by abel] at this
    refine this.trans ?_
    exact_mod_cast hcK
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set β : ℝ := 48 * (K : ℝ) ^ 2 with hβ
  have hβ0 : 0 < β := by positivity
  -- `k ≥ 1`
  have hk1 : (1 : ℝ) ≤ H.k := by
    have h0 : (0 : Γ) ∈ H.box 0 := (H.mem_box _ _).mpr (by simp [H.h_zero])
    have h1 : (1 : ℝ) ≤ (H.box 0).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
    have := H.card_box 0
    simp only [Nat.cast_zero, mul_zero, zero_add, mul_one] at this
    linarith
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
  set D : ℕ := H.c₁ + H.c₂ + l with hD_def
  set kr : ℝ := (H.k : ℝ) with hkr
  refine ⟨C * (2 * D) ^ α * β ^ (α / 2) * (Real.log kr + 2) +
    4 * C * (D : ℝ) ^ 2 * kr * (3 + 2 * K) * lF + Real.log 2, max 3 N₁, fun n hn => ?_⟩
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
  set M := ⌈s⌉₊ with hM_def
  have hsM : s ≤ M := Nat.le_ceil s
  have hMs : (M : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0
  have hM2 : X ≤ (M : ℝ) ^ 2 := by nlinarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hMpos : 1 ≤ M := by exact_mod_cast hM1
  have hMs2 : (M : ℝ) ≤ 2 * s := by linarith
  have hMn : (M : ℝ) ≤ n := by
    have h1 := hN₁ n hnN
    have : X ≤ (n : ℝ) ^ 2 / 4 := by rw [hX]; nlinarith
    have : s ≤ n / 2 := by nlinarith
    linarith
  set L : ℕ := H.c₁ * M + H.c₂ + l with hL_def
  have hin : ∀ a : Γ, |H.h a| ≤ (M : ℤ) →
      ∃ m : ℕ, a ∈ wordBall (T : Set Γ) m ∧ m + l ≤ L := by
    intro a ha
    refine ⟨H.c₁ * (H.h a).natAbs + H.c₂, H.coarse a, ?_⟩
    have h1 : ((H.h a).natAbs : ℤ) ≤ M := by rw [← Int.abs_eq_natAbs]; exact ha
    have h2 : (H.h a).natAbs ≤ M := by exact_mod_cast h1
    have := Nat.mul_le_mul_left H.c₁ h2
    omega
  have hmain := entropy_le_depth H hp hS hμ hsymm hF hFinv hK hstep hloc hin n (by omega)
  set ρ := (complexity (T : Set Γ) p L : ℝ) with hρ_def
  have hL1 : 1 ≤ L := by omega
  have hLD : (L : ℝ) ≤ D * M := by
    have : L ≤ D * M := by
      have h1 : H.c₂ ≤ H.c₂ * M := Nat.le_mul_of_pos_right _ hMpos
      have h2 : l ≤ l * M := Nat.le_mul_of_pos_right _ hMpos
      rw [hL_def, hD_def, add_mul, add_mul]
      omega
    exact_mod_cast this
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hρ1 : ρ ≤ C * (L : ℝ) ^ α := hρ L hL1
  have hρ0 : 0 ≤ ρ := Nat.cast_nonneg _
  have hρ2 : ρ ≤ C * ((D : ℝ) * M) ^ α :=
    hρ1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hLD hα0) (by linarith))
  -- the first term
  have hcard1 : (1 : ℝ) ≤ (H.box M).card := by
    have h0 : (0 : Γ) ∈ H.box M := (H.mem_box _ _).mpr (by rw [H.h_zero, abs_zero]; positivity)
    exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
  have hcardM : ((H.box M).card : ℝ) ≤ kr * (2 * M + 1) := H.card_box M
  have hT1 : ρ * Real.log (H.box M).card ≤
      C * (2 * D) ^ α * β ^ (α / 2) * (Real.log kr + 2) * (n : ℝ) ^ (α / 2) *
        Real.log n ^ (1 + α / 2) := by
    calc ρ * Real.log (H.box M).card ≤ C * ((D : ℝ) * M) ^ α * Real.log (kr * (2 * M + 1)) :=
          mul_le_mul hρ2 (Real.log_le_log (by linarith) hcardM) (Real.log_nonneg hcard1)
            (by positivity)
      _ ≤ _ := term1_le hα0 (by linarith) (Nat.cast_nonneg _) hβ0 hx3 hlog1 hM1 hMs2 hMn hk1
  -- the second term
  have hρ9 : ρ ≤ C * (D : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
    calc ρ ≤ C * (L : ℝ) ^ α := hρ1
      _ ≤ C * (L : ℝ) ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hLr hα.le) (by linarith)
      _ = C * (L : ℝ) ^ 2 := by rw [Real.rpow_two]
      _ ≤ C * ((D : ℝ) * n) ^ 2 := by
          gcongr
          calc (L : ℝ) ≤ D * M := hLD
            _ ≤ D * n := by gcongr
      _ = C * (D : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
  have hcb : ((H.box ((M : ℤ) + K * n)).card : ℝ) ≤ kr * (3 + 2 * K) * n := by
    have := H.card_box (M + K * n)
    push_cast at this
    refine this.trans ?_
    have hk0 : (0 : ℝ) ≤ kr := by linarith
    have : 2 * ((M : ℝ) + K * n) + 1 ≤ (3 + 2 * K) * n := by nlinarith
    calc kr * (2 * ((M : ℝ) + K * n) + 1) ≤ kr * ((3 + 2 * K) * n) := by gcongr
      _ = kr * (3 + 2 * K) * n := by ring
  have he := exp_tail_le (Mr := M) (K := K) (x := n) (by linarith) (by linarith)
    (by rw [hX, hβ] at hM2; nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ n by linarith)])
  have hT2 := term2_le (C := C) (D := D) (kr := kr) (K := K) (x := n) (ρ := ρ)
    (cb := ((H.box ((M : ℤ) + K * n)).card : ℝ))
    (e := Real.exp (-(((M : ℝ) / K) ^ 2) / (2 * n))) (lF := lF) (by linarith)
    (by linarith) hρ0 hρ9 (Nat.cast_nonneg _) hcb (by linarith) (by positivity)
    (Real.exp_pos _).le he hlF
  have hD1 : 1 ≤ (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
    have h1 : 1 ≤ (n : ℝ) ^ (α / 2) := Real.one_le_rpow (by linarith) (by linarith)
    have h2 : 1 ≤ Real.log n ^ (1 + α / 2) := Real.one_le_rpow hlog1 (by linarith)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hK2 : 0 ≤ 4 * C * (D : ℝ) ^ 2 * kr * (3 + 2 * K) * lF := by
    have : 0 ≤ C := by linarith
    have : 0 ≤ kr := by linarith
    positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc entropy (convPow μ n)
      ≤ ρ * Real.log (H.box M).card + ρ * ((n + 1) * ((H.box ((M : ℤ) + K * n)).card : ℝ) *
          (2 * Real.exp (-(((M : ℝ) / K) ^ 2) / (2 * n)))) * (n * lF) + Real.log 2 :=
        hmain
    _ ≤ C * (2 * D) ^ α * β ^ (α / 2) * (Real.log kr + 2) * (n : ℝ) ^ (α / 2) *
          Real.log n ^ (1 + α / 2) + 4 * C * (D : ℝ) ^ 2 * kr * (3 + 2 * K) * lF +
          Real.log 2 := by linarith
    _ ≤ (C * (2 * D) ^ α * β ^ (α / 2) * (Real.log kr + 2) +
          4 * C * (D : ℝ) ^ 2 * kr * (3 + 2 * K) * lF + Real.log 2) *
          (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
        rw [mul_assoc _ ((n : ℝ) ^ (α / 2)), mul_assoc _ ((n : ℝ) ^ (α / 2))]
        nlinarith

end Final

end IETMBVC

open IETMBVC in
theorem chk_entropy_convPow_le_and_asymptoticEntropy_eq_zero_of_virtuallyCyclic
    {Γ A ι : Type*} [AddCommGroup Γ]
    (hΓ : ∃ γ : Γ, addOrderOf γ = 0 ∧ (AddSubgroup.zmultiples γ).FiniteIndex)
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] (S : Subshift Γ A)
    (hS : Dense {x : S | ∀ γ : Γ, γ +ᵥ x = x → γ = 0})
    (T : Finset Γ) (hT : AddSubgroup.closure (T : Set Γ) = ⊤)
    [Finite ι] (p : S → ι) (hp : IsClopenPartition p) (hsep : IsSeparatingPartition Γ p)
    {α C : ℝ} (hα : α < 2)
    (hρ : ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Γ) p n : ℝ) ≤ C * (n : ℝ) ^ α)
    (μ : topologicalFullGroup Γ S → ℝ) (hfin : (Function.support μ).Finite)
    (hμ : IsProbability μ) (hsymm : IsSymmetric μ) :
    (∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
      entropy (convPow μ n) ≤ C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2)) ∧
    asymptoticEntropy μ = 0 := by
  classical
  -- the bound for all `n ≥ 2`
  have hbound : ∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
      entropy (convPow μ n) ≤ C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2) := by
    rcases isEmpty_or_nonempty S with hSe | hSne
    · have hsub : ∀ g h : topologicalFullGroup Γ S, g = h := fun g h =>
        Subtype.ext (Homeomorph.ext fun y => (IsEmpty.false y).elim)
      refine ⟨0, fun n _ => ?_⟩
      have hp := isProb_convPow hμ n
      have hT : Function.support (convPow μ n) ⊆
          (({1} : Finset (topologicalFullGroup Γ S)) : Set (topologicalFullGroup Γ S)) :=
        fun g _ => by
        simp [hsub g 1]
      have h1 := sum_eq_one_of_support hp _ hT
      rw [Finset.sum_singleton] at h1
      rw [entropy_eq_sum _ hT, Finset.sum_singleton, h1, Real.negMulLog_one]
      simp
    · obtain ⟨H⟩ := exists_height T hΓ hT
      obtain ⟨K, N₀, hK⟩ := entropy_eventually_le hT hp hsep H hS hα hρ μ hfin hμ hsymm
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

end JMMS
end

open CantorSystems ErschlerZheng
theorem solution
    {Γ A ι : Type*} [AddCommGroup Γ]
    (hΓ : ∃ γ : Γ, addOrderOf γ = 0 ∧ (AddSubgroup.zmultiples γ).FiniteIndex)
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] (S : Subshift Γ A)
    (hS : Dense {x : S | ∀ γ : Γ, γ +ᵥ x = x → γ = 0})
    (T : Finset Γ) (hT : AddSubgroup.closure (T : Set Γ) = ⊤)
    [Finite ι] (p : S → ι) (hp : IsClopenPartition p) (hsep : IsSeparatingPartition Γ p)
    {α C : ℝ} (hα : α < 2)
    (hρ : ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Γ) p n : ℝ) ≤ C * (n : ℝ) ^ α)
    (μ : topologicalFullGroup Γ S → ℝ) (hfin : (Function.support μ).Finite)
    (hμ : IsProbability μ) (hsymm : IsSymmetric μ) :
    (∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
      entropy (convPow μ n) ≤ C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2)) ∧
    asymptoticEntropy μ = 0 :=
  JMMS.chk_entropy_convPow_le_and_asymptoticEntropy_eq_zero_of_virtuallyCyclic hΓ S hS T hT p hp hsep hα hρ μ hfin hμ hsymm
