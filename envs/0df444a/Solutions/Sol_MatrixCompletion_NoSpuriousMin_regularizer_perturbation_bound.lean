-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.regularizer_perturbation_bound
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-14T01:28:52.854195+00:00
-- url     : https://prove2.me/submissions/ff3ca3d9-f86e-46db-b8f9-1480436ee393

/-
Chen–Li 2019 Lemma 4.10 (a modified Ge–Jin–Zheng 2017 Lemma 11), in the mission's
language: the regularizer's contribution to the auxiliary function `K`,

  K₃(X) = λ ( ⟨Δ, ∇²R(X)[Δ]⟩ − 4⟨∇R(X), Δ⟩ ),  Δ = X − U,

is bounded by `199.54 α² ‖Δ‖_F² − 0.3 Σᵢ ‖Δᵢ‖⁴` whenever `α ≥ 100 ‖Z‖_{2→∞}` and
`U Uᵀ = Z Zᵀ`.  The negative quartic term is the point of the lemma: it is what absorbs
the `Σᵢ ‖Δᵢ‖⁴` produced by the sampling estimate (Lemma 4.9).

Source: arXiv:1711.01742v3, Lemma 4.10 and its proof in appendix B.
-/
import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix Finset MatrixCompletion.NoSpuriousMin WithLp

namespace RegPerturb

variable {r : ℕ}

/-! ### `vecNorm` is the Euclidean norm -/

lemma vecNorm_nonneg (x : Fin r → ℝ) : 0 ≤ vecNorm x := Real.sqrt_nonneg _

lemma vecNorm_eq_norm (x : Fin r → ℝ) :
    vecNorm x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin r))‖ := by
  rw [EuclideanSpace.norm_eq, vecNorm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp [sq_abs]

lemma vecNorm_sq (x : Fin r → ℝ) : vecNorm x ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma toLp_sub (x y : Fin r → ℝ) :
    (toLp 2 (x - y) : EuclideanSpace ℝ (Fin r)) = toLp 2 x - toLp 2 y := rfl

lemma vecNorm_sub_le (x y : Fin r → ℝ) : vecNorm (x - y) ≤ vecNorm x + vecNorm y := by
  rw [vecNorm_eq_norm, vecNorm_eq_norm, vecNorm_eq_norm, toLp_sub]
  exact norm_sub_le _ _

lemma le_vecNorm_sub (x y : Fin r → ℝ) : vecNorm x - vecNorm y ≤ vecNorm (x - y) := by
  rw [vecNorm_eq_norm, vecNorm_eq_norm, vecNorm_eq_norm, toLp_sub]
  exact norm_sub_norm_le _ _

/-- Cauchy–Schwarz. -/
lemma abs_inner_le (x y : Fin r → ℝ) :
    |∑ j, x j * y j| ≤ vecNorm x * vecNorm y := by
  have h := abs_real_inner_le_norm (toLp 2 x : EuclideanSpace ℝ (Fin r)) (toLp 2 y)
  rw [EuclideanSpace.inner_toLp_toLp] at h
  simpa [vecNorm_eq_norm, dotProduct, mul_comm] using h

/-! ### The per-row estimate (appendix B of Chen–Li) -/

set_option maxHeartbeats 1000000 in
/-- The polynomial inequality at the end of appendix B, in the variables `w = ‖Xᵢ‖ − α`
and `α`.  The single negative monomial `−13.17774 w² α` is absorbed by
`w (w − 4α)² ≥ 0`. -/
lemma poly_aux {w a : ℝ} (hw : 0 ≤ w) (ha : 0 ≤ a) :
    12.2412 * w ^ 2 * (w + a) + 0.3122 * (w + a) ^ 3 - 15.68 * w ^ 3
      ≤ 195.56 * a ^ 2 * (w + a) := by
  nlinarith [mul_nonneg hw (sq_nonneg (w - 4 * a)), pow_nonneg hw 3,
    mul_nonneg hw (sq_nonneg a), pow_nonneg ha 3]

/-- The scalar heart of Lemma 4.10.  For one row, with `t = ‖Xᵢ‖`, `nd = ‖Δᵢ‖`,
`ip = ⟨Xᵢ, Δᵢ⟩` and `‖Uᵢ‖ ≤ α/100`, the row's contribution to
`⟨Δ, ∇²R(X)[Δ]⟩ − 4⟨∇R(X), Δ⟩` is at most `199.54 α² nd² − 0.3 nd⁴`. -/
lemma row_estimate {α t nd ip : ℝ} (hα : 0 < α) (ht : 0 ≤ t) (hnd : 0 ≤ nd)
    (hub : nd ≤ t + α / 100) (hlb : t - α / 100 ≤ nd)
    (hip : t ^ 2 - t * (α / 100) ≤ ip) (hcs : ip ≤ t * nd) :
    12 * max (t - α) 0 ^ 2 * (ip / t) ^ 2
        + 4 * max (t - α) 0 ^ 3 / t * (nd ^ 2 - (ip / t) ^ 2)
        - 4 * (4 * max (t - α) 0 ^ 3 / t * ip)
      ≤ 199.54 * α ^ 2 * nd ^ 2 - 0.3 * nd ^ 4 := by
  rcases le_or_gt t α with hle | hgt
  · -- Rows below the threshold contribute nothing on the left.
    rw [max_eq_right (by linarith : t - α ≤ 0)]
    have hnda : nd ≤ 1.01 * α := by linarith
    have hkey : 0 ≤ nd ^ 2 * (199.54 * α ^ 2 - 0.3 * nd ^ 2) := by
      have : 0.3 * nd ^ 2 ≤ 199.54 * α ^ 2 := by nlinarith
      exact mul_nonneg (sq_nonneg nd) (by linarith)
    have : (0 : ℝ) ≤ 199.54 * α ^ 2 * nd ^ 2 - 0.3 * nd ^ 4 := by nlinarith
    simpa using this
  · -- Rows above the threshold: the cubic term dominates.
    have ht0 : 0 < t := lt_trans hα hgt
    have htne : t ≠ 0 := ne_of_gt ht0
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ t - α)]
    set w : ℝ := t - α with hwdef
    have hw0 : 0 < w := by simp only [hwdef]; linarith
    set c : ℝ := ip / t with hcdef
    have hipc : ip = c * t := by
      rw [hcdef]; field_simp
    have hndt1 : nd ≤ 1.01 * t := by linarith
    have hndt2 : 0.99 * t ≤ nd := by linarith
    have hc1 : 0.99 * t ≤ c := by
      rw [hcdef, le_div_iff₀ ht0]
      nlinarith
    have hc2 : c ≤ nd := by
      rw [hcdef, div_le_iff₀ ht0]
      nlinarith
    have hcnn : (0 : ℝ) ≤ c := by linarith
    have hcsq : c ^ 2 ≤ nd ^ 2 := by nlinarith
    have e1 : nd ^ 2 ≤ 1.0201 * t ^ 2 := by nlinarith
    have e2 : 0.9801 * t ^ 2 ≤ nd ^ 2 := by nlinarith
    have ec : 0.9801 * t ^ 2 ≤ c ^ 2 := by nlinarith
    -- (B.4): bound the three terms separately.
    have hA : 4 * w ^ 3 / t * (nd ^ 2 - c ^ 2) ≤ 0.16 * w ^ 3 * t := by
      have hnc : nd ^ 2 - c ^ 2 ≤ 0.04 * t ^ 2 := by linarith
      have hfac : (0 : ℝ) ≤ 4 * w ^ 3 / t := by positivity
      calc 4 * w ^ 3 / t * (nd ^ 2 - c ^ 2)
          ≤ 4 * w ^ 3 / t * (0.04 * t ^ 2) := by
            exact mul_le_mul_of_nonneg_left hnc hfac
        _ = 0.16 * w ^ 3 * t := by field_simp; ring
    have hB : 4 * (4 * w ^ 3 / t * ip) = 16 * w ^ 3 * c := by
      rw [hipc]; field_simp; ring
    have hC : 12 * w ^ 2 * c ^ 2 ≤ 12 * w ^ 2 * nd ^ 2 := by
      have p : (0 : ℝ) ≤ w ^ 2 * (nd ^ 2 - c ^ 2) :=
        mul_nonneg (sq_nonneg w) (by linarith)
      linarith
    have hD : -(16 * w ^ 3 * c) ≤ -(15.84 * w ^ 3 * t) := by
      have p : (0 : ℝ) ≤ w ^ 3 * (16 * c - 15.84 * t) :=
        mul_nonneg (pow_nonneg hw0.le 3) (by linarith)
      linarith
    have hstep : 12 * w ^ 2 * c ^ 2 + 4 * w ^ 3 / t * (nd ^ 2 - c ^ 2)
        - 4 * (4 * w ^ 3 / t * ip) ≤ 12 * w ^ 2 * nd ^ 2 - 15.68 * w ^ 3 * t := by
      rw [hB]; linarith
    -- The final polynomial inequality.
    have e3 : 0.3 * nd ^ 4 ≤ 0.30603 * t ^ 2 * nd ^ 2 := by
      have p : (0 : ℝ) ≤ (1.0201 * t ^ 2 - nd ^ 2) * nd ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg nd)
      linarith
    have e4 : 12 * w ^ 2 * nd ^ 2 ≤ 12.2412 * w ^ 2 * t ^ 2 := by
      have p : (0 : ℝ) ≤ w ^ 2 * (1.0201 * t ^ 2 - nd ^ 2) :=
        mul_nonneg (sq_nonneg w) (by linarith)
      linarith
    have e5 : 195.56 * α ^ 2 * t ^ 2 ≤ 199.54 * α ^ 2 * nd ^ 2 := by
      have p : (0 : ℝ) ≤ α ^ 2 * (nd ^ 2 - 0.9801 * t ^ 2) :=
        mul_nonneg (sq_nonneg α) (by linarith)
      have q : (0 : ℝ) ≤ α ^ 2 * t ^ 2 := mul_nonneg (sq_nonneg α) (sq_nonneg t)
      linarith
    have e6 : 0.30603 * t ^ 2 * nd ^ 2 ≤ 0.3122 * t ^ 4 := by
      have p : (0 : ℝ) ≤ t ^ 2 * (1.0201 * t ^ 2 - nd ^ 2) :=
        mul_nonneg (sq_nonneg t) (by linarith)
      have q : (0 : ℝ) ≤ t ^ 2 * t ^ 2 := mul_nonneg (sq_nonneg t) (sq_nonneg t)
      linarith
    have htw : t = w + α := by rw [hwdef]; ring
    have hpoly : 12.2412 * w ^ 2 * t + 0.3122 * t ^ 3 - 15.68 * w ^ 3
        ≤ 195.56 * α ^ 2 * t := by
      rw [htw]; exact poly_aux hw0.le hα.le
    have hpoly' : 12.2412 * w ^ 2 * t ^ 2 + 0.3122 * t ^ 4 - 15.68 * w ^ 3 * t
        ≤ 195.56 * α ^ 2 * t ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hpoly ht0.le
      linarith [h]
    linarith

/-! ### From rows to matrices -/

variable {d : ℕ}

lemma frobSq_eq_sum_rowNorm_sq (A : Matrix (Fin d) (Fin r) ℝ) :
    frobSq A = ∑ i, rowNorm A i ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowNorm, vecNorm_sq]

/-- `U Uᵀ = Z Zᵀ` forces the two factorizations to have the same row norms
(the mission's `row_norms_of_factorization`). -/
lemma rowNorm_eq_of_mul_transpose_eq {U Z : Matrix (Fin d) (Fin r) ℝ}
    (hU : U * Uᵀ = Z * Zᵀ) (i : Fin d) : rowNorm U i = rowNorm Z i := by
  have h : (U * Uᵀ) i i = (Z * Zᵀ) i i := by rw [hU]
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
  rw [rowNorm, rowNorm, vecNorm, vecNorm]
  congr 1
  simpa [sq] using h

lemma rowNorm_le_twoInftyNorm (A : Matrix (Fin d) (Fin r) ℝ) (i : Fin d) :
    rowNorm A i ≤ twoInftyNorm A := by
  rw [twoInftyNorm]
  exact le_ciSup (f := fun k => rowNorm A k) (Set.Finite.bddAbove (Set.finite_range _)) i

lemma sub_row (X U : Matrix (Fin d) (Fin r) ℝ) (i : Fin d) : (X - U) i = X i - U i := rfl

end RegPerturb

open RegPerturb in
/-- **Chen–Li 2019, Lemma 4.10.** -/
theorem solution
    {d r : ℕ} (Z X U : Matrix (Fin d) (Fin r) ℝ) (α : ℝ) (hα : 0 < α)
    (hU : U * Uᵀ = Z * Zᵀ) (hα1 : 100 * twoInftyNorm Z ≤ α) :
    regHessQF α X (X - U) - 4 * innerM (regGrad α X) (X - U)
      ≤ 199.54 * α ^ 2 * frobSq (X - U) - 0.3 * ∑ i, rowNorm (X - U) i ^ 4 := by
  classical
  have hUrow : ∀ i, rowNorm U i ≤ α / 100 := by
    intro i
    rw [rowNorm_eq_of_mul_transpose_eq hU i]
    have h := rowNorm_le_twoInftyNorm Z i
    linarith
  have hgrad : ∀ i : Fin d, ∑ j, regGrad α X i j * (X - U) i j
      = 4 * max (rowNorm X i - α) 0 ^ 3 / rowNorm X i * ∑ j, X i j * (X - U) i j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [regGrad, Matrix.of_apply]; ring
  have hL : regHessQF α X (X - U) - 4 * innerM (regGrad α X) (X - U)
      = ∑ i, (12 * max (rowNorm X i - α) 0 ^ 2
              * ((∑ j, X i j * (X - U) i j) / rowNorm X i) ^ 2
            + 4 * max (rowNorm X i - α) 0 ^ 3 / rowNorm X i
                * (rowNorm (X - U) i ^ 2 - ((∑ j, X i j * (X - U) i j) / rowNorm X i) ^ 2)
            - 4 * (4 * max (rowNorm X i - α) 0 ^ 3 / rowNorm X i
                * ∑ j, X i j * (X - U) i j)) := by
    rw [regHessQF, innerM, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hgrad i]; simp only [rowNorm]
  have hR : 199.54 * α ^ 2 * frobSq (X - U) - 0.3 * ∑ i, rowNorm (X - U) i ^ 4
      = ∑ i, (199.54 * α ^ 2 * rowNorm (X - U) i ^ 2 - 0.3 * rowNorm (X - U) i ^ 4) := by
    rw [frobSq_eq_sum_rowNorm_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hL, hR]
  refine Finset.sum_le_sum fun i _ => ?_
  -- the row data
  have hrX : rowNorm X i = vecNorm (X i) := rfl
  have hrU : rowNorm U i = vecNorm (U i) := rfl
  have hrD : rowNorm (X - U) i = vecNorm (X i - U i) := rfl
  have ht : (0 : ℝ) ≤ rowNorm X i := vecNorm_nonneg _
  have hnd : (0 : ℝ) ≤ rowNorm (X - U) i := vecNorm_nonneg _
  have hu : rowNorm U i ≤ α / 100 := hUrow i
  have hub : rowNorm (X - U) i ≤ rowNorm X i + α / 100 := by
    have h := vecNorm_sub_le (X i) (U i)
    rw [hrX, hrD]; rw [hrU] at hu; linarith
  have hlb : rowNorm X i - α / 100 ≤ rowNorm (X - U) i := by
    have h := le_vecNorm_sub (X i) (U i)
    rw [hrX, hrD]; rw [hrU] at hu; linarith
  have hsplit : (∑ j, X i j * (X - U) i j)
      = rowNorm X i ^ 2 - ∑ j, X i j * U i j := by
    rw [rowNorm, vecNorm_sq, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Matrix.sub_apply]; ring
  have hxu : |∑ j, X i j * U i j| ≤ rowNorm X i * (α / 100) := by
    refine le_trans (abs_inner_le (X i) (U i)) ?_
    rw [rowNorm] at hu
    exact mul_le_mul_of_nonneg_left hu (vecNorm_nonneg _)
  have hip : rowNorm X i ^ 2 - rowNorm X i * (α / 100) ≤ ∑ j, X i j * (X - U) i j := by
    rw [hsplit]
    have := abs_le.mp hxu
    linarith [this.2]
  have hcs : (∑ j, X i j * (X - U) i j) ≤ rowNorm X i * rowNorm (X - U) i := by
    have h := abs_inner_le (X i) ((X - U) i)
    rw [rowNorm, rowNorm]
    exact le_trans (le_abs_self _) h
  exact row_estimate hα ht hnd hub hlb hip hcs
