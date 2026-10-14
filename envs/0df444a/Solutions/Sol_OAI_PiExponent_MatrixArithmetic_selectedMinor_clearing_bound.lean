-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.selectedMinor_clearing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T15:38:15.129625+00:00
-- url     : https://prove2.me/submissions/ba0472e2-99f9-4e59-ad19-c38d47fb1669

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_entry_truncatedLog_cleared_gaussian

namespace OAI.PiExponent

open scoped BigOperators
open Filter Topology

theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

end OAI.PiExponent

namespace OAI.PiExponent.InterpolationMatrix

open scoped BigOperators

theorem column_mem_iff {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (a : Fin (m + 1) → ℕ) :
    a ∈ PiExponent.realWeightedSimplex (columnWeights w0 w) H ↔
      w0 * (a 0 : ℝ) + ∑ i, w i * (a i.succ : ℝ) ≤ H := by
  have hp : ∀ i, 0 < columnWeights w0 w i := by
    intro i
    refine Fin.cases hw0 (fun j => hw j) i
  rw [PiExponent.mem_realWeightedSimplex hp, Fin.sum_univ_succ]
  rfl

theorem column_weight_le {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (c : Column w0 w H) :
    w0 * (c.1 0 : ℝ) + ∑ i, w i * (c.1 i.succ : ℝ) ≤ H :=
  (column_mem_iff hw0 hw c.1).mp c.2

end OAI.PiExponent.InterpolationMatrix

namespace OAI.PiExponent.Arithmetic


theorem gaussian_norm_one_le (z : GaussianInt) (hz : z ≠ 0) :
    1 ≤ ‖(z : ℂ)‖ := by
  have hi : (1 : ℤ) ≤ z.norm := (GaussianInt.norm_pos.mpr hz)
  have hr : (1 : ℝ) ≤ (z.norm : ℝ) := by exact_mod_cast hi
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq] at hr
  have hn : 0 ≤ ‖(z : ℂ)‖ := norm_nonneg _
  nlinarith

theorem gaussian_det_norm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι GaussianInt) (hA : A.det ≠ 0) :
    1 ≤ ‖(A.map GaussianInt.toComplex).det‖ := by
  change 1 ≤ ‖(GaussianInt.toComplex.mapMatrix A).det‖
  rw [← RingHom.map_det]
  exact gaussian_norm_one_le A.det hA

theorem det_row_column_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℂ) :
    Matrix.det (fun i j => r i * (c j * A i j)) =
      (∏ i, r i) * (∏ j, c j) * A.det := by
  calc
    _ = (∏ i, r i) * (Matrix.of fun i j => c j * A i j).det :=
      Matrix.det_mul_column r (Matrix.of fun i j => c j * A i j)
    _ = _ := by rw [Matrix.det_mul_row c A]; ring

theorem cleared_det_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (B : Matrix ι ι GaussianInt)
    (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hB : B.map GaussianInt.toComplex = fun i j => (r i : ℂ) * ((c j : ℂ) * A i j)) :
    1 ≤ (∏ i, r i) * (∏ j, c j) * ‖A.det‖ := by
  have hd : (B.map GaussianInt.toComplex).det =
      (∏ i, (r i : ℂ)) * (∏ j, (c j : ℂ)) * A.det := by
    rw [hB, det_row_column_scale]
  have hn : B.det ≠ 0 := by
    intro he
    have hz : (B.map GaussianInt.toComplex).det = 0 := by
      change (GaussianInt.toComplex.mapMatrix B).det = 0
      rw [← RingHom.map_det, he, map_zero]
    rw [hd] at hz
    have hr' : (∏ i, (r i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact_mod_cast (hr i).ne')
    have hc' : (∏ j, (c j : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      exact_mod_cast (hc j).ne')
    exact mul_ne_zero (mul_ne_zero hr' hc') hA hz
  have h := gaussian_det_norm_one_le B hn
  rw [hd, norm_mul, norm_mul, norm_prod, norm_prod] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr _),
    abs_of_pos (hc _)] using h

theorem cleared_det_log_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (B : Matrix ι ι GaussianInt)
    (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hB : B.map GaussianInt.toComplex = fun i j => (r i : ℂ) * ((c j : ℂ) * A i j)) :
    -(∑ i, Real.log (r i)) - ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  have hrp : 0 < ∏ i, r i := Finset.prod_pos (by intro i hi; exact hr i)
  have hcp : 0 < ∏ i, c i := Finset.prod_pos (by intro i hi; exact hc i)
  have hn : 0 < ‖A.det‖ := norm_pos_iff.mpr hA
  have h := Real.log_nonneg (cleared_det_norm_bound A B r c hr hc hA hB)
  rw [Real.log_mul (mul_pos hrp hcp).ne' hn.ne', Real.log_mul hrp.ne' hcp.ne',
    Real.log_prod (by intro i hi; exact (hr i).ne'),
    Real.log_prod (by intro i hi; exact (hc i).ne')] at h
  linarith

theorem cleared_det_log_bound_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hentries : ∀ i j, (r i : ℂ) * ((c j : ℂ) * A i j) ∈ GaussianInt.toComplex.range) :
    -(∑ i, Real.log (r i)) - ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  classical
  choose B hB using hentries
  apply cleared_det_log_bound A B r c hr hc hA
  ext i j
  exact hB i j

theorem cleared_det_log_bound_with_denominator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℝ) (D : ℝ)
    (hD : 0 < D) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i) (hA : A.det ≠ 0)
    (hentries : ∀ i j, (D : ℂ) * (r i : ℂ) * ((c j : ℂ) * A i j) ∈
      GaussianInt.toComplex.range) :
    -(Fintype.card ι : ℝ) * Real.log D - (∑ i, Real.log (r i)) -
      ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  have h := cleared_det_log_bound_of_entries A (fun i => D * r i) c
    (fun i => mul_pos hD (hr i)) hc hA (by simpa using hentries)
  simp_rw [Real.log_mul hD.ne' (hr _).ne'] at h
  rw [Finset.sum_add_distrib, Finset.sum_const] at h
  simp only [Finset.card_univ, nsmul_eq_mul] at h
  linarith

end OAI.PiExponent.Arithmetic

namespace OAI.PiExponent.MatrixArithmetic

open scoped BigOperators

theorem columnScale_pos {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (a : Fin m → ℕ) : 0 < columnScale q a := by
  exact Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hq i) _)

theorem rowScale_pos {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (b : Fin m → ℕ) : 0 < rowScale q b :=
  inv_pos.mpr (columnScale_pos hq b)

theorem denominator_pos {m : ℕ} (q : Fin m → ℕ) (T : Fin m → ℕ) (H : ℝ) :
    0 < denominator q T H := by
  apply Finset.prod_pos
  intro i hi
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))

theorem log_columnScale {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (a : Fin m → ℕ) :
    Real.log (columnScale q a) = ∑ i, (a i : ℝ) * Real.log (q i) := by
  rw [columnScale, Real.log_prod (by
    intro i hi
    exact pow_ne_zero _ (by exact_mod_cast (hq i).ne'))]
  simp only [Real.log_pow]

theorem log_rowScale {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (b : Fin m → ℕ) :
    Real.log (rowScale q b) = -(∑ i, (b i : ℝ) * Real.log (q i)) := by
  rw [rowScale, Real.log_inv, log_columnScale hq]

theorem ceil_log_weight_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  exact lt_of_lt_of_le (Real.log_pos hqR) (Nat.le_ceil _)

theorem column_coordinate_le_floor {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (c : PiExponent.InterpolationMatrix.Column w0 w H) (i : Fin m) :
    c.1 i.succ ≤ ⌊H / w i⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ (hw i)).mpr
  have hs : w i * (c.1 i.succ : ℝ) ≤
      ∑ j, w j * (c.1 j.succ : ℝ) :=
    Finset.single_le_sum (fun j hj => mul_nonneg (hw j).le (Nat.cast_nonneg (c.1 j.succ)))
      (Finset.mem_univ i)
  have h0 : 0 ≤ w0 * (c.1 0 : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg _)
  have hb := PiExponent.InterpolationMatrix.column_weight_le hw0 hw c
  nlinarith only [hs, h0, hb]

theorem selectedMinor_entries_gaussian {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (ρ σ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :
    (denominator q (truncationOrders q F v0) H : ℂ) *
      (rowScale q (fun i => ρ.2.1 i.succ) : ℂ) *
        ((columnScale q (fun i => (selection σ).1 i.succ) : ℂ) *
          selectedMinor K w0 v0 θ F H p q selection ρ σ) ∈
        GaussianInt.toComplex.range := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have he := InterpolationMatrix.entry_truncatedLog_cleared_gaussian
    (truncationOrders q F v0) q (fun i => ⌊H / logWeights q i⌋₊) p
    (fun i => by have := hq i; omega) ρ.1.val (ρ.2.1 0) ((selection σ).1 0)
    (fun i => ρ.2.1 i.succ) (fun i => (selection σ).1 i.succ)
    (column_coordinate_le_floor hw0 hw (selection σ))
  simp only [denominator, rowScale, columnScale, selectedMinor,
    InterpolationMatrix.truncatedLogMatrix, InterpolationMatrix.matrix,
    Matrix.submatrix_apply, id_eq,
    Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_inv]
  have hcenters : rationalCenters p q =
      (fun i => 2 * Complex.I * (p i : ℂ) / (q i : ℂ)) := rfl
  rw [← hcenters] at he
  convert he using 1
  ring

end OAI.PiExponent.MatrixArithmetic

open OAI.PiExponent OAI.PiExponent.MatrixArithmetic
open scoped BigOperators

theorem solution {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) *
      Real.log (denominator q (truncationOrders q F v0) H) -
      columnCost q selection + rowCost K v0 θ q H ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  have hc := Arithmetic.cleared_det_log_bound_with_denominator
    (selectedMinor K w0 v0 θ F H p q selection)
    (fun ρ => rowScale q (fun i => ρ.2.1 i.succ))
    (fun σ => columnScale q (fun i => (selection σ).1 i.succ))
    (denominator q (truncationOrders q F v0) H)
    (denominator_pos _ _ _) (fun ρ => rowScale_pos hqpos _)
    (fun σ => columnScale_pos hqpos _) hdet
    (selectedMinor_entries_gaussian p q hq hw0 selection)
  simp only [log_rowScale hqpos, log_columnScale hqpos,
    Finset.sum_neg_distrib, sub_neg_eq_add] at hc
  dsimp [columnCost, rowCost]
  linarith
