-- Prove2me | solution 1 for OAI.Release075.finite_quotient_rank_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:57:38.015213+00:00
-- url     : https://prove2.me/submissions/101974fb-43b5-4785-b1d6-94218c25601c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L828-L869
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.finite_quotient_rank_obstruction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Theorems.Thm_OAI_Release075_exists_full_rank_minor
import Theorems.Thm_OAI_Release075_nonsingular_rank_reduction_half
import Theorems.Thm_OAI_Release075_quotientMatrix_gram_sq_trace_of_rectangles
import Theorems.Thm_OAI_Release075_sum_rank_le_rank_diagonalBlocks
import Theorems.Thm_OAI_Release075_tensor_certificate
import Theorems.Thm_OAI_Release075_trace_sq_le_rank_mul_trace_sq

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace Release075

universe u v

open scoped BigOperators

theorem rank_reduction_half {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℤ) (r : ℝ) (hr : 1 ≤ r)
    (hrow : ∀ i, ∑ j, (M i j : ℝ) ^ 2 ≤ r)
    (q : ℕ) [Fact q.Prime] (hqr : r < q) :
    (M.map (Int.cast : ℤ → ℝ)).rank ≤
      2 * (M.map (Int.cast : ℤ → ZMod q)).rank := by
  classical
  let MR := M.map (Int.cast : ℤ → ℝ)
  obtain ⟨f, g, _, hg, hdet⟩ := exists_full_rank_minor MR
  let B := M.submatrix f g
  have hBR : B.map (Int.cast : ℤ → ℝ) = MR.submatrix f g := by
    rw [Matrix.submatrix_map]
  have hBdet : B.det ≠ 0 := by
    intro h
    apply hdet
    have hcast : (B.map (Int.cast : ℤ → ℝ)).det = (B.det : ℝ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) B).symm
    rw [← hBR, hcast, h]
    simp
  have hBrow : ∀ i, ∑ j, (B i j : ℝ) ^ 2 ≤ r := by
    intro i
    apply le_trans _ (hrow (f i))
    change (∑ j, (M (f i) (g j) : ℝ) ^ 2) ≤ _
    rw [← Finset.sum_image (f := fun j => (M (f i) j : ℝ) ^ 2)
      (s := Finset.univ) hg.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro j _ _; positivity)
  have hh := nonsingular_rank_reduction_half B hBdet r hr hBrow q hqr
  apply hh.trans
  apply Nat.mul_le_mul_left
  change ((M.submatrix f g).map (Int.cast : ℤ → ZMod q)).rank ≤ _
  rw [← Matrix.submatrix_map]
  exact Matrix.rank_submatrix_le _ _ _

/-- Subadditivity of matrix rank over a field. -/
theorem rank_add_le {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (A B : Matrix ι κ K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_sum_le {ι κ τ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (s : Finset τ) (A : τ → Matrix ι κ K) : (∑ t ∈ s, A t).rank ≤ ∑ t ∈ s, (A t).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | @insert t s ht ih =>
    simp only [Finset.sum_insert ht]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem flattenMatrix_mul {ι κ τ F R : Type*} [Fintype κ] [Fintype F]
    [DecidableEq F] [Semiring R] (A : Matrix ι κ (Matrix F F R))
    (B : Matrix κ τ (Matrix F F R)) :
    flattenMatrix (A * B) = flattenMatrix A * flattenMatrix B := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [flattenMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

theorem flattenMatrix_transpose {ι κ α β R : Type*}
    (A : Matrix ι κ (Matrix α β R)) :
    (flattenMatrix A).transpose = flattenMatrix (Matrix.of fun i j => (A j i).transpose) := rfl

theorem flattenMatrix_trace {ι F R : Type*} [Fintype ι] [Fintype F]
    [AddCommMonoid R] (A : Matrix ι ι (Matrix F F R)) :
    (flattenMatrix A).trace = ∑ i, (A i i).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type, flattenMatrix]

theorem quotientMatrix_gram {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    quotientMatrix (R := R) g * (quotientMatrix g).transpose =
      flattenMatrix (Matrix.of fun u u' => ∑ v, regularMatrix (g u v * (g u' v)⁻¹)) := by
  rw [quotientMatrix, flattenMatrix_transpose, ← flattenMatrix_mul]
  congr 1
  ext u u' a b
  simp [Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply, ← map_mul]

theorem quotientMatrix_gram_trace {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    (quotientMatrix (R := R) g * (quotientMatrix g).transpose).trace =
      (Fintype.card ι : R) ^ 2 * Fintype.card F := by
  rw [quotientMatrix_gram, flattenMatrix_trace]
  simp only [Matrix.of_apply, mul_inv_cancel, map_one, Matrix.trace_sum]
  simp [pow_two, mul_assoc]

/-- Each integral row has exactly one unit entry per block column. -/
theorem quotientMatrix_row_sq {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (i : ι × F) :
    ∑ j, ((quotientMatrix (R := ℤ) g i j : ℤ) : ℝ) ^ 2 = Fintype.card ι := by
  rw [Fintype.sum_prod_type]
  simp [quotientMatrix, flattenMatrix, Matrix.of_apply, ← inv_mul_eq_iff_eq_mul]

/-- Casting the integral matrix gives the corresponding coefficient representation. -/
theorem quotientMatrix_map {ι F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Ring R] (g : ι → ι → F) :
    (quotientMatrix (R := ℤ) g).map (Int.cast : ℤ → R) = quotientMatrix (R := R) g := by
  ext i j
  simp [quotientMatrix, flattenMatrix]

theorem quotientMatrix_rank_real_lower {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (hg : RectanglesSurvive g) :
    Fintype.card ι * Fintype.card F ≤ 2 * (quotientMatrix (R := ℝ) g).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  let Y := quotientMatrix (R := ℝ) g
  have hA : (Y * Y.transpose).IsHermitian := by
    exact Matrix.isHermitian_mul_conjTranspose_self Y
  have hArank : (Y * Y.transpose).rank = Y.rank := by
    exact Matrix.rank_self_mul_conjTranspose Y
  have h := trace_sq_le_rank_mul_trace_sq (Y * Y.transpose) hA
  rw [hArank] at h
  change (quotientMatrix (R := ℝ) g * (quotientMatrix g).transpose).trace ^ 2 ≤ _ at h
  rw [quotientMatrix_gram_trace] at h
  change _ ≤ (Y.rank : ℝ) * ((quotientMatrix (R := ℝ) g * (quotientMatrix g).transpose) *
    (quotientMatrix g * (quotientMatrix g).transpose)).trace at h
  rw [quotientMatrix_gram_sq_trace_of_rectangles g hg] at h
  let r : ℝ := Fintype.card ι
  let D : ℝ := Fintype.card F
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast Nat.pos_of_ne_zero hzero
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hk : 0 ≤ (Y.rank : ℝ) := Nat.cast_nonneg _
  have hcancel : (r ^ 3 * D) * (r * D) ≤ (r ^ 3 * D) * (2 * (Y.rank : ℝ)) := by
    calc
      _ = (r ^ 2 * D) ^ 2 := by ring
      _ ≤ (Y.rank : ℝ) * ((2 * r ^ 3 - r ^ 2) * D) := h
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hk (sq_nonneg r)) hD.le]
  have hf := (mul_le_mul_iff_right₀ (show 0 < r ^ 3 * D by positivity)).mp hcancel
  dsimp [r, D, Y] at hf
  exact_mod_cast hf

theorem quotientMatrix_rank_mod_lower {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (hg : RectanglesSurvive g)
    (q : ℕ) [Fact q.Prime] (hq : Fintype.card ι < q) :
    Fintype.card ι * Fintype.card F ≤ 4 * (quotientMatrix (R := ZMod q) g).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  have hr : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have hqr : (Fintype.card ι : ℝ) < q := by exact_mod_cast hq
  have hred := rank_reduction_half (quotientMatrix (R := ℤ) g) (Fintype.card ι) hr
    (fun i => (quotientMatrix_row_sq g i).le) q hqr
  rw [quotientMatrix_map, quotientMatrix_map] at hred
  have hreal := quotientMatrix_rank_real_lower g hg
  omega

theorem rank_neg {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (A : Matrix ι κ K) : (-A).rank = A.rank := by
  simpa using Matrix.rank_smul_of_mem_nonZeroDivisors A
    (mem_nonZeroDivisors_of_ne_zero (show (-1 : K) ≠ 0 by simp))

/-- A rank-one tensor weight never increases rank. -/
theorem weightedMatrix_rank_le {I ι κ K : Type*} [Fintype I] [Fintype ι]
    [Fintype κ] [Field K] (f : I → K) (Z : Matrix ι κ K) :
    (weightedMatrix f Z).rank ≤ Z.rank := by
  classical
  let L : Matrix (I × ι) ι K := Matrix.of fun x a => if x.2 = a then f x.1 else 0
  let R : Matrix κ (I × κ) K := Matrix.of fun b y => if b = y.2 then f y.1 else 0
  have hfactor : weightedMatrix f Z = L * Z * R := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [weightedMatrix, L, R, Matrix.mul_apply, mul_ite, ite_mul]
    ring
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem rank_budget_of_line_certificate {P I ι κ K : Type*} [Fintype P]
    [Fintype I] [Fintype ι] [Fintype κ] [DecidableEq I] [Field K]
    (inc : P → Finset I) (f : P → I → K) (Y : I → Matrix ι κ K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0)) :
    (∑ i, (Y i).rank) ≤ ∑ z, (∑ i ∈ inc z, Y i).rank := by
  calc
    _ ≤ (diagonalBlocks Y).rank := sum_rank_le_rank_diagonalBlocks Y
    _ = (-diagonalBlocks Y).rank := (rank_neg _).symm
    _ = (∑ z, weightedMatrix (f z) (∑ i ∈ inc z, Y i)).rank := by
      rw [tensor_certificate inc f Y hline]
    _ ≤ ∑ z, (weightedMatrix (f z) (∑ i ∈ inc z, Y i)).rank := rank_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun z _ => weightedMatrix_rank_le _ _)

/-- The numerical rank contradiction. The exceptional incidences are retained;
the ambient dimension, not a deletion, bounds their matrices. -/
theorem finite_quotient_rank_obstruction {P I F : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] [Group F] [Fintype F] [DecidableEq F]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (inc : P → Finset I) (f : P → I → ZMod q) (E : Finset P)
    (g : I → Fin r → Fin r → F) (hg : ∀ i, RectanglesSurvive (g i))
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (hlocal : ∀ z, z ∉ E → (∑ i ∈ inc z, quotientMatrix (R := ZMod q) (g i)).rank ≤
      2 * Fintype.card F)
    (hbudget : 4 * (2 * Fintype.card P + r * E.card) < Fintype.card I * r) : False := by
  classical
  let D := Fintype.card F
  let Y := fun i => quotientMatrix (R := ZMod q) (g i)
  let Z := fun z => ∑ i ∈ inc z, Y i
  have lower : Fintype.card I * r * D ≤ 4 * ∑ i, (Y i).rank := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      quotientMatrix_rank_mod_lower (g i) (hg i) q (by simpa using hq))
    simpa [Y, D, ← Finset.mul_sum, mul_assoc] using h
  have middle : (∑ i, (Y i).rank) ≤ ∑ z, (Z z).rank :=
    rank_budget_of_line_certificate inc f Y hline
  have upper : (∑ z, (Z z).rank) ≤ (2 * Fintype.card P + r * E.card) * D := by
    have hbound (z : P) : (Z z).rank ≤ 2 * D + if z ∈ E then r * D else 0 := by
      by_cases hz : z ∈ E
      · rw [ite_eq_left hz]
        have hrank : (Z z).rank ≤ r * D := by
          simpa [D] using Matrix.rank_le_card_height (Z z)
        omega
      · rw [ite_eq_right hz, add_zero]
        exact hlocal z hz
    calc
      _ ≤ ∑ z, (2 * D + if z ∈ E then r * D else 0) := Finset.sum_le_sum (fun z _ => hbound z)
      _ = _ := by simp [Finset.sum_add_distrib, add_mul]; ring
  have hc : Fintype.card I * r * D ≤ (4 * (2 * Fintype.card P + r * E.card)) * D := by
    calc
      _ ≤ 4 * ∑ i, (Y i).rank := lower
      _ ≤ 4 * ∑ z, (Z z).rank := Nat.mul_le_mul_left _ middle
      _ ≤ 4 * ((2 * Fintype.card P + r * E.card) * D) := Nat.mul_le_mul_left _ upper
      _ = _ := by ring
  exact (Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_right hbudget
    (Fintype.card_pos : 0 < D))) hc

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.finite_quotient_rank_obstruction := @_root_.OAI.Release075.finite_quotient_rank_obstruction
