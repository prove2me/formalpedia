-- Prove2me | solution 1 for LocalPush.pagerank_properties
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T09:29:25.677672+00:00
-- url     : https://prove2.me/submissions/e251070b-bc5c-4ac4-ad1b-0bab45f7273b

import Mathlib
import Definitions.Def_LocalPush_PageRank

open Finset Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset Matrix

namespace LocalPush.Aux

/-- Minimum principle for Z-matrices with positive row sums. -/
theorem zmat_nonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j)
    (y : ι → ℝ) (hy : ∀ i, 0 ≤ (M *ᵥ y) i) : ∀ i, 0 ≤ y i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i0, hi0⟩ := hcon
  obtain ⟨v, -, hv⟩ := Finset.exists_min_image Finset.univ y ⟨i0, Finset.mem_univ _⟩
  have hyv : y v < 0 := lt_of_le_of_lt (hv i0 (Finset.mem_univ _)) hi0
  have h1 : (M *ᵥ y) v ≤ (∑ j, M v j) * y v := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : v = j
    · subst hj; exact le_refl _
    · have := hoff v j hj
      have := hv j (Finset.mem_univ _)
      nlinarith
  have h2 : (∑ j, M v j) * y v < 0 := mul_neg_of_pos_of_neg (hrow v) hyv
  linarith [hy v]

theorem zmat_injective {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j) :
    Function.Injective M.mulVec := by
  intro x y hxy
  have h0 : M *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have a := zmat_nonneg M hoff hrow (x - y) (by intro i; rw [h0]; simp)
  have b := zmat_nonneg M hoff hrow (y - x) (by intro i; rw [← neg_sub, Matrix.mulVec_neg, h0]; simp)
  funext i
  have := a i; have := b i
  simp only [Pi.sub_apply] at *
  linarith

theorem zmat_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j) : IsUnit M.det :=
  (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_injective_iff_isUnit.mp (zmat_injective M hoff hrow))

theorem zmat_inv_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j) (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∀ i, 0 ≤ (M⁻¹ *ᵥ y) i := by
  apply zmat_nonneg M hoff hrow
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (zmat_isUnit_det M hoff hrow), Matrix.one_mulVec]
  exact hy

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem deg_pos (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (v : V) : 0 < deg G v := by
  unfold deg; exact_mod_cast hG v

theorem Lα_apply (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (i j : V) :
    Lα G α i j = (if i = j then deg G i else 0) - (1 - α) * (if G.Adj i j then 1 else 0) := by
  simp [Lα, degM, adjM, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]

theorem Lα_off (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (hα1 : α < 1) (i j : V) (h : i ≠ j) :
    Lα G α i j ≤ 0 := by
  rw [Lα_apply, if_neg h]; split_ifs <;> nlinarith

theorem Lα_rowsum (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (i : V) :
    ∑ j, Lα G α i j = α * deg G i := by
  simp only [Lα_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ← Finset.mul_sum]
  have : (∑ j, if G.Adj i j then (1:ℝ) else 0) = deg G i := by
    rw [Finset.sum_boole]; simp [deg, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  rw [this]; ring

theorem Lα_isUnit_det (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) : IsUnit (Lα G α).det :=
  zmat_isUnit_det _ (Lα_off G α hα1) (fun i => by rw [Lα_rowsum]; exact mul_pos hα0 (deg_pos G hG i))

theorem Lα_symm (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) : (Lα G α)ᵀ = Lα G α := by
  ext i j; simp only [Matrix.transpose_apply, Lα_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]; simp [G.adj_comm]

/-- `I − (1−α)AD⁻¹ = L_α D⁻¹`. -/
theorem M_eq (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ) :
    (1 : Matrix V V ℝ) - (1 - α) • (adjM G * Dinv G) = Lα G α * Dinv G := by
  rw [Lα, Matrix.sub_mul, Matrix.smul_mul]
  congr 1
  rw [degM, Dinv, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, (deg_pos G hG i).ne']

theorem Dinv_isUnit_det (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) :
    IsUnit (Dinv G).det := by
  rw [Dinv, Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (deg_pos G hG i).ne')

theorem Dinv_inv (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) :
    (Dinv G)⁻¹ = degM G := by
  rw [Matrix.inv_eq_left_inv]
  rw [degM, Dinv, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, (deg_pos G hG i).ne']

theorem M_isUnit_det (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    IsUnit ((1 : Matrix V V ℝ) - (1 - α) • (adjM G * Dinv G)).det := by
  rw [M_eq G hG, Matrix.det_mul]
  exact (Lα_isUnit_det G hG α hα0 hα1).mul (Dinv_isUnit_det G hG)

/-- `pr_α(σ) = α D L_α⁻¹ σ`. -/
theorem pr_eq (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ) (σ : V → ℝ) :
    pr G α σ = α • (degM G *ᵥ ((Lα G α)⁻¹ *ᵥ σ)) := by
  rw [pr, M_eq G hG, Matrix.mul_inv_rev, Dinv_inv G hG, Matrix.mulVec_mulVec]

end LocalPush.Aux


namespace LocalPush.Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pr_e_apply (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ) (u v : V) :
    pr G α (e u) v = α * deg G v * (Lα G α)⁻¹ v u := by
  rw [pr_eq G hG]
  simp [e, degM, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  ring

theorem Lα_colsum (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (j : V) :
    ∑ i, Lα G α i j = α * deg G j := by
  rw [← Lα_rowsum G α j]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [← Lα_symm G α]
  rfl

theorem Linv_symm (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (i j : V) :
    (Lα G α)⁻¹ i j = (Lα G α)⁻¹ j i := by
  have : ((Lα G α)⁻¹)ᵀ = (Lα G α)⁻¹ := by rw [Matrix.transpose_nonsing_inv, Lα_symm]
  conv_lhs => rw [← this]
  rfl

/-- `α ∑_v d(v) (L_α⁻¹)_{v u} = 1`. -/
theorem Linv_mass (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (u : V) :
    ∑ v, α * deg G v * (Lα G α)⁻¹ v u = 1 := by
  have h1 : (fun _ : V => (1:ℝ)) ᵥ* Lα G α = fun j => α * deg G j := by
    funext j; simp [Matrix.vecMul, dotProduct, Lα_colsum]
  have h2 : (fun _ : V => (1:ℝ)) ᵥ* (Lα G α * (Lα G α)⁻¹) = fun _ => 1 := by
    rw [Matrix.mul_nonsing_inv _ (Lα_isUnit_det G hG α hα0 hα1), Matrix.vecMul_one]
  rw [← Matrix.vecMul_vecMul, h1] at h2
  have := congrFun h2 u
  simpa [Matrix.vecMul, dotProduct] using this

end LocalPush.Aux


open LocalPush LocalPush.Aux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ u v, 0 ≤ pr G α (e u) v) ∧ (∀ u, ∑ v, pr G α (e u) v = 1) ∧
      ∀ u v, deg G u * pr G α (e u) v = deg G v * pr G α (e v) u := by
  refine ⟨fun u v => ?_, fun u => ?_, fun u v => ?_⟩
  · rw [pr_eq G hG]
    have h := zmat_inv_nonneg (Lα G α) (Lα_off G α hα1)
      (fun i => by rw [Lα_rowsum]; exact mul_pos hα0 (deg_pos G hG i)) (e u)
      (fun i => by simp [e, Pi.single_apply]; split_ifs <;> norm_num) v
    simp only [Pi.smul_apply, smul_eq_mul, degM, Matrix.mulVec_diagonal]
    exact mul_nonneg hα0.le (mul_nonneg (deg_pos G hG v).le h)
  · simp_rw [pr_e_apply G hG]; exact Linv_mass G hG α hα0 hα1 u
  · rw [pr_e_apply G hG, pr_e_apply G hG, Linv_symm G α v u]; ring

