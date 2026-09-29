-- Prove2me | solution 1 for Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a1006785-6070-5395-af14-58162e344fac

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero

set_option autoImplicit false

open scoped InnerProductSpace
open InnerProductSpace

namespace IwasawaAux

theorem main (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ∃ b o : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j : Fin n, j < i → b i j = 0) ∧ (∀ i : Fin n, 0 < b i i) ∧
      (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) ∧ A = b * o := by
  classical

  let f : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (A (Fin.rev i))
  have hf_apply : ∀ i c, f i c = A (Fin.rev i) c := fun i c => rfl

  have hli : LinearIndependent ℝ f := by
    have h1 : LinearIndependent ℝ (fun i => A i) := Matrix.linearIndependent_rows_of_det_ne_zero hA
    have h2 : LinearIndependent ℝ (fun i => A (Fin.rev i)) := (linearIndependent_equiv Fin.revPerm).2 h1
    exact LinearIndependent.of_comp (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap h2
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  let U : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := gramSchmidtOrthonormalBasis hcard f
  have hU : ∀ i, U i = gramSchmidtNormed ℝ f i := fun i =>
    gramSchmidtOrthonormalBasis_apply hcard (by
      intro h0
      have := gramSchmidtNormed_unit_length (𝕜 := ℝ) i hli
      rw [h0, norm_zero] at this
      exact zero_ne_one this)

  let o : Matrix (Fin n) (Fin n) ℝ := fun j c => U (Fin.rev j) c
  let b : Matrix (Fin n) (Fin n) ℝ := fun i j => ⟪f (Fin.rev i), U (Fin.rev j)⟫_ℝ
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪x, y⟫_ℝ = ∑ c, x c * y c := fun x y => by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]
  refine ⟨b, o, ?_, ?_, ?_, ?_⟩
  ·
    intro i j hji
    show ⟪f (Fin.rev i), U (Fin.rev j)⟫_ℝ = 0
    rw [real_inner_comm]
    exact gramSchmidtOrthonormalBasis_inv_triangular hcard f (Fin.rev_lt_rev.2 hji)
  ·
    intro i
    show 0 < ⟪f (Fin.rev i), U (Fin.rev i)⟫_ℝ
    set m := Fin.rev i
    have hgs : gramSchmidt ℝ f m ≠ 0 := gramSchmidt_ne_zero m hli
    have hkey : ⟪f m, gramSchmidt ℝ f m⟫_ℝ = ‖gramSchmidt ℝ f m‖ ^ 2 := by
      conv_lhs => rw [gramSchmidt_def'' ℝ f m]
      rw [inner_add_left, real_inner_self_eq_norm_sq, sum_inner]
      rw [Finset.sum_eq_zero, add_zero]
      intro k hk
      rw [real_inner_smul_left, gramSchmidt_orthogonal ℝ f (Finset.mem_Iio.1 hk).ne, mul_zero]
    have hn : 0 < ‖gramSchmidt ℝ f m‖ := norm_pos_iff.2 hgs
    rw [hU, gramSchmidtNormed, real_inner_smul_right, hkey]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    positivity
  ·
    have hrow : o * o.transpose = 1 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.one_apply]
      have := (orthonormal_iff_ite.1 U.orthonormal) (Fin.rev i) (Fin.rev j)
      rw [hinner] at this
      simp only [Matrix.transpose_apply]
      rw [show (∑ c, o i c * o j c) = ∑ c, U (Fin.rev i) c * U (Fin.rev j) c from rfl, this]
      simp [Fin.rev_inj]
    have hcol : o.transpose * o = 1 := mul_eq_one_comm.1 hrow
    intro i j
    have := congrFun (congrFun hcol i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.transpose_apply] using this
  ·
    ext i c
    rw [Matrix.mul_apply]
    show A i c = ∑ j, ⟪f (Fin.rev i), U (Fin.rev j)⟫_ℝ * U (Fin.rev j) c
    have hsum : (∑ j, ⟪U j, f (Fin.rev i)⟫_ℝ • U j) = f (Fin.rev i) := U.sum_repr' (f (Fin.rev i))
    have h2 : (f (Fin.rev i)) c = A i c := by rw [hf_apply, Fin.rev_rev]
    rw [Fintype.sum_equiv Fin.revPerm (fun j => ⟪f (Fin.rev i), U (Fin.rev j)⟫_ℝ * U (Fin.rev j) c)
        (fun j => ⟪U j, f (Fin.rev i)⟫_ℝ * U j c) (fun j => by simp [Fin.revPerm_apply, real_inner_comm])]
    rw [← h2]
    conv_lhs => rw [← hsum]
    simp

end IwasawaAux

theorem solution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ∃ b o : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j : Fin n, j < i → b i j = 0) ∧ (∀ i : Fin n, 0 < b i i) ∧
      (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) ∧ A = b * o :=
  IwasawaAux.main n A hA

end S_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero
end P2MW
export P2MW.S_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero (solution)
