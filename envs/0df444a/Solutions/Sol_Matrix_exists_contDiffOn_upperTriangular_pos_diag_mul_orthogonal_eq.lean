-- Prove2me | solution 1 for Matrix.exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/546d2a1b-564f-5c1e-ba96-939304b6a04f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq

set_option autoImplicit false

open scoped InnerProductSpace
open InnerProductSpace

namespace IwasawaSmoothAux

variable (n : ℕ)

def U : Set (Fin n → Fin n → ℝ) := {A | (Matrix.of A).det ≠ 0}

theorem mem_U {A : Fin n → Fin n → ℝ} : A ∈ U n ↔ (Matrix.of A).det ≠ 0 := Iff.rfl

noncomputable def R (A : Fin n → Fin n → ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (A (Fin.rev i))

noncomputable def G (A : Fin n → Fin n → ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin n) := gramSchmidt ℝ (R n A) i

theorem R_apply (A : Fin n → Fin n → ℝ) (i c : Fin n) : R n A i c = A (Fin.rev i) c := rfl

theorem contDiff_R (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => R n A i) := by
  have : (fun A : Fin n → Fin n → ℝ => R n A i) =
      ⇑(((EuclideanSpace.equiv (Fin n) ℝ).symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        (ContinuousLinearMap.proj (Fin.rev i))) := by
    funext A; rfl
  rw [this]; exact ContinuousLinearMap.contDiff _

theorem contDiff_coord (c : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin n) => x c) := by
  have : (fun x : EuclideanSpace ℝ (Fin n) => x c) =
      ⇑((ContinuousLinearMap.proj c).comp (EuclideanSpace.equiv (Fin n) ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))) := by
    funext x; rfl
  rw [this]; exact ContinuousLinearMap.contDiff _

theorem linearIndependent_R (A : Fin n → Fin n → ℝ) (hA : (Matrix.of A).det ≠ 0) : LinearIndependent ℝ (R n A) := by
  have h1 : LinearIndependent ℝ (fun i => (Matrix.of A) i) := Matrix.linearIndependent_rows_of_det_ne_zero hA
  have h2 : LinearIndependent ℝ (fun i => A (Fin.rev i)) := (linearIndependent_equiv Fin.revPerm).2 h1
  exact LinearIndependent.of_comp (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap h2

theorem G_ne_zero (A : Fin n → Fin n → ℝ) (hA : (Matrix.of A).det ≠ 0) (i : Fin n) : G n A i ≠ 0 :=
  gramSchmidt_ne_zero i (linearIndependent_R n A hA)

theorem contDiffOn_G : ∀ i : Fin n, ContDiffOn ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => G n A i) (U n) := by
  suffices h : ∀ (m : ℕ) (i : Fin n), (i : ℕ) < m → ContDiffOn ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => G n A i) (U n) from
    fun i => h (i + 1) i (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    have hrec : (fun A : Fin n → Fin n → ℝ => G n A i) = fun A => R n A i -
        ∑ k ∈ Finset.Iio i, (⟪G n A k, R n A i⟫_ℝ / (‖G n A k‖ : ℝ) ^ 2) • G n A k := by
      funext A
      show gramSchmidt ℝ (R n A) i = _
      rw [eq_sub_iff_add_eq]
      have := gramSchmidt_def'' ℝ (R n A) i
      simp only [RCLike.ofReal_real_eq_id, id_eq] at this
      exact this.symm
    rw [hrec]
    apply ((contDiff_R n i).contDiffOn).sub
    apply ContDiffOn.sum
    intro k hk
    have hk' : (k : ℕ) < m := lt_of_lt_of_le (Fin.lt_def.1 (Finset.mem_Iio.1 hk)) (Nat.lt_succ_iff.1 hi)
    have hGk := ih k hk'
    have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun A => ⟪G n A k, R n A i⟫_ℝ / ‖G n A k‖ ^ 2) (U n) :=
      (hGk.inner ℝ (contDiff_R n i).contDiffOn).div ((hGk.norm ℝ fun A hA => G_ne_zero n A hA k).pow 2)
        (fun A hA => pow_ne_zero 2 (norm_ne_zero_iff.2 (G_ne_zero n A hA k)))
    exact hs.smul hGk

noncomputable def oF (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun j c => G n A (Fin.rev j) c / ‖G n A (Fin.rev j)‖

noncomputable def bF (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ⟪R n A (Fin.rev i), G n A (Fin.rev j)⟫_ℝ / ‖G n A (Fin.rev j)‖

theorem contDiffOn_oF : ContDiffOn ℝ (⊤ : ℕ∞) (oF n) (U n) := by
  refine contDiffOn_pi.2 fun j => contDiffOn_pi.2 fun c => ?_
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun A => G n A (Fin.rev j) c / ‖G n A (Fin.rev j)‖) (U n)
  exact ((contDiff_coord n c).comp_contDiffOn (contDiffOn_G n (Fin.rev j))).div
    ((contDiffOn_G n (Fin.rev j)).norm ℝ fun A hA => G_ne_zero n A hA _)
    (fun A hA => norm_ne_zero_iff.2 (G_ne_zero n A hA _))

theorem contDiffOn_bF : ContDiffOn ℝ (⊤ : ℕ∞) (bF n) (U n) := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun A => ⟪R n A (Fin.rev i), G n A (Fin.rev j)⟫_ℝ / ‖G n A (Fin.rev j)‖) (U n)
  exact (((contDiff_R n (Fin.rev i)).contDiffOn).inner ℝ (contDiffOn_G n (Fin.rev j))).div
    ((contDiffOn_G n (Fin.rev j)).norm ℝ fun A hA => G_ne_zero n A hA _)
    (fun A hA => norm_ne_zero_iff.2 (G_ne_zero n A hA _))

theorem oF_eq (A : Fin n → Fin n → ℝ) (j c : Fin n) : oF n A j c = gramSchmidtNormed ℝ (R n A) (Fin.rev j) c := by
  rw [gramSchmidtNormed]
  show G n A (Fin.rev j) c / ‖G n A (Fin.rev j)‖ = ((‖G n A (Fin.rev j)‖ : ℝ)⁻¹ • G n A (Fin.rev j)) c
  simp [div_eq_inv_mul]

end IwasawaSmoothAux

namespace IwasawaSmoothAux

variable (n : ℕ)

theorem algebra (A : Fin n → Fin n → ℝ) (hA : (Matrix.of A).det ≠ 0) :
    (∀ i j : Fin n, j < i → bF n A i j = 0) ∧ (∀ i : Fin n, 0 < bF n A i i) ∧
    (∀ i j : Fin n, ∑ a : Fin n, oF n A a i * oF n A a j = if i = j then 1 else 0) ∧
    ∀ i j : Fin n, A i j = ∑ k : Fin n, bF n A i k * oF n A k j := by
  classical
  have hli := linearIndependent_R n A hA
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  let Ub : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := gramSchmidtOrthonormalBasis hcard (R n A)
  have hU : ∀ i, Ub i = gramSchmidtNormed ℝ (R n A) i := fun i =>
    gramSchmidtOrthonormalBasis_apply hcard (by
      intro h0
      have := gramSchmidtNormed_unit_length (𝕜 := ℝ) i hli
      rw [h0, norm_zero] at this
      exact zero_ne_one this)
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪x, y⟫_ℝ = ∑ c, x c * y c := fun x y => by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]

  have ho : ∀ j c, oF n A j c = Ub (Fin.rev j) c := fun j c => by rw [oF_eq, hU]
  have hb : ∀ i j, bF n A i j = ⟪R n A (Fin.rev i), Ub (Fin.rev j)⟫_ℝ := fun i j => by
    rw [hU, gramSchmidtNormed, inner_smul_right]
    show ⟪R n A (Fin.rev i), G n A (Fin.rev j)⟫_ℝ / ‖G n A (Fin.rev j)‖ = _
    simp only [G, RCLike.ofReal_real_eq_id, id_eq]
    rw [div_eq_inv_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hji
    rw [hb, real_inner_comm]
    exact gramSchmidtOrthonormalBasis_inv_triangular hcard (R n A) (Fin.rev_lt_rev.2 hji)
  · intro i
    rw [hb]
    set m := Fin.rev i
    have hgs : gramSchmidt ℝ (R n A) m ≠ 0 := gramSchmidt_ne_zero m hli
    have hkey : ⟪R n A m, gramSchmidt ℝ (R n A) m⟫_ℝ = ‖gramSchmidt ℝ (R n A) m‖ ^ 2 := by
      conv_lhs => rw [gramSchmidt_def'' ℝ (R n A) m]
      rw [inner_add_left, real_inner_self_eq_norm_sq, sum_inner]
      rw [Finset.sum_eq_zero, add_zero]
      intro k hk
      rw [real_inner_smul_left, gramSchmidt_orthogonal ℝ (R n A) (Finset.mem_Iio.1 hk).ne, mul_zero]
    have hn : 0 < ‖gramSchmidt ℝ (R n A) m‖ := norm_pos_iff.2 hgs
    rw [hU, gramSchmidtNormed, real_inner_smul_right, hkey]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    positivity
  · have hrow : (Matrix.of (oF n A)) * (Matrix.of (oF n A)).transpose = 1 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.one_apply]
      have := (orthonormal_iff_ite.1 Ub.orthonormal) (Fin.rev i) (Fin.rev j)
      rw [hinner] at this
      simp only [Matrix.transpose_apply, Matrix.of_apply, ho]
      rw [this]
      simp [Fin.rev_inj]
    have hcol : (Matrix.of (oF n A)).transpose * Matrix.of (oF n A) = 1 := mul_eq_one_comm.1 hrow
    intro i j
    have := congrFun (congrFun hcol i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.transpose_apply, Matrix.of_apply] using this
  · intro i c
    simp only [hb, ho]
    have hsum : (∑ j, ⟪Ub j, R n A (Fin.rev i)⟫_ℝ • Ub j) = R n A (Fin.rev i) := Ub.sum_repr' (R n A (Fin.rev i))
    have h2 : (R n A (Fin.rev i)) c = A i c := by rw [R_apply, Fin.rev_rev]
    rw [Fintype.sum_equiv Fin.revPerm (fun j => ⟪R n A (Fin.rev i), Ub (Fin.rev j)⟫_ℝ * Ub (Fin.rev j) c)
        (fun j => ⟪Ub j, R n A (Fin.rev i)⟫_ℝ * Ub j c) (fun j => by simp [Fin.revPerm_apply, real_inner_comm])]
    rw [← h2]
    conv_lhs => rw [← hsum]
    simp

theorem main :
    ∃ (b o : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)),
      ContDiffOn ℝ (⊤ : ℕ∞) b {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) o {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ∀ A : Fin n → Fin n → ℝ, (Matrix.of A).det ≠ 0 →
        (∀ i j : Fin n, j < i → b A i j = 0) ∧ (∀ i : Fin n, 0 < b A i i) ∧
        (∀ i j : Fin n, ∑ a : Fin n, o A a i * o A a j = if i = j then 1 else 0) ∧
        ∀ i j : Fin n, A i j = ∑ k : Fin n, b A i k * o A k j :=
  ⟨bF n, oF n, contDiffOn_bF n, contDiffOn_oF n, fun A hA => algebra n A hA⟩

end IwasawaSmoothAux

theorem solution (n : ℕ) :
    ∃ (b o : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)),
      ContDiffOn ℝ (⊤ : ℕ∞) b {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) o {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ∀ A : Fin n → Fin n → ℝ, (Matrix.of A).det ≠ 0 →
        (∀ i j : Fin n, j < i → b A i j = 0) ∧ (∀ i : Fin n, 0 < b A i i) ∧
        (∀ i j : Fin n, ∑ a : Fin n, o A a i * o A a j = if i = j then 1 else 0) ∧
        ∀ i j : Fin n, A i j = ∑ k : Fin n, b A i k * o A k j :=
  IwasawaSmoothAux.main n

end S_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq
end P2MW
export P2MW.S_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq (solution)
