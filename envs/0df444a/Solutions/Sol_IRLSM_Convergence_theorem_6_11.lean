-- Prove2me | solution 1 for IRLSM.Convergence.theorem_6_11
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T17:24:08.371389+00:00
-- url     : https://prove2.me/submissions/e16d289a-520e-40c4-b255-3279bccd378e

-- SPDX-License-Identifier: Apache-2.0
-- Independent formalization of the stated Fornasier--Rauhut--Ward IRLS-M theorem.
-- Existing accepted support contributions by shivm and fizzyinc3 are acknowledged;
-- their submitted proof code was not retrieved or reused in this reconstruction.

import Definitions.Def_IRLSM_Convergence_Algorithm
import Mathlib



section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators

namespace IRLSM.Convergence.IRLSFresh

variable {n p m : ℕ}

theorem traceInner_comm (X Y : Matrix (Fin n) (Fin p) ℝ) : traceInner X Y=traceInner Y X := by
  simp only [traceInner,mul_comm]

theorem traceInner_add_right (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X (Y+Z)=traceInner X Y+traceInner X Z := by
  simp [traceInner,mul_add,Finset.sum_add_distrib]

theorem traceInner_sub_right (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X (Y-Z)=traceInner X Y-traceInner X Z := by
  simp [traceInner,mul_sub,Finset.sum_sub_distrib]

theorem traceInner_smul_right (X Y : Matrix (Fin n) (Fin p) ℝ) (a : ℝ) :
    traceInner X (a•Y)=a*traceInner X Y := by
  simp [traceInner,Finset.mul_sum,mul_left_comm]

theorem traceInner_self_nonneg (X : Matrix (Fin n) (Fin p) ℝ) : 0≤traceInner X X := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (X i j)

theorem frobeniusNorm_sq (X : Matrix (Fin n) (Fin p) ℝ) : frobeniusNorm X^2=traceInner X X := by
  rw [frobeniusNorm,Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (X i j))]
  simp only [traceInner,pow_two]

theorem frobeniusNorm_nonneg (X : Matrix (Fin n) (Fin p) ℝ) : 0≤frobeniusNorm X :=
  Real.sqrt_nonneg _

theorem frobeniusNorm_eq_zero_iff (X : Matrix (Fin n) (Fin p) ℝ) : frobeniusNorm X=0 ↔ X=0 := by
  constructor
  · intro h
    have hs : traceInner X X=0 := by rw [←frobeniusNorm_sq,h]; norm_num
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => mul_self_nonneg (X i j))).mp hs i (Finset.mem_univ _)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (X i j))).mp hi j (Finset.mem_univ _)
    exact mul_self_eq_zero.mp hj
  · rintro rfl
    simp [frobeniusNorm]

theorem continuous_frobeniusNorm : Continuous (frobeniusNorm : Matrix (Fin n) (Fin p) ℝ → ℝ) := by
  unfold frobeniusNorm
  fun_prop

theorem traceInner_eq_trace (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X Y=Matrix.trace (Xᵀ*Y) := by
  simp only [traceInner,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem observationOp_sub (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (X Y : Matrix (Fin n) (Fin p) ℝ) : observationOp A (X-Y)=observationOp A X-observationOp A Y := by
  ext i
  exact traceInner_sub_right _ _ _

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

noncomputable def gramUnitary (X : Matrix (Fin n) (Fin p) ℝ) : Matrix.unitaryGroup (Fin p) ℝ :=
  (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvectorUnitary

noncomputable def gramValue (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : ℝ :=
  Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues j)

theorem gramValue_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : 0 ≤ gramValue X j :=
  Real.sqrt_nonneg _

theorem gramValue_sq (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    gramValue X j ^ 2 = (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues j :=
  Real.sq_sqrt ((Matrix.posSemidef_conjTranspose_mul_self X).eigenvalues_nonneg j)

theorem gramUnitary_transpose_mul (X : Matrix (Fin n) (Fin p) ℝ) :
    (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_star_mul_self (gramUnitary X)

theorem gramUnitary_mul_transpose (X : Matrix (Fin n) (Fin p) ℝ) :
    (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_mul_star_self (gramUnitary X)

theorem gram_diagonal (X : Matrix (Fin n) (Fin p) ℝ) :
    (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ * (Xᵀ * X) * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) =
      Matrix.diagonal (fun j => gramValue X j ^ 2) := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self X).1.conjStarAlgAut_star_eigenvectorUnitary
  simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id,
    gramUnitary, gramValue_sq, id_eq] using h

theorem gram_columns (X : Matrix (Fin n) (Fin p) ℝ) :
    (X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ))ᵀ * (X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) =
      Matrix.diagonal (fun j => gramValue X j ^ 2) := by
  rw [Matrix.transpose_mul]
  simpa only [Matrix.mul_assoc] using gram_diagonal X

theorem nuclearNorm_eq_sum_gramValue (X : Matrix (Fin n) (Fin p) ℝ) :
    nuclearNorm X = ∑ j, gramValue X j := by
  unfold nuclearNorm singularValues gramValue Matrix.IsHermitian.eigenvalues
  let f := fun j : Fin (Fintype.card (Fin p)) =>
    Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues₀ j)
  exact ((finCongr (Fintype.card_fin p)).symm.sum_comp f).trans
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p)))).symm.sum_comp f).symm

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem traceInner_mul_orthogonal (X Y : Matrix (Fin n) (Fin p) ℝ)
    (U : Matrix (Fin p) (Fin p) ℝ) (hU : U*Uᵀ=1) :
    traceInner (X*U) (Y*U)=traceInner X Y := by
  rw [traceInner_eq_trace,traceInner_eq_trace,Matrix.transpose_mul]
  calc
    Matrix.trace (Uᵀ * Xᵀ * (Y*U)) = Matrix.trace (Uᵀ * (Xᵀ*Y) * U) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (U * Uᵀ * (Xᵀ*Y)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Xᵀ*Y) := by rw [hU,Matrix.one_mul]

theorem gram_column_square_sum (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    ∑ i, (X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j ^ 2 = gramValue X j ^ 2 := by
  have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ => A j j) (gram_columns X)
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.diagonal_apply_eq,pow_two] using h

theorem frobeniusNorm_sq_eq_sum_gramValue (X : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm X ^ 2 = ∑ j, gramValue X j ^ 2 := by
  rw [frobeniusNorm_sq,← traceInner_mul_orthogonal X X _ (gramUnitary_mul_transpose X)]
  simp only [traceInner,←pow_two]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => gram_column_square_sum X j

theorem nuclearNorm_nonneg (X : Matrix (Fin n) (Fin p) ℝ) : 0 ≤ nuclearNorm X := by
  rw [nuclearNorm_eq_sum_gramValue]
  exact Finset.sum_nonneg fun j _ => gramValue_nonneg X j

theorem nuclearNorm_eq_zero_iff (X : Matrix (Fin n) (Fin p) ℝ) : nuclearNorm X=0 ↔ X=0 := by
  constructor
  · intro h
    rw [nuclearNorm_eq_sum_gramValue] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => gramValue_nonneg X j)).mp h
    have hf : frobeniusNorm X ^ 2=0 := by
      rw [frobeniusNorm_sq_eq_sum_gramValue]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hz j hj]
      norm_num
    exact (frobeniusNorm_eq_zero_iff X).mp (sq_eq_zero_iff.mp hf)
  · intro hX
    have hf := (frobeniusNorm_eq_zero_iff X).mpr hX
    have hs : ∑ j, gramValue X j ^ 2 = 0 := by
      rw [←frobeniusNorm_sq_eq_sum_gramValue,hf]
      norm_num
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (gramValue X j))).mp hs
    rw [nuclearNorm_eq_sum_gramValue]
    exact Finset.sum_eq_zero fun j hj => sq_eq_zero_iff.mp (hz j hj)

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

def MatrixContractive {n p : ℕ} (Y : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  ∀ v : Fin p → ℝ, (∑ i, (Y *ᵥ v) i ^ 2) ≤ ∑ j, v j ^ 2

theorem matrixContractive_zero {n p : ℕ} :
    MatrixContractive (0 : Matrix (Fin n) (Fin p) ℝ) := by
  intro v
  simp only [zero_mulVec, Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem matrixContractive_column {n p : ℕ} {Y : Matrix (Fin n) (Fin p) ℝ}
    (hY : MatrixContractive Y) (j : Fin p) : ∑ i, Y i j ^ 2 ≤ 1 := by
  have h := hY (Pi.single j 1)
  simpa [Matrix.mulVec_single_one, Pi.single_apply] using h

theorem matrixContractive_entry {n p : ℕ} {Y : Matrix (Fin n) (Fin p) ℝ}
    (hY : MatrixContractive Y) (i : Fin n) (j : Fin p) : |Y i j| ≤ 1 := by
  have hi : Y i j ^ 2 ≤ ∑ k, Y k j ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (Y k j)) (Finset.mem_univ i)
  have hc := matrixContractive_column hY j
  nlinarith [sq_abs (Y i j), abs_nonneg (Y i j)]

theorem isClosed_matrixContractive {n p : ℕ} :
    IsClosed {Y : Matrix (Fin n) (Fin p) ℝ | MatrixContractive Y} := by
  have he : {Y : Matrix (Fin n) (Fin p) ℝ | MatrixContractive Y} =
      ⋂ v : Fin p → ℝ, {Y | (∑ i, (Y *ᵥ v) i ^ 2) ≤ ∑ j, v j ^ 2} := by
    ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, MatrixContractive]
  rw [he]
  apply isClosed_iInter
  intro v
  apply isClosed_le
  · unfold Matrix.mulVec dotProduct
    fun_prop
  · exact continuous_const

theorem isCompact_matrixContractive {n p : ℕ} :
    IsCompact {Y : Matrix (Fin n) (Fin p) ℝ | MatrixContractive Y} := by
  apply (isCompact_Icc : IsCompact (Set.Icc
    (fun _ : Fin n => fun _ : Fin p => (-1 : ℝ)) (fun _ => fun _ => (1 : ℝ)))).of_isClosed_subset
    isClosed_matrixContractive
  intro Y hY
  constructor
  · intro i j
    exact (abs_le.mp (matrixContractive_entry hY i j)).1
  · intro i j
    exact (abs_le.mp (matrixContractive_entry hY i j)).2

theorem convex_matrixContractive {n p : ℕ} :
    Convex ℝ {Y : Matrix (Fin n) (Fin p) ℝ | MatrixContractive Y} := by
  intro X hX Y hY a b ha hb hab v
  have hscalar : ∀ x y : ℝ, (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
    intro x y
    have hb' : b = 1 - a := by linarith
    have hp := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))
    rw [hb'] at hp ⊢
    nlinarith
  calc
    (∑ i, ((a • X + b • Y) *ᵥ v) i ^ 2) =
        ∑ i, (a * (X *ᵥ v) i + b * (Y *ᵥ v) i) ^ 2 := by
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    _ ≤ ∑ i, (a * (X *ᵥ v) i ^ 2 + b * (Y *ᵥ v) i ^ 2) :=
      Finset.sum_le_sum fun i _ => hscalar _ _
    _ = a * (∑ i, (X *ᵥ v) i ^ 2) + b * (∑ i, (Y *ᵥ v) i ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * (∑ j, v j ^ 2) + b * (∑ j, v j ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (hX v) ha)
        (mul_le_mul_of_nonneg_left (hY v) hb)
    _ = ∑ j, v j ^ 2 := by rw [← add_mul, hab, one_mul]

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem sum_sq_mulVec (C : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) :
    ∑ i, (C*ᵥv) i ^ 2 = v ⬝ᵥ (Cᵀ*C)*ᵥv := by
  rw [←Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct,pow_two]

theorem sum_sq_orthogonal_mulVec (U : Matrix (Fin p) (Fin p) ℝ) (hU : Uᵀ*U=1)
    (v : Fin p → ℝ) : ∑ i,(U*ᵥv) i ^ 2=∑ i, v i^2 := by
  rw [sum_sq_mulVec,hU,Matrix.one_mulVec]
  simp only [dotProduct,pow_two]

theorem matrixContractive_mul_orthogonal (Y : Matrix (Fin n) (Fin p) ℝ)
    (hY : MatrixContractive Y) (U : Matrix (Fin p) (Fin p) ℝ) (hU : Uᵀ*U=1) :
    MatrixContractive (Y*U) := by
  intro v
  rw [←Matrix.mulVec_mulVec]
  exact (hY (U*ᵥv)).trans_eq (sum_sq_orthogonal_mulVec U hU v)

theorem sum_sq_gram_coordinates (X : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) :
    ∑ i, ((X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ))*ᵥv) i ^ 2 =
      ∑ j,  gramValue X j ^ 2 * v j ^ 2 := by
  rw [sum_sq_mulVec,gram_columns]
  simp only [dotProduct,Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def polarWitness (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) *
    Matrix.diagonal (fun j => (gramValue X j)⁻¹) *
      (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ

theorem polarWitness_contractive (X : Matrix (Fin n) (Fin p) ℝ) :
    MatrixContractive (polarWitness X) := by
  intro v
  let w := (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ *ᵥ v
  have hn : ∑ j,w j^2=∑ j, v j^2 := by
    apply sum_sq_orthogonal_mulVec
    simpa only [Matrix.transpose_transpose] using gramUnitary_mul_transpose X
  change (∑ i, (((X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) *
    Matrix.diagonal (fun j => (gramValue X j)⁻¹)) *
    (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ) *ᵥ v) i ^ 2) ≤ _
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,sum_sq_gram_coordinates]
  rw [←hn]
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.mulVec_diagonal]
  by_cases h : gramValue X j=0
  · simp [h,sq_nonneg]
  · dsimp [w]
    field_simp
    exact le_rfl

theorem polarWitness_pairing (X : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (polarWitness X) X=nuclearNorm X := by
  rw [←traceInner_mul_orthogonal (polarWitness X) X _ (gramUnitary_mul_transpose X)]
  have hmul : polarWitness X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) =
      X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) *
        Matrix.diagonal (fun j => (gramValue X j)⁻¹) := by
    unfold polarWitness
    rw [Matrix.mul_assoc,gramUnitary_transpose_mul,Matrix.mul_one]
  rw [hmul,nuclearNorm_eq_sum_gramValue]
  simp only [traceInner,Matrix.mul_diagonal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    ∑ i,  (X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j * (gramValue X j)⁻¹ *
      (X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j =
        (gramValue X j)⁻¹ * ∑ i, (X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = gramValue X j := by
      rw [gram_column_square_sum]
      by_cases h : gramValue X j=0
      · simp [h]
      · field_simp

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p r : ℕ}

theorem matrixContractive_mul {A : Matrix (Fin n) (Fin p) ℝ}
    {B : Matrix (Fin p) (Fin r) ℝ} (hA : MatrixContractive A) (hB : MatrixContractive B) :
    MatrixContractive (A*B) := by
  intro v
  rw [←Matrix.mulVec_mulVec]
  exact (hA (B*ᵥv)).trans (hB v)

theorem matrixContractive_transpose {A : Matrix (Fin n) (Fin p) ℝ}
    (hA : MatrixContractive A) : MatrixContractive Aᵀ := by
  intro v
  let w := Aᵀ*ᵥv
  have he : ∑j,w j^2 = ∑i,v i*(A*ᵥw) i := by
    simpa only [dotProduct,pow_two] using Matrix.dotProduct_transpose_mulVec A w v
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (A*ᵥw)
  rw [←he] at hc
  have hb := hA w
  have hv : 0≤∑i,v i^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hw : 0≤∑j,w j^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hb hv
  change (∑j,w j^2)≤∑i,v i^2
  nlinarith

theorem matrixContractive_of_orthonormal (Q : Matrix (Fin n) (Fin p) ℝ)
    (hQ : Qᵀ*Q=1) : MatrixContractive Q := by
  intro v
  rw [sum_sq_mulVec,hQ,Matrix.one_mulVec]
  simp only [dotProduct,pow_two,le_refl]

theorem traceInner_mul_right (X : Matrix (Fin n) (Fin r) ℝ)
    (Y : Matrix (Fin n) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin r) ℝ) :
    traceInner X (Y*Q)=traceInner (X*Qᵀ) Y := by
  rw [traceInner_eq_trace,traceInner_eq_trace,Matrix.transpose_mul,Matrix.transpose_transpose]
  simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle' Xᵀ Y Q)

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix
open scoped MatrixOrder
namespace IRLSM.Convergence.IRLSFresh

theorem psd_sqrt_orthogonal {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hab : A * B = 0) :
    CFC.sqrt A * CFC.sqrt B = 0 := by
  have hba : B * A = 0 := by
    have h := congrArg Matrix.conjTranspose hab
    simpa only [Matrix.conjTranspose_mul, hA.1.eq, hB.1.eq, Matrix.conjTranspose_zero] using h
  have hc : Commute A B := hab.trans hba.symm
  have hs : Commute (CFC.sqrt A) (CFC.sqrt B) := by
    rw [CFC.sqrt_eq_cfc, CFC.sqrt_eq_cfc]
    exact ((hc.cfc_nnreal NNReal.sqrt).symm.cfc_nnreal NNReal.sqrt).symm
  have hsa : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hsb : (CFC.sqrt B).IsHermitian := (CFC.sqrt_nonneg B).posSemidef.1
  have hh : (CFC.sqrt A * CFC.sqrt B)ᴴ = CFC.sqrt A * CFC.sqrt B := by
    rw [Matrix.conjTranspose_mul, hsa, hsb]
    exact hs.eq.symm
  have hz : (CFC.sqrt A * CFC.sqrt B) * (CFC.sqrt A * CFC.sqrt B) = 0 := by
    calc
      _ = CFC.sqrt A * (CFC.sqrt B * CFC.sqrt A) * CFC.sqrt B := by
        simp only [Matrix.mul_assoc]
      _ = CFC.sqrt A * (CFC.sqrt A * CFC.sqrt B) * CFC.sqrt B := by rw [← hs.eq]
      _ = (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt B * CFC.sqrt B) := by
        simp only [Matrix.mul_assoc]
      _ = A * B := by rw [CFC.sqrt_mul_sqrt_self A hA.nonneg,
        CFC.sqrt_mul_sqrt_self B hB.nonneg]
      _ = 0 := hab
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  rw [hh, hz]
  simp

theorem psd_sqrt_add_orthogonal {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hab : A * B = 0) :
    CFC.sqrt (A + B) = CFC.sqrt A + CFC.sqrt B := by
  have hxy := psd_sqrt_orthogonal hA hB hab
  have hyx : CFC.sqrt B * CFC.sqrt A = 0 := by
    have h := congrArg Matrix.conjTranspose hxy
    simpa only [Matrix.conjTranspose_mul, (CFC.sqrt_nonneg A).posSemidef.1.eq,
      (CFC.sqrt_nonneg B).posSemidef.1.eq, Matrix.conjTranspose_zero] using h
  apply CFC.sqrt_unique _ (add_nonneg (CFC.sqrt_nonneg A) (CFC.sqrt_nonneg B))
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hxy, hyx,
    CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  simp

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped MatrixOrder
namespace IRLSM.Convergence.IRLSFresh

theorem trace_psd_mul_nonneg {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ Matrix.trace (A * B) := by
  have h := (hB.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg
  rw [(CFC.sqrt_nonneg A).posSemidef.1.eq, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at h
  exact h

theorem contractive_left_complement_psd {n p : ℕ} {Z : Matrix (Fin n) (Fin p) ℝ}
    (hZ : MatrixContractive Z) : (1 - Z * Zᵀ).PosSemidef := by
  have hh : (Z * Zᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose Z).1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_one.sub hh)
  intro x
  have h := matrixContractive_transpose hZ x
  rw [sum_sq_mulVec, Matrix.transpose_transpose] at h
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  simpa only [dotProduct, pow_two] using sub_nonneg.mpr h

theorem contractive_weighted_trace_le {n p : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : D.PosSemidef) {Z : Matrix (Fin n) (Fin p) ℝ} (hZ : MatrixContractive Z) :
    traceInner Z (D * Z) ≤ Matrix.trace D := by
  have h := trace_psd_mul_nonneg hD (contractive_left_complement_psd hZ)
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub] at h
  rw [traceInner_eq_trace]
  have he : Matrix.trace (Zᵀ * (D * Z)) = Matrix.trace (D * (Z * Zᵀ)) := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [he]
  linarith

theorem weighted_trace_nonneg {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosSemidef) (X : Matrix (Fin n) (Fin p) ℝ) :
    0 ≤ traceInner X (W * X) := by
  rw [traceInner_eq_trace, ← Matrix.mul_assoc]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hW.conjTranspose_mul_mul_same X).trace_nonneg

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

private theorem majorant_pairing_left {n p : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (B * X) Y = traceInner X (Bᵀ * Y) := by
  simp only [traceInner_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem majorant_pairing_sub_left {n p : ℕ}
    (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (X - Y) Z = traceInner X Z - traceInner Y Z := by
  rw [traceInner_comm, traceInner_sub_right, traceInner_comm Z X, traceInner_comm Z Y]

theorem dual_quadratic_upper {n p : ℕ} (ε : ℝ)
    (W S : Matrix (Fin n) (Fin n) ℝ) (hW : W.PosSemidef) (hS : Sᵀ = S)
    (hWS : W * S = 1) (hSW : S * W = 1) (hD : (S - ε • 1).PosSemidef)
    (V Z : Matrix (Fin n) (Fin p) ℝ) (hZ : MatrixContractive Z) :
    traceInner Z V - ε / 2 * frobeniusNorm Z ^ 2 ≤
      traceInner V (W * V) / 2 + Matrix.trace (S - ε • 1) / 2 := by
  have hp := weighted_trace_nonneg hW (V - S * Z)
  rw [Matrix.mul_sub, ← Matrix.mul_assoc W S Z, hWS, Matrix.one_mul,
    majorant_pairing_sub_left, traceInner_sub_right, traceInner_sub_right] at hp
  have hc : traceInner (S * Z) (W * V) = traceInner Z V := by
    rw [majorant_pairing_left, hS, ← Matrix.mul_assoc, hSW, Matrix.one_mul]
  rw [hc, traceInner_comm V Z, traceInner_comm (S * Z) Z] at hp
  have ht := contractive_weighted_trace_le hD hZ
  have hd : traceInner Z ((S - ε • 1) * Z) =
      traceInner Z (S * Z) - ε * frobeniusNorm Z ^ 2 := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, traceInner_sub_right,
      traceInner_smul_right, frobeniusNorm_sq]
  rw [hd] at ht
  linarith

theorem dual_quadratic_contact {n p : ℕ} (ε : ℝ)
    (W S : Matrix (Fin n) (Fin n) ℝ) (hSW : S * W = 1)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (hcontact : (S - ε • 1) * (1 - (W * X) * (W * X)ᵀ) = 0) :
    traceInner (W * X) X - ε / 2 * frobeniusNorm (W * X) ^ 2 =
      traceInner X (W * X) / 2 + Matrix.trace (S - ε • 1) / 2 := by
  let Y := W * X
  have hSY : S * Y = X := by dsimp [Y]; rw [← Matrix.mul_assoc, hSW, Matrix.one_mul]
  have hc := congrArg Matrix.trace hcontact
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_zero] at hc
  have ht : Matrix.trace ((S - ε • 1) * (Y * Yᵀ)) =
      traceInner Y (S * Y) - ε * frobeniusNorm Y ^ 2 := by
    rw [traceInner_eq_trace, frobeniusNorm_sq, traceInner_eq_trace]
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [Matrix.trace_sub, Matrix.trace_smul]
    have h1 : Matrix.trace (S * (Y * Yᵀ)) = Matrix.trace (Yᵀ * (S * Y)) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    have h2 : Matrix.trace (Y * Yᵀ) = Matrix.trace (Yᵀ * Y) := Matrix.trace_mul_comm _ _
    rw [h1, h2]
    rfl
  change Matrix.trace (S - ε • 1) - Matrix.trace ((S - ε • 1) * (Y * Yᵀ)) = 0 at hc
  rw [ht, hSY] at hc
  change traceInner Y X - ε / 2 * frobeniusNorm Y ^ 2 =
    traceInner X Y / 2 + Matrix.trace (S - ε • 1) / 2
  rw [traceInner_comm X Y]
  linarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem real_cfc_intertwining (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A*X=X*B) (f : ℝ→ℝ) :
    cfc f A * X = X * cfc f B := by
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  let V : Matrix (Fin p) (Fin p) ℝ := hB.eigenvectorUnitary
  have hu : Uᵀ*U=1 := by
    simpa only [U,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hu' : U*Uᵀ=1 := mul_eq_one_comm.mp hu
  have hv : Vᵀ*V=1 := by
    simpa only [V,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hv' : V*Vᵀ=1 := mul_eq_one_comm.mp hv
  have huC {q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ) : U*(Uᵀ*Z)=Z := by
    rw [←Matrix.mul_assoc,hu',Matrix.one_mul]
  have hvC {q : ℕ} (Z : Matrix (Fin p) (Fin q) ℝ) : V*(Vᵀ*Z)=Z := by
    rw [←Matrix.mul_assoc,hv',Matrix.one_mul]
  have ha : Uᵀ*A*U=Matrix.diagonal hA.eigenvalues := by
    simpa only [U,Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq]
      using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb : Vᵀ*B*V=Matrix.diagonal hB.eigenvalues := by
    simpa only [V,Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq]
      using hB.conjStarAlgAut_star_eigenvectorUnitary
  let Z := Uᵀ*X*V
  have hz : Matrix.diagonal hA.eigenvalues * Z = Z * Matrix.diagonal hB.eigenvalues := by
    rw [←ha,←hb]
    dsimp [Z]
    calc
      Uᵀ*A*U*(Uᵀ*X*V) = Uᵀ*(A*X)*V := by
        simp only [Matrix.mul_assoc,huC]
      _ = Uᵀ*(X*B)*V := by rw [h]
      _ = Uᵀ*X*V*(Vᵀ*B*V) := by
        simp only [Matrix.mul_assoc,hvC]
  have hf : Matrix.diagonal (f ∘ hA.eigenvalues) * Z = Z * Matrix.diagonal (f ∘ hB.eigenvalues) := by
    ext i j
    have hij := congrArg (fun C : Matrix (Fin n) (Fin p) ℝ => C i j) hz
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at hij ⊢
    by_cases he : hA.eigenvalues i=hB.eigenvalues j
    · simp only [Function.comp_apply,he,mul_comm]
    · have hz0 : Z i j=0 := by
        have : (hA.eigenvalues i-hB.eigenvalues j)*Z i j=0 := by nlinarith [hij]
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr he)
      simp [hz0]
  have hback := congrArg (fun C : Matrix (Fin n) (Fin p) ℝ => U*C*Vᵀ) hf
  rw [hA.cfc_eq,hB.cfc_eq]
  simp only [Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq]
  dsimp [Z] at hback
  simp only [Matrix.mul_assoc,huC,hv',Matrix.mul_one] at hback
  simpa only [U,V,Function.comp_def,Matrix.mul_assoc] using hback

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix
namespace IRLSM.Convergence.IRLSFresh
variable {n : ℕ}

theorem real_cfc_posSemidef (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (f : ℝ→ℝ) (hf : ∀i,0≤f (hA.eigenvalues i)) : (cfc f A).PosSemidef := by
  rw [hA.cfc_eq,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  have hu : IsUnit (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := Unitary.isUnit_coe
  apply hu.posSemidef_star_right_conjugate_iff.mpr
  simpa only [Matrix.posSemidef_diagonal_iff,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq] using hf

theorem real_cfc_posDef (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (f : ℝ→ℝ) (hf : ∀i,0<f (hA.eigenvalues i)) : (cfc f A).PosDef := by
  rw [hA.cfc_eq,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  have hu : IsUnit (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := Unitary.isUnit_coe
  apply hu.posDef_star_right_conjugate_iff.mpr
  simpa only [Matrix.posDef_diagonal_iff,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq] using hf

theorem real_cfc_mul (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (f g : ℝ→ℝ) : cfc f A*cfc g A=cfc (fun t=>f t*g t) A := by
  rw [hA.cfc_eq f,hA.cfc_eq g,hA.cfc_eq (fun t=>f t*g t)]
  unfold Matrix.IsHermitian.cfc
  rw [←map_mul]
  congr 1
  ext i j
  simp only [Matrix.diagonal_mul_diagonal,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq]

theorem real_cfc_congr_eigenvalues (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (f g : ℝ→ℝ) (h : ∀i,f (hA.eigenvalues i)=g (hA.eigenvalues i)) : cfc f A=cfc g A := by
  rw [hA.cfc_eq f,hA.cfc_eq g]
  unfold Matrix.IsHermitian.cfc
  congr 2
  funext i
  exact h i

theorem real_cfc_const_one (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    cfc (fun _ : ℝ=>1) A=1 := by
  rw [hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  simp only [Function.comp_def,Matrix.diagonal_one,map_one]

theorem real_cfc_const_zero (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    cfc (fun _ : ℝ=>0) A=0 := by
  rw [hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  simp only [Function.comp_def,Matrix.diagonal_zero,map_zero]

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix
namespace IRLSM.Convergence.IRLSFresh
variable {n : ℕ}

theorem real_cfc_sub (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (f g : ℝ→ℝ) : cfc f A-cfc g A=cfc (fun t=>f t-g t) A := by
  rw [hA.cfc_eq f,hA.cfc_eq g,hA.cfc_eq (fun t=>f t-g t)]
  unfold Matrix.IsHermitian.cfc
  rw [←map_sub]
  congr 1
  ext i j
  simp only [Matrix.diagonal_sub,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq]

theorem real_cfc_const (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (a : ℝ) :
    cfc (fun _ : ℝ=>a) A=a•(1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  have hd : Matrix.diagonal (RCLike.ofReal ∘ (fun _ : ℝ=>a) ∘ hA.eigenvalues) =
      a•(1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Matrix.diagonal,Matrix.one_apply]
  rw [hd,map_smul,map_one]

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

noncomputable def smoothWitness (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) *
    Matrix.diagonal (fun j => (max (gramValue X j) ε)⁻¹) *
      (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ

theorem weight_mul_eq_smoothWitness (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    weight ε X * X=smoothWitness ε X := by
  have hl : (X*Xᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose X).1
  have hr : (Xᵀ*X).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self X).1
  have he : (X*Xᵀ)*X=X*(Xᵀ*X) := Matrix.mul_assoc _ _ _
  have h := real_cfc_intertwining _ _ X hl hr he (fun t => (max (Real.sqrt t) ε)⁻¹)
  change cfc (fun t : ℝ => (max (Real.sqrt t) ε)⁻¹) (X*Xᵀ) * X = _
  rw [h]
  have hg := (Matrix.posSemidef_conjTranspose_mul_self X).1.cfc_eq
    (fun t : ℝ => (max (Real.sqrt t) ε)⁻¹)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hg
  rw [hg]
  simp only [Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,
    Function.comp_def,RCLike.ofReal_real_eq_id,id_eq,smoothWitness,gramUnitary,gramValue,
    Matrix.mul_assoc]

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

noncomputable def weightInverse (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  cfc (fun t : ℝ => max (Real.sqrt t) ε) (X*Xᵀ)

theorem weight_posDef (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ) :
    (weight ε X).PosDef := by
  have hA : (X*Xᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (Matrix.posSemidef_self_mul_conjTranspose X).1
  apply real_cfc_posDef _ hA
  intro i
  exact inv_pos.mpr (lt_of_lt_of_le hε (le_max_right _ _))

theorem weightInverse_posDef (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ) :
    (weightInverse ε X).PosDef := by
  have hA : (X*Xᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (Matrix.posSemidef_self_mul_conjTranspose X).1
  apply real_cfc_posDef _ hA
  intro i
  exact lt_of_lt_of_le hε (le_max_right _ _)

theorem weight_mul_inverse (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ) :
    weight ε X*weightInverse ε X=1 := by
  have hA : (X*Xᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (Matrix.posSemidef_self_mul_conjTranspose X).1
  unfold weight weightInverse
  rw [real_cfc_mul _ hA]
  calc
    _ = cfc (fun _ : ℝ=>1) (X*Xᵀ) := by
      apply real_cfc_congr_eigenvalues _ hA
      intro i
      exact inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le hε (le_max_right _ _)))
    _ = 1 := real_cfc_const_one _ hA

theorem weightInverse_margin_psd (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    (weightInverse ε X-ε•(1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  have hA : (X*Xᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (Matrix.posSemidef_self_mul_conjTranspose X).1
  rw [←real_cfc_const _ hA ε]
  unfold weightInverse
  rw [real_cfc_sub _ hA]
  apply real_cfc_posSemidef _ hA
  intro i
  exact sub_nonneg.mpr (le_max_right _ _)

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem weight_complementarity (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ) :
    (weightInverse ε X-ε•(1 : Matrix (Fin n) (Fin n) ℝ)) *
      (1-(weight ε X*X)*(weight ε X*X)ᵀ)=0 := by
  let A : Matrix (Fin n) (Fin n) ℝ := X*Xᵀ
  have hP : A.PosSemidef := by
    simpa only [A,Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose X
  have hA := hP.1
  let f : ℝ→ℝ := fun t => (max (Real.sqrt t) ε)⁻¹
  let g : ℝ→ℝ := fun t => max (Real.sqrt t) ε
  have hW : (weight ε X)ᵀ=weight ε X := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (weight_posDef ε hε X).1.eq
  have hid : cfc (fun t : ℝ=>t) A=A := by
    rw [hA.cfc_eq]
    exact hA.spectral_theorem.symm
  have hY : (weight ε X*X)*(weight ε X*X)ᵀ = cfc (fun t=>f t*t*f t) A := by
    rw [Matrix.transpose_mul,hW]
    calc
      weight ε X*X*(Xᵀ*weight ε X) = weight ε X*A*weight ε X := by
        simp only [A,Matrix.mul_assoc]
      _ = cfc f A*cfc (fun t : ℝ=>t) A*cfc f A := by rw [hid]; rfl
      _ = _ := by rw [real_cfc_mul _ hA,real_cfc_mul _ hA]
  have hD : weightInverse ε X-ε•(1 : Matrix (Fin n) (Fin n) ℝ)=cfc (fun t=>g t-ε) A := by
    rw [←real_cfc_const A hA ε]
    exact real_cfc_sub A hA g (fun _=>ε)
  rw [hY,hD,←real_cfc_const_one A hA,real_cfc_sub _ hA,real_cfc_mul _ hA]
  calc
    _ = cfc (fun _ : ℝ=>0) A := by
      apply real_cfc_congr_eigenvalues A hA
      intro i
      have hs := Real.sq_sqrt (hP.eigenvalues_nonneg i)
      dsimp [f,g]
      by_cases he : ε≤Real.sqrt (hA.eigenvalues i)
      · rw [max_eq_left he]
        have hp : Real.sqrt (hA.eigenvalues i)≠0 := ne_of_gt (hε.trans_le he)
        have hz : 1-(Real.sqrt (hA.eigenvalues i))⁻¹*(hA.eigenvalues i)*
            (Real.sqrt (hA.eigenvalues i))⁻¹=0 := by
          field_simp
          nlinarith [hs]
        rw [hz,mul_zero]
      · rw [max_eq_right (le_of_not_ge he)]
        ring
    _ = 0 := real_cfc_const_zero A hA

end IRLSM.Convergence.IRLSFresh
end


section

namespace IRLSM.Convergence.IRLSFresh

 theorem scalar_smoothing_lower {ε u : ℝ} (hε : 0 < ε) : |u| ≤ jε ε u := by
  unfold jε
  split_ifs with h
  · exact le_rfl
  · apply (le_div_iff₀ (by positivity : 0 < 2 * ε)).2
    nlinarith [sq_nonneg (|u| - ε), sq_abs u]

 theorem scalar_smoothing_upper {ε u : ℝ} (hε : 0 < ε) :
    jε ε u ≤ |u| + ε / 2 := by
  unfold jε
  split_ifs with h
  · linarith
  · apply (div_le_iff₀ (by positivity : 0 < 2 * ε)).2
    have hu : |u| < ε := lt_of_not_ge h
    have hab := abs_nonneg u
    have hp := mul_nonneg hab (sub_nonneg.mpr hu.le)
    nlinarith [sq_abs u]

 theorem scalar_smoothing_nonneg {ε u : ℝ} (hε : 0 < ε) : 0 ≤ jε ε u :=
  (abs_nonneg u).trans (scalar_smoothing_lower hε)

 theorem scalar_smoothing_zero {ε : ℝ} (hε : 0 < ε) : jε ε 0 = ε / 2 := by
  rw [jε, if_neg (by simpa using not_le_of_gt hε)]
  field_simp
  ring

 theorem scalar_smoothing_mono {ε δ u : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    jε ε u ≤ jε δ u := by
  have hδ : 0 < δ := hε.trans_le hεδ
  by_cases hdu : δ ≤ |u|
  · simp only [jε, if_pos hdu, if_pos (hεδ.trans hdu)]
    exact le_rfl
  by_cases heu : ε ≤ |u|
  · rw [jε, if_pos heu]
    exact scalar_smoothing_lower hδ
  rw [jε, if_neg heu, jε, if_neg hdu]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * ε)
    (by positivity : 0 < 2 * δ)).2
  have hu : |u| < ε := lt_of_not_ge heu
  have hs : u ^ 2 ≤ ε ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  have hm := mul_nonneg (sub_nonneg.mpr hεδ) (show 0 ≤ ε * δ - u ^ 2 by
    nlinarith [mul_le_mul_of_nonneg_left hεδ hε.le])
  nlinarith

end IRLSM.Convergence.IRLSFresh
end


section

namespace IRLSM.Convergence.IRLSFresh

theorem scalar_variational_upper {ε s y : ℝ} (hε : 0 < ε) (hs : 0 ≤ s)
    (hy : y ≤ 1) : ε / 2 + s * y - ε / 2 * y ^ 2 ≤ jε ε s := by
  rw [jε, abs_of_nonneg hs]
  split_ifs with h
  · have hm := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hy)
    have hq := mul_nonneg hε.le (sq_nonneg (1 - y))
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 2 * ε)).2
    nlinarith [sq_nonneg (s - ε * y)]

theorem scalar_variational_witness_range {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    0 ≤ min (s / ε) 1 ∧ min (s / ε) 1 ≤ 1 := by
  exact ⟨le_min (div_nonneg hs hε.le) zero_le_one, min_le_right _ _⟩

theorem scalar_variational_witness {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    jε ε s = ε / 2 + s * min (s / ε) 1 - ε / 2 * (min (s / ε) 1) ^ 2 := by
  rw [jε, abs_of_nonneg hs]
  split_ifs with h
  · have hr : 1 ≤ s / ε := (le_div_iff₀ hε).2 (by simpa using h)
    rw [min_eq_right hr]
    ring
  · have hr : s / ε ≤ 1 := (div_le_iff₀ hε).2 (by linarith)
    rw [min_eq_left hr]
    field_simp
    ring

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem smooth_ratio_eq {s ε : ℝ} (_hs : 0 ≤ s) (hε : 0 < ε) :
    s/(max s ε)=min (s/ε) 1 := by
  by_cases h : ε ≤ s
  · rw [max_eq_left h,min_eq_right ((le_div_iff₀ hε).2 (by simpa using h)),div_self (ne_of_gt (hε.trans_le h))]
  · rw [max_eq_right (le_of_not_ge h),min_eq_left ((div_le_iff₀ hε).2 (by linarith))]

theorem smoothWitness_mul_gramUnitary (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    smoothWitness ε X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) =
      X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) *
        Matrix.diagonal (fun j => (max (gramValue X j) ε)⁻¹) := by
  unfold smoothWitness
  rw [Matrix.mul_assoc,gramUnitary_transpose_mul,Matrix.mul_one]

theorem smoothWitness_contractive (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ) :
    MatrixContractive (smoothWitness ε X) := by
  intro v
  let w := (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ*ᵥv
  have hn : ∑j,w j^2=∑j,v j^2 := by
    apply sum_sq_orthogonal_mulVec
    simpa only [Matrix.transpose_transpose] using gramUnitary_mul_transpose X
  unfold smoothWitness
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,sum_sq_gram_coordinates,←hn]
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.mulVec_diagonal]
  have hr := scalar_variational_witness_range hε (gramValue_nonneg X j)
  rw [←smooth_ratio_eq (gramValue_nonneg X j) hε] at hr
  have hs : (gramValue X j / max (gramValue X j) ε)^2 ≤ 1 := by nlinarith [hr.1,hr.2]
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (w j))
  dsimp [w] at hm ⊢
  simpa only [div_eq_mul_inv,mul_pow,one_mul,mul_assoc] using hm

theorem smoothWitness_pairing (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (smoothWitness ε X) X =
      ∑j,(max (gramValue X j) ε)⁻¹*gramValue X j^2 := by
  rw [←traceInner_mul_orthogonal (smoothWitness ε X) X _ (gramUnitary_mul_transpose X),
    smoothWitness_mul_gramUnitary]
  simp only [traceInner,Matrix.mul_diagonal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [←gram_column_square_sum X j,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem smoothWitness_frobenius (ε : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm (smoothWitness ε X)^2 =
      ∑j,(gramValue X j / max (gramValue X j) ε)^2 := by
  rw [frobeniusNorm_sq,←traceInner_mul_orthogonal (smoothWitness ε X) (smoothWitness ε X) _
    (gramUnitary_mul_transpose X),smoothWitness_mul_gramUnitary]
  simp only [traceInner,Matrix.mul_diagonal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (max (gramValue X j) ε)⁻¹^2 * ∑i,(X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [gram_column_square_sum]; ring

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem gram_eigenvalues_zero_nonneg (X : Matrix (Fin n) (Fin p) ℝ)
    (j : Fin (Fintype.card (Fin p))) :
    0 ≤ (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues₀ j := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self X).eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p)))) j)
  simpa only [Matrix.IsHermitian.eigenvalues,Equiv.symm_apply_apply] using h

theorem singularValues_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    0 ≤ singularValues X j := Real.sqrt_nonneg _

theorem singularValues_sq (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    singularValues X j ^ 2 = (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues₀
      ((finCongr (Fintype.card_fin p)).symm j) :=
  Real.sq_sqrt (gram_eigenvalues_zero_nonneg X _)

theorem singularValues_antitone (X : Matrix (Fin n) (Fin p) ℝ) :
    Antitone (singularValues X) := by
  intro i j hij
  apply Real.sqrt_le_sqrt
  apply (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues₀_antitone
  exact hij

theorem sv_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (j : ℕ) : 0 ≤ sv X j := by
  unfold sv
  split_ifs
  · exact singularValues_nonneg X _
  · exact le_rfl

theorem sv_antitone (X : Matrix (Fin n) (Fin p) ℝ) : Antitone (sv X) := by
  intro i j hij
  unfold sv
  split_ifs with hi hj
  · exact singularValues_antitone X hij
  · omega
  · exact singularValues_nonneg X _
  · exact le_rfl

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

noncomputable def orderedGramIndex (p : ℕ) : Fin p ≃ Fin p :=
  (finCongr (Fintype.card_fin p)).symm.trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p))))

theorem gramValue_ordered (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) :
    gramValue X (orderedGramIndex p j)=singularValues X j := by
  simp only [gramValue,orderedGramIndex,Equiv.trans_apply,Matrix.IsHermitian.eigenvalues,
    Equiv.symm_apply_apply,singularValues]

theorem rank_eq_card_singularValues (X : Matrix (Fin n) (Fin p) ℝ) :
    X.rank=Fintype.card {j : Fin p // singularValues X j ≠ 0} := by
  rw [←Matrix.rank_conjTranspose_mul_self X,
    (Matrix.posSemidef_conjTranspose_mul_self X).1.rank_eq_card_non_zero_eigs]
  apply Fintype.card_congr
  refine { toFun := fun j => ⟨(orderedGramIndex p).symm j.val, ?_⟩
           invFun := fun j => ⟨orderedGramIndex p j.val, ?_⟩
           left_inv := ?_
           right_inv := ?_ }
  · intro hz
    have hg : gramValue X j.val=0 := by
      simpa only [gramValue_ordered,Equiv.apply_symm_apply] using
        (gramValue_ordered X ((orderedGramIndex p).symm j.val)).trans hz
    have hs := gramValue_sq X j.val
    rw [hg] at hs
    exact j.property (by simpa using hs.symm)
  · intro hz
    have hs := gramValue_sq X (orderedGramIndex p j.val)
    rw [hz,gramValue_ordered] at hs
    exact j.property (sq_eq_zero_iff.mp hs)
  · intro j
    apply Subtype.ext
    exact (orderedGramIndex p).apply_symm_apply j.val
  · intro j
    apply Subtype.ext
    exact (orderedGramIndex p).symm_apply_apply j.val

theorem rank_le_of_sv_eq_zero (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (h : sv X k=0) : X.rank≤k := by
  classical
  rw [rank_eq_card_singularValues]
  let f : {j : Fin p // singularValues X j ≠ 0} → Fin k := fun j =>
    ⟨j.val.val, by
      by_contra hn
      have hle := sv_antitone X (show k≤j.val.val by omega)
      have hj : sv X j.val.val=singularValues X j.val := by simp [sv]
      rw [h,hj] at hle
      exact j.property (le_antisymm hle (singularValues_nonneg X _))⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin k => z.val) hab
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hi

theorem sv_eq_zero_of_rank_le (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (h : X.rank≤k) : sv X k=0 := by
  classical
  by_contra hz
  have hk : k<p := by by_contra hk; simp [sv,show ¬k<p from hk] at hz
  have hp : 0<sv X k := lt_of_le_of_ne (sv_nonneg X k) (Ne.symm hz)
  let f : Fin (k+1) → {j : Fin p // singularValues X j≠0} := fun j =>
    ⟨⟨j.val,by omega⟩,by
      have hj := sv_antitone X (show j.val≤k by omega)
      have hj' : sv X j.val=singularValues X ⟨j.val,by omega⟩ := by simp [sv,show j.val<p by omega]
      rw [hj'] at hj
      exact ne_of_gt (hp.trans_le hj)⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun j => j.val.val) hab
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_fin,←rank_eq_card_singularValues] at hc
  omega

theorem sv_eq_zero_of_row_le (X : Matrix (Fin n) (Fin p) ℝ) (j : ℕ) (hj : n≤j) :
    sv X j=0 := sv_eq_zero_of_rank_le X j ((X.rank_le_card_height.trans_eq (Fintype.card_fin n)).trans hj)

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem sum_gramValue_eq_sum_singularValues (X : Matrix (Fin n) (Fin p) ℝ) (f : ℝ→ℝ) :
    (∑j,f (gramValue X j))=∑j,f (singularValues X j) := by
  simpa only [gramValue_ordered] using ((orderedGramIndex p).sum_comp (fun j => f (gramValue X j))).symm

theorem smoothing_sum_coordinates (X : Matrix (Fin n) (Fin p) ℝ) (hnp : n≤p)
    (ε : ℝ) (hε : 0≤ε) :
    Jeps ε X = (n:ℝ)*ε/2 + ∑j,(jε ε (gramValue X j)-ε/2) := by
  rw [sum_gramValue_eq_sum_singularValues X (fun s => jε ε s-ε/2)]
  have hf : (∑ j : Fin p, (jε ε (singularValues X j)-ε/2)) =
      ∑ j∈Finset.range p,(jε ε (sv X j)-ε/2) := by
    rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp only [sv,dif_pos j.isLt]
  rw [hf]
  have ht : (∑j∈Finset.range n,(jε ε (sv X j)-ε/2)) =
      ∑j∈Finset.range p,(jε ε (sv X j)-ε/2) := by
    apply Finset.sum_subset (Finset.range_mono hnp)
    intro j hj hnj
    have hnj' : n≤j := by simpa only [Finset.mem_range,not_lt] using hnj
    rw [sv_eq_zero_of_row_le X j hnj']
    rw [jε]
    simp only [abs_zero]
    split_ifs with he
    · have hz : ε=0 := le_antisymm he hε
      simp [hz]
    · have hp : ε≠0 := ne_of_gt (lt_of_not_ge he)
      field_simp
      ring
  rw [←ht,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Jeps]
  ring

end IRLSM.Convergence.IRLSFresh
end


section

namespace IRLSM.Convergence.IRLSFresh

theorem vector_variational_upper {ι : Type*} [Fintype ι] {ε s : ℝ}
    (hε : 0 < ε) (hs : 0 ≤ s) (x y : ι → ℝ)
    (hx : ∑ i, x i ^ 2 = s ^ 2) (hy : ∑ i, y i ^ 2 ≤ 1) :
    (∑ i, x i * y i) - ε / 2 * (∑ i, y i ^ 2) ≤ jε ε s - ε / 2 := by
  have hnon : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (y i)
  have hroot : Real.sqrt (∑ i, y i ^ 2) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hy
  have hdot := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y
  rw [hx, Real.sqrt_sq hs] at hdot
  have hscalar := scalar_variational_upper hε hs hroot
  rw [Real.sq_sqrt hnon] at hscalar
  linarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem smoothed_dual_upper (ε : ℝ) (hε : 0<ε) (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hnp : n≤p) (hY : MatrixContractive Y) :
    (n:ℝ)*ε/2+traceInner Y X-ε/2*frobeniusNorm Y^2 ≤ Jeps ε X := by
  let U : Matrix (Fin p) (Fin p) ℝ := gramUnitary X
  have hu : U*Uᵀ=1 := gramUnitary_mul_transpose X
  have hu' : Uᵀ*U=1 := gramUnitary_transpose_mul X
  have hy := matrixContractive_mul_orthogonal Y hY U hu'
  have hi : traceInner Y X = ∑j,∑i,(X*U) i j*(Y*U) i j := by
    rw [traceInner_comm,←traceInner_mul_orthogonal X Y U hu]
    exact Finset.sum_comm
  have hf : frobeniusNorm Y^2=∑j,∑i,(Y*U) i j^2 := by
    rw [frobeniusNorm_sq,←traceInner_mul_orthogonal Y Y U hu]
    simp only [traceInner,←pow_two]
    exact Finset.sum_comm
  have hs : (∑j,((∑i,(X*U) i j*(Y*U) i j)-ε/2*(∑i,(Y*U) i j^2))) ≤
      ∑j,(jε ε (gramValue X j)-ε/2) := by
    apply Finset.sum_le_sum
    intro j _
    exact vector_variational_upper hε (gramValue_nonneg X j) _ _
      (gram_column_square_sum X j) (matrixContractive_column hy j)
  rw [smoothing_sum_coordinates X hnp ε hε.le,hi,hf]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum] at hs
  simp only [Finset.sum_sub_distrib]
  linarith

theorem smoothed_dual_witness (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ)
    (hnp : n≤p) :
    Jeps ε X = (n:ℝ)*ε/2+traceInner (smoothWitness ε X) X-
      ε/2*frobeniusNorm (smoothWitness ε X)^2 := by
  rw [smoothing_sum_coordinates X hnp ε hε.le,smoothWitness_pairing,smoothWitness_frobenius]
  have hs : (∑j,(jε ε (gramValue X j)-ε/2)) =
      (∑j,(max (gramValue X j) ε)⁻¹*gramValue X j^2)-
      ε/2*(∑j,(gramValue X j/max (gramValue X j) ε)^2) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [scalar_variational_witness hε (gramValue_nonneg X j),
      ←smooth_ratio_eq (gramValue_nonneg X j) hε]
    ring
  rw [hs]
  ring

theorem native_smoothed_variational (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ)
    (hnp : n≤p) :
    MatrixContractive (weight ε X * X) ∧
    Jeps ε X=(n:ℝ)*ε/2+traceInner (weight ε X*X) X-ε/2*frobeniusNorm (weight ε X*X)^2 ∧
    ∀Y,MatrixContractive Y→(n:ℝ)*ε/2+traceInner Y X-ε/2*frobeniusNorm Y^2≤Jeps ε X := by
  rw [weight_mul_eq_smoothWitness]
  exact ⟨smoothWitness_contractive ε hε X,smoothed_dual_witness ε hε X hnp,
    fun Y hY => smoothed_dual_upper ε hε X Y hnp hY⟩

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

theorem native_quadratic_majorant {n p : ℕ} (hnp : n ≤ p)
    {ε : ℝ} (hε : 0 < ε) (X V : Matrix (Fin n) (Fin p) ℝ) :
    Jeps ε V ≤ Jeps ε X +
      (traceInner V (weight ε X * V) - traceInner X (weight ε X * X)) / 2 := by
  let W := weight ε X
  let S := weightInverse ε X
  have hWS : W * S = 1 := weight_mul_inverse ε hε X
  have hSW : S * W = 1 := mul_eq_one_comm.mp hWS
  have hS : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (weightInverse_posDef ε hε X).1.eq
  have hv := native_smoothed_variational ε hε V hnp
  have hx := native_smoothed_variational ε hε X hnp
  have hu := dual_quadratic_upper ε W S (weight_posDef ε hε X).posSemidef hS
    hWS hSW (weightInverse_margin_psd ε X) V (weight ε V * V) hv.1
  have hc := dual_quadratic_contact ε W S hSW X (weight_complementarity ε hε X)
  have hvEq := hv.2.1
  have hxEq := hx.2.1
  change Jeps ε X = (n : ℝ) * ε / 2 + traceInner (W * X) X -
    ε / 2 * frobeniusNorm (W * X) ^ 2 at hxEq
  change Jeps ε V ≤ Jeps ε X + (traceInner V (W * V) - traceInner X (W * X)) / 2
  linarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem quadratic_minimum_linear_zero {a b c : ℝ}
    (h : ∀ t : ℝ, c ≤ a * t ^ 2 + b * t + c) : b = 0 := by
  have hm : IsLocalMin (fun t : ℝ => a * t ^ 2 + b * t + c) 0 := by
    filter_upwards [] with t
    simpa using h t
  have hd : HasDerivAt (fun t : ℝ => a * t ^ 2 + b * t + c) b 0 := by
    exact ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul a).add
      ((hasDerivAt_id (0 : ℝ)).const_mul b) |>.add_const c).congr_deriv (by norm_num)
  exact hm.hasDerivAt_eq_zero hd

theorem frobenius_square_line {n p : ℕ} (X H : Matrix (Fin n) (Fin p) ℝ) (t : ℝ) :
    frobeniusNorm (X + t • H) ^ 2 =
      frobeniusNorm H ^ 2 * t ^ 2 + (2 * traceInner X H) * t + frobeniusNorm X ^ 2 := by
  simp only [frobeniusNorm_sq]
  rw [traceInner_add_right, traceInner_smul_right]
  rw [traceInner_comm (X + t • H) X, traceInner_add_right, traceInner_smul_right]
  rw [traceInner_comm (X + t • H) H, traceInner_add_right, traceInner_smul_right,
    traceInner_comm H X]
  ring

theorem frobenius_line_minimum_orthogonal {n p : ℕ} (X H : Matrix (Fin n) (Fin p) ℝ)
    (h : ∀ t : ℝ, frobeniusNorm X ^ 2 ≤ frobeniusNorm (X + t • H) ^ 2) :
    traceInner X H = 0 := by
  have hz := quadratic_minimum_linear_zero (fun t => by
    simpa only [frobenius_square_line] using h t)
  linarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

theorem weighted_minimum_orthogonal {n p m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (X H : Matrix (Fin n) (Fin p) ℝ)
    (hX : observationOp A X = M) (hH : observationOp A H = 0)
    (hmin : ∀ Y, observationOp A Y = M →
      frobeniusNorm (B * X) ^ 2 ≤ frobeniusNorm (B * Y) ^ 2) :
    traceInner (B * X) (B * H) = 0 := by
  apply frobenius_line_minimum_orthogonal
  intro t
  have hf : observationOp A (X + t • H) = M := by
    ext i
    change traceInner (A i) (X + t • H) = M i
    rw [traceInner_add_right, traceInner_smul_right]
    have hx := congrFun hX i
    have hh := congrFun hH i
    change traceInner (A i) X = M i at hx
    change traceInner (A i) H = 0 at hh
    rw [hx, hh]
    ring
  simpa only [Matrix.mul_add, Matrix.mul_smul] using hmin (X + t • H) hf

theorem weighted_minimum_descent {n p m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hX : observationOp A X = M) (hY : observationOp A Y = M)
    (hmin : ∀ Z, observationOp A Z = M →
      frobeniusNorm (B * X) ^ 2 ≤ frobeniusNorm (B * Z) ^ 2) :
    frobeniusNorm (B * Y) ^ 2 =
      frobeniusNorm (B * X) ^ 2 + frobeniusNorm (B * (Y - X)) ^ 2 := by
  have hh : observationOp A (Y - X) = 0 := by
    rw [observationOp_sub, hY, hX, sub_self]
  have ho := weighted_minimum_orthogonal A M B X (Y - X) hX hh hmin
  have he := frobenius_square_line (B * X) (B * (Y - X)) 1
  have hid : B * X + (1 : ℝ) • (B * (Y - X)) = B * Y := by
    rw [one_smul, Matrix.mul_sub]
    abel
  rw [hid, ho] at he
  nlinarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped MatrixOrder
namespace IRLSM.Convergence.IRLSFresh

theorem psd_sqrt_eq_cfc_real {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : CFC.sqrt A = cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg,
    cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := Real.sqrt_zero)]

theorem nuclearNorm_eq_trace_sqrt {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) :
    nuclearNorm X = Matrix.trace (CFC.sqrt (Xᵀ * X)) := by
  have hA : (Xᵀ * X).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  rw [nuclearNorm_eq_sum_gramValue, psd_sqrt_eq_cfc_real hA, hA.1.cfc_eq]
  change (∑ j, gramValue X j) = Matrix.trace
    ((gramUnitary X : Matrix (Fin p) (Fin p) ℝ) *
      Matrix.diagonal (gramValue X) * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ)
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, gramUnitary_transpose_mul,
    Matrix.one_mul, Matrix.trace_diagonal]

theorem orthogonal_nuclear_add {n p : ℕ} (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hxy : X * Yᵀ = 0) (hxty : Xᵀ * Y = 0) :
    nuclearNorm (X + Y) = nuclearNorm X + nuclearNorm Y := by
  have hyx : Yᵀ * X = 0 := by
    have h := congrArg Matrix.transpose hxty
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hA : (Xᵀ * X).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  have hB : (Yᵀ * Y).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self Y
  have hAB : (Xᵀ * X) * (Yᵀ * Y) = 0 := by
    calc
      _ = Xᵀ * (X * Yᵀ) * Y := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hxy, Matrix.mul_zero, Matrix.zero_mul]
  have hg : (X + Y)ᵀ * (X + Y) = Xᵀ * X + Yᵀ * Y := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hxty, hyx]
    simp
  rw [nuclearNorm_eq_trace_sqrt, hg, psd_sqrt_add_orthogonal hA hB hAB,
    Matrix.trace_add, ← nuclearNorm_eq_trace_sqrt, ← nuclearNorm_eq_trace_sqrt]

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped MatrixOrder
namespace IRLSM.Convergence.IRLSFresh

theorem psd_sqrt_quadratic {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosSemidef) (V : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm (cfc Real.sqrt W * V) ^ 2 = traceInner V (W * V) := by
  rw [← psd_sqrt_eq_cfc_real hW, frobeniusNorm_sq, traceInner_eq_trace,
    traceInner_eq_trace, Matrix.transpose_mul]
  have hb : (CFC.sqrt W)ᵀ = CFC.sqrt W := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg W).posSemidef.1.eq
  rw [hb]
  have he : (Vᵀ * CFC.sqrt W) * (CFC.sqrt W * V) = Vᵀ * (W * V) := by
    calc
      _ = Vᵀ * ((CFC.sqrt W * CFC.sqrt W) * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self W hW.nonneg]
  rw [he]

end IRLSM.Convergence.IRLSFresh
end


section

open HighDimStat.MatrixRank Matrix Filter Topology
namespace IRLSM.Convergence.IRLSFresh

private theorem run_sv_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (i : ℕ) :
    0 ≤ sv X i := by
  unfold sv singularValues
  split_ifs <;> positivity

variable {n p m : ℕ} {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ}
  {K : ℕ} {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}

theorem run_epsilon_nonneg (hrun : IsRun A M K γ X ε) (hγ : 0 ≤ γ) (j : ℕ) :
    0 ≤ ε j := by
  induction j with
  | zero => rw [hrun.eps_zero]; norm_num
  | succ j ih =>
    by_cases hj : ε j = 0
    · rw [((hrun.step j).1 hj).2]
    · rw [((hrun.step j).2 hj).2]
      exact le_min ih (mul_nonneg hγ (run_sv_nonneg _ _))

theorem run_epsilon_antitone (hrun : IsRun A M K γ X ε) : Antitone ε := by
  apply antitone_nat_of_succ_le
  intro j
  by_cases hj : ε j = 0
  · rw [((hrun.step j).1 hj).2, hj]
  · rw [((hrun.step j).2 hj).2]
    exact min_le_left _ _

theorem run_feasible_succ (hrun : IsRun A M K γ X ε) (j : ℕ) :
    observationOp A (X (j + 1)) = M := by
  induction j with
  | zero =>
    exact ((hrun.step 0).2 (by rw [hrun.eps_zero]; norm_num)).1.1
  | succ j ih =>
    by_cases hj : ε (j + 1) = 0
    · rw [((hrun.step (j + 1)).1 hj).1]
      exact ih
    · exact ((hrun.step (j + 1)).2 hj).1.1

theorem run_frozen_tail (hrun : IsRun A M K γ X ε) {j : ℕ} (hj : ε j = 0)
    (r : ℕ) : X (j + r) = X j ∧ ε (j + r) = 0 := by
  induction r with
  | zero => simpa using hj
  | succ r ih =>
    obtain ⟨hx, he⟩ := (hrun.step (j + r)).1 ih.2
    constructor
    · exact hx.trans ih.1
    · exact he

theorem run_epsilon_le_singular (hrun : IsRun A M K γ X ε) (hγ : 0 ≤ γ)
    (j : ℕ) : ε (j + 1) ≤ γ * sv (X (j + 1)) K := by
  by_cases hj : ε j = 0
  · rw [((hrun.step j).1 hj).2]
    exact mul_nonneg hγ (run_sv_nonneg _ _)
  · rw [((hrun.step j).2 hj).2]
    exact min_le_right _ _

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

theorem nuclearNorm_eq_sum_sv_row {n p : ℕ} (hnp : n ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ) :
    nuclearNorm X = ∑ i ∈ Finset.range n, sv X i := by
  have hf : nuclearNorm X = ∑ i ∈ Finset.range p, sv X i := by
    rw [nuclearNorm, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [sv, dif_pos i.isLt]
  rw [hf]
  symm
  apply Finset.sum_subset (Finset.range_mono hnp)
  intro i _ hi
  exact sv_eq_zero_of_row_le X i (by simpa only [Finset.mem_range, not_lt] using hi)

theorem native_smoothing_sandwich {n p : ℕ} (hnp : n ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ) {ε : ℝ} (hε : 0 < ε) :
    nuclearNorm X ≤ Jeps ε X ∧ Jeps ε X ≤ nuclearNorm X + (n : ℝ) * ε / 2 := by
  rw [nuclearNorm_eq_sum_sv_row hnp, Jeps]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    simpa only [abs_of_nonneg (sv_nonneg X i)] using
      scalar_smoothing_lower (u := sv X i) hε
  · calc
      (∑ i ∈ Finset.range n, jε ε (sv X i)) ≤
          ∑ i ∈ Finset.range n, (sv X i + ε / 2) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [abs_of_nonneg (sv_nonneg X i)] using
          scalar_smoothing_upper (u := sv X i) hε
      _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]; ring

theorem native_smoothing_mono {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) : Jeps ε X ≤ Jeps δ X := by
  unfold Jeps
  exact Finset.sum_le_sum fun _ _ => scalar_smoothing_mono hε hεδ

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

theorem native_run_descent {n p m : ℕ} (hnp : n ≤ p)
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K γ X ε) (hε : ∀ j, 0 < ε j) (j : ℕ) :
    Jeps (ε (j + 2)) (X (j + 2)) +
      traceInner (X (j + 1) - X (j + 2))
        (weight (ε (j + 1)) (X (j + 1)) * (X (j + 1) - X (j + 2))) / 2 ≤
      Jeps (ε (j + 1)) (X (j + 1)) := by
  let W := weight (ε (j + 1)) (X (j + 1))
  let B := cfc Real.sqrt W
  have hW : W.PosSemidef := (weight_posDef _ (hε _) _).posSemidef
  have hmin : ∀ Y, observationOp A Y = M →
      frobeniusNorm (B * X (j + 2)) ^ 2 ≤ frobeniusNorm (B * Y) ^ 2 := by
    simpa only [Wseq] using ((hrun.step (j + 1)).2 (ne_of_gt (hε _))).1.2
  have hd := weighted_minimum_descent A M B (X (j + 2)) (X (j + 1))
    (run_feasible_succ hrun (j + 1)) (run_feasible_succ hrun j) hmin
  change frobeniusNorm (cfc Real.sqrt W * X (j + 1)) ^ 2 =
    frobeniusNorm (cfc Real.sqrt W * X (j + 2)) ^ 2 +
      frobeniusNorm (cfc Real.sqrt W * (X (j + 1) - X (j + 2))) ^ 2 at hd
  simp only [psd_sqrt_quadratic hW] at hd
  have hm := native_quadratic_majorant hnp (hε (j + 1)) (X (j + 1)) (X (j + 2))
  have he := native_smoothing_mono (X (j + 2)) (hε (j + 2))
    (run_epsilon_antitone hrun (show j + 1 ≤ j + 2 by omega))
  change Jeps (ε (j + 2)) (X (j + 2)) +
    traceInner (X (j + 1) - X (j + 2)) (W * (X (j + 1) - X (j + 2))) / 2 ≤ _
  change Jeps (ε (j + 1)) (X (j + 2)) ≤ Jeps (ε (j + 1)) (X (j + 1)) +
    (traceInner (X (j + 2)) (W * X (j + 2)) - traceInner (X (j + 1)) (W * X (j + 1))) / 2 at hm
  linarith

end IRLSM.Convergence.IRLSFresh
end


section

open Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem descent_gap_summable {E gap : ℕ → ℝ} {b : ℝ}
    (hbound : ∀ j, b ≤ E j) (hgap : ∀ j, 0 ≤ gap j)
    (hstep : ∀ j, E (j + 1) + gap j ≤ E j) : Summable gap := by
  have hsum : ∀ N, E N + ∑ j ∈ Finset.range N, gap j ≤ E 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep N]
  apply summable_of_sum_range_le hgap
  intro N
  exact (show ∑ j ∈ Finset.range N, gap j ≤ E 0 - b by linarith [hsum N, hbound N])

theorem descent_gap_tendsto_zero {E gap : ℕ → ℝ} {b : ℝ}
    (hbound : ∀ j, b ≤ E j) (hgap : ∀ j, 0 ≤ gap j)
    (hstep : ∀ j, E (j + 1) + gap j ≤ E j) :
    Tendsto gap atTop (𝓝 0) :=
  (descent_gap_summable hbound hgap hstep).tendsto_atTop_zero

theorem antitone_nonneg_limit {e : ℕ → ℝ} (he : Antitone e) (hn : ∀ j, 0 ≤ e j) :
    ∃ a : ℝ, 0 ≤ a ∧ Tendsto e atTop (𝓝 a) := by
  have hb : BddBelow (Set.range e) := ⟨0, by rintro _ ⟨j, rfl⟩; exact hn j⟩
  refine ⟨⨅ j, e j, ?_, tendsto_atTop_ciInf he hb⟩
  exact le_ciInf hn

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

variable {n p m : ℕ} {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ}
  {K : ℕ} {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}

theorem native_run_energy_antitone (hnp : n ≤ p) (hrun : IsRun A M K γ X ε)
    (hε : ∀ j, 0 < ε j) : Antitone (fun j => Jeps (ε (j + 1)) (X (j + 1))) := by
  apply antitone_nat_of_succ_le
  intro j
  have hd := native_run_descent hnp hrun hε j
  have hg := weighted_trace_nonneg (weight_posDef _ (hε (j + 1)) (X (j + 1))).posSemidef
    (X (j + 1) - X (j + 2))
  change Jeps (ε (j + 2)) (X (j + 2)) ≤ Jeps (ε (j + 1)) (X (j + 1))
  linarith

theorem native_run_nuclear_bounded (hnp : n ≤ p) (hrun : IsRun A M K γ X ε)
    (hε : ∀ j, 0 < ε j) (j : ℕ) :
    nuclearNorm (X (j + 1)) ≤ Jeps (ε 1) (X 1) := by
  exact (native_smoothing_sandwich hnp (X (j + 1)) (hε (j + 1))).1.trans
    (native_run_energy_antitone hnp hrun hε (Nat.zero_le j))

theorem native_run_gap_tendsto_zero (hnp : n ≤ p) (hrun : IsRun A M K γ X ε)
    (hε : ∀ j, 0 < ε j) :
    Tendsto (fun j => traceInner (X (j + 1) - X (j + 2))
      (weight (ε (j + 1)) (X (j + 1)) * (X (j + 1) - X (j + 2))) / 2)
      atTop (𝓝 0) := by
  apply descent_gap_tendsto_zero
    (E := fun j => Jeps (ε (j + 1)) (X (j + 1))) (b := 0)
  · intro j
    exact (nuclearNorm_nonneg _).trans (native_smoothing_sandwich hnp _ (hε (j + 1))).1
  · intro j
    exact div_nonneg
      (weighted_trace_nonneg (weight_posDef _ (hε (j + 1)) (X (j + 1))).posSemidef _) (by norm_num)
  · intro j
    exact native_run_descent hnp hrun hε j

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

theorem contractive_column_pairing {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    {Y : Matrix (Fin n) (Fin p) ℝ} (hY : MatrixContractive Y) (j : Fin p) :
    (∑ i, X i j * Y i j) ≤ Real.sqrt (∑ i, X i j ^ 2) := by
  have hy : Real.sqrt (∑ i, Y i j ^ 2) ≤ 1 := by
    have := Real.sqrt_le_sqrt (matrixContractive_column hY j)
    simpa using this
  calc
    (∑ i, X i j * Y i j) ≤
        Real.sqrt (∑ i, X i j ^ 2) * Real.sqrt (∑ i, Y i j ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ i, X i j ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _)
    _ = _ := mul_one _

theorem contractive_trace_pairing {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    {Y : Matrix (Fin n) (Fin p) ℝ} (hY : MatrixContractive Y) :
    traceInner X Y ≤ ∑ j, Real.sqrt (∑ i, X i j ^ 2) := by
  unfold traceInner
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun j _ => contractive_column_pairing X hY j

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem contractive_pairing_le_nuclearNorm (X : Matrix (Fin n) (Fin p) ℝ)
    {Y : Matrix (Fin n) (Fin p) ℝ} (hY : MatrixContractive Y) :
    traceInner Y X ≤ nuclearNorm X := by
  rw [traceInner_comm,←traceInner_mul_orthogonal X Y _ (gramUnitary_mul_transpose X),
    nuclearNorm_eq_sum_gramValue]
  refine (contractive_trace_pairing _
    (matrixContractive_mul_orthogonal Y hY _ (gramUnitary_transpose_mul X))).trans_eq ?_
  apply Finset.sum_congr rfl
  intro j _
  rw [gram_column_square_sum,Real.sqrt_sq (gramValue_nonneg X j)]

theorem nuclearNorm_triangle (X Y : Matrix (Fin n) (Fin p) ℝ) :
    nuclearNorm (X+Y) ≤ nuclearNorm X+nuclearNorm Y := by
  rw [←polarWitness_pairing (X+Y),traceInner_add_right]
  exact add_le_add (contractive_pairing_le_nuclearNorm X (polarWitness_contractive (X+Y)))
    (contractive_pairing_le_nuclearNorm Y (polarWitness_contractive (X+Y)))

theorem matrixContractive_neg {Y : Matrix (Fin n) (Fin p) ℝ} (hY : MatrixContractive Y) :
    MatrixContractive (-Y) := by
  intro v
  simpa only [Matrix.neg_mulVec,Pi.neg_apply,neg_sq] using hY v

theorem nuclearNorm_neg (X : Matrix (Fin n) (Fin p) ℝ) : nuclearNorm (-X)=nuclearNorm X := by
  have hle : ∀ Z : Matrix (Fin n) (Fin p) ℝ, nuclearNorm (-Z) ≤ nuclearNorm Z := by
    intro Z
    rw [←polarWitness_pairing (-Z)]
    have h := contractive_pairing_le_nuclearNorm Z (matrixContractive_neg (polarWitness_contractive (-Z)))
    simpa only [traceInner,Matrix.neg_apply,neg_mul,mul_neg] using h
  exact le_antisymm (hle X) (by simpa only [neg_neg] using hle (-X))

theorem nuclearNorm_sub_le (X Y : Matrix (Fin n) (Fin p) ℝ) :
    |nuclearNorm X-nuclearNorm Y| ≤ nuclearNorm (X-Y) := by
  apply abs_le.mpr
  have hx := nuclearNorm_triangle (X-Y) Y
  have hy := nuclearNorm_triangle (Y-X) X
  have he : Y-X=-(X-Y) := by abel
  rw [sub_add_cancel] at hx hy
  rw [he,nuclearNorm_neg] at hy
  constructor <;> linarith

theorem nuclearNorm_le_frobenius (X : Matrix (Fin n) (Fin p) ℝ) :
    nuclearNorm X ≤ (p:ℝ)*frobeniusNorm X := by
  rw [nuclearNorm_eq_sum_gramValue]
  have h : (∑ j : Fin p, gramValue X j) ≤ ∑ _j : Fin p, frobeniusNorm X := by
    apply Finset.sum_le_sum
    intro j _
    have hsq : gramValue X j ^ 2 ≤ frobeniusNorm X ^ 2 := by
      rw [frobeniusNorm_sq_eq_sum_gramValue]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (gramValue X i)) (Finset.mem_univ j)
    nlinarith [gramValue_nonneg X j,frobeniusNorm_nonneg X]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem frobeniusNorm_le_nuclearNorm {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm X ≤ nuclearNorm X := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (fun j _ => gramValue_nonneg X j)
  rw [← frobeniusNorm_sq_eq_sum_gramValue, ← nuclearNorm_eq_sum_gramValue] at hs
  nlinarith [frobeniusNorm_nonneg X, nuclearNorm_nonneg X]

theorem entry_abs_le_frobeniusNorm {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (i : Fin n) (j : Fin p) : |X i j| ≤ frobeniusNorm X := by
  have h1 : X i j ^ 2 ≤ ∑ k, X i k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (X i k)) (Finset.mem_univ j)
  have h2 : (∑ k, X i k ^ 2) ≤ ∑ l, ∑ k, X l k ^ 2 :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg (X l k))
      (Finset.mem_univ i)
  have hf : frobeniusNorm X ^ 2 = ∑ l, ∑ k, X l k ^ 2 := by
    rw [frobeniusNorm, Real.sq_sqrt]
    exact Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun k _ => sq_nonneg (X l k)
  nlinarith [sq_abs (X i j), abs_nonneg (X i j), frobeniusNorm_nonneg X]

theorem continuous_nuclearNorm {n p : ℕ} :
    Continuous (nuclearNorm : Matrix (Fin n) (Fin p) ℝ → ℝ) := by
  apply continuous_iff_continuousAt.mpr
  intro X
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun Y : Matrix (Fin n) (Fin p) ℝ =>
      (p : ℝ) * frobeniusNorm (Y - X)) (𝓝 X) (𝓝 0) := by
    have hc : Continuous (fun Y : Matrix (Fin n) (Fin p) ℝ =>
        (p : ℝ) * frobeniusNorm (Y - X)) :=
      continuous_const.mul (continuous_frobeniusNorm.comp (continuous_id.sub continuous_const))
    simpa only [sub_self, (frobeniusNorm_eq_zero_iff _).mpr rfl, mul_zero] using hc.tendsto X
  apply squeeze_zero (fun Y => norm_nonneg _) _ ht
  intro Y
  simpa only [Real.norm_eq_abs] using
    (nuclearNorm_sub_le Y X).trans (nuclearNorm_le_frobenius (Y - X))

theorem isCompact_nuclear_sublevel {n p : ℕ} (R : ℝ) :
    IsCompact {X : Matrix (Fin n) (Fin p) ℝ | nuclearNorm X ≤ R} := by
  have hc : IsClosed {X : Matrix (Fin n) (Fin p) ℝ | nuclearNorm X ≤ R} :=
    isClosed_le continuous_nuclearNorm continuous_const
  apply (isCompact_Icc : IsCompact (Set.Icc
    (fun _ : Fin n => fun _ : Fin p => -R) (fun _ => fun _ => R))).of_isClosed_subset hc
  intro X hX
  have hb : ∀ i j, |X i j| ≤ R := fun i j =>
    (entry_abs_le_frobeniusNorm X i j).trans ((frobeniusNorm_le_nuclearNorm X).trans hX)
  exact ⟨fun i j => (abs_le.mp (hb i j)).1, fun i j => (abs_le.mp (hb i j)).2⟩

theorem continuous_observationOp {n p m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin p) ℝ) : Continuous (observationOp A) := by
  unfold observationOp traceInner
  fun_prop

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

variable {n p m : ℕ} {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ}
  {K : ℕ} {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}

theorem run_epsilon_pos_of_positive_limit (hrun : IsRun A M K γ X ε)
    {e : ℝ} (he : 0 < e) (heps : Tendsto ε atTop (𝓝 e)) (j : ℕ) : 0 < ε j := by
  have hj : e ≤ ε j := le_of_tendsto heps (by
    filter_upwards [eventually_ge_atTop j] with l hl
    exact run_epsilon_antitone hrun hl)
  exact he.trans_le hj

theorem native_run_compact_range (hnp : n ≤ p) (hrun : IsRun A M K γ X ε)
    (hε : ∀ j, 0 < ε j) : ∃ S : Set (Matrix (Fin n) (Fin p) ℝ),
    IsCompact S ∧ ∀ j, X j ∈ S := by
  refine ⟨{Z | nuclearNorm Z ≤ max (nuclearNorm (X 0)) (Jeps (ε 1) (X 1))},
    isCompact_nuclear_sublevel _, ?_⟩
  intro j
  change nuclearNorm (X j) ≤ max (nuclearNorm (X 0)) (Jeps (ε 1) (X 1))
  cases j with
  | zero => exact le_max_left _ _
  | succ j => exact (native_run_nuclear_bounded hnp hrun hε j).trans (le_max_right _ _)

theorem native_run_subsequence_compact (hnp : n ≤ p) (hrun : IsRun A M K γ X ε)
    (hε : ∀ j, 0 < ε j) (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ L : Matrix (Fin n) (Fin p) ℝ, Tendsto (X ∘ φ ∘ ψ) atTop (𝓝 L) := by
  let : FirstCountableTopology (Matrix (Fin n) (Fin p) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin p → ℝ))
  obtain ⟨S, hS, hmem⟩ := native_run_compact_range hnp hrun hε
  obtain ⟨L, _, ψ, hψ, hlim⟩ := hS.tendsto_subseq (fun j => hmem (φ j))
  exact ⟨ψ, hψ, L, hlim⟩

theorem native_cluster_feasible (hrun : IsRun A M K γ X ε)
    {L : Matrix (Fin n) (Fin p) ℝ} (hL : MapClusterPt L atTop X) :
    observationOp A L = M := by
  let : FirstCountableTopology (Matrix (Fin n) (Fin p) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin p → ℝ))
  obtain ⟨φ, hφ, hlim⟩ := hL.tendsto_subseq
  have hobs := (continuous_observationOp A).continuousAt.tendsto.comp hlim
  have hevent : ∀ᶠ j in atTop, observationOp A (X (φ j)) = M := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop 1)] with j hj
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : φ j ≠ 0)
    rw [hr]
    exact run_feasible_succ hrun r
  exact tendsto_nhds_unique hobs (tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm))

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem antitone_positive_zero_frequently_decreases {e : ℕ → ℝ}
    (he : Antitone e) (hp : ∀ j, 0 < e j) (hz : Tendsto e atTop (𝓝 0)) :
    ∃ᶠ j in atTop, e (j + 1) < e j := by
  by_contra hf
  have hv : ∀ᶠ j in atTop, ¬ e (j + 1) < e j := not_frequently.mp hf
  obtain ⟨N, hN⟩ := eventually_atTop.mp hv
  have hstep : ∀ j, N ≤ j → e (j + 1) = e j := by
    intro j hj
    exact le_antisymm (he (Nat.le_succ j)) (le_of_not_gt (hN j hj))
  have hc : ∀ r, e (N + r) = e N := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => exact (hstep (N + r) (Nat.le_add_right _ _)).trans ih
  have ht : Tendsto e atTop (𝓝 (e N)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with j hj
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact (hc r).symm
  have heq := tendsto_nhds_unique hz ht
  linarith [hp N]

theorem native_run_decrease_selection {n p m : ℕ}
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K γ X ε) (hp : ∀ j, 0 < ε j)
    (hz : Tendsto ε atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ (∀ j, 1 ≤ φ j) ∧
      ∀ j, ε (φ j) = γ * sv (X (φ j)) K := by
  have hf := antitone_positive_zero_frequently_decreases (run_epsilon_antitone hrun) hp hz
  obtain ⟨ψ, hψ, hdrop⟩ := subseq_forall_of_frequently (x := fun j : ℕ => j)
    (p := fun j => ε (j + 1) < ε j) tendsto_id hf
  refine ⟨fun j => ψ j + 1, tendsto_atTop_mono (fun j => Nat.le_succ (ψ j)) hψ,
    fun j => Nat.succ_pos (ψ j), ?_⟩
  intro j
  have hu := ((hrun.step (ψ j)).2 (ne_of_gt (hp _))).2
  have hd := hdrop j
  by_cases hs : γ * sv (X (ψ j + 1)) K ≤ ε (ψ j)
  · simpa only [min_eq_right hs] using hu
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hs))] at hu
    rw [hu] at hd
    exact (lt_irrefl _ hd).elim

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p l : ℕ}

noncomputable def leadingColumns (X : Matrix (Fin n) (Fin p) ℝ) (hl : l≤p) : Matrix (Fin p) (Fin l) ℝ :=
  fun i j => (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) i
    (orderedGramIndex p ⟨j.val,lt_of_lt_of_le j.isLt hl⟩)

theorem leadingColumns_orthonormal (X : Matrix (Fin n) (Fin p) ℝ) (hl : l≤p) :
    (leadingColumns X hl)ᵀ*leadingColumns X hl=1 := by
  ext i j
  have h := congrArg (fun C : Matrix (Fin p) (Fin p) ℝ =>
    C (orderedGramIndex p ⟨i.val,lt_of_lt_of_le i.isLt hl⟩)
      (orderedGramIndex p ⟨j.val,lt_of_lt_of_le j.isLt hl⟩)) (gramUnitary_transpose_mul X)
  simpa only [leadingColumns,Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,
    Equiv.apply_eq_iff_eq,Fin.mk.injEq,Fin.ext_iff] using h

theorem leadingColumns_gram (X : Matrix (Fin n) (Fin p) ℝ) (hl : l≤p) :
    (X*leadingColumns X hl)ᵀ*(X*leadingColumns X hl)=
      Matrix.diagonal (fun j : Fin l=>sv X j.val ^ 2) := by
  ext i j
  have h := congrArg (fun C : Matrix (Fin p) (Fin p) ℝ =>
    C (orderedGramIndex p ⟨i.val,lt_of_lt_of_le i.isLt hl⟩)
      (orderedGramIndex p ⟨j.val,lt_of_lt_of_le j.isLt hl⟩)) (gram_columns X)
  have hi : i.val<p := lt_of_lt_of_le i.isLt hl
  simpa only [leadingColumns,Matrix.mul_apply,Matrix.transpose_apply,Matrix.diagonal_apply,
    Equiv.apply_eq_iff_eq,Fin.mk.injEq,Fin.ext_iff,gramValue_ordered,sv,dif_pos hi] using h

theorem leadingColumns_expansion (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (hk : k<p)
    (v : Fin (k+1)→ℝ) :
    (sv X k)^2*(∑j,v j^2)≤∑i,((X*leadingColumns X (show k+1≤p by omega))*ᵥv) i^2 := by
  rw [sum_sq_mulVec,leadingColumns_gram]
  simp only [dotProduct,Matrix.mulVec_diagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj := sv_antitone X (show j.val≤k by omega)
  have h0 := sv_nonneg X k
  have h1 := sv_nonneg X j.val
  have hs : (sv X k)^2≤(sv X j.val)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (v j))
  nlinarith only [hm]

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix Module
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem exists_kernel_orthonormal (Z : Matrix (Fin n) (Fin p) ℝ) :
    ∃r : ℕ, ∃R : Matrix (Fin p) (Fin r) ℝ, Rᵀ*R=1 ∧ Z*R=0 ∧ r+Z.rank=p := by
  let L : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin Z
  let K := LinearMap.ker L
  let r := Module.finrank ℝ K
  let b : OrthonormalBasis (Fin r) ℝ K := stdOrthonormalBasis ℝ K
  let R : Matrix (Fin p) (Fin r) ℝ := fun i j => (b j).val i
  refine ⟨r,R,?_,?_,?_⟩
  · ext i j
    have h := b.inner_eq_ite i j
    change (∑k,(b i).val k*(b j).val k) = if i=j then 1 else 0
    simpa only [Submodule.coe_inner,PiLp.inner_apply,Real.inner_apply] using h
  · ext i j
    have h := (b j).property
    change L (b j).val=0 at h
    have hv := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    exact hv
  · have h := L.finrank_range_add_finrank_ker
    have hr : Z.rank=Module.finrank ℝ (LinearMap.range L) := by
      exact Z.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin p) ℝ).toBasis
    rw [←hr,finrank_euclideanSpace,Fintype.card_fin] at h
    change Z.rank+r=p at h
    omega

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p r : ℕ}

theorem nuclearNorm_mul_contractive (X : Matrix (Fin n) (Fin p) ℝ)
    (Q : Matrix (Fin p) (Fin r) ℝ) (hQ : MatrixContractive Q) :
    nuclearNorm (X*Q)≤nuclearNorm X := by
  rw [←polarWitness_pairing (X*Q),traceInner_mul_right]
  exact contractive_pairing_le_nuclearNorm X
    (matrixContractive_mul (polarWitness_contractive (X*Q)) (matrixContractive_transpose hQ))

theorem orthogonal_column_square_sum (U : Matrix (Fin p) (Fin p) ℝ)
    (hU : Uᵀ*U=1) (j : Fin p) : ∑i,U i j^2=1 := by
  have h := congrArg (fun C : Matrix (Fin p) (Fin p) ℝ => C j j) hU
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,pow_two] using h

theorem nuclearNorm_lower_of_expansion (X : Matrix (Fin n) (Fin p) ℝ) (s : ℝ) (_hs : 0 ≤ s)
    (hX : ∀v : Fin p→ℝ, s^2*(∑j,v j^2)≤∑i,(X*ᵥv) i^2) :
    (p:ℝ)*s≤nuclearNorm X := by
  rw [nuclearNorm_eq_sum_gramValue]
  have hb : ∀j : Fin p,s≤gramValue X j := by
    intro j
    have hv := orthogonal_column_square_sum (gramUnitary X) (gramUnitary_transpose_mul X) j
    have he := hX (fun i => (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) i j)
    rw [hv,mul_one] at he
    have hcol : X*ᵥ(fun i=>(gramUnitary X : Matrix (Fin p) (Fin p) ℝ) i j)=
        fun i=>(X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j := by rfl
    rw [hcol] at he
    change s^2 ≤ ∑i,(X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j^2 at he
    rw [gram_column_square_sum] at he
    nlinarith [gramValue_nonneg X j]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _=>hb j)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem rank_approximation_tail (X Z : Matrix (Fin n) (Fin p) ℝ) (K k : ℕ)
    (hZ : Z.rank≤k) : ((K+1-k : ℕ):ℝ)*sv X K≤nuclearNorm (X-Z) := by
  by_cases hK : K<p
  · let Q := leadingColumns X (show K+1≤p by omega)
    have hQ : Qᵀ*Q=1 := leadingColumns_orthonormal X _
    obtain ⟨r,R,hR,hZR,hr⟩ := exists_kernel_orthonormal (Z*Q)
    have hrank : (Z*Q).rank≤k := (Matrix.rank_mul_le_left Z Q).trans hZ
    have hdim : K+1-k≤r := by omega
    let T : Matrix (Fin p) (Fin r) ℝ := Q*R
    have hT : Tᵀ*T=1 := by
      dsimp [T]
      rw [Matrix.transpose_mul]
      calc
        Rᵀ*Qᵀ*(Q*R) = Rᵀ*(Qᵀ*Q)*R := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQ,Matrix.mul_one,hR]
    have hXT : (X-Z)*T=(X*Q)*R := by
      dsimp [T]
      rw [Matrix.sub_mul,←Matrix.mul_assoc,←Matrix.mul_assoc,hZR,sub_zero]
    have hlow : (r:ℝ)*sv X K≤nuclearNorm ((X-Z)*T) := by
      apply nuclearNorm_lower_of_expansion _ _ (sv_nonneg X K)
      intro v
      have he := leadingColumns_expansion X K hK (R*ᵥv)
      have hn : ∑j,(R*ᵥv) j^2=∑j,v j^2 := by
        rw [sum_sq_mulVec,hR,Matrix.one_mulVec]
        simp only [dotProduct,pow_two]
      rw [hn] at he
      rw [hXT,←Matrix.mulVec_mulVec]
      exact he
    have hupper := nuclearNorm_mul_contractive (X-Z) T (matrixContractive_of_orthonormal T hT)
    have hcast : ((K+1-k:ℕ):ℝ)≤(r:ℝ) := by exact_mod_cast hdim
    exact (mul_le_mul_of_nonneg_right hcast (sv_nonneg X K)).trans (hlow.trans hupper)
  · have hz : sv X K=0 := by simp [sv,hK]
    rw [hz,mul_zero]
    exact nuclearNorm_nonneg _

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped BigOperators
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

noncomputable def gramTruncate (X : Matrix (Fin n) (Fin p) ℝ) (K : ℕ) : Matrix (Fin n) (Fin p) ℝ :=
  X * (gramUnitary X : Matrix (Fin p) (Fin p) ℝ) *
    Matrix.diagonal (fun j => if ((orderedGramIndex p).symm j).val<K then (1:ℝ) else 0) *
      (gramUnitary X : Matrix (Fin p) (Fin p) ℝ)ᵀ

theorem gramTruncate_rank (X : Matrix (Fin n) (Fin p) ℝ) (K : ℕ) : (gramTruncate X K).rank≤K := by
  classical
  let D : Matrix (Fin p) (Fin p) ℝ := Matrix.diagonal
    (fun j => if ((orderedGramIndex p).symm j).val<K then (1:ℝ) else 0)
  have hd : D.rank≤K := by
    rw [Matrix.rank_diagonal]
    let f : {j : Fin p // (if ((orderedGramIndex p).symm j).val<K then (1:ℝ) else 0)≠0} → Fin K :=
      fun j=>⟨((orderedGramIndex p).symm j.val).val,by
        by_contra h
        exact j.property (if_neg h)⟩
    have hi : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply (orderedGramIndex p).symm.injective
      apply Fin.ext
      exact congrArg (fun z : Fin K=>z.val) h
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hi
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ D).trans hd)

theorem gramTruncate_residual_coordinates (X : Matrix (Fin n) (Fin p) ℝ) (K : ℕ) :
    (X-gramTruncate X K)*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ) =
      X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)*
        Matrix.diagonal (fun j=>if ((orderedGramIndex p).symm j).val<K then (0:ℝ) else 1) := by
  have ht : gramTruncate X K*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ) =
      X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)*
        Matrix.diagonal (fun j=>if ((orderedGramIndex p).symm j).val<K then (1:ℝ) else 0) := by
    unfold gramTruncate
    rw [Matrix.mul_assoc,gramUnitary_transpose_mul,Matrix.mul_one]
  rw [Matrix.sub_mul,ht]
  ext i j
  simp only [Matrix.sub_apply,Matrix.mul_diagonal]
  split_ifs <;> ring

theorem gramTruncate_error_sq (X : Matrix (Fin n) (Fin p) ℝ) (K : ℕ) :
    frobeniusNorm (X-gramTruncate X K)^2≤(p:ℝ)*(sv X K)^2 := by
  rw [frobeniusNorm_sq,←traceInner_mul_orthogonal (X-gramTruncate X K) (X-gramTruncate X K) _
    (gramUnitary_mul_transpose X),gramTruncate_residual_coordinates]
  simp only [traceInner,Matrix.mul_diagonal]
  rw [Finset.sum_comm]
  have hs : (∑j,∑i,((X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j*
      (if ((orderedGramIndex p).symm j).val<K then (0:ℝ) else 1)) *
      ((X*(gramUnitary X : Matrix (Fin p) (Fin p) ℝ)) i j*
      (if ((orderedGramIndex p).symm j).val<K then (0:ℝ) else 1))) ≤
      ∑ _j : Fin p,(sv X K)^2 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : ((orderedGramIndex p).symm j).val<K
    · simp only [if_pos hj,mul_zero,Finset.sum_const_zero]
      exact sq_nonneg _
    · simp only [if_neg hj,mul_one,←pow_two]
      rw [gram_column_square_sum]
      have he : gramValue X j=sv X ((orderedGramIndex p).symm j).val := by
        have h := gramValue_ordered X ((orderedGramIndex p).symm j)
        simpa only [Equiv.apply_symm_apply,sv,dif_pos ((orderedGramIndex p).symm j).isLt] using h
      rw [he]
      have hm := sv_antitone X (show K≤((orderedGramIndex p).symm j).val by omega)
      nlinarith [sv_nonneg X K,sv_nonneg X ((orderedGramIndex p).symm j).val]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hs

theorem gramTruncate_error_nuclear (X : Matrix (Fin n) (Fin p) ℝ) (K : ℕ) :
    nuclearNorm (X-gramTruncate X K)≤(p:ℝ)*Real.sqrt p*sv X K := by
  have hsq := gramTruncate_error_sq X K
  have hs := Real.sq_sqrt (Nat.cast_nonneg p : (0:ℝ)≤p)
  have hf : frobeniusNorm (X-gramTruncate X K)≤Real.sqrt p*sv X K := by
    nlinarith [frobeniusNorm_nonneg (X-gramTruncate X K),Real.sqrt_nonneg (p:ℝ),
      sv_nonneg X K,mul_nonneg (Real.sqrt_nonneg (p:ℝ)) (sv_nonneg X K)]
  exact (nuclearNorm_le_frobenius _).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg p))

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem sv_le_nuclear_difference (X Y : Matrix (Fin n) (Fin p) ℝ) (K : ℕ) :
    sv X K≤nuclearNorm (X-Y)+(p:ℝ)*Real.sqrt p*sv Y K := by
  have ht := rank_approximation_tail X (gramTruncate Y K) K K (gramTruncate_rank Y K)
  have hk : K+1-K=1 := by omega
  rw [hk,Nat.cast_one,one_mul] at ht
  have he : X-gramTruncate Y K=(X-Y)+(Y-gramTruncate Y K) := by abel
  rw [he] at ht
  exact ht.trans ((nuclearNorm_triangle _ _).trans
    (add_le_add le_rfl (gramTruncate_error_nuclear Y K)))

theorem rank_le_of_tendsto_sv_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    (X : ι→Matrix (Fin n) (Fin p) ℝ) (L : Matrix (Fin n) (Fin p) ℝ) (K : ℕ)
    (hX : Tendsto X l (𝓝 L)) (hsv : Tendsto (fun j=>sv (X j) K) l (𝓝 0)) : L.rank≤K := by
  have hd : Tendsto (fun j=>nuclearNorm (L-X j)) l (𝓝 0) := by
    have hm : Tendsto (fun j=>L-X j) l (𝓝 (L-L)) := tendsto_const_nhds.sub hX
    have h := (continuous_nuclearNorm.tendsto (L-L)).comp hm
    have hz : nuclearNorm (0 : Matrix (Fin n) (Fin p) ℝ)=0 := (nuclearNorm_eq_zero_iff _).mpr rfl
    simpa only [sub_self,hz,Function.comp_def] using h
  have hb : Tendsto (fun j=>nuclearNorm (L-X j)+(p:ℝ)*Real.sqrt p*sv (X j) K) l (𝓝 0) := by
    simpa only [mul_zero,add_zero] using hd.add (hsv.const_mul ((p:ℝ)*Real.sqrt p))
  have hz : sv L K≤0 := ge_of_tendsto hb (Filter.Eventually.of_forall fun j=>sv_le_nuclear_difference L (X j) K)
  exact rank_le_of_sv_eq_zero L K (le_antisymm hz (sv_nonneg L K))

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem native_zero_parameter_rank_cluster {n p m : ℕ} (hn : 0 < n) (hnp : n ≤ p)
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K (1 / (n : ℝ)) X ε) (hp : ∀ j, 0 < ε j)
    (heps : Tendsto ε atTop (𝓝 0)) :
    ∃ L : Matrix (Fin n) (Fin p) ℝ, L.rank ≤ K ∧ MapClusterPt L atTop X := by
  let : FirstCountableTopology (Matrix (Fin n) (Fin p) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin p → ℝ))
  obtain ⟨φ, hφ, _, heq⟩ := native_run_decrease_selection hrun hp heps
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hval : ∀ j, sv (X (φ j)) K = (n : ℝ) * ε (φ j) := by
    intro j
    rw [heq j]
    field_simp
  have hsv : Tendsto (fun j => sv (X (φ j)) K) atTop (𝓝 0) := by
    have h := (heps.comp hφ).const_mul (n : ℝ)
    simpa only [Function.comp_def, ← hval, mul_zero] using h
  obtain ⟨S, hS, hmem⟩ := native_run_compact_range hnp hrun hp
  obtain ⟨L, _, ψ, hψ, hlim⟩ := hS.tendsto_subseq (fun j => hmem (φ j))
  have hrank := rank_le_of_tendsto_sv_zero (fun j => X (φ (ψ j))) L K hlim
    (hsv.comp hψ.tendsto_atTop)
  refine ⟨L, hrank, ?_⟩
  exact hlim.mapClusterPt.of_comp (hφ.comp hψ.tendsto_atTop)

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem native_zero_parameter_norm_limit {n p m : ℕ} (hnp : n ≤ p)
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K γ X ε) (hε : ∀ j, 0 < ε j)
    (heps : Tendsto ε atTop (𝓝 0)) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun j => nuclearNorm (X j)) atTop (𝓝 L) := by
  obtain ⟨L, hL, hE⟩ := antitone_nonneg_limit (native_run_energy_antitone hnp hrun hε)
    (fun j => (nuclearNorm_nonneg _).trans
      (native_smoothing_sandwich hnp (X (j + 1)) (hε (j + 1))).1)
  have heps' : Tendsto (fun j => ε (j + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr heps
  have hb : Tendsto (fun j => (n : ℝ) * ε (j + 1) / 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (tendsto_const_nhds.mul heps').div_const 2
  have hd : Tendsto (fun j => Jeps (ε (j + 1)) (X (j + 1)) -
      nuclearNorm (X (j + 1))) atTop (𝓝 0) := by
    apply squeeze_zero _ _ hb
    · intro j
      exact sub_nonneg.mpr (native_smoothing_sandwich hnp _ (hε (j + 1))).1
    · intro j
      have h := (native_smoothing_sandwich hnp (X (j + 1)) (hε (j + 1))).2
      linarith
  refine ⟨L, hL, (tendsto_add_atTop_iff_nat 1).mp ?_⟩
  have h := hE.sub hd
  simpa only [sub_sub_cancel, sub_zero] using h

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

private theorem rho_nuclear_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) :
    0 ≤ nuclearNorm X := by
  unfold nuclearNorm singularValues
  exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem rho_set_nonempty {n p : ℕ} (k : ℕ) (X : Matrix (Fin n) (Fin p) ℝ) :
    ((fun Z : Matrix (Fin n) (Fin p) ℝ => nuclearNorm (X - Z)) ''
      {Z : Matrix (Fin n) (Fin p) ℝ | Z.rank ≤ k}).Nonempty := by
  refine ⟨nuclearNorm (X - 0), 0, ?_, rfl⟩
  simp

theorem rho_set_bddBelow {n p : ℕ} (k : ℕ) (X : Matrix (Fin n) (Fin p) ℝ) :
    BddBelow ((fun Z : Matrix (Fin n) (Fin p) ℝ => nuclearNorm (X - Z)) ''
      {Z : Matrix (Fin n) (Fin p) ℝ | Z.rank ≤ k}) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨Z, _, rfl⟩
  exact rho_nuclear_nonneg _

theorem rho_nonneg {n p : ℕ} (k : ℕ) (X : Matrix (Fin n) (Fin p) ℝ) :
    0 ≤ rho k X := by
  apply le_csInf (rho_set_nonempty k X)
  rintro _ ⟨Z, _, rfl⟩
  exact rho_nuclear_nonneg _

theorem rho_le_approximation {n p : ℕ} {k : ℕ} (X Z : Matrix (Fin n) (Fin p) ℝ)
    (hZ : Z.rank ≤ k) : rho k X ≤ nuclearNorm (X - Z) :=
  csInf_le (rho_set_bddBelow k X) ⟨Z, hZ, rfl⟩

theorem le_rho_of_le_approximations {n p : ℕ} {k : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    {a : ℝ} (h : ∀ Z : Matrix (Fin n) (Fin p) ℝ,
      Z.rank ≤ k → a ≤ nuclearNorm (X - Z)) : a ≤ rho k X := by
  apply le_csInf (rho_set_nonempty k X)
  rintro _ ⟨Z, hZ, rfl⟩
  exact h Z hZ

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

theorem srnsp_comparison_approximation {n p m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin p) ℝ) {K : ℕ} {η : ℝ}
    (hS : SRNSP A K η) (X Y Z : Matrix (Fin n) (Fin p) ℝ)
    (hXY : observationOp A X = observationOp A Y) (hZ : Z.rank ≤ K)
    (hne : X - Y ≠ 0) :
    (1 - η) * nuclearNorm (X - Y) ≤
      (1 + η) * (nuclearNorm Y - nuclearNorm X + 2 * nuclearNorm (X - Z)) := by
  have hker : observationOp A (X - Y) = 0 := by rw [observationOp_sub, hXY, sub_self]
  obtain ⟨H₁, H₂, hsplit, _, _, hleft, hright, hsmall⟩ :=
    hS.2.2 (X - Y) hker hne Z (X - Y - Z) (by abel) hZ
  have ht := nuclearNorm_triangle H₁ H₂
  rw [← hsplit] at ht
  have hsum : nuclearNorm (X - Y) ≤ (1 + η) * nuclearNorm H₂ := by nlinarith
  have horth : nuclearNorm (Z - H₂) = nuclearNorm Z + nuclearNorm H₂ := by
    have h1 : Z * (-H₂)ᵀ = 0 := by rw [Matrix.transpose_neg, Matrix.mul_neg, hleft, neg_zero]
    have h2 : Zᵀ * (-H₂) = 0 := by rw [Matrix.mul_neg, hright, neg_zero]
    simpa only [sub_eq_add_neg, nuclearNorm_neg] using orthogonal_nuclear_add Z (-H₂) h1 h2
  have hh : H₂ = X - Y - H₁ := by rw [hsplit]; abel
  have hdecomp : Z - H₂ = Y + H₁ - (X - Z) := by rw [hh]; abel
  have ht1 := nuclearNorm_triangle (Y + H₁) (-(X - Z))
  have ht2 := nuclearNorm_triangle Y H₁
  rw [nuclearNorm_neg, ← sub_eq_add_neg, ← hdecomp, horth] at ht1
  have ht3 := nuclearNorm_triangle Z (X - Z)
  have hid : Z + (X - Z) = X := by abel
  rw [hid] at ht3
  have hgap : (1 - η) * nuclearNorm H₂ ≤
      nuclearNorm Y - nuclearNorm X + 2 * nuclearNorm (X - Z) := by nlinarith
  have hη := hS.1
  have hη1 := hS.2.1
  have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 - η by linarith)
  have hg := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 1 + η by linarith)
  nlinarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

private theorem comparison_nuclear_zero {n p : ℕ} :
    nuclearNorm (0 : Matrix (Fin n) (Fin p) ℝ) = 0 := by
  rw [nuclearNorm_eq_trace_sqrt]
  simp

theorem rho_eq_zero_of_rank_le {n p : ℕ} {k : ℕ}
    (X : Matrix (Fin n) (Fin p) ℝ) (hX : X.rank ≤ k) : rho k X = 0 := by
  apply le_antisymm _ (rho_nonneg k X)
  have h := rho_le_approximation X X hX
  simpa only [sub_self, comparison_nuclear_zero] using h

theorem srnsp_inverse_triangle {n p m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin p) ℝ) {K k : ℕ} {η : ℝ}
    (hS : SRNSP A K η) (hk : k ≤ K) (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hXY : observationOp A X = observationOp A Y) :
    nuclearNorm (X - Y) ≤ (1 + η) / (1 - η) *
      (nuclearNorm Y - nuclearNorm X + 2 * rho k X) := by
  have hη := hS.1
  have hη1 := hS.2.1
  have he : 0 < 1 - η := by linarith
  have hp : 0 < 1 + η := by linarith
  by_cases hzero : X - Y = 0
  · have hsame : X = Y := sub_eq_zero.mp hzero
    subst Y
    simp only [sub_self, comparison_nuclear_zero, zero_add]
    exact mul_nonneg (div_nonneg hp.le he.le) (mul_nonneg (by norm_num) (rho_nonneg k X))
  have hr : (((1 - η) * nuclearNorm (X - Y)) / (1 + η) -
      (nuclearNorm Y - nuclearNorm X)) / 2 ≤ rho k X := by
    apply le_rho_of_le_approximations X
    intro Z hZ
    have hc := srnsp_comparison_approximation A hS X Y Z hXY (hZ.trans hk) hzero
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    have hh : ((1 - η) * nuclearNorm (X - Y)) / (1 + η) ≤
        nuclearNorm Y - nuclearNorm X + 2 * nuclearNorm (X - Z) :=
      (div_le_iff₀ hp).2 (by nlinarith [hc])
    linarith
  have hh := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hr
  have hd : (1 - η) * nuclearNorm (X - Y) ≤
      (1 + η) * (nuclearNorm Y - nuclearNorm X + 2 * rho k X) := by
    have ht : (1 - η) * nuclearNorm (X - Y) / (1 + η) ≤
        nuclearNorm Y - nuclearNorm X + 2 * rho k X := by linarith
    have hm := (div_le_iff₀ hp).mp ht
    nlinarith [hm]
  calc
    nuclearNorm (X - Y) ≤
        ((1 + η) * (nuclearNorm Y - nuclearNorm X + 2 * rho k X)) / (1 - η) :=
      (le_div_iff₀ he).2 (by nlinarith [hd])
    _ = _ := by ring

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

theorem srnsp_unique_recovery {n p m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin p) ℝ) {K : ℕ} {η : ℝ}
    (hS : SRNSP A K η) (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hX : X.rank ≤ K) (hXY : observationOp A X = observationOp A Y) (hne : Y ≠ X) :
    nuclearNorm X < nuclearNorm Y := by
  have h := srnsp_inverse_triangle A hS le_rfl X Y hXY
  rw [rho_eq_zero_of_rank_le X hX, mul_zero, add_zero] at h
  have hz : nuclearNorm (X - Y) ≠ 0 := by
    intro hh
    have he := (nuclearNorm_eq_zero_iff _).mp hh
    exact hne (sub_eq_zero.mp he).symm
  have hp : 0 < nuclearNorm (X - Y) := lt_of_le_of_ne (nuclearNorm_nonneg _) (Ne.symm hz)
  have hη := hS.1
  have hη1 := hS.2.1
  have ha : 0 < (1 + η) / (1 - η) := by positivity
  nlinarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem matrix_tendsto_zero_of_frobenius {ι : Type*} {l : Filter ι} {n p : ℕ}
    {X : ι → Matrix (Fin n) (Fin p) ℝ}
    (hX : Tendsto (fun j => frobeniusNorm (X j)) l (𝓝 0)) :
    Tendsto X l (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _) _ hX
  intro k
  simpa only [Real.norm_eq_abs] using entry_abs_le_frobeniusNorm (X k) i j

theorem frobenius_tendsto_zero_of_sq_bound {ι : Type*} {l : Filter ι} {n p : ℕ}
    {X : ι → Matrix (Fin n) (Fin p) ℝ} {b : ι → ℝ}
    (hb : Tendsto b l (𝓝 0)) (hbound : ∀ j, frobeniusNorm (X j) ^ 2 ≤ b j) :
    Tendsto (fun j => frobeniusNorm (X j)) l (𝓝 0) := by
  have hs : Tendsto (fun j => frobeniusNorm (X j) ^ 2) l (𝓝 0) :=
    squeeze_zero (fun j => sq_nonneg _) hbound hb
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (frobeniusNorm_nonneg _), Real.sqrt_zero] using hr

theorem continuous_trace_pairing {n p : ℕ} :
    Continuous (fun q : Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ =>
      traceInner q.1 q.2) := by
  unfold traceInner
  fun_prop

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem srnsp_convergence_of_nuclear_norms {n p m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ)
    {K : ℕ} {η : ℝ} (hS : SRNSP A K η)
    (L : Matrix (Fin n) (Fin p) ℝ) (hL : L.rank ≤ K) (hfL : observationOp A L = M)
    (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (hX : ∀ j, observationOp A (X j) = M)
    (hnorm : Tendsto (fun j => nuclearNorm (X j)) atTop (𝓝 (nuclearNorm L))) :
    Tendsto X atTop (𝓝 L) := by
  have hr : Tendsto (fun j => (1 + η) / (1 - η) * (nuclearNorm (X j) - nuclearNorm L))
      atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      (tendsto_const_nhds.mul (hnorm.sub tendsto_const_nhds) :
        Tendsto (fun j => (1 + η) / (1 - η) * (nuclearNorm (X j) - nuclearNorm L))
          atTop (𝓝 ((1 + η) / (1 - η) * (nuclearNorm L - nuclearNorm L))))
  have hb : ∀ j, frobeniusNorm (X j - L) ≤
      (1 + η) / (1 - η) * (nuclearNorm (X j) - nuclearNorm L) := by
    intro j
    have h := srnsp_inverse_triangle A hS le_rfl L (X j) (hfL.trans (hX j).symm)
    rw [rho_eq_zero_of_rank_le L hL, mul_zero, add_zero] at h
    have he : L - X j = -(X j - L) := by abel
    rw [he, nuclearNorm_neg] at h
    exact (frobeniusNorm_le_nuclearNorm _).trans h
  have hf : Tendsto (fun j => frobeniusNorm (X j - L)) atTop (𝓝 0) :=
    squeeze_zero (fun j => frobeniusNorm_nonneg _) hb hr
  have hz := matrix_tendsto_zero_of_frobenius hf
  have ht := hz.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (𝓝 L))
  simpa only [sub_add_cancel, zero_add] using ht

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem run_finite_stop_limit {n p m : ℕ}
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K γ X ε) (hγ : 0 < γ) (hstop : ∃ j, ε j = 0) :
    ∃ Z, Z.rank ≤ K ∧ observationOp A Z = M ∧ Tendsto X atTop (𝓝 Z) ∧
      Tendsto ε atTop (𝓝 0) := by
  let j := Nat.find hstop
  have hj : ε j = 0 := Nat.find_spec hstop
  have hj0 : j ≠ 0 := by
    intro hz
    rw [hz, hrun.eps_zero] at hj
    norm_num at hj
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hprev : ε r ≠ 0 := by
    intro hz
    have hm := Nat.find_min' hstop hz
    change j ≤ r at hm
    omega
  have hupdate := ((hrun.step r).2 hprev).2
  have hzero : sv (X j) K = 0 := by
    have hnon := sv_nonneg (X j) K
    by_contra hne
    have hsv : 0 < sv (X j) K := lt_of_le_of_ne hnon (Ne.symm hne)
    have heps : 0 < ε r := lt_of_le_of_ne (run_epsilon_nonneg hrun hγ.le r) (Ne.symm hprev)
    have hp : 0 < min (ε r) (γ * sv (X j) K) := lt_min heps (mul_pos hγ hsv)
    have he : ε j = min (ε r) (γ * sv (X j) K) := by simpa only [hr] using hupdate
    rw [← he, hj] at hp
    exact lt_irrefl 0 hp
  refine ⟨X j, rank_le_of_sv_eq_zero _ _ hzero, ?_, ?_, ?_⟩
  · simpa only [hr] using run_feasible_succ hrun r
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop j] with k hk
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact (run_frozen_tail hrun hj s).1.symm
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop j] with k hk
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact (run_frozen_tail hrun hj s).2.symm

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem zero_rows_run {p m : ℕ}
    {A : Fin m → Matrix (Fin 0) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {X : ℕ → Matrix (Fin 0) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K (1 / (0 : ℝ)) X ε) :
    observationOp A 0 = M ∧ Tendsto X atTop (𝓝 0) ∧ Tendsto ε atTop (𝓝 0) := by
  have hx : ∀ j, X j = 0 := fun _ => Subsingleton.elim _ _
  have hf := run_feasible_succ hrun 0
  rw [hx] at hf
  have he : ε 1 = 0 := by
    have h := ((hrun.step 0).2 (by rw [hrun.eps_zero]; norm_num)).2
    simpa [hrun.eps_zero] using h
  refine ⟨hf, ?_, ?_⟩
  · have heq : X = fun _ => 0 := funext hx
    rw [heq]
    exact tendsto_const_nhds
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with j hj
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact (run_frozen_tail hrun he r).2.symm

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem native_zero_branch {n p m : ℕ} (hnp : n ≤ p)
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K (1 / (n : ℝ)) X ε)
    (hS : ∃ η : ℝ, SRNSP A K η) (heps : Tendsto ε atTop (𝓝 0)) :
    ∃ L : Matrix (Fin n) (Fin p) ℝ, Tendsto X atTop (𝓝 L) ∧ L.rank ≤ K ∧
      observationOp A L = M ∧ ∀ Y, observationOp A Y = M → Y ≠ L →
        nuclearNorm L < nuclearNorm Y := by
  obtain ⟨η, hη⟩ := hS
  by_cases hn : n = 0
  · subst n
    have hrun0 : IsRun A M K (1 / (0 : ℝ)) X ε := by
      simpa only [Nat.cast_zero] using hrun
    obtain ⟨hf, hx, _⟩ := zero_rows_run hrun0
    refine ⟨0, hx, by simp, hf, ?_⟩
    intro Y _ hne
    exact (hne (Subsingleton.elim _ _)).elim
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hγ : 0 < 1 / (n : ℝ) := by positivity
  by_cases hs : ∃ j, ε j = 0
  · obtain ⟨L, hr, hf, hx, _⟩ := run_finite_stop_limit hrun hγ hs
    refine ⟨L, hx, hr, hf, ?_⟩
    intro Y hY hne
    exact srnsp_unique_recovery A hη L Y hr (hf.trans hY.symm) hne
  have hp : ∀ j, 0 < ε j := by
    intro j
    have hz : ε j ≠ 0 := fun h => hs ⟨j, h⟩
    exact lt_of_le_of_ne (run_epsilon_nonneg hrun hγ.le j) (Ne.symm hz)
  obtain ⟨L, hr, hcluster⟩ := native_zero_parameter_rank_cluster hnpos hnp hrun hp heps
  have hf := native_cluster_feasible hrun hcluster
  obtain ⟨c, _, hc⟩ := native_zero_parameter_norm_limit hnp hrun hp heps
  let : FirstCountableTopology (Matrix (Fin n) (Fin p) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin p → ℝ))
  obtain ⟨φ, hφ, hφL⟩ := hcluster.tendsto_subseq
  have hnormL := continuous_nuclearNorm.continuousAt.tendsto.comp hφL
  have heq : c = nuclearNorm L := tendsto_nhds_unique (hc.comp hφ.tendsto_atTop) hnormL
  rw [heq] at hc
  have htail := srnsp_convergence_of_nuclear_norms A M hη L hr hf
    (fun j => X (j + 1)) (run_feasible_succ hrun)
    ((tendsto_add_atTop_iff_nat 1).mpr hc)
  refine ⟨L, (tendsto_add_atTop_iff_nat 1).mp htail, hr, hf, ?_⟩
  intro Y hY hne
  exact srnsp_unique_recovery A hη L Y hr (hf.trans hY.symm) hne

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh
variable {n p : ℕ}

theorem left_gram_sqrt_eigenvalue_le_frobenius (X : Matrix (Fin n) (Fin p) ℝ) (j : Fin n) :
    Real.sqrt ((Matrix.posSemidef_self_mul_conjTranspose X).1.eigenvalues j) ≤ frobeniusNorm X := by
  have hp : (X*Xᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose X
  have hs : hp.1.eigenvalues j ≤ ∑i,hp.1.eigenvalues i :=
    Finset.single_le_sum (fun i _ => hp.eigenvalues_nonneg i) (Finset.mem_univ j)
  have htrace : Matrix.trace (X*Xᵀ)=∑i,hp.1.eigenvalues i := by
    simpa only [RCLike.ofReal_real_eq_id,id_eq] using hp.1.trace_eq_sum_eigenvalues
  rw [←htrace] at hs
  have ht : Matrix.trace (X*Xᵀ)=frobeniusNorm X^2 := by
    rw [Matrix.trace_mul_comm,
      ←traceInner_eq_trace,frobeniusNorm_sq]
  rw [ht] at hs
  change Real.sqrt (hp.1.eigenvalues j)≤frobeniusNorm X
  exact (Real.sqrt_le_iff).mpr ⟨frobeniusNorm_nonneg X,hs⟩

theorem weight_coercive_order (ε B : ℝ) (hε : 0<ε) (hB : 0<B)
    (X : Matrix (Fin n) (Fin p) ℝ) (hX : frobeniusNorm X≤B) (heB : ε≤B) :
    (weight ε X-B⁻¹•(1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  have hp : (X*Xᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose X
  rw [←real_cfc_const _ hp.1 B⁻¹]
  unfold weight
  rw [real_cfc_sub _ hp.1]
  apply real_cfc_posSemidef _ hp.1
  intro i
  have hi : Real.sqrt (hp.1.eigenvalues i)≤B := (left_gram_sqrt_eigenvalue_le_frobenius X i).trans hX
  have hd : 0 < max (Real.sqrt (hp.1.eigenvalues i)) ε := lt_of_lt_of_le hε (le_max_right _ _)
  exact sub_nonneg.mpr ((inv_le_inv₀ hB hd).2 (max_le hi heB))

theorem weight_square_upper_order (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ) :
    ((ε⁻¹)^2•(1 : Matrix (Fin n) (Fin n) ℝ)-(weight ε X)ᵀ*weight ε X).PosSemidef := by
  have hp : (X*Xᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose X
  have hw : (weight ε X)ᵀ=weight ε X := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (weight_posDef ε hε X).1.eq
  rw [hw,←real_cfc_const _ hp.1 ((ε⁻¹)^2)]
  unfold weight
  rw [real_cfc_mul _ hp.1,real_cfc_sub _ hp.1]
  apply real_cfc_posSemidef _ hp.1
  intro i
  have hd : 0 < max (Real.sqrt (hp.1.eigenvalues i)) ε := lt_of_lt_of_le hε (le_max_right _ _)
  have hi := (inv_le_inv₀ hd hε).2 (le_max_right (Real.sqrt (hp.1.eigenvalues i)) ε)
  have hn := inv_nonneg.mpr hd.le
  have hn' := inv_nonneg.mpr hε.le
  nlinarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh
variable {n p q : ℕ}

theorem weight_coercive_trace (ε B : ℝ) (hε : 0<ε) (hB : 0<B)
    (X : Matrix (Fin n) (Fin p) ℝ) (hX : frobeniusNorm X≤B) (heB : ε≤B)
    (H : Matrix (Fin n) (Fin q) ℝ) :
    B⁻¹*frobeniusNorm H^2≤traceInner H (weight ε X*H) := by
  have h := weighted_trace_nonneg (weight_coercive_order ε B hε hB X hX heB) H
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,traceInner_sub_right,
    traceInner_smul_right,←frobeniusNorm_sq] at h
  linarith

theorem weight_mul_frobenius_sq_le (ε : ℝ) (hε : 0<ε) (X : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin n) (Fin q) ℝ) :
    frobeniusNorm (weight ε X*H)^2≤(ε⁻¹)^2*frobeniusNorm H^2 := by
  have h := weighted_trace_nonneg (weight_square_upper_order ε hε X) H
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,traceInner_sub_right,
    traceInner_smul_right,←frobeniusNorm_sq] at h
  have he : traceInner H (((weight ε X)ᵀ*weight ε X)*H)=frobeniusNorm (weight ε X*H)^2 := by
    rw [frobeniusNorm_sq,traceInner_eq_trace,traceInner_eq_trace,Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [he] at h
  linarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem native_run_difference_frobenius {n p m : ℕ} (hnp : n ≤ p)
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K γ X ε) (hε : ∀ j, 0 < ε j) :
    Tendsto (fun j => frobeniusNorm (X j - X (j + 1))) atTop (𝓝 0) := by
  let B := max (Jeps (ε 1) (X 1)) 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let q := fun j => traceInner (X (j + 1) - X (j + 2))
    (weight (ε (j + 1)) (X (j + 1)) * (X (j + 1) - X (j + 2))) / 2
  have hq : Tendsto q atTop (𝓝 0) := native_run_gap_tendsto_zero hnp hrun hε
  have hb : Tendsto (fun j => (2 * B) * q j) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hq
  have hh : ∀ j, frobeniusNorm (X (j + 1) - X (j + 2)) ^ 2 ≤ (2 * B) * q j := by
    intro j
    have hx : frobeniusNorm (X (j + 1)) ≤ B :=
      (frobeniusNorm_le_nuclearNorm _).trans
        ((native_run_nuclear_bounded hnp hrun hε j).trans (le_max_left _ _))
    have he : ε (j + 1) ≤ B := by
      have hu := run_epsilon_antitone hrun (Nat.zero_le (j + 1))
      rw [hrun.eps_zero] at hu
      exact hu.trans (le_max_right _ _)
    have hc := weight_coercive_trace (ε (j + 1)) B (hε _) hB (X (j + 1)) hx he
      (X (j + 1) - X (j + 2))
    have hm := mul_le_mul_of_nonneg_left hc hB.le
    rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul] at hm
    dsimp [q]
    nlinarith [hm]
  have hf := frobenius_tendsto_zero_of_sq_bound hb hh
  exact (tendsto_add_atTop_iff_nat 1).mp hf

theorem native_run_asymptotic_regular {n p m : ℕ} (hnp : n ≤ p)
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K γ X ε) (hε : ∀ j, 0 < ε j) :
    Tendsto (fun j => X j - X (j + 1)) atTop (𝓝 0) :=
  matrix_tendsto_zero_of_frobenius (native_run_difference_frobenius hnp hrun hε)

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

private theorem pairing_add_left {n p : ℕ} (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (X + Y) Z = traceInner X Z + traceInner Y Z := by
  rw [traceInner_comm, traceInner_add_right, traceInner_comm Z X, traceInner_comm Z Y]

private theorem pairing_sub_left {n p : ℕ} (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (X - Y) Z = traceInner X Z - traceInner Y Z := by
  rw [traceInner_comm, traceInner_sub_right, traceInner_comm Z X, traceInner_comm Z Y]

private theorem pairing_smul_left {n p : ℕ} (a : ℝ) (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (a • X) Y = a * traceInner X Y := by
  rw [traceInner_comm, traceInner_smul_right, traceInner_comm Y X]

theorem variational_midpoint_identity {n p : ℕ} (ε : ℝ)
    (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Z) X -
        ε / 2 * frobeniusNorm ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Z) ^ 2 =
      (traceInner Y X - ε / 2 * frobeniusNorm Y ^ 2) / 2 +
      (traceInner Z X - ε / 2 * frobeniusNorm Z ^ 2) / 2 +
      ε / 8 * frobeniusNorm (Y - Z) ^ 2 := by
  simp only [frobeniusNorm_sq, pairing_add_left, pairing_sub_left, pairing_smul_left,
    traceInner_add_right, traceInner_sub_right, traceInner_smul_right]
  rw [traceInner_comm Z Y]
  ring

theorem contractive_variational_unique {n p : ℕ} {ε : ℝ} (hε : 0 < ε)
    (X : Matrix (Fin n) (Fin p) ℝ) {Y Z : Matrix (Fin n) (Fin p) ℝ}
    (hY : MatrixContractive Y) (hZ : MatrixContractive Z)
    (hy : ∀ T, MatrixContractive T → traceInner T X - ε / 2 * frobeniusNorm T ^ 2 ≤
      traceInner Y X - ε / 2 * frobeniusNorm Y ^ 2)
    (hz : ∀ T, MatrixContractive T → traceInner T X - ε / 2 * frobeniusNorm T ^ 2 ≤
      traceInner Z X - ε / 2 * frobeniusNorm Z ^ 2) : Y = Z := by
  have hm : MatrixContractive ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Z) :=
    convex_matrixContractive hY hZ (by norm_num) (by norm_num) (by norm_num)
  have hh := hy _ hm
  rw [variational_midpoint_identity] at hh
  have hyz := hy Z hZ
  have hzy := hz Y hY
  have hs : frobeniusNorm (Y - Z) ^ 2 = 0 := by
    nlinarith [sq_nonneg (frobeniusNorm (Y - Z))]
  have hf : frobeniusNorm (Y - Z) = 0 := by nlinarith
  exact sub_eq_zero.mp ((frobeniusNorm_eq_zero_iff _).mp hf)

end IRLSM.Convergence.IRLSFresh
end


section

open Filter Topology
namespace IRLSM.Convergence.IRLSFresh

/-- Continuity along sequences of unique maximizers, proved by compactness rather than
continuity of a chosen spectral representation. -/
theorem compact_argmax_tendsto {P E : Type*} [TopologicalSpace P]
    [TopologicalSpace E] [FirstCountableTopology E]
    {S : Set E} (hS : IsCompact S) {f : P → E → ℝ}
    (hf : Continuous (fun q : P × E => f q.1 q.2))
    {t : ℕ → P} {t₀ : P} (ht : Tendsto t atTop (𝓝 t₀))
    {z : ℕ → E} (hz : ∀ j, z j ∈ S)
    (hmax : ∀ j, ∀ y ∈ S, f (t j) y ≤ f (t j) (z j))
    {z₀ : E} (hunique : ∀ x ∈ S, (∀ y ∈ S, f t₀ y ≤ f t₀ x) → x = z₀) :
    Tendsto z atTop (𝓝 z₀) := by
  apply hS.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hz)
  intro x hx hcluster
  obtain ⟨φ, hφ, hzφ⟩ := hcluster.tendsto_subseq
  apply hunique x hx
  intro y hy
  have hleft : Tendsto (fun j => f (t (φ j)) y) atTop (𝓝 (f t₀ y)) := by
    have hp : Tendsto (fun j => (t (φ j), y)) atTop (𝓝 (t₀, y)) :=
      (ht.comp hφ.tendsto_atTop).prodMk_nhds tendsto_const_nhds
    exact (hf.tendsto (t₀, y)).comp hp
  have hright : Tendsto (fun j => f (t (φ j)) (z (φ j))) atTop (𝓝 (f t₀ x)) := by
    have hp : Tendsto (fun j => (t (φ j), z (φ j))) atTop (𝓝 (t₀, x)) :=
      (ht.comp hφ.tendsto_atTop).prodMk_nhds hzφ
    exact (hf.tendsto (t₀, x)).comp hp
  exact le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall fun j => hmax (φ j) y hy)

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem native_gradient_tendsto {n p : ℕ} (hnp : n ≤ p)
    {ε : ℕ → ℝ} {e : ℝ} (he : 0 < e) (hε : ∀ j, 0 < ε j)
    (heps : Tendsto ε atTop (𝓝 e))
    {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {L : Matrix (Fin n) (Fin p) ℝ}
    (hX : Tendsto X atTop (𝓝 L)) :
    Tendsto (fun j => weight (ε j) (X j) * X j) atTop (𝓝 (weight e L * L)) := by
  let : FirstCountableTopology (Matrix (Fin n) (Fin p) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin p → ℝ))
  let f : (ℝ × Matrix (Fin n) (Fin p) ℝ) → Matrix (Fin n) (Fin p) ℝ → ℝ :=
    fun q Y => traceInner Y q.2 - q.1 / 2 * frobeniusNorm Y ^ 2
  have hf : Continuous (fun q : (ℝ × Matrix (Fin n) (Fin p) ℝ) ×
      Matrix (Fin n) (Fin p) ℝ => f q.1 q.2) := by
    dsimp [f]
    unfold traceInner frobeniusNorm
    fun_prop
  have hmax : ∀ j, ∀ Y, MatrixContractive Y →
      f (ε j, X j) Y ≤ f (ε j, X j) (weight (ε j) (X j) * X j) := by
    intro j Y hY
    obtain ⟨_, heq, hupper⟩ := native_smoothed_variational (ε j) (hε j) (X j) hnp
    have hu := hupper Y hY
    dsimp [f]
    linarith
  have hL := native_smoothed_variational e he L hnp
  apply compact_argmax_tendsto isCompact_matrixContractive hf
    (heps.prodMk_nhds hX)
    (fun j => (native_smoothed_variational (ε j) (hε j) (X j) hnp).1)
    hmax
  intro Y hY hYm
  apply contractive_variational_unique he L hY hL.1
  · exact hYm
  · intro Z hZ
    have hu := hL.2.2 Z hZ
    have heq := hL.2.1
    linarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
open scoped MatrixOrder
namespace IRLSM.Convergence.IRLSFresh

theorem psd_sqrt_pairing {n p : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosSemidef) (X H : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (cfc Real.sqrt W * X) (cfc Real.sqrt W * H) = traceInner (W * X) H := by
  rw [← psd_sqrt_eq_cfc_real hW]
  have hb : (CFC.sqrt W)ᵀ = CFC.sqrt W := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg W).posSemidef.1.eq
  have hw : Wᵀ = W := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hW.1.eq
  simp only [traceInner_eq_trace, Matrix.transpose_mul, hb, hw]
  have he : (Xᵀ * CFC.sqrt W) * (CFC.sqrt W * H) = (Xᵀ * W) * H := by
    calc
      _ = Xᵀ * ((CFC.sqrt W * CFC.sqrt W) * H) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self W hW.nonneg, Matrix.mul_assoc]
  rw [he]

theorem native_run_stationarity {n p m : ℕ}
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K γ X ε) (hε : ∀ j, 0 < ε j)
    (j : ℕ) (H : Matrix (Fin n) (Fin p) ℝ) (hH : observationOp A H = 0) :
    traceInner (weight (ε (j + 1)) (X (j + 1)) * X (j + 2)) H = 0 := by
  let W := weight (ε (j + 1)) (X (j + 1))
  have hmin : ∀ Y, observationOp A Y = M →
      frobeniusNorm (cfc Real.sqrt W * X (j + 2)) ^ 2 ≤
        frobeniusNorm (cfc Real.sqrt W * Y) ^ 2 := by
    simpa only [Wseq] using ((hrun.step (j + 1)).2 (ne_of_gt (hε _))).1.2
  have h := weighted_minimum_orthogonal A M (cfc Real.sqrt W) (X (j + 2)) H
    (run_feasible_succ hrun (j + 1)) hH hmin
  rw [psd_sqrt_pairing (weight_posDef _ (hε (j + 1)) (X (j + 1))).posSemidef] at h
  exact h

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank
namespace IRLSM.Convergence.IRLSFresh

theorem native_stationary_minimum {n p m : ℕ} (hnp : n ≤ p)
    (A : Fin m → Matrix (Fin n) (Fin p) ℝ) {e : ℝ} (he : 0 < e)
    (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hXY : observationOp A X = observationOp A Y)
    (hstat : ∀ H, observationOp A H = 0 → traceInner (weight e X * X) H = 0) :
    Jeps e X ≤ Jeps e Y := by
  have hx := native_smoothed_variational e he X hnp
  have hy := native_smoothed_variational e he Y hnp
  have hu := hy.2.2 (weight e X * X) hx.1
  have hh : observationOp A (Y - X) = 0 := by rw [observationOp_sub, hXY, sub_self]
  have hz := hstat (Y - X) hh
  rw [traceInner_sub_right] at hz
  have heq := hx.2.1
  linarith

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

variable {n p m : ℕ} {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ}
  {K : ℕ} {γ : ℝ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}

theorem native_weighted_difference_zero (hnp : n ≤ p) (hrun : IsRun A M K γ X ε)
    {e : ℝ} (he : 0 < e) (heps : Tendsto ε atTop (𝓝 e)) :
    Tendsto (fun j => weight (ε j) (X j) * (X j - X (j + 1))) atTop (𝓝 0) := by
  have hε := run_epsilon_pos_of_positive_limit hrun he heps
  have hd := native_run_difference_frobenius hnp hrun hε
  have hb : Tendsto (fun j => ((ε j)⁻¹) ^ 2 * frobeniusNorm (X j - X (j + 1)) ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
      ((heps.inv₀ he.ne').pow 2).mul (hd.pow 2)
  apply matrix_tendsto_zero_of_frobenius
  exact frobenius_tendsto_zero_of_sq_bound hb
    (fun j => weight_mul_frobenius_sq_le (ε j) (hε j) (X j) (X j - X (j + 1)))

theorem native_positive_cluster_stationary (hnp : n ≤ p) (hrun : IsRun A M K γ X ε)
    {e : ℝ} (he : 0 < e) (heps : Tendsto ε atTop (𝓝 e))
    {L : Matrix (Fin n) (Fin p) ℝ} (hL : MapClusterPt L atTop X) :
    ∀ H, observationOp A H = 0 → traceInner (weight e L * L) H = 0 := by
  let : FirstCountableTopology (Matrix (Fin n) (Fin p) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin p → ℝ))
  have hε := run_epsilon_pos_of_positive_limit hrun he heps
  obtain ⟨φ, hφ, hlim⟩ := hL.tendsto_subseq
  have hg := native_gradient_tendsto hnp he (fun j => hε (φ j))
    (heps.comp hφ.tendsto_atTop) hlim
  have hd := (native_weighted_difference_zero hnp hrun he heps).comp hφ.tendsto_atTop
  have hn := hg.sub hd
  have heq : (fun j => weight (ε (φ j)) (X (φ j)) * X (φ j) -
      weight (ε (φ j)) (X (φ j)) * (X (φ j) - X (φ j + 1))) =
      (fun j => weight (ε (φ j)) (X (φ j)) * X (φ j + 1)) := by
    funext j
    rw [Matrix.mul_sub]
    abel
  change Tendsto (fun j => weight (ε (φ j)) (X (φ j)) * X (φ j) -
    weight (ε (φ j)) (X (φ j)) * (X (φ j) - X (φ j + 1))) atTop
    (𝓝 (weight e L * L - 0)) at hn
  rw [heq, sub_zero] at hn
  intro H hH
  have ht := continuous_trace_pairing.tendsto (weight e L * L, H) |>.comp
    (hn.prodMk_nhds tendsto_const_nhds)
  have hz : ∀ᶠ j in atTop, traceInner (weight (ε (φ j)) (X (φ j)) * X (φ j + 1)) H = 0 := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop 1)] with j hj
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : φ j ≠ 0)
    simpa only [hr] using native_run_stationarity hrun hε r H hH
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm))

theorem native_positive_cluster_minimum (hnp : n ≤ p) (hrun : IsRun A M K γ X ε)
    {e : ℝ} (he : 0 < e) (heps : Tendsto ε atTop (𝓝 e))
    {L : Matrix (Fin n) (Fin p) ℝ} (hL : MapClusterPt L atTop X) :
    observationOp A L = M ∧ ∀ Y, observationOp A Y = M → Jeps e L ≤ Jeps e Y := by
  have hf := native_cluster_feasible hrun hL
  refine ⟨hf, ?_⟩
  intro Y hY
  exact native_stationary_minimum hnp A he L Y (hf.trans hY.symm)
    (native_positive_cluster_stationary hnp hrun he heps hL)

end IRLSM.Convergence.IRLSFresh
end


section

namespace IRLSM.Convergence.IRLSFresh

theorem robust_denominator_pos {η : ℝ} {K k : ℕ} (_hη : 0 < η) (hη1 : η < 1)
    (hk : (k : ℝ) < K - 2 * η / (1 - η)) :
    0 < ((K : ℝ) - k) * (1 - η) - 2 * η := by
  have hd : 0 < 1 - η := sub_pos.mpr hη1
  have ht : 2 * η / (1 - η) < (K : ℝ) - k := by linarith
  have hm := (div_lt_iff₀ hd).mp ht
  nlinarith

theorem robust_rank_lt {η : ℝ} {K k : ℕ} (hη : 0 < η) (hη1 : η < 1)
    (hk : (k : ℝ) < K - 2 * η / (1 - η)) : k < K := by
  have hp : 0 < 2 * η / (1 - η) := by positivity
  exact_mod_cast (show (k : ℝ) < K by linarith)

theorem robust_scalar_bound {η u d R : ℝ} {K k : ℕ}
    (hη : 0 < η) (hη1 : η < 1)
    (hk : (k : ℝ) < K - 2 * η / (1 - η)) (hR : 0 ≤ R)
    (hfirst : d ≤ (1 + η) / (1 - η) * (u + 2 * R))
    (hsecond : ((K : ℝ) + 1 - k) * u ≤ d + R) :
    u ≤ (3 + η) * R / (((K : ℝ) - k) * (1 - η) - 2 * η) ∧
      d ≤ Lambda η K k * R := by
  let D := ((K : ℝ) - k) * (1 - η) - 2 * η
  have hD : 0 < D := robust_denominator_pos hη hη1 hk
  have he : 0 < 1 - η := sub_pos.mpr hη1
  have ha : 0 < (1 + η) / (1 - η) := by positivity
  have hf : (1 - η) * d ≤ (1 + η) * (u + 2 * R) := by
    have := mul_le_mul_of_nonneg_left hfirst he.le
    field_simp at this
    nlinarith
  have hu : u ≤ (3 + η) * R / D := by
    apply (le_div_iff₀ hD).2
    have hs := mul_le_mul_of_nonneg_left hsecond he.le
    dsimp [D]
    nlinarith
  refine ⟨hu, ?_⟩
  have hd : d ≤ ((1 + η) / (1 - η) * (3 + η) / D +
      2 * ((1 + η) / (1 - η))) * R := by
    calc
      d ≤ (1 + η) / (1 - η) * (u + 2 * R) := hfirst
      _ ≤ (1 + η) / (1 - η) * ((3 + η) * R / D + 2 * R) :=
        mul_le_mul_of_nonneg_left (add_le_add hu le_rfl) ha.le
      _ = _ := by ring
  have hc : (1 + η) / (1 - η) * (3 + η) / D +
      2 * ((1 + η) / (1 - η)) ≤ Lambda η K k := by
    unfold Lambda
    change (1 + η) / (1 - η) * (3 + η) / D +
      2 * ((1 + η) / (1 - η)) ≤
      4 * (1 + η) ^ 2 / ((1 - η) ^ 2 * D) + 2 * (1 + η) / (1 - η)
    field_simp
    nlinarith [sq_nonneg η]
  exact hd.trans (mul_le_mul_of_nonneg_right hc hR)

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

variable {n p m : ℕ} {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ}
  {K : ℕ} {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}

theorem native_positive_cluster_tail (hn : 0 < n)
    (hrun : IsRun A M K (1 / (n : ℝ)) X ε)
    {e : ℝ} (heps : Tendsto ε atTop (𝓝 e))
    {L : Matrix (Fin n) (Fin p) ℝ} (hL : MapClusterPt L atTop X)
    (k : ℕ) (hk : k ≤ K) (Z : Matrix (Fin n) (Fin p) ℝ) (hZ : Z.rank ≤ k) :
    ((K : ℝ) + 1 - k) * ((n : ℝ) * e) ≤ nuclearNorm (L - Z) := by
  let : FirstCountableTopology (Matrix (Fin n) (Fin p) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin p → ℝ))
  obtain ⟨φ, hφ, hlim⟩ := hL.tendsto_subseq
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbound : ∀ j, 1 ≤ j → (n : ℝ) * ε j ≤ sv (X j) K := by
    intro j hj
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have h := run_epsilon_le_singular hrun (by positivity : 0 ≤ 1 / (n : ℝ)) r
    have hm := mul_le_mul_of_nonneg_left h hnpos.le
    field_simp at hm
    nlinarith [hm]
  have hb : 0 ≤ (K : ℝ) + 1 - k := by exact_mod_cast (show (0 : ℤ) ≤ (K : ℤ) + 1 - k by omega)
  have hl : Tendsto (fun j => ((K : ℝ) + 1 - k) * ((n : ℝ) * ε (φ j)))
      atTop (𝓝 (((K : ℝ) + 1 - k) * ((n : ℝ) * e))) :=
    ((heps.comp hφ.tendsto_atTop).const_mul (n : ℝ)).const_mul _
  have hr : Tendsto (fun j => nuclearNorm (X (φ j) - Z)) atTop (𝓝 (nuclearNorm (L - Z))) :=
    continuous_nuclearNorm.continuousAt.tendsto.comp (hlim.sub tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop 1)] with j hj
  have ht := rank_approximation_tail (X (φ j)) Z K k hZ
  have hcast : ((K + 1 - k : ℕ) : ℝ) = (K : ℝ) + 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [hcast] at ht
  exact (mul_le_mul_of_nonneg_left (hbound (φ j) hj) hb).trans ht

theorem native_positive_robust_bound (hnp : n ≤ p)
    (hrun : IsRun A M K (1 / (n : ℝ)) X ε)
    {e : ℝ} (he : 0 < e) (heps : Tendsto ε atTop (𝓝 e))
    {η : ℝ} (hS : SRNSP A K η)
    {L : Matrix (Fin n) (Fin p) ℝ} (hL : MapClusterPt L atTop X)
    (Y : Matrix (Fin n) (Fin p) ℝ) (hY : observationOp A Y = M)
    (k : ℕ) (hk : (k : ℝ) < K - 2 * η / (1 - η)) :
    nuclearNorm (Y - L) ≤ Lambda η K k * rho k Y := by
  by_cases hn : n = 0
  · subst n
    have hrun0 : IsRun A M K (1 / (0 : ℝ)) X ε := by
      simpa only [Nat.cast_zero] using hrun
    have hz := (zero_rows_run hrun0).2.2
    have heq := tendsto_nhds_unique heps hz
    linarith
  have hnpos := Nat.pos_of_ne_zero hn
  have hkK := (robust_rank_lt hS.1 hS.2.1 hk).le
  have hmin := native_positive_cluster_minimum hnp hrun he heps hL
  have hsand := native_smoothing_sandwich hnp Y he
  have hlow := (native_smoothing_sandwich hnp L he).1
  have hcost : nuclearNorm L - nuclearNorm Y ≤ (n : ℝ) * e := by
    have hm := hmin.2 Y hY
    have hne : 0 ≤ (n : ℝ) * e := by positivity
    linarith
  have hi := srnsp_inverse_triangle A hS hkK Y L (hY.trans hmin.1.symm)
  have ha : 0 ≤ (1 + η) / (1 - η) := by
    have hη := hS.1
    have hη1 := hS.2.1
    positivity
  have hfirst : nuclearNorm (Y - L) ≤
      (1 + η) / (1 - η) * ((n : ℝ) * e + 2 * rho k Y) :=
    hi.trans (mul_le_mul_of_nonneg_left (add_le_add hcost le_rfl) ha)
  have hsecond : ((K : ℝ) + 1 - k) * ((n : ℝ) * e) ≤ nuclearNorm (Y - L) + rho k Y := by
    have hr : ((K : ℝ) + 1 - k) * ((n : ℝ) * e) - nuclearNorm (Y - L) ≤ rho k Y := by
      apply le_rho_of_le_approximations Y
      intro Z hZ
      have ht := native_positive_cluster_tail hnpos hrun heps hL k hkK Z hZ
      have htri := nuclearNorm_triangle (L - Y) (Y - Z)
      have hid : (L - Y) + (Y - Z) = L - Z := by abel
      have hneg : L - Y = -(Y - L) := by abel
      rw [hid, hneg, nuclearNorm_neg] at htri
      linarith
    linarith
  exact (robust_scalar_bound hS.1 hS.2.1 hk (rho_nonneg k Y) hfirst hsecond).2

end IRLSM.Convergence.IRLSFresh
end


section

open Matrix HighDimStat.MatrixRank Filter Topology
namespace IRLSM.Convergence.IRLSFresh

theorem native_positive_unique_limit {n p m : ℕ} (hnp : n ≤ p)
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K (1 / (n : ℝ)) X ε)
    {e : ℝ} (he : 0 < e) (heps : Tendsto ε atTop (𝓝 e))
    (L : Matrix (Fin n) (Fin p) ℝ)
    (hunique : ∀ Z, observationOp A Z = M →
      (∀ Y, observationOp A Y = M → Jeps e Z ≤ Jeps e Y) → Z = L) :
    Tendsto X atTop (𝓝 L) := by
  have hp := run_epsilon_pos_of_positive_limit hrun he heps
  obtain ⟨S, hS, hmem⟩ := native_run_compact_range hnp hrun hp
  apply hS.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hmem)
  intro Z _ hZ
  have hm := native_positive_cluster_minimum hnp hrun he heps hZ
  exact hunique Z hm.1 hm.2

theorem native_epsilon_zero_of_low_rank {n p m : ℕ} (hnp : n ≤ p)
    {A : Fin m → Matrix (Fin n) (Fin p) ℝ} {M : Fin m → ℝ} {K : ℕ}
    {X : ℕ → Matrix (Fin n) (Fin p) ℝ} {ε : ℕ → ℝ}
    (hrun : IsRun A M K (1 / (n : ℝ)) X ε)
    {η : ℝ} (hS : SRNSP A K η) (k : ℕ)
    (hk : (k : ℝ) < K - 2 * η / (1 - η))
    (hsmall : ∃ Y : Matrix (Fin n) (Fin p) ℝ, Y.rank ≤ k ∧ observationOp A Y = M) :
    Tendsto ε atTop (𝓝 0) := by
  by_cases hn : n = 0
  · subst n
    have hrun0 : IsRun A M K (1 / (0 : ℝ)) X ε := by
      simpa only [Nat.cast_zero] using hrun
    exact (zero_rows_run hrun0).2.2
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨e, he0, heps⟩ := antitone_nonneg_limit (run_epsilon_antitone hrun)
    (run_epsilon_nonneg hrun (by positivity : 0 ≤ 1 / (n : ℝ)))
  have heq : e = 0 := by
    by_contra hne
    have he : 0 < e := lt_of_le_of_ne he0 (Ne.symm hne)
    have hp := run_epsilon_pos_of_positive_limit hrun he heps
    let : FirstCountableTopology (Matrix (Fin n) (Fin p) ℝ) :=
      inferInstanceAs (FirstCountableTopology (Fin n → Fin p → ℝ))
    obtain ⟨S, hc, hmem⟩ := native_run_compact_range hnp hrun hp
    obtain ⟨L, _, φ, hφ, hlim⟩ := hc.tendsto_subseq hmem
    have hL : MapClusterPt L atTop X := hlim.mapClusterPt.of_comp hφ.tendsto_atTop
    obtain ⟨Y, hr, hf⟩ := hsmall
    have hb := native_positive_robust_bound hnp hrun he heps hS hL Y hf k hk
    rw [rho_eq_zero_of_rank_le Y hr, mul_zero] at hb
    have hyL : Y = L := sub_eq_zero.mp ((nuclearNorm_eq_zero_iff _).mp
      (le_antisymm hb (nuclearNorm_nonneg _)))
    have hkK := (robust_rank_lt hS.1 hS.2.1 hk).le
    have ht := native_positive_cluster_tail hnpos hrun heps hL k hkK Y hr
    rw [hyL, sub_self, (nuclearNorm_eq_zero_iff _).mpr rfl] at ht
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hkR : (k : ℝ) ≤ K := by exact_mod_cast hkK
    have hcoef : 0 < (K : ℝ) + 1 - k := by linarith
    have hpos := mul_pos hcoef (mul_pos hnR he)
    linarith
  simpa only [heq] using heps

end IRLSM.Convergence.IRLSFresh
end


section

open HighDimStat.MatrixRank Matrix Filter Topology
namespace IRLSM.Convergence.IRLSFresh

/-- **Theorem 6.11.** Consider the IRLS-M algorithm with `γ = 1/n` and `K ∈ ℕ`, for a surjective
`S : M_{n×p} → ℝ^m` and data `𝓜`. The iterates `(X^ℓ)` satisfy:
(i) if `S` has the SRNSP of order `K` and `ε_ℓ → 0`, then `X^ℓ` converges to a matrix `X̄` of rank
at most `K` with `S(X̄) = 𝓜`, which is the unique nuclear norm minimizer;
(ii) if `ε_ℓ → ε > 0`, then every subsequence has a convergent subsequence, every accumulation
point is a minimizer of `𝒥_ε` subject to `S(X) = 𝓜`, the whole sequence converges if this
minimizer is unique; and if `S` has the SRNSP of order `K` with constant `η < 1 − 2/(K − 2)`, every
accumulation point `X̄` satisfies `‖X − X̄‖_* ≤ Λ ρ_k(X)_*` for every feasible `X` and every
`k < K − 2η/(1 − η)`;
(iii) under that SRNSP, if some feasible matrix has rank at most `k`, then `ε = 0`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Theorem 6.11, pp. 20–21.

Formalization Notes: real matrices; `S(X)_l = ⟨A_l, X⟩`; `n ≤ p` is the page's standing assumption
(p. 4); the run is `IsRun` (`X 0` free, `ε_j = 0` after a stop). `ε_ℓ` is nonincreasing and
nonnegative, so it always converges; "`lim ε_ℓ = ε`" is `Tendsto ε atTop (𝓝 e)`, and (iii)'s
"`ε = 0`" is `Tendsto ε atTop (𝓝 0)`. Accumulation points are `MapClusterPt`. In (ii)(d) the
page's `X` is `Y` and `X̄` is `Xt`; `Λ` is `Lambda η K k`. In (iii) `k` ranges over the same
`k < K − 2η/(1 − η)` as in (ii), which its proof uses. The condition `η < 1 − 2/(K − 2)` is kept
literally in `ℝ` (for `K ≤ 2` it is implied by `η < 1`, part of the SRNSP). The goal's "unique
nuclear norm minimizer" is the strict inequality `‖X̄‖_* < ‖Y‖_*` for every feasible `Y ≠ X̄`. -/
theorem native_theorem_6_11 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ) (K : ℕ)
    (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (ε : ℕ → ℝ) (hnp : n ≤ p)
    (_hS : Function.Surjective (observationOp A)) (hrun : IsRun A M K (1 / (n : ℝ)) X ε) :
    -- (i)
    ((∃ η : ℝ, SRNSP A K η) → Tendsto ε atTop (𝓝 0) →
      ∃ Xbar : Matrix (Fin n) (Fin p) ℝ, Tendsto X atTop (𝓝 Xbar) ∧ Xbar.rank ≤ K ∧
        observationOp A Xbar = M ∧
        ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Y ≠ Xbar →
          nuclearNorm Xbar < nuclearNorm Y) ∧
    -- (ii)
    (∀ e : ℝ, 0 < e → Tendsto ε atTop (𝓝 e) →
      (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ L : Matrix (Fin n) (Fin p) ℝ, Tendsto (X ∘ φ ∘ ψ) atTop (𝓝 L)) ∧
      (∀ Xt : Matrix (Fin n) (Fin p) ℝ, MapClusterPt Xt atTop X →
        observationOp A Xt = M ∧
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Xt ≤ Jeps e Y) ∧
      (∀ Xm : Matrix (Fin n) (Fin p) ℝ,
        (observationOp A Xm = M ∧
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Xm ≤ Jeps e Y) →
        (∀ Z : Matrix (Fin n) (Fin p) ℝ, observationOp A Z = M →
          (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Z ≤ Jeps e Y) →
            Z = Xm) →
        Tendsto X atTop (𝓝 Xm)) ∧
      (∀ η : ℝ, SRNSP A K η → η < 1 - 2 / ((K : ℝ) - 2) →
        ∀ Xt : Matrix (Fin n) (Fin p) ℝ, MapClusterPt Xt atTop X →
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M →
            ∀ k : ℕ, (k : ℝ) < K - 2 * η / (1 - η) →
              nuclearNorm (Y - Xt) ≤ Lambda η K k * rho k Y)) ∧
    -- (iii)
    (∀ η : ℝ, SRNSP A K η → η < 1 - 2 / ((K : ℝ) - 2) →
      ∀ k : ℕ, (k : ℝ) < K - 2 * η / (1 - η) →
        (∃ X₀ : Matrix (Fin n) (Fin p) ℝ, X₀.rank ≤ k ∧ observationOp A X₀ = M) →
          Tendsto ε atTop (𝓝 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hSR heps
    exact native_zero_branch hnp hrun hSR heps
  · intro e he heps
    have hp := run_epsilon_pos_of_positive_limit hrun he heps
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro φ _hφ
      exact native_run_subsequence_compact hnp hrun hp φ
    · intro Xt hXt
      exact native_positive_cluster_minimum hnp hrun he heps hXt
    · intro Xm _hXm huniq
      exact native_positive_unique_limit hnp hrun he heps Xm huniq
    · intro η hSR _hηK Xt hXt Y hY k hk
      exact native_positive_robust_bound hnp hrun he heps hSR hXt Y hY k hk
  · intro η hSR _hηK k hk hlow
    exact native_epsilon_zero_of_low_rank hnp hrun hSR k hk hlow

end IRLSM.Convergence.IRLSFresh

end


section

open HighDimStat.MatrixRank Matrix Filter Topology

namespace IRLSM.Convergence

/-- **Theorem 6.11.** Consider the IRLS-M algorithm with `γ = 1/n` and `K ∈ ℕ`, for a surjective
`S : M_{n×p} → ℝ^m` and data `𝓜`. The iterates `(X^ℓ)` satisfy:
(i) if `S` has the SRNSP of order `K` and `ε_ℓ → 0`, then `X^ℓ` converges to a matrix `X̄` of rank
at most `K` with `S(X̄) = 𝓜`, which is the unique nuclear norm minimizer;
(ii) if `ε_ℓ → ε > 0`, then every subsequence has a convergent subsequence, every accumulation
point is a minimizer of `𝒥_ε` subject to `S(X) = 𝓜`, the whole sequence converges if this
minimizer is unique; and if `S` has the SRNSP of order `K` with constant `η < 1 − 2/(K − 2)`, every
accumulation point `X̄` satisfies `‖X − X̄‖_* ≤ Λ ρ_k(X)_*` for every feasible `X` and every
`k < K − 2η/(1 − η)`;
(iii) under that SRNSP, if some feasible matrix has rank at most `k`, then `ε = 0`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Theorem 6.11, pp. 20–21.

Formalization Notes: real matrices; `S(X)_l = ⟨A_l, X⟩`; `n ≤ p` is the page's standing assumption
(p. 4); the run is `IsRun` (`X 0` free, `ε_j = 0` after a stop). `ε_ℓ` is nonincreasing and
nonnegative, so it always converges; "`lim ε_ℓ = ε`" is `Tendsto ε atTop (𝓝 e)`, and (iii)'s
"`ε = 0`" is `Tendsto ε atTop (𝓝 0)`. Accumulation points are `MapClusterPt`. In (ii)(d) the
page's `X` is `Y` and `X̄` is `Xt`; `Λ` is `Lambda η K k`. In (iii) `k` ranges over the same
`k < K − 2η/(1 − η)` as in (ii), which its proof uses. The condition `η < 1 − 2/(K − 2)` is kept
literally in `ℝ` (for `K ≤ 2` it is implied by `η < 1`, part of the SRNSP). The goal's "unique
nuclear norm minimizer" is the strict inequality `‖X̄‖_* < ‖Y‖_*` for every feasible `Y ≠ X̄`. -/
theorem theorem_6_11 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ) (K : ℕ)
    (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (ε : ℕ → ℝ) (hnp : n ≤ p)
    (hS : Function.Surjective (observationOp A)) (hrun : IsRun A M K (1 / (n : ℝ)) X ε) :
    -- (i)
    ((∃ η : ℝ, SRNSP A K η) → Tendsto ε atTop (𝓝 0) →
      ∃ Xbar : Matrix (Fin n) (Fin p) ℝ, Tendsto X atTop (𝓝 Xbar) ∧ Xbar.rank ≤ K ∧
        observationOp A Xbar = M ∧
        ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Y ≠ Xbar →
          nuclearNorm Xbar < nuclearNorm Y) ∧
    -- (ii)
    (∀ e : ℝ, 0 < e → Tendsto ε atTop (𝓝 e) →
      (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ L : Matrix (Fin n) (Fin p) ℝ, Tendsto (X ∘ φ ∘ ψ) atTop (𝓝 L)) ∧
      (∀ Xt : Matrix (Fin n) (Fin p) ℝ, MapClusterPt Xt atTop X →
        observationOp A Xt = M ∧
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Xt ≤ Jeps e Y) ∧
      (∀ Xm : Matrix (Fin n) (Fin p) ℝ,
        (observationOp A Xm = M ∧
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Xm ≤ Jeps e Y) →
        (∀ Z : Matrix (Fin n) (Fin p) ℝ, observationOp A Z = M →
          (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Z ≤ Jeps e Y) →
            Z = Xm) →
        Tendsto X atTop (𝓝 Xm)) ∧
      (∀ η : ℝ, SRNSP A K η → η < 1 - 2 / ((K : ℝ) - 2) →
        ∀ Xt : Matrix (Fin n) (Fin p) ℝ, MapClusterPt Xt atTop X →
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M →
            ∀ k : ℕ, (k : ℝ) < K - 2 * η / (1 - η) →
              nuclearNorm (Y - Xt) ≤ Lambda η K k * rho k Y)) ∧
    -- (iii)
    (∀ η : ℝ, SRNSP A K η → η < 1 - 2 / ((K : ℝ) - 2) →
      ∀ k : ℕ, (k : ℝ) < K - 2 * η / (1 - η) →
        (∃ X₀ : Matrix (Fin n) (Fin p) ℝ, X₀.rank ≤ k ∧ observationOp A X₀ = M) →
          Tendsto ε atTop (𝓝 0)) := by
  exact IRLSFresh.native_theorem_6_11 A M K X ε hnp hS hrun

end IRLSM.Convergence
end


open Matrix Filter Topology
theorem solution {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ) (K : ℕ)
    (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (ε : ℕ → ℝ) (hnp : n ≤ p)
    (hS : Function.Surjective (HighDimStat.MatrixRank.observationOp A)) (hrun : IRLSM.Convergence.IsRun A M K (1 / (n : ℝ)) X ε) :
    -- (i)
    ((∃ η : ℝ, IRLSM.Convergence.SRNSP A K η) → Tendsto ε atTop (𝓝 0) →
      ∃ Xbar : Matrix (Fin n) (Fin p) ℝ, Tendsto X atTop (𝓝 Xbar) ∧ Xbar.rank ≤ K ∧
        HighDimStat.MatrixRank.observationOp A Xbar = M ∧
        ∀ Y : Matrix (Fin n) (Fin p) ℝ, HighDimStat.MatrixRank.observationOp A Y = M → Y ≠ Xbar →
          HighDimStat.MatrixRank.nuclearNorm Xbar < HighDimStat.MatrixRank.nuclearNorm Y) ∧
    -- (ii)
    (∀ e : ℝ, 0 < e → Tendsto ε atTop (𝓝 e) →
      (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ L : Matrix (Fin n) (Fin p) ℝ, Tendsto (X ∘ φ ∘ ψ) atTop (𝓝 L)) ∧
      (∀ Xt : Matrix (Fin n) (Fin p) ℝ, MapClusterPt Xt atTop X →
        HighDimStat.MatrixRank.observationOp A Xt = M ∧
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, HighDimStat.MatrixRank.observationOp A Y = M → IRLSM.Convergence.Jeps e Xt ≤ IRLSM.Convergence.Jeps e Y) ∧
      (∀ Xm : Matrix (Fin n) (Fin p) ℝ,
        (HighDimStat.MatrixRank.observationOp A Xm = M ∧
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, HighDimStat.MatrixRank.observationOp A Y = M → IRLSM.Convergence.Jeps e Xm ≤ IRLSM.Convergence.Jeps e Y) →
        (∀ Z : Matrix (Fin n) (Fin p) ℝ, HighDimStat.MatrixRank.observationOp A Z = M →
          (∀ Y : Matrix (Fin n) (Fin p) ℝ, HighDimStat.MatrixRank.observationOp A Y = M → IRLSM.Convergence.Jeps e Z ≤ IRLSM.Convergence.Jeps e Y) →
            Z = Xm) →
        Tendsto X atTop (𝓝 Xm)) ∧
      (∀ η : ℝ, IRLSM.Convergence.SRNSP A K η → η < 1 - 2 / ((K : ℝ) - 2) →
        ∀ Xt : Matrix (Fin n) (Fin p) ℝ, MapClusterPt Xt atTop X →
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, HighDimStat.MatrixRank.observationOp A Y = M →
            ∀ k : ℕ, (k : ℝ) < K - 2 * η / (1 - η) →
              HighDimStat.MatrixRank.nuclearNorm (Y - Xt) ≤ IRLSM.Convergence.Lambda η K k * IRLSM.Convergence.rho k Y)) ∧
    -- (iii)
    (∀ η : ℝ, IRLSM.Convergence.SRNSP A K η → η < 1 - 2 / ((K : ℝ) - 2) →
      ∀ k : ℕ, (k : ℝ) < K - 2 * η / (1 - η) →
        (∃ X₀ : Matrix (Fin n) (Fin p) ℝ, X₀.rank ≤ k ∧ HighDimStat.MatrixRank.observationOp A X₀ = M) →
          Tendsto ε atTop (𝓝 0))  := by
  exact IRLSM.Convergence.theorem_6_11 A M K X ε hnp hS hrun
