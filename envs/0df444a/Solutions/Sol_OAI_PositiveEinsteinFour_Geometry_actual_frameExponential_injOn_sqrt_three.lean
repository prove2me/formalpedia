-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:45:53.13708+00:00
-- url     : https://prove2.me/submissions/decd62f8-9e33-4a53-96d4-ebd7786ae4c7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C030
import Definitions.Def_OAIQ091C031

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletVectorSequence
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The block Dirichlet operator on an actual vector sequence. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem scalarLift_mulVec {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin 3 × Fin N → ℝ) (a : Fin 3) (i : Fin N) :
    (scalarLift G *ᵥ x) (a,i) = (G *ᵥ fun j => x (a,j)) i := by
  simp [Matrix.mulVec, dotProduct, scalarLift, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.one_apply, Fintype.sum_prod_type]

theorem blockDiagonal_mulVec {N : ℕ} (D : Fin N → NormalMatrix)
    (x : Fin 3 × Fin N → ℝ) (a : Fin 3) (i : Fin N) :
    (Matrix.blockDiagonal D *ᵥ x) (a,i) = (D i *ᵥ fun b => x (b,i)) a := by
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]

theorem dirichletMatrix_eq_scalarLift {N : ℕ} (D : Fin N → NormalMatrix) :
    dirichletMatrix D = scalarLift (scalarDirichlet N 2) -
      Matrix.blockDiagonal (fun i => (2 : ℝ) • (1 : NormalMatrix) - D i) := by
  have h := scalarLift_sub_diagonal (N := N) 2 1
    (fun i => (2 : ℝ) • (1 : NormalMatrix) - D i)
  simpa only [one_smul, sub_sub_cancel] using h.symm

theorem dirichlet_mulVec_sequence {N : ℕ} (D : Fin N → NormalMatrix)
    (z : ℕ → Fin 3 → ℝ) (hzero : z 0 = 0) (hend : z (N + 1) = 0)
    (a : Fin 3) (i : Fin N) :
    (dirichletMatrix D *ᵥ fun p => z (p.2.val + 1) p.1) (a,i) =
      (D i *ᵥ z (i.val + 1)) a - z i.val a - z (i.val + 2) a := by
  rw [dirichletMatrix_eq_scalarLift, Matrix.sub_mulVec, Pi.sub_apply,
    scalarLift_mulVec, blockDiagonal_mulVec]
  have h := scalarDirichlet_apply_sequence 2 (fun n => z n a)
    (by rw [hzero]; rfl) (by rw [hend]; rfl) i
  rw [h, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletEndpointInvertible
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive discrete Dirichlet forms have nonsingular Jacobi endpoints. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem jacobi_endpoint_isUnit_of_dirichlet_posDef
    (D Y : ℕ → NormalMatrix) (N : ℕ)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef) :
    IsUnit (Y (N + 1)) := by
  have hker (v : Fin 3 → ℝ) (hv : Y (N + 1) *ᵥ v = 0) : v = 0 := by
    by_cases hN : N = 0
    · simpa [hN, h1] using hv
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let z : ℕ → Fin 3 → ℝ := fun i => Y i *ᵥ v
    let x : Fin 3 × Fin N → ℝ := fun p => z (p.2.val + 1) p.1
    have hz0 : z 0 = 0 := by simp [z,h0]
    have hzN : z (N + 1) = 0 := hv
    have hxzero : dirichletMatrix (fun i : Fin N => D i.val) *ᵥ x = 0 := by
      ext ⟨a,i⟩
      rw [show x = (fun p => z (p.2.val + 1) p.1) from rfl,
        dirichlet_mulVec_sequence _ z hz0 hzN]
      dsimp [z]
      rw [hrec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Pi.sub_apply]
      ring
    have hx : x = 0 := by
      by_contra hx
      have h := hpos.dotProduct_mulVec_pos hx
      rw [hxzero, dotProduct_zero] at h
      exact (lt_irrefl 0) h
    funext a
    have h := congrFun hx (a,⟨0,hNpos⟩)
    simpa [x,z,h1] using h
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have h : Y (N + 1) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hker (v - w) h)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletLeadingPositive
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the full discrete form controls every Jacobi endpoint. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem dirichlet_leading_posDef (D : ℕ → NormalMatrix) {n N : ℕ} (hn : n ≤ N)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef) :
    (dirichletMatrix (fun i : Fin n => D i.val)).PosDef := by
  let f : Fin 3 × Fin n → Fin 3 × Fin N := fun p => (p.1, Fin.castLE hn p.2)
  have hf : Function.Injective f := by
    intro p q h
    apply Prod.ext
    · exact congrArg (fun z : Fin 3 × Fin N => z.1) h
    · apply Fin.ext
      exact congrArg (fun z => z.2.val) h
  convert hpos.submatrix hf using 1
  all_goals try with_reducible_and_instances rfl
  ext ⟨a,i⟩ ⟨b,j⟩
  simp [dirichletMatrix, Matrix.submatrix, f]

theorem jacobi_prefix_isUnit_of_dirichlet_posDef
    (D Y : ℕ → NormalMatrix) (N : ℕ)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef)
    (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N + 1) : IsUnit (Y i) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact jacobi_endpoint_isUnit_of_dirichlet_posDef D Y n h0 h1 hrec
    (dirichlet_leading_posDef D (by omega) hpos)

theorem curvatureDirichlet_determinant_of_posDef {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix) (hsym : ∀ i, (R i)ᵀ = R i)
    (hpos : (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).PosDef) :
    (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).det =
      (normalizedDiscrete R (t / (N + 1)) (N + 1)).det := by
  let D := fun i => (2 : ℝ) • (1 : NormalMatrix) - (t / (N + 1)) ^ 2 • R (i + 1)
  have hD : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef := by
    simpa only [curvatureDirichlet_eq, add_sub_cancel] using hpos
  have hh : t / ((N : ℝ) + 1) ≠ 0 := div_ne_zero ht (by positivity)
  apply curvatureDirichlet_determinant ht R hsym
  intro i hi hiN
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (jacobi_prefix_isUnit_of_dirichlet_posDef D (normalizedDiscrete R (t / (N + 1))) N
      (normalizedDiscrete_zero _ _) (normalizedDiscrete_one _ hh)
      (normalizedDiscrete_recurrence R _) hD i hi hiN)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit positive Green kernel for the flat discrete Dirichlet operator. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

private theorem tent_second_difference (i j : ℕ) :
    2 * (min (i + 1) j : ℕ) - (min i j : ℕ) - (min (i + 2) j : ℕ) =
      (if i + 1 = j then (1 : ℝ) else 0) := by
  by_cases h : j ≤ i
  · have h1 : j ≤ i + 1 := by omega
    have h2 : j ≤ i + 2 := by omega
    have hn : i + 1 ≠ j := by omega
    simp only [min_eq_right h, min_eq_right h1, min_eq_right h2, ite_eq_right hn]
    ring
  · by_cases he : i + 1 = j
    · subst j
      simp only [min_eq_left (by omega : i ≤ i + 1), min_self,
        min_eq_right (by omega : i + 1 ≤ i + 2), ite_true, if_true, Nat.cast_add, Nat.cast_one]
      ring
    · have h2 : i + 2 ≤ j := by omega
      simp only [min_eq_left (by omega : i ≤ j), min_eq_left (by omega : i + 1 ≤ j),
        min_eq_left h2, ite_eq_right he, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      ring

theorem flatGreenValue_second_difference (N i j : ℕ) :
    2 * flatGreenValue N j (i + 1) - flatGreenValue N j i -
      flatGreenValue N j (i + 2) = if i + 1 = j then 1 else 0 := by
  have h := tent_second_difference i j
  simp only [flatGreenValue, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linear_combination h

theorem scalarDirichlet_mul_flatGreen (N : ℕ) : scalarDirichlet N 2 * flatGreen N = 1 := by
  ext i j
  have h0 : flatGreenValue N (j.val + 1) 0 = 0 := by simp [flatGreenValue]
  have hN : flatGreenValue N (j.val + 1) (N + 1) = 0 := by
    have hj : j.val + 1 ≤ N + 1 := by omega
    simp only [flatGreenValue, min_eq_right hj, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have h := scalarDirichlet_apply_sequence 2 (flatGreenValue N (j.val + 1)) h0 hN i
  change (scalarDirichlet N 2 *ᵥ fun k => flatGreenValue N (j.val + 1) (k.val + 1)) i = _
  rw [h, flatGreenValue_second_difference]
  by_cases hij : i = j
  · subst j
    simp
  · have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
    simp [hv, hij]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletNormalizer
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual square-root normalizer for the flat Green kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatDirichlet_posDef (N : ℕ) : (scalarDirichlet N 2).PosDef := by
  apply scalarDirichlet_posDef
  rw [two_sub_two_cos]
  have hx : 0 < firstSineAngle N / 2 := by unfold firstSineAngle; positivity
  have hxπ : firstSineAngle N / 2 < Real.pi := by
    unfold firstSineAngle
    rw [div_div, div_lt_iff₀ (by positivity : (0 : ℝ) < (N + 1) * 2)]
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [Real.pi_pos]
  exact mul_pos (by norm_num) (sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hx hxπ))

theorem flatGreen_eq_inverse (N : ℕ) : flatGreen N = (scalarDirichlet N 2)⁻¹ :=
  (Matrix.inv_eq_right_inv (scalarDirichlet_mul_flatGreen N)).symm

theorem flatGreenRoot_square (t : ℝ) (N : ℕ) :
    flatGreenRoot t N * flatGreenRoot t N = scaledFlatGreen t N := by
  rw [flatGreenRoot, scaledFlatGreen, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← pow_two, scalarNormalizer_square (flatDirichlet_posDef N),
    ← flatGreen_eq_inverse]

theorem flatGreenRoot_transpose (t : ℝ) (N : ℕ) :
    (flatGreenRoot t N)ᵀ = flatGreenRoot t N := by
  have h := (scalarNormalizer_posSemidef (scalarDirichlet N 2)).isHermitian.eq
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  simp only [flatGreenRoot, Matrix.transpose_smul, h]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletThreshold
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat perturbation is positive below pi/sqrt(3). -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped _root_.Topology
noncomputable section

theorem referenceMatrix_sqrt_three (t : ℝ) (N : ℕ) :
    referenceMatrix (Real.sqrt 3 * t) N = scalarDirichlet N 2 -
      (3 * (t / (N + 1)) ^ 2) • 1 := by
  have hs : (Real.sqrt 3 * t / (N + 1)) ^ 2 = 3 * (t / (N + 1)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), div_pow]
    ring
  ext i j
  simp only [referenceMatrix, scalarDirichlet, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, hs]
  by_cases hij : i = j <;> simp [hij]

theorem scaledFlatGreen_threshold_posDef (t : ℝ) (N : ℕ)
    (hRef : (referenceMatrix (Real.sqrt 3 * t) N).PosDef) :
    (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef := by
  let U := scalarNormalizer (scalarDirichlet N 2)
  have hu : U * scalarDirichlet N 2 * U = 1 :=
    scalarNormalizer_normalizes (flatDirichlet_posDef N)
  have hs : U * U = flatGreen N := by
    rw [flatGreen_eq_inverse]
    exact scalarNormalizer_square (flatDirichlet_posDef N)
  have ht : Uᴴ = U := (scalarNormalizer_posSemidef _).isHermitian.eq
  have hunit : IsUnit U := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse hu)
  have hp := hRef.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)
  rw [ht, referenceMatrix_sqrt_three] at hp
  have he : U * (scalarDirichlet N 2 - (3 * (t / (N + 1)) ^ 2) • 1) * U =
      1 - (3 : ℝ) • scaledFlatGreen t N := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hu, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hs, scaledFlatGreen, smul_smul]
  rwa [he] at hp

theorem scaledFlatGreen_eventually_below_one {t : ℝ} (ht : 0 ≤ t)
    (htop : t < Real.pi / Real.sqrt 3) :
    ∀ᶠ N : ℕ in atTop, (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef := by
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ hsqrt).mp htop
    nlinarith
  filter_upwards [firstEigenvalue_eventually_pos (mul_nonneg hsqrt.le ht) hlt] with N hN
  apply scaledFlatGreen_threshold_posDef t N
  exact scalarDirichlet_posDef N _ hN

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiCyclicPowers
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving the square-root factors in the finite Jacobi perturbation.
Only cyclicity of trace is used; curvature matrices are never commuted. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_one_sub_sandwich (S D : Matrix ι ι ℝ) :
    (1 - S * D * S).det = (1 - S * S * D).det := by
  rw [Matrix.det_one_sub_mul_comm (S * D) S, ← Matrix.mul_assoc]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSymmetricKernel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric realization of the positive Green-kernel perturbation. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem symmetricCurvatureKernel_det {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G)
    (R : Fin N → NormalMatrix) :
    (1 - symmetricCurvatureKernel S R).det = (1 - curvatureKernel G R).det := by
  rw [symmetricCurvatureKernel, det_one_sub_sandwich, ← scalarLift_mul, hS]
  rfl

theorem blockDiagonal_posSemidef {N : ℕ} (R : Fin N → NormalMatrix)
    (hR : ∀ i, (R i).PosSemidef) : (Matrix.blockDiagonal R).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (Matrix.blockDiagonal R).conjTranspose = Matrix.blockDiagonal R
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext i
    exact (hR i).isHermitian.eq
  · intro x
    rw [blockDiagonal_quadratic]
    exact Finset.sum_nonneg (fun i _ => (hR i).dotProduct_mulVec_nonneg _)

theorem scalarLift_conjTranspose {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : Sᵀ = S) : (scalarLift S)ᴴ = scalarLift S := by
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) b a * S j i = (1 : NormalMatrix) a b * S i j
  have hs : S j i = S i j := congrFun (congrFun hS i) j
  rw [hs]
  simp only [Matrix.one_apply, eq_comm]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiCurvatureCap
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the curvature perturbation below the scalar conjugate
threshold. The cap three follows from positivity and trace three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem three_sub_posSemidef {A : NormalMatrix} (hA : A.PosSemidef)
    (htr : A.trace = 3) : ((3 : ℝ) • (1 : NormalMatrix) - A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix U
  have hdiag : A = φ (diagonal hA.isHermitian.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.isHermitian.spectral_theorem
  have hsum : (∑ i, hA.isHermitian.eigenvalues i) = 3 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, htr] using
      hA.isHermitian.trace_eq_sum_eigenvalues.symm
  have hb (i : Fin 3) : hA.isHermitian.eigenvalues i ≤ 3 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hp : (diagonal (fun i => 3 - hA.isHermitian.eigenvalues i)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hb i))
  have hφ : φ (diagonal (fun i => 3 - hA.isHermitian.eigenvalues i)) =
      (3 : ℝ) • (1 : NormalMatrix) - A := by
    have he : diagonal (fun i => 3 - hA.isHermitian.eigenvalues i) =
        (3 : ℝ) • (1 : NormalMatrix) - diagonal hA.isHermitian.eigenvalues := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [he, map_sub, map_smul, map_one, ← hdiag]
  rw [← hφ]
  simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using
    hp.conjTranspose_mul_mul_same (star (U : NormalMatrix))

theorem scalarLift_quadratic {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin 3 × Fin N → ℝ) :
    star x ⬝ᵥ (scalarLift G *ᵥ x) =
      ∑ a : Fin 3, star (fun i => x (a,i)) ⬝ᵥ (G *ᵥ fun i => x (a,i)) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, scalarLift,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, star_trivial, Finset.mul_sum]
  simp

theorem scalarLift_posDef {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) : (scalarLift G).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply scalarLift_conjTranspose
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq
  · intro x hx
    rw [scalarLift_quadratic]
    have hn : ∃ a : Fin 3, (fun i => x (a,i)) ≠ 0 := by
      by_contra! h
      apply hx
      funext p
      exact congrFun (h p.1) p.2
    obtain ⟨a,ha⟩ := hn
    exact Finset.sum_pos' (fun b _ => hG.posSemidef.dotProduct_mulVec_nonneg _)
      ⟨a, Finset.mem_univ _, hG.dotProduct_mulVec_pos ha⟩

theorem scalarLift_sub_three {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    scalarLift (1 - (3 : ℝ) • G) = 1 - (3 : ℝ) • scalarLift G := by
  rw [← scalarLift_one N]
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) a b * ((1 : Matrix (Fin N) (Fin N) ℝ) i j - 3 * G i j) =
    (1 : NormalMatrix) a b * (1 : Matrix (Fin N) (Fin N) ℝ) i j -
      3 * ((1 : NormalMatrix) a b * G i j)
  ring

theorem symmetricCurvatureKernel_one_sub_posDef {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (hscalar : (1 - (3 : ℝ) • G).PosDef)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3) :
    (1 - symmetricCurvatureKernel S R).PosDef := by
  have hc := blockDiagonal_posSemidef (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i)
    (fun i => three_sub_posSemidef (hR i).1 (hR i).2)
  have hb : Matrix.blockDiagonal (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i) =
      (3 : ℝ) • 1 - Matrix.blockDiagonal R := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal_apply, Matrix.one_apply]
    · simp [Matrix.blockDiagonal_apply, hij]
  rw [hb] at hc
  have hp := hc.conjTranspose_mul_mul_same (scalarLift S)
  rw [scalarLift_conjTranspose S hSt] at hp
  have h := (scalarLift_posDef hscalar).add_posSemidef hp
  have he : scalarLift (1 - (3 : ℝ) • G) + scalarLift S *
      ((3 : ℝ) • 1 - Matrix.blockDiagonal R) * scalarLift S =
      1 - symmetricCurvatureKernel S R := by
    rw [scalarLift_sub_three, symmetricCurvatureKernel,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← scalarLift_mul, hS]
    module
  rwa [he] at h

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatCurvatureDirichlet
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual flat Green normalization of the curvature Dirichlet form. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
noncomputable section

theorem scalarLift_smul {N : ℕ} (c : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) :
    scalarLift (c • G) = c • scalarLift G := by
  ext ⟨a,i⟩ ⟨b,j⟩
  change (1 : NormalMatrix) a b * (c * G i j) = c * ((1 : NormalMatrix) a b * G i j)
  ring

theorem flat_curvatureDirichlet_eq {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    curvatureDirichlet t (fun i => R i - 1) =
      scalarLift (scalarDirichlet N 2) - (t / (N + 1)) ^ 2 • Matrix.blockDiagonal R := by
  rw [curvatureDirichlet_eq, scalarLift_sub_diagonal]
  simp only [add_sub_cancel]

theorem flat_curvatureDirichlet_normalized {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    scalarLift (scalarNormalizer (scalarDirichlet N 2)) *
      curvatureDirichlet t (fun i => R i - 1) *
      scalarLift (scalarNormalizer (scalarDirichlet N 2)) =
        1 - symmetricCurvatureKernel (flatGreenRoot t N) R := by
  rw [flat_curvatureDirichlet_eq, Matrix.mul_sub, Matrix.sub_mul,
    ← scalarLift_mul, ← scalarLift_mul,
    scalarNormalizer_normalizes (flatDirichlet_posDef N), scalarLift_one,
    Matrix.mul_smul, Matrix.smul_mul, symmetricCurvatureKernel,
    flatGreenRoot, scalarLift_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul]
  rw [pow_two]

theorem flat_curvatureDirichlet_posDef {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix)
    (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3)
    (hscalar : (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef) :
    (curvatureDirichlet t (fun i => R i - 1)).PosDef := by
  let U := scalarNormalizer (scalarDirichlet N 2)
  have hn : U * scalarDirichlet N 2 * U = 1 :=
    scalarNormalizer_normalizes (flatDirichlet_posDef N)
  have hu : IsUnit (scalarLift U) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [det_scalarLift]
    exact (Matrix.isUnit_det_of_left_inverse hn).pow 3
  have hUt : Uᵀ = U := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (scalarNormalizer_posSemidef (scalarDirichlet N 2)).isHermitian.eq
  apply hu.posDef_star_left_conjugate_iff.mp
  rw [Matrix.star_eq_conjTranspose, scalarLift_conjTranspose U hUt,
    flat_curvatureDirichlet_normalized]
  exact symmetricCurvatureKernel_one_sub_posDef _ _ (flatGreenRoot_square t N)
    (flatGreenRoot_transpose t N) hscalar R hR

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletDeterminant
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalization of the flat discrete determinant. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatDirichlet_det (N : ℕ) : (scalarDirichlet N 2).det = N + 1 := by
  let D := fun _ : ℕ => (2 : ℝ) • (1 : NormalMatrix)
  let Y := fun n : ℕ => (n : ℝ) • (1 : NormalMatrix)
  have hrec (i : ℕ) : Y (i + 2) = D i * Y (i + 1) - Y i := by
    dsimp [D,Y]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    push_cast
    module
  have hu (i : ℕ) (hi : 1 ≤ i) (_ : i ≤ N + 1) : IsUnit (Y i).det := by
    simp only [Y, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    apply isUnit_iff_ne_zero.mpr
    positivity
  have h := dirichlet_determinant_eq_jacobi D Y N
    (fun _ => by simp [D]) (by simp [Y]) (by simp [Y]) hrec hu
  have he : dirichletMatrix (fun i : Fin N => D i.val) =
      scalarLift (scalarDirichlet N 2) := by
    simpa only [D, smul_zero, zero_smul, sub_zero] using
      (scalarLift_sub_diagonal (N := N) 2 0 (fun _ => (0 : NormalMatrix))).symm
  rw [he, det_scalarLift] at h
  simp only [Y, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
    Nat.cast_add, Nat.cast_one] at h
  exact (Odd.pow_injective (by decide : Odd 3)) h

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatGreenDeterminant
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact determinant normalization by the flat discrete Green matrix. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatGreen_curvature_factorization {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    1 - curvatureKernel (scaledFlatGreen t N) R =
      scalarLift (flatGreen N) * curvatureDirichlet t (fun i => R i - 1) := by
  have hflat : flatGreen N * scalarDirichlet N 2 = 1 := by
    rw [flatGreen_eq_inverse]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (flatDirichlet_posDef N).isUnit)
  rw [flat_curvatureDirichlet_eq, Matrix.mul_sub, ← scalarLift_mul, hflat,
    scalarLift_one, curvatureKernel, scaledFlatGreen, scalarLift_smul,
    Matrix.smul_mul, Matrix.mul_smul]

theorem flatGreen_curvature_det {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix) :
    ((N : ℝ) + 1) ^ 3 * (1 - curvatureKernel (scaledFlatGreen t N) R).det =
      (curvatureDirichlet t (fun i => R i - 1)).det := by
  rw [flatGreen_curvature_factorization, Matrix.det_mul, det_scalarLift,
    flatGreen_eq_inverse, Matrix.det_nonsing_inv, flatDirichlet_det, Ring.inverse_eq_inv]
  field_simp

theorem flatGreen_endpoint_det {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix) (hsym : ∀ i, (R i)ᵀ = R i)
    (hpos : (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).PosDef) :
    t ^ 3 * (1 - curvatureKernel (scaledFlatGreen t N)
      (fun i => R (i.val + 1))).det =
        (discretePosition R (t / (N + 1)) (N + 1)).det := by
  have hd := flatGreen_curvature_det t (fun i : Fin N => R (i.val + 1))
  rw [curvatureDirichlet_determinant_of_posDef ht R hsym hpos] at hd
  have hh : t / ((N : ℝ) + 1) ≠ 0 := div_ne_zero ht (by positivity)
  have he : (t / ((N : ℝ) + 1)) • normalizedDiscrete R (t / (N + 1)) (N + 1) =
      discretePosition R (t / (N + 1)) (N + 1) := by
    simp only [normalizedDiscrete, smul_smul, mul_inv_cancel₀ hh, one_smul]
  rw [← he, Matrix.det_smul, Fintype.card_fin, ← hd]
  field_simp

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatJacobiLimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat-kernel determinants converge without a preconjugacy premise. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped Matrix.Norms.L2Operator
noncomputable section

namespace RegularJacobi
variable {t : ℝ} (d : RegularJacobi t)

theorem flat_kernel_determinant_tendsto (ht : 0 < t)
    (htop : t < Real.pi / Real.sqrt 3)
    (hR : ∀ s, (d.R s).PosSemidef ∧ (d.R s).trace = 3) :
    Tendsto (fun N : ℕ => (1 - curvatureKernel (scaledFlatGreen t N)
      (fun i => d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N))).det)
      atTop (nhds ((d.J t).det / t ^ 3)) := by
  have hx := (continuous_id.matrix_det.tendsto (d.J t)).comp
    (d.endpoint_position_tendsto ht)
  apply (hx.div_const (t ^ 3)).congr'
  filter_upwards [scaledFlatGreen_eventually_below_one ht.le htop] with N hN
  have hp := flat_curvatureDirichlet_posDef t
    (fun i : Fin N => d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N))
    (fun i => hR _) hN
  have he := flatGreen_endpoint_det ht.ne' (meshCurvature d.R t N)
    (fun i => d.symmetric _) hp
  change (discretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1)).det / t ^ 3 = _
  simp only [meshStep, meshCurvature] at he ⊢
  rw [← he]
  field_simp

end RegularJacobi
end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! An oriented orthogonal map fixing a tangent direction in dimension four
has a nonzero fixed normal vector. This is the odd-dimensional determinant
argument used for parallel transport around a closed geodesic. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators
noncomputable section

theorem orthogonal_three_fixed_vector (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : Qᵀ * Q = 1) (hdet : Q.det = 1) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧ Q *ᵥ w = w := by
  have hright : Q * Qᵀ = 1 := mul_eq_one_comm.mp horth
  have hid : (-Q) * (1 - Qᵀ) = 1 - Q := by
    rw [mul_sub,mul_one,neg_mul,hright]
    abel
  have htranspose : (1 - Qᵀ).det = (1 - Q).det := by
    have h : 1 - Qᵀ = (1 - Q)ᵀ := by rw [Matrix.transpose_sub,Matrix.transpose_one]
    rw [h,Matrix.det_transpose]
  have hd := congrArg Matrix.det hid
  rw [Matrix.det_mul,Matrix.det_neg,Fintype.card_fin,hdet,htranspose] at hd
  have hz : (1 - Q).det = 0 := by norm_num at hd; linarith
  obtain ⟨w,hw,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  refine ⟨w,hw,?_⟩
  rw [Matrix.sub_mulVec,Matrix.one_mulVec] at hker
  exact (sub_eq_zero.mp hker).symm

theorem oriented_four_fixed_normal (Q : OrientedOrthogonalFour)
    (hfirst : ∀ i, Q.val i 0 = (1 : Mat4) i 0) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧ Q.val *ᵥ Fin.cons 0 w = Fin.cons 0 w := by
  have ho := (orientedToOrthogonal Q).property
  change Q.valᵀ * Q.val = 1 at ho
  have hd := (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).2
  have hrow (j : Fin 4) : Q.val 0 j = (1 : Mat4) 0 j := by
    have h := congrArg (fun A : Mat4 => A 0 j) ho
    simp only [Matrix.mul_apply,Matrix.transpose_apply,hfirst,Matrix.one_apply] at h
    simpa [Matrix.one_apply] using h
  have hrowzero (j : Fin 3) : Q.val 0 j.succ = 0 := by
    simpa only [Matrix.one_apply, (Fin.succ_ne_zero j).symm,ite_false, if_false] using hrow j.succ
  let A : Matrix (Fin 3) (Fin 3) ℝ := Q.val.submatrix Fin.succ Fin.succ
  have hblock : Q.val = jacobiBlockMatrix 1 A := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [jacobiBlockMatrix,Fin.cons_zero,Matrix.one_apply,ite_true, if_true] using hfirst 0
      · exact hrowzero j
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [jacobiBlockMatrix,Fin.cons_succ,Fin.cons_zero,Matrix.one_apply,
          Fin.succ_ne_zero,ite_false, if_false] using hfirst i.succ
      · rfl
  have hAo : Aᵀ * A = 1 := by
    ext i j
    have h := congrArg (fun B : Mat4 => B i.succ j.succ) ho
    simp only [Matrix.mul_apply,Matrix.transpose_apply] at h
    rw [Fin.sum_univ_succ] at h
    simp only [hrowzero,Matrix.one_apply,zero_mul,zero_add,
      Fin.succ_inj] at h
    simpa only [A,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply,
      Matrix.one_apply,Fin.succ_inj] using h
  have hAd : A.det = 1 := by
    rw [hblock,jacobiBlockMatrix_det,one_mul] at hd
    exact hd
  obtain ⟨w,hw,hfixed⟩ := orthogonal_three_fixed_vector A hAo hAd
  refine ⟨w,hw,?_⟩
  rw [hblock,jacobiBlockMatrix_mulVec]
  simp only [Fin.cons_zero,Fin.cons_succ,mul_zero,hfixed]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A negative second variation with zero first variation gives strict
shortening for every sufficiently small positive parameter. -/
namespace PositiveEinsteinFour.Geometry
open Set Filter Metric
open scoped _root_.Topology

theorem scalar_second_variation_decreases (f : ℝ → ℝ) (D : ℝ)
    (hfd : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f s)
    (hzero : deriv f 0 = 0) (hD : HasDerivAt (deriv f) D 0) (hneg : D < 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < f 0 := by
  have hratio : ∀ᶠ s in 𝓝[>] (0 : ℝ), s⁻¹ * deriv f s < 0 := by
    have h := hD.tendsto_slope_zero_right.eventually (Iio_mem_nhds hneg)
    simpa only [zero_add,hzero,sub_zero,smul_eq_mul,mem_Iio] using h
  have hsign : ∀ᶠ s in 𝓝[>] (0 : ℝ), deriv f s < 0 := by
    filter_upwards [hratio,eventually_mem_nhdsWithin] with s hs hpos
    have hp : 0 < s := hpos
    have hi : 0 < s⁻¹ := inv_pos.mpr hp
    nlinarith
  have hsign' : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Ioi 0 → deriv f s < 0 :=
    eventually_nhdsWithin_iff.mp hsign
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hfd.and hsign')
  have hnear : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (δ / 2) := by
    have hh : ∀ᶠ s in 𝓝 (0 : ℝ), s < δ / 2 := Iio_mem_nhds (half_pos hδ)
    filter_upwards [hh.filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin] with s hlt hpos
    exact ⟨hpos,hlt⟩
  filter_upwards [hnear] with s hs
  have hmem (r : ℝ) (hr : r ∈ Icc 0 s) : r ∈ ball (0 : ℝ) δ := by
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hr.1]
    linarith [hr.2,hs.2]
  have hc : ContinuousOn f (Icc 0 s) := fun r hr =>
    ((hball (hmem r hr)).1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ f (Ioo 0 s) := fun r hr =>
    ((hball (hmem r ⟨hr.1.le,hr.2.le⟩)).1).differentiableWithinAt
  obtain ⟨r,hr,heq⟩ := exists_deriv_eq_slope f hs.1 hc hd
  have hrneg : deriv f r < 0 := (hball (hmem r ⟨hr.1.le,hr.2.le⟩)).2 hr.1
  rw [heq] at hrneg
  have hn := (div_lt_iff₀ (sub_pos.mpr hs.1)).mp hrneg
  linarith

end PositiveEinsteinFour.Geometry
end


section

/-! Continuous extensions of the first two jets of an actual C2 curve,
restricted to a sufficiently small parameter interval. -/
namespace PositiveEinsteinFour.Geometry
open Set Filter Metric
open scoped _root_.Topology ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_curve_second_jets (f : ℝ → E) (hf : ContDiffAt ℝ 2 f 0) :
    ∃ δ > 0, ∃ A A' A'' : ℝ → E,
      Continuous A ∧ Continuous A' ∧ Continuous A'' ∧
      (∀ s ∈ Icc (-δ) δ, A s = f s ∧ A' s = deriv f s ∧ A'' s = deriv (deriv f) s) ∧
      (∀ s ∈ Ioo (-δ) δ, HasDerivAt A (A' s) s ∧ HasDerivAt A' (A'' s) s) := by
  have hnear := hf.eventually (by decide : (2 : ℕ∞ω) ≠ ∞)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hab : -δ ≤ δ := by linarith
  have hfd (s : ℝ) (hs : s ∈ Icc (-δ) δ) : ContDiffAt ℝ 2 f s := by
    apply hball
    rw [mem_ball,Real.dist_eq,sub_zero,abs_lt]
    dsimp [δ] at hs
    constructor <;> linarith [hs.1,hs.2]
  let A := IccExtend hab (fun s : Icc (-δ) δ => f s)
  let A' := IccExtend hab (fun s : Icc (-δ) δ => deriv f s)
  let A'' := IccExtend hab (fun s : Icc (-δ) δ => deriv (deriv f) s)
  have hc : ContinuousOn f (Icc (-δ) δ) := fun s hs => (hfd s hs).continuousAt.continuousWithinAt
  have hc' : ContinuousOn (deriv f) (Icc (-δ) δ) := fun s hs =>
    ((hfd s hs).derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hc'' : ContinuousOn (deriv (deriv f)) (Icc (-δ) δ) := fun s hs =>
    (((hfd s hs).derivWithin (m := 1) (by norm_num)).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have heq (s : ℝ) (hs : s ∈ Icc (-δ) δ) :
      A s = f s ∧ A' s = deriv f s ∧ A'' s = deriv (deriv f) s :=
    ⟨IccExtend_of_mem hab _ hs,IccExtend_of_mem hab _ hs,IccExtend_of_mem hab _ hs⟩
  refine ⟨δ,hδ,A,A',A'',hc.domRestrict.Icc_extend',hc'.domRestrict.Icc_extend',
    hc''.domRestrict.Icc_extend',heq,?_⟩
  intro s hs
  have hsc : s ∈ Icc (-δ) δ := ⟨hs.1.le,hs.2.le⟩
  have hn : A =ᶠ[𝓝 s] f := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact (heq t ⟨ht.1.le,ht.2.le⟩).1
  have hn' : A' =ᶠ[𝓝 s] deriv f := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact (heq t ⟨ht.1.le,ht.2.le⟩).2.1
  rw [(heq s hsc).2.1,(heq s hsc).2.2]
  exact ⟨((hfd s hsc).differentiableAt (by norm_num)).hasDerivAt.congr_of_eventuallyEq hn,
    (((hfd s hsc).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt.congr_of_eventuallyEq hn'⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal endpoint curves with zero covariant acceleration at zero.
Their quadratic coordinate correction is the actual Christoffel term. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem normalEndpointQuadratic_zero (g : SmoothMetric M) (e : FrameBundle g) (a : Fin 3 → ℝ) :
    normalEndpointQuadratic g e a 0 = chartAt FourSpace e.base e.base := by
  simp [normalEndpointQuadratic]

theorem normalEndpointQuadratic_hasDerivAt (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (normalEndpointQuadratic g e a)
      (WithLp.toLp 2 (normalEndpointDirection g e a + s • normalEndpointAcceleration g e a)) s := by
  have h1 := ((hasDerivAt_id s).smul_const (WithLp.toLp 2 (normalEndpointDirection g e a))).const_add
    (chartAt FourSpace e.base e.base)
  have h2 := (((hasDerivAt_id s).pow 2).div_const 2).smul_const
    (WithLp.toLp 2 (normalEndpointAcceleration g e a))
  convert! h1.add h2 using 1
  all_goals try with_reducible_and_instances rfl
  simp [WithLp.toLp_add,WithLp.toLp_smul]

theorem normalEndpointQuadratic_contDiff (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) : ContDiff ℝ ∞ (normalEndpointQuadratic g e a) := by
  unfold normalEndpointQuadratic
  fun_prop

theorem normal_quadratic_boundary_zero (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) :
    chartEnergyBoundary g e.base (chartAt FourSpace e.base e.base)
      (fun i => frameChartMatrix g e.base e i 0)
      (normalEndpointDirection g e a) (normalEndpointAcceleration g e a) = 0 := by
  simp [chartEnergyBoundary,jacobiCovariantSecondJet,normalEndpointAcceleration,jacobiMetricPair]

theorem exists_normalQuadraticJetData (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (hc : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    Nonempty (NormalQuadraticJetData g e c a) := by
  let z := chartAt FourSpace e.base e.base
  let y := normalEndpointDirection g e a
  let u := normalEndpointAcceleration g e a
  let q := normalEndpointQuadratic g e a
  let f := fun s => chartTransition e.base c (q s)
  let v := fun s : ℝ => y + s • u
  let F := fun s => WithLp.toLp 2 (chartTransitionMatrix e.base c (q s) *ᵥ v s)
  have hz : z ∈ (chartAt FourSpace e.base).target :=
    (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hbase : (chartAt FourSpace e.base).symm z = e.base :=
    (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)
  have hqc : Continuous q := (normalEndpointQuadratic_contDiff g e a).continuous
  have hq0 : q 0 = z := normalEndpointQuadratic_zero g e a
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), q s ∈ (chartAt FourSpace e.base).target ∧
      (chartAt FourSpace e.base).symm (q s) ∈ (chartAt FourSpace c).source := by
    have ht : ∀ᶠ s in 𝓝 (0 : ℝ), q s ∈ (chartAt FourSpace e.base).target := hqc.continuousAt.preimage_mem_nhds
      ((chartAt FourSpace e.base).open_target.mem_nhds (hq0.symm ▸ hz))
    have hd : ContinuousAt (fun s => (chartAt FourSpace e.base).symm (q s)) 0 :=
      ((chartAt FourSpace e.base).continuousAt_symm (hq0.symm ▸ hz)).comp hqc.continuousAt
    have hd0 : (chartAt FourSpace e.base).symm (q 0) ∈ (chartAt FourSpace c).source := by
      rw [hq0,hbase]; exact hc
    exact ht.and (hd.preimage_mem_nhds ((chartAt FourSpace c).open_source.mem_nhds hd0))
  have hfd : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt f (F s) s := by
    filter_upwards [hnear] with s hs
    exact chartTransition_hasDerivAt e.base c q (v s) s hs.1 hs.2
      (normalEndpointQuadratic_hasDerivAt g e a s)
  have hsecond : HasDerivAt F
      (WithLp.toLp 2 (chartTransitionSecondJet e.base c z y u)) 0 := by
    have hv : HasDerivAt v u 0 := by
      simpa only [v,one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add y
    have h := chartTransition_secondJet_hasDerivAt e.base c q v u 0
      (hnear.self_of_nhds.1) (hnear.self_of_nhds.2)
      (normalEndpointQuadratic_hasDerivAt g e a 0) hv
    have hh := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap
      |>.hasFDerivAt.comp_hasDerivAt 0 h
    simpa only [F,hq0,v,zero_smul,add_zero,Function.comp_def,WithLp.toLp_ofLp] using! hh
  have hdiff : ContDiffAt ℝ 2 f 0 := by
    have hd := chartTransition_contDiffAt e.base c z hz (hbase.symm ▸ hc)
    have houter : ContDiffAt ℝ 2 (chartTransition e.base c) (q 0) := by
      rw [hq0]
      exact hd.of_le (by norm_num)
    have hinner : ContDiffAt ℝ 2 q 0 := (normalEndpointQuadratic_contDiff g e a).contDiffAt.of_le (by norm_num)
    exact houter.comp 0 hinner
  obtain ⟨r,hr,A,A',A'',hA,hA',hA'',heq,hder⟩ := exists_curve_second_jets f hdiff
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min r (s / 2)
  have hδ : 0 < δ := lt_min hr (half_pos hs)
  have hinr {t : ℝ} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-r) r := by
    have hm : δ ≤ r := min_le_left _ _
    constructor <;> linarith [ht.1,ht.2]
  have hingood {t : ℝ} (ht : t ∈ Icc (-δ) δ) :
      q t ∈ (chartAt FourSpace e.base).target ∧
        (chartAt FourSpace e.base).symm (q t) ∈ (chartAt FourSpace c).source := by
    apply hball
    rw [mem_ball,Real.dist_eq,sub_zero,abs_lt]
    have hm : δ ≤ s / 2 := min_le_right _ _
    constructor <;> linarith [ht.1,ht.2]
  have h00 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith,hδ.le⟩
  have hvalue : f 0 = chartAt FourSpace c e.base := by
    dsimp only [f]
    rw [hq0]
    exact congrArg (chartAt FourSpace c) hbase
  have hfirst : deriv f 0 = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ Fin.cons 0 a) := by
    rw [hfd.self_of_nhds.deriv]
    change WithLp.toLp 2 (chartTransitionMatrix e.base c (q 0) *ᵥ (y + 0 • u)) = _
    rw [hq0,zero_smul,add_zero,normalEndpoint_first_chart g e c hc a]
  have hderivEq : deriv f =ᶠ[𝓝 (0 : ℝ)] F := hfd.mono (fun _ h => h.deriv)
  have hsecond0 : deriv (deriv f) 0 = WithLp.toLp 2 (chartTransitionSecondJet e.base c z y u) :=
    (hsecond.congr_of_eventuallyEq hderivEq).deriv
  refine ⟨⟨δ,hδ,A,A',A'',hA,hA',hA'',(heq 0 (hinr h00)).1.trans hvalue,
    (heq 0 (hinr h00)).2.1.trans hfirst,(heq 0 (hinr h00)).2.2.trans hsecond0,?_,?_,?_⟩⟩
  · intro t ht
    apply hder t
    have hm : δ ≤ r := min_le_left _ _
    constructor <;> linarith [ht.1,ht.2]
  · intro t ht
    rw [(heq t (hinr ht)).1]
    exact (chartAt FourSpace c).map_source (hingood ht).2
  · intro t ht
    rw [(heq t (hinr ht)).1]
    exact (chartAt FourSpace c).left_inv (hingood ht).2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual quadratic endpoint correction cancels the covariant
acceleration boundary term in every overlapping chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem normalQuadratic_boundary_chart_zero (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (hc : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    chartEnergyBoundary g c (chartAt FourSpace c e.base)
      (fun i => frameChartMatrix g c e i 0) (frameChartMatrix g c e *ᵥ Fin.cons 0 a)
      (chartTransitionSecondJet e.base c (chartAt FourSpace e.base e.base)
        (normalEndpointDirection g e a) (normalEndpointAcceleration g e a)) = 0 := by
  have hz := (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hd : (chartAt FourSpace e.base).symm (chartAt FourSpace e.base e.base) ∈
      (chartAt FourSpace c).source := by
    simpa only [(chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)] using hc
  have h := chartEnergyBoundary_transition g e.base c (chartAt FourSpace e.base e.base)
    hz hd (fun i => frameChartMatrix g e.base e i 0) (normalEndpointDirection g e a)
      (normalEndpointAcceleration g e a)
  have hcoord : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    simp only [chartTransition, (chartAt FourSpace e.base).left_inv
      (mem_chart_source FourSpace e.base)]
  rw [hcoord,normalEndpoint_velocity_chart g e c hc,normalEndpoint_first_chart g e c hc a,
    normal_quadratic_boundary_zero] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The quadratic normal endpoint curve depends only on its base point
and its actual tangent vector, not on the frame used to represent it. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChart_map (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) :
    WithLp.toLp 2 (frameChartMatrix g c e *ᵥ WithLp.ofLp v) =
      chartForwardOperator c e.base (e.frame.map v) := by
  let Q := (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap
  have hcol (i : Fin 4) : Q (coordinateVector i) =
      WithLp.toLp 2 (fun j => frameChartMatrix g c e j i) := by
    change chartForwardOperator c e.base (e.frame.map (coordinateVector i)) = _
    rw [e.frame.map_coordinateVector]
    exact (frameChart_column_eq_derivative g c e i he).symm
  have hQ : Q v = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ WithLp.ofLp v) := by
    have hsum : (∑ i, (WithLp.ofLp v) i • coordinateVector i) = v :=
      sum_coordinateVector (WithLp.ofLp v)
    conv_lhs => rw [← hsum]
    rw [map_sum]
    simp only [map_smul,hcol]
    ext j
    simp [Matrix.mulVec,dotProduct,mul_comm]
  exact hQ.symm

theorem normalQuadraticEndpointCurve_zero (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) : normalQuadraticEndpointCurve g e a 0 = e.base := by
  rw [normalQuadraticEndpointCurve,normalEndpointQuadratic_zero]
  exact (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)

theorem normalQuadraticEndpointCurve_continuousAt (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) : ContinuousAt (normalQuadraticEndpointCurve g e a) 0 := by
  have hin : normalEndpointQuadratic g e a 0 ∈ (chartAt FourSpace e.base).target := by
    rw [normalEndpointQuadratic_zero]
    exact (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  exact ((chartAt FourSpace e.base).continuousAt_symm hin).comp
    (f := normalEndpointQuadratic g e a) (normalEndpointQuadratic_contDiff g e a).continuous.continuousAt

theorem normalQuadraticEndpointCurve_eq (g : SmoothMetric M) (e f : FrameBundle g)
    (a b : Fin 3 → ℝ) (hbase : e.base = f.base)
    (hvec : e.frame.map (WithLp.toLp 2 (Fin.cons 0 a)) =
      f.frame.map (WithLp.toLp 2 (Fin.cons 0 b))) :
    normalQuadraticEndpointCurve g e a = normalQuadraticEndpointCurve g f b := by
  cases e with
  | mk x E =>
    cases f with
    | mk y F =>
      change x = y at hbase
      subst y
      have hd : normalEndpointDirection g (⟨x,E⟩ : FrameBundle g) a =
          normalEndpointDirection g (⟨x,F⟩ : FrameBundle g) b := by
        apply WithLp.toLp_injective 2
        change WithLp.toLp 2 (frameChartMatrix g x (⟨x,E⟩ : FrameBundle g) *ᵥ
            WithLp.ofLp (WithLp.toLp 2 (Fin.cons 0 a))) =
          WithLp.toLp 2 (frameChartMatrix g x (⟨x,F⟩ : FrameBundle g) *ᵥ
            WithLp.ofLp (WithLp.toLp 2 (Fin.cons 0 b)))
        rw [frameChart_map g x _ (mem_chart_source FourSpace x),
          frameChart_map g x _ (mem_chart_source FourSpace x),hvec]
      funext s
      simp only [normalQuadraticEndpointCurve,normalEndpointQuadratic,
        normalEndpointAcceleration,hd]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential endpoint is jointly C1 in a nonzero normal
vector and its initial coordinate frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatRadialCotangentState_contDiffAt (g : SmoothMetric M) (c : M)
    (z : HeatRadialFrameSpace) (hz : z.2.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ 1 (fun w : HeatRadialFrameSpace => heatRadialCotangentState g c w.1 w.2) z := by
  apply contDiffAt_snd.fst.prodMk
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.contDiff.contDiffAt.comp
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ 1 (fun w : HeatRadialFrameSpace => ∑ j : Fin 4,
    metricInChart g c w.2.1 i j * ∑ k : Fin 4, w.2.2 j k * w.1 k) z
  apply ContDiffAt.sum
  intro j _
  apply ((metricInChart_contDiffAt g c z.2.1 hz i j).of_le (by first | simp | exact_mod_cast le_top)).comp z
    contDiffAt_snd.fst |>.mul
  apply ContDiffAt.sum
  intro k _
  have hE : ContDiffAt ℝ 1 (fun w : HeatRadialFrameSpace => w.2.2 j k) z := by fun_prop
  have hV : ContDiffAt ℝ 1 (fun w : HeatRadialFrameSpace => w.1 k) z :=
    by fun_prop
  exact hE.mul hV

variable [T2Space M] [CompactSpace M]

theorem exponentialFamilyCoordinates_frame (g : SmoothMetric M)
    (o : FrameOrientation g) (c d : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) (hv : v ≠ 0) :
    exponentialFamilyCoordinates g o c d (v, frameCoordinateState g c e) =
      chartAt FourSpace d (frameExponential g o e v) := by
  unfold exponentialFamilyCoordinates
  rw [heatRadialCotangentState_frame g c e he]
  exact radialCoordinateFlow_frame_endpoint g o c d e he v hv

theorem exponentialFamilyCoordinates_contDiffAt (g : SmoothMetric M)
    (o : FrameOrientation g) (c d : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) (hv : v ≠ 0)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ 1 (exponentialFamilyCoordinates g o c d) (v, frameCoordinateState g c e) := by
  let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
  let q := (euclideanPolarHomeomorph w).1
  let r := (euclideanPolarHomeomorph w).2
  let p : PositiveRadius × UnitTangentBundle g := (r, unitTangentTurn e q)
  have hvr : r.val • q.val = v :=
    congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
  have hstate : unitRadialCotangentState g c p =
      heatRadialCotangentState g c v (frameCoordinateState g c e) := by
    rw [heatRadialCotangentState_frame g c e he]
    change unitCotangentState g c r.val (unitTangentTurn e q) = _
    rw [unitCotangentState_turn g c e he, hvr]
  have hout : (unitTangentRadialFlow g o 1 p).2.base = frameExponential g o e v := by
    change (unitTangentFlowMap g o (r.val * 1) (unitTangentTurn e q)).base = _
    rw [mul_one, ← hvr, frameExponential_radial]
    rfl
  have hcore := radialFlowContDiffAt_all_time g o 1 p c d he (by rwa [hout])
  rw [hstate] at hcore
  exact (hcore.comp (v, frameCoordinateState g c e)
    (heatRadialCotangentState_contDiffAt g c _ ((chartAt FourSpace c).map_source he))).fst

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exponential commutes with oriented orthogonal changes of its initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameRotate_map (g : SmoothMetric M) (e : FrameBundle g) (Q : OrthogonalFour)
    (v : FourSpace) :
    (e.rotate Q).frame.map v =
      e.frame.map (orthogonalEuclideanIsometry Q.val Q.property v) := by
  ext i
  change ((e.frame.matrix * Q.val) *ᵥ WithLp.ofLp v) i =
    (e.frame.matrix *ᵥ (Q.val *ᵥ WithLp.ofLp v)) i
  rw [Matrix.mulVec_mulVec]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first variation of the squared radial length of a genuine local
inverse branch of the exponential. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology RealInnerProductSpace
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_exponential_log_first_variation (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (d : M) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    ∃ C : OpenPartialHomeomorph FourSpace FourSpace,
      (C : FourSpace → FourSpace) = (fun v => chartAt FourSpace d (frameExponential g o e v)) ∧
      t • coordinateVector 0 ∈ C.source ∧
      ∀ a : FourSpace, HasDerivAt
        (fun ε : ℝ => ‖C.symm (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base + ε • a)‖ ^ 2)
        (2 * t * ((fun i => frameChartMatrix g d (parallelFrameFlowMap g 0 t e) i 0) ⬝ᵥ
          (metricInChart g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base) *ᵥ WithLp.ofLp a))) 0 := by
  let v : FourSpace := t • coordinateVector 0
  let F : FourSpace → FourSpace := fun x => chartAt FourSpace d (frameExponential g o e x)
  let z : FourSpace := chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base
  have hz : F v = z := congrArg (chartAt FourSpace d) (frameExponential_first_ray g o e he t ht)
  let L := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
      jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))
  have hL := frameExponential_preconjugate_isUnit g hRic d e t ht htc hd
  let A : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hA : (A : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hder : HasFDerivAt F (A : FourSpace →L[ℝ] FourSpace) v := by
    rw [hA]
    exact frameExponential_hasFDerivAt g o hRic d e he t ht hd
  have hs : HasStrictFDerivAt F (A : FourSpace →L[ℝ] FourSpace) v :=
    (frameExponential_chart_contDiffAt g o d e v
      ((frameExponential_first_ray g o e he t ht).symm ▸ hd)).hasStrictFDerivAt' hder one_ne_zero
  let C := hs.toOpenPartialHomeomorph F
  have hC : (C : FourSpace → FourSpace) = F := rfl
  have hvC : v ∈ C.source := hs.mem_toOpenPartialHomeomorph_source
  have hInv : HasFDerivAt C.symm (A.symm : FourSpace →L[ℝ] FourSpace) z := by
    rw [← hz]
    exact hs.to_localInverse.hasFDerivAt
  have hInv0 : C.symm z = v := by rw [← hz]; exact C.left_inv hvC
  refine ⟨C,hC,hvC,?_⟩
  intro a
  have hline : HasDerivAt (fun ε : ℝ => z + ε • a) a 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add z
  have hbranch : HasDerivAt (fun ε : ℝ => C.symm (z + ε • a)) (A.symm a) 0 := by
    have hh : HasFDerivAt C.symm (A.symm : FourSpace →L[ℝ] FourSpace) (z + (0 : ℝ) • a) := by
      simpa only [zero_smul,add_zero] using hInv
    exact hh.comp_hasDerivAt 0 hline
  have hnorm := hbranch.norm_sq
  have hgauss := frameExponential_chart_gauss g o hRic d e he t ht hd (A.symm a)
  rw [hder.fderiv] at hgauss
  change _ ⬝ᵥ (_ *ᵥ WithLp.ofLp (A (A.symm a))) = _ at hgauss
  rw [A.apply_symm_apply] at hgauss
  have hinner : inner ℝ v (A.symm a) = t * (A.symm a) 0 := by
    rw [show v = t • coordinateVector 0 from rfl,real_inner_smul_left]
    change t * inner ℝ (EuclideanSpace.single 0 (1 : ℝ) : FourSpace) (A.symm a) = _
    rw [EuclideanSpace.inner_single_left]
    simp only [conj_trivial,one_mul]
  simpa only [zero_smul,add_zero,hInv0,hinner,← hgauss,mul_assoc] using hnorm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nonzero parallel normal field has strictly negative index on every
positive-length geodesic segment in positive sectional curvature. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix SectionalPlane MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem actual_normal_curvature_positive (hsec : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((1 + frameCurvatureField g e) *ᵥ v) := by
  have heq : v ⬝ᵥ ((1 + frameCurvatureField g e) *ᵥ v) =
      sectionalValue (frameCurvature g e.base e.frame)
        (normalCoordinates v) (coordinateVector 0) := by
    simpa only [star_trivial] using frameJacobiMatrix_quadratic e v
  rw [heq]
  have hu : normalCoordinates v ≠ 0 := normalCoordinates_ne_zero hv
  have hz : coordinateVector (0 : Fin 4) ≠ 0 := by
    intro he
    have h := congrArg (fun w : FourSpace => w 0) he
    norm_num [coordinateVector] at h
  have hlin : LinearIndependent ℝ ![normalCoordinates v, coordinateVector 0] := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i
      fin_cases i
      · exact hu
      · exact hz
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact normalCoordinates_orthogonal v
      · change inner ℝ (coordinateVector 0) (normalCoordinates v) = 0
        rw [real_inner_comm]
        exact normalCoordinates_orthogonal v
      · exact False.elim (hij rfl)
  rw [sectionalValue_frame]
  exact e.frame.sectional_pos hsec _ _ hlin

variable [T3Space M] [CompactSpace M]

theorem parallel_normal_index_negative (hRic : RicciThree g) (hsec : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (v : Fin 3 → ℝ) (hv : v ≠ 0)
    {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) v 0) < 0 := by
  have hc : Continuous (fun t => normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) v 0) := by
    apply continuous_normalIndexDensity
    · exact actualJacobiCurvature_continuous g hRic e
    · exact continuous_const
    · exact continuous_const
  have hn (t : ℝ) : normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) v 0 < 0 := by
    rw [normalIndexDensity]
    simp only [dotProduct_zero,zero_sub]
    rw [dotProduct_comm]
    exact neg_neg_of_pos (actual_normal_curvature_positive hsec _ v hv)
  simpa only [intervalIntegral.integral_zero] using
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      hc.continuousOn continuousOn_const (fun t _ => (hn t).le)
      ⟨a,⟨le_rfl,hab.le⟩,hn a⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The inverse radial first variation in the actual metric at the endpoint. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChart_center_inner (g : SmoothMetric M) (d : M) (E : FrameBundle g)
    (hd : E.base = d) (a : FourSpace) :
    (fun i => frameChartMatrix g d E i 0) ⬝ᵥ
      (metricInChart g d (chartAt FourSpace d d) *ᵥ WithLp.ofLp a) =
      g.inner d (E.frame.vector 0) a := by
  cases E with
  | mk x F =>
    change x = d at hd
    subst x
    have hcol := frameChart_column_eq_derivative g d (⟨d,F⟩ : FrameBundle g) 0
      (mem_chart_source FourSpace d)
    rw [chartForwardOperator_center] at hcol
    have hp := metricInChart_center_pairing g d
      (fun i => frameChartMatrix g d (⟨d,F⟩ : FrameBundle g) i 0) (WithLp.ofLp a)
    rw [hcol,WithLp.toLp_ofLp] at hp
    exact hp

variable [T3Space M] [CompactSpace M]

theorem exists_exponential_log_center (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (d : M) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e)
    (hd : (parallelFrameFlowMap g 0 t e).base = d) :
    ∃ C : OpenPartialHomeomorph FourSpace FourSpace,
      (C : FourSpace → FourSpace) = (fun v => chartAt FourSpace d (frameExponential g o e v)) ∧
      t • coordinateVector 0 ∈ C.source ∧
      ∀ a : FourSpace, HasDerivAt
        (fun ε : ℝ => ‖C.symm (chartAt FourSpace d d + ε • a)‖ ^ 2)
        (2 * t * g.inner d ((parallelFrameFlowMap g 0 t e).frame.vector 0) a) 0 := by
  obtain ⟨C,hC,hv,hder⟩ := exists_exponential_log_first_variation g o hRic e he d t ht htc
    (hd ▸ mem_chart_source FourSpace d)
  refine ⟨C,hC,hv,?_⟩
  intro a
  have h := hder a
  rw [hd,frameChart_center_inner g d _ hd a] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The parameter-preserving inverse theorem at an arbitrary normal vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
theorem exponentialFamily_local_inverse
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (v : FourSpace) (q : CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 1 P (v, q)) (A : FourSpace ≃L[ℝ] FourSpace)
    (hA : HasFDerivAt (fun x : FourSpace => (P (x, q)).1) (A : FourSpace →L[ℝ] FourSpace) v) :
    ∃ H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace,
      (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P ∧
      (v, q) ∈ H.source ∧
      ContDiffAt ℝ 1 H.symm (heatFamilyBaseAugment P (v, q)) := by
  let B := (ContinuousLinearMap.fst ℝ FourSpace Mat4).comp
    ((fderiv ℝ P (v, q)).comp (ContinuousLinearMap.inr ℝ FourSpace CoordinateFrameSpace))
  let E : HeatRadialFrameSpace ≃L[ℝ] HeatRadialFrameSpace :=
    (ContinuousLinearEquiv.prodComm ℝ FourSpace CoordinateFrameSpace).trans
      (((ContinuousLinearEquiv.refl ℝ CoordinateFrameSpace).skewProd A B).trans
        (ContinuousLinearEquiv.prodComm ℝ CoordinateFrameSpace FourSpace))
  have hdP := (hP.differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (heatFamilyBaseAugment P)
      (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (v, q))).prod
        (ContinuousLinearMap.snd ℝ FourSpace CoordinateFrameSpace)) (v, q) :=
    hdP.fst.prodMk hasFDerivAt_snd
  have hfirst : HasFDerivAt (fun z : HeatRadialFrameSpace => (P z).1)
      ((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (v, q))) (v, q) := hdP.fst
  have harg : HasFDerivAt (fun x : FourSpace => (x, q))
      ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace)) v :=
    (hasFDerivAt_id v).prodMk (hasFDerivAt_const q v)
  have hs : HasFDerivAt (fun x : FourSpace => (P (x, q)).1)
      (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (v, q))).comp
        ((ContinuousLinearMap.id ℝ FourSpace).prod
          (0 : FourSpace →L[ℝ] CoordinateFrameSpace))) v := HasFDerivAt.comp (f := fun x : FourSpace => (x, q))
      (g := fun z : HeatRadialFrameSpace => (P z).1) v hfirst harg
  have hsame := hs.unique hA
  have hsp (w : FourSpace) : (fderiv ℝ P (v, q) (w, 0)).1 = A w :=
    congrArg (fun L : FourSpace →L[ℝ] FourSpace => L w) hsame
  have hE : (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (v, q))).prod
        (ContinuousLinearMap.snd ℝ FourSpace CoordinateFrameSpace)) =
      (E : HeatRadialFrameSpace →L[ℝ] HeatRadialFrameSpace) := by
    apply ContinuousLinearMap.ext
    intro z
    change ((fderiv ℝ P (v, q) z).1, z.2) = (A z.1 + B z.2, z.2)
    have hz : z = (z.1, (0 : CoordinateFrameSpace)) + ((0 : FourSpace), z.2) := by simp
    apply Prod.ext
    · change (fderiv ℝ P (v, q) z).1 = A z.1 + B z.2
      calc
        (fderiv ℝ P (v, q) z).1 =
            (fderiv ℝ P (v, q) ((z.1, 0) + (0, z.2))).1 := congrArg (fun w : HeatRadialFrameSpace => (fderiv ℝ P (v, q) w).1) hz
        _ = (fderiv ℝ P (v, q) (z.1, 0)).1 +
            (fderiv ℝ P (v, q) (0, z.2)).1 := by rw [map_add]; rfl
        _ = A z.1 + B z.2 := by rw [hsp]; rfl
    · rfl
  rw [hE] at hd
  have hf : ContDiffAt ℝ 1 (heatFamilyBaseAugment P) (v, q) :=
    hP.fst.prodMk contDiffAt_snd
  let H := hf.toOpenPartialHomeomorph (heatFamilyBaseAugment P) hd (by norm_num)
  refine ⟨H, rfl, hf.mem_toOpenPartialHomeomorph_source hd (by norm_num), ?_⟩
  exact hf.to_localInverse hd (by norm_num)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nonconjugate radial vector has one injective neighborhood that works
for every sufficiently nearby initial frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_common_injective_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
      ∀ f ∈ U, InjOn (frameExponential g o f) (ball (t • coordinateVector 0) r) := by
  let v : FourSpace := t • coordinateVector 0
  let c := e.base
  let d := (parallelFrameFlowMap g 0 t e).base
  have hc : e.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hvexp : frameExponential g o e v = d := frameExponential_first_ray g o e he t ht
  have hvn : ‖v‖ = t := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit, mul_one]
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvn]; exact ht.ne')
  let q := frameCoordinateState g c e
  let P : HeatRadialFrameSpace → CoordinateFrameSpace :=
    fun z => (exponentialFamilyCoordinates g o c d z, 0)
  have hP : ContDiffAt ℝ 1 P (v,q) :=
    (exponentialFamilyCoordinates_contDiffAt g o c d e hc v hv (hvexp ▸ hd)).prodMk contDiffAt_const
  let L := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
      jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))
  have hL : IsUnit L := frameExponential_preconjugate_isUnit g hRic d e t ht htc hd
  let A : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hA : (A : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hder : HasFDerivAt (fun x => (P (x,q)).1) (A : FourSpace →L[ℝ] FourSpace) v := by
    rw [hA]
    have heq : (fun x => (P (x,q)).1) =ᶠ[𝓝 v]
        (fun x => chartAt FourSpace d (frameExponential g o e x)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
      exact exponentialFamilyCoordinates_frame g o c d e hc x hx
    exact (frameExponential_hasFDerivAt g o hRic d e he t ht hd).congr_of_eventuallyEq heq
  obtain ⟨H,hH,hvH,_⟩ := exponentialFamily_local_inverse P v q hP A hder
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds hvH)
  have hframe : {f : FrameBundle g | f.base ∈ (chartAt FourSpace c).source ∧
      frameCoordinateState g c f ∈ ball q R} ∈ 𝓝 e :=
    Filter.inter_mem ((continuous_frameBase g).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc))
      ((frameCoordinateState_continuousAt g c e hc).preimage_mem_nhds (ball_mem_nhds q hR))
  obtain ⟨U,hsub,hU,heU⟩ := mem_nhds_iff.mp hframe
  let r := min R (t / 2)
  have hr : 0 < r := lt_min hR (half_pos ht)
  have hnz (x : FourSpace) (hx : x ∈ ball v r) : x ≠ 0 := by
    intro hzero
    rw [hzero, mem_ball, dist_zero_left, hvn] at hx
    have hh : r ≤ t / 2 := min_le_right _ _
    linarith
  refine ⟨U,hU,heU,r,hr,?_⟩
  intro f hf x hx y hy hxy
  obtain ⟨hfc,hfq⟩ := hsub hf
  have hxH : (x,frameCoordinateState g c f) ∈ H.source := hball (by
    change max (dist x v) (dist (frameCoordinateState g c f) q) < R
    exact max_lt (lt_of_lt_of_le hx (min_le_left _ _)) hfq)
  have hyH : (y,frameCoordinateState g c f) ∈ H.source := hball (by
    change max (dist y v) (dist (frameCoordinateState g c f) q) < R
    exact max_lt (lt_of_lt_of_le hy (min_le_left _ _)) hfq)
  apply congrArg Prod.fst (H.injOn hxH hyH ?_)
  rw [hH]
  dsimp only [heatFamilyBaseAugment]
  apply Prod.ext
  swap
  · rfl
  change exponentialFamilyCoordinates g o c d (x,frameCoordinateState g c f) =
    exponentialFamilyCoordinates g o c d (y,frameCoordinateState g c f)
  rw [exponentialFamilyCoordinates_frame g o c d f hfc x (hnz x hx),
    exponentialFamilyCoordinates_frame g o c d f hfc y (hnz y hy), hxy]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual exponential, including zero vectors and
varying base frames. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_joint_continuous (g : SmoothMetric M) (o : FrameOrientation g) :
    Continuous (fun p : FrameBundle g × FourSpace => frameExponential g o p.1 p.2) := by
  let U : Set (FrameBundle g × FourSpace) := {p | p.2 ≠ 0}
  have hU : IsOpen U := isOpen_compl_singleton.preimage continuous_snd
  have hpol : Continuous (fun p : U => euclideanPolarHomeomorph
      (⟨p.val.2, p.property⟩ : ({0}ᶜ : Set FourSpace))) :=
    euclideanPolarHomeomorph.continuous.comp
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  have hturn : Continuous (fun p : U => unitTangentTurn p.val.1
      (euclideanPolarHomeomorph (⟨p.val.2,p.property⟩ : ({0}ᶜ : Set FourSpace))).1) :=
    continuous_unitTangentTurn.comp ((continuous_fst.comp continuous_subtype_val).prodMk hpol.fst)
  have htime : Continuous (fun p : U =>
      (euclideanPolarHomeomorph (⟨p.val.2,p.property⟩ : ({0}ᶜ : Set FourSpace))).2.val) :=
    continuous_subtype_val.comp hpol.snd
  have hnonzero : ContinuousOn
      (fun p : FrameBundle g × FourSpace => frameExponential g o p.1 p.2) U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := (continuous_unitTangentBase g).comp
      ((unitTangentFlowMap_continuous g o).comp (htime.prodMk hturn))
    exact h.congr (fun p => (frameExponential_nonzero g o p.val.1 ⟨p.val.2,p.property⟩).symm)
  apply continuous_iff_continuousAt.mpr
  rintro ⟨e,v⟩
  by_cases hv : v = 0
  · subst v
    let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
    apply (tendsto_iff_edist_tendsto_0).mpr
    change Tendsto (fun p : FrameBundle g × FourSpace =>
      edist (frameExponential g o p.1 p.2) (frameExponential g o e 0)) (𝓝 (e,0)) (𝓝 0)
    rw [frameExponential_zero]
    have hb : Tendsto (fun p : FrameBundle g × FourSpace =>
        metricEDistance g p.1.base e.base) (𝓝 (e,0)) (𝓝 0) := by
      have h : Continuous (fun p : FrameBundle g × FourSpace =>
          metricEDistance g p.1.base e.base) :=
        (metricEDistance_continuous g).comp
          (((continuous_frameBase g).comp continuous_fst).prodMk continuous_const)
      simpa only [metricEDistance, Manifold.riemannianEDist_self] using h.tendsto (e,(0 : FourSpace))
    have hn : Tendsto (fun p : FrameBundle g × FourSpace => ENNReal.ofReal ‖p.2‖)
        (𝓝 (e,0)) (𝓝 0) := by
      have h : Continuous (fun p : FrameBundle g × FourSpace => ENNReal.ofReal ‖p.2‖) :=
        ENNReal.continuous_ofReal.comp (continuous_norm.comp continuous_snd)
      simpa only [norm_zero, ENNReal.ofReal_zero] using h.tendsto (e,(0 : FourSpace))
    have hsum : Tendsto (fun p : FrameBundle g × FourSpace =>
        ENNReal.ofReal ‖p.2‖ + metricEDistance g p.1.base e.base) (𝓝 (e,0)) (𝓝 0) := by
      simpa only [zero_add] using hn.add hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le)
    intro p
    exact (Manifold.riemannianEDist_triangle (I := I4)
      (x := frameExponential g o p.1 p.2) (y := p.1.base) (z := e.base)).trans
      (add_le_add (by
        rw [Manifold.riemannianEDist_comm]
        exact frameExponential_distance g o p.1 p.2) le_rfl)
  · exact (hnonzero (e,v) hv).continuousAt (hU.mem_nhds hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine inverse exponential branch is continuous jointly in the
initial frame and the endpoint, near any nonconjugate radial pair. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_joint_exponential_log (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e) :
    ∃ U : Set (FrameBundle g × M), IsOpen U ∧
      (e,frameGeodesic g 0 e t) ∈ U ∧
      ∃ log : FrameBundle g × M → FourSpace, ContinuousOn log U ∧
        log (e,frameGeodesic g 0 e t) = t • coordinateVector 0 ∧
        ∀ p ∈ U, frameExponential g o p.1 (log p) = p.2 := by
  let v : FourSpace := t • coordinateVector 0
  let c := e.base
  let d := (parallelFrameFlowMap g 0 t e).base
  have hc : e.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hvexp : frameExponential g o e v = d := frameExponential_first_ray g o e he t ht
  have hvn : ‖v‖ = t := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit, mul_one]
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvn]; exact ht.ne')
  let q := frameCoordinateState g c e
  let P : HeatRadialFrameSpace → CoordinateFrameSpace :=
    fun z => (exponentialFamilyCoordinates g o c d z, 0)
  have hP : ContDiffAt ℝ 1 P (v,q) :=
    (exponentialFamilyCoordinates_contDiffAt g o c d e hc v hv (hvexp ▸ hd)).prodMk contDiffAt_const
  let L := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
      jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))
  have hL : IsUnit L := frameExponential_preconjugate_isUnit g hRic d e t ht htc hd
  let A : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hA : (A : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hder : HasFDerivAt (fun x => (P (x,q)).1) (A : FourSpace →L[ℝ] FourSpace) v := by
    rw [hA]
    have heq : (fun x => (P (x,q)).1) =ᶠ[𝓝 v]
        (fun x => chartAt FourSpace d (frameExponential g o e x)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
      exact exponentialFamilyCoordinates_frame g o c d e hc x hx
    exact (frameExponential_hasFDerivAt g o hRic d e he t ht hd).congr_of_eventuallyEq heq
  obtain ⟨H,hH,hvH,_⟩ := exponentialFamily_local_inverse P v q hP A hder
  let b : FrameBundle g × M := (e,d)
  let C : FrameBundle g × M → HeatRadialFrameSpace :=
    fun p => (chartAt FourSpace d p.2,frameCoordinateState g c p.1)
  have hC : C b = H (v,q) := by
    rw [hH]
    change (chartAt FourSpace d d,q) = (exponentialFamilyCoordinates g o c d (v,q),q)
    rw [exponentialFamilyCoordinates_frame g o c d e hc v hv,hvexp]
  have htarget : C b ∈ H.target := hC.symm ▸ H.map_source hvH
  let log : FrameBundle g × M → FourSpace := fun p => (H.symm (C p)).1
  have hlog : log b = v := by
    dsimp only [log]
    rw [hC,H.left_inv hvH]
  have hCcont : ContinuousAt C b := by
    have hfirst : ContinuousAt (fun p : FrameBundle g × M => chartAt FourSpace d p.2) b :=
      (chartAt FourSpace d).continuousAt hd |>.comp continuous_snd.continuousAt
    have hsecond : ContinuousAt (fun p : FrameBundle g × M => frameCoordinateState g c p.1) b := by
      simpa only [Function.comp_def] using!
        ((frameCoordinateState_continuousAt g c e hc).comp
          (continuous_fst.continuousAt : ContinuousAt (Prod.fst : FrameBundle g × M → FrameBundle g) b))
    exact hfirst.prodMk hsecond
  have hlcont : ContinuousAt log b :=
    continuous_fst.continuousAt.comp ((H.continuousAt_symm htarget).comp hCcont)
  have hbbase : b.1.base ∈ (chartAt FourSpace c).source := hc
  have hbpoint : b.2 ∈ (chartAt FourSpace d).source := hd
  have hlexp : frameExponential g o b.1 (log b) ∈ (chartAt FourSpace d).source := by
    rw [hlog]
    exact hvexp.symm ▸ hd
  have hlognz : log b ≠ 0 := by rw [hlog]; exact hv
  have hnear : {p : FrameBundle g × M |
      p.1.base ∈ (chartAt FourSpace c).source ∧ p.2 ∈ (chartAt FourSpace d).source ∧
      C p ∈ H.target ∧ log p ≠ 0 ∧
      frameExponential g o p.1 (log p) ∈ (chartAt FourSpace d).source} ∈ 𝓝 b := by
    apply Filter.inter_mem
      (((continuous_frameBase g).comp continuous_fst).continuousAt.preimage_mem_nhds
        ((chartAt FourSpace c).open_source.mem_nhds hbbase))
    apply Filter.inter_mem
      (continuous_snd.continuousAt.preimage_mem_nhds ((chartAt FourSpace d).open_source.mem_nhds hbpoint))
    apply Filter.inter_mem (hCcont.preimage_mem_nhds (H.open_target.mem_nhds htarget))
    apply Filter.inter_mem (hlcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hlognz))
    exact ((frameExponential_joint_continuous g o).continuousAt.comp
      (continuous_fst.continuousAt.prodMk hlcont)).preimage_mem_nhds
        ((chartAt FourSpace d).open_source.mem_nhds hlexp)
  obtain ⟨U,hUsub,hU,hbU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U,hU,hbU,log,?_,hlog,?_⟩
  · intro p hp
    obtain ⟨hpc,hpd,hpt,_,_⟩ := hUsub hp
    apply ContinuousAt.continuousWithinAt
    have hfirst : ContinuousAt (fun q : FrameBundle g × M => chartAt FourSpace d q.2) p :=
      (chartAt FourSpace d).continuousAt hpd |>.comp continuous_snd.continuousAt
    have hsecond : ContinuousAt (fun q : FrameBundle g × M => frameCoordinateState g c q.1) p := by
      simpa only [Function.comp_def] using!
        ((frameCoordinateState_continuousAt g c p.1 hpc).comp
          (continuous_fst.continuousAt : ContinuousAt (Prod.fst : FrameBundle g × M → FrameBundle g) p))
    exact continuous_fst.continuousAt.comp ((H.continuousAt_symm hpt).comp (hfirst.prodMk hsecond))
  · intro p hp
    obtain ⟨hpc,hpd,hpt,hnz,hpexp⟩ := hUsub hp
    have hr := H.right_inv hpt
    have hq : (H.symm (C p)).2 = (C p).2 := by
      have hh := congrArg Prod.snd hr
      rw [hH] at hh
      exact hh
    have hf := congrArg Prod.fst hr
    rw [hH] at hf
    change exponentialFamilyCoordinates g o c d (H.symm (C p)) = chartAt FourSpace d p.2 at hf
    have hpair : H.symm (C p) = (log p,frameCoordinateState g c p.1) :=
      Prod.ext rfl hq
    rw [hpair,exponentialFamilyCoordinates_frame g o c d p.1 hpc (log p) hnz] at hf
    exact (chartAt FourSpace d).injOn hpexp hpd hf

end
end PositiveEinsteinFour.Geometry
end


section

/-! The energy of a finite piecewise C1 path bounds the distance to every
point on that path, using only its actual speed integral. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Bundle MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

omit [T3Space M] [PreconnectedSpace M] in
theorem metricCurveEnergy_nonneg (g : SmoothMetric M) (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ metricCurveEnergy g γ a b :=
  intervalIntegral.integral_nonneg hab (fun t _ => mul_nonneg (by norm_num) (sq_nonneg _))

theorem metricDistance_point_le_curveEnergy_add (g : SmoothMetric M) (γ : ℝ → M)
    {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b))
    {r : ℝ} (hr : r ∈ Icc a b) :
    metricDistance g (γ a) (γ r) ≤ metricCurveEnergy g γ a b + (b - a) / 2 := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hl : metricEDistance g (γ a) (γ r) ≤
      ENNReal.ofReal (∫ t in a..b, metricIntervalSpeed g γ a b t) := by
    calc
      _ ≤ Manifold.pathELength I4 γ a r :=
        Manifold.riemannianEDist_le_pathELength
          (hγ.mono (Icc_subset_Icc le_rfl hr.2)) rfl rfl hr.1
      _ ≤ Manifold.pathELength I4 γ a b := Manifold.pathELength_mono le_rfl hr.2
      _ = _ := metric_pathELength_eq_ofReal_integral g γ hab hγ
  have hn : 0 ≤ ∫ t in a..b, metricIntervalSpeed g γ a b t :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => metricIntervalSpeed_nonneg g γ a b t)
  rw [← ofReal_metricDistance g (γ a) (γ r),ENNReal.ofReal_le_ofReal_iff hn] at hl
  exact hl.trans (integral_speed_le_energy_add _ hab.le (metricIntervalSpeed_continuousOn g γ hab hγ))

theorem finite_piece_metric_energy_point_bound (g : SmoothMetric M) (n : ℕ)
    (p : ℕ → M) (t : ℕ → ℝ) (γ : ℕ → ℝ → M)
    (ht : ∀ i < n, t i < t (i + 1))
    (hγ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i) (Icc (t i) (t (i + 1))))
    (hleft : ∀ i < n, γ i (t i) = p i)
    (hright : ∀ i < n, γ i (t (i + 1)) = p (i + 1))
    (i : ℕ) (hi : i < n) (r : ℝ) (hr : r ∈ Icc (t i) (t (i + 1))) :
    metricDistance g (p 0) (γ i r) ≤
      (∑ j ∈ Finset.range n, metricCurveEnergy g (γ j) (t j) (t (j + 1))) +
        (t n - t 0) / 2 := by
  have hprefix := finite_piece_metric_energy_lower g i p t γ
    (fun j hj => ht j (hj.trans hi)) (fun j hj => hγ j (hj.trans hi))
    (fun j hj => hleft j (hj.trans hi)) (fun j hj => hright j (hj.trans hi))
  have hlast := metricDistance_point_le_curveEnergy_add g (γ i) (ht i hi) (hγ i hi) hr
  rw [hleft i hi] at hlast
  have htri := metricDistance_triangle g (p 0) (p i) (γ i r)
  have hs : (∑ j ∈ Finset.range (i + 1), metricCurveEnergy g (γ j) (t j) (t (j + 1))) ≤
      ∑ j ∈ Finset.range n, metricCurveEnergy g (γ j) (t j) (t (j + 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hi))
    intro j hj _
    exact metricCurveEnergy_nonneg g (γ j) (ht j (Finset.mem_range.mp hj)).le
  have htime (j k : ℕ) (hjk : j ≤ k) (hkn : k ≤ n) : t j ≤ t k := by
    induction k, hjk using Nat.le_induction with
    | base => rfl
    | succ k hjk ih => exact (ih (Nat.le_of_succ_le hkn)).trans (ht k (lt_of_lt_of_le (Nat.lt_succ_self k) hkn)).le
  have htn := htime (i+1) n (Nat.succ_le_of_lt hi) le_rfl
  rw [Finset.sum_range_succ] at hs
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual normal variations with endpoint curves of zero covariant acceleration. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
theorem normalQuadraticSegment_common_radius (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ContinuousOn N (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    ∃ δ > 0, δ ≤ A.radius ∧ δ ≤ B.radius ∧ ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈
        (chartAt FourSpace c).target := by
  have hx : ContinuousOn (fun t => chartAt FourSpace c (frameGeodesic g 0 e t)) (Icc a b) :=
    ((frameGeodesic_chart_contDiffOn g 0 e c).mono hc).continuousOn
  have hy : ContinuousOn (fun t => WithLp.toLp 2 (normalChartField g c e N t)) (Icc a b) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (normalChartField_continuousOn g c e N (Icc a b) hc hN)
  obtain ⟨r, hr, hinside⟩ := endpointCorrectedPosition_inside_on
    (fun t => chartAt FourSpace c (frameGeodesic g 0 e t))
    (fun t => WithLp.toLp 2 (normalChartField g c e N t)) A.position B.position hab.le
    hx hy A.position_continuous B.position_continuous A.position_zero B.position_zero
    (chartAt FourSpace c).target (chartAt FourSpace c).open_target
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
  refine ⟨min r (min A.radius B.radius), lt_min hr (lt_min A.radius_pos B.radius_pos),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro ε hε t ht
  apply hinside ε ?_ t ht
  constructor <;> linarith [hε.1, hε.2, min_le_left r (min A.radius B.radius)]

theorem normalQuadraticSegmentCurve_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b t : ℝ}
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (ht : frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source) :
    normalSegmentCurve g e c N A.position B.position a b 0 t = frameGeodesic g 0 e t := by
  unfold normalSegmentCurve normalSegmentPosition
  rw [endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero]
  exact (chartAt FourSpace c).left_inv ht

theorem normalQuadraticSegmentCurve_endpoints (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b ε : ℝ} (hab : a < b)
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : ε ∈ Icc (-A.radius) A.radius) (hB : ε ∈ Icc (-B.radius) B.radius) :
    normalSegmentCurve g e c N A.position B.position a b ε a =
      normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 a e) (N a) ε ∧
    normalSegmentCurve g e c N A.position B.position a b ε b =
      normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 b e) (N b) ε := by
  unfold normalSegmentCurve normalSegmentPosition
  rw [endpointCorrectedPosition_left _ _ _ _ _ _ _ hab.ne,
    endpointCorrectedPosition_right _ _ _ _ _ _ _ hab.ne]
  exact ⟨A.realizes ε hA, B.realizes ε hB⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual corrected curve at the reference
geodesic, including both ends of each chart segment. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff
noncomputable section
theorem endpointCorrectedPosition_continuousAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x y A B : ℝ → E)
    (a b ε r : ℝ) (hx : ContinuousAt x r) (hy : ContinuousAt y r)
    (hA : ContinuousAt A ε) (hB : ContinuousAt B ε) :
    ContinuousAt (fun p : ℝ × ℝ => endpointCorrectedPosition x y A B a b p.1 p.2) (ε,r) := by
  have hxp := hx.comp (x := (ε,r)) (f := Prod.snd) continuous_snd.continuousAt
  have hyp := hy.comp (x := (ε,r)) (f := Prod.snd) continuous_snd.continuousAt
  have hAp := hA.comp (x := (ε,r)) (f := Prod.fst) continuous_fst.continuousAt
  have hBp := hB.comp (x := (ε,r)) (f := Prod.fst) continuous_fst.continuousAt
  unfold endpointCorrectedPosition endpointResidual endpointWeightLeft endpointWeightRight
  exact ((hxp.add (continuous_fst.continuousAt.smul hyp)).add
    (((continuousAt_const.sub continuous_snd.continuousAt).div_const (b-a)).smul
      ((hAp.sub continuousAt_const).sub (continuous_fst.continuousAt.smul continuousAt_const)))).add
    (((continuous_snd.continuousAt.sub continuousAt_const).div_const (b-a)).smul
      ((hBp.sub continuousAt_const).sub (continuous_fst.continuousAt.smul continuousAt_const)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalQuadraticSegmentCurve_continuousAt (g : SmoothMetric M)
    (e : FrameBundle g) (c : M) (a : Fin 3 → ℝ) (u v r : ℝ)
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 u e) c a)
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 v e) c a)
    (hr : frameGeodesic g 0 e r ∈ (chartAt FourSpace c).source) :
    ContinuousAt (fun p : ℝ × ℝ =>
      normalSegmentCurve g e c (fun _ => a) A.position B.position u v p.1 p.2) (0,r) := by
  let x := fun s => chartAt FourSpace c (frameGeodesic g 0 e s)
  let y := fun s => WithLp.toLp 2 (normalChartField g c e (fun _ => a) s)
  have hx : ContinuousAt x r := (geodesicChartPosition_hasDerivAt g c e r hr).continuousAt
  have hy : ContinuousAt y r :=
    ((PiLp.continuous_toLp 2 _).continuousAt.comp
      (normalChartField_hasDerivAt g c e (fun _ => a) (fun _ => 0) r hr
        (hasDerivAt_const r a)).continuousAt)
  have hp := endpointCorrectedPosition_continuousAt x y A.position B.position
    u v 0 r hx hy A.position_continuous.continuousAt B.position_continuous.continuousAt
  have hzero : endpointCorrectedPosition x y A.position B.position u v 0 r = x r :=
    endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero
  have hin : endpointCorrectedPosition x y A.position B.position u v 0 r ∈
      (chartAt FourSpace c).target := by
    rw [hzero]
    exact (chartAt FourSpace c).map_source hr
  exact ((chartAt FourSpace c).continuousAt_symm hin).comp
    (x := (0,r))
    (f := fun p : ℝ × ℝ => endpointCorrectedPosition x y A.position B.position u v p.1 p.2) hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous joint inverse branch agrees with the original radial
segment close to its nonconjugate endpoint. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem joint_exponential_log_radial_eventually (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (htc : t < actualFirstConjugateTime g hRic e)
    (U : Set (FrameBundle g × M)) (hU : IsOpen U)
    (heU : (e,frameGeodesic g 0 e t) ∈ U)
    (log : FrameBundle g × M → FourSpace) (hlog : ContinuousOn log U)
    (hlog0 : log (e,frameGeodesic g 0 e t) = t • coordinateVector 0)
    (hreal : ∀ p ∈ U, frameExponential g o p.1 (log p) = p.2) :
    ∀ᶠ s in 𝓝 t, log (e,frameGeodesic g 0 e s) = s • coordinateVector 0 := by
  obtain ⟨V,_,heV,r,hr,hinj⟩ := frameExponential_common_injective_neighborhood g o hRic e he t ht htc
  let f : ℝ → FrameBundle g × M := fun s => (e,frameGeodesic g 0 e s)
  have hf : Continuous f := continuous_const.prodMk (frameGeodesic_continuous g 0 e)
  have hl : ContinuousAt (fun s => log (f s)) t :=
    (hlog.continuousAt (hU.mem_nhds heU)).comp (x := t) (f := f) hf.continuousAt
  have hline : Continuous (fun s : ℝ => s • (coordinateVector 0 : FourSpace)) :=
    continuous_id.smul continuous_const
  have hL : ∀ᶠ s in 𝓝 t, log (f s) ∈ ball (t • coordinateVector 0) r := by
    apply hl.preimage_mem_nhds
    rw [hlog0]
    exact ball_mem_nhds _ hr
  have hR : ∀ᶠ s in 𝓝 t, s • (coordinateVector 0 : FourSpace) ∈ ball (t • coordinateVector 0) r :=
    hline.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)
  have hmem : ∀ᶠ s in 𝓝 t, f s ∈ U := hf.continuousAt.preimage_mem_nhds (hU.mem_nhds heU)
  filter_upwards [hL,hR,hmem] with s hs hs' hsU
  apply hinj e heV hs hs'
  rw [hreal _ hsU,frameExponential_first_ray_all g o e he s]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual normal variations with endpoint curves of zero covariant acceleration. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
theorem normalQuadraticSegmentEnergy_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t)
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    normalSegmentEnergy g e c N P A.position B.position a b 0 = (b - a) / 2 := by
  have href : EqOn (normalSegmentCurve g e c N A.position B.position a b 0)
      (frameGeodesic g 0 e) (Icc a b) :=
    fun t ht => normalQuadraticSegmentCurve_zero g e c N A B (hc t ht)
  have hz : ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b 0 t ∈
        (chartAt FourSpace c).target := by
    intro t ht
    unfold normalSegmentPosition
    rw [endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero]
    exact (chartAt FourSpace c).map_source (hc t ht)
  rw [normalSegmentEnergy_eq_actual g e c N P A.position B.position hab hc hN hz,
    metricCurveEnergy_congr g hab.le href, frameGeodesic_energy g 0 e hab]

theorem normalQuadraticSegmentEnergy_secondDeriv (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (deriv (normalSegmentEnergy g e c N P A.position B.position a b))
      (∫ t in a..b, chartEnergySecondDensity g c
        (chartAt FourSpace c (frameGeodesic g 0 e t))
        (normalChartField g c e N t) (geodesicChartVelocity g c e t)
        (normalChartFieldRate g c e N P t)
        (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t))
        (WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0))) 0 := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have h := endpointCorrected_energy_secondDerivOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hδ hab.le
    hx hy hv hw A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn
    (fun ε hε => (A.derivative ε (ha ε hε)).1)
    (fun ε hε => (B.derivative ε (hb ε hε)).1)
    (fun ε hε => (A.derivative ε (ha ε hε)).2)
    (fun ε hε => (B.derivative ε (hb ε hε)).2) hz
  have hA0 : A.position 0 = x a := A.position_zero
  have hB0 : B.position 0 = x b := B.position_zero
  have hA1 : A.first 0 = y a := A.first_zero
  have hB1 : B.first 0 = y b := B.first_zero
  have hX (t : ℝ) := endpointCorrectedPosition_zero x y A.position B.position a b t hA0 hB0
  have hY (t : ℝ) := endpointCorrectedParameter_zero y A.first B.first a b t hA1 hB1
  have hV (t : ℝ) := endpointCorrectedVelocity_zero x y v w A.position B.position a b t hA0 hB0
  have hW (t : ℝ) := endpointCorrectedMixed_zero y w A.first B.first a b t hA1 hB1
  simpa only [hX, hY, hV, hW, x, y, v, w, WithLp.ofLp_toLp,
    normalSegmentEnergy, normalSegmentPosition, normalSegmentVelocity] using! h

theorem normalQuadraticSegmentEnergy_first_differentiable (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (normalSegmentEnergy g e c N P A.position B.position a b) ε := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have hcont := endpointCorrected_energy_continuousOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hx hy hv hw
    A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn hz
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ by constructor <;> linarith)] with ε hε
  apply HasDerivAt.differentiableAt
  apply intervalIntegral_hasDerivAt_rectangle
    (fun ε t => chartEnergyDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
      (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t)))
    (fun ε t => chartEnergyFirstDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
      (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b ε t))
      (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t))
      (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b ε t)))
    hab.le hε hcont.1 hcont.2.1
  intro s hs t ht
  apply chartEnergy_firstJet_hasDerivAt
  · exact hz s ⟨hs.1.le, hs.2.le⟩ t ht
  · simpa only [WithLp.toLp_ofLp] using endpointCorrectedPosition_parameter x y
      A.position B.position A.first B.first a b s t
      (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1
  · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt s (endpointCorrectedVelocity_parameter x y v w
        A.position B.position A.first B.first a b s t
        (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first energy density of a normal variation vanishes in the
actual Levi-Civita connection, including nonconstant normal components. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartEnergyFirstDensity_covariant (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (y v w : JacobiCoordinateVector) :
    chartEnergyFirstDensity g c z y v w =
      jacobiMetricPair (metricInChart g c z) v
        (w + jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ y) := by
  have hG : (metricInChart g c z).IsSymm := by
    ext i j
    exact metricInChart_comm g c z j i
  rw [chartEnergyFirstDensity,jacobiMetricFirstDirectional_eq g c z hz,
    jacobiMetricRate_pair,jacobiMetricPair_symm hG _ v,
    actual_jacobiConnection_comm g c z y v,jacobiMetricPair_add_right]
  ring

theorem frame_normal_first_density_zero (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (a b : Fin 3 → ℝ) :
    chartEnergyFirstDensity g c (chartAt FourSpace c e.base)
      (frameChartMatrix g c e *ᵥ Fin.cons 0 a)
      (fun i => frameChartMatrix g c e i 0)
      (frameChartMatrix g c e *ᵥ Fin.cons 0 b -
        jacobiConnection (fun i => connectionMatrix g c i (chartAt FourSpace c e.base))
          (fun i => frameChartMatrix g c e i 0) *ᵥ
            (frameChartMatrix g c e *ᵥ Fin.cons 0 a)) = 0 := by
  rw [chartEnergyFirstDensity_covariant g c _ ((chartAt FourSpace c).map_source he),sub_add_cancel]
  have hv : (fun i => frameChartMatrix g c e i 0) =
      frameChartMatrix g c e *ᵥ Pi.single 0 (1 : ℝ) := by
    ext i
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [hv,jacobiMetricPair_frame _ _ (frameChartMatrix_normalizes g c e he)]
  simp [dotProduct,Pi.single_apply]

variable [T3Space M] [CompactSpace M]

theorem normalChartField_first_density_zero (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (N P : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source) :
    chartEnergyFirstDensity g c (chartAt FourSpace c (frameGeodesic g 0 e t))
      (normalChartField g c e N t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e N P t) = 0 := by
  rw [normalChartFieldRate_eq]
  exact frame_normal_first_density_zero g c (parallelFrameFlowMap g 0 t e) hc (N t) (P t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The corrected normal variation has exactly the index as its second
energy derivative: both actual endpoint acceleration terms vanish. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalQuadraticSegmentSecond_integral (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : M) (N P : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    (∫ t in a..b, chartEnergySecondDensity g c
      (chartAt FourSpace c (frameGeodesic g 0 e t))
      (normalChartField g c e N t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e N P t)
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t))
      (WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0))) =
      (∫ t in a..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (N t) (P t)) := by
  let U : ℝ → JacobiCoordinateVector := fun t =>
    WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t)
  let Q : ℝ → JacobiCoordinateVector := fun _ =>
    WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0)
  have hU : Continuous U := (PiLp.continuous_ofLp 2 _).comp
    ((continuous_endpointCorrectedSecond A.second B.second a b
      A.second_continuous B.second_continuous).comp (continuous_const.prodMk continuous_id))
  have hQ : Continuous Q := continuous_const
  have hu (t : ℝ) : HasDerivAt U (Q t) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt t (endpointCorrectedSecond_time A.second B.second a b 0 t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hS := continuousOn_chartEnergySecondDensity g c
    (fun t => chartAt FourSpace c (frameGeodesic g 0 e t))
    (normalChartField g c e N) (geodesicChartVelocity g c e)
    (normalChartFieldRate g c e N P) U Q
    (geodesicChartPosition_continuousOn g c e _ hc)
    (normalChartField_continuousOn g c e N _ hc hNc)
    (geodesicChartVelocity_continuousOn g c e _ hc)
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
    hU.continuousOn hQ.continuousOn
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
  have hi := normalChartField_second_integral g hRic c e N P U Q a b
    (by simpa only [uIcc_of_le hab.le, frameGeodesic] using hc)
    (by simpa only [uIcc_of_le hab.le] using hN)
    (by simpa only [uIcc_of_le hab.le] using hP)
    (fun t _ => hu t) (hS.intervalIntegrable_of_Icc hab.le)
  have hleft : chartEnergyBoundary g c (chartAt FourSpace c (frameGeodesic g 0 e a))
      (geodesicChartVelocity g c e a) (normalChartField g c e N a) (U a) = 0 := by
    change chartEnergyBoundary g c _ _ _
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 a)) = _
    rw [endpointCorrectedSecond_left _ _ _ _ _ hab.ne, A.second_zero,WithLp.ofLp_toLp]
    exact normalQuadratic_boundary_chart_zero g (parallelFrameFlowMap g 0 a e) c
      (hc a ⟨le_rfl, hab.le⟩) (N a)
  have hright : chartEnergyBoundary g c (chartAt FourSpace c (frameGeodesic g 0 e b))
      (geodesicChartVelocity g c e b) (normalChartField g c e N b) (U b) = 0 := by
    change chartEnergyBoundary g c _ _ _
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 b)) = _
    rw [endpointCorrectedSecond_right _ _ _ _ _ hab.ne, B.second_zero,WithLp.ofLp_toLp]
    exact normalQuadratic_boundary_chart_zero g (parallelFrameFlowMap g 0 b e) c
      (hc b ⟨hab.le, le_rfl⟩) (N b)
  simp only [frameGeodesic] at hleft hright
  rw [hleft, hright,add_zero,sub_zero] at hi
  exact hi

theorem normalQuadraticSegmentEnergy_index_secondDeriv (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : M) (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ}
    (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (deriv (normalSegmentEnergy g e c N P A.position B.position a b))
      ((∫ t in a..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (N t) (P t))) 0 := by
  have h := normalQuadraticSegmentEnergy_secondDeriv g e c N P hab hδ hc hN hP A B hA hB hz
  rw [normalQuadraticSegmentSecond_integral g hRic e c N P hab hc hN hP A B] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact set of minimizing tangent vectors and its polar
cut-time description. Its exponential image is the whole manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualMinimizingTangentDomain_compact (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : IsCompact (actualMinimizingTangentDomain g o e) := by
  obtain ⟨D, hD, hbound⟩ := metricEDistance_uniform_bound g e.base
  apply (isCompact_closedBall (0 : FourSpace) D).of_isClosed_subset
    (actualMinimizingTangentDomain_closed g o e)
  intro v hv
  have heq := (metricDistance_eq_iff g e.base (frameExponential g o e v) (norm_nonneg v)).mp hv
  have hle : ‖v‖ ≤ D := (ENNReal.ofReal_le_ofReal_iff hD).mp (heq ▸ hbound _)
  simpa only [mem_closedBall, dist_zero_right] using hle

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual quadratic normal variation has zero first energy derivative. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalQuadraticSegmentEnergy_first_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (normalSegmentEnergy g e c N P A.position B.position a b) 0 0 := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have hcont := endpointCorrected_energy_continuousOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hx hy hv hw
    A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn hz
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hε : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith,hδ⟩
  have hd : HasDerivAt (normalSegmentEnergy g e c N P A.position B.position a b)
      (∫ t in a..b, chartEnergyFirstDensity g c
        (endpointCorrectedPosition x y A.position B.position a b 0 t)
        (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b 0 t))
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b 0 t))
        (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b 0 t))) 0 := by
    apply intervalIntegral_hasDerivAt_rectangle
      (fun ε t => chartEnergyDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t)))
      (fun ε t => chartEnergyFirstDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
        (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b ε t))
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t))
        (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b ε t)))
      hab.le hε hcont.1 hcont.2.1
    intro s hs t ht
    apply chartEnergy_firstJet_hasDerivAt
    · exact hz s ⟨hs.1.le, hs.2.le⟩ t ht
    · simpa only [WithLp.toLp_ofLp] using endpointCorrectedPosition_parameter x y
        A.position B.position A.first B.first a b s t
        (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1
    · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
        |>.comp_hasDerivAt s (endpointCorrectedVelocity_parameter x y v w
          A.position B.position A.first B.first a b s t
          (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1)
  have hA0 : A.position 0 = x a := A.position_zero
  have hB0 : B.position 0 = x b := B.position_zero
  have hA1 : A.first 0 = y a := A.first_zero
  have hB1 : B.first 0 = y b := B.first_zero
  have hX (t : ℝ) := endpointCorrectedPosition_zero x y A.position B.position a b t hA0 hB0
  have hY (t : ℝ) := endpointCorrectedParameter_zero y A.first B.first a b t hA1 hB1
  have hV (t : ℝ) := endpointCorrectedVelocity_zero x y v w A.position B.position a b t hA0 hB0
  have hW (t : ℝ) := endpointCorrectedMixed_zero y w A.first B.first a b t hA1 hB1
  have heq : (∫ t in a..b, chartEnergyFirstDensity g c
        (endpointCorrectedPosition x y A.position B.position a b 0 t)
        (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b 0 t))
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b 0 t))
        (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b 0 t))) = 0 := by
    calc
      _ = ∫ t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab.le] at ht
        simpa only [hX,hY,hV,hW,x,y,v,w,WithLp.ofLp_toLp] using
          normalChartField_first_density_zero g c e N P t (hc t ht)
      _ = 0 := intervalIntegral.integral_zero
  rwa [heq] at hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! Before its cut time an actual radial geodesic is the unique minimizing
radial segment to its endpoint. This follows from the no-corner theorem. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem positive_frames_relative_rotation (g : SmoothMetric M) (o : FrameOrientation g)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hbase : e.base = f.base) :
    ∃ Q : OrientedOrthogonalFour, e.rotate (orientedToOrthogonal Q) = f := by
  cases e with
  | mk x E =>
    cases f with
    | mk y F =>
      change x = y at hbase
      subst y
      have hsign := (o.compatible x E F he).mp hf
      exact ⟨orientedFrameChange E F hsign, orientedFrameMap_change E F hsign⟩

variable [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem frameGeodesic_minimizing_initial_unique (g : SmoothMetric M)
    (o : FrameOrientation g) (e f : FrameBundle g)
    (he : e ∈ o.positive) (hf : f ∈ o.positive) (hbase : e.base = f.base)
    (t : ℝ) (ht : 0 < t) (htc : t < actualCutTime g e)
    (hend : frameGeodesic g 0 e t = frameGeodesic g 0 f t) :
    unitTangentOfFrame e = unitTangentOfFrame f := by
  let E := parallelFrameFlowMap g 0 t e
  let F := parallelFrameFlowMap g 0 t f
  have hE : E ∈ o.positive := parallelFrameFlowMap_positive g o e he t
  have hF : F ∈ o.positive := parallelFrameFlowMap_positive g o f hf t
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o E F hE hF hend
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property
  let u : FourSpace := L (coordinateVector 0)
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖(coordinateVector 0 : FourSpace)‖ from L.norm_map _]
    exact firstDirection.property
  let s := (actualCutTime g e - t) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hts : t + s ≤ actualCutTime g e := by dsimp [s]; linarith
  have hleft : frameExponential g o E ((-t) • u) = f.base := by
    have hrot := frameExponential_rotate g o E Q ((-t) • coordinateVector 0)
    rw [hQ, map_smul] at hrot
    rw [← hrot, frameExponential_shift_first g o f hf (-t) t, neg_add_cancel]
    simp only [frameGeodesic, parallelFrameFlowMap_zero]
  have hright : frameExponential g o E (s • coordinateVector 0) =
      frameGeodesic g 0 e (t + s) := by
    rw [frameExponential_shift_first g o e he s t, add_comm]
  have hmin : metricEDistance g (frameExponential g o E ((-t) • u))
      (frameExponential g o E (s • coordinateVector 0)) = ENNReal.ofReal (t + s) := by
    rw [hleft, hright, ← hbase]
    exact (show t + s ∈ frameMinimizingTimes g e from by
      rw [frameMinimizingTimes_eq_Icc]; exact ⟨(add_pos ht hs).le,hts⟩).2
  have hueq : u = coordinateVector 0 := frameExponential_no_minimizing_corner g o E
    u (coordinateVector 0) hu firstDirection.property t s ht hs hmin
  have hstate : unitTangentOfFrame E = unitTangentOfFrame F := by
    rw [← hQ]
    apply unitTangent_ext (u := unitTangentOfFrame E)
      (v := unitTangentOfFrame (E.rotate (orientedToOrthogonal Q))) rfl
    change E.frame.vector 0 = (E.rotate (orientedToOrthogonal Q)).frame.vector 0
    rw [← E.frame.map_coordinateVector, ← (E.rotate (orientedToOrthogonal Q)).frame.map_coordinateVector,
      frameRotate_map]
    change E.frame.map (coordinateVector 0) = E.frame.map u
    rw [hueq]
  have hb := unitTangentOfFrame_flow_eq g o E F hE hF hstate (-t)
  dsimp [E,F] at hb
  rw [← parallelFrameFlowMap_add, ← parallelFrameFlowMap_add, neg_add_cancel,
    parallelFrameFlowMap_zero, parallelFrameFlowMap_zero] at hb
  exact hb

theorem frameExponential_minimizing_before_cut_unique (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (htc : t < actualCutTime g e)
    (w : FourSpace) (hw : w ∈ actualMinimizingTangentDomain g o e)
    (hend : frameExponential g o e w = frameGeodesic g 0 e t) :
    w = t • coordinateVector 0 := by
  have hmin : t ∈ frameMinimizingTimes g e := by
    rw [frameMinimizingTimes_eq_Icc]; exact ⟨ht.le,htc.le⟩
  have hn : ‖w‖ = t := by
    rw [← hw, hend]
    exact (metricDistance_eq_iff g _ _ ht.le).mpr hmin.2
  let p : Directions := ⟨t⁻¹ • w, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),hn,inv_mul_cancel₀ ht.ne']⟩
  have hp : t • p.val = w := by
    change t • (t⁻¹ • w) = w
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix p))
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hpoint : frameGeodesic g 0 e t = frameGeodesic g 0 f t := by
    rw [← frameExponential_direction_ray g o e he p t,hp]
    exact hend.symm
  have hs := frameGeodesic_minimizing_initial_unique g o e f he hf rfl t ht htc hpoint
  have hv := congrArg (fun u : UnitTangentBundle g => u.vector) hs
  have hdir : p.val = coordinateVector 0 := by
    apply e.frame.map_injective
    change e.frame.vector 0 = (e.frame.turn p).vector 0 at hv
    rw [e.frame.turn_first] at hv
    rw [e.frame.map_coordinateVector]
    exact hv.symm
  rw [← hp,hdir]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing vectors over all positive frames form a compact
set. This gives uniform control of fibers near a unique minimizing vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualMinimizingFramePairs_compact (g : SmoothMetric M) (o : FrameOrientation g) :
    IsCompact (actualMinimizingFramePairs g o) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  obtain ⟨D,hD⟩ := (isCompact_range (metricDistance_continuous g)).bddAbove
  have hc : IsClosed (actualMinimizingFramePairs g o) :=
    (o.clopen.isClosed.preimage continuous_fst).inter
      (isClosed_eq ((metricDistance_continuous g).comp
        (((continuous_frameBase g).comp continuous_fst).prodMk
          (frameExponential_joint_continuous g o))) (continuous_norm.comp continuous_snd))
  apply (isCompact_univ.prod (isCompact_closedBall (0 : FourSpace) D)).of_isClosed_subset hc
  intro p hp
  refine ⟨mem_univ _, ?_⟩
  rw [mem_closedBall, dist_zero_right]
  rw [← hp.2]
  exact hD ⟨(p.1.base,frameExponential g o p.1 p.2),rfl⟩

theorem minimizing_vectors_common_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (t : ℝ) (U : Set FourSpace)
    (hU : IsOpen U)
    (hunique : ∀ w ∈ actualMinimizingTangentDomain g o e,
      frameExponential g o e w = frameGeodesic g 0 e t → w ∈ U) :
    ∃ V : Set (FrameBundle g), IsOpen V ∧ e ∈ V ∧
      ∀ f ∈ V, f ∈ o.positive → ∀ w ∈ actualMinimizingTangentDomain g o f,
        frameExponential g o f w = frameGeodesic g 0 f t → w ∈ U := by
  let K := actualMinimizingFramePairs g o ∩
    {p : FrameBundle g × FourSpace | frameExponential g o p.1 p.2 = frameGeodesic g 0 p.1 t} ∩
    {p : FrameBundle g × FourSpace | p.2 ∉ U}
  have hendpoint : Continuous (fun p : FrameBundle g × FourSpace => frameGeodesic g 0 p.1 t) :=
    ((continuous_frameBase g).comp (parallelFrameFlowMap_continuous_slice g 0 t)).comp continuous_fst
  have hK : IsCompact K :=
    ((actualMinimizingFramePairs_compact g o).inter_right
      (isClosed_eq (frameExponential_joint_continuous g o) hendpoint)).inter_right
        (hU.isClosed_compl.preimage continuous_snd)
  have hclosed : IsClosed (Prod.fst '' K) := (hK.image continuous_fst).isClosed
  refine ⟨(Prod.fst '' K)ᶜ,hclosed.isOpen_compl,?_,?_⟩
  · rintro ⟨⟨f,w⟩,⟨⟨hf,heq⟩,hwU⟩,hfe⟩
    change f = e at hfe
    subst f
    exact hwU (hunique w hf.2 heq)
  · intro f hf hpos w hw heq
    by_contra hwU
    exact hf ⟨(f,w),⟨⟨⟨hpos,hw⟩,heq⟩,hwU⟩,rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nonconjugate cut point has two genuine minimizing radial vectors.
The compact set used below consists of actual distance-minimizing vectors. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

private theorem minimizing_vectors_near_unique (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (v : FourSpace)
    (U : Set FourSpace) (hU : IsOpen U) (hvU : v ∈ U)
    (hunique : ∀ w ∈ actualMinimizingTangentDomain g o e,
      frameExponential g o e w = frameExponential g o e v → w = v) :
    ∃ V : Set M, IsOpen V ∧ frameExponential g o e v ∈ V ∧
      ∀ w ∈ actualMinimizingTangentDomain g o e,
        frameExponential g o e w ∈ V → w ∈ U := by
  let K := actualMinimizingTangentDomain g o e ∩ Uᶜ
  have hK : IsCompact K := (actualMinimizingTangentDomain_compact g o e).inter_right
    hU.isClosed_compl
  have hclosed : IsClosed (frameExponential g o e '' K) :=
    (hK.image (frameExponential_continuous g o e)).isClosed
  refine ⟨(frameExponential g o e '' K)ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨w, hw, heq⟩
    exact hw.2 ((hunique w hw.1 heq) ▸ hvU)
  · intro w hw hV
    by_contra hnot
    exact hV ⟨w, ⟨hw, hnot⟩, rfl⟩

theorem actualCutTime_second_minimizing_vector (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hnoconj : actualCutTime g e < actualFirstConjugateTime g hRic e) :
    ∃ w : FourSpace, w ∈ actualMinimizingTangentDomain g o e ∧
      frameExponential g o e w = frameGeodesic g 0 e (actualCutTime g e) ∧
      w ≠ actualCutTime g e • coordinateVector 0 := by
  classical
  let c := actualCutTime g e
  let v : FourSpace := c • coordinateVector 0
  have hc : 0 < c := actualCutTime_pos g o hRic e he
  have hv : frameExponential g o e v = frameGeodesic g 0 e c :=
    frameExponential_first_ray g o e he c hc
  by_contra hnot
  have hunique : ∀ w ∈ actualMinimizingTangentDomain g o e,
      frameExponential g o e w = frameExponential g o e v → w = v := by
    intro w hw heq
    by_contra hne
    exact hnot ⟨w, hw, heq.trans hv, hne⟩
  obtain ⟨C, hvC, hC⟩ := frameExponential_preconjugate_localChart g o hRic e he c hc hnoconj
  obtain ⟨V, hV, hvV, hnear⟩ := minimizing_vectors_near_unique g o e v
    C.source C.open_source hvC hunique
  let line : ℝ → FourSpace := fun t => t • coordinateVector 0
  have hl : Continuous line := continuous_id.smul continuous_const
  have hgood : {t : ℝ | line t ∈ C.source ∧ frameExponential g o e (line t) ∈ V ∧ 0 < t}
      ∈ 𝓝 c := by
    exact Filter.inter_mem (C.open_source.preimage hl |>.mem_nhds hvC)
      (Filter.inter_mem (hV.preimage ((frameExponential_continuous g o e).comp hl)
        |>.mem_nhds hvV) (Ioi_mem_nhds hc))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let t := c + δ / 2
  have htc : c < t := by dsimp [t]; linarith
  have htg : line t ∈ C.source ∧ frameExponential g o e (line t) ∈ V ∧ 0 < t := by
    apply hball
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr htc)]
    dsimp [t]
    linarith
  obtain ⟨w, hw, hn⟩ := frameExponential_global_minimizing g o hRic e he
    (frameExponential g o e (line t))
  have hwK : w ∈ actualMinimizingTangentDomain g o e := by
    change metricDistance g e.base (frameExponential g o e w) = ‖w‖
    rw [hw, hn]
  have hwC : w ∈ C.source := hnear w hwK (hw ▸ htg.2.1)
  have heq : w = line t := C.injOn hwC htg.1
    ((hC hwC).trans (hw.trans (hC htg.1).symm))
  have hnline : ‖line t‖ = t := by
    dsimp [line]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htg.2.2]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit, mul_one]
  have hmin : t ∈ frameMinimizingTimes g e := by
    refine ⟨htg.2.2.le, ?_⟩
    have hd : metricDistance g e.base (frameGeodesic g 0 e t) = t := by
      rw [heq, hnline, frameExponential_first_ray g o e he t htg.2.2] at hn
      exact hn.symm
    exact (metricDistance_eq_iff g _ _ htg.2.2.le).mp hd
  rw [frameMinimizingTimes_eq_Icc] at hmin
  exact (not_lt_of_ge hmin.2) htc

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform actual cut-time lower bound gives minimizing and injective normal balls. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_minimizing_of_cut_lower (R : ℝ)
    (hcut : ∀ e ∈ o.positive, R ≤ actualCutTime g e)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ ≤ R) :
    metricDistance g e.base (frameExponential g o e v) = ‖v‖ := by
  by_cases hz : v = 0
  · subst v
    rw [frameExponential_zero, norm_zero]
    exact (metricDistance_eq_zero_iff g _ _).mpr rfl
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hm : ‖v‖ • q.val ∈ actualMinimizingTangentDomain g o e := by
    apply (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖ (norm_nonneg _)).mpr
    exact hv.trans (hcut _ (frameRotate_oriented_positive o e he _))
  rwa [hrad] at hm

theorem direction_injective_of_cut_lower (R : ℝ)
    (hcut : ∀ e ∈ o.positive, R ≤ actualCutTime g e)
    (e : FrameBundle g) (he : e ∈ o.positive) (q p : Directions)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R)
    (hqp : frameExponential g o e (t • q.val) = frameExponential g o e (t • p.val)) : q = p := by
  let s := (R - t) / 2
  have hs : 0 < s := by dsimp [s]; linarith [ht.2]
  have hsum : t + s < R := by dsimp [s]; linarith [ht.2]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := parallelFrameFlowMap g 0 (-s) f
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hF : F ∈ o.positive := parallelFrameFlowMap_positive g o f hf (-s)
  have hbase : F.base = frameExponential g o e ((-s) • q.val) :=
    (frameExponential_direction_ray g o e he q (-s)).symm
  have hend : frameExponential g o F ((t + s) • coordinateVector 0) =
      frameExponential g o e (t • p.val) := by
    rw [frameExponential_shift_first g o f hf (t + s) (-s),
      show t + s + -s = t by ring]
    exact (frameExponential_direction_ray g o e he q t).symm.trans hqp
  have hnorm : ‖(t + s) • (coordinateVector 0 : FourSpace)‖ = t + s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos ht.1 hs)]
    simp [coordinateVector]
  have hmin := frameExponential_minimizing_of_cut_lower R hcut F hF
    ((t + s) • coordinateVector 0) (by rw [hnorm]; exact hsum.le)
  rw [hbase, hend, hnorm] at hmin
  have hd := (metricDistance_eq_iff g _ _ (add_pos ht.1 hs).le).mp hmin
  rw [add_comm t s] at hd
  exact Subtype.ext (frameExponential_no_minimizing_corner g o e q.val p.val
    q.property p.property s t hs ht.1 hd)

theorem frameExponential_injOn_ball_of_cut_lower (R : ℝ)
    (hcut : ∀ e ∈ o.positive, R ≤ actualCutTime g e)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    InjOn (frameExponential g o e) (Metric.ball 0 R) := by
  intro v hv w hw heq
  have hvπ : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hwπ : ‖w‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hn : ‖v‖ = ‖w‖ := by
    rw [← frameExponential_minimizing_of_cut_lower R hcut e he v hvπ.le,
      ← frameExponential_minimizing_of_cut_lower R hcut e he w hwπ.le, heq]
  by_cases hz : v = 0
  · subst v
    have hwzero : w = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hn.symm)
    exact hwzero.symm
  have hwz : w ≠ 0 := fun h => hz (norm_eq_zero.mp (by simpa only [h, norm_zero] using hn))
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  let p : Directions := ⟨‖w‖⁻¹ • w, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwz)]⟩
  have hq : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hp : ‖v‖ • p.val = w := by
    change ‖v‖ • (‖w‖⁻¹ • w) = w
    rw [hn, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hwz), one_smul]
  have hqp : q = p := direction_injective_of_cut_lower R hcut e he q p
    ‖v‖ ⟨norm_pos_iff.mpr hz, hvπ⟩ (by rwa [hq, hp])
  rw [← hq, hqp, hp]


end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine finite chart variation of a geodesic in a parallel normal
direction strictly lowers its energy when sectional curvature is positive.
The endpoint curves have zero covariant acceleration, and are shared by
all adjacent pieces. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_finite_parallel_normal_shortening (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (n : ℕ) (hn : 0 < n) (t : ℕ → ℝ) (c : ℕ → M)
    (a : Fin 3 → ℝ) (ha : a ≠ 0)
    (ht : ∀ i < n, t i < t (i + 1))
    (hc : ∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)),
      frameGeodesic g 0 e r ∈ (chartAt FourSpace (c i)).source) :
    ∃ γ : ℕ → ℝ → ℝ → M,
      (∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)), γ i 0 r = frameGeodesic g 0 e r) ∧
      (∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)),
        ContinuousAt (fun p : ℝ × ℝ => γ i p.1 p.2) (0,r)) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i ε) (Icc (t i) (t (i + 1)))) ∧
        (∀ i < n, γ i ε (t i) = normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 (t i) e) a ε ∧
          γ i ε (t (i + 1)) = normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 (t (i + 1)) e) a ε) ∧
        (∑ i ∈ Finset.range n, metricCurveEnergy g (γ i ε) (t i) (t (i + 1))) <
          (t n - t 0) / 2 := by
  classical
  let A := fun i : Fin n => Classical.choice (exists_normalQuadraticJetData g
    (parallelFrameFlowMap g 0 (t i.val) e) (c i.val)
      (hc i.val i.isLt (t i.val) ⟨le_rfl,(ht i.val i.isLt).le⟩) a)
  let B := fun i : Fin n => Classical.choice (exists_normalQuadraticJetData g
    (parallelFrameFlowMap g 0 (t (i.val + 1)) e) (c i.val)
      (hc i.val i.isLt (t (i.val + 1)) ⟨(ht i.val i.isLt).le,le_rfl⟩) a)
  let N : ℝ → Fin 3 → ℝ := fun _ => a
  let P : ℝ → Fin 3 → ℝ := fun _ => 0
  have hN (i : Fin n) (r : ℝ) (_ : r ∈ Icc (t i.val) (t (i.val + 1))) :
      HasDerivAt N (P r) r := hasDerivAt_const r a
  choose δ hδ hδA hδB hinside using fun i : Fin n =>
    normalQuadraticSegment_common_radius g e (c i.val) N (ht i.val i.isLt)
      (hc i.val i.isLt) continuousOn_const (A i) (B i)
  let E : ℕ → ℝ → ℝ := fun i ε => if hi : i < n then
    normalSegmentEnergy g e (c i) N P (A ⟨i,hi⟩).position (B ⟨i,hi⟩).position
      (t i) (t (i + 1)) ε else 0
  let γ : ℕ → ℝ → ℝ → M := fun i ε => if hi : i < n then
    normalSegmentCurve g e (c i) N (A ⟨i,hi⟩).position (B ⟨i,hi⟩).position
      (t i) (t (i + 1)) ε else frameGeodesic g 0 e
  let I : ℕ → ℝ := fun i => ∫ r in t i..t (i + 1),
    normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) a 0
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin n, ε ∈ Icc (-δ i) (δ i) := by
    apply eventually_all.mpr
    intro i
    exact Icc_mem_nhds (neg_neg_of_pos (hδ i)) (hδ i)
  have hfd : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i < n, DifferentiableAt ℝ (E i) ε := by
    have hh : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin n, DifferentiableAt ℝ (E i.val) ε := by
      apply eventually_all.mpr
      intro i
      simpa only [E,dite_eq_left i.isLt] using
        normalQuadraticSegmentEnergy_first_differentiable g e (c i.val) N P
          (ht i.val i.isLt) (hδ i) (hc i.val i.isLt) (hN i) continuousOn_const
          (A i) (B i) (hδA i) (hδB i) (hinside i)
    filter_upwards [hh] with ε hε i hi
    exact hε ⟨i,hi⟩
  have hzero : (∑ i ∈ Finset.range n, E i 0) = (t n - t 0) / 2 := by
    calc
      _ = ∑ i ∈ Finset.range n, (t (i + 1) - t i) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simpa only [E,dite_eq_left hi'] using
          normalQuadraticSegmentEnergy_zero g e (c i) N P (ht i hi') (hc i hi')
            (hN ⟨i,hi'⟩) (A ⟨i,hi'⟩) (B ⟨i,hi'⟩)
      _ = _ := by rw [← Finset.sum_div,Finset.sum_range_sub]
  have hfirst (i : ℕ) (hi : i < n) : HasDerivAt (E i) 0 0 := by
    simpa only [E,dite_eq_left hi] using
      normalQuadraticSegmentEnergy_first_zero g e (c i) N P (ht i hi) (hδ ⟨i,hi⟩)
        (hc i hi) (hN ⟨i,hi⟩) continuousOn_const (A ⟨i,hi⟩) (B ⟨i,hi⟩)
        (hδA ⟨i,hi⟩) (hδB ⟨i,hi⟩) (hinside ⟨i,hi⟩)
  have hsecond (i : ℕ) (hi : i < n) : HasDerivAt (deriv (E i)) (I i) 0 := by
    simpa only [E,dite_eq_left hi,I,N,P] using
      normalQuadraticSegmentEnergy_index_secondDeriv g hRic e (c i) N P
        (ht i hi) (hδ ⟨i,hi⟩) (hc i hi) (hN ⟨i,hi⟩) continuousOn_const
        (A ⟨i,hi⟩) (B ⟨i,hi⟩) (hδA ⟨i,hi⟩) (hδB ⟨i,hi⟩) (hinside ⟨i,hi⟩)
  have hnegative : (∑ i ∈ Finset.range n, I i) < 0 := by
    have hI (i : ℕ) (hi : i ∈ Finset.range n) : I i < 0 :=
      parallel_normal_index_negative hRic hpositive e a ha (ht i (Finset.mem_range.mp hi))
    have h := Finset.sum_lt_sum (fun i hi => (hI i hi).le)
      ⟨0,Finset.mem_range.mpr hn,hI 0 (Finset.mem_range.mpr hn)⟩
    simpa only [Finset.sum_const_zero] using h
  have hsum0 : deriv (fun ε => ∑ i ∈ Finset.range n, E i ε) 0 = 0 := by
    have h := (HasDerivAt.fun_sum (fun i hi => hfirst i (Finset.mem_range.mp hi))).deriv
    simpa only [Finset.sum_const_zero] using h
  have hsumdiff : ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (fun ε => ∑ i ∈ Finset.range n, E i ε) ε := by
    filter_upwards [hfd] with ε hε
    exact DifferentiableAt.fun_sum (fun i hi => hε i (Finset.mem_range.mp hi))
  have hshort := scalar_second_variation_decreases _ _ hsumdiff hsum0
    (finite_piece_secondDeriv n E I hfd hsecond) hnegative
  rw [hzero] at hshort
  refine ⟨γ,?_,?_,?_⟩
  · intro i hi r hr
    simpa only [γ,dite_eq_left hi] using
      normalQuadraticSegmentCurve_zero g e (c i) N (A ⟨i,hi⟩) (B ⟨i,hi⟩) (hc i hi r hr)
  · intro i hi r hr
    simpa only [γ,dite_eq_left hi,N] using
      normalQuadraticSegmentCurve_continuousAt g e (c i) a (t i) (t (i + 1)) r
        (A ⟨i,hi⟩) (B ⟨i,hi⟩) (hc i hi r hr)
  · filter_upwards [hshort,hnear.filter_mono nhdsWithin_le_nhds] with ε hε hεnear
    have hregion (i : Fin n) : ε ∈ Icc (-(A i).radius) (A i).radius ∧
        ε ∈ Icc (-(B i).radius) (B i).radius := by
      have hh := hεnear i
      have hA := hδA i
      have hB := hδB i
      constructor <;> constructor <;> linarith [hh.1,hh.2]
    refine ⟨?_,?_,?_⟩
    · intro i hi
      simpa only [γ,dite_eq_left hi] using
        normalSegmentCurve_contMDiffOn g e (c i) N P (A ⟨i,hi⟩).position
          (B ⟨i,hi⟩).position (ht i hi) (hc i hi) (hN ⟨i,hi⟩) continuousOn_const
          (hinside ⟨i,hi⟩ ε (hεnear ⟨i,hi⟩))
    · intro i hi
      simpa only [γ,dite_eq_left hi,N] using
        normalQuadraticSegmentCurve_endpoints g e (c i) N (ht i hi)
          (A ⟨i,hi⟩) (B ⟨i,hi⟩) (hregion ⟨i,hi⟩).1 (hregion ⟨i,hi⟩).2
    · have heq : (∑ i ∈ Finset.range n, metricCurveEnergy g (γ i ε) (t i) (t (i + 1))) =
          ∑ i ∈ Finset.range n, E i ε := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simpa only [γ,E,dite_eq_left hi'] using
          (normalSegmentEnergy_eq_actual g e (c i) N P (A ⟨i,hi'⟩).position
            (B ⟨i,hi'⟩).position (ht i hi') (hc i hi') (hN ⟨i,hi'⟩)
            (hinside ⟨i,hi'⟩ ε (hεnear ⟨i,hi'⟩))).symm
      rw [heq]
      exact hε

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform cut bounds compare initial vectors even when their frames
are different. A scalar derivative test supplies strict short variations. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section

theorem scalar_decreases_right {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (ha : a < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have hs := hf.hasDerivWithinAt.limsup_slope_le' (s := Ioi (0 : ℝ)) (by simp) ha
  filter_upwards [hs,self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field,sub_zero] at ht
  have h := (div_lt_iff₀ htpos).mp ht
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem uniform_cut_initial_vector_unique (g : SmoothMetric M) (o : FrameOrientation g)
    (c : ℝ) (hcut : ∀ e ∈ o.positive, c ≤ actualCutTime g e)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hbase : e.base = f.base) (v w : FourSpace) (hv : ‖v‖ < c) (hw : ‖w‖ < c)
    (hend : frameExponential g o e v = frameExponential g o f w) :
    e.frame.map v = f.frame.map w := by
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o e f he hf hbase
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property
  have hnorm : ‖L w‖ < c := by rw [L.norm_map]; exact hw
  have hexp : frameExponential g o e v = frameExponential g o e (L w) := by
    rw [← frameExponential_rotate g o e Q w,hQ]
    exact hend
  have heq : v = L w := frameExponential_injOn_ball_of_cut_lower c hcut e he
    (by simpa only [mem_ball,dist_zero_right] using hv)
    (by simpa only [mem_ball,dist_zero_right] using hnorm) hexp
  rw [heq,← hQ,frameRotate_map]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual cut times are lower semicontinuous on the oriented frame bundle,
and attain a positive global minimum. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualCutTime_common_lower_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (htc : t < actualCutTime g e) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∀ f ∈ U, f ∈ o.positive → t ≤ actualCutTime g f := by
  obtain ⟨U,hU,heU,r,hr,hinj⟩ := frameExponential_common_injective_neighborhood g o hRic e he
    t ht (htc.trans_le (actualCutTime_le_firstConjugateTime g hRic e))
  obtain ⟨V,hV,heV,hnear⟩ := minimizing_vectors_common_neighborhood g o e t
    (ball (t • coordinateVector 0) r) isOpen_ball (by
      intro w hw hend
      rw [frameExponential_minimizing_before_cut_unique g o e he t ht htc w hw hend]
      exact mem_ball_self hr)
  refine ⟨U ∩ V,hU.inter hV,⟨heU,heV⟩,?_⟩
  intro f hf hpos
  obtain ⟨w,hw,hn⟩ := frameExponential_global_minimizing g o hRic f hpos
    (frameGeodesic g 0 f t)
  have hwK : w ∈ actualMinimizingTangentDomain g o f := by
    change metricDistance g f.base (frameExponential g o f w) = ‖w‖
    rw [hw,hn]
  have hwball := hnear f hf.2 hpos w hwK hw
  have heq : w = t • coordinateVector 0 := hinj f hf.1 hwball (mem_ball_self hr)
    (hw.trans (frameExponential_first_ray g o f hpos t ht).symm)
  have hnorm : ‖(t • coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit,mul_one]
  rw [heq,hnorm] at hn
  have hm : t ∈ frameMinimizingTimes g f :=
    ⟨ht.le,(metricDistance_eq_iff g _ _ ht.le).mp hn.symm⟩
  rw [frameMinimizingTimes_eq_Icc] at hm
  exact hm.2

theorem actualCutTime_lowerSemicontinuousOn_positive (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    LowerSemicontinuousOn (actualCutTime g) o.positive := by
  apply lowerSemicontinuousOn_iff.mpr
  intro e he
  apply lowerSemicontinuousWithinAt_iff.mpr
  intro a ha
  obtain ⟨t,ht,htc⟩ := exists_between (max_lt (actualCutTime_pos g o hRic e he) ha)
  obtain ⟨U,hU,heU,hbound⟩ := actualCutTime_common_lower_bound g o hRic e he t
    ((le_max_left 0 a).trans_lt ht) htc
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds heU),self_mem_nhdsWithin]
    with f hf hpos
  exact ((le_max_right 0 a).trans_lt ht).trans_le (hbound f hf hpos)

theorem exists_minimal_actualCutTime [Nonempty M] (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    ∃ e ∈ o.positive, 0 < actualCutTime g e ∧
      ∀ f ∈ o.positive, actualCutTime g e ≤ actualCutTime g f := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hne : o.positive.Nonempty :=
    ⟨⟨Classical.arbitrary M,o.frame (Classical.arbitrary M)⟩,o.frame_positive _⟩
  obtain ⟨e,he,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne o.clopen.isClosed.isCompact
    (actualCutTime_lowerSemicontinuousOn_positive g o hRic)
  exact ⟨e,he,actualCutTime_pos g o hRic e he,hmin⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous local inverse branch cannot cross the uniform cut-radius
sphere while its actual endpoint stays strictly inside the distance ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exponential_log_norm_lt_along_curve (g : SmoothMetric M) (o : FrameOrientation g)
    (R : ℝ) (hcut : ∀ e ∈ o.positive, R ≤ actualCutTime g e)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (log : ℝ → FourSpace) (γ : ℝ → M) {a b : ℝ}
    (hlog : ContinuousOn log (Icc a b)) (hstart : ‖log a‖ < R)
    (hreal : ∀ s ∈ Icc a b, frameExponential g o e (log s) = γ s)
    (hdist : ∀ s ∈ Icc a b, metricDistance g e.base (γ s) < R) :
    ∀ s ∈ Icc a b, ‖log s‖ < R := by
  intro s hs
  by_contra hnot
  have hn : R ≤ ‖log s‖ := le_of_not_gt hnot
  have hc : ContinuousOn (fun t => ‖log t‖) (Icc a s) :=
    hlog.norm.mono (Icc_subset_Icc le_rfl hs.2)
  obtain ⟨r,hr,hrR⟩ := intermediate_value_Icc hs.1 hc ⟨hstart.le,hn⟩
  change ‖log r‖ = R at hrR
  have hrb : r ∈ Icc a b := ⟨hr.1,hr.2.trans hs.2⟩
  have hm := frameExponential_minimizing_of_cut_lower R hcut e he (log r) hrR.le
  rw [hreal r hrb,hrR] at hm
  exact (ne_of_lt (hdist r hrb)) hm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous base curve has a local positive orthonormal frame lift
through any prescribed positive frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_moving_positive_frame (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (γ : ℝ → M)
    (hγ : ContinuousAt γ 0) (hγ0 : γ 0 = e.base) :
    ∃ α : ℝ → FrameBundle g, ContinuousAt α 0 ∧ α 0 = e ∧
      (∀ s, (α s).base = γ s) ∧ ∀ᶠ s in 𝓝 (0 : ℝ), α s ∈ o.positive := by
  obtain ⟨S,hS,hpositive⟩ := exists_positive_localGramSection g o e.base
  let F := localGramSection g e.base S hS e.base
  have hF : F ∈ o.positive := hpositive.self_of_nhds
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o F e hF he
    (localGramSection_base g e.base S hS e.base)
  let α : ℝ → FrameBundle g := fun s =>
    (localGramSection g e.base S hS (γ s)).rotate (orientedToOrthogonal Q)
  have hsection : ContinuousAt (fun s => localGramSection g e.base S hS (γ s)) 0 := by
    have hh : ContinuousAt (localGramSection g e.base S hS) (γ 0) := by
      rw [hγ0]; exact continuousAt_localGramSection g e.base S hS
    exact hh.comp hγ
  refine ⟨α,?_,?_,?_,?_⟩
  · exact (continuous_frameRotate g).continuousAt.comp
      (f := fun s => (localGramSection g e.base S hS (γ s),orientedToOrthogonal Q))
      (hsection.prodMk continuousAt_const)
  · change (localGramSection g e.base S hS (γ 0)).rotate (orientedToOrthogonal Q) = e
    rw [hγ0]
    exact hQ
  · intro s
    exact localGramSection_base g e.base S hS (γ s)
  · have hp : ∀ᶠ s in 𝓝 (0 : ℝ), localGramSection g e.base S hS (γ s) ∈ o.positive := by
      have hh : ∀ᶠ x in 𝓝 (γ 0), localGramSection g e.base S hS x ∈ o.positive := by
        rw [hγ0]; exact hpositive
      exact hγ hh
    filter_upwards [hp] with s hs
    exact frameRotate_oriented_positive o _ hs Q

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two nonconjugate branches at a globally shortest cut point have
opposite terminal velocities. Both branches are actual exponential inverses. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem minimal_cut_terminal_opposite (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) (ht : 0 < t)
    (hcut : ∀ e ∈ o.positive, t ≤ actualCutTime g e)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hbase : e.base = f.base)
    (hne : e.frame.vector 0 ≠ f.frame.vector 0)
    (hend : frameGeodesic g 0 e t = frameGeodesic g 0 f t)
    (hte : t < actualFirstConjugateTime g hRic e)
    (htf : t < actualFirstConjugateTime g hRic f) :
    (parallelFrameFlowMap g 0 t e).frame.vector 0 =
      -(parallelFrameFlowMap g 0 t f).frame.vector 0 := by
  let E := parallelFrameFlowMap g 0 t e
  let F := parallelFrameFlowMap g 0 t f
  let d := E.base
  have hFd : F.base = d := hend.symm
  let u := E.frame.vector 0
  let v := F.frame.vector 0
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ := g.inner d
  by_contra hopposite
  have hsum : u + v ≠ 0 := by
    intro h
    apply hopposite
    exact eq_neg_of_add_eq_zero_left h
  have huu : B u u = 1 := E.frame.inner_vector_self 0
  have hvv : B v v = 1 := by
    change g.inner d (F.frame.vector 0) (F.frame.vector 0) = 1
    rw [← hFd]
    exact F.frame.inner_vector_self 0
  have hsym : B v u = B u v := g.symm d v u
  have hpositive : 0 < B (u + v) (u + v) := g.pos d (u + v) hsum
  simp only [map_add,add_apply] at hpositive
  rw [huu,hvv,hsym] at hpositive
  let a : FourSpace := -(u + v)
  have hnegU : g.inner d u a < 0 := by
    dsimp [a]
    change B u (-(u + v)) < 0
    simp only [map_neg,map_add]
    rw [huu]
    linarith
  have hnegV : g.inner d v a < 0 := by
    dsimp [a]
    change B v (-(u + v)) < 0
    simp only [map_neg,map_add]
    rw [hvv,hsym]
    linarith
  obtain ⟨C,hC,hc,hCd⟩ := exists_exponential_log_center g o hRic e he d t ht hte rfl
  obtain ⟨D,hD,hd,hDd⟩ := exists_exponential_log_center g o hRic f hf d t ht htf hFd
  let z := chartAt FourSpace d d
  let x : ℝ → FourSpace := fun ε => C.symm (z + ε • a)
  let y : ℝ → FourSpace := fun ε => D.symm (z + ε • a)
  have hCv : C (t • coordinateVector 0) = z := by
    rw [hC]
    change chartAt FourSpace d (frameExponential g o e (t • coordinateVector 0)) = z
    rw [frameExponential_first_ray g o e he t ht]
  have hDv : D (t • coordinateVector 0) = z := by
    rw [hD]
    change chartAt FourSpace d (frameExponential g o f (t • coordinateVector 0)) = z
    rw [frameExponential_first_ray g o f hf t ht,hFd]
  have hzC : z ∈ C.target := hCv ▸ C.map_source hc
  have hzD : z ∈ D.target := hDv ▸ D.map_source hd
  have hx0 : x 0 = t • coordinateVector 0 := by
    dsimp [x]; rw [zero_smul,add_zero,← hCv]; exact C.left_inv hc
  have hy0 : y 0 = t • coordinateVector 0 := by
    dsimp [y]; rw [zero_smul,add_zero,← hDv]; exact D.left_inv hd
  have hnorm : ‖(t • coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hi : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hi,mul_one]
  have hdx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖x ε‖ ^ 2 < t ^ 2 := by
    have hh := scalar_decreases_right (hCd a) (mul_neg_of_pos_of_neg (mul_pos (by norm_num) ht) hnegU)
    change ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖x ε‖ ^ 2 < ‖x 0‖ ^ 2 at hh
    simpa only [hx0,hnorm] using hh
  have hdy : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε‖ ^ 2 < t ^ 2 := by
    have hh := scalar_decreases_right (hDd a) (mul_neg_of_pos_of_neg (mul_pos (by norm_num) ht) hnegV)
    change ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε‖ ^ 2 < ‖y 0‖ ^ 2 at hh
    simpa only [hy0,hnorm] using hh
  have hline : Continuous (fun ε : ℝ => z + ε • a) := continuous_const.add (continuous_id.smul continuous_const)
  have hxcont : ContinuousAt x 0 := by
    have hcc : ContinuousAt (C.symm : FourSpace → FourSpace) (z + (0 : ℝ) • a) := by
      simpa only [zero_smul,add_zero] using C.continuousAt_symm hzC
    have hh := hcc.comp (x := 0) hline.continuousAt
    simpa only [Function.comp_def,x] using! hh
  have hycont : ContinuousAt y 0 := by
    have hdc : ContinuousAt (D.symm : FourSpace → FourSpace) (z + (0 : ℝ) • a) := by
      simpa only [zero_smul,add_zero] using D.continuousAt_symm hzD
    have hh := hdc.comp (x := 0) hline.continuousAt
    simpa only [Function.comp_def,y] using! hh
  have hpointx : frameExponential g o e (x 0) = d := by
    rw [hx0,frameExponential_first_ray g o e he t ht]
  have hpointy : frameExponential g o f (y 0) = d := by
    rw [hy0,frameExponential_first_ray g o f hf t ht]; exact hFd
  have hnearx : ∀ᶠ ε in 𝓝 (0 : ℝ), frameExponential g o e (x ε) ∈ (chartAt FourSpace d).source :=
    ((frameExponential_continuous g o e).continuousAt.comp hxcont).preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds (hpointx ▸ mem_chart_source FourSpace d))
  have hneary : ∀ᶠ ε in 𝓝 (0 : ℝ), frameExponential g o f (y ε) ∈ (chartAt FourSpace d).source :=
    ((frameExponential_continuous g o f).continuousAt.comp hycont).preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds (hpointy ▸ mem_chart_source FourSpace d))
  have htargets : ∀ᶠ ε in 𝓝 (0 : ℝ), z + ε • a ∈ C.target ∩ D.target := by
    have h0 : z + (0 : ℝ) • a ∈ C.target ∩ D.target := by simpa using And.intro hzC hzD
    exact hline.continuousAt.preimage_mem_nhds ((C.open_target.inter D.open_target).mem_nhds h0)
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), e.frame.map (x ε) = f.frame.map (y ε) := by
    filter_upwards [hdx,hdy,hnearx.filter_mono nhdsWithin_le_nhds,
      hneary.filter_mono nhdsWithin_le_nhds,htargets.filter_mono nhdsWithin_le_nhds]
      with ε hx hy hxs hys htg
    have hxlt : ‖x ε‖ < t := by nlinarith [norm_nonneg (x ε)]
    have hylt : ‖y ε‖ < t := by nlinarith [norm_nonneg (y ε)]
    apply uniform_cut_initial_vector_unique g o t hcut e f he hf hbase (x ε) (y ε) hxlt hylt
    apply (chartAt FourSpace d).injOn hxs hys
    calc
      _ = C (x ε) := (congrFun hC (x ε)).symm
      _ = z + ε • a := C.right_inv htg.1
      _ = D (y ε) := (D.right_inv htg.2).symm
      _ = _ := congrFun hD (y ε)
  have hl : Tendsto (fun ε => e.frame.map (x ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (e.frame.map (t • coordinateVector 0))) := by
    rw [← hx0]
    exact ((e.frame.map.toContinuousLinearMap.continuous.continuousAt).comp hxcont).tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun ε => f.frame.map (y ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (f.frame.map (t • coordinateVector 0))) := by
    rw [← hy0]
    exact ((f.frame.map.toContinuousLinearMap.continuous.continuousAt).comp hycont).tendsto.mono_left nhdsWithin_le_nhds
  have hsame := tendsto_nhds_unique (hl.congr' heq) hr
  have hvectors := congrArg (fun w : FourSpace => t⁻¹ • w) hsame
  apply hne
  simpa only [map_smul,smul_smul,inv_mul_cancel₀ ht.ne',one_smul,
    e.frame.map_coordinateVector,f.frame.map_coordinateVector] using hvectors

end
end PositiveEinsteinFour.Geometry
end


section

/-! Two short inverse branches cannot approach different initial vectors
at a common cut radius. The comparison is made in a fixed actual chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Matrix
open scoped Manifold ContDiff _root_.Topology BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [T3Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem moving_frame_chart_vector_continuousAt (g : SmoothMetric M) (c : M)
    (α : ℝ → FrameBundle g) (u : ℝ → FourSpace)
    (hα : ContinuousAt α 0) (hu : ContinuousAt u 0)
    (hc : (α 0).base ∈ (chartAt FourSpace c).source) :
    ContinuousAt (fun s => WithLp.toLp 2
      (frameChartMatrix g c (α s) *ᵥ WithLp.ofLp (u s))) 0 := by
  apply (PiLp.continuous_toLp 2 _).continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  change Tendsto (fun s => ∑ j, frameChartMatrix g c (α s) i j * (u s) j)
    (𝓝 0) (𝓝 (∑ j, frameChartMatrix g c (α 0) i j * (u 0) j))
  apply tendsto_finsetSum
  intro j _
  exact ((frameChartMatrix_continuousAt g c (α 0) hc i j).comp hα).mul
    ((continuous_apply j).continuousAt.comp ((PiLp.continuous_ofLp 2 _).continuousAt.comp hu))

theorem short_inverse_branches_limit (g : SmoothMetric M) (o : FrameOrientation g)
    (c : ℝ) (hcut : ∀ e ∈ o.positive, c ≤ actualCutTime g e)
    (e f : FrameBundle g) (hbase : e.base = f.base)
    (α β : ℝ → FrameBundle g) (u v : ℝ → FourSpace)
    (hα : ContinuousAt α 0) (hβ : ContinuousAt β 0)
    (hu : ContinuousAt u 0) (hv : ContinuousAt v 0)
    (hα0 : α 0 = e) (hβ0 : β 0 = f)
    (hshort : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      α s ∈ o.positive ∧ β s ∈ o.positive ∧ (α s).base = (β s).base ∧
      ‖u s‖ < c ∧ ‖v s‖ < c ∧
      frameExponential g o (α s) (u s) = frameExponential g o (β s) (v s)) :
    e.frame.map (u 0) = f.frame.map (v 0) := by
  have hec : (α 0).base ∈ (chartAt FourSpace e.base).source := by
    rw [hα0]; exact mem_chart_source FourSpace e.base
  have hfc : (β 0).base ∈ (chartAt FourSpace e.base).source := by
    rw [hβ0,← hbase]; exact mem_chart_source FourSpace e.base
  let A := fun s => WithLp.toLp 2 (frameChartMatrix g e.base (α s) *ᵥ WithLp.ofLp (u s))
  let B := fun s => WithLp.toLp 2 (frameChartMatrix g e.base (β s) *ᵥ WithLp.ofLp (v s))
  have hA := moving_frame_chart_vector_continuousAt g e.base α u hα hu hec
  have hB := moving_frame_chart_vector_continuousAt g e.base β v hβ hv hfc
  have hnearA : ∀ᶠ s in 𝓝 (0 : ℝ), (α s).base ∈ (chartAt FourSpace e.base).source :=
    (continuous_frameBase g).continuousAt.comp hα |>.preimage_mem_nhds
      ((chartAt FourSpace e.base).open_source.mem_nhds hec)
  have hnearB : ∀ᶠ s in 𝓝 (0 : ℝ), (β s).base ∈ (chartAt FourSpace e.base).source :=
    (continuous_frameBase g).continuousAt.comp hβ |>.preimage_mem_nhds
      ((chartAt FourSpace e.base).open_source.mem_nhds hfc)
  have heq : A =ᶠ[𝓝[>] (0 : ℝ)] B := by
    filter_upwards [hshort,hnearA.filter_mono nhdsWithin_le_nhds,
      hnearB.filter_mono nhdsWithin_le_nhds] with s hs hsa hsb
    have hvec := uniform_cut_initial_vector_unique g o c hcut (α s) (β s)
      hs.1 hs.2.1 hs.2.2.1 (u s) (v s) hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2
    dsimp [A,B]
    rw [frameChart_map g e.base _ hsa,frameChart_map g e.base _ hsb]
    have hOp : (chartForwardOperator e.base (α s).base : FourSpace →L[ℝ] FourSpace) =
        chartForwardOperator e.base (β s).base := congrArg
          (fun x => (chartForwardOperator e.base x : FourSpace →L[ℝ] FourSpace)) hs.2.2.1
    rw [hOp,hvec]
  have hzero : A 0 = B 0 := tendsto_nhds_unique
    (hA.tendsto.mono_left nhdsWithin_le_nhds)
    ((hB.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  dsimp [A,B] at hzero
  rw [frameChart_map g e.base _ hec,frameChart_map g e.base _ hfc,hα0,hβ0] at hzero
  have hOp : (chartForwardOperator e.base f.base : FourSpace →L[ℝ] FourSpace) =
      ContinuousLinearMap.id ℝ FourSpace := by
    rw [← hbase,chartForwardOperator_center]
  rw [hOp,chartForwardOperator_center] at hzero
  exact hzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! A short actual curve near a nonconjugate radial segment ends in the
corresponding short inverse branch. The proof uses compactness only on
a final subinterval and the actual cut-radius barrier. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem short_variation_log_norm_lt (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (htc : t < actualFirstConjugateTime g hRic e)
    (hcut : ∀ f ∈ o.positive, t ≤ actualCutTime g f)
    (U : Set (FrameBundle g × M)) (hU : IsOpen U)
    (heU : (e,frameGeodesic g 0 e t) ∈ U)
    (log : FrameBundle g × M → FourSpace) (hlog : ContinuousOn log U)
    (hlog0 : log (e,frameGeodesic g 0 e t) = t • coordinateVector 0)
    (hreal : ∀ p ∈ U, frameExponential g o p.1 (log p) = p.2)
    (a : ℝ) (ha : 0 ≤ a) (hat : a < t)
    (α : ℝ → FrameBundle g) (hα : ContinuousAt α 0) (hα0 : α 0 = e)
    (hαpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), α ε ∈ o.positive)
    (γ : ℝ → ℝ → M)
    (href : ∀ r ∈ Icc a t, γ 0 r = frameGeodesic g 0 e r)
    (hjoint : ∀ r ∈ Icc a t, ContinuousAt (fun p : ℝ × ℝ => γ p.1 p.2) (0,r))
    (hcont : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (γ ε) (Icc a t))
    (hshort : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc a t,
      metricDistance g (α ε).base (γ ε r) < t) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖log (α ε,γ ε t)‖ < t := by
  have hrad := joint_exponential_log_radial_eventually g o hRic e he t ht htc U hU heU
    log hlog hlog0 hreal
  have hcurve : Continuous (fun r => (e,frameGeodesic g 0 e r)) :=
    continuous_const.prodMk (frameGeodesic_contMDiff g 0 e).continuous
  have hmem : ∀ᶠ r in 𝓝 t, (e,frameGeodesic g 0 e r) ∈ U :=
    hcurve.continuousAt.preimage_mem_nhds (hU.mem_nhds heU)
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp (hmem.and hrad)
  let d := min (δ/2) ((t-a)/2)
  let b := t-d
  have hd : 0 < d := lt_min (half_pos hδ) (half_pos (sub_pos.mpr hat))
  have hb : a < b := by dsimp [b]; have := min_le_right (δ/2) ((t-a)/2); dsimp [d] at *; linarith
  have hbt : b < t := by dsimp [b]; linarith
  have hgood (r : ℝ) (hr : r ∈ Icc b t) :
      (e,frameGeodesic g 0 e r) ∈ U ∧ log (e,frameGeodesic g 0 e r) = r • coordinateVector 0 := by
    apply hδball
    rw [mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hr.2)]
    have hsmall := min_le_left (δ/2) ((t-a)/2)
    have hrleft : t-d ≤ r := hr.1
    dsimp [d] at *
    linarith [hrleft]
  have hba : Icc b t ⊆ Icc a t := Icc_subset_Icc hb.le le_rfl
  let H : ℝ × ℝ → FrameBundle g × M := fun p => (α p.1,γ p.1 p.2)
  have hH (r : ℝ) (hr : r ∈ Icc b t) : ContinuousAt H (0,r) :=
    (hα.comp (x := (0,r)) (f := Prod.fst) continuous_fst.continuousAt).prodMk (hjoint r (hba hr))
  have hH0 (r : ℝ) (hr : r ∈ Icc b t) : H (0,r) = (e,frameGeodesic g 0 e r) := by
    change (α 0,γ 0 r) = _
    rw [hα0,href r (hba hr)]
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ r ∈ Icc b t, H (ε,r) ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    exact (hH r hr).preimage_mem_nhds (hU.mem_nhds ((hH0 r hr).symm ▸ (hgood r hr).1))
  have hbmem : b ∈ Icc b t := ⟨le_rfl,hbt.le⟩
  have hbH : H (0,b) ∈ U := (hH0 b hbmem).symm ▸ (hgood b hbmem).1
  have hstart0 : ‖log (H (0,b))‖ < t := by
    rw [hH0 b hbmem,(hgood b hbmem).2,norm_smul,Real.norm_eq_abs,abs_of_pos (ha.trans_lt hb)]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit,mul_one]
    exact hbt
  have hstart : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖log (H (ε,b))‖ < t := by
    have hc := ((hlog.continuousAt (hU.mem_nhds hbH)).comp (hH b hbmem)).norm
    have hε : ContinuousAt (fun ε : ℝ => ‖log (H (ε,b))‖) 0 :=
      hc.comp (x := 0) (f := fun ε : ℝ => (ε,b)) (continuous_id.prodMk continuous_const).continuousAt
    exact hε.preimage_mem_nhds (isOpen_Iio.mem_nhds hstart0)
  filter_upwards [hαpos,hcont,hshort,hnear.filter_mono nhdsWithin_le_nhds,
    hstart.filter_mono nhdsWithin_le_nhds] with ε hpos hγε hdist hUε hstartε
  have hcomp : ContinuousOn (fun r => log (H (ε,r))) (Icc b t) := by
    have hp : ContinuousOn (fun r => (α ε,γ ε r)) (Icc b t) :=
      (continuousOn_const (c := α ε)).prodMk (hγε.mono hba)
    exact hlog.comp hp (fun r hr => hUε r hr)
  exact exponential_log_norm_lt_along_curve g o t hcut (α ε) hpos
    (fun r => log (H (ε,r))) (γ ε) hcomp hstartε
    (fun r hr => hreal _ (hUε r hr)) (fun r hr => hdist r (hba hr)) t ⟨hbt.le,le_rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual parallel normal shortening produces a short inverse-exponential
branch with the prescribed moving endpoints. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators
noncomputable section

theorem affinePartitionTime_strictMono {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    StrictMono (affinePartitionTime 0 b n) := by
  intro i j hij
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hijr : (i : ℝ) < j := by exact_mod_cast hij
  simp only [affinePartitionTime,sub_zero,zero_add]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hijr hb) hnr

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_parallel_short_branch (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e)
    (hcut : ∀ f ∈ o.positive, t ≤ actualCutTime g f)
    (a : Fin 3 → ℝ) (ha : a ≠ 0) :
    ∃ (α : ℝ → FrameBundle g) (u : ℝ → FourSpace),
      ContinuousAt α 0 ∧ ContinuousAt u 0 ∧ α 0 = e ∧ u 0 = t • coordinateVector 0 ∧
      (∀ ε, (α ε).base = normalQuadraticEndpointCurve g e a ε) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), α ε ∈ o.positive ∧ ‖u ε‖ < t ∧
        frameExponential g o (α ε) (u ε) =
          normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 t e) a ε := by
  obtain ⟨n,hn,C,hC⟩ := exists_finite_curve_chart_partition (frameGeodesic g 0 e)
    (frameGeodesic_contMDiff g 0 e).continuous 0 t ht
  let T := affinePartitionTime 0 t n
  have hT0 : T 0 = 0 := affinePartitionTime_zero 0 t n
  have hTn : T n = t := affinePartitionTime_last 0 t n hn
  have hTmono : StrictMono T := affinePartitionTime_strictMono ht hn
  have hT (i : ℕ) (_ : i < n) : T i < T (i+1) := hTmono (Nat.lt_succ_self i)
  obtain ⟨γ,href,hjoint,hshort⟩ := exists_finite_parallel_normal_shortening
    g hRic hpositive e n hn T C a ha hT hC
  obtain ⟨α,hα,hα0,hbase,hαpos⟩ := exists_moving_positive_frame g o e he
    (normalQuadraticEndpointCurve g e a)
    (normalQuadraticEndpointCurve_continuousAt g e a)
    (normalQuadraticEndpointCurve_zero g e a)
  obtain ⟨U,hU,heU,log,hlog,hlog0,hreal⟩ :=
    exists_joint_exponential_log g o hRic e he t ht htc
  let k := n-1
  have hk : k < n := Nat.sub_lt hn (by omega)
  have hkn : k+1=n := by dsimp [k]; omega
  have hTk : 0 ≤ T k := by rw [← hT0]; exact hTmono.monotone (Nat.zero_le k)
  have hTkt : T k < t := by rw [← hTn]; exact hTmono hk
  have hlastref (r : ℝ) (hr : r ∈ Icc (T k) t) : γ k 0 r = frameGeodesic g 0 e r := by
    apply href k hk
    simpa only [hkn,hTn] using hr
  have hlastjoint (r : ℝ) (hr : r ∈ Icc (T k) t) :
      ContinuousAt (fun p : ℝ × ℝ => γ k p.1 p.2) (0,r) := by
    apply hjoint k hk
    simpa only [hkn,hTn] using hr
  have hlast : ContinuousAt (fun ε : ℝ => γ k ε t) 0 :=
    (hlastjoint t ⟨hTkt.le,le_rfl⟩).comp (f := fun ε : ℝ => (ε,t))
      (continuous_id.prodMk continuous_const).continuousAt
  let H : ℝ → FrameBundle g × M := fun ε => (α ε,γ k ε t)
  have hH : ContinuousAt H 0 := hα.prodMk hlast
  have hH0 : H 0 = (e,frameGeodesic g 0 e t) := by
    dsimp [H]; rw [hα0,hlastref t ⟨hTkt.le,le_rfl⟩]
  have hHU : H 0 ∈ U := hH0.symm ▸ heU
  let u : ℝ → FourSpace := fun ε => log (H ε)
  have hu : ContinuousAt u 0 := (hlog.continuousAt (hU.mem_nhds hHU)).comp hH
  have hu0 : u 0 = t • coordinateVector 0 := by dsimp [u]; rw [hH0,hlog0]
  have hcont : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (γ k ε) (Icc (T k) t) := by
    filter_upwards [hshort] with ε hε
    simpa only [hkn,hTn] using (hε.1 k hk).continuousOn
  have hdist : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc (T k) t,
      metricDistance g (α ε).base (γ k ε r) < t := by
    filter_upwards [hshort] with ε hε r hr
    let p := fun i => normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 (T i) e) a ε
    have hleft (i : ℕ) (hi : i < n) : γ i ε (T i) = p i := (hε.2.1 i hi).1
    have hright (i : ℕ) (hi : i < n) : γ i ε (T (i+1)) = p (i+1) := (hε.2.1 i hi).2
    have hbound := finite_piece_metric_energy_point_bound g n p T (fun i => γ i ε)
      hT hε.1 hleft hright k hk r (by simpa only [hkn,hTn] using hr)
    have hp0 : p 0 = (α ε).base := by
      dsimp [p]; rw [hT0,parallelFrameFlowMap_zero]; exact (hbase ε).symm
    rw [hp0,hT0,hTn,sub_zero] at hbound
    have henergy := hε.2.2
    rw [hT0,hTn,sub_zero] at henergy
    linarith
  have hnorm := short_variation_log_norm_lt g o hRic e he t ht htc hcut U hU heU
    log hlog hlog0 hreal (T k) hTk hTkt α hα hα0
    (hαpos.filter_mono nhdsWithin_le_nhds) (γ k) hlastref hlastjoint hcont hdist
  refine ⟨α,u,hα,hu,hα0,hu0,hbase,?_⟩
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), H ε ∈ U := hH.preimage_mem_nhds (hU.mem_nhds hHU)
  filter_upwards [hnorm,hshort,hαpos.filter_mono nhdsWithin_le_nhds,
    hnear.filter_mono nhdsWithin_le_nhds] with ε hnε hε hpε hUε
  refine ⟨hpε,hnε,?_⟩
  change frameExponential g o (H ε).1 (log (H ε)) = _
  rw [hreal _ hUε]
  change γ k ε t = _
  have hh := (hε.2.1 k hk).2
  simpa only [hkn,hTn] using hh

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_PositiveDeterminantOrder
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Determinant monotonicity for the positive matrices in radial comparison. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped MatrixOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem one_le_det_one_add_posSemidef {P : Matrix ι ι ℝ} (hP : P.PosSemidef) :
    1 ≤ (1 + P).det := by
  let U := star hP.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hd : φ P = diagonal hP.isHermitian.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have he : φ (1 + P) = diagonal (fun i => 1 + hP.isHermitian.eigenvalues i) := by
    rw [map_add, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hdet : (φ (1 + P)).det = (1 + P).det := by
    have hu := congrArg Matrix.det (Unitary.coe_star_mul_self U)
    simp only [Matrix.det_mul, Matrix.det_one] at hu
    dsimp only [φ]
    rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
    calc
      _ = ((star U : Matrix ι ι ℝ).det * (U : Matrix ι ι ℝ).det) * (1 + P).det := by ring
      _ = _ := by rw [hu, one_mul]
  rw [← hdet, he, Matrix.det_diagonal]
  exact Finset.one_le_prod (fun i _ => by linarith [hP.eigenvalues_nonneg i])

theorem det_le_det_of_posDef_sub_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hBA : (B - A).PosSemidef) : A.det ≤ B.det := by
  let U := CFC.sqrt A⁻¹
  have hU : Uᴴ = U := (CFC.sqrt_nonneg A⁻¹).posSemidef.isHermitian.eq
  have hsq : U * U = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
  have hn : U * A * U = 1 := by
    apply mul_eq_one_comm.mp
    rw [← Matrix.mul_assoc, hsq,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)]
  have hp : (U * (B - A) * U).PosSemidef := by
    simpa only [hU] using hBA.conjTranspose_mul_mul_same U
  have he : U * B * U = 1 + U * (B - A) * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hn]
    abel
  have hd := one_le_det_one_add_posSemidef hp
  rw [← he, Matrix.det_mul, Matrix.det_mul] at hd
  have hn' := congrArg Matrix.det hn
  simp only [Matrix.det_mul, Matrix.det_one] at hn'
  calc
    A.det ≤ A.det * (U.det * B.det * U.det) := le_mul_of_one_le_right hA.det_pos.le hd
    _ = (U.det * A.det * U.det) * B.det := by ring
    _ = B.det := by rw [hn', one_mul]

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiKernelLowerCap
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise lower comparison with the scalar curvature cap three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem symmetricCurvatureKernel_cap_posSemidef {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3) :
    ((3 : ℝ) • scalarLift G - symmetricCurvatureKernel S R).PosSemidef := by
  have hc := blockDiagonal_posSemidef (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i)
    (fun i => three_sub_posSemidef (hR i).1 (hR i).2)
  have he : Matrix.blockDiagonal (fun i => (3 : ℝ) • (1 : NormalMatrix) - R i) =
      (3 : ℝ) • 1 - Matrix.blockDiagonal R := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal_apply, Matrix.one_apply]
    · simp [Matrix.blockDiagonal_apply, hij]
  rw [he] at hc
  have hp := hc.conjTranspose_mul_mul_same (scalarLift S)
  simpa only [scalarLift_conjTranspose S hSt, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← scalarLift_mul, hS,
    symmetricCurvatureKernel] using hp

theorem curvatureKernel_determinant_lower_cap {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (R : Fin N → NormalMatrix) (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3)
    (hscalar : (1 - (3 : ℝ) • G).PosDef) :
    (1 - (3 : ℝ) • G).det ^ 3 ≤ (1 - curvatureKernel G R).det := by
  have hp : ((1 - symmetricCurvatureKernel S R) - scalarLift (1 - (3 : ℝ) • G)).PosSemidef := by
    rw [scalarLift_sub_three]
    convert symmetricCurvatureKernel_cap_posSemidef S G hS hSt R hR using 1
    all_goals try with_reducible_and_instances rfl
    abel
  have h := det_le_det_of_posDef_sub_posSemidef (scalarLift_posDef hscalar) hp
  rwa [det_scalarLift, symmetricCurvatureKernel_det S G hS R] at h

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarGreenLimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar flat-kernel determinant converges to sin(theta)/theta. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
noncomputable section

theorem tendsto_of_cube_tendsto {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (h : Tendsto (fun x => f x ^ 3) l (nhds (a ^ 3))) : Tendsto f l (nhds a) := by
  have ho : Odd 3 := by decide
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [(tendsto_order.mp h).1 (b ^ 3) (ho.pow_lt_pow.mpr hb)] with x hx
    exact ho.pow_lt_pow.mp hx
  · intro b hb
    filter_upwards [(tendsto_order.mp h).2 (b ^ 3) (ho.pow_lt_pow.mpr hb)] with x hx
    exact ho.pow_lt_pow.mp hx

theorem scalarGreen_reference_factorization (t : ℝ) (N : ℕ) :
    1 - (3 : ℝ) • scaledFlatGreen t N =
      flatGreen N * referenceMatrix (Real.sqrt 3 * t) N := by
  have hf : flatGreen N * scalarDirichlet N 2 = 1 := by
    rw [flatGreen_eq_inverse]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (flatDirichlet_posDef N).isUnit)
  rw [referenceMatrix_sqrt_three, Matrix.mul_sub, hf, Matrix.mul_smul,
    Matrix.mul_one, scaledFlatGreen, smul_smul]

theorem scalarGreen_reference_det (t : ℝ) (N : ℕ) :
    (1 - (3 : ℝ) • scaledFlatGreen t N).det =
      (referenceMatrix (Real.sqrt 3 * t) N).det / ((N : ℝ) + 1) := by
  rw [scalarGreen_reference_factorization, Matrix.det_mul, flatGreen_eq_inverse,
    Matrix.det_nonsing_inv, flatDirichlet_det, Ring.inverse_eq_inv]
  ring

theorem scalarGreen_determinant_tendsto {t : ℝ} (ht : 0 < t)
    (htop : t < Real.pi / Real.sqrt 3) :
    Tendsto (fun N : ℕ => (1 - (3 : ℝ) • scaledFlatGreen t N).det) atTop
      (nhds (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t))) := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have hc : Tendsto (fun N : ℕ =>
      ((Real.sqrt 3 * t / (N + 1)) * (referenceMatrix (Real.sqrt 3 * t) N).det) ^ 3)
      atTop (nhds (Real.sin (Real.sqrt 3 * t) ^ 3)) := by
    simpa only [mul_pow] using reference_determinant_tendsto hθ hθπ
  have h := (tendsto_of_cube_tendsto hc).div_const (Real.sqrt 3 * t)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  rw [scalarGreen_reference_det]
  field_simp

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Dominated convergence for the actual averaged lower Jacobi comparison. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi Filter
open scoped Manifold ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] [SecondCountableTopology M] in
theorem actualFlatKernelDeterminant_tendsto (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    Tendsto (fun N => actualFlatKernelDeterminant g t N e) atTop
      (nhds (((actualJacobiSolution g hRic e).J t).det / t ^ 3)) := by
  have hR : ∀ s, ((actualRegularJacobi g hRic e t).R s).PosSemidef ∧
      ((actualRegularJacobi g hRic e t).R s).trace = 3 := by
    intro s
    rw [actualRegularJacobi_R]
    exact ⟨actual_jacobi_posSemidef hpositive _, actualJacobiCurvature_trace g hRic e s⟩
  simpa only [actualFlatKernelDeterminant, actualRegularJacobi_R, actualRegularJacobi_J] using
    (actualRegularJacobi g hRic e t).flat_kernel_determinant_tendsto ht htop hR

end
end PositiveEinsteinFour.Geometry
end


section

/-! No actual conjugate point occurs below pi/sqrt(3). -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix Filter
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_determinant_lower_cap (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t)) ^ 3 ≤
      ((actualJacobiSolution g hRic e).J t).det / t ^ 3 := by
  apply le_of_tendsto_of_tendsto ((scalarGreen_determinant_tendsto ht htop).pow 3)
    (actualFlatKernelDeterminant_tendsto g hRic hpositive e ht htop)
  filter_upwards [scaledFlatGreen_eventually_below_one ht.le htop] with N hN
  exact curvatureKernel_determinant_lower_cap _ _ (flatGreenRoot_square t N)
    (flatGreenRoot_transpose t N) _
    (fun i => ⟨actual_jacobi_posSemidef hpositive _, actualJacobiCurvature_trace g hRic e _⟩) hN

theorem actualJacobi_determinant_pos_below_sqrt_three (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    0 < ((actualJacobiSolution g hRic e).J t).det := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have hp := pow_pos (div_pos (Real.sin_pos_of_pos_of_lt_pi hθ hθπ) hθ) 3
  have hd := hp.trans_le (actualJacobi_determinant_lower_cap g hRic hpositive e ht htop)
  have h := (lt_div_iff₀ (pow_pos ht 3)).mp hd
  simpa only [zero_mul] using h

theorem actualJacobi_isUnit_below_sqrt_three (g : SmoothMetric M) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g)
    {t : ℝ} (ht : 0 < t) (htop : t < Real.pi / Real.sqrt 3) :
    IsUnit ((actualJacobiSolution g hRic e).J t) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
    (actualJacobi_determinant_pos_below_sqrt_three g hRic hpositive e ht htop).ne')

theorem actualFirstConjugateTime_lower_sqrt_three (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g) :
    Real.pi / Real.sqrt 3 ≤ actualFirstConjugateTime g hRic e := by
  by_contra hn
  exact actualFirstConjugateTime_singular g hRic e
    (actualJacobi_isUnit_below_sqrt_three g hRic hpositive e
      (actualFirstConjugateTime_pos g hRic e) (lt_of_not_ge hn))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A globally shortest cut point below the conjugate radius yields a
closed geodesic, with matching velocity at both joins. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameAntipode_vector (g : SmoothMetric M) (e : FrameBundle g) (i : Fin 4) :
    (frameAntipode g e).frame.vector i = -e.frame.vector i := by
  change (e.frame.rotate (orientedToOrthogonal reverseFrameRotation)).vector i = _
  rw [OrthonormalFrame.rotate_vector,reverseFrameRotation_matrix]
  simp [Matrix.one_apply]

variable [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [PreconnectedSpace M] in
theorem frameAntipode_flow_cancel (g : SmoothMetric M) (e : FrameBundle g) (t : ℝ) :
    parallelFrameFlowMap g 0 t (frameAntipode g (parallelFrameFlowMap g 0 t e)) =
      frameAntipode g e := by
  rw [← parallelFrameFlowMap_antipode,← parallelFrameFlowMap_add,neg_add_cancel,
    parallelFrameFlowMap_zero]

theorem minimal_cut_pair_initial_opposite (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) (ht : 0 < t)
    (hcut : ∀ e ∈ o.positive, t ≤ actualCutTime g e)
    (hconj : ∀ e ∈ o.positive, t < actualFirstConjugateTime g hRic e)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hbase : e.base = f.base) (hne : e.frame.vector 0 ≠ f.frame.vector 0)
    (hend : frameGeodesic g 0 e t = frameGeodesic g 0 f t) :
    e.frame.vector 0 = -f.frame.vector 0 := by
  have hterminal := minimal_cut_terminal_opposite g o hRic t ht hcut e f he hf
    hbase hne hend (hconj e he) (hconj f hf)
  let E := parallelFrameFlowMap g 0 t e
  let F := parallelFrameFlowMap g 0 t f
  let E' := frameAntipode g E
  let F' := frameAntipode g F
  have hE : E' ∈ o.positive := frameRotate_oriented_positive o E
    (parallelFrameFlowMap_positive g o e he t) _
  have hF : F' ∈ o.positive := frameRotate_oriented_positive o F
    (parallelFrameFlowMap_positive g o f hf t) _
  have hne' : E'.frame.vector 0 ≠ F'.frame.vector 0 := by
    intro h
    have hsame : E.frame.vector 0 = F.frame.vector 0 := by
      simpa only [E',F',frameAntipode_vector,neg_inj] using h
    have hz : E.frame.vector 0 = 0 := by
      have hh : E.frame.vector 0 = -F.frame.vector 0 := hterminal
      rw [← hsame] at hh
      ext i
      have hhi := congrArg (fun v : FourSpace => v i) hh
      change (E.frame.vector 0) i = -(E.frame.vector 0) i at hhi
      change (E.frame.vector 0) i = 0
      linarith
    have hu := E.frame.inner_vector_self 0
    rw [hz] at hu
    have hzinner : g.inner E.base (0 : FourSpace) 0 = 0 := (g.inner E.base 0).map_zero
    exact zero_ne_one (hzinner.symm.trans hu)
  have hends : frameGeodesic g 0 E' t = frameGeodesic g 0 F' t := by
    change (parallelFrameFlowMap g 0 t (frameAntipode g E)).base =
      (parallelFrameFlowMap g 0 t (frameAntipode g F)).base
    rw [frameAntipode_flow_cancel,frameAntipode_flow_cancel]
    exact hbase
  have hh := minimal_cut_terminal_opposite g o hRic t ht hcut E' F' hE hF
    hend hne' hends (hconj E' hE) (hconj F' hF)
  change (parallelFrameFlowMap g 0 t (frameAntipode g E)).frame.vector 0 =
    -(parallelFrameFlowMap g 0 t (frameAntipode g F)).frame.vector 0 at hh
  rw [frameAntipode_flow_cancel,frameAntipode_flow_cancel,frameAntipode_vector,
    frameAntipode_vector,neg_neg] at hh
  exact (neg_eq_iff_eq_neg.mp hh)

theorem exists_closed_geodesic_at_minimal_cut (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hcut : ∀ f ∈ o.positive, actualCutTime g e ≤ actualCutTime g f)
    (hconj : ∀ f ∈ o.positive,
      actualCutTime g e < actualFirstConjugateTime g hRic f) :
    unitTangentOfFrame (parallelFrameFlowMap g 0 (2 * actualCutTime g e) e) =
      unitTangentOfFrame e := by
  let t := actualCutTime g e
  have ht : 0 < t := actualCutTime_pos g o hRic e he
  obtain ⟨w,hw,hend,hwne⟩ := actualCutTime_second_minimizing_vector g o hRic e he (hconj e he)
  have hn : ‖w‖ = t := by
    rw [← hw,hend]
    exact (metricDistance_eq_iff g _ _ ht.le).mpr
      (show t ∈ frameMinimizingTimes g e from by
        rw [frameMinimizingTimes_eq_Icc]; exact ⟨ht.le,le_rfl⟩).2
  let p : Directions := ⟨t⁻¹ • w, by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),hn,inv_mul_cancel₀ ht.ne']⟩
  have hp : t • p.val = w := by
    change t • (t⁻¹ • w) = w
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix p))
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hpoint : frameGeodesic g 0 e t = frameGeodesic g 0 f t := by
    rw [← frameExponential_direction_ray g o e he p t,hp]
    exact hend.symm
  have hne : e.frame.vector 0 ≠ f.frame.vector 0 := by
    intro hh
    have hdir : p.val = coordinateVector 0 := by
      apply e.frame.map_injective
      change e.frame.vector 0 = (e.frame.turn p).vector 0 at hh
      rw [e.frame.turn_first] at hh
      rw [e.frame.map_coordinateVector]
      exact hh.symm
    apply hwne
    rw [← hp,hdir]
  have hi := minimal_cut_pair_initial_opposite g o hRic t ht hcut hconj e f he hf rfl hne hpoint
  have ho := minimal_cut_terminal_opposite g o hRic t ht hcut e f he hf rfl hne hpoint
    (hconj e he) (hconj f hf)
  let F := parallelFrameFlowMap g 0 t f
  have hjoin : unitTangentOfFrame (parallelFrameFlowMap g 0 t e) =
      unitTangentOfFrame (frameAntipode g F) := by
    apply unitTangent_ext (u := unitTangentOfFrame (parallelFrameFlowMap g 0 t e))
      (v := unitTangentOfFrame (frameAntipode g F)) hpoint
    change (parallelFrameFlowMap g 0 t e).frame.vector 0 = (frameAntipode g F).frame.vector 0
    rw [frameAntipode_vector]
    exact ho
  have hfpos : frameAntipode g F ∈ o.positive := frameRotate_oriented_positive o F
    (parallelFrameFlowMap_positive g o f hf t) _
  have hflow := unitTangentOfFrame_flow_eq g o _ _
    (parallelFrameFlowMap_positive g o e he t) hfpos hjoin t
  rw [← parallelFrameFlowMap_add,frameAntipode_flow_cancel] at hflow
  have hstart : unitTangentOfFrame (frameAntipode g f) = unitTangentOfFrame e := by
    apply unitTangent_ext (u := unitTangentOfFrame (frameAntipode g f))
      (v := unitTangentOfFrame e) rfl
    change (frameAntipode g f).frame.vector 0 = e.frame.vector 0
    rw [frameAntipode_vector]
    exact hi.symm
  simpa only [two_mul] using hflow.trans hstart

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual parallel transport around an oriented closed four-dimensional
geodesic fixes a nonzero normal vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [PreconnectedSpace M] in
theorem closed_geodesic_fixed_normal (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (T : ℝ)
    (hclosed : unitTangentOfFrame (parallelFrameFlowMap g 0 T e) = unitTangentOfFrame e) :
    ∃ a : Fin 3 → ℝ, a ≠ 0 ∧
      (parallelFrameFlowMap g 0 T e).frame.map (WithLp.toLp 2 (Fin.cons 0 a)) =
        e.frame.map (WithLp.toLp 2 (Fin.cons 0 a)) := by
  let E := parallelFrameFlowMap g 0 T e
  have hbase : e.base = E.base := (congrArg UnitTangentBundle.base hclosed).symm
  have hvec : E.frame.vector 0 = e.frame.vector 0 := congrArg UnitTangentBundle.vector hclosed
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o e E he
    (parallelFrameFlowMap_positive g o e he T) hbase
  have hfirst : ∀ i, Q.val i 0 = (1 : Mat4) i 0 := by
    have h := hvec
    rw [← hQ,← (e.rotate (orientedToOrthogonal Q)).frame.map_coordinateVector,
      frameRotate_map,← e.frame.map_coordinateVector] at h
    have hh := e.frame.map_injective h
    have hc (i : Fin 4) := congrArg (fun v : FourSpace => v i) hh
    intro i
    have hi := hc i
    change (Q.val *ᵥ WithLp.ofLp (coordinateVector 0)) i = (coordinateVector 0 : FourSpace) i at hi
    simpa [coordinateVector,Matrix.mulVec,dotProduct,Matrix.one_apply,eq_comm] using hi
  obtain ⟨a,ha,hfixed⟩ := oriented_four_fixed_normal Q hfirst
  refine ⟨a,ha,?_⟩
  change E.frame.map (WithLp.toLp 2 (Fin.cons 0 a)) =
    e.frame.map (WithLp.toLp 2 (Fin.cons 0 a))
  rw [← hQ,frameRotate_map]
  apply congrArg e.frame.map
  apply WithLp.ofLp_injective
  exact hfixed

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equal vectors transported along the same actual oriented geodesic
remain equal, even when represented in different parallel frames. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem parallelFrameFlow_vector_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hstate : unitTangentOfFrame e = unitTangentOfFrame f)
    (a b : FourSpace) (hab : e.frame.map a = f.frame.map b) (t : ℝ) :
    (parallelFrameFlowMap g 0 t e).frame.map a =
      (parallelFrameFlowMap g 0 t f).frame.map b := by
  have hbase : e.base = f.base := congrArg UnitTangentBundle.base hstate
  have hvec : e.frame.vector 0 = f.frame.vector 0 := congrArg UnitTangentBundle.vector hstate
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o e f he hf hbase
  have hfirst : ∀ i, Q.val i 0 = (1 : Mat4) i 0 := by
    have h := hvec.symm
    rw [← hQ,← (e.rotate (orientedToOrthogonal Q)).frame.map_coordinateVector,
      frameRotate_map,← e.frame.map_coordinateVector] at h
    have hh := e.frame.map_injective h
    intro i
    have hi := congrArg (fun v : FourSpace => v i) hh
    change (Q.val *ᵥ WithLp.ofLp (coordinateVector 0)) i = (coordinateVector 0 : FourSpace) i at hi
    simpa [coordinateVector,Matrix.mulVec,dotProduct,Matrix.one_apply,eq_comm] using hi
  have hc : a = orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property b := by
    apply e.frame.map_injective
    rw [← hQ,frameRotate_map] at hab
    exact hab
  have hflow : parallelFrameFlowMap g 0 t f =
      (parallelFrameFlowMap g 0 t e).rotate (orientedToOrthogonal Q) := by
    rw [← hQ]
    exact (parallelFrameFlowMap_rotate g 0 (orientedToOrthogonal Q) hfirst t e).symm
  rw [hflow,frameRotate_map,← hc]

omit [T3Space M] [CompactSpace M] in
theorem frameAntipode_map (g : SmoothMetric M) (e : FrameBundle g) (v : FourSpace) :
    (frameAntipode g e).frame.map v = -e.frame.map v := by
  rw [frameAntipode,frameRotate_map]
  have hv : orthogonalEuclideanIsometry (orientedToOrthogonal reverseFrameRotation).val
      (orientedToOrthogonal reverseFrameRotation).property v = -v := by
    apply WithLp.ofLp_injective
    change (orientedToOrthogonal reverseFrameRotation).val *ᵥ WithLp.ofLp v = WithLp.ofLp (-v)
    rw [reverseFrameRotation_matrix,Matrix.neg_mulVec,Matrix.one_mulVec]
    rfl
  rw [hv,map_neg]

theorem closed_geodesic_normal_midpoint (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (a : FourSpace)
    (hclosed : unitTangentOfFrame (parallelFrameFlowMap g 0 (2*t) e) = unitTangentOfFrame e)
    (hfixed : (parallelFrameFlowMap g 0 (2*t) e).frame.map a = e.frame.map a) :
    (parallelFrameFlowMap g 0 t (frameAntipode g e)).frame.map (-a) =
      (parallelFrameFlowMap g 0 t e).frame.map a := by
  have hh := parallelFrameFlow_vector_eq g o (parallelFrameFlowMap g 0 (2*t) e) e
    (parallelFrameFlowMap_positive g o e he (2*t)) he hclosed a a hfixed (-t)
  rw [← parallelFrameFlowMap_add,show -t + 2*t = t by ring] at hh
  rw [← parallelFrameFlowMap_antipode,frameAntipode_map,map_neg,neg_neg]
  exact hh.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A shortest nonconjugate cut loop contradicts the actual two-sided
parallel normal shortening in positive curvature. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [T3Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem normalCoordinates_neg (a : Fin 3 → ℝ) :
    (WithLp.toLp 2 (Fin.cons 0 (-a)) : FourSpace) =
      -(WithLp.toLp 2 (Fin.cons 0 a) : FourSpace) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [PreconnectedSpace M] in
theorem closed_geodesic_antipode_midpoint_base (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ)
    (hclosed : unitTangentOfFrame (parallelFrameFlowMap g 0 (2*t) e) = unitTangentOfFrame e) :
    (parallelFrameFlowMap g 0 t e).base =
      (parallelFrameFlowMap g 0 t (frameAntipode g e)).base := by
  have hh := unitTangentOfFrame_flow_eq g o (parallelFrameFlowMap g 0 (2*t) e) e
    (parallelFrameFlowMap_positive g o e he (2*t)) he hclosed (-t)
  rw [← parallelFrameFlowMap_add,show -t + 2*t = t by ring] at hh
  have hb := congrArg UnitTangentBundle.base hh
  rw [← parallelFrameFlowMap_antipode]
  exact hb

theorem closed_geodesic_impossible_below_uniform_cut (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (hcut : ∀ f ∈ o.positive, t ≤ actualCutTime g f)
    (hconj : ∀ f ∈ o.positive, t < actualFirstConjugateTime g hRic f)
    (hclosed : unitTangentOfFrame (parallelFrameFlowMap g 0 (2*t) e) = unitTangentOfFrame e) :
    False := by
  obtain ⟨a,ha,hfixed⟩ := closed_geodesic_fixed_normal g o e he (2*t) hclosed
  let f := frameAntipode g e
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he reverseFrameRotation
  have hstart : normalQuadraticEndpointCurve g e a = normalQuadraticEndpointCurve g f (-a) := by
    apply normalQuadraticEndpointCurve_eq g e f a (-a) rfl
    dsimp [f]
    rw [normalCoordinates_neg,frameAntipode_map,map_neg,neg_neg]
  have hend : normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 t e) a =
      normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 t f) (-a) := by
    apply normalQuadraticEndpointCurve_eq g _ _ a (-a)
      (closed_geodesic_antipode_midpoint_base g o e he t hclosed)
    rw [normalCoordinates_neg]
    exact (closed_geodesic_normal_midpoint g o e he t _ hclosed hfixed).symm
  obtain ⟨α,u,hα,hu,hα0,hu0,hαbase,hαshort⟩ :=
    exists_parallel_short_branch g o hRic hpositive e he t ht (hconj e he) hcut a ha
  obtain ⟨β,v,hβ,hv,hβ0,hv0,hβbase,hβshort⟩ :=
    exists_parallel_short_branch g o hRic hpositive f hf t ht (hconj f hf) hcut (-a)
      (neg_ne_zero.mpr ha)
  have hcommon : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      α s ∈ o.positive ∧ β s ∈ o.positive ∧ (α s).base = (β s).base ∧
      ‖u s‖ < t ∧ ‖v s‖ < t ∧
      frameExponential g o (α s) (u s) = frameExponential g o (β s) (v s) := by
    filter_upwards [hαshort,hβshort] with s hs ht'
    refine ⟨hs.1,ht'.1,?_,hs.2.1,ht'.2.1,?_⟩
    · rw [hαbase,hβbase,hstart]
    · rw [hs.2.2,ht'.2.2,hend]
  have hh := short_inverse_branches_limit g o t hcut e f rfl α β u v
    hα hβ hu hv hα0 hβ0 hcommon
  rw [hu0,hv0] at hh
  dsimp [f] at hh
  rw [frameAntipode_map,← map_neg] at hh
  have hz := e.frame.map_injective hh
  have hz0 := congrArg (fun w : FourSpace => w 0) hz
  simp [coordinateVector] at hz0
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global injectivity bound in the oriented positively curved
Ricci-normalized four-dimensional case. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualCutTime_lower_sqrt_three (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    Real.pi / Real.sqrt 3 ≤ actualCutTime g e := by
  let : Nonempty M := ⟨e.base⟩
  obtain ⟨f,hf,hpos,hmin⟩ := exists_minimal_actualCutTime g o hRic
  have hbound : Real.pi / Real.sqrt 3 ≤ actualCutTime g f := by
    by_contra hh
    have hlt := lt_of_not_ge hh
    have hconj (q : FrameBundle g) (_ : q ∈ o.positive) :
        actualCutTime g f < actualFirstConjugateTime g hRic q :=
      hlt.trans_le (actualFirstConjugateTime_lower_sqrt_three g hRic hpositive q)
    exact closed_geodesic_impossible_below_uniform_cut g o hRic hpositive f hf
      (actualCutTime g f) hpos hmin hconj
      (exists_closed_geodesic_at_minimal_cut g o hRic f hf hmin hconj)
  exact hbound.trans (hmin e he)

theorem actual_frameExponential_injOn_sqrt_three_oai (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g) (e : FrameBundle g) (he : e ∈ o.positive) :
    InjOn (frameExponential g o e) (ball 0 (Real.pi / Real.sqrt 3)) :=
  frameExponential_injOn_ball_of_cut_lower (Real.pi / Real.sqrt 3)
    (actualCutTime_lower_sqrt_three g o hRic hpositive) e he

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three_oai.{u_1}
