-- Prove2me | solution 1 for MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/dd886cc4-8d4d-5ffd-8e29-56ec81bdda15

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Constructions
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Regular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv

set_option autoImplicit false

namespace FLT
namespace SpectralSide

private scoped instance matrixMeasurableSpace {K : Type*} [MeasurableSpace K] :
    MeasurableSpace (Matrix (Fin 2) (Fin 2) K) :=
  inferInstanceAs (MeasurableSpace ((Fin 2) → (Fin 2) → K))

end FLT.SpectralSide
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide"
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT"

namespace FLT
namespace SpectralSide

open Set Filter Function MeasureTheory Matrix Topology
open scoped ENNReal NNReal BigOperators Classical

noncomputable section

section BorelBridge

private scoped instance matrixFin2BorelSpace {R : Type*} [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] [SecondCountableTopology R] :
    BorelSpace (Matrix (Fin 2) (Fin 2) R) :=
  inferInstanceAs (BorelSpace ((Fin 2) → (Fin 2) → R))

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]

private theorem gl2_isEmbedding_val :
    IsEmbedding (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K) := by
  refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
  · intro A hA
    have hdet : IsUnit (Matrix.det A) := (Matrix.isUnit_iff_isUnit_det A).mp hA
    have hdet0 : Matrix.det A ≠ 0 := hdet.ne_zero
    have hcont : ContinuousAt Ring.inverse (Matrix.det A) := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet0
    exact (continuousAt_matrix_inv A hcont).continuousWithinAt
  · intro u
    exact (Matrix.coe_units_inv u).symm

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

private scoped instance gl2CommittedBorelSpace : BorelSpace (GL (Fin 2) K) := by
  have hval : IsEmbedding (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K) :=
    gl2_isEmbedding_val
  have hmat : (matrixMeasurableSpace : MeasurableSpace (Matrix (Fin 2) (Fin 2) K))
      = borel (Matrix (Fin 2) (Fin 2) K) := BorelSpace.measurable_eq
  refine ⟨?_⟩

  have h1 : (Units.instMeasurableSpace : MeasurableSpace (GL (Fin 2) K))
      = MeasurableSpace.comap Units.val (borel (Matrix (Fin 2) (Fin 2) K)) := by
    rw [← hmat]
    rfl

  have h2 : MeasurableSpace.comap (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
        (borel (Matrix (Fin 2) (Fin 2) K))
      = @borel (GL (Fin 2) K)
          (TopologicalSpace.induced (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
            inferInstance) :=
    borel_comap.symm

  have h3 : (TopologicalSpace.induced (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
        (inferInstance : TopologicalSpace (Matrix (Fin 2) (Fin 2) K)))
      = (inferInstance : TopologicalSpace (GL (Fin 2) K)) :=
    hval.toIsInducing.eq_induced.symm
  calc (inferInstance : MeasurableSpace (GL (Fin 2) K))
      = MeasurableSpace.comap Units.val (borel (Matrix (Fin 2) (Fin 2) K)) := h1
    _ = @borel (GL (Fin 2) K)
          (TopologicalSpace.induced (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
            inferInstance) := h2
    _ = borel (GL (Fin 2) K) := by rw [h3]

end BorelBridge
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide"

end
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide"

end FLT.SpectralSide
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide"
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide"

namespace FLT
namespace PortProbe
namespace GL2Furniture

open Topology

private theorem continuousOn_matrixInv_isUnit' :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_ (Continuous.matrix_adjugate continuous_id).continuousOn
  exact (Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

private theorem isEmbedding_glVal' : IsEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv_isUnit' fun u => (Matrix.coe_units_inv u).symm

private theorem isOpen_range_glVal' : IsOpen (Set.range (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h : Set.range (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) =
      (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det) ⁻¹' {x | x ≠ 0} := by
    ext A
    constructor
    · rintro ⟨u, rfl⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
    · intro hA
      exact (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
  rw [h]
  exact isOpen_ne.preimage (Continuous.matrix_det continuous_id)

private theorem isOpenEmbedding_glVal' : IsOpenEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨isEmbedding_glVal', isOpen_range_glVal'⟩

private theorem locallyCompactSpace_gl' : LocallyCompactSpace (GL (Fin 2) ℝ) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact isOpenEmbedding_glVal'.locallyCompactSpace

private theorem secondCountableTopology_gl' : SecondCountableTopology (GL (Fin 2) ℝ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact isEmbedding_glVal'.secondCountableTopology

private scoped instance : LocallyCompactSpace (GL (Fin 2) ℝ) := locallyCompactSpace_gl'
private scoped instance : SecondCountableTopology (GL (Fin 2) ℝ) := secondCountableTopology_gl'

end FLT.PortProbe.GL2Furniture
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe.GL2Furniture"
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe"
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide"

open Set Function MeasureTheory Matrix Topology
open scoped ENNReal NNReal MatrixGroups

namespace FLT
namespace GL2RealDetSqLebesgueHaarModel

open FLT.SpectralSide

noncomputable section

private def gl2MatrixLebesgue : Measure (Matrix (Fin 2) (Fin 2) ℝ) :=
  (volume : Measure ((Fin 2) → (Fin 2) → ℝ))

private theorem gl2MatrixLebesgue_def :
    gl2MatrixLebesgue = (volume : Measure ((Fin 2) → (Fin 2) → ℝ)) := rfl

private scoped instance gl2PiVolume_isAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure ((Fin 2) → (Fin 2) → ℝ)) := by
  constructor

private scoped instance gl2MatrixLebesgue_isOpenPosMeasure : gl2MatrixLebesgue.IsOpenPosMeasure :=
  inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ((Fin 2) → (Fin 2) → ℝ)))

private scoped instance gl2MatrixLebesgue_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts gl2MatrixLebesgue :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ((Fin 2) → (Fin 2) → ℝ)))

private scoped instance gl2MatrixLebesgue_sigmaFinite : SigmaFinite gl2MatrixLebesgue :=
  inferInstanceAs (SigmaFinite (volume : Measure ((Fin 2) → (Fin 2) → ℝ)))

private theorem gl2_measurable_det : Measurable fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det :=
  continuous_id.matrix_det.measurable

private theorem gl2_val_det_ne_zero (g : GL (Fin 2) ℝ) :
    ((g : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

private theorem gl2_val_det_mul_inv_det (g : GL (Fin 2) ℝ) :
    ((g : Matrix (Fin 2) (Fin 2) ℝ)).det
      * (((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

private theorem gl2_isOpen_unitLocus : IsOpen {A : Matrix (Fin 2) (Fin 2) ℝ | IsUnit A} := by
  have h : {A : Matrix (Fin 2) (Fin 2) ℝ | IsUnit A}
      = (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det) ⁻¹' {x : ℝ | x ≠ 0} := by
    ext A
    simp [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [h]
  exact (isOpen_compl_iff.mpr isClosed_singleton).preimage continuous_id.matrix_det

private theorem gl2_range_val :
    Set.range (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
      = {A : Matrix (Fin 2) (Fin 2) ℝ | IsUnit A} := by
  ext A
  constructor
  · rintro ⟨u, rfl⟩
    exact u.isUnit
  · intro hA
    exact ⟨hA.unit, rfl⟩

private theorem gl2_measurableSet_range_val :
    MeasurableSet (Set.range (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [gl2_range_val]
  exact gl2_isOpen_unitLocus.measurableSet

private theorem gl2_measurableEmbedding_val :
    MeasurableEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  (gl2_isEmbedding_val (K := ℝ)).measurableEmbedding gl2_measurableSet_range_val

private theorem gl2_isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  { toIsEmbedding := gl2_isEmbedding_val (K := ℝ)
    isOpen_range := by rw [gl2_range_val]; exact gl2_isOpen_unitLocus }

private def gl2DetSqDensity (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (|A.det| ^ 2))⁻¹

private theorem gl2DetSqDensity_def (A : Matrix (Fin 2) (Fin 2) ℝ) :
    gl2DetSqDensity A = (ENNReal.ofReal (|A.det| ^ 2))⁻¹ := rfl

private theorem gl2_measurable_detSqDensity : Measurable gl2DetSqDensity := by
  have hcont : Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => |A.det| ^ 2 :=
    (continuous_id.matrix_det.abs).pow 2
  exact (ENNReal.measurable_ofReal.comp hcont.measurable).inv

private theorem gl2DetSqDensity_ne_zero (A : Matrix (Fin 2) (Fin 2) ℝ) :
    gl2DetSqDensity A ≠ 0 := by
  rw [gl2DetSqDensity_def]
  exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top

private theorem gl2DetSqDensity_one : gl2DetSqDensity (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  rw [gl2DetSqDensity_def]
  norm_num

private theorem gl2DetSqDensity_lt_top_of_isUnit {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsUnit A) :
    gl2DetSqDensity A < ∞ := by
  rw [gl2DetSqDensity_def]
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hA).ne_zero
  exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (by positivity))

private theorem gl2_detSq_factor_mul {a b : ℝ} (hab : a * b = 1) (x : ℝ) :
    (ENNReal.ofReal (|a| ^ 2))⁻¹ * (ENNReal.ofReal (|b| ^ 2 * |x| ^ 2))⁻¹
      = (ENNReal.ofReal (|x| ^ 2))⁻¹ := by
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  have habs : |a| * |b| = 1 := by rw [← abs_mul, hab, abs_one]
  have h1 : (ENNReal.ofReal (|a| ^ 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  rw [← ENNReal.mul_inv (Or.inl h1) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  calc |a| ^ 2 * (|b| ^ 2 * |x| ^ 2) = (|a| * |b|) ^ 2 * |x| ^ 2 := by ring
    _ = |x| ^ 2 := by rw [habs]; ring

private theorem gl2_detSq_factor_mul' {a b : ℝ} (hab : a * b = 1) (x : ℝ) :
    (ENNReal.ofReal (|a| ^ 2))⁻¹ * (ENNReal.ofReal (|x| ^ 2 * |b| ^ 2))⁻¹
      = (ENNReal.ofReal (|x| ^ 2))⁻¹ := by
  rw [mul_comm (|x| ^ 2) (|b| ^ 2)]
  exact gl2_detSq_factor_mul hab x

private def gl2TransposeLM : ((Fin 2) → (Fin 2) → ℝ) →ₗ[ℝ] ((Fin 2) → (Fin 2) → ℝ) where
  toFun A := fun i j => A j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem gl2TransposeLM_apply (A : Matrix (Fin 2) (Fin 2) ℝ) : gl2TransposeLM A = Aᵀ := rfl

private theorem gl2TransposeLM_comp_self : gl2TransposeLM.comp gl2TransposeLM = LinearMap.id := by
  apply LinearMap.ext
  intro A
  rfl

private theorem gl2TransposeLM_det_mul_self : gl2TransposeLM.det * gl2TransposeLM.det = 1 := by
  rw [← LinearMap.det_comp, gl2TransposeLM_comp_self, LinearMap.det_id]

private theorem gl2TransposeLM_abs_det : |gl2TransposeLM.det| = 1 := by
  rcases mul_self_eq_one_iff.mp gl2TransposeLM_det_mul_self with h | h <;> rw [h] <;> norm_num

private def gl2MulRightLM (T : Matrix (Fin 2) (Fin 2) ℝ) :
    ((Fin 2) → (Fin 2) → ℝ) →ₗ[ℝ] ((Fin 2) → (Fin 2) → ℝ) :=
  LinearMap.pi fun i : Fin 2 =>
    (Matrix.toLin' Tᵀ).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => (Fin 2) → ℝ) i)

private theorem gl2MulRightLM_def (T : Matrix (Fin 2) (Fin 2) ℝ) :
    gl2MulRightLM T = LinearMap.pi fun i : Fin 2 =>
      (Matrix.toLin' Tᵀ).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => (Fin 2) → ℝ) i) :=
  rfl

private theorem gl2MulRightLM_apply (T A : Matrix (Fin 2) (Fin 2) ℝ) : gl2MulRightLM T A = A * T := by
  funext i k
  simp [gl2MulRightLM, LinearMap.pi_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.transpose_apply, mul_comm]

private theorem gl2MulRightLM_det (T : Matrix (Fin 2) (Fin 2) ℝ) :
    (gl2MulRightLM T).det = T.det ^ 2 := by
  rw [gl2MulRightLM_def, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Finset.prod_const]

private def gl2MulLeftLM (T : Matrix (Fin 2) (Fin 2) ℝ) :
    ((Fin 2) → (Fin 2) → ℝ) →ₗ[ℝ] ((Fin 2) → (Fin 2) → ℝ) :=
  gl2TransposeLM.comp ((gl2MulRightLM Tᵀ).comp gl2TransposeLM)

private theorem gl2MulLeftLM_def (T : Matrix (Fin 2) (Fin 2) ℝ) :
    gl2MulLeftLM T = gl2TransposeLM.comp ((gl2MulRightLM Tᵀ).comp gl2TransposeLM) := rfl

private theorem gl2MulLeftLM_apply (T A : Matrix (Fin 2) (Fin 2) ℝ) : gl2MulLeftLM T A = T * A := by
  have h1 : gl2MulLeftLM T A = gl2TransposeLM (gl2MulRightLM Tᵀ (gl2TransposeLM A)) := rfl
  rw [h1, gl2TransposeLM_apply A]
  rw [gl2MulRightLM_apply Tᵀ Aᵀ]
  rw [gl2TransposeLM_apply (Aᵀ * Tᵀ)]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]

private theorem gl2MulLeftLM_det (T : Matrix (Fin 2) (Fin 2) ℝ) :
    (gl2MulLeftLM T).det = T.det ^ 2 := by
  rw [gl2MulLeftLM_def, LinearMap.det_comp, LinearMap.det_comp, gl2MulRightLM_det,
    Matrix.det_transpose]
  calc gl2TransposeLM.det * (T.det ^ 2 * gl2TransposeLM.det)
      = (gl2TransposeLM.det * gl2TransposeLM.det) * T.det ^ 2 := by ring
    _ = 1 * T.det ^ 2 := by rw [gl2TransposeLM_det_mul_self]
    _ = T.det ^ 2 := one_mul _

private theorem gl2_jacobian_scalar_eq {T : Matrix (Fin 2) (Fin 2) ℝ} (hT : T.det ≠ 0) :
    ENNReal.ofReal |(T.det ^ 2)⁻¹| = (ENNReal.ofReal (|T.det| ^ 2))⁻¹ := by
  rw [abs_inv, abs_pow, ENNReal.ofReal_inv_of_pos (pow_pos (abs_pos.mpr hT) 2)]

private theorem gl2MatrixLebesgue_map_mul_right {T : Matrix (Fin 2) (Fin 2) ℝ} (hT : T.det ≠ 0) :
    gl2MatrixLebesgue.map (fun A : Matrix (Fin 2) (Fin 2) ℝ => A * T)
      = (ENNReal.ofReal (|T.det| ^ 2))⁻¹ • gl2MatrixLebesgue := by
  have hdet : (gl2MulRightLM T).det ≠ 0 := by
    rw [gl2MulRightLM_det]; exact pow_ne_zero 2 hT
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure ((Fin 2) → (Fin 2) → ℝ)) hdet
  rw [gl2MulRightLM_det] at h
  rw [gl2_jacobian_scalar_eq hT] at h
  have hcoe : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A * T) = ⇑(gl2MulRightLM T) := by
    funext A
    rw [gl2MulRightLM_apply]
  rw [gl2MatrixLebesgue_def, hcoe]
  exact h

private theorem gl2MatrixLebesgue_map_mul_left {T : Matrix (Fin 2) (Fin 2) ℝ} (hT : T.det ≠ 0) :
    gl2MatrixLebesgue.map (fun A : Matrix (Fin 2) (Fin 2) ℝ => T * A)
      = (ENNReal.ofReal (|T.det| ^ 2))⁻¹ • gl2MatrixLebesgue := by
  have hdet : (gl2MulLeftLM T).det ≠ 0 := by
    rw [gl2MulLeftLM_det]; exact pow_ne_zero 2 hT
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure ((Fin 2) → (Fin 2) → ℝ)) hdet
  rw [gl2MulLeftLM_det] at h
  rw [gl2_jacobian_scalar_eq hT] at h
  have hcoe : (fun A : Matrix (Fin 2) (Fin 2) ℝ => T * A) = ⇑(gl2MulLeftLM T) := by
    funext A
    rw [gl2MulLeftLM_apply]
  rw [gl2MatrixLebesgue_def, hcoe]
  exact h

private def gl2DetSqMatrixMeasure : Measure (Matrix (Fin 2) (Fin 2) ℝ) :=
  gl2MatrixLebesgue.withDensity gl2DetSqDensity

private theorem gl2DetSqMatrixMeasure_def :
    gl2DetSqMatrixMeasure = gl2MatrixLebesgue.withDensity gl2DetSqDensity := rfl

private theorem gl2DetSqMatrixMeasure_apply {s : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    (hs : MeasurableSet s) :
    gl2DetSqMatrixMeasure s = ∫⁻ A in s, gl2DetSqDensity A ∂gl2MatrixLebesgue :=
  withDensity_apply _ hs

private theorem gl2_map_withDensity_comp {φ : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hφ : Measurable φ) {g : Matrix (Fin 2) (Fin 2) ℝ → ℝ≥0∞} (hg : Measurable g) :
    (gl2MatrixLebesgue.withDensity (g ∘ φ)).map φ = (gl2MatrixLebesgue.map φ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hφ]
  rfl

private theorem gl2DetSqMatrixMeasure_map_eq
    {φ ψ : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ) (hinv : ∀ A, ψ (φ A) = A)
    {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hmap : gl2MatrixLebesgue.map φ = c • gl2MatrixLebesgue)
    (hpt : ∀ B, c * gl2DetSqDensity (ψ B) = gl2DetSqDensity B) :
    gl2DetSqMatrixMeasure.map φ = gl2DetSqMatrixMeasure := by
  have hδψ : Measurable (gl2DetSqDensity ∘ ψ) := gl2_measurable_detSqDensity.comp hψ
  have hcomp : gl2DetSqDensity = (gl2DetSqDensity ∘ ψ) ∘ φ := by
    funext A
    simp only [Function.comp_apply, hinv]
  calc gl2DetSqMatrixMeasure.map φ
      = (gl2MatrixLebesgue.withDensity ((gl2DetSqDensity ∘ ψ) ∘ φ)).map φ := by
        rw [gl2DetSqMatrixMeasure_def, ← hcomp]
    _ = (gl2MatrixLebesgue.map φ).withDensity (gl2DetSqDensity ∘ ψ) :=
        gl2_map_withDensity_comp hφ hδψ
    _ = (c • gl2MatrixLebesgue).withDensity (gl2DetSqDensity ∘ ψ) := by rw [hmap]
    _ = c • gl2MatrixLebesgue.withDensity (gl2DetSqDensity ∘ ψ) :=
        withDensity_smul_measure c _
    _ = gl2MatrixLebesgue.withDensity (c • (gl2DetSqDensity ∘ ψ)) :=
        (withDensity_smul' c _ hc).symm
    _ = gl2MatrixLebesgue.withDensity gl2DetSqDensity := by
        congr 1
        funext B
        simpa using hpt B
    _ = gl2DetSqMatrixMeasure := rfl

private theorem gl2_jacobian_const_ne_top (g : GL (Fin 2) ℝ) :
    ((ENNReal.ofReal (|((g : Matrix (Fin 2) (Fin 2) ℝ)).det| ^ 2))⁻¹ : ℝ≥0∞) ≠ ∞ := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := gl2_val_det_ne_zero g
  exact (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (by positivity))).ne

private theorem gl2DetSqMatrixMeasure_map_mul_left (g : GL (Fin 2) ℝ) :
    gl2DetSqMatrixMeasure.map
        (fun A : Matrix (Fin 2) (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) * A)
      = gl2DetSqMatrixMeasure := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := gl2_val_det_ne_zero g
  have hφ : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (g : Matrix (Fin 2) (Fin 2) ℝ) * A) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hψ : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * A) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hinv : ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * ((g : Matrix (Fin 2) (Fin 2) ℝ) * A) = A := fun A => by
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hpt : ∀ B : Matrix (Fin 2) (Fin 2) ℝ,
      ((ENNReal.ofReal (|((g : Matrix (Fin 2) (Fin 2) ℝ)).det| ^ 2))⁻¹ : ℝ≥0∞)
        * gl2DetSqDensity (((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * B)
        = gl2DetSqDensity B := fun B => by
    rw [gl2DetSqDensity_def, gl2DetSqDensity_def, Matrix.det_mul, abs_mul, mul_pow]
    exact gl2_detSq_factor_mul (gl2_val_det_mul_inv_det g) B.det
  exact gl2DetSqMatrixMeasure_map_eq hφ hψ hinv (gl2_jacobian_const_ne_top g)
    (gl2MatrixLebesgue_map_mul_left hdet) hpt

private theorem gl2DetSqMatrixMeasure_map_mul_right (g : GL (Fin 2) ℝ) :
    gl2DetSqMatrixMeasure.map
        (fun A : Matrix (Fin 2) (Fin 2) ℝ => A * (g : Matrix (Fin 2) (Fin 2) ℝ))
      = gl2DetSqMatrixMeasure := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := gl2_val_det_ne_zero g
  have hφ : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      A * (g : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hψ : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      A * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hinv : ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      (A * (g : Matrix (Fin 2) (Fin 2) ℝ))
        * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A := fun A => by
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hpt : ∀ B : Matrix (Fin 2) (Fin 2) ℝ,
      ((ENNReal.ofReal (|((g : Matrix (Fin 2) (Fin 2) ℝ)).det| ^ 2))⁻¹ : ℝ≥0∞)
        * gl2DetSqDensity (B * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
        = gl2DetSqDensity B := fun B => by
    rw [gl2DetSqDensity_def, gl2DetSqDensity_def, Matrix.det_mul, abs_mul, mul_pow]
    exact gl2_detSq_factor_mul' (gl2_val_det_mul_inv_det g) B.det
  exact gl2DetSqMatrixMeasure_map_eq hφ hψ hinv (gl2_jacobian_const_ne_top g)
    (gl2MatrixLebesgue_map_mul_right hdet) hpt

private def gl2DetSqHaarModel : Measure (GL (Fin 2) ℝ) :=
  gl2DetSqMatrixMeasure.comap Units.val

private theorem gl2DetSqHaarModel_def :
    gl2DetSqHaarModel = gl2DetSqMatrixMeasure.comap Units.val := rfl

private theorem gl2DetSqHaarModel_apply {s : Set (GL (Fin 2) ℝ)} (hs : MeasurableSet s) :
    gl2DetSqHaarModel s = gl2DetSqMatrixMeasure (Units.val '' s) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ ht => gl2_measurableEmbedding_val.measurableSet_image.mpr ht) _ hs

private theorem gl2_val_image_preimage_mul_left (g : GL (Fin 2) ℝ) (s : Set (GL (Fin 2) ℝ)) :
    (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' ((fun x => g * x) ⁻¹' s)
      = (fun A : Matrix (Fin 2) (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) * A) ⁻¹'
          (Units.val '' s) := by
  ext A
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨g * h, hh, by rw [Units.val_mul]⟩
  · rintro ⟨k, hk, hval⟩
    refine ⟨g⁻¹ * k, ?_, ?_⟩
    · show g * (g⁻¹ * k) ∈ s
      rwa [← mul_assoc, mul_inv_cancel, one_mul]
    · show ((g⁻¹ * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A
      rw [Units.val_mul, hval, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mul]

private theorem gl2_val_image_preimage_mul_right (g : GL (Fin 2) ℝ) (s : Set (GL (Fin 2) ℝ)) :
    (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' ((fun x => x * g) ⁻¹' s)
      = (fun A : Matrix (Fin 2) (Fin 2) ℝ => A * (g : Matrix (Fin 2) (Fin 2) ℝ)) ⁻¹'
          (Units.val '' s) := by
  ext A
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, hh, by rw [Units.val_mul]⟩
  · rintro ⟨k, hk, hval⟩
    refine ⟨k * g⁻¹, ?_, ?_⟩
    · show (k * g⁻¹) * g ∈ s
      rwa [mul_assoc, inv_mul_cancel, mul_one]
    · show ((k * g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A
      rw [Units.val_mul, hval, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]

private theorem gl2DetSqHaarModel_map_mul_left (g : GL (Fin 2) ℝ) :
    gl2DetSqHaarModel.map (fun x => g * x) = gl2DetSqHaarModel := by
  ext s hs
  have hsval : MeasurableSet (Units.val '' s) :=
    gl2_measurableEmbedding_val.measurableSet_image.mpr hs
  have hmeasM : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (g : Matrix (Fin 2) (Fin 2) ℝ) * A) :=
    (continuous_const.matrix_mul continuous_id).measurable
  rw [Measure.map_apply (measurable_const_mul g) hs,
    gl2DetSqHaarModel_apply ((measurable_const_mul g) hs), gl2DetSqHaarModel_apply hs,
    gl2_val_image_preimage_mul_left g s,
    ← Measure.map_apply hmeasM hsval,
    gl2DetSqMatrixMeasure_map_mul_left g]

private theorem gl2DetSqHaarModel_map_mul_right (g : GL (Fin 2) ℝ) :
    gl2DetSqHaarModel.map (fun x => x * g) = gl2DetSqHaarModel := by
  ext s hs
  have hsval : MeasurableSet (Units.val '' s) :=
    gl2_measurableEmbedding_val.measurableSet_image.mpr hs
  have hmeasM : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      A * (g : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  rw [Measure.map_apply (measurable_mul_const g) hs,
    gl2DetSqHaarModel_apply ((measurable_mul_const g) hs), gl2DetSqHaarModel_apply hs,
    gl2_val_image_preimage_mul_right g s,
    ← Measure.map_apply hmeasM hsval,
    gl2DetSqMatrixMeasure_map_mul_right g]

private scoped instance gl2DetSqHaarModel_isMulLeftInvariant :
    gl2DetSqHaarModel.IsMulLeftInvariant :=
  ⟨gl2DetSqHaarModel_map_mul_left⟩

private scoped instance gl2DetSqHaarModel_isMulRightInvariant :
    gl2DetSqHaarModel.IsMulRightInvariant :=
  ⟨gl2DetSqHaarModel_map_mul_right⟩

private theorem gl2DetSqMatrixMeasure_pos_of_isOpen {V : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    (hV : IsOpen V) (hne : V.Nonempty) : 0 < gl2DetSqMatrixMeasure V := by
  rw [pos_iff_ne_zero]
  intro h0
  rw [gl2DetSqMatrixMeasure_apply hV.measurableSet] at h0
  have hae : ∀ᵐ A ∂gl2MatrixLebesgue, A ∈ V → gl2DetSqDensity A = 0 :=
    (setLIntegral_eq_zero_iff hV.measurableSet gl2_measurable_detSqDensity).mp h0
  have hVzero : gl2MatrixLebesgue V = 0 := by
    have h2 : {A : Matrix (Fin 2) (Fin 2) ℝ | ¬ (A ∈ V → gl2DetSqDensity A = 0)} = V := by
      ext A
      simp [gl2DetSqDensity_ne_zero A]
    have h3 := ae_iff.mp hae
    rwa [h2] at h3
  exact absurd hVzero (hV.measure_pos gl2MatrixLebesgue hne).ne'

private theorem gl2DetSqHaarModel_pos_of_isOpen {U : Set (GL (Fin 2) ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < gl2DetSqHaarModel U := by
  rw [gl2DetSqHaarModel_apply hU.measurableSet]
  exact gl2DetSqMatrixMeasure_pos_of_isOpen (gl2_isOpenEmbedding_val.isOpenMap U hU)
    (hne.image _)

private scoped instance gl2DetSqHaarModel_isOpenPosMeasure : gl2DetSqHaarModel.IsOpenPosMeasure :=
  ⟨fun _ hU hne => (gl2DetSqHaarModel_pos_of_isOpen hU hne).ne'⟩

private theorem gl2DetSqMatrixMeasure_lt_top_of_isCompact {K : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    (hK : IsCompact K) (hKunit : ∀ A ∈ K, IsUnit A) : gl2DetSqMatrixMeasure K < ∞ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · rw [gl2DetSqMatrixMeasure_def]
    simp
  obtain ⟨A₀, hA₀K, hA₀min⟩ := hK.exists_isMinOn hne
    ((continuous_abs.comp continuous_id.matrix_det).continuousOn)
  have hA₀det : A₀.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (hKunit A₀ hA₀K)).ne_zero
  have hε : (0 : ℝ) < |A₀.det| := abs_pos.mpr hA₀det
  have hbound : ∀ A ∈ K, gl2DetSqDensity A ≤ (ENNReal.ofReal (|A₀.det| ^ 2))⁻¹ := by
    intro A hA
    rw [gl2DetSqDensity_def]
    refine ENNReal.inv_le_inv' (ENNReal.ofReal_le_ofReal ?_)
    have h1 : |A₀.det| ≤ |A.det| := hA₀min hA
    gcongr
  calc gl2DetSqMatrixMeasure K
      = ∫⁻ A in K, gl2DetSqDensity A ∂gl2MatrixLebesgue :=
        gl2DetSqMatrixMeasure_apply hK.measurableSet
    _ ≤ ∫⁻ _ in K, (ENNReal.ofReal (|A₀.det| ^ 2))⁻¹ ∂gl2MatrixLebesgue :=
        setLIntegral_mono measurable_const hbound
    _ = (ENNReal.ofReal (|A₀.det| ^ 2))⁻¹ * gl2MatrixLebesgue K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (by positivity)))
        hK.measure_lt_top

private theorem gl2DetSqHaarModel_lt_top_of_isCompact {K : Set (GL (Fin 2) ℝ)} (hK : IsCompact K) :
    gl2DetSqHaarModel K < ∞ := by
  have hKM : IsCompact ((Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' K) :=
    hK.image Units.continuous_val
  have hKunit : ∀ A ∈ (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' K, IsUnit A := by
    rintro A ⟨u, _, rfl⟩
    exact u.isUnit
  rw [gl2DetSqHaarModel_apply hK.isClosed.measurableSet]
  exact gl2DetSqMatrixMeasure_lt_top_of_isCompact hKM hKunit

private scoped instance gl2DetSqHaarModel_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts gl2DetSqHaarModel :=
  ⟨fun _ hK => gl2DetSqHaarModel_lt_top_of_isCompact hK⟩

private theorem gl2DetSqHaarModel_isHaarMeasure : gl2DetSqHaarModel.IsHaarMeasure := by
  constructor

private scoped instance gl2DetSqHaarModel_isHaarMeasure' : gl2DetSqHaarModel.IsHaarMeasure :=
  gl2DetSqHaarModel_isHaarMeasure

private theorem gl2DetSqHaarModel_ne_zero : gl2DetSqHaarModel ≠ 0 := by
  intro h
  have hpos : 0 < gl2DetSqHaarModel (Set.univ : Set (GL (Fin 2) ℝ)) :=
    gl2DetSqHaarModel_pos_of_isOpen isOpen_univ ⟨1, trivial⟩
  rw [h] at hpos
  simp at hpos

private def gl2DetSqWindow : Set (GL (Fin 2) ℝ) :=
  (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) ⁻¹'
    {A : Matrix (Fin 2) (Fin 2) ℝ |
      ∀ i j, |A i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < (8 : ℝ)⁻¹}

private theorem gl2_isOpen_matrixBox :
    IsOpen {A : Matrix (Fin 2) (Fin 2) ℝ |
      ∀ i j, |A i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < (8 : ℝ)⁻¹} := by
  have h : {A : Matrix (Fin 2) (Fin 2) ℝ |
        ∀ i j, |A i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < (8 : ℝ)⁻¹}
      = ⋂ i, ⋂ j, {A : Matrix (Fin 2) (Fin 2) ℝ |
          |A i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < (8 : ℝ)⁻¹} := by
    ext A
    simp [Set.mem_iInter]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have hcont : Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      |A i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := by
    have hentry : Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j :=
      ((continuous_apply j).comp (continuous_apply i))
    exact (hentry.sub continuous_const).abs
  exact isOpen_lt hcont continuous_const

private theorem gl2_isOpen_detSqWindow : IsOpen gl2DetSqWindow :=
  gl2_isOpen_matrixBox.preimage Units.continuous_val

private theorem gl2_one_mem_detSqWindow : (1 : GL (Fin 2) ℝ) ∈ gl2DetSqWindow := by
  intro i j
  rw [Units.val_one]
  norm_num

private theorem gate_gl2DetSqHaarModel_window_pos : 0 < gl2DetSqHaarModel gl2DetSqWindow :=
  gl2DetSqHaarModel_pos_of_isOpen gl2_isOpen_detSqWindow ⟨1, gl2_one_mem_detSqWindow⟩

private def gl2MatrixClosedBox : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {A : Matrix (Fin 2) (Fin 2) ℝ |
    ∀ i j, |A i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ (8 : ℝ)⁻¹}

private theorem gl2_matrixClosedBox_eq_pi :
    gl2MatrixClosedBox = Set.pi Set.univ (fun i : Fin 2 => Set.pi Set.univ (fun j : Fin 2 =>
      Set.Icc ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j - (8 : ℝ)⁻¹)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j + (8 : ℝ)⁻¹))) := by
  ext A
  constructor
  · intro h i _ j _
    have h2 := abs_le.mp (h i j)
    exact Set.mem_Icc.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · intro h i j
    have h2 := Set.mem_Icc.mp (h i (Set.mem_univ i) j (Set.mem_univ j))
    exact abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩

private theorem gl2_isCompact_matrixClosedBox : IsCompact gl2MatrixClosedBox := by
  rw [gl2_matrixClosedBox_eq_pi]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc

private theorem gl2_det_ge_of_mem_matrixClosedBox {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ gl2MatrixClosedBox) : (3 : ℝ) / 4 ≤ A.det := by
  have h00 := hA 0 0
  have h01 := hA 0 1
  have h10 := hA 1 0
  have h11 := hA 1 1
  rw [Matrix.one_apply_eq] at h00 h11
  rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), sub_zero] at h01
  rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h10
  have h00' := abs_le.mp h00
  have h11' := abs_le.mp h11
  have hA00 : (7 : ℝ) / 8 ≤ A 0 0 := by linarith [h00'.1]
  have hA11 : (7 : ℝ) / 8 ≤ A 1 1 := by linarith [h11'.1]
  have h1 : (7 : ℝ) / 8 * (7 / 8) ≤ A 0 0 * A 1 1 :=
    mul_le_mul hA00 hA11 (by norm_num) (le_trans (by norm_num) hA00)
  have h2 : A 0 1 * A 1 0 ≤ (8 : ℝ)⁻¹ * (8 : ℝ)⁻¹ := by
    calc A 0 1 * A 1 0 ≤ |A 0 1 * A 1 0| := le_abs_self _
      _ = |A 0 1| * |A 1 0| := abs_mul _ _
      _ ≤ (8 : ℝ)⁻¹ * (8 : ℝ)⁻¹ := mul_le_mul h01 h10 (abs_nonneg _) (by norm_num)
  rw [Matrix.det_fin_two]
  nlinarith [h1, h2]

private theorem gl2_matrixClosedBox_subset_unitLocus :
    gl2MatrixClosedBox ⊆ {A : Matrix (Fin 2) (Fin 2) ℝ | IsUnit A} := by
  intro A hA
  have hdet : (3 : ℝ) / 4 ≤ A.det := gl2_det_ge_of_mem_matrixClosedBox hA
  have hne : A.det ≠ 0 := by linarith
  exact (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hne)

private theorem gl2DetSqDensity_le_of_mem_matrixClosedBox {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ gl2MatrixClosedBox) :
    gl2DetSqDensity A ≤ (ENNReal.ofReal (((3 : ℝ) / 4) ^ 2))⁻¹ := by
  have h2 : (3 : ℝ) / 4 ≤ |A.det| :=
    le_trans (gl2_det_ge_of_mem_matrixClosedBox hA) (le_abs_self _)
  rw [gl2DetSqDensity_def]
  refine ENNReal.inv_le_inv' (ENNReal.ofReal_le_ofReal ?_)
  gcongr

private def gl2DetSqClosedWindow : Set (GL (Fin 2) ℝ) :=
  (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) ⁻¹' gl2MatrixClosedBox

private theorem gl2_isCompact_detSqClosedWindow : IsCompact gl2DetSqClosedWindow := by
  have hsub : gl2MatrixClosedBox
      ⊆ Set.range (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [gl2_range_val]
    exact gl2_matrixClosedBox_subset_unitLocus
  have himg : (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' gl2DetSqClosedWindow
      = gl2MatrixClosedBox := Set.image_preimage_eq_of_subset hsub
  rw [(gl2_isEmbedding_val (K := ℝ)).isCompact_iff, himg]
  exact gl2_isCompact_matrixClosedBox

private theorem gl2_one_mem_detSqClosedWindow : (1 : GL (Fin 2) ℝ) ∈ gl2DetSqClosedWindow := by
  intro i j
  rw [Units.val_one, sub_self, abs_zero]
  norm_num

private theorem gl2DetSqWindow_subset_closedWindow : gl2DetSqWindow ⊆ gl2DetSqClosedWindow := by
  intro x hx i j
  exact le_of_lt (hx i j)

private theorem gate_gl2DetSqHaarModel_closedWindow_pos_finite :
    0 < gl2DetSqHaarModel gl2DetSqClosedWindow ∧
      gl2DetSqHaarModel gl2DetSqClosedWindow < ∞ := by
  constructor
  · exact lt_of_lt_of_le gate_gl2DetSqHaarModel_window_pos
      (measure_mono gl2DetSqWindow_subset_closedWindow)
  · exact gl2DetSqHaarModel_lt_top_of_isCompact gl2_isCompact_detSqClosedWindow

private def gl2GateDiag : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![2, 1]

private theorem gl2GateDiag_det : gl2GateDiag.det = 2 := by
  rw [gl2GateDiag, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

private theorem gate_gl2DetSqDensity_ne_at_diag :
    gl2DetSqDensity gl2GateDiag ≠ gl2DetSqDensity 1 := by
  rw [gl2DetSqDensity_one, gl2DetSqDensity_def, gl2GateDiag_det]
  intro h
  rw [show |(2 : ℝ)| ^ 2 = 4 by norm_num, ENNReal.inv_eq_one] at h
  have h2 := ENNReal.ofReal_eq_one.mp h
  norm_num at h2

private theorem gate_gl2_jacobian_scalar_ne_one :
    ((ENNReal.ofReal (|(2 : ℝ)| ^ 2))⁻¹ : ℝ≥0∞) ≠ 1 := by
  intro h
  rw [show |(2 : ℝ)| ^ 2 = 4 by norm_num, ENNReal.inv_eq_one] at h
  have h2 := ENNReal.ofReal_eq_one.mp h
  norm_num at h2

private theorem gate_gl2DetSqHaarModel_univ_pos :
    0 < gl2DetSqHaarModel (Set.univ : Set (GL (Fin 2) ℝ)) :=
  gl2DetSqHaarModel_pos_of_isOpen isOpen_univ ⟨1, trivial⟩

private theorem gate_gl2DetSqWindow_nonempty : gl2DetSqWindow.Nonempty :=
  ⟨1, gl2_one_mem_detSqWindow⟩

private theorem gate_gl2DetSqClosedWindow_nonempty : gl2DetSqClosedWindow.Nonempty :=
  ⟨1, gl2_one_mem_detSqClosedWindow⟩

private abbrev glCommittedMeasurableSpace : MeasurableSpace (GL (Fin 2) ℝ) := Units.instMeasurableSpace

private theorem glCommittedMeasurableSpace_eq_borel :
    glCommittedMeasurableSpace = borel (GL (Fin 2) ℝ) :=
  BorelSpace.measurable_eq

private theorem gl2DetSqHaarModel_eq_map_entryModel :
    gl2DetSqHaarModel = Measure.map
        (fun A : Fin 2 → Fin 2 → ℝ =>
          if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℝ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal (((Matrix.of A).det ^ 2)⁻¹)) := by
  have hof : Measurable (fun A : Fin 2 → Fin 2 → ℝ => (Matrix.of A : Matrix (Fin 2) (Fin 2) ℝ)) :=
    fun _ h => h
  have hdetm : Measurable fun A : Fin 2 → Fin 2 → ℝ => (Matrix.of A).det := gl2_measurable_det.comp hof
  have hS : MeasurableSet {A : Fin 2 → Fin 2 → ℝ | (Matrix.of A).det ≠ 0} :=
    hdetm (measurableSet_singleton (0 : ℝ)).compl
  have hφ : Measurable (fun A : Fin 2 → Fin 2 → ℝ =>
      if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
      else 1) := by
    rw [← gl2_measurableEmbedding_val.measurable_comp_iff]
    have h : (Units.val ∘ fun A : Fin 2 → Fin 2 → ℝ =>
        if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
        else 1) = fun A => if (Matrix.of A).det ≠ 0 then Matrix.of A else 1 := by
      funext A
      simp only [Function.comp_apply]
      split_ifs with h <;> rfl
    rw [h]
    exact Measurable.ite hS hof measurable_const
  ext s hs
  have himg : MeasurableSet ((Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' s) :=
    gl2_measurableEmbedding_val.measurableSet_image.mpr hs
  rw [gl2DetSqHaarModel_apply hs, gl2DetSqMatrixMeasure_apply himg, Measure.map_apply hφ hs,
    withDensity_apply _ (hφ hs), Measure.restrict_restrict (hφ hs)]
  have hset : (fun A : Fin 2 → Fin 2 → ℝ => (Matrix.of A : Matrix (Fin 2) (Fin 2) ℝ)) ⁻¹'
      ((Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' s) =
      (fun A : Fin 2 → Fin 2 → ℝ =>
        if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
        else 1) ⁻¹' s ∩ {A : Fin 2 → Fin 2 → ℝ | (Matrix.of A).det ≠ 0} := by
    ext A
    constructor
    · rintro ⟨g, hg, hgA⟩
      have hgA' : (g : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of A := hgA
      have hdet : (Matrix.of A).det ≠ 0 := by
        rw [← hgA']
        exact gl2_val_det_ne_zero g
      refine ⟨?_, hdet⟩
      show (if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
        else 1) ∈ s
      rw [dif_pos hdet, show Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) hdet = g from
        Units.ext hgA'.symm]
      exact hg
    · rintro ⟨hA, hdet⟩
      have hdet' : (Matrix.of A).det ≠ 0 := hdet
      refine ⟨(if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
        else 1), hA, ?_⟩
      rw [dif_pos hdet']
      rfl
  change ∫⁻ A in (fun A : Fin 2 → Fin 2 → ℝ => (Matrix.of A : Matrix (Fin 2) (Fin 2) ℝ)) ⁻¹'
      ((Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' s),
      gl2DetSqDensity (Matrix.of A) ∂(volume : Measure (Fin 2 → Fin 2 → ℝ)) = _
  rw [hset]
  refine setLIntegral_congr_fun ((hφ hs).inter hS) fun A hA => ?_
  have hdet : (Matrix.of A).det ≠ 0 := hA.2
  simp only [gl2DetSqDensity_def]
  rw [sq_abs, ENNReal.ofReal_inv_of_pos (sq_pos_iff.mpr hdet)]

private theorem exists_pos_smul_map_entryModel (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧
      μ = c • Measure.map
        (fun A : Fin 2 → Fin 2 → ℝ =>
          if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℝ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal (((Matrix.of A).det ^ 2)⁻¹)) := by
  rw [← gl2DetSqHaarModel_eq_map_entryModel]
  exact ⟨μ.haarScalarFactor gl2DetSqHaarModel, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul _ _⟩

end
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe.GL2Furniture"

end FLT.GL2RealDetSqLebesgueHaarModel
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe.GL2Furniture P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.GL2RealDetSqLebesgueHaarModel"
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.SpectralSide P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.FLT.PortProbe.GL2Furniture"

open MeasureTheory

theorem solution
    [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
    (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧
      μ = c • Measure.map
        (fun A : Fin 2 → Fin 2 → ℝ =>
          if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℝ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal (((Matrix.of A).det ^ 2)⁻¹)) := by
  have h : ‹MeasurableSpace (GL (Fin 2) ℝ)› = FLT.GL2RealDetSqLebesgueHaarModel.glCommittedMeasurableSpace :=
    BorelSpace.measurable_eq.trans FLT.GL2RealDetSqLebesgueHaarModel.glCommittedMeasurableSpace_eq_borel.symm
  subst h
  exact FLT.GL2RealDetSqLebesgueHaarModel.exists_pos_smul_map_entryModel μ

end S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
end P2MW
export P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv (solution)
