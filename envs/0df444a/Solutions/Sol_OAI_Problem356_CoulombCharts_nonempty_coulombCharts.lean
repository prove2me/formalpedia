-- Prove2me | solution 1 for OAI.Problem356.CoulombCharts.nonempty_coulombCharts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:08:17.760985+00:00
-- url     : https://prove2.me/submissions/5a94c091-2c98-49bf-8682-b0e9cbc42436

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombCharts.lean:L69-L84
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.CoulombCharts.nonempty_coulombCharts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Theorems.Thm_OAI_Problem356_CoulombCharts_centerStateHessian_axis_eq
import Theorems.Thm_OAI_Problem356_GeometryJets_contDiffAt_stationaryEquation_center
import Theorems.Thm_OAI_Problem356_GeometryJets_hasFDerivAt_stationary_center
import Theorems.Thm_OAI_Problem356_LocalImplicit_nonempty_analyticStationaryCharts

-- ---- from OAI.Analysis.CoulombTransport.AxisHessian ----
namespace OAI

/-! Explicit nondegeneracy algebra for the two local Coulomb branches.
The Hessian eigenvalues are 2 in the axial direction and -1 transversely.
A common regularization parameter K = 20 works in every direction. -/

noncomputable section

namespace Problem356.LocalHessian

open Matrix

lemma eigenvalue_cases (k i : Fin 3) :
    eigenvalue k i = 2 ∨ eigenvalue k i = -1 := by
  unfold eigenvalue
  split_ifs <;> simp

lemma scalar_quadratic_positive {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) (hxz : x ≠ 0 ∨ z ≠ 0) :
    0 < (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
      (20 + (9 / 8) * q) * z ^ 2 := by
  have hsum : 0 < x ^ 2 + z ^ 2 := by
    rcases hxz with hx | hz
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg z)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hz)
  rcases hq with rfl | rfl
  · nlinarith [sq_nonneg (x - z), sq_nonneg x, sq_nonneg z]
  · nlinarith [sq_nonneg (x + z), sq_nonneg x, sq_nonneg z]

lemma scalar_quadratic_nonnegative {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) :
    0 ≤ (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
      (20 + (9 / 8) * q) * z ^ 2 := by
  by_cases hx : x = 0
  · by_cases hz : z = 0
    · simp [hx, hz]
    · exact (scalar_quadratic_positive hq (Or.inr hz)).le
  · exact (scalar_quadratic_positive hq (Or.inl hx)).le

lemma centralDerivative_isUnit (k : Fin 3) : IsUnit (centralDerivative k) := by
  rw [centralDerivative, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> norm_num

lemma oppositeDerivative_isUnit (k : Fin 3) : IsUnit (oppositeDerivative k) := by
  rw [oppositeDerivative, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> norm_num

lemma regularizedHessian_quadratic (k : Fin 3) (v : Fin 3 ⊕ Fin 3 → ℝ) :
    star v ⬝ᵥ ((regularizedHessian k) *ᵥ v) =
      ∑ i : Fin 3, ((20 + 2 * eigenvalue k i) * v (Sum.inl i) ^ 2 -
        2 * eigenvalue k i * v (Sum.inl i) * v (Sum.inr i) +
        (20 + (9 / 8) * eigenvalue k i) * v (Sum.inr i) ^ 2) := by
  simp only [regularizedHessian, fromBlocks_mulVec, dotProduct,
    Fintype.sum_sum_type, Pi.star_apply, star_trivial, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, upperBlock, lowerBlock, mixedBlock,
    mulVec_diagonal, Function.comp_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma regularizedHessian_isHermitian (k : Fin 3) :
    (regularizedHessian k).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact Matrix.isHermitian_diagonal _
  · exact Matrix.isHermitian_diagonal _
  · exact Matrix.isHermitian_diagonal _

lemma regularizedHessian_posDef (k : Fin 3) :
    (regularizedHessian k).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (regularizedHessian_isHermitian k)
  intro v hv
  rw [regularizedHessian_quadratic]
  apply Finset.sum_pos'
  · intro i hi
    exact scalar_quadratic_nonnegative (eigenvalue_cases k i)
  · have hex : ∃ j, v j ≠ 0 := by
      contrapose! hv
      ext j
      exact hv j
    obtain ⟨j, hj⟩ := hex
    cases j with
    | inl i =>
      exact ⟨i, Finset.mem_univ _,
        scalar_quadratic_positive (eigenvalue_cases k i) (Or.inl hj)⟩
    | inr i =>
      exact ⟨i, Finset.mem_univ _,
        scalar_quadratic_positive (eigenvalue_cases k i) (Or.inr hj)⟩

lemma regularizedHessian_isUnit (k : Fin 3) : IsUnit (regularizedHessian k) :=
  (regularizedHessian_posDef k).isUnit

end Problem356.LocalHessian

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.HessianCLM ----
namespace OAI

universe uN

noncomputable section

namespace Problem356.LocalHessian

open Matrix
open scoped RealInnerProductSpace

/-- Invertible matrices induce invertible continuous linear maps in Euclidean coordinates. -/
lemma toEuclideanCLM_isInvertible {n : Type uN} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).IsInvertible := by
  obtain ⟨u, hu⟩ := hA.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).toMonoidHom
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

lemma stateOperator_isInvertible (k : Fin 3) : (stateOperator k).IsInvertible := by
  exact ContinuousLinearMap.IsInvertible.comp
    (ContinuousLinearMap.isInvertible_equiv (f := stateCoordinates))
    (ContinuousLinearMap.IsInvertible.comp
      (toEuclideanCLM_isInvertible _ (regularizedHessian_isUnit k))
      (ContinuousLinearMap.isInvertible_equiv (f := stateCoordinates.symm)))

lemma centralDerivativeCLM_isInvertible (k : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (centralDerivative k)).IsInvertible :=
  toEuclideanCLM_isInvertible _ (centralDerivative_isUnit k)

lemma oppositeDerivativeCLM_isInvertible (k : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (oppositeDerivative k)).IsInvertible :=
  toEuclideanCLM_isInvertible _ (oppositeDerivative_isUnit k)

lemma stateOperator_fst_apply (k : Fin 3) (v : StateSpace) (i : Fin 3) :
    (stateOperator k v).1 i =
      (20 + 2 * eigenvalue k i) * v.1 i - eigenvalue k i * v.2 i := by
  change ((regularizedHessian k) *ᵥ (WithLp.ofLp (stateCoordinates.symm v)))
    (Sum.inl i) = _
  rw [regularizedHessian, fromBlocks_mulVec]
  simp [upperBlock, mixedBlock, mulVec_diagonal, sub_eq_add_neg]

lemma stateOperator_snd_apply (k : Fin 3) (v : StateSpace) (i : Fin 3) :
    (stateOperator k v).2 i =
      -eigenvalue k i * v.1 i + (20 + (9 / 8) * eigenvalue k i) * v.2 i := by
  change ((regularizedHessian k) *ᵥ (WithLp.ofLp (stateCoordinates.symm v)))
    (Sum.inr i) = _
  rw [regularizedHessian, fromBlocks_mulVec]
  simp [lowerBlock, mixedBlock, mulVec_diagonal]

lemma stateOperator_comp_branchOperator (k : Fin 3) :
    stateOperator k ∘L branchOperator k = -parameterOperator k := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    simp only [ContinuousLinearMap.comp_apply, stateOperator_fst_apply,
      branchOperator_fst_apply, branchOperator_snd_apply,
      _root_.neg_apply, Prod.fst_neg, PiLp.neg_apply,
      parameterOperator_fst_apply]
    unfold eigenvalue
    split_ifs <;> ring
  · ext i
    simp only [ContinuousLinearMap.comp_apply, stateOperator_snd_apply,
      branchOperator_fst_apply, branchOperator_snd_apply,
      _root_.neg_apply, Prod.snd_neg, PiLp.neg_apply,
      parameterOperator_snd_apply]
    unfold eigenvalue
    split_ifs <;> ring

lemma neg_inverse_comp_parameterOperator (k : Fin 3) :
    -((stateOperator k).inverse ∘L parameterOperator k) = branchOperator k := by
  calc
    -((stateOperator k).inverse ∘L parameterOperator k) =
        (stateOperator k).inverse ∘L (-parameterOperator k) := by
          rw [ContinuousLinearMap.comp_neg]
    _ = (stateOperator k).inverse ∘L (stateOperator k ∘L branchOperator k) := by
          rw [stateOperator_comp_branchOperator]
    _ = branchOperator k := by
          rw [← ContinuousLinearMap.comp_assoc,
            (stateOperator_isInvertible k).inverse_comp_self, ContinuousLinearMap.id_comp]

lemma central_inverse_block_isInvertible (k : Fin 3) :
    ((ContinuousLinearMap.fst ℝ AxisSpace AxisSpace) ∘L
      (-((stateOperator k).inverse ∘L parameterOperator k))).IsInvertible := by
  rw [neg_inverse_comp_parameterOperator]
  exact centralDerivativeCLM_isInvertible k

lemma opposite_inverse_block_isInvertible (k : Fin 3) :
    ((ContinuousLinearMap.snd ℝ AxisSpace AxisSpace) ∘L
      (-((stateOperator k).inverse ∘L parameterOperator k))).IsInvertible := by
  rw [neg_inverse_comp_parameterOperator]
  exact oppositeDerivativeCLM_isInvertible k

end Problem356.LocalHessian

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CoulombCalculus ----
namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pairHessian_apply (x y : E) :
    pairHessian x y = -(‖x‖ ^ 3)⁻¹ • y +
      (3 * (‖x‖ ^ 5)⁻¹ * ⟪x, y⟫) • x := by
  simp [pairHessian, smul_smul]

lemma pairHessian_apply_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) (y : E) :
    pairHessian x y = -y + (3 * ⟪x, y⟫) • x := by
  simp [pairHessian_apply, hx]

end Problem356.CoulombCalculus

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.StationaryEquation ----
namespace OAI

universe uE

noncomputable section

namespace Problem356.GeometryJets

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stationaryEquation_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    stationaryEquation K a (a, (0, -a)) = 0 := by
  have hvec : a - -a = (2 : ℝ) • a := by module
  simp [stationaryEquation, pairGradient, hvec, norm_smul, ha]
  module

end Problem356.GeometryJets

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.HessianMatrix ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace
open Matrix

namespace Problem356.CoulombCalculus

/-- The analytic Coulomb Hessian at a coordinate axis is precisely the diagonal
matrix used in the finite-dimensional local nondegeneracy calculation. -/
theorem pairHessian_axisVector (k : Fin 3) :
    pairHessian (axisVector k) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  ext v i
  rw [pairHessian_apply_of_norm_eq_one (norm_axisVector k), inner_axisVector]
  change (-v + (3 * v k) • axisVector k) i =
    (LocalHessian.pairHessian k *ᵥ WithLp.ofLp v) i
  simp only [LocalHessian.pairHessian, Matrix.mulVec_diagonal]
  by_cases hi : i = k
  · subst i
    simp [LocalHessian.eigenvalue, axisVector]
    ring
  · simp [LocalHessian.eigenvalue, axisVector, hi]

end Problem356.CoulombCalculus

namespace Problem356.GeometryJets

open CoulombCalculus

end Problem356.GeometryJets

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CoulombCharts ----
namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem356.CoulombCharts

open CoulombCalculus GeometryJets LocalImplicit

/-- The computed parameter derivative agrees with the mixed Hessian block. -/
theorem centerParameterDerivative_axis_eq (k : Fin 3) :
    centerParameterDerivative (CoulombCalculus.pairHessian (axisVector k)) =
      LocalHessian.parameterOperator k := by
  rw [pairHessian_axisVector]
  unfold centerParameterDerivative LocalHessian.parameterOperator
  dsimp
  congr 1
  module

theorem stationary_state_partial_eq (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k)) ∘L
      ContinuousLinearMap.inr ℝ E3 (E3 × E3) = LocalHessian.stateOperator k := by
  rw [(hasFDerivAt_stationary_center 20 (axisVector k) (norm_axisVector k)).fderiv]
  have h : centerTotalDerivative 20 (CoulombCalculus.pairHessian (axisVector k)) ∘L
      ContinuousLinearMap.inr ℝ E3 (E3 × E3) =
      centerStateHessian 20 (CoulombCalculus.pairHessian (axisVector k)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [centerTotalDerivative]
  rw [h, centerStateHessian_axis_eq]

/-- Identification of the actual partial parameter derivative. -/
theorem stationary_parameter_partial_eq (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k)) ∘L
      ContinuousLinearMap.inl ℝ E3 (E3 × E3) = LocalHessian.parameterOperator k := by
  rw [(hasFDerivAt_stationary_center 20 (axisVector k) (norm_axisVector k)).fderiv]
  have h : centerTotalDerivative 20 (CoulombCalculus.pairHessian (axisVector k)) ∘L
      ContinuousLinearMap.inl ℝ E3 (E3 × E3) =
      centerParameterDerivative (CoulombCalculus.pairHessian (axisVector k)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [centerTotalDerivative]
  rw [h, centerParameterDerivative_axis_eq]

/-- Nonlinear local Coulomb branches exist at every coordinate-axis reference triple.
Both branch coordinates are analytic local diffeomorphisms on one common source. -/
theorem nonempty_coulombCharts (k : Fin 3) :
    Nonempty (AnalyticStationaryCharts
      (stationaryEquation 20 (axisVector k)) (axisVector k) (0, -axisVector k)) := by
  apply nonempty_analyticStationaryCharts
  · exact contDiffAt_stationaryEquation_center 20 (axisVector k) (norm_axisVector k)
  · exact stationaryEquation_center 20 (axisVector k) (norm_axisVector k)
  · rw [stationary_state_partial_eq]
    exact LocalHessian.stateOperator_isInvertible k
  · unfold implicitDerivative
    rw [stationary_state_partial_eq, stationary_parameter_partial_eq]
    exact LocalHessian.central_inverse_block_isInvertible k
  · unfold implicitDerivative
    rw [stationary_state_partial_eq, stationary_parameter_partial_eq]
    exact LocalHessian.opposite_inverse_block_isInvertible k

end Problem356.CoulombCharts

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.CoulombCharts
open scoped ContDiff
open CoulombCalculus GeometryJets LocalImplicit


theorem solution : type_of% @_root_.OAI.Problem356.CoulombCharts.nonempty_coulombCharts := @_root_.OAI.Problem356.CoulombCharts.nonempty_coulombCharts
