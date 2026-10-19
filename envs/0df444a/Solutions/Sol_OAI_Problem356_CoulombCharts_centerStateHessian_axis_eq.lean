-- Prove2me | solution 1 for OAI.Problem356.CoulombCharts.centerStateHessian_axis_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:05:36.581684+00:00
-- url     : https://prove2.me/submissions/6e094e97-75dd-4097-8a38-bf971259f5da

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombCharts.lean:L15-L30
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.CoulombCharts.centerStateHessian_axis_eq. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.HessianCLM ----
namespace OAI

universe uN

noncomputable section

namespace Problem356.LocalHessian

open Matrix
open scoped RealInnerProductSpace

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

theorem pairHessian_axisVector_apply (k : Fin 3) (v : EuclideanSpace ℝ (Fin 3))
    (i : Fin 3) :
    pairHessian (axisVector k) v i = LocalHessian.eigenvalue k i * v i := by
  rw [pairHessian_axisVector]
  change (LocalHessian.pairHessian k *ᵥ WithLp.ofLp v) i = _
  simp [LocalHessian.pairHessian, Matrix.mulVec_diagonal]

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

/-- The computed state derivative is the coercive, invertible operator certified
by the finite-dimensional algebra, in the actual product-space coordinates. -/
theorem centerStateHessian_axis_eq (k : Fin 3) :
    centerStateHessian 20 (CoulombCalculus.pairHessian (axisVector k)) =
      LocalHessian.stateOperator k := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    simp [centerStateHessian, LocalHessian.stateOperator_fst_apply,
      pairHessian_axisVector_apply]
    ring
  · ext i
    simp [centerStateHessian, LocalHessian.stateOperator_snd_apply,
      pairHessian_axisVector_apply]
    ring

end Problem356.CoulombCharts

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.CoulombCharts
open scoped ContDiff
open CoulombCalculus GeometryJets LocalImplicit


theorem solution : type_of% @_root_.OAI.Problem356.CoulombCharts.centerStateHessian_axis_eq := @_root_.OAI.Problem356.CoulombCharts.centerStateHessian_axis_eq
