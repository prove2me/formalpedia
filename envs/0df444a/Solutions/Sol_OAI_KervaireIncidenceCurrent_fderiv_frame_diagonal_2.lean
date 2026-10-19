-- Prove2me | solution 2 for OAI.KervaireIncidenceCurrent.fderiv_frame_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:15:00.931977+00:00
-- url     : https://prove2.me/submissions/4d677c14-88c3-42fb-8166-489f7ca43a73

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean:L113-L131
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireIncidenceCurrent.fderiv_frame_diagonal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Theorems.Thm_OAI_KervaireIncidenceCurrent_fderiv_incidence

-- ---- from OAI.GroupTheory.Kervaire.IncidenceSpaces ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma diag_sub (A C : Mat K) (B D : Mat R) : diag A B - diag C D = diag (A-C) (B-D) := by
  ext i j
  cases i <;> cases j <;> simp [diag, fromBlocks]

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

/-- A diagonal change of the frame is absorbed by a fiber-unitary direction. -/
lemma frame_diagonal_commutator (T : unitary (Mat R)) (U : Mat K) (V : Mat R) :
    diag U V * diag 1 (star (T : Mat R)) - diag 1 (star (T : Mat R)) * diag U V =
      in22 (V * star (T : Mat R) - star (T : Mat R) * V) := by
  rw [diag_mul, diag_mul, diag_sub]
  simp only [mul_one, one_mul, sub_self, diag, in22]
  rfl

lemma compensated_star_mul (T : unitary (Mat R)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    star ((T : Mat R) * (compensated T V : Mat R)) =
      (V : Mat R) * star (T : Mat R) - star (T : Mat R) * V := by
  change star ((T : Mat R) * (star (T : Mat R) * (V : Mat R) * T - V)) = _
  rw [mul_sub, ← mul_assoc, ← mul_assoc, (Unitary.mem_iff.mp T.property).2, one_mul,
    star_sub, star_mul, star_mul, V.property]
  noncomm_ring

end KervaireIncidenceCurrent

open scoped ComplexOrder
namespace KervaireSkewTrace
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
local notation "S" => skewAdjoint.submodule ℝ M

end KervaireSkewTrace
namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

variable {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

end KervaireIncidenceCurrent

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.IncidenceTangent ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
/-- Diagonal frame directions and compensated fiber directions have identical images. -/
lemma fderiv_frame_diagonal {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (X : Mat K) (Q : Mat (K ⊕ R)) (T : unitary (Mat R))
    (U : skewAdjoint.submodule ℝ (Mat K)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    fderiv ℝ (incidence f) (t,X,Q,(T : Mat R)) (0,0,Q*diag U V,0) =
    fderiv ℝ (incidence f) (t,X,Q,(T : Mat R)) (0,0,0,(T : Mat R)*compensated T V) := by
  have hU : star (U : Mat K) = -(U : Mat K) := U.property
  have hV : star (V : Mat R) = -(V : Mat R) := V.property
  rw [fderiv_incidence hf, fderiv_incidence hf]
  simp only [show ((0 : ℝ),(0 : Mat K)) = 0 from rfl, _root_.map_zero, zero_mul,
    mul_zero, star_zero, zero_add, add_zero]
  rw [compensated_star_mul, star_mul, diag_star, hU, hV]
  have h := frame_diagonal_commutator T (U : Mat K) (V : Mat R)
  have hn : diag (-(U : Mat K)) (-(V : Mat R)) = -diag U V := by
    ext i j
    cases i <;> cases j <;> simp [diag, fromBlocks]
  rw [hn]
  rw [← h]
  noncomm_ring

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

end KervaireIncidenceCurrent

namespace KervaireFixedSpace
open Matrix
variable {K R : Type*}
end KervaireFixedSpace
namespace KervaireIncidenceCurrent
open MeasureTheory
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireIncidenceCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireIncidenceCurrent
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder


theorem solution : type_of% @_root_.OAI.KervaireIncidenceCurrent.fderiv_frame_diagonal := @_root_.OAI.KervaireIncidenceCurrent.fderiv_frame_diagonal
