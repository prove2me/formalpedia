-- Prove2me | solution 2 for OAI.KervaireUnitaryExponential.exists_smooth_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:29:13.808883+00:00
-- url     : https://prove2.me/submissions/3c70a797-5c54-4be5-b477-bbb1d02e2761

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceDegree.lean:L173-L187
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireUnitaryExponential.exists_smooth_path. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Theorems.Thm_OAI_KervaireUnitaryExponential_exists_skew_log

-- ---- from OAI.GroupTheory.Kervaire.IncidenceDegree ----
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
open scoped ContDiff

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

end KervaireIncidenceCurrent

open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireUnitaryExponential
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.KervaireUnitaryExponential.instNormedAlgebraRat_oAI
/-- A smooth ambient path from the identity to any finite-spectrum unitary. -/
lemma exists_smooth_path (u : unitary A) (hfin : (spectrum ℂ (u : A)).Finite) :
    ∃ p : ℝ → A, ContDiff ℝ ∞ p ∧ p 0 = 1 ∧ p 1 = (u : A) ∧
      ∀ t, p t ∈ unitary A := by
  obtain ⟨a, ha, hua⟩ := exists_skew_log u hfin
  let p : ℝ → A := fun t ↦ exp (t • a)
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · exact (show AnalyticOnNhd ℝ (exp : A → A) Set.univ from
      fun x _ ↦ exp_analytic x).contDiff.comp (contDiff_id.smul contDiff_const)
  · simp [p]
  · simpa [p] using hua
  · intro t
    apply exp_mem_unitary_of_mem_skewAdjoint
    change star (t • a) = -(t • a)
    simp [ha]

end KervaireUnitaryExponential

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {J : Type*} [Fintype J] [DecidableEq J]

end KervaireIncidenceCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireUnitaryExponential
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
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
attribute [local instance] OAI.KervaireUnitaryExponential.instNormedAlgebraRat_oAI


theorem solution : type_of% @_root_.OAI.KervaireUnitaryExponential.exists_smooth_path := @_root_.OAI.KervaireUnitaryExponential.exists_smooth_path
