-- Prove2me | solution 2 for OAI.KervaireUnitaryExponential.exists_skew_log
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:27:36.313996+00:00
-- url     : https://prove2.me/submissions/03812618-ace3-475b-ac63-0105a9fe87f4

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceDegree.lean:L154-L171
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireUnitaryExponential.exists_skew_log. The node keeps its source
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
/-- A finite-spectrum unitary has a skew logarithm, including the cut point -1. -/
lemma exists_skew_log (u : unitary A) (hfin : (spectrum ℂ (u : A)).Finite) :
    ∃ a : A, star a = -a ∧ exp a = (u : A) := by
  let f : ℂ → ℂ := fun z ↦ (z.arg : ℂ) * I
  have hf : ContinuousOn f (spectrum ℂ (u : A)) := hfin.continuousOn f
  have hnorm : IsStarNormal (u : A) := inferInstance
  refine ⟨cfc f (u : A), ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    apply cfc_congr
    intro z _
    simp [f, mul_neg]
  · rw [← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp' Complex.exp f (u : A)
      Complex.continuous_exp.continuousOn hf hnorm]
    conv_rhs => rw [← cfc_id' ℂ (u : A)]
    apply cfc_congr
    intro z hz
    have hn := spectrum.norm_eq_one_of_unitary u.property hz
    simpa only [f, hn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z

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


theorem solution : type_of% @_root_.OAI.KervaireUnitaryExponential.exists_skew_log := @_root_.OAI.KervaireUnitaryExponential.exists_skew_log
