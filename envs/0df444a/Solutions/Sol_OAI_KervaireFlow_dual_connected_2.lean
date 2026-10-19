-- Prove2me | solution 2 for OAI.KervaireFlow.dual_connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:50:46.273224+00:00
-- url     : https://prove2.me/submissions/0323f356-da37-44d8-8163-acd2d1fa6802

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean:L156-L175
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireFlow.dual_connected. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow

-- ---- from OAI.GroupTheory.Kervaire.BoundaryFlow ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireFlow

section
open scoped Classical
variable {D Z : Type*} [Fintype D] [Fintype Z]

end

variable {D Z : Type*}
/-- Changing the disk successor to the boundary successor does not change
connectivity of the dual graph. -/
lemma dual_connected (b : D → Z) (hb : Function.Surjective b)
    (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hcycle : ∀ d, b (σ (θ d)) = b d)
    (hconn : ∀ d e, Relation.ReflTransGen (fun d e => e = σ d ∨ e = θ d) d e) :
    ∀ x y, Relation.ReflTransGen (Adj b θ) x y := by
  intro x y
  obtain ⟨d,rfl⟩ := hb x
  obtain ⟨e,rfl⟩ := hb y
  have hnext : ∀ a, b (σ a) = b (θ a) := by
    intro a
    simpa only [hθ] using hcycle (θ a)
  induction hconn d e with
  | refl => exact .refl
  | @tail a c h ha ih =>
    apply Relation.ReflTransGen.tail ih
    rcases ha with rfl | rfl
    · exact ⟨a,rfl,(hnext a).symm⟩
    · exact ⟨a,rfl,rfl⟩
end KervaireFlow
namespace KervaireBoundary

section
open Matrix KervaireMatrix KervaireRegular KervaireSpectral KervaireMixing KervaireTraversal
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot
end
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular KervaireMixing KervaireTraversal
open scoped Classical
variable {I K Z A : Type*} [Fintype I] [Fintype K] [Fintype Z] [Group A]
  [Nonempty I] [Nonempty K]
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot_1
end KervaireBoundary

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireFlow
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
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix


theorem solution : type_of% @_root_.OAI.KervaireFlow.dual_connected := @_root_.OAI.KervaireFlow.dual_connected
