-- Prove2me | solution 2 for OAI.KervaireFlow.exists_flow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:49:14.168746+00:00
-- url     : https://prove2.me/submissions/480d43d5-cc1a-4019-bd46-222bc5409d40

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean:L131-L152
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireFlow.exists_flow. The node keeps its source
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

omit [Fintype Z] in
lemma divergence_single (b : D → Z) (d : D) (c : ℝ) :
    divergence b (Pi.single d c) = Pi.single (b d) c := by
  ext z
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single d]
  · simp [Pi.single_apply, eq_comm]
  · intro e _ he
    simp [he]
  · simp

omit [Fintype D] in
lemma edgeFlow_mem (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d) (d : D) :
    edgeFlow θ d ∈ antisymmetric θ := by
  intro e
  change (Pi.single d 1 : D → ℝ) (θ e) - (Pi.single (θ d) 1 : D → ℝ) (θ e) =
    -((Pi.single d 1 : D → ℝ) e - (Pi.single (θ d) 1 : D → ℝ) e)
  have he : θ e = d ↔ e = θ d := by
    constructor
    · intro h
      simpa only [hθ] using congrArg θ h
    · intro h
      rw [h,hθ]
  simp only [Pi.single_apply, he, Equiv.apply_eq_iff_eq, eq_comm]
  ring

omit [Fintype Z] in
lemma divergence_edgeFlow (b : D → Z) (θ : Equiv.Perm D) (d : D) :
    divergence b (edgeFlow θ d) = Pi.single (b d) 1 - Pi.single (b (θ d)) 1 := by
  rw [edgeFlow, map_sub, divergence_single, divergence_single]

omit [Fintype Z] in
lemma difference_mem_range (b : D → Z) (θ : Equiv.Perm D)
    (hθ : ∀ d, θ (θ d) = d) {x y : Z}
    (hxy : Relation.ReflTransGen (Adj b θ) x y) :
    Pi.single x 1 - Pi.single y 1 ∈
      LinearMap.range ((divergence b).comp (antisymmetric θ).subtype) := by
  induction hxy with
  | refl => simp
  | @tail y z hxy hyz ih =>
    obtain ⟨d,rfl,rfl⟩ := hyz
    have hd : Pi.single (b d) 1 - Pi.single (b (θ d)) 1 ∈
        LinearMap.range ((divergence b).comp (antisymmetric θ).subtype) := by
      refine ⟨⟨edgeFlow θ d, edgeFlow_mem θ hθ d⟩, ?_⟩
      exact divergence_edgeFlow b θ d
    convert (LinearMap.range ((divergence b).comp (antisymmetric θ).subtype)).add_mem ih hd using 1
    ext z
    simp only [Pi.sub_apply, Pi.add_apply]
    ring

/-- Any total-zero boundary phases are
realized by antisymmetric phases on the paired slots of a connected diagram. -/
theorem exists_flow (b : D → Z) (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hconn : ∀ x y, Relation.ReflTransGen (Adj b θ) x y)
    (root : Z) (η : Z → ℝ) (hη : ∑ z, η z = 0) :
    ∃ γ : D → ℝ, (∀ d, γ (θ d) = -γ d) ∧
      ∀ z, (∑ d, if b d = z then γ d else 0) = η z := by
  let R := LinearMap.range ((divergence b).comp (antisymmetric θ).subtype)
  have he : η = ∑ z, η z • (Pi.single z 1 - Pi.single root 1) := by
    ext y
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hη, zero_mul, sub_zero]
    simp [Pi.single_apply]
  have hm : η ∈ R := by
    rw [he]
    apply Submodule.sum_mem
    intro z _
    exact R.smul_mem _ (difference_mem_range b θ hθ (hconn z root))
  obtain ⟨γ,hγ⟩ := hm
  refine ⟨γ,γ.property,?_⟩
  intro z
  exact congrFun hγ z
end

variable {D Z : Type*}
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
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireFlow.exists_flow := @_root_.OAI.KervaireFlow.exists_flow
