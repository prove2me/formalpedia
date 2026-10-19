-- Prove2me | solution 2 for OAI.KervaireTraversal.offDiagonal_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:40:55.632975+00:00
-- url     : https://prove2.me/submissions/4ac1e525-f41b-426f-b7f4-78f80e4a28bd

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Traversal.lean:L137-L161
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraversal.offDiagonal_representation. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.Traversal ----
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

namespace KervaireTraversal

section
open Matrix KervaireFixed KervaireSignPairing
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K]
end

section
open Matrix KervaireFixed
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Every unitary selfadjoint exchange has a unitary off-diagonal block. -/
lemma offDiagonal_representation (N : Matrix (E ⊕ E) (E ⊕ E) ℂ)
    (hNs : star N = N) (hNu : N ∈ unitary (Matrix (E ⊕ E) (E ⊕ E) ℂ))
    (h₀ : ∀ i j, N (.inl i) (.inl j) = 0)
    (h₁ : ∀ i j, N (.inr i) (.inr j) = 0) :
    ∃ P : unitary (Matrix E E ℂ), N = fromBlocks 0 (star (P : Matrix E E ℂ)) P 0 := by
  let P : Matrix E E ℂ := fun i j ↦ N (.inr i) (.inl j)
  have he : N = fromBlocks 0 (star P) P 0 := by
    ext (i|i) (j|j)
    · exact h₀ i j
    · have h := congrFun (congrFun hNs (.inl i)) (.inr j)
      exact h.symm
    · rfl
    · exact h₁ i j
  have hp : P ∈ unitary (Matrix E E ℂ) := by
    have hs : N * N = 1 := by simpa only [hNs] using hNu.1
    rw [he,fromBlocks_multiply] at hs
    constructor
    · ext i j
      have h := congrFun (congrFun hs (.inl i)) (.inl j)
      simpa [Matrix.one_apply] using h
    · ext i j
      have h := congrFun (congrFun hs (.inr i)) (.inr j)
      simpa [Matrix.one_apply] using h
  exact ⟨⟨P,hp⟩,he⟩
end

open Matrix KervaireFixed
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
attribute [local instance] OAI.KervaireTraversal.instDecidableEqSlots
end KervaireTraversal

namespace KervaireMatrix
open Matrix KervaireRegular
open scoped Classical
variable {D : Type*} [Fintype D]

variable {A : Type*} [Group A]
end KervaireMatrix

namespace KervaireMixing
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A] [Nonempty I] [Nonempty K]
attribute [local instance] OAI.KervaireMixing.instDecidableEqSlot
end KervaireMixing

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireTraversal
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
open Matrix KervaireFixed
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireTraversal.offDiagonal_representation := @_root_.OAI.KervaireTraversal.offDiagonal_representation
