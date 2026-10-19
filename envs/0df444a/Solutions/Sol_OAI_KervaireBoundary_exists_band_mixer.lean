-- Prove2me | solution 1 for OAI.KervaireBoundary.exists_band_mixer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:53:09.852173+00:00
-- url     : https://prove2.me/submissions/408a5e03-675d-43d9-b229-af6796717e8a

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean:L201-L232
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireBoundary.exists_band_mixer. The node keeps its source
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
import Theorems.Thm_OAI_KervaireMatrix_monomial_star
import Theorems.Thm_OAI_KervaireTraversal_exists_mixer_for_exchange

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

lemma monomial_unitary [DecidableEq D] (θ : Equiv.Perm D) (u : D → ℂ)
    (hu : ∀ d, u d ∈ unitary ℂ) : monomial θ u ∈ unitary (Matrix D D ℂ) := by
  rw [Unitary.mem_iff,monomial_star,monomial_mul,monomial_mul]
  constructor
  · simp only [inv_mul_cancel]
    change monomial (Equiv.refl D) (fun j ↦ star (u (θ.symm (θ j))) * u j) = 1
    simpa only [Equiv.symm_apply_apply,funext (fun j ↦ (hu j).1)] using monomial_one (D := D)
  · simp only [mul_inv_cancel]
    change monomial (Equiv.refl D) (fun j ↦ u (θ.symm j) * star (u (θ.symm j))) = 1
    simpa only [funext (fun j ↦ (hu (θ.symm j)).2)] using monomial_one (D := D)

omit [Fintype D] in
lemma monomial_selfadjoint (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → ℂ) (hu : ∀ d, u (θ d) = star (u d)) :
    star (monomial θ u) = monomial θ u := by
  have hi : θ⁻¹ = θ := by ext d; exact (θ.injective (by simp [hθ]))
  rw [monomial_star,hi]
  congr 1
  ext d
  simp [hu]

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

-- ---- from OAI.GroupTheory.Kervaire.BoundaryFlow ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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
end KervaireFlow
namespace KervaireBoundary

section
open Matrix KervaireMatrix KervaireRegular KervaireSpectral KervaireMixing KervaireTraversal
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot
omit [Fintype I] [Fintype K] in
lemma traversalSign_positive (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (p : K × I) :
    traversalSign s (coordinates s (.inl p)) = 1 := by
  rcases p with ⟨k,i⟩
  rcases hs i with h | h <;> simp [coordinates,traversalSign,h]

omit [Fintype I] [Fintype K] in
lemma traversalSign_negative (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (p : K × I) :
    traversalSign s (coordinates s (.inr p)) = -1 := by
  rcases p with ⟨k,i⟩
  rcases hs i with h | h <;> simp [coordinates,traversalSign,h]

/-- The signed band involution supplies exactly the scalar hypotheses of the
full fixed-space mixing theorem. -/
lemma exists_band_mixer [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Equiv.Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = -traversalSign s d)
    (γ : Slot I K → ℝ) (hγ : ∀ d, γ (θ d) = -γ d) :
    ∃ X : Matrix.unitaryGroup K ℂ, 2 * Fintype.card K ≤
      KervaireFixed.fixedDim (mixingMatrix (I := I) (X : Matrix K K ℂ) *
        monomial θ (fun d ↦ scalarRotation (γ d))) := by
  let T := monomial θ (fun d ↦ scalarRotation (γ d))
  have hsT : star T = T := monomial_selfadjoint θ hθ _ (by
    intro d
    rw [hγ,star_scalarRotation])
  have huT : T ∈ unitary (Matrix (Slot I K) (Slot I K) ℂ) :=
    monomial_unitary θ _ (fun d ↦ scalarRotation_unitary _)
  have h₀ (i j : K × I) : T (coordinates s (.inl i)) (coordinates s (.inl j)) = 0 := by
    have hn : coordinates s (.inl i) ≠ θ (coordinates s (.inl j)) := by
      intro he
      have hh := hop (coordinates s (.inl j))
      rw [← he,traversalSign_positive s hs,traversalSign_positive s hs] at hh
      omega
    simp only [T,monomial,ite_eq_right hn]
  have h₁ (i j : K × I) : T (coordinates s (.inr i)) (coordinates s (.inr j)) = 0 := by
    have hn : coordinates s (.inr i) ≠ θ (coordinates s (.inr j)) := by
      intro he
      have hh := hop (coordinates s (.inr j))
      rw [← he,traversalSign_negative s hs,traversalSign_negative s hs] at hh
      omega
    simp only [T,monomial,ite_eq_right hn]
  obtain ⟨X,hX⟩ := exists_mixer_for_exchange s hs hsum T hsT huT h₀ h₁
  exact ⟨X,hX⟩

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
open OAI OAI.KervaireBoundary
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
open Matrix KervaireMatrix KervaireRegular KervaireSpectral KervaireMixing KervaireTraversal
open scoped Classical
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot


theorem solution : type_of% @_root_.OAI.KervaireBoundary.exists_band_mixer := @_root_.OAI.KervaireBoundary.exists_band_mixer
