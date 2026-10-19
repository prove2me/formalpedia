-- Prove2me | solution 1 for OAI.KervaireFlow.exists_flow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:47:42.132257+00:00
-- url     : https://prove2.me/submissions/6c6a5616-3249-41ef-af01-319b924ae1e5

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
variable {D Z : Type*} [Fintype D] [Fintype Z]


theorem solution (b : D → Z) (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hconn : ∀ x y, Relation.ReflTransGen (Adj b θ) x y)
    (root : Z) (η : Z → ℝ) (hη : ∑ z, η z = 0) :
    ∃ γ : D → ℝ, (∀ d, γ (θ d) = -γ d) ∧
      ∀ z, (∑ d, if b d = z then γ d else 0) = η z := by
  let δ : Z → Z → ℝ := fun x z => if x = z then 1 else 0
  have hstep : ∀ x y, Relation.ReflTransGen (Adj b θ) x y →
      ∃ γ : D → ℝ, (∀ d, γ (θ d) = -γ d) ∧ ∀ z, (∑ d, if b d = z then γ d else 0) = δ x z - δ y z := by
    intro x y h
    induction h with
    | refl => exact ⟨0, by simp, by intro z; simp⟩
    | tail _ hyw ih =>
      rename_i y w
      obtain ⟨γ, hγ1, hγ2⟩ := ih
      obtain ⟨d, rfl, rfl⟩ := hyw
      refine ⟨fun e => γ e + ((if e = d then 1 else 0) - (if e = θ d then 1 else 0)), ?_, ?_⟩
      · intro e
        dsimp only
        rw [hγ1]
        have h1 : (θ e = d) ↔ (e = θ d) := ⟨fun h => by rw [← h, hθ], fun h => by rw [h, hθ]⟩
        have h2 : (θ e = θ d) ↔ (e = d) := θ.injective.eq_iff
        simp only [h1, h2]; ring
      · intro z
        have hs : ∀ e, (if b e = z then γ e + ((if e = d then (1:ℝ) else 0) - (if e = θ d then 1 else 0)) else 0)
            = (if b e = z then γ e else 0) + ((if e = d then (if b d = z then 1 else 0) else 0)
              - (if e = θ d then (if b (θ d) = z then 1 else 0) else 0)) := by
          intro e
          by_cases h1 : e = d
          · rw [h1]
            by_cases h2 : d = θ d
            · have h3 : θ d = d := h2.symm
              simp only [h3, if_true]; split_ifs <;> ring
            · simp only [h2, if_true, if_false]; split_ifs <;> ring
          · by_cases h2 : e = θ d
            · rw [h2]; have h3 : θ d ≠ d := fun h => h1 (h2.trans h)
              simp only [h3, if_true, if_false]; split_ifs <;> ring
            · simp only [h1, h2, if_false]; split_ifs <;> ring
        simp only [hs, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hγ2]
        simp only [δ]; ring
  choose γz hγz1 hγz2 using fun z => hstep z root (hconn z root)
  refine ⟨fun e => ∑ z, η z * γz z e, ?_, ?_⟩
  · intro e
    simp only [hγz1, mul_neg, Finset.sum_neg_distrib]
  · intro w
    have : ∀ d, (if b d = w then ∑ z, η z * γz z d else 0) = ∑ z, η z * (if b d = w then γz z d else 0) := by
      intro d; split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hγz2, δ, mul_sub, Finset.sum_sub_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs <;> simp [hη]

