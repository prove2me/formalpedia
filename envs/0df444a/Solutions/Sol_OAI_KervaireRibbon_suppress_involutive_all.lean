-- Prove2me | solution 1 for OAI.KervaireRibbon.suppress_involutive_all
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:31:52.544527+00:00
-- url     : https://prove2.me/submissions/92b612c3-9d72-4ba4-a4eb-3e8988a96bf1

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
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]
omit [Fintype D] in
theorem kr_suppress_involutive (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    ∀ d, suppress θ x y (suppress θ x y d) = d := by
  intro d
  set a := θ x with ha
  let θ' : D → D := fun d => swap y a (θ (swap y a d))
  have hinv : ∀ d, θ' (θ' d) = d := by
    intro d; simp only [θ', swap_apply_self, hθ]
  have hya : y ≠ a := fun h => hxy' h.symm
  have hxa : x ≠ a := fun h => hx h.symm
  have h1 : θ' x = y := by
    simp only [θ']
    rw [swap_apply_of_ne_of_ne hxy hxa, ← ha, swap_apply_right]
  have h2 : θ' y = x := by
    simp only [θ']
    rw [swap_apply_left, ha, hθ, swap_apply_of_ne_of_ne hxy hxa]
  have hs : ∀ d, suppress θ x y d = swap x y (θ' d) := by
    intro d; simp only [suppress, Perm.mul_apply, θ']; rfl
  rw [hs, hs]
  by_cases hu1 : θ' d = x
  · rw [hu1, swap_apply_left, h2, swap_apply_left]
    have := congrArg θ' hu1; rw [hinv, h1] at this; exact this.symm
  by_cases hu2 : θ' d = y
  · rw [hu2, swap_apply_right, h1, swap_apply_right]
    have := congrArg θ' hu2; rw [hinv, h2] at this; exact this.symm
  rw [swap_apply_of_ne_of_ne hu1 hu2, hinv]
  have hdx : d ≠ x := fun h => hu2 (by rw [h, h1])
  have hdy : d ≠ y := fun h => hu1 (by rw [h, h2])
  exact swap_apply_of_ne_of_ne hdx hdy

omit [Fintype D] in
theorem solution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) :
    ∀ d, suppress θ x y (suppress θ x y d) = d := by
  by_cases h : θ x = y
  · intro d
    have hyx : θ y = x := by rw [← h, hθ]
    have hs : ∀ d, suppress θ x y d = swap x y (θ d) := by
      intro d; simp [suppress, h, Perm.mul_apply]
    rw [hs, hs]
    by_cases h1 : d = x
    · subst h1; rw [h, swap_apply_right, h, swap_apply_right]
    by_cases h2 : d = y
    · subst h2; rw [hyx, swap_apply_left, hyx, swap_apply_left]
    have h3 : θ d ≠ x := fun e => h2 (by rw [← hyx] at e; exact θ.injective e)
    have h4 : θ d ≠ y := fun e => h1 (by rw [← h] at e; exact θ.injective e)
    rw [swap_apply_of_ne_of_ne h3 h4, hθ, swap_apply_of_ne_of_ne h1 h2]
  · exact kr_suppress_involutive θ hθ hxy hx h hy

