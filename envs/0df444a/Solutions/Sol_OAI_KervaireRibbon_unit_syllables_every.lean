-- Prove2me | solution 1 for OAI.KervaireRibbon.unit_syllables_every
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:39:59.340751+00:00
-- url     : https://prove2.me/submissions/93a303f1-e88c-436a-b1c2-c6641fa729e9

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
import Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon
import Definitions.Def_OAI_GroupTheory_Kervaire_RibbonProducts
import Definitions.Def_OAI_GroupTheory_Kervaire_Conjugation
import Definitions.Def_OAI_GroupTheory_Kervaire_Inversion
import Definitions.Def_OAI_GroupTheory_Kervaire_Realization
import Definitions.Def_OAI_GroupTheory_Kervaire_Annulus
import Definitions.Def_OAI_GroupTheory_Kervaire_WordNormalization

open OAI OAI.KervaireRibbon
open Monoid Multiplicative
variable {A : Type*} [Group A]


theorem solution (w : FreeProd A) :
    ∃ l : List (ℤ × A), 2 ≤ l.length ∧ UnitSyllables l ∧ syllableEval l = w := by
  have hmul : ∀ l m : List (ℤ × A), syllableEval (l ++ m) = syllableEval l * syllableEval m := by
    intro l m; simp [syllableEval]
  have hU : ∀ l m : List (ℤ × A), UnitSyllables l → UnitSyllables m → UnitSyllables (l ++ m) := by
    intro l m hl hm x hx
    rcases List.mem_append.mp hx with h | h
    · exact hl x h
    · exact hm x h
  have hP : ∀ w : FreeProd A, ∃ l : List (ℤ × A), UnitSyllables l ∧ syllableEval l = w := by
    intro w
    induction w using Monoid.Coprod.induction_on with
    | inl g =>
      refine ⟨[(1, 1), (-1, g)], ?_, ?_⟩
      · intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp
      · simp only [syllableEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_one, mul_one, ← map_mul]
        rw [← mul_assoc, ← map_mul, ← ofAdd_add]; simp
    | inr n =>
      obtain ⟨k, rfl⟩ : ∃ k : ℤ, ofAdd k = n := ⟨n.toAdd, rfl⟩
      have h1 : ∃ l : List (ℤ × A), UnitSyllables l ∧ syllableEval l = Coprod.inr (ofAdd (1:ℤ)) :=
        ⟨[(1,1)], by intro x hx; simp at hx; simp [hx], by simp [syllableEval]⟩
      have h2 : ∃ l : List (ℤ × A), UnitSyllables l ∧ syllableEval l = Coprod.inr (ofAdd (-1:ℤ)) :=
        ⟨[(-1,1)], by intro x hx; simp at hx; simp [hx], by simp [syllableEval]⟩
      induction k using Int.induction_on with
      | zero => exact ⟨[], by intro x hx; simp at hx, by simp [syllableEval]⟩
      | succ k ih =>
        obtain ⟨l, hl, he⟩ := ih
        obtain ⟨m, hm, hme⟩ := h1
        exact ⟨l ++ m, hU l m hl hm, by rw [hmul, he, hme, ← map_mul, ← ofAdd_add]⟩
      | pred k ih =>
        obtain ⟨l, hl, he⟩ := ih
        obtain ⟨m, hm, hme⟩ := h2
        exact ⟨l ++ m, hU l m hl hm, by rw [hmul, he, hme, ← map_mul, ← ofAdd_add]; rfl⟩
    | mul x y hx hy =>
      obtain ⟨l, hl, he⟩ := hx
      obtain ⟨m, hm, hme⟩ := hy
      exact ⟨l ++ m, hU l m hl hm, by rw [hmul, he, hme]⟩
  obtain ⟨l, hl, he⟩ := hP w
  refine ⟨[(1, 1), (-1, 1)] ++ l, by simp, hU _ _ ?_ hl, ?_⟩
  · intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp
  · rw [hmul, he]
    simp only [syllableEval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_one, mul_one]
    rw [← map_mul, ← ofAdd_add]; simp

