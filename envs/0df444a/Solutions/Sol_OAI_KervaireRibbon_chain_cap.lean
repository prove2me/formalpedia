-- Prove2me | solution 1 for OAI.KervaireRibbon.chain_cap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:37:37.784496+00:00
-- url     : https://prove2.me/submissions/fab3747b-9f52-4f8f-8f8f-2eabb6ebe446

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

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]


omit [Finite D] in
theorem solution (σ : Perm D) (pre post : List D) {d x y : D}
    (hc : (pre ++ d::x::y::post).IsChain (fun x y ↦ σ x = y))
    (hxy : x ≠ y) (hno : ∀ z ∈ pre ++ d::post, z ≠ x ∧ z ≠ y) :
    (pre ++ d::post).IsChain (fun a b ↦ erase (erase σ x) y a = b) := by
  have key : ∀ a b, a ≠ x → a ≠ y → b ≠ x → b ≠ y → σ a = b → erase (erase σ x) y a = b := by
    intro a b ha1 ha2 hb1 hb2 hab
    have h1 : erase σ x a = b := by rw [erase_apply σ x a ha1, if_neg (by rw [hab]; exact hb1), hab]
    rw [erase_apply _ y a ha2, if_neg (by rw [h1]; exact hb2), h1]
  rw [List.isChain_split] at hc ⊢
  obtain ⟨hc1, hc2⟩ := hc
  constructor
  · refine hc1.imp_of_mem_imp ?_
    intro a b ha hb hab
    have ha' : a ∈ pre ++ d :: post := by simp at ha ⊢; tauto
    have hb' : b ∈ pre ++ d :: post := by simp at hb ⊢; tauto
    exact key a b (hno a ha').1 (hno a ha').2 (hno b hb').1 (hno b hb').2 hab
  · have hd := hno d (by simp)
    rw [List.isChain_cons_cons, List.isChain_cons_cons] at hc2
    obtain ⟨hdx, hxy', hc3⟩ := hc2
    cases post with
    | nil => exact List.IsChain.singleton _
    | cons p post' =>
      rw [List.isChain_cons_cons] at hc3 ⊢
      have hp := hno p (by simp)
      refine ⟨?_, hc3.2.imp_of_mem_imp ?_⟩
      · have h1 : erase σ x d = y := by rw [erase_apply σ x d hd.1, if_pos hdx, hxy']
        rw [erase_apply _ y d hd.2, if_pos h1, erase_apply σ x y (Ne.symm hxy), if_neg (by rw [hc3.1]; exact hp.1), hc3.1]
      · intro a b ha hb hab
        have ha' := hno a (by simp at ha ⊢; tauto)
        have hb' := hno b (by simp at hb ⊢; tauto)
        exact key a b ha'.1 ha'.2 hb'.1 hb'.2 hab

