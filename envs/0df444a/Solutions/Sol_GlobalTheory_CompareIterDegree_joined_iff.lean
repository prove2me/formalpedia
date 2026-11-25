-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.joined_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:50.974906+00:00
-- url     : https://prove2.me/submissions/00899595-c410-4ef9-9805-4035acbad4cc

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
namespace GlobalTheory.CompareIterDegree
theorem _root_.solution {n : ℕ} (Q : Set (Fin n → ℝ)) (μ ν : Fin n → ℝ) :
    Relation.EqvGen (fun x y => x ∈ Q ∧ y ∈ Q ∧ ∃ s, y = x + Pi.single s 1) μ ν ↔
      Relation.ReflTransGen (StepIn Q) μ ν := by
  have hsymm : ∀ {x y}, StepIn Q x y → StepIn Q y x := by
    rintro x y ⟨hx, hy, s, rfl | rfl⟩
    · exact ⟨hy, hx, s, Or.inr (by simp)⟩
    · exact ⟨hy, hx, s, Or.inl (by simp)⟩
  have hrev : ∀ {x y}, Relation.ReflTransGen (StepIn Q) x y → Relation.ReflTransGen (StepIn Q) y x := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact .head (hsymm hs) ih
  constructor
  · intro h
    induction h with
    | rel x y h => obtain ⟨hx, hy, s, hs⟩ := h; exact .single ⟨hx, hy, s, Or.inl hs⟩
    | refl x => exact .refl
    | symm x y _ ih => exact hrev ih
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ hs ih =>
      refine .trans _ _ _ ih ?_
      obtain ⟨hx, hy, s, rfl | rfl⟩ := hs
      · exact .rel _ _ ⟨hx, hy, s, rfl⟩
      · exact .symm _ _ (.rel _ _ ⟨hy, hx, s, by simp⟩)
end GlobalTheory.CompareIterDegree
