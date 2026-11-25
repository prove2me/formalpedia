-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:30.219478+00:00
-- url     : https://prove2.me/submissions/cc98b966-748c-405f-ae1c-d81b0486fd28

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
theorem _root_.solution {α : Type} [DecidableEq α] (F : Finset α → ℝ) (lo hi : ℝ) (hlo : 0 ≤ lo) (I : Finset α)
    (hpos : ∀ J ⊆ I, 0 < F J)
    (hstep : ∀ J s, s ∉ J → insert s J ⊆ I → lo ≤ F (insert s J) / F J ∧ F (insert s J) / F J ≤ hi) :
    lo ^ I.card ≤ F I / F ∅ ∧ F I / F ∅ ≤ hi ^ I.card := by
  have h0 := hpos ∅ (empty_subset _)
  induction I using Finset.induction_on with
  | empty => simp [h0.ne']
  | insert s J hs ih =>
    have hJ := hpos J (subset_insert _ _)
    obtain ⟨i1, i2⟩ := ih (fun K hK => hpos K (hK.trans (subset_insert _ _)))
      (fun K u hu hK => hstep K u hu (hK.trans (subset_insert _ _)))
    obtain ⟨j1, j2⟩ := hstep J s hs subset_rfl
    have e : F (insert s J) / F ∅ = F J / F ∅ * (F (insert s J) / F J) := by field_simp
    rw [card_insert_of_notMem hs, pow_succ, pow_succ, e]
    exact ⟨mul_le_mul i1 j1 hlo (div_pos hJ h0).le,
      mul_le_mul i2 j2 (hlo.trans j1) ((div_pos hJ h0).le.trans i2)⟩
end GlobalTheory.CompareIterDegree
