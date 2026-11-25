-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.degreeProportional_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:18.836111+00:00
-- url     : https://prove2.me/submissions/22ebbec1-19f4-4e85-806f-de3fc0767486

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_joined_iff
import Theorems.Thm_Formalism_QuantumDeterminants_formal_degree_pos_holds


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
theorem _root_.solution : DegVand ↔ DegreeProportional := by
  constructor
  · intro h n P Q d hreg hpos hstep hPQ hjoin
    rcases P.eq_empty_or_nonempty with rfl | ⟨μ₀, h0⟩
    · exact ⟨1, one_pos, by simp⟩
    refine ⟨d μ₀ / fdegHC μ₀, div_pos (hpos _ (hPQ h0)) (formal_degree_pos_holds n _ (hreg _ (hPQ h0)).1),
      fun μ hμ => ?_⟩
    rw [h n Q d hreg hpos hstep μ₀ μ ((joined_iff Q _ _).2 (hjoin _ h0 _ hμ)) (hPQ h0),
      div_mul_cancel₀ _ (formal_degree_pos_holds n _ (hreg _ (hPQ hμ)).1).ne']
  · intro h n Q d hreg hpos hstep μ ν hj hμ
    have hν : ν ∈ Q := by
      have := (joined_iff Q _ _).1 hj
      induction this with
      | refl => exact hμ
      | tail _ hs _ => exact hs.2.1
    obtain ⟨c, -, hc⟩ := h n {μ, ν} Q d hreg hpos hstep (Set.pair_subset hμ hν) (by
      rintro x (rfl | rfl) y (rfl | rfl)
      · exact .refl
      · exact (joined_iff Q _ _).1 hj
      · exact (joined_iff Q _ _).1 (.symm _ _ hj)
      · exact .refl)
    rw [hc μ (by simp), hc ν (by simp), mul_div_cancel_right₀ _ (formal_degree_pos_holds n _ (hreg _ hμ).1).ne',
      mul_div_cancel_right₀ _ (formal_degree_pos_holds n _ (hreg _ hν).1).ne']
end GlobalTheory.CompareIterDegree
