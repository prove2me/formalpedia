-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.termCount_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:55.139409+00:00
-- url     : https://prove2.me/submissions/0ff82620-0df1-4232-aa46-0849462c5c8f

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_norm_mul_sqrt

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
theorem _root_.solution : FormalDegreeSubsetSum ↔ TermCount := by
  constructor
  · intro h n l H H' τ ρ hH hH' hτ hρ
    have := h n l (fun I => ‖τ I‖) ρ (H * H') (mul_nonneg hH hH')
      (fun I hI => ⟨by simpa using hτ I hI, (hρ I hI).1.le, (hρ I hI).2⟩)
    simp only [norm_mul_sqrt, gam]
    simpa only [mul_assoc] using this
  · intro h n l tau ratio H hH hI
    classical
    have key := h n l H 1 (fun I => if ratio I = 0 then 0 else (tau I : ℂ))
      (fun I => if ratio I = 0 then (Real.exp 1 * n) ^ l else ratio I) hH zero_le_one ?_ ?_
    · simp only [norm_mul_sqrt, gam, mul_one] at key
      refine le_trans (le_of_eq (sum_congr rfl fun I _ => ?_)) key
      by_cases h0 : ratio I = 0 <;> simp [h0]
    · intro I hc
      by_cases h0 : ratio I = 0
      · simp [h0, pow_nonneg hH]
      · simpa [h0] using (hI I hc).1
    · intro I hc
      by_cases h0 : ratio I = 0
      · simp only [h0, if_true, le_refl, and_true]
        rcases I.eq_empty_or_nonempty with rfl | ⟨s, _⟩
        · simp [← hc]
        · have : (0 : ℝ) < n := by exact_mod_cast s.pos
          positivity
      · simp only [h0, if_false]
        exact ⟨lt_of_le_of_ne (hI I hc).2.1 (Ne.symm h0), (hI I hc).2.2⟩
end GlobalTheory.CompareIterDegree
