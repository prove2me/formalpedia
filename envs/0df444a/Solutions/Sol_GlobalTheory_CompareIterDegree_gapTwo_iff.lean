-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.gapTwo_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:00.611772+00:00
-- url     : https://prove2.me/submissions/de0d6633-84b3-496c-89e9-7ed5a787e8f3

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
theorem _root_.solution {n : ℕ} {μ : Fin n → ℝ} (h : StrictAnti μ) :
    (∀ a b, a < b → 2 ≤ μ a - μ b) ↔ GapTwo μ := by
  constructor
  · intro hg a b hab
    rcases lt_or_gt_of_ne hab with h1 | h1
    · exact (hg a b h1).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hg b a h1).trans (le_abs_self _)
  · intro hg a b hab
    have := hg a b hab.ne
    rwa [abs_of_pos (sub_pos.2 (h hab))] at this
end GlobalTheory.CompareIterDegree
