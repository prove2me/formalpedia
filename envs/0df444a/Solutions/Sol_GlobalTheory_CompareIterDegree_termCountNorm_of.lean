-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.termCountNorm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:53.642662+00:00
-- url     : https://prove2.me/submissions/1e9d14e5-8fe9-49f2-b991-23e6ec4d04ac

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
theorem _root_.solution (h : TermCount) : TermCountNorm := by
  intro V _ _ n l H H' τ ρ v w hH hH' hτ hρ hw
  refine (norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_right
    (h n l H H' τ ρ hH hH' hτ hρ) (norm_nonneg v)))
  rw [sum_mul]
  refine sum_le_sum fun I hI => ?_
  rw [norm_smul, norm_mul_sqrt, abs_norm, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hw I (mem_powersetCard.1 hI).2) (norm_nonneg _)
end GlobalTheory.CompareIterDegree
