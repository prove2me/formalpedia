-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.fac_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:11:40.162854+00:00
-- url     : https://prove2.me/submissions/b3da7947-fcbf-4c3f-825f-3e7530df7b43

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
theorem _root_.solution {d t : ℝ} (hd : 1 ≤ |d|) (ht : |t| ≤ 1) : 0 ≤ (d + t) / d := by
  rw [abs_le] at ht
  rcases le_abs.1 hd with h | h
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg_of_nonpos (by linarith) (by linarith)
end GlobalTheory.CompareIterDegree
