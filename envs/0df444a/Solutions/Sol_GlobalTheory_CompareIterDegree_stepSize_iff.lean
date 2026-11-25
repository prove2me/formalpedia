-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.stepSize_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:04:46.263861+00:00
-- url     : https://prove2.me/submissions/e8c2b8c0-996c-4f7d-8186-1d109db7ed49

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_step_ratio_eq

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
theorem _root_.solution : DegStepBound ↔ StepSize := by
  refine forall_congr' fun n => forall_congr' fun μ => forall_congr' fun s => ?_
  rw [RegInt, and_imp]
  refine forall_congr' fun h1 => forall_congr' fun h2 => ?_
  rw [(step_ratio_eq ⟨h1, h2⟩ s).1, (step_ratio_eq ⟨h1, h2⟩ s).2]
end GlobalTheory.CompareIterDegree
