-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.gapStep_of_stepBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:04:43.965474+00:00
-- url     : https://prove2.me/submissions/c8423f5d-5b73-4332-82f1-e6483f32baa8

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_sub_single
import Theorems.Thm_GlobalTheory_CompareIterDegree_real_step
import Theorems.Thm_GlobalTheory_CompareIterDegree_weaken_consts

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
theorem _root_.solution (h : DegStepBound) : GapStepSize := by
  intro n μ s hg
  obtain ⟨w1, w2⟩ := weaken_consts s.pos
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨a, b⟩ := real_step h hg s 1 (Or.inl rfl)
    exact ⟨w1.trans a, b.trans w2⟩
  · obtain ⟨a, b⟩ := real_step h hg s (-1) (Or.inr rfl)
    rw [sub_single]
    exact ⟨w1.trans a, b.trans w2⟩
end GlobalTheory.CompareIterDegree
