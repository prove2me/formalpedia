-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.typings_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:44:58.56132+00:00
-- url     : https://prove2.me/submissions/f5e299fa-d150-4765-87ee-cf1b986e2adf

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_termCount_iff
import Theorems.Thm_GlobalTheory_CompareIterDegree_termCountNorm_of
import Theorems.Thm_GlobalTheory_CompareIterDegree_iteration_iff
import Theorems.Thm_GlobalTheory_CompareIterDegree_iterationSum_of
import Theorems.Thm_GlobalTheory_CompareIterDegree_iterationGauge_of
import Theorems.Thm_GlobalTheory_CompareIterDegree_stepSize_iff
import Theorems.Thm_GlobalTheory_CompareIterDegree_setBound_of_stepSize
import Theorems.Thm_GlobalTheory_CompareIterDegree_gapSubset_of_gapStep
import Theorems.Thm_GlobalTheory_CompareIterDegree_gapStep_of_stepBound
import Theorems.Thm_GlobalTheory_CompareIterDegree_degreeProportional_iff

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
theorem _root_.solution :
    (FormalDegreeSubsetSum ∧ IteratedHighestWeightBound ∧ DegSetBound ∧ DegStepBound ∧ DegVand) ↔ Statement := by
  constructor
  · rintro ⟨h1, h2, -, h4, h5⟩
    have t := termCount_iff.1 h1
    have i := iteration_iff.1 h2
    have g := gapStep_of_stepBound h4
    exact ⟨t, termCountNorm_of t, i, iterationSum_of i, iterationGauge_of i, stepSize_iff.1 h4, g,
      gapSubset_of_gapStep g, degreeProportional_iff.1 h5⟩
  · rintro ⟨t, -, i, -, -, s, -, -, d⟩
    exact ⟨termCount_iff.2 t, iteration_iff.2 i, setBound_of_stepSize s, stepSize_iff.2 s,
      degreeProportional_iff.2 d⟩
end GlobalTheory.CompareIterDegree
