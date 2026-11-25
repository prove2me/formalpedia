-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.gapSubset_of_gapStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:44.544553+00:00
-- url     : https://prove2.me/submissions/97864598-b578-490f-876a-62c89b5693e6

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_chain_bound
import Theorems.Thm_GlobalTheory_CompareIterDegree_eSet_insert
import Theorems.Thm_GlobalTheory_CompareIterDegree_eSet_empty
import Theorems.Thm_GlobalTheory_CompareIterDegree_inj_of_gapTwo
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
theorem _root_.solution (h : GapStepSize) : GapSubsetSize := by
  intro n μ I
  constructor
  · intro hg
    have := chain_bound (fun J => fdegHC (μ + eSet J)) (1 / (4 * (n : ℝ) ^ 2)) (Real.exp 1 * n) (by positivity) I
      (fun J hJ => formal_degree_pos_holds n _ (inj_of_gapTwo (hg J hJ))) (fun J s hs hJ => by
        have h1 := hg _ hJ
        rw [eSet_insert hs, ← add_assoc] at h1 ⊢
        exact (h n _ s (hg J ((subset_insert _ _).trans hJ))).1 h1)
    simpa only [eSet_empty, add_zero] using this
  · intro hg
    have := chain_bound (fun J => fdegHC (μ - eSet J)) (1 / (4 * (n : ℝ) ^ 2)) (Real.exp 1 * n) (by positivity) I
      (fun J hJ => formal_degree_pos_holds n _ (inj_of_gapTwo (hg J hJ))) (fun J s hs hJ => by
        have h1 := hg _ hJ
        rw [eSet_insert hs, ← sub_sub] at h1 ⊢
        exact (h n _ s (hg J ((subset_insert _ _).trans hJ))).2 h1)
    simpa only [eSet_empty, sub_zero] using this
end GlobalTheory.CompareIterDegree
