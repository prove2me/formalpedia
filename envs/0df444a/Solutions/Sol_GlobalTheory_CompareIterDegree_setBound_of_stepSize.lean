-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.setBound_of_stepSize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:47.07685+00:00
-- url     : https://prove2.me/submissions/a92bdd56-166a-48a0-ac63-1234d6265979

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_chain_bound
import Theorems.Thm_GlobalTheory_CompareIterDegree_eSet_insert
import Theorems.Thm_GlobalTheory_CompareIterDegree_eSet_empty
import Theorems.Thm_GlobalTheory_CompareIterDegree_inj_add_of_gapTwo
import Theorems.Thm_GlobalTheory_CompareIterDegree_gapTwo_iff
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
theorem _root_.solution (h : StepSize) : DegSetBound := by
  intro n μ I hanti hint hgap
  have hg := (gapTwo_iff hanti).1 hgap
  have hreg : ∀ J : Finset (Fin n), RegInt (μ + eSet J) := fun J =>
    ⟨inj_add_of_gapTwo hg fun a b => by unfold eSet; split_ifs <;> simp, fun a b => by
      obtain ⟨m, hm⟩ := hint a b
      refine ⟨m + (if a ∈ J then 1 else 0) - (if b ∈ J then 1 else 0), ?_⟩
      simp only [Pi.add_apply, eSet]
      push_cast
      linarith⟩
  have := chain_bound (fun J => fdegHC (μ + eSet J)) (1 / n) n (by positivity) I
    (fun J _ => formal_degree_pos_holds n _ (hreg J).1) (fun J s hs _ => by
      have h1 := (hreg (insert s J)).1
      rw [eSet_insert hs, ← add_assoc] at h1 ⊢
      exact (h n _ s (hreg J)).1 h1)
  simp only [eSet_empty, add_zero, one_div, inv_pow] at this
  exact this
end GlobalTheory.CompareIterDegree
