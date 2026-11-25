-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.fdeg_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:13.156154+00:00
-- url     : https://prove2.me/submissions/2b578378-310f-48e5-a10f-ebf6cdcc3e62

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_fdeg_ratio_abs
import Theorems.Thm_GlobalTheory_CompareIterDegree_fac_nonneg

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
theorem _root_.solution {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (ht : |t| ≤ 1)
    (hgap : ∀ a b, a ≠ b → 1 ≤ |μ a - μ b|) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c) := by
  have hinj : Function.Injective μ := fun a b hab => by
    by_contra hne
    have := hgap a b hne
    rw [hab, sub_self, abs_zero] at this
    linarith
  rw [fdeg_ratio_abs μ s t hinj]
  refine prod_congr rfl fun c hc => abs_of_nonneg ?_
  rw [add_sub_right_comm]
  exact fac_nonneg (hgap s c (ne_of_mem_erase hc).symm) ht
end GlobalTheory.CompareIterDegree
