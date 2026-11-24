-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.contDiffOn_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:44.315988+00:00
-- url     : https://prove2.me/submissions/eff582cb-79a2-4809-a409-5b7093b02f16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_hasFDerivAt_tsum
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_goodFam_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.SumGood
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] {ι : Type}
namespace GlobalTheory.HeckeTwo.SumGood
theorem _root_.solution {U : Set V} (hU : IsOpen U) (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ι → V → E},
      GoodFam U f → ContDiffOn ℝ n (fun y => ∑' i, f i y) U := by
  induction n with
  | zero =>
    intro E _ _ _ f hf
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun z hz => (hasFDerivAt_tsum hU hf hz).continuousAt.continuousWithinAt
  | succ n ih =>
    intro E _ _ _ f hf
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun z hz => (hasFDerivAt_tsum hU hf hz).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, ?_⟩
    exact (ih (goodFam_fderiv hU hf)).congr fun z hz => (hasFDerivAt_tsum hU hf hz).fderiv
end GlobalTheory.HeckeTwo.SumGood
