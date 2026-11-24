-- Prove2me | solution 1 for GlobalTheory.HeckeTwoMul.isGood_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:00:03.832779+00:00
-- url     : https://prove2.me/submissions/ffc7295e-d260-49ef-96f2-1badb67db632

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyMulLeft
import Theorems.Thm_GlobalTheory_HeckeTwoMul_wirtWord_const_mul

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
open GlobalTheory GlobalTheory.HeckeTwoMul
namespace GlobalTheory.HeckeTwoMul
theorem _root_.solution (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ)
    (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ) (hk : DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane)
    (hP : GlobalTheory.HeckeTwo.IsGood P) : GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun σ hσ => contDiffOn_const.mul (h1 σ hσ), fun w z hz => ?_⟩
  simp only [wirtWord_const_mul]
  exact hk.mul (h2 w z hz)
end GlobalTheory.HeckeTwoMul
