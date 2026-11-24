-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.isGood_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:36.200437+00:00
-- url     : https://prove2.me/submissions/312bb1c0-09c0-4e67-89be-b4ca9e373d36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirtWord_add
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_upperHalf_isOpen

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
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (P Q : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood Q → GlobalTheory.HeckeTwo.IsGood (fun σ z => P σ z + Q σ z) := by
  intro F _ _ P Q hP hQ
  have hU := GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen F
  refine ⟨fun σ hσ => (hP.1 σ hσ).add (hQ.1 σ hσ), fun w z hz => ?_⟩
  refine ((hP.2 w z hz).add (hQ.2 w z hz)).congr fun σ hσ => ?_
  exact GlobalTheory.HeckeTwo.GoodAdd.wirtWord_add hU w (hP.1 σ hσ) (hQ.1 σ hσ) hz
end GlobalTheory.HeckeTwo
