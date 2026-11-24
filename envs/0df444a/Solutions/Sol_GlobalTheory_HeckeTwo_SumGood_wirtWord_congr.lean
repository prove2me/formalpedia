-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.wirtWord_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:10.40581+00:00
-- url     : https://prove2.me/submissions/72f70c4e-978f-4a0e-b845-9e5ac639ff7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirt_congr


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
variable {Φ : Type} [Fintype Φ] {ι : Type}
namespace GlobalTheory.HeckeTwo.SumGood
theorem _root_.solution {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool))
    {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by
  induction w with
  | nil => exact h
  | cons a w ih => exact GoodAdd.wirt_congr hU ih a.1 a.2
end GlobalTheory.HeckeTwo.SumGood
