-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.GoodAdd.wirtWord_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:27.643144+00:00
-- url     : https://prove2.me/submissions/81552d85-bb32-4ada-b6b6-64af1408a161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirt_contDiffOn
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_cons
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_nil


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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.GoodAdd
variable {Φ : Type} [Fintype Φ]
namespace GlobalTheory.HeckeTwo.GoodAdd
theorem _root_.solution {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (wirtWord w f) U := by
  induction w with
  | nil => simpa [wirtWord_nil] using hf
  | cons a w ih => rw [wirtWord_cons]; exact wirt_contDiffOn hU ih _ _
end GlobalTheory.HeckeTwo.GoodAdd
