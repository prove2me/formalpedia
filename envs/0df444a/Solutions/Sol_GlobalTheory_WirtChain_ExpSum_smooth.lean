-- Prove2me | solution 1 for GlobalTheory.WirtChain.ExpSum.smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:12.650925+00:00
-- url     : https://prove2.me/submissions/6ae7b417-2bd7-428f-b7a1-4aee6e819fe7

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
import Theorems.Thm_P2M_GlobalTheory_WirtChain_contDiffOn_wirtWord__3aa88b37ccd1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.WirtChain
open Complex
variable {Φ I : Type} [Fintype Φ] [Fintype I]
variable (U : Set (I → ℂ)) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (l : (I → ℂ) → ℂ)
variable {U G t l}
namespace GlobalTheory.WirtChain
namespace ExpSum
theorem _root_.solution {D : Set ℂ} {V : Set (Φ → ℂ)} (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {σ : ℂ} (hσ : σ ∈ D) :
    ContDiffOn ℝ ∞ (F σ) U := by
  induction hF with
  | zero => exact contDiffOn_const
  | term n β w hβ =>
    exact ((contDiffOn_const.mul hβ).mul (contDiffOn_const.mul hl).cexp).mul
      ((contDiffOn_wirtWord' hV (hGs σ hσ) w).comp ht hmaps)
  | add _ _ h₁ h₂ => exact h₁.add h₂
end ExpSum
end GlobalTheory.WirtChain
