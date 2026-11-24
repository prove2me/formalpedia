-- Prove2me | solution 1 for GlobalTheory.WirtChain.ExpSum.holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:50.723918+00:00
-- url     : https://prove2.me/submissions/ca87e1cf-1a42-4b56-90ee-33b3bd1fcc96

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp

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
theorem _root_.solution {D : Set ℂ} {V : Set (Φ → ℂ)} (hmaps : Set.MapsTo t U V)
    (hGh : ∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {z : I → ℂ} (hz : z ∈ U) :
    DifferentiableOn ℂ (fun σ => F σ z) D := by
  induction hF with
  | zero => exact differentiableOn_const _
  | term n β w hβ =>
    exact (((differentiableOn_id.pow n).mul (differentiableOn_const _)).mul
      ((differentiableOn_id.neg.mul_const (l z)).cexp)).mul (hGh w (t z) (hmaps hz))
  | add _ _ h₁ h₂ => exact h₁.add h₂
end ExpSum
end GlobalTheory.WirtChain
