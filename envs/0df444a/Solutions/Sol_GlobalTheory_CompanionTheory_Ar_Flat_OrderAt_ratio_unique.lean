-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.OrderAt.ratio_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:16.577079+00:00
-- url     : https://prove2.me/submissions/94dea145-5548-46fd-bee4-8aacf83a84c8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_OrderAt_mul_nat
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_OrderAt_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}
namespace GlobalTheory.CompanionTheory.Ar.Flat
namespace OrderAt
theorem _root_.solution (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ regAt ξ p) (hp : ¬ Ar.unitAt ξ p ϖ)
    (ha : OrderAt L σ ϖ M a p) (ha' : OrderAt L σ ϖ M' a' p) : a * M' = a' * M :=
  OrderAt.unique h0 hϖ hp (ha.mul_nat M') (by rw [mul_comm M M']; exact ha'.mul_nat M)
end OrderAt
end GlobalTheory.CompanionTheory.Ar.Flat
