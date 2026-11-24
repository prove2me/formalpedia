-- Prove2me | solution 1 for GlobalTheory.HolPeriods.isHolTo_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:18.676927+00:00
-- url     : https://prove2.me/submissions/cd4ede5a-d783-4a7e-a47e-41947d04fcb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolPeriods
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X : Scheme.{0}}
namespace GlobalTheory.HolPeriods
theorem _root_.solution {B : Set V} {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (hy : ∀ b ∈ B, y' b = y b) :
    IsHolTo B y' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hy b h1 ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hy b h1).symm ▸ h2⟩
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [hy b hb.1]⟩
end GlobalTheory.HolPeriods
