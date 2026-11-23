-- Prove2me | solution 1 for GlobalTheory.HolPeriods.isHolTo_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:48.580994+00:00
-- url     : https://prove2.me/submissions/09b0bf0b-0462-4adf-b5f6-8bddc95da35d

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
theorem _root_.solution {B : Set V} {C : Set W} {y : V → (Sp ℂ ⟶ X)} {φ : W → V} (h : IsHolTo B y)
    (hC : IsOpen C) (hφ : DifferentiableOn ℂ φ C) (hm : Set.MapsTo φ C B) :
    IsHolTo C (fun c => y (φ c)) := by
  intro U f
  have hs : {c ∈ C | ⊤ ≤ y (φ c) ⁻¹ᵁ U} = C ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext c
    exact ⟨fun hc => ⟨hc.1, hm hc.1, hc.2⟩, fun hc => ⟨hc.1, hc.2.2⟩⟩
  refine ⟨?_, ?_⟩
  · rw [hs]; exact hφ.continuousOn.isOpen_inter_preimage hC (h U f).1
  · exact (h U f).2.comp (hφ.mono fun c hc => hc.1) fun c hc => ⟨hm hc.1, hc.2⟩
end GlobalTheory.HolPeriods
