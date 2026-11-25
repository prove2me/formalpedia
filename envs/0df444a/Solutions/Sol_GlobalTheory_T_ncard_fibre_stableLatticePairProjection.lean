-- Prove2me | solution 1 for GlobalTheory.T.ncard_fibre_stableLatticePairProjection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:44.862902+00:00
-- url     : https://prove2.me/submissions/bcfdf591-711f-495c-ba5d-aced99132530

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardFibreStableLatticePairProjection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardFibreStableLatticePairProjectionStatement
import Theorems.Thm_GlobalTheory_UnitLemma_ncard_fibre_latProj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ y : LatPair O E g₁ g₂, ((latProj O E g₁ g₂ ⁻¹' {y}).ncard : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  first | exact @GlobalTheory.UnitLemma.ncard_fibre_latProj | exact GlobalTheory.UnitLemma.ncard_fibre_latProj | (intros; apply GlobalTheory.UnitLemma.ncard_fibre_latProj <;> assumption)
end _root_.GlobalTheory.T
