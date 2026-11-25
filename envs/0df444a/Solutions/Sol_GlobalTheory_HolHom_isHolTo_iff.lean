-- Prove2me | solution 1 for GlobalTheory.HolHom.isHolTo_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:04.115833+00:00
-- url     : https://prove2.me/submissions/994546d3-9b28-47bd-a8c2-5ed5fc2a5642

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isOpen_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_of_holAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {B : Set V} {c : V → (Sp ℂ ⟶ X)} : IsHolTo B c ↔ IsOpen B ∧ ∀ z ∈ B, HolAt c z :=
  ⟨fun h => ⟨isOpen_of_isHolTo h, fun _ hz => holAt_of_isHolTo h hz⟩, fun h => isHolTo_of_holAt h.1 h.2⟩
end GlobalTheory.HolHom
