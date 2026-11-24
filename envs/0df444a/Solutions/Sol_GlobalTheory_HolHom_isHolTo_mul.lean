-- Prove2me | solution 1 for GlobalTheory.HolHom.isHolTo_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:03.857803+00:00
-- url     : https://prove2.me/submissions/17cfb269-1ba2-44ec-8861-8789de2e1092

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isOpen_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_of_holAt
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_holAt_lift

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}}
variable {G : Over S} [GrpObj G]
namespace GlobalTheory.HolHom
theorem _root_.solution {B : Set V} {y : V → (Sp ℂ ⟶ S)} {a b : ∀ t, Over.mk (y t) ⟶ G}
    (ha : IsHolTo B (fun t => (a t).left)) (hb : IsHolTo B (fun t => (b t).left)) :
    IsHolTo B (fun t => (a t * b t).left) := by
  refine isHolTo_of_holAt (isOpen_of_isHolTo ha) fun z hz => ?_
  have := (holAt_lift (P := fun t => Over.mk (y t)) (fun _ => 𝟙 (Sp ℂ)) (a := a) (b := b) (z := z)
    (by simpa using holAt_of_isHolTo ha hz) (by simpa using holAt_of_isHolTo hb hz)).comp μ[G].left
  simpa [Hom.mul_def] using this
end GlobalTheory.HolHom
