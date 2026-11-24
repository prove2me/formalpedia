-- Prove2me | solution 1 for GlobalTheory.HolHom.isDerivAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:01:57.012115+00:00
-- url     : https://prove2.me/submissions/bc3260b1-40dc-477b-8159-d32c94a9007e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt_lift

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
variable {y : Sp ℂ ⟶ S}
namespace GlobalTheory.HolHom
theorem _root_.solution {a b : V → (Over.mk y ⟶ G)} {z w : V}
    (ha : HolAt (fun t => (a t).left) z) (hb : HolAt (fun t => (b t).left) z) {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt (fun t => (a t).left) z w v.left) (hv' : IsDerivAt (fun t => (b t).left) z w v'.left) :
    IsDerivAt (fun t => (a t * b t).left) z w (v * v').left :=
  (isDerivAt_lift ha hb hv hv').comp μ[G].left
end GlobalTheory.HolHom
