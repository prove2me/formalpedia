-- Prove2me | solution 1 for GlobalTheory.HolHom.IsDerivAt.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:08.757789+00:00
-- url     : https://prove2.me/submissions/860db567-458e-43c1-8ff5-d9a95992c9b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_tangent_ext

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
namespace IsDerivAt
theorem _root_.solution {c : V → (Sp ℂ ⟶ X)} {z w : V} {v v' : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt c z w v)
    (h' : IsDerivAt c z w v') : v = v' :=
  tangent_ext h.1 h'.1 fun U hU f => (h.2 U hU f).trans (h'.2 U hU f).symm
end IsDerivAt
end GlobalTheory.HolHom
