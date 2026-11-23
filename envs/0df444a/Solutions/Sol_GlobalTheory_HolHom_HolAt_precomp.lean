-- Prove2me | solution 1 for GlobalTheory.HolHom.HolAt.precomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:29.759558+00:00
-- url     : https://prove2.me/submissions/63c1fb28-dcd7-4bb9-be67-a93e824de830

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp

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
namespace HolAt
theorem _root_.solution {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V'] {c : V → (Sp ℂ ⟶ X)} {k : V' → V} {z : V'}
    (h : HolAt c (k z)) (hk : DifferentiableAt ℂ k z) : HolAt (fun t => c (k t)) z :=
  fun U hU => ⟨hk.continuousAt.eventually (h U hU).1, fun f => ((h U hU).2 f).comp z hk⟩
end HolAt
end GlobalTheory.HolHom
