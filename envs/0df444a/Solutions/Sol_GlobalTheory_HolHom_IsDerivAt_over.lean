-- Prove2me | solution 1 for GlobalTheory.HolHom.IsDerivAt.over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:08:40.273796+00:00
-- url     : https://prove2.me/submissions/a78b834a-9c2c-4db8-943c-1cbf6a3777ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_unique
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt_const

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
omit [GrpObj G]
namespace GlobalTheory.HolHom
namespace IsDerivAt
theorem _root_.solution {a : V → (Over.mk y ⟶ G)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ G.left}
    (h : IsDerivAt (fun t => (a t).left) z w v) : v ≫ G.hom = (epsPt y).hom := by
  have h1 := h.comp G.hom
  have h2 : (fun t => (a t).left ≫ G.hom) = fun _ => y := funext fun t => Over.w (a t)
  exact (h2 ▸ h1).unique (isDerivAt_const y z w)
end IsDerivAt
end GlobalTheory.HolHom
