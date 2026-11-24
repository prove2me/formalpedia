-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction.IsGtTangent.isTangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:33.254398+00:00
-- url     : https://prove2.me/submissions/cc488875-6aac-41d0-a6f1-82709b548fb9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_LieLiftsTangentReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj
namespace GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
namespace IsGtTangent
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ν : GtPt D (epsR R)}
    (h : IsGtTangent ν) : IsTangent ν.b := h.1
end IsGtTangent
end GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
