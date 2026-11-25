-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.UnitBall.norm_unif_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:58.574881+00:00
-- url     : https://prove2.me/submissions/74c3ec94-ea8e-4a22-bd5f-64ed18e4be5e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.UnitBall
variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
variable {L}
variable {p : Lˣ}
namespace GlobalTheory.CompanionTheory.CartGL.UnitBall
theorem _root_.solution (p : Lˣ) : 0 < ‖(p : L)‖ := norm_pos_iff.2 p.ne_zero
end GlobalTheory.CompanionTheory.CartGL.UnitBall
