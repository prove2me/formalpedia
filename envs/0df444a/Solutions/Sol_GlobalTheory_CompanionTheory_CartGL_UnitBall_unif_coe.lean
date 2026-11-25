-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.UnitBall.unif_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:59:48.628232+00:00
-- url     : https://prove2.me/submissions/b7e5834e-64f8-4c8d-adab-e1b0542dac3e

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
theorem _root_.solution (hp : IsUnif p) : ((unif hp : ball L) : L) = p := rfl
end GlobalTheory.CompanionTheory.CartGL.UnitBall
