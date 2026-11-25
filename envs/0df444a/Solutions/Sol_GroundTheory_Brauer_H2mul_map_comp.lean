-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.map_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:10.126184+00:00
-- url     : https://prove2.me/submissions/811b64d7-5406-494d-a5b0-2f4c80a47193

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v u' v'
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
open GroundTheory.Brauer.H2mul
variable {G M}
variable {G' : Type u'} {M' : Type v'} [Group G'] [CommGroup M'] [MulDistribMulAction G' M']
variable {N : Type v'} [CommGroup N] [MulDistribMulAction G N]
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution {P : Type*} [CommGroup P] [MulDistribMulAction G P] (φ : M →*[G] N)
    (ψ : N →*[G] P) : map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext x
  rfl
end GroundTheory.Brauer.H2mul
