-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.mapPair_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:44:26.667999+00:00
-- url     : https://prove2.me/submissions/61ddafd9-b35a-4ee4-a105-d97cf0df12b9

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
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution : mapPair (MonoidHom.id G) (MonoidHom.id M) (fun _ _ => rfl) =
    MonoidHom.id (H2mul G M) := by
  ext x
  rfl
end GroundTheory.Brauer.H2mul
