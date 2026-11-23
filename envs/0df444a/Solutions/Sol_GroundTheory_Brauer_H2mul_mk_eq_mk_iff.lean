-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:43.869799+00:00
-- url     : https://prove2.me/submissions/42fb55d7-bf76-4c16-a289-1ab232a7ab59

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
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution (f f' : mulCocycles₂ G M) :
    mk G M f = mk G M f' ↔ IsMulCoboundary₂ ((f : G × G → M) / (f' : G × G → M)) := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff]
  rfl
end GroundTheory.Brauer.H2mul
