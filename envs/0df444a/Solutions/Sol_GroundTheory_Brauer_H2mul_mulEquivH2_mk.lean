-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.mulEquivH2_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:28.792424+00:00
-- url     : https://prove2.me/submissions/619a7805-3e4b-485c-a813-e682490ae9ef

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
variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
open GroundTheory.Brauer.H2mul
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution (c : mulCocycles₂ G M) :
    mulEquivH2 (mk G M c) = Multiplicative.ofAdd (H2π (Rep.ofMulDistribMulAction G M)
      (cocyclesOfIsMulCocycle₂ (f := (c : G × G → M)) c.2)) :=
  rfl
end GroundTheory.Brauer.H2mul
