-- Prove2me | solution 1 for GroundTheory.Global.cycSubOne_cycNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:31.516156+00:00
-- url     : https://prove2.me/submissions/a200dc61-55cc-4800-a3bd-2ea52e94ba93

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (ρ : Representation k G V) (σ : G) (x : V) :
    cycSubOne ρ σ (cycNorm ρ x) = 0 := by
  rw [cycSubOne_apply, sub_eq_zero]
  exact ρ.self_norm_apply σ x
end GroundTheory.Global
