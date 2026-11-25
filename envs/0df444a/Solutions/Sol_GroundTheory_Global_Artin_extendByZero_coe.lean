-- Prove2me | solution 1 for GroundTheory.Global.Artin.extendByZero_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:55:31.667021+00:00
-- url     : https://prove2.me/submissions/0d247728-c3a1-44d2-98fb-551696968eb3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
namespace GroundTheory.Global.Artin
theorem _root_.solution (H : Subgroup G) (f : H → ℂ) (h : H) : extendByZero H f h = f h :=
  extendByZero_of_mem H f h.2
end GroundTheory.Global.Artin
