-- Prove2me | solution 1 for GroundTheory.Global.Artin.extendByZero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:27.355362+00:00
-- url     : https://prove2.me/submissions/843707de-d222-4a37-b92e-14078ac880a7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey

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
theorem _root_.solution (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∉ H) :
    extendByZero H f g = 0 := by
  unfold extendByZero
  rw [dif_neg hg]
end GroundTheory.Global.Artin
