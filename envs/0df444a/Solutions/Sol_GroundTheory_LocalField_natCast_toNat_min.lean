-- Prove2me | solution 1 for GroundTheory.LocalField.natCast_toNat_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:28.417951+00:00
-- url     : https://prove2.me/submissions/da8c847b-d8e9-420b-bd00-389bdd23dc99

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℕ∞) (m : ℕ) : (((min n m).toNat : ℕ) : ℕ∞) = min n m :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top m) (min_le_right _ _))
end GroundTheory.LocalField
