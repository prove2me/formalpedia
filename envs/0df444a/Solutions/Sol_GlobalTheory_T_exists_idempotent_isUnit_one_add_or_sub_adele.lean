-- Prove2me | solution 1 for GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:03.932312+00:00
-- url     : https://prove2.me/submissions/bda74e67-e0d8-4ffc-a7cd-6aa4d6182e08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdele
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdeleStatement
import Theorems.Thm_GlobalTheory_AdIdem_exists_idem_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F), ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  first | exact @GlobalTheory.AdIdem.exists_idem_isUnit | exact GlobalTheory.AdIdem.exists_idem_isUnit | (intros; apply GlobalTheory.AdIdem.exists_idem_isUnit <;> assumption)
end _root_.GlobalTheory.T
