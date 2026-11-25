-- Prove2me | solution 1 for GlobalTheory.PDivGroup.dlog_tateMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:07:00.194186+00:00
-- url     : https://prove2.me/submissions/252aa912-7723-46f8-8131-21253c62af18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDivGroup_charHom_tateMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable {G H : PDivGroup p O}
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (f : G ⟶ H) (χ : H.dual.Tate) :
    dlog G (tateMap _ _ O (dualHom G H f) χ) = omegaMap G H f (dlog H χ) := by
  rw [dlog_eq_omegaMap, dlog_eq_omegaMap, charHom_tateMap, omegaMap_comp, LinearMap.comp_apply]
end GlobalTheory.PDivGroup
