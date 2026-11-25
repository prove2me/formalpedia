-- Prove2me | solution 1 for GlobalTheory.PDivGroup.hodgeTate_tateMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:20:59.167464+00:00
-- url     : https://prove2.me/submissions/69d2d870-27b6-46d2-aa59-8f8fa5cd5ac5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDivGroup_omegaDualMap_apply
import Theorems.Thm_GlobalTheory_PDivGroup_dlog_tateMap
import Theorems.Thm_GlobalTheory_PDivGroup_hodgeTate_apply

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
theorem _root_.solution (f : G ⟶ H) (t : G.Tate) :
    hodgeTate H (tateMap G H O f t) = omegaDualMap G H f (hodgeTate G t) := by
  rw [hodgeTate_apply, hodgeTate_apply, omegaDualMap_apply, ← dlog_tateMap, ← tateMap_comp,
    ← tateMap_comp, bidual_hom_dualHom_dualHom]
end GlobalTheory.PDivGroup
