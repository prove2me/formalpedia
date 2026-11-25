-- Prove2me | solution 1 for GlobalTheory.PDivGroup.pairing_tateMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:11.511+00:00
-- url     : https://prove2.me/submissions/5a4ccdfb-0d08-4236-b3a0-71386febd3fd

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
variable {B : Type} [CommRing B] [Algebra O B]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (f : G ⟶ H) (t : G.TateOver B) (χ : H.dual.Tate) :
    pairing H B (tateMap G H B f t) χ = pairing G B t (tateMap _ _ O (dualHom G H f) χ) := by
  rw [pairing_apply, pairing_apply, charHom_tateMap, tateMap_comp]
end GlobalTheory.PDivGroup
