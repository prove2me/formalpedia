-- Prove2me | solution 1 for GlobalTheory.PDivGroup.constHom_comp_charHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:06.252348+00:00
-- url     : https://prove2.me/submissions/7de1d014-0f4c-463a-b1ce-bc6804b9add4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDivGroup_constHom_tateMap

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
theorem _root_.solution (t : G.Tate) (χ : G.dual.Tate) :
    constHom G t ≫ charHom G χ = constHom (mu p O) (pairing G O t χ) :=
  (constHom_tateMap _ t).symm
end GlobalTheory.PDivGroup
