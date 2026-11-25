-- Prove2me | solution 1 for GlobalTheory.PDivGroup.charHom_tateMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:29:32.524077+00:00
-- url     : https://prove2.me/submissions/d969999f-b9f2-424c-9ee4-324b5e6f2cf1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective

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
    charHom G (tateMap _ _ O (dualHom G H f) χ) = f ≫ charHom H χ :=
  hom_mu_ext fun n => by
    rw [charHom_app_muT, charElem_tateMap, comp_app, BialgHom.comp_apply, charHom_app_muT]
end GlobalTheory.PDivGroup
