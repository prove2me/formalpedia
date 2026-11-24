-- Prove2me | solution 1 for GlobalTheory.CechDR.cupHyp_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:37:39.730057+00:00
-- url     : https://prove2.me/submissions/45700751-d4df-4c6a-a648-fddf84e1bca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)
variable {F}
variable (F)
namespace GlobalTheory.CechDR
theorem _root_.solution (a b : cechDeRhamTotalCocyclesOne F) : cupHyp F (Hyp1.mk F a) (Hyp1.mk F b) = Hyp2.mk F (cupZZ F a b) := rfl
end GlobalTheory.CechDR
