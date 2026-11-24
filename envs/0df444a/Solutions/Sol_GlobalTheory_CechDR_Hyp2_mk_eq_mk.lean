-- Prove2me | solution 1 for GlobalTheory.CechDR.Hyp2.mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:37:33.306804+00:00
-- url     : https://prove2.me/submissions/edeabf07-ad9b-43c2-a83a-19ecf0eaf433

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
namespace GlobalTheory.CechDR
namespace Hyp2
theorem _root_.solution {c c' : cechDeRhamTotalCocyclesTwo F} : Hyp2.mk F c = Hyp2.mk F c' ↔ ∃ e, dTot1 F e = c.1 - c'.1 := by
  rw [← sub_eq_zero, ← map_sub, Hyp2.mk_eq_zero]
  rfl
end Hyp2
end GlobalTheory.CechDR
