-- Prove2me | solution 1 for GlobalTheory.CechDR.Hyp1.mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:37:30.191796+00:00
-- url     : https://prove2.me/submissions/8046c200-01ee-4adc-8a8e-422add4a8231

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
namespace Hyp1
theorem _root_.solution {c c' : cechDeRhamTotalCocyclesOne F} : Hyp1.mk F c = Hyp1.mk F c' ↔ ∃ g, dTot0 F g = c.1 - c'.1 := by
  rw [← sub_eq_zero, ← map_sub, Hyp1.mk_eq_zero]
  rfl
end Hyp1
end GlobalTheory.CechDR
