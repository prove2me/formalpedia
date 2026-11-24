-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHyp1_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:36:37.301519+00:00
-- url     : https://prove2.me/submissions/106f2395-0d0d-4201-9cf2-dab389ee695d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_comp_oneFormMap


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
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')
namespace GlobalTheory.CechDR
theorem _root_.solution (n : CoefMap τ F' F'') (c : Hyp1 F) :
    pullHyp1 (m.comp n) c = pullHyp1 n (pullHyp1 m c) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F c
  exact congrArg (Hyp1.mk F'') (Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl)
    fun _ ↦ (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _).symm))
end GlobalTheory.CechDR
