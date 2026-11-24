-- Prove2me | solution 1 for GlobalTheory.CechDR.pullTot2_cupTot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:21.514141+00:00
-- url     : https://prove2.me/submissions/beaff5c7-770e-41e2-93b3-3fa5176bad65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_prodFirstProjection_smul
import Theorems.Thm_GlobalTheory_CechDR_qOm_wedge
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



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
theorem _root_.solution (a b : Tot1 F) :
    pullTot2 m (cupTot F a b) = cupTot F' (pullTot1 m a) (pullTot1 m b) :=
  Tot2.ext (fun T T' T'' φ ψ ↦ by simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, cupTot_apply, pullTot1_f, map_mul, m.naturality])
    (fun T T' φ ↦ by simp only [pullTot2_a, cupTot_a, pullTot1_f, pullTot1_ω, map_sub, cechDeRhamCoefMapOneForms_naturality, prodFirstProjection_smul])
    fun T ↦ by simp only [pullTot2_η, cupTot_η, pullTot1_ω, qOm_wedge]
end GlobalTheory.CechDR
