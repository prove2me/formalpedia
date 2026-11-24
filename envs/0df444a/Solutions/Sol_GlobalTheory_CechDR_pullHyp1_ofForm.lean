-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHyp1_ofForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:38:45.695826+00:00
-- url     : https://prove2.me/submissions/7ac1f84a-1ef3-4e41-9d0c-85d8fc5aae7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor

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
theorem _root_.solution (ω : Closed1 F) : pullHyp1 m (ofForm F ω) = ofForm F' (pullClosed1 m ω) :=
  congrArg (Hyp1.mk F') (Subtype.ext (Tot1.ext (fun _ _ _ ↦ map_zero _) fun _ ↦ rfl))
end GlobalTheory.CechDR
