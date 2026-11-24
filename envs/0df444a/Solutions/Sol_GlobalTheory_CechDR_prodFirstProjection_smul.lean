-- Prove2me | solution 1 for GlobalTheory.CechDR.prodFirstProjection_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:34.807059+00:00
-- url     : https://prove2.me/submissions/47e1562f-98ae-41ca-85ab-19771027f855

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
variable {T T' : C'}
namespace GlobalTheory.CechDR
theorem _root_.solution (b : F.obj (m.G.obj T)) (ω : Ω[F.obj (m.G.obj T)⁄R]) :
    q1 m T (b • ω) = m.α T b • q1 m T ω := (semiHom_coef m T).oneFormMap_smul_semilinear b ω
end GlobalTheory.CechDR
