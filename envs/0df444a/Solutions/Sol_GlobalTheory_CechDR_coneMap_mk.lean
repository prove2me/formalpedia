-- Prove2me | solution 1 for GlobalTheory.CechDR.coneMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:39:42.061645+00:00
-- url     : https://prove2.me/submissions/c8488d05-0ce7-4c51-a4b7-77f9b04321e7

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
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)
namespace GlobalTheory.CechDR
theorem _root_.solution (ω : LinearMap.ker (dOne R B)) :
    coneMap e he (Submodule.Quotient.mk ω) = ofForm F (coneForm e he ω) := rfl
end GlobalTheory.CechDR
