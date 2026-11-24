-- Prove2me | solution 1 for GlobalTheory.CechDR.cechDeRhamTotalCocyclesTwo.two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:37:44.557909+00:00
-- url     : https://prove2.me/submissions/0333b4db-03cb-49cc-9cbb-0a0e8523d636

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
variable {T T' T'' T''' : C}
namespace GlobalTheory.CechDR
namespace cechDeRhamTotalCocyclesTwo
theorem _root_.solution (c : cechDeRhamTotalCocyclesTwo F) (φ : T ⟶ T') :
    c.1.2.2 T' = pOm F 2 φ (c.1.2.2 T) + dOne R _ (c.1.2.1 T T' φ) := (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).2.2.1 φ
end cechDeRhamTotalCocyclesTwo
end GlobalTheory.CechDR
