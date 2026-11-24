-- Prove2me | solution 1 for GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:47.709733+00:00
-- url     : https://prove2.me/submissions/d7df4303-0cc8-474e-b7b6-9983b7c8ffa0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.FormalAlgebraisation
variable {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
namespace GlobalTheory.Published.FormalAlgebraisation
namespace Morphisms
theorem _root_.solution (H : Morphisms) (hI : IsAdicComplete I R)
    (X Z : Over (Spec (CommRingCat.of R))) [hX : IsProper X.hom] [hZ : IsProper Z.hom]
    (f : ∀ e, (thickObj R I e X).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst X.hom (thick R I e) ≫ X.hom)
    (hc : ∀ e, thickMap R I e X ≫ f (e + 1) = f e) :
    ∃! g : X ⟶ Z, ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = f e :=
  H R I hI X Z hX inferInstance inferInstance inferInstance (fun e => thickObj R I e X)
    (fun e => thickMap R I e X) (fun e => pullback.fst X.hom (thick R I e))
    (fun _ => IsPullback.of_hasPullback _ _)
    (fun _ => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) f
    (fun e => (hf e).trans pullback.condition) hc
end Morphisms
end GlobalTheory.Published.FormalAlgebraisation
