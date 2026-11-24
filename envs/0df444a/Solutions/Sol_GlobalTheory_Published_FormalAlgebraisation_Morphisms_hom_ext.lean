-- Prove2me | solution 1 for GlobalTheory.Published.FormalAlgebraisation.Morphisms.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:54:09.502153+00:00
-- url     : https://prove2.me/submissions/cd1ce001-8a11-4798-9fbc-67aae1dd8c36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Theorems.Thm_GlobalTheory_Published_FormalAlgebraisation_Morphisms_existsUnique_thick

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
    {X Z : Over (Spec (CommRingCat.of R))} [IsProper X.hom] [IsProper Z.hom] {g g' : X ⟶ Z}
    (h : ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = pullback.fst X.hom (thick R I e) ≫ g'.left) :
    g = g' :=
  (H.existsUnique_thick hI X Z (fun e => pullback.fst X.hom (thick R I e) ≫ g'.left)
    (fun e => by rw [Category.assoc, Over.w])
    (fun e => by
      rw [← Category.assoc]
      exact congrArg (· ≫ g'.left) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)))).unique
    h (fun _ => rfl)
end Morphisms
end GlobalTheory.Published.FormalAlgebraisation
