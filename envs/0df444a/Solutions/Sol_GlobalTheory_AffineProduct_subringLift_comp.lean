-- Prove2me | solution 1 for GlobalTheory.AffineProduct.subringLift_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:42.786533+00:00
-- url     : https://prove2.me/submissions/b202afcd-adfc-4894-8921-d54e84a314dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineAndGeneratedOfWideProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AffineProduct
namespace GlobalTheory.AffineProduct
theorem _root_.solution {Y X X' : Scheme.{0}} [IsAffine X] [IsAffine X'] (B : Subring Γ(Y, ⊤))
    (f : Y ⟶ X) (h : ∀ a, f.appTop.hom a ∈ B) (e : X ⟶ X') (g : Y ⟶ X') (w : f ≫ e = g)
    (h' : ∀ a, g.appTop.hom a ∈ B) :
    subringLift B f h ≫ e = subringLift B g h' := by
  subst w
  have e' : CommRingCat.ofHom ((f ≫ e).appTop.hom.codRestrict B h')
      = e.appTop ≫ CommRingCat.ofHom (f.appTop.hom.codRestrict B h) := by
    ext a; rfl
  simp only [subringLift, Category.assoc]
  rw [e', Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality]
end GlobalTheory.AffineProduct
