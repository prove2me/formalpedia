-- Prove2me | solution 1 for GlobalTheory.AffineProduct.toSpecSubring_subringLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:30.162412+00:00
-- url     : https://prove2.me/submissions/03ef0cce-cbf8-4064-a87d-22918b73be46

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
theorem _root_.solution {Y X : Scheme.{0}} [IsAffine X] (B : Subring Γ(Y, ⊤))
    (f : Y ⟶ X) (h : ∀ a, f.appTop.hom a ∈ B) :
    toSpecSubring B ≫ subringLift B f h = f := by
  have e : CommRingCat.ofHom (f.appTop.hom.codRestrict B h) ≫ CommRingCat.ofHom B.subtype
      = f.appTop := by
    ext a; rfl
  simp only [toSpecSubring, subringLift, Category.assoc]
  rw [← Spec.map_comp_assoc, e, ← Scheme.toSpecΓ_naturality_assoc]
  simp [← Scheme.isoSpec_hom]
end GlobalTheory.AffineProduct
