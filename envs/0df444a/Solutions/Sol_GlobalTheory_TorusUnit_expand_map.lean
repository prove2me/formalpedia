-- Prove2me | solution 1 for GlobalTheory.TorusUnit.expand_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:04:23.08381+00:00
-- url     : https://prove2.me/submissions/22a79145-26c7-44fa-b10c-e5ce0d56ffd0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_value_comp
import Theorems.Thm_GlobalTheory_TorusUnit_fromInt_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext


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
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusUnit
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {Y : Over S}
attribute [local instance] TorusInj.zuAlg
namespace GlobalTheory.TorusUnit
theorem _root_.solution {R R' : CommRingCat.{0}} (g : R ⟶ R') (y : Spec R ⟶ Y.left)
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    (expand (Spec.map g ≫ y)).hom ρ = AddMonoidAlgebra.mapRingHom X g.hom ((expand y).hom ρ) := by
  have h := value_comp (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X g.hom) :
    grpAlg X R ⟶ grpAlg X R') (fromInt X R) (Spec.map (const X R) ≫ y)
  have h1 : fromInt X R ≫ (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X g.hom) :
      grpAlg X R ⟶ grpAlg X R') = fromInt X R' := by
    apply CommRingCat.hom_ext
    apply ringHom_ext_ZU
    intro x
    rw [CommRingCat.hom_comp, RingHom.comp_apply, fromInt_single, fromInt_single]
    simp
  have h2 : const X R ≫ (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X g.hom) :
      grpAlg X R ⟶ grpAlg X R') = g ≫ const X R' := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun r => ?_
    simp [const]
  rw [h1, ← Spec.map_comp_assoc, h2, Spec.map_comp, Category.assoc] at h
  exact (congrArg (fun f => f.hom ρ) h).symm
end GlobalTheory.TorusUnit
