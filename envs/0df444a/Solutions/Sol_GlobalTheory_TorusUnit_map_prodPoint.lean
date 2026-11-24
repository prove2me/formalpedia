-- Prove2me | solution 1 for GlobalTheory.TorusUnit.map_prodPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:21.158702+00:00
-- url     : https://prove2.me/submissions/74637daf-560f-477b-8412-b0a62243281c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_prodPoint_fst
import Theorems.Thm_GlobalTheory_TorusUnit_prodPoint_snd
import Theorems.Thm_GlobalTheory_TorusUnit_isPullback_prod
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
namespace GlobalTheory.TorusUnit
theorem _root_.solution {R R' : CommRingCat.{0}} (g : R ⟶ R') (φ : torusRing ZU X ⟶ R)
    (y : Spec R ⟶ Y.left) :
    Spec.map g ≫ prodPoint φ y = prodPoint (φ ≫ g) (Spec.map g ≫ y) := by
  apply (isPullback_prod X Y).hom_ext
  · rw [Category.assoc, prodPoint_fst, prodPoint_fst, Spec.map_comp]
  · rw [Category.assoc, prodPoint_snd, prodPoint_snd]
end GlobalTheory.TorusUnit
