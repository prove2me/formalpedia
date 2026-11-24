-- Prove2me | solution 1 for GlobalTheory.TorusUnit.isPullback_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:57.650828+00:00
-- url     : https://prove2.me/submissions/de6d7548-4859-46d6-82c0-31473500421b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_prodPoint_fst
import Theorems.Thm_GlobalTheory_TorusUnit_prodPoint_snd
import Theorems.Thm_GlobalTheory_TorusUnit_isPullback_prod
import Theorems.Thm_GlobalTheory_TorusUnit_isPushout_grpAlg
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
theorem _root_.solution {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    IsPullback (prodPoint (fromInt X R) (Spec.map (const X R) ≫ y)) (Spec.map (const X R))
      (snd (splitTorus S X) Y).left y := by
  have h0 : IsPushout (CommRingCat.ofHom (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)))
      (CommRingCat.ofHom (algebraMap ZU.{0} R)) (fromInt X R) (const X R) :=
    isPushout_grpAlg R
  have h1 := isPullback_SpecMap_of_isPushout _ _ _ _ h0
  refine IsPullback.of_right ?_ (prodPoint_snd _ _) (isPullback_prod X Y)
  rw [prodPoint_fst]
  rw [show y ≫ Y.hom ≫ toZ S = Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} R)) from
    specULiftZIsTerminal.hom_ext _ _]
  exact h1
end GlobalTheory.TorusUnit
