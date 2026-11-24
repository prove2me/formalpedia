-- Prove2me | solution 1 for GlobalTheory.TorusUnit.value_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:23.247811+00:00
-- url     : https://prove2.me/submissions/bf6a24ea-430b-472e-b849-0c7ec16a2bce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_prodPoint_fst
import Theorems.Thm_GlobalTheory_TorusUnit_charUnit_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_charUnit_val


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
theorem _root_.solution {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) (χ : X) :
    (value φ y).hom ((fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val) =
      φ.hom (single χ 1) := by
  have : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ (torusFst S X).appTop ≫
      (fst (splitTorus S X) Y).left.appTop ≫ value φ y = φ := by
    rw [value, ← Scheme.Hom.comp_appTop_assoc, ← Scheme.Hom.comp_appTop_assoc,
      prodPoint_fst, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [charUnit_val]
  exact congrArg (fun f => f.hom (single χ 1)) this
end GlobalTheory.TorusUnit
