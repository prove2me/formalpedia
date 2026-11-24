-- Prove2me | solution 1 for GlobalTheory.TorusUnit.IsCharNear.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:02.654868+00:00
-- url     : https://prove2.me/submissions/ee3dd2c2-ba42-4043-860a-c45a44cf5137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_eq_of_single_one_eq
import Theorems.Thm_GlobalTheory_TorusUnit_IsCharNear_residueField
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
namespace IsCharNear
theorem _root_.solution {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ χ' : X} {p : Y.left}
    (h : IsCharNear ρ χ p) (h' : IsCharNear ρ χ' p) : χ = χ' :=
  eq_of_single_one_eq (h.residueField.symm.trans h'.residueField)
end IsCharNear
end GlobalTheory.TorusUnit
