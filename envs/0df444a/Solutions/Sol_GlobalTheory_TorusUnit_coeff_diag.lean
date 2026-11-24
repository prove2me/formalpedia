-- Prove2me | solution 1 for GlobalTheory.TorusUnit.coeff_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:48:20.128801+00:00
-- url     : https://prove2.me/submissions/fb4eff1f-2425-4990-a602-a4135c03c64e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
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
variable {A X : Type} [CommRing A] [AddCommGroup X]
namespace GlobalTheory.TorusUnit
theorem _root_.solution (u : AddMonoidAlgebra A X) (x y : X) [Decidable (x = y)] :
    (AddMonoidAlgebra.mapDomainRingHom A ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) u).coeff
      (x, y) = if x = y then u.coeff x else 0 := by
  classical
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add]; simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb]
    split_ifs <;> simp
  | single a r =>
    simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h1 : a = x <;> by_cases h2 : x = y <;> simp [h1, h2]
    all_goals aesop
end GlobalTheory.TorusUnit
