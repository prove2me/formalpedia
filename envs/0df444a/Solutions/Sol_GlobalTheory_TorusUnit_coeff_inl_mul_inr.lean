-- Prove2me | solution 1 for GlobalTheory.TorusUnit.coeff_inl_mul_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:18.360925+00:00
-- url     : https://prove2.me/submissions/b2a0df0a-e745-4c4f-a667-6ee88d4f6a58

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
theorem _root_.solution (u v : AddMonoidAlgebra A X) (x y : X) :
    (AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inl X X) u *
      AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inr X X) v).coeff (x, y) =
      u.coeff x * v.coeff y := by
  classical
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, add_mul]; simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb, add_mul]
  | single a r =>
    induction v using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add c d hc hd => rw [map_add, mul_add]; simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hc, hd, mul_add]
    | single b s =>
      simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h1 : a = x <;> by_cases h2 : b = y <;> simp [h1, h2]
end GlobalTheory.TorusUnit
