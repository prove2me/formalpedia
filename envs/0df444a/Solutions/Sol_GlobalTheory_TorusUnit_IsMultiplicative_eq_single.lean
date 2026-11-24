-- Prove2me | solution 1 for GlobalTheory.TorusUnit.IsMultiplicative.eq_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:10.454985+00:00
-- url     : https://prove2.me/submissions/c75e6c29-6200-4962-9d00-f7e864bf8250

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_coeff_inl_mul_inr
import Theorems.Thm_GlobalTheory_TorusUnit_coeff_diag
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
namespace IsMultiplicative
theorem _root_.solution {u : AddMonoidAlgebra A X} (hu : IsMultiplicative u) {x : X}
    (hx : IsUnit (u.coeff x)) : u = single x 1 := by
  classical
  have key : ∀ y, (if x = y then u.coeff x else 0) = u.coeff x * u.coeff y := fun y => by
    rw [← coeff_diag, ← coeff_inl_mul_inr, hu]
  ext y
  have := key y
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  apply hx.mul_left_cancel
  rw [← this]
  split_ifs <;> simp
end IsMultiplicative
end GlobalTheory.TorusUnit
