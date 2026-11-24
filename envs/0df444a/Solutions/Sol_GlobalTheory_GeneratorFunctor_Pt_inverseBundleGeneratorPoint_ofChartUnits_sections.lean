-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.Pt.inverseBundleGeneratorPoint_ofChartUnits_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:24:10.275816+00:00
-- url     : https://prove2.me/submissions/113f18d2-5ff9-4193-9a8b-ee63e01f9442

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
import Theorems.Thm_GlobalTheory_GeneratorFunctor_pb_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_g_self


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
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
variable {B : Scheme.{0}} {κ : Type} (N : κ → LB B)
variable {N}
namespace GlobalTheory.GeneratorFunctor
namespace Pt
theorem _root_.solution (hN : ∀ k, (N k).IsLB) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hb : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (v : κ → Γ(Z, ⊤)ˣ) (k)
    {T : Scheme.{0}} (a : T ⟶ Z) (h) :
    (pb a _ ⊤ h ((Pt.ofChart hN b j hb v).s k (j k))).val = a.appTop.hom (v k).val := by
  have := LB.pull_g_self (hN k) b (j k) (W := b ⁻¹ᵁ (N k).U (j k)) (le_inf le_rfl le_rfl)
  rw [res_eq_pb, pullU_eq_pb, pb_id_comp] at this
  change (pb a (b ⁻¹ᵁ (N k).U (j k)) ⊤ h (pb _ _ _ _ _ * pb _ _ _ _ _)).val = _
  rw [this, _root_.one_mul, pb_comp_id, pb_top]
end Pt
end GlobalTheory.GeneratorFunctor
