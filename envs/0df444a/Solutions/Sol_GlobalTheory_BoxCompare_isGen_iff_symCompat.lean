-- Prove2me | solution 1 for GlobalTheory.BoxCompare.isGen_iff_symCompat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:29.284259+00:00
-- url     : https://prove2.me/submissions/14bd7a8d-2625-4b47-acc2-40ca1bec01d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
import Theorems.Thm_GlobalTheory_BoxCompare_res_lcg_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxCompare
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LB
open GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum (PowerDatum IsNormSymm)
variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X)
namespace GlobalTheory.BoxCompare
theorem _root_.solution (sy : SymGen L f) : sy.IsGen ↔ SymCompat L f sy := by
  rw [isGen_iff]
  refine ⟨fun H a b a' b' W h₁ h₂ h₃ h₄ => ?_, fun H i j => ?_⟩
  · have key := congrArg (res (le_inf h₃ h₄)) (H ![a, b] ![a', b'])
    rw [map_mul, res_res, res_res, res_lcg_two L f _ _ _ h₁ h₂] at key
    exact key
  · obtain ⟨a, b, rfl⟩ : ∃ a b, i = ![a, b] := ⟨i 0, i 1, by funext k; fin_cases k <;> rfl⟩
    obtain ⟨a', b', rfl⟩ : ∃ a b, j = ![a, b] := ⟨j 0, j 1, by funext k; fin_cases k <;> rfl⟩
    have h₁ := wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] ![a, b] ![a', b'] 0
    have h₂ := wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] ![a, b] ![a', b'] 1
    rw [← res_self le_rfl (lcg _ _ _ _ _), res_lcg_two L f _ _ _ h₁ h₂]
    exact H a b a' b' _ h₁ h₂ _ _
end GlobalTheory.BoxCompare
