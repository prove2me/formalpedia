-- Prove2me | solution 1 for GlobalTheory.BoxCompare.res_lcg_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:42.76849+00:00
-- url     : https://prove2.me/submissions/11f1422c-d485-4c48-9261-252b1c501814

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
import Theorems.Thm_GlobalTheory_BoxCompare_res_pullU_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_lcg


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
theorem _root_.solution (i j : Fin 2 → L.ι) {W : X.Opens}
    (h : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] i ⊓ wchart L (K := Fin 2) ![f, 𝟙 X] j)
    (h₁ : W ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0))) (h₂ : W ≤ L.U (i 1) ⊓ L.U (j 1)) :
    res h (lcg L (K := Fin 2) ![f, 𝟙 X] ![1, -1] i j) =
      res h₁ (pullU f _ (L.g (i 0) (j 0))) * (res h₂ (L.g (i 1) (j 1)))⁻¹ := by
  rw [res_lcg, Fin.prod_univ_two]
  refine congrArg₂ (· * ·) (zpow_one _) ((zpow_neg_one _).trans (congrArg (·⁻¹) ?_))
  exact res_pullU_id _ _ _
end GlobalTheory.BoxCompare
