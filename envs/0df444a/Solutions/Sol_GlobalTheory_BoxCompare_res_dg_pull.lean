-- Prove2me | solution 1 for GlobalTheory.BoxCompare.res_dg_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:40.944653+00:00
-- url     : https://prove2.me/submissions/1522612e-b266-4b40-bd93-ad39c695d2bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_dg
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
theorem _root_.solution (p q : (PUnit.{1} → L.ι) × L.ι) {W : X.Opens}
    (h : W ≤ wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2 ⊓
      (wchart L (fun _ : PUnit.{1} => f) q.1 ⊓ L.U q.2))
    (h₁ : W ≤ f ⁻¹ᵁ (L.U (p.1 ⟨⟩) ⊓ L.U (q.1 ⟨⟩))) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    res h (dg (L.pull f) L p q) =
      res h₁ (pullU f _ (L.g (p.1 ⟨⟩) (q.1 ⟨⟩))) * (res h₂ (L.g p.2 q.2))⁻¹ := by
  refine (res_dg (L.pull f) L p q h).trans (congrArg₂ (· * ·) ?_ rfl)
  exact (congrArg (res _) (lcg_pull L f p.1 q.1)).trans (res_res _ _ _)
end GlobalTheory.BoxCompare
