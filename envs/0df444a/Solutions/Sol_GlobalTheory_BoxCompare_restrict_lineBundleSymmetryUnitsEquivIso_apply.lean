-- Prove2me | solution 1 for GlobalTheory.BoxCompare.restrict_lineBundleSymmetryUnitsEquivIso_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:43.980093+00:00
-- url     : https://prove2.me/submissions/1f044dd0-5169-4282-a1d7-61af0433a2d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
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
theorem _root_.solution (sy : SymGen L f) (p : (PUnit.{1} → L.ι) × L.ι) {W : X.Opens}
    (h : W ≤ wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2)
    (h' : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![p.1 ⟨⟩, p.2]) :
    res h ((symEquiv L f sy).s p) = res h' (ts sy ![p.1 ⟨⟩, p.2]) :=
  res_res (toIso_le L f p) h _
end GlobalTheory.BoxCompare
