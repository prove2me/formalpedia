-- Prove2me | solution 1 for GlobalTheory.BoxCompare.res_pullU_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:50.444793+00:00
-- url     : https://prove2.me/submissions/5b1b2176-a28e-4072-9cab-dc2e3ab9cb27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply

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
variable {X Y : Scheme.{0}}
namespace GlobalTheory.BoxCompare
theorem _root_.solution {U W : X.Opens} (h : W ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (h' : W ≤ U) (x : Γ(X, U)ˣ) :
    res h (pullU (𝟙 X) U x) = res h' x := by
  ext
  rfl
end GlobalTheory.BoxCompare
