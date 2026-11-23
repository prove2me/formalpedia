-- Prove2me | solution 1 for GlobalTheory.MulSplit.dv_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:35.365821+00:00
-- url     : https://prove2.me/submissions/496420e9-42d5-4a93-847e-992933f0b262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {X Y B : Scheme.{0}} (L : LB X) (p : Y ⟶ B)
variable {L p}
variable {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.MulSplit
theorem _root_.solution (D : (Y ⟶ X) →₀ ℤ) : dv (fun k : D.support => k.1) (fun k => D k.1) = D :=
  (Finset.sum_coe_sort D.support (fun ψ => Finsupp.single ψ (D ψ))).trans D.sum_single
end GlobalTheory.MulSplit
