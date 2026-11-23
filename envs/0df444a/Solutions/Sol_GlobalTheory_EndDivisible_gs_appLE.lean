-- Prove2me | solution 1 for GlobalTheory.EndDivisible.gs_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:33.253287+00:00
-- url     : https://prove2.me/submissions/29275082-4ac6-4f35-8619-d04fefb6240b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeOfSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.EndDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace
namespace GlobalTheory.EndDivisible
theorem _root_.solution {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens)
    (hle : V ≤ r ⁻¹ᵁ U) (h : f z ∈ V) (a : Γ(X, U)) :
    gs f z V ((r.appLE U V hle).hom a) = gs (f ≫ r) z U a :=
  (gs_res f z hle h _).trans (gs_pull f r z U (hle h) a)
end GlobalTheory.EndDivisible
