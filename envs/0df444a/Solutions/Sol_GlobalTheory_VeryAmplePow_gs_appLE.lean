-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.gs_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:23.308266+00:00
-- url     : https://prove2.me/submissions/ad637bdd-8962-4ca8-a6a0-aba7a71e1036

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem

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
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z) (r : Z ⟶ Y) (z : Z') (U : Y.Opens) (V : Z.Opens)
    (hle : V ≤ r ⁻¹ᵁ U) (h : q z ∈ V) (a : Γ(Y, U)) :
    gs q z V ((r.appLE U V hle).hom a) = gs (q ≫ r) z U a :=
  (gs_res q z hle h _).trans (gs_pull q r z U (hle h) a)
end GlobalTheory.VeryAmplePow
