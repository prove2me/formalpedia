-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.gm_unitRes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:09.631427+00:00
-- url     : https://prove2.me/submissions/a1bdad50-33b4-48b0-88cf-7e3c5f39fea8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution {T : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) {Z : Scheme.{0}} (r : Z ⟶ V.toScheme) (z : Z) :
    gm r z ⊤ (unitRes V c) = gm (r ≫ V.ι) z ⊤ c := gm_pull r V.ι z ⊤ trivial c
end GlobalTheory.CommutatorPairing
