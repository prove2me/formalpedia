-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.sval_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:44.329204+00:00
-- url     : https://prove2.me/submissions/730ef9e8-d721-456d-a5ca-5fa09d1a2052

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add


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
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution {k : ℤ} (v w : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) :
    secVal (SecM.toSec A (v + w)) r z J =
      secVal (SecM.toSec A v) r z J +
      secVal (SecM.toSec A w) r z J :=
  gs_add r z _ (hJ.mem _ r) _ _
end GlobalTheory.TorsionFixedAut
