-- Prove2me | solution 1 for GlobalTheory.WeilMul.prod_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:46.521491+00:00
-- url     : https://prove2.me/submissions/d1892b05-1cde-4c89-ad10-c6894b49360c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_GlobalTheory_WeilMul_lift_translPt

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilMul
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilMul
theorem _root_.solution {T T' : Over S} (x : T ⟶ A) (t : T' ⟶ T) (a : T' ⟶ A) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t a).left ≫ ![(snd T A).left, (translPt A x).left] i) ^ (![k, -k] i) =
      h a.left ^ k * h ((t ≫ x) * a).left ^ (-k) := by
  rw [Fin.prod_univ_two]
  show h (lift t a ≫ snd T A).left ^ k * h (lift t a ≫ translPt A x).left ^ (-k) = _
  rw [lift_snd, lift_translPt]
end GlobalTheory.WeilMul
