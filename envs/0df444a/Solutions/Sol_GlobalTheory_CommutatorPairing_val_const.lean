-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.val_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:00.904827+00:00
-- url     : https://prove2.me/submissions/b794312b-f956-48c4-8855-6278c3518fd8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
omit [GrpObj A]
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution {T Z : Over S} (c : Γ(T.left, ⊤)ˣ) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J) :
    val (constGen A L c) (lift t a).left z J = gm t.left z ⊤ c := by
  have e : t.left = (lift t a).left ≫ (fst T A).left := by rw [← Over.comp_left, lift_fst]
  rw [e]
  exact (gm_res _ z le_top (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull _ (fst T A).left z ⊤ trivial c)
end GlobalTheory.CommutatorPairing
