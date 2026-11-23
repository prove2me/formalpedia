-- Prove2me | solution 1 for GlobalTheory.WeilMul.val_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:16.989801+00:00
-- url     : https://prove2.me/submissions/8d6d2151-27e3-4e62-a435-8d40e86caa0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
theorem _root_.solution {T T' : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) (t : T' ⟶ overRes V) (a : T' ⟶ A)
    (z : T'.left) (J) :
    val (constGen A L (unitRes V c)) (lift t a).left z J = gm (t ≫ overResι V).left z ⊤ c := by
  have hm : (lift t a).left z ∈ LB.wchart L (PEmpty.elim : PEmpty → ((overRes V ⊗ A).left ⟶ A.left)) PEmpty.elim :=
    Set.mem_iInter.2 fun k => k.elim
  rw [val_of _ _ z J PEmpty.elim (fun k => k.elim)]
  refine (gm_res _ z le_top hm _).trans ((gm_pull (lift t a).left (fst (overRes V) A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]
  exact gm_pull t.left V.ι z ⊤ trivial c
end GlobalTheory.WeilMul
