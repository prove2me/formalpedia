-- Prove2me | solution 1 for GlobalTheory.WeilMul.val_pull_tv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:28.604782+00:00
-- url     : https://prove2.me/submissions/e9daa55d-9770-4736-b8d7-98f0beb570b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
theorem _root_.solution {T T₁ T' : Over S} (θ : ThetaGrp A L k T) (t : T₁ ⟶ T) (a : T₁ ⟶ A) (ρ : T' ⟶ T₁)
    {z : T'.left} {J} (hJ : Good L z J) :
    val (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (lift t a).left)
      ρ.left z J = tv θ (ρ ≫ t) (ρ ≫ a) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift]; rfl
end GlobalTheory.WeilMul
