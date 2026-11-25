-- Prove2me | solution 1 for GlobalTheory.RosatiCube.rosati_cubical_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:26.126176+00:00
-- url     : https://prove2.me/submissions/08443075-fcb1-4306-a7d2-8fb332bae112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RosatiCubicalAdditive
import Theorems.Thm_GlobalTheory_RosatiCube_ros_add_of_surj
import Theorems.Thm_GlobalTheory_RosatiCube_ros_sum_of_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RosatiCube
open ReciprocityTheory.ChartRestriction.G.DVR
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable {L : LB A.left}
variable {Lr : RigLB A} (c : CubicalStr A Lr)
namespace GlobalTheory.RosatiCube
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, (u a).IsGen ∧ LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ (u a) (zero2 G)) (LB.oneGen Lr.L)) → ∀ (T : Over S) (z : T.left) (J), Good Lr.L z J → (∀ (a : O) (x x' y : T ⟶ G), val₂ (u a) z J (x * x') y * cubV c z J x x' (y ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) (x' ≫ act.act a) y * (val₂ (u a) z J x y * val₂ (u a) z J x' y)) ∧ (∀ (a : O) (x y y' : T ⟶ G), val₂ (u a) z J x (y * y') * cubV c z J x (y ≫ act.act (star a)) (y' ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) y y' * (val₂ (u a) z J x y * val₂ (u a) z J x y')) ∧ (∀ (a b : O) (x y : T ⟶ G), val₂ (u (a + b)) z J x y * cubV c z J x (y ≫ act.act (star a)) (y ≫ act.act (star b)) = cubV c z J (x ≫ act.act a) (x ≫ act.act b) y * (val₂ (u a) z J x y * val₂ (u b) z J x y)) := by
  intro S G _ _ s₂ s₃ Lr c O _ _ act u hu T z J hJ
  refine ⟨fun a x x' y => ?_, fun a x y y' => ?_, fun a b x y => ?_⟩
  · have := act.hom a
    have := act.hom (star a)
    exact (ros_add_of_surj c s₃ _ _ (u a) (hu a).1 (hu a).2 hJ x x' y).1
  · have := act.hom a
    have := act.hom (star a)
    exact (ros_add_of_surj c s₃ _ _ (u a) (hu a).1 (hu a).2 hJ y y' x).2
  · exact ros_sum_of_surj c s₂ (act.add a b) (by rw [star_add, act.add]) (hu (a + b)) (hu a) (hu b) hJ x y
end GlobalTheory.RosatiCube
