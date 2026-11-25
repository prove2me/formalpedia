-- Prove2me | solution 1 for GlobalTheory.WeilCube.cubN_rosati
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:58:43.776208+00:00
-- url     : https://prove2.me/submissions/117c5824-30a7-4b4e-bbc8-5a3ec85dee74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ros_add


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory.WeilCube
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)
namespace GlobalTheory.WeilCube
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : RosatiAdj A Lr.L f g) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) (z : T.left) (J)
    (hJ : Good Lr.L z J) : ∃ u, cubN (cubV c z J) k 1 x (y ≫ g) = cubN (cubV c z J) k 1 (x ≫ f) y * u ∧
      cubN (cubV c z J) k 1 (y ≫ g) x = cubN (cubV c z J) k 1 y (x ≫ f) * u := by
  obtain ⟨u, hu, h₀⟩ := exists_ros hG hA Lr.isLB f g h
  have C := isCub_cubV c hJ
  have first : ∀ n : ℕ, val₂ u z J (x ^ n) y * cubN (cubV c z J) n 1 x (y ≫ g) =
      val₂ u z J 1 y * (cubN (cubV c z J) n 1 (x ≫ f) y * val₂ u z J x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := (ros_add c hG hA f g u hu h₀ hJ (x ^ n) x y).1
      rw [MonObj.pow_comp] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have second : ∀ n : ℕ, val₂ u z J x (y ^ n) * cubN (cubV c z J) n 1 (y ≫ g) x =
      val₂ u z J x 1 * (cubN (cubV c z J) n 1 y (x ≫ f) * val₂ u z J x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := (ros_add c hG hA f g u hu h₀ hJ (y ^ n) y x).2
      rw [MonObj.pow_comp, C.s01 x, C.s12 _ x, C.s01 (x ≫ f), C.s12 _ (x ≫ f)] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have a := first k
  have b := second k
  rw [hx] at a
  rw [hy] at b
  exact ⟨_, mul_left_cancel a, mul_left_cancel b⟩
end GlobalTheory.WeilCube
