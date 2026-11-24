-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.Rel.gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:53.062665+00:00
-- url     : https://prove2.me/submissions/14e41c63-1d10-465b-9819-ba39de44365e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_gen_of_refine
import Theorems.Thm_GlobalTheory_SmallExtLift_isUnit_one_add

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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
variable {R : Type} [CommRing R]
variable {p : X ⟶ Spec (CommRingCat.of R)} {ε : R} {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}
namespace GlobalTheory.SmallExtLift
namespace Rel
theorem _root_.solution (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hM : M.IsLB) (hV : ⨆ a, V a = ⊤)
    (hu : ∀ a, IsUnit (u a)) (β : ∀ a, Γ(X, V a))
    (hβ : ∀ a b x (ha : (𝟙 X : X ⟶ X) x ∈ V a) (hb : (𝟙 X : X ⟶ X) x ∈ V b),
      cstS (𝟙 X ≫ p) x ε * (gr (𝟙 X) x (V a ⊓ V b) ⟨ha, hb⟩ (α a b) -
        (gr (𝟙 X) x _ ha (β a) - gr (𝟙 X) x _ hb (β b))) = 0) :
    ∃ t : LB.Gen M, t.IsGen := by
  refine gen_of_refine hM V hV j hj (fun a => u a * (1 + cst p _ ε * (-β a)))
    (fun a => (hu a).mul (isUnit_one_add (by rw [← map_mul, hε, map_zero]) _))
    fun a b x ha hb => ?_
  have he : cstS (𝟙 X ≫ p) x ε * cstS (𝟙 X ≫ p) x ε = 0 := by rw [← map_mul, hε, map_zero]
  have h := hβ a b x ha hb
  simp only [map_mul, map_add, map_one, map_neg, gr_cst]
  rw [H a b _ _ x ha hb]
  generalize gr (𝟙 X) x (V a ⊓ V b) ⟨ha, hb⟩ (α a b) = x₁ at *
  generalize gr (𝟙 X) x _ ha (β a) = x₂ at *
  generalize gr (𝟙 X) x _ hb (β b) = x₃ at *
  generalize cstS (𝟙 X ≫ p) x ε = e at *
  generalize gr (𝟙 X) x _ hb (u b) = v at *
  generalize gr (𝟙 X) x (M.U (j a) ⊓ M.U (j b)) _ _ = g₁ at *
  linear_combination (g₁ * v) * h - (g₁ * v * x₁ * x₂) * he
end Rel
end GlobalTheory.SmallExtLift
