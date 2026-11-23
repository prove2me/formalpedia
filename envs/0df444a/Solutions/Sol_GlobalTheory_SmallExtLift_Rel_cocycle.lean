-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.Rel.cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:15.408931+00:00
-- url     : https://prove2.me/submissions/39f41968-9ae4-4170-8ede-70c660c95d62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cocycle

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
theorem _root_.solution (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hM : M.IsLB)
    (hu : ∀ a, IsUnit (u a)) (a b d : I) (f : Z ⟶ X) (z : Z) (ha : f z ∈ V a) (hb : f z ∈ V b)
    (hd : f z ∈ V d) :
    cstS (f ≫ p) z ε * (gr f z (V a ⊓ V b) ⟨ha, hb⟩ (α a b) + gr f z (V b ⊓ V d) ⟨hb, hd⟩ (α b d) -
      gr f z (V a ⊓ V d) ⟨ha, hd⟩ (α a d)) = 0 := by
  have h1 := H a b _ f z ha hb
  have h2 := H b d _ f z hb hd
  have h3 := H a d _ f z ha hd
  have hc := gr_cocycle hM f z (hj a ha) (hj b hb) (hj d hd)
  have he : cstS (f ≫ p) z ε * cstS (f ≫ p) z ε = 0 := by rw [← map_mul, hε, map_zero]
  have un := ((Units.isUnit (M.g (j a) (j d))).map
    (gr f z (M.U (j a) ⊓ M.U (j d)) ⟨hj a ha, hj d hd⟩)).mul ((hu d).map (gr f z _ hd))
  refine un.mul_right_eq_zero.1 ?_
  rw [h1, h2] at h3
  generalize gr f z (V a ⊓ V b) ⟨ha, hb⟩ (α a b) = x₁ at *
  generalize gr f z (V b ⊓ V d) ⟨hb, hd⟩ (α b d) = x₂ at *
  generalize gr f z (V a ⊓ V d) ⟨ha, hd⟩ (α a d) = x₃ at *
  generalize cstS (f ≫ p) z ε = e at *
  generalize gr f z _ hd (u d) = v at *
  rw [← hc] at h3 ⊢
  generalize gr f z (M.U (j a) ⊓ M.U (j b)) _ _ = g₁ at *
  generalize gr f z (M.U (j b) ⊓ M.U (j d)) _ _ = g₂ at *
  linear_combination h3 - (g₁ * g₂ * v * x₁ * x₂) * he
end Rel
end GlobalTheory.SmallExtLift
