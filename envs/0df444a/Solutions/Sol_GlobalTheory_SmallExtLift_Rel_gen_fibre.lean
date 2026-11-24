-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.Rel.gen_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:51.860667+00:00
-- url     : https://prove2.me/submissions/f99510b3-b345-41e7-b19e-58592d6e93b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_appLE
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_app_surj
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_gen
import Theorems.Thm_GlobalTheory_SmallExtLift_mul_eq_zero_of_app

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
variable [IsLocalRing R] {ε : R} {p : X ⟶ Spec (CommRingCat.of R)} {i : Y ⟶ X}
  {f : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
variable {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}
namespace GlobalTheory.SmallExtLift
namespace Rel
theorem _root_.solution (H : Rel p ε M V j hj u α) (hε : ε * ε = 0)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) [X.IsSeparated] (hM : M.IsLB)
    (hV : ⨆ a, V a = ⊤) (hA : ∀ a, IsAffineOpen (V a)) (hu : ∀ a, IsUnit (u a))
    (P : IsPullback i f p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (ψ : ∀ a, Γ(Y, i ⁻¹ᵁ V a))
    (hψ : ∀ a b, (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b) =
      (Y.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) -
        (Y.presheaf.map (homOfLE inf_le_right).op).hom (ψ b)) :
    ∃ t : LB.Gen M, t.IsGen := by
  choose β hβ using fun a => app_surj IsLocalRing.residue_surjective P (hA a) (ψ a)
  refine H.gen hε hM hV hu β fun a b x ha hb => ?_
  have h := mul_eq_zero_of_app hm P ((hA a).inf (hA b)) (α a b -
    ((X.presheaf.map (homOfLE inf_le_left).op).hom (β a) -
      (X.presheaf.map (homOfLE inf_le_right).op).hom (β b))) (gr_ext fun y hy => by
      have h' := congrArg (gr (𝟙 Y) y (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) hy) (hψ a b)
      rw [gr_appLE, map_sub, gr_res, gr_res, ← hβ, ← hβ, gr_app, gr_app] at h'
      rw [gr_app, map_sub, map_sub, gr_res, gr_res, map_zero]
      exact sub_eq_zero.2 h')
  have h' := congrArg (gr (𝟙 X) x (V a ⊓ V b) ⟨ha, hb⟩) h
  rwa [map_mul, map_sub, map_sub, gr_res, gr_res, gr_cst, map_zero] at h'
end Rel
end GlobalTheory.SmallExtLift
