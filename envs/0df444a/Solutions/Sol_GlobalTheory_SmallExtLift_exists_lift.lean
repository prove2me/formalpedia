-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:29.394948+00:00
-- url     : https://prove2.me/submissions/1494f4ca-38bc-4965-ace3-24e54267948c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_app_surj
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_gen
import Theorems.Thm_GlobalTheory_SmallExtLift_exists_eq_mul
import Theorems.Thm_GlobalTheory_SmallExtLift_isUnit_of_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


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
namespace GlobalTheory.SmallExtLift
theorem _root_.solution {ε : R} (hε : ε * ε = 0) {p : X ⟶ Spec (CommRingCat.of R)} [X.IsSeparated]
    {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    {M : LB X} (hM : M.IsLB) (t : LB.Gen (M.pull π)) (ht : t.IsGen) :
    ∃ (I : Type) (V : I → X.Opens) (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a))
      (u : ∀ a, Γ(X, V a)) (α : ∀ a b, Γ(X, V a ⊓ V b)),
      ⨆ a, V a = ⊤ ∧ (∀ a, IsAffineOpen (V a)) ∧ (∀ a, IsUnit (u a)) ∧ Rel p ε M V j hj u α := by
  let I := {q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}
  let V : I → X.Opens := fun a => a.1.2
  let j : I → M.ι := fun a => a.1.1
  have hj : ∀ a, V a ≤ M.U (j a) := fun a => a.2.2
  have hV : ∀ a, IsAffineOpen (V a) := fun a => a.2.1
  choose u hu using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    ((Y.presheaf.map (homOfLE (pull_le M π (j a) (hj a))).op).hom (t.s fun _ => j a).val)
  have uu : ∀ a, IsUnit (u a) := fun a => isUnit_of_app hε H (hV a) _ (by
    rw [hu]; exact (Units.isUnit _).map _)
  have key : ∀ a b, ∃ α : Γ(X, V a ⊓ V b), (X.presheaf.map (homOfLE inf_le_left).op).hom (u a) =
      (X.presheaf.map (homOfLE (inf_le_inf (hj a) (hj b))).op).hom (M.g (j a) (j b)).val *
      (X.presheaf.map (homOfLE inf_le_right).op).hom (u b) * (1 + cst p _ ε * α) := by
    intro a b
    obtain ⟨c, hc⟩ := exists_eq_mul H ((hV a).inf (hV b))
      ((X.presheaf.map (homOfLE inf_le_left).op).hom (u a) -
      (X.presheaf.map (homOfLE (inf_le_inf (hj a) (hj b))).op).hom (M.g (j a) (j b)).val *
      (X.presheaf.map (homOfLE inf_le_right).op).hom (u b)) (gr_ext fun y hy => by
        have e : ∀ c (h : (𝟙 Y ≫ π) y ∈ V c), gr (𝟙 Y ≫ π) y (V c) h (u c) =
            gr (𝟙 Y) y _ (pull_le M π (j c) le_rfl (hj c h)) (t.s fun _ => j c).val := fun c h =>
          (gr_app (𝟙 Y) π y (V c) h (u c)).symm.trans ((congrArg _ (hu c)).trans (gr_res (𝟙 Y) y _ h _))
        refine (gr_app _ _ _ _ _ _).trans ?_
        rw [map_zero, map_sub, map_mul, gr_res, gr_res, gr_res, e, e, sub_eq_zero]
        exact gr_gen ht (𝟙 Y) y (hj a hy.1) (hj b hy.2))
    obtain ⟨v, hv⟩ := (((Units.isUnit (M.g (j a) (j b))).map
      (X.presheaf.map (homOfLE (inf_le_inf (hj a) (hj b))).op).hom).mul ((uu b).map
      (X.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ _)).op).hom)).exists_right_inv
    exact ⟨v * c, by linear_combination hc - (cst p _ ε * c) * hv⟩
  choose α hα using key
  refine ⟨I, V, j, hj, u, α, eq_top_iff.2 fun x _ => ?_, hV, uu, fun a b Z f z ha hb => ?_⟩
  · obtain ⟨i, hi⟩ := TLinPf.exists_chart M hM x
    obtain ⟨W, hW, hxW, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩
  · have := congrArg (gr f z (V a ⊓ V b) ⟨ha, hb⟩) (hα a b)
    rwa [map_mul, map_mul, map_add, map_one, map_mul, gr_res, gr_res, gr_res, gr_cst] at this
end GlobalTheory.SmallExtLift
