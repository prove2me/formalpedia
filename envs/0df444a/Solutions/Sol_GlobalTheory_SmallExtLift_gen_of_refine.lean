-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.gen_of_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:37.705045+00:00
-- url     : https://prove2.me/submissions/22538b99-fb39-4200-b42c-19080dae6cef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_isUnit_of_gr
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_glue


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
theorem _root_.solution {M : LB X} (hM : M.IsLB) {I : Type} (V : I → X.Opens) (hV : ⨆ a, V a = ⊤)
    (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (w : ∀ a, Γ(X, V a)) (hw : ∀ a, IsUnit (w a))
    (H : ∀ a b x (ha : (𝟙 X : X ⟶ X) x ∈ V a) (hb : (𝟙 X : X ⟶ X) x ∈ V b),
      gr (𝟙 X) x _ ha (w a) = gr (𝟙 X) x (M.U (j a) ⊓ M.U (j b)) ⟨hj a ha, hj b hb⟩
        (M.g (j a) (j b)).val * gr (𝟙 X) x _ hb (w b)) :
    ∃ t : LB.Gen M, t.IsGen := by
  have cov : ∀ x : X, ∃ a, x ∈ V a := fun x =>
    Opens.mem_iSup.1 (show x ∈ ⨆ a, V a by rw [hV]; trivial)
  have glue : ∀ i : M.ι, ∃ s : Γ(X, M.U i), ∀ a x (hi : (𝟙 X : X ⟶ X) x ∈ M.U i)
      (ha : (𝟙 X : X ⟶ X) x ∈ V a), gr (𝟙 X) x _ hi s =
        gr (𝟙 X) x (M.U i ⊓ M.U (j a)) ⟨hi, hj a ha⟩ (M.g i (j a)).val * gr (𝟙 X) x _ ha (w a) := by
    intro i
    let u : ∀ a, Γ(X, M.U i ⊓ V a) := fun a =>
      (X.presheaf.map (homOfLE (inf_le_inf_left _ (hj a))).op).hom (M.g i (j a)).val *
        (X.presheaf.map (homOfLE inf_le_right).op).hom (w a)
    have hu : ∀ a x (h : (𝟙 X : X ⟶ X) x ∈ M.U i ⊓ V a), gr (𝟙 X) x _ h (u a) =
        gr (𝟙 X) x (M.U i ⊓ M.U (j a)) ⟨h.1, hj a h.2⟩ (M.g i (j a)).val *
          gr (𝟙 X) x _ h.2 (w a) := fun a x h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gr_res _ x _ h _) (gr_res _ x _ h _))
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun a => M.U i ⊓ V a) (M.U i)
      (fun a => homOfLE inf_le_left) (fun x hx => by
        obtain ⟨a, ha⟩ := cov x
        exact Opens.mem_iSup.2 ⟨a, hx, ha⟩) u
      (fun a b => gr_ext (V := (M.U i ⊓ V a) ⊓ (M.U i ⊓ V b)) fun x hx => by
        refine (gr_res _ x inf_le_left hx _).trans
          (Eq.trans ?_ (gr_res _ x inf_le_right hx _).symm)
        refine (hu a x hx.1).trans (Eq.trans ?_ (hu b x hx.2).symm)
        rw [H a b x hx.1.2 hx.2.2, ← _root_.mul_assoc,
          gr_cocycle hM _ x hx.1.1 (hj a hx.1.2) (hj b hx.2.2)])
    refine ⟨s, fun a x hi ha => ?_⟩
    have hm : (𝟙 X : X ⟶ X) x ∈ M.U i ⊓ V a := ⟨hi, ha⟩
    exact (gr_res _ x inf_le_left hm s).symm.trans ((congrArg (gr _ x _ hm) (hs a)).trans (hu a x hm))
  choose s hs using glue
  have hu : ∀ i, IsUnit (s i) := fun i => isUnit_of_gr fun x hx => by
    obtain ⟨a, ha⟩ := cov x
    rw [hs i a x hx ha]
    exact ((Units.isUnit _).map _).mul ((hw a).map _)
  refine ⟨⟨fun i => (hu i).unit⟩, fun i k => Units.ext (gr_ext fun x hx => ?_)⟩
  obtain ⟨a, ha⟩ := cov x
  refine (gr_res _ x inf_le_left hx (s i)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gr_res _ x inf_le_right hx (s k)))).symm)
  rw [hs i a x hx.1 ha, hs k a x hx.2 ha, ← _root_.mul_assoc, ← gr_cocycle hM _ x hx.1 hx.2 (hj a ha)]
end GlobalTheory.SmallExtLift
