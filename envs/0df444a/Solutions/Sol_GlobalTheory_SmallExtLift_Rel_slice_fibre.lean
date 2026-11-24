-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.Rel.slice_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:09:32.322848+00:00
-- url     : https://prove2.me/submissions/c518ce8e-09eb-4bfb-989d-838c0f4cd2aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_appLE
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_congr
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_slice
import Theorems.Thm_GlobalTheory_SmallExtLift_app_eq_zero_of_mul

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
theorem _root_.solution (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (h0 : ε ≠ 0)
    [X.IsSeparated] (hV : ⨆ a, V a = ⊤)
    (hA : ∀ a, IsAffineOpen (V a)) {A A' Ak : Scheme.{0}} (s : A ⟶ X) [IsAffineHom s]
    [Flat (s ≫ p)] {π : A' ⟶ A} {f' : A' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (P : IsPullback π f' (s ≫ p)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hf : Function.Surjective f'.appTop.hom) (hu : ∀ a, IsUnit (u a))
    (t : LB.Gen (M.pull s)) (ht : t.IsGen) {iA : Ak ⟶ A}
    {fk : Ak ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
    (w : iA ≫ s ≫ p = fk ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (sk : Ak ⟶ Y) (e : sk ≫ i = iA ≫ s) :
    ∃ ψ : ∀ a, Γ(Ak, sk ⁻¹ᵁ i ⁻¹ᵁ V a), ∀ a b,
      (sk.app (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b)).hom
          ((i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b)) =
        (Ak.presheaf.map (homOfLE (show sk ⁻¹ᵁ (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) ≤ sk ⁻¹ᵁ i ⁻¹ᵁ V a from
          fun _ h => h.1)).op).hom (ψ a) -
        (Ak.presheaf.map (homOfLE (show sk ⁻¹ᵁ (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) ≤ sk ⁻¹ᵁ i ⁻¹ᵁ V b from
          fun _ h => h.2)).op).hom (ψ b) := by
  obtain ⟨β, hβ⟩ := H.slice hε hV hA s P hf hu t ht
  have le : ∀ a, sk ⁻¹ᵁ i ⁻¹ᵁ V a ≤ iA ⁻¹ᵁ s ⁻¹ᵁ V a := fun a => by
    rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
  refine ⟨fun a => (iA.appLE _ _ (le a)).hom (β a), fun a b => gr_ext fun y hy => ?_⟩
  have h := app_eq_zero_of_mul h0 w (((hA a).inf (hA b)).preimage s)
    ((s.app _).hom (α a b) -
      ((A.presheaf.map (homOfLE (show s ⁻¹ᵁ (V a ⊓ V b) ≤ s ⁻¹ᵁ V a from fun _ h => h.1)).op).hom
        (β a) -
      (A.presheaf.map (homOfLE (show s ⁻¹ᵁ (V a ⊓ V b) ≤ s ⁻¹ᵁ V b from fun _ h => h.2)).op).hom
        (β b))) (gr_ext fun x hx => by
      rw [map_mul, map_sub, map_sub, gr_res, gr_res, gr_app, gr_cst, map_zero, ← Category.assoc]
      exact hβ a b x hx.1 hx.2)
  have h' := congrArg (gr (𝟙 Ak) y (iA ⁻¹ᵁ s ⁻¹ᵁ (V a ⊓ V b)) ⟨le a hy.1, le b hy.2⟩) h
  rw [gr_app, map_sub, map_sub, gr_res, gr_res, gr_app, map_zero] at h'
  rw [map_sub, gr_res, gr_res, gr_app, gr_appLE, gr_appLE, gr_appLE]
  refine Eq.trans (gr_congr ?_ _ _ _ _) (sub_eq_zero.1 h')
  simp [e]
end Rel
end GlobalTheory.SmallExtLift
