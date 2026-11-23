-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.Rel.slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:46.534911+00:00
-- url     : https://prove2.me/submissions/861103e3-95c5-4b27-b762-fc8979b13b37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_cstS_comp
import Theorems.Thm_GlobalTheory_SmallExtLift_app_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_gen
import Theorems.Thm_GlobalTheory_SmallExtLift_exists_eq_mul
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
variable {p : X ⟶ Spec (CommRingCat.of R)} {ε : R} {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}
namespace GlobalTheory.SmallExtLift
namespace Rel
theorem _root_.solution (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hV : ⨆ a, V a = ⊤)
    (hA : ∀ a, IsAffineOpen (V a)) {A A' : Scheme.{0}} (s : A ⟶ X) [IsAffineHom s]
    {π : A' ⟶ A} {f' : A' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (P : IsPullback π f' (s ≫ p)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hf : Function.Surjective f'.appTop.hom) (hu : ∀ a, IsUnit (u a))
    (t : LB.Gen (M.pull s)) (ht : t.IsGen) :
    ∃ β : ∀ a, Γ(A, s ⁻¹ᵁ V a), ∀ a b x (ha : s ((𝟙 A : A ⟶ A) x) ∈ V a)
      (hb : s ((𝟙 A : A ⟶ A) x) ∈ V b),
      cstS ((𝟙 A ≫ s) ≫ p) x ε * (gr (𝟙 A ≫ s) x (V a ⊓ V b) ⟨ha, hb⟩ (α a b) -
        (gr (𝟙 A) x (s ⁻¹ᵁ V a) ha (β a) - gr (𝟙 A) x (s ⁻¹ᵁ V b) hb (β b))) = 0 := by
  let r : ∀ a, Γ(A, s ⁻¹ᵁ V a) := fun a => (s.app (V a)).hom (u a) *
    (A.presheaf.map (homOfLE (pull_le M s (j a) (hj a))).op).hom (t.s fun _ => j a)⁻¹.val
  have ru : ∀ a, IsUnit (r a) := fun a => ((hu a).map _).mul ((Units.isUnit _).map _)
  have hr : ∀ a b (Z : Scheme.{0}) (f : Z ⟶ A) (z : Z) (ha : s (f z) ∈ V a) (hb : s (f z) ∈ V b),
      gr f z (s ⁻¹ᵁ V a) ha (r a) = gr f z (s ⁻¹ᵁ V b) hb (r b) *
        (1 + cstS ((f ≫ s) ≫ p) z ε * gr (f ≫ s) z (V a ⊓ V b) ⟨ha, hb⟩ (α a b)) := by
    intro a b Z f z ha hb
    have h1 := H a b _ (f ≫ s) z ha hb
    have h2 := gr_gen ht f z (hj a ha) (hj b hb)
    have i1 := congrArg (gr f z _ (pull_le M s (j a) le_rfl (hj a ha))) (t.s fun _ => j a).mul_inv
    have i2 := congrArg (gr f z _ (pull_le M s (j b) le_rfl (hj b hb))) (t.s fun _ => j b).mul_inv
    rw [map_mul, map_one] at i1 i2
    simp only [r, map_mul]
    rw [gr_res, gr_res, gr_app, gr_app, h1]
    rw [h2] at i1
    generalize gr f z _ (pull_le M s (j a) le_rfl (hj a ha)) (t.s fun _ => j a)⁻¹.val = ta at *
    generalize gr f z _ (pull_le M s (j b) le_rfl (hj b hb)) (t.s fun _ => j b)⁻¹.val = tb at *
    generalize gr f z _ (pull_le M s (j b) le_rfl (hj b hb)) (t.s fun _ => j b).val = sb at *
    generalize gr (f ≫ s) z (M.U (j a) ⊓ M.U (j b)) _ _ = g at *
    generalize (1 + cstS ((f ≫ s) ≫ p) z ε * gr (f ≫ s) z (V a ⊓ V b) ⟨ha, hb⟩ (α a b)) = w at *
    generalize gr (f ≫ s) z (V b) _ (u b) = v at *
    linear_combination (v * w * tb) * i1 - (g * v * w * ta) * i2
  have cov : ⨆ a, π ⁻¹ᵁ s ⁻¹ᵁ V a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hV]; rfl
  obtain ⟨c', hc'⟩ := TLinPf.glue (fun a => π ⁻¹ᵁ s ⁻¹ᵁ V a) cov (fun a => (π.app _).hom (r a))
    (fun a b => gr_ext fun y hy => by
      rw [gr_res, gr_res, gr_app, gr_app, hr a b _ (𝟙 _ ≫ π) y hy.1 hy.2]
      have : ((𝟙 A' ≫ π) ≫ s) ≫ p = f' ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {ε}))) := by rw [← P.w]; simp
      rw [this, cstS_comp, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε),
        map_zero, zero_mul, add_zero, _root_.mul_one])
  obtain ⟨c₁, rfl⟩ := hf c'
  obtain ⟨c₂, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {ε}))).inv).2 c₁
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c₂
  have key : ∀ a, ∃ β : Γ(A, s ⁻¹ᵁ V a), cst (s ≫ p) (s ⁻¹ᵁ V a) c =
      r a * (1 + cst (s ≫ p) (s ⁻¹ᵁ V a) ε * -β) := fun a => by
    obtain ⟨b, hb⟩ := exists_eq_mul P ((hA a).preimage s) (r a - cst (s ≫ p) _ c) (by
      rw [map_sub, app_cst P.w, ← hc' a, sub_eq_zero]; rfl)
    obtain ⟨v, hv⟩ := (ru a).exists_right_inv
    refine ⟨v * b, ?_⟩
    generalize cst (s ≫ p) (s ⁻¹ᵁ V a) c = c₀ at *
    generalize cst (s ≫ p) (s ⁻¹ᵁ V a) ε = e at *
    generalize r a = ρ at *
    linear_combination (e * b) * hv - hb
  choose β hβ using key
  refine ⟨β, fun a b x ha hb => ?_⟩
  have h1 := hr a b _ (𝟙 A) x ha hb
  have h2 := congrArg (gr (𝟙 A) x (s ⁻¹ᵁ V a) ha) (hβ a)
  have h3 := congrArg (gr (𝟙 A) x (s ⁻¹ᵁ V b) hb) (hβ b)
  simp only [map_mul, map_add, map_one, map_neg, gr_cst, ← Category.assoc] at h2 h3
  have he : cstS ((𝟙 A ≫ s) ≫ p) x ε * cstS ((𝟙 A ≫ s) ≫ p) x ε = 0 := by
    rw [← map_mul, hε, map_zero]
  refine ((ru b).map (gr (𝟙 A) x (s ⁻¹ᵁ V b) hb)).mul_right_eq_zero.1 ?_
  rw [h2, h1] at h3
  generalize gr (𝟙 A ≫ s) x (V a ⊓ V b) _ (α a b) = x₁ at *
  generalize gr (𝟙 A) x (s ⁻¹ᵁ V a) ha (β a) = x₂ at *
  generalize gr (𝟙 A) x (s ⁻¹ᵁ V b) hb (β b) = x₃ at *
  generalize gr (𝟙 A) x (s ⁻¹ᵁ V b) hb (r b) = v at *
  generalize cstS ((𝟙 A ≫ s) ≫ p) x ε = e at *
  linear_combination h3 + (v * x₁ * x₂) * he
end Rel
end GlobalTheory.SmallExtLift
