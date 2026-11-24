-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.exists_gen_of_small_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:05.686606+00:00
-- url     : https://prove2.me/submissions/43328261-3310-42ea-8bd3-e62e8b1bfe70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_appLE
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_exists_lift
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_gen
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_slice
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_cocycle_fibre
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_slice_fibre
import Theorems.Thm_GlobalTheory_SmallExtLift_Rel_gen_fibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback


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
open scoped CategoryTheory.Obj
namespace GlobalTheory.SmallExtLift
theorem _root_.solution : GlobalFnsSt → (∀ (K : Type) [Field K] (X Y : Over (Spec (CommRingCat.of K))) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → Function.Bijective X.hom.appTop.hom → Function.Bijective Y.hom.appTop.hom → ∀ (I : Type) (V : I → (X ⊗ Y).left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ((X ⊗ Y).left, V a ⊓ V b), (∀ a b d, ((X ⊗ Y).left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b)).op).hom (φ a b) + ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d)).op).hom (φ b d) = ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d)).op).hom (φ a d)) → (∃ ψ : ∀ a, Γ(X.left, (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a), ∀ a b, ((lift (𝟙 X) (toUnit X ≫ y₀)).left.app (V a ⊓ V b)).hom (φ a b) = (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → (∃ ψ : ∀ a, Γ(Y.left, (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a), ∀ a b, ((lift (toUnit Y ≫ x₀) (𝟙 Y)).left.app (V a ⊓ V b)).hom (φ a b) = (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → ∃ ψ : ∀ a, Γ((X ⊗ Y).left, V a), ∀ a b, φ a b = ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) - ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_right).op).hom (ψ b)) → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → (∃ t : LB.Gen (M.pull (lift (𝟙 A) 1).left), t.IsGen) → (∃ t : LB.Gen (M.pull (lift 1 (𝟙 A)).left), t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → (∃ t : LB.Gen (M.pull π), t.IsGen) → ∃ t : LB.Gen M, t.IsGen := by
  intro hG hK R _ _ ε hm A _ hA M hM ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ X' π f' P hε ⟨t, ht⟩
  have hεε : ε * ε = 0 := hm ε hε
  have := hA.smooth
  have := hA.proper
  have sep : IsSeparated (A ⊗ A).hom := by
    change IsSeparated (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have fl : Flat (A ⊗ A).hom := by
    change Flat (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have : (A ⊗ A).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (A ⊗ A).hom]; infer_instance⟩
  obtain ⟨I, V, j, hj, u, α, hV, haff, hu, H⟩ := exists_lift hεε P hM t ht
  by_cases h0 : ε = 0
  · exact H.gen hεε hM hV hu (fun _ => 0) fun a b x ha hb => by rw [h0, map_zero, zero_mul]
  let φ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
  let F := Over.pullback φ
  have hk := TLinPf.isAb_pullback φ A hA
  have := hk.proper
  let i : (F.obj A ⊗ F.obj A).left ⟶ (A ⊗ A).left :=
    (Functor.Monoidal.μIso F A A).hom.left ≫ pullback.fst (A ⊗ A).hom φ
  have Pk : IsPullback i (F.obj A ⊗ F.obj A).hom (A ⊗ A).hom φ := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback (A ⊗ A).hom φ)
      ((Over.forget _).mapIso (Functor.Monoidal.μIso F A A).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · change _ ≫ 𝟙 _ = (Functor.Monoidal.μIso F A A).inv.left ≫ i
      rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
      simp
    · exact (Category.comp_id _).trans (Over.w (Functor.Monoidal.μIso F A A).inv).symm
  have slice : ∀ (s : A ⟶ A ⊗ A) (r : A ⊗ A ⟶ A) [IsSeparated r.left], s ≫ r = 𝟙 A →
      ∀ (t : LB.Gen (M.pull s.left)), t.IsGen → ∀ sk : F.obj A ⟶ F.obj A ⊗ F.obj A,
      sk ≫ (Functor.Monoidal.μIso F A A).hom = F.map s → _ := fun s r _ hs t ht sk e => by
    have h1 : s.left ≫ r.left = 𝟙 _ := congrArg (fun q => q.left) hs
    have : IsClosedImmersion (s.left ≫ r.left) := by rw [h1]; infer_instance
    have : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left r.left
    have : Flat (s.left ≫ (A ⊗ A).hom) := by rw [Over.w]; infer_instance
    exact H.slice_fibre (i := i) hεε h0 hV haff s.left (π := pullback.fst A.hom q)
      (f' := pullback.snd A.hom q) (by rw [Over.w]; exact IsPullback.of_hasPullback _ _)
      (hG _ _ (TLinPf.isAb_pullback q A hA)).2 hu t ht (iA := pullback.fst A.hom φ)
      (fk := pullback.snd A.hom φ) (by rw [Over.w]; exact pullback.condition) sk.left (by
        rw [← Category.assoc, ← Over.comp_left, e]
        exact pullback.lift_fst _ _ _)
  have one : toUnit (F.obj A) ≫ η[F.obj A] = F.map (1 : A ⟶ A) := by
    rw [Functor.obj.η_def, Hom.one_def, F.map_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.OplaxMonoidal.η F)]
    exact toUnit_unique _ _
  obtain ⟨ψ, hψ⟩ := hK (IsLocalRing.ResidueField R) (F.obj A) (F.obj A) η[F.obj A] η[F.obj A]
    inferInstance inferInstance inferInstance inferInstance (hG _ _ hk) (hG _ _ hk) I
    (fun a => i ⁻¹ᵁ V a) (by rw [← Scheme.Hom.preimage_iSup, hV]; rfl)
    (fun a b => (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b))
    (fun a b d => gr_ext fun y hy => by
      rw [map_add, gr_res, gr_res, gr_res, gr_appLE, gr_appLE, gr_appLE]
      exact H.cocycle_fibre hεε h0 hM haff hu Pk.w a b d y hy.1.1 hy.1.2 hy.2)
    (@slice _ (fst A A) (by change IsSeparated (pullback.fst A.hom A.hom); infer_instance)
      (by simp) t₁ ht₁ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
    (@slice _ (snd A A) (by change IsSeparated (pullback.snd A.hom A.hom); infer_instance)
      (by simp) t₂ ht₂ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
  exact H.gen_fibre hεε hm hM hV haff hu Pk ψ hψ
end GlobalTheory.SmallExtLift
