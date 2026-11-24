-- Prove2me | solution 1 for GlobalTheory.KuennethOne.kuenneth_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:29.259723+00:00
-- url     : https://prove2.me/submissions/3bf250c4-06df-4cee-8c5f-1ef5a02300ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
import Theorems.Thm_GlobalTheory_KuennethOne_exists_splits_preimage
import Theorems.Thm_GlobalTheory_KuennethOne_exists_splits_top
import Theorems.Thm_GlobalTheory_KuennethOne_isAffineOpen_inf_of_isSeparated
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KuennethOne
namespace GlobalTheory.KuennethOne
theorem _root_.solution :
    ∀ (K : Type) [Field K] (X Y : Over (Spec (CommRingCat.of K))) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → Function.Bijective X.hom.appTop.hom → Function.Bijective Y.hom.appTop.hom → ∀ (I : Type) (V : I → (X ⊗ Y).left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ((X ⊗ Y).left, V a ⊓ V b), (∀ a b d, ((X ⊗ Y).left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b)).op).hom (φ a b) + ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d)).op).hom (φ b d) = ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d)).op).hom (φ a d)) → (∃ ψ : ∀ a, Γ(X.left, (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a), ∀ a b, ((lift (𝟙 X) (toUnit X ≫ y₀)).left.app (V a ⊓ V b)).hom (φ a b) = (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → (∃ ψ : ∀ a, Γ(Y.left, (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a), ∀ a b, ((lift (toUnit Y ≫ x₀) (𝟙 Y)).left.app (V a ⊓ V b)).hom (φ a b) = (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → ∃ ψ : ∀ a, Γ((X ⊗ Y).left, V a), ∀ a b, φ a b = ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) - ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_right).op).hom (ψ b) := by
  intro K _ X Y x₀ y₀ sX qX sY qY bX bY I V hV φ hφ ⟨ρX, hρX⟩ ⟨ρY, hρY⟩
  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    IsPullback.of_hasPullback X.hom Y.hom
  have hR : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := (quasiSeparated_iff_quasiSeparatedSpace X.hom).mp inferInstance
  have : Flat Y.hom := inferInstance
  have hco : IsCocycle V φ := by
    intro a b d N ha hb hd
    have := congrArg (rs (le_inf (le_inf ha hb) hd)) (hφ a b d)
    rw [map_add] at this
    exact (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm.trans (this.trans (rs_rs _ _ _))
  let y : Spec (CommRingCat.of K) ⟶ Y.left := y₀.left
  have hy : y ≫ Y.hom = 𝟙 _ := Over.w y₀
  have hs : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (fst X Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hs' : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (snd X Y).left = X.hom ≫ y := by
    rw [← Over.comp_left, lift_snd]; rfl
  have ht : (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ≫ (snd X Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Y.left.affineOpens, ⊤ ≤ y ⁻¹ᵁ W₀.1 := by
    have : y default ∈ ⨆ W : Y.left.affineOpens, W.1 := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine ⟨W, fun z _ => ?_⟩
    rw [Subsingleton.elim z default]
    exact hW
  obtain ⟨χ, hχ⟩ := exists_splits_top H (isAffineOpen_inf_of_isSeparated Y.hom) bX ht hV ρY hρY
    (exists_splits_preimage H hR (isAffineOpen_inf_of_isSeparated X.hom)
      (isAffineOpen_inf_of_isSeparated Y.hom) bY.2 hy hs hs' W₀ hW₀ hV hco ρX hρX)
  refine ⟨fun a => rs (le_inf le_top le_rfl) (χ a), fun a b => ?_⟩
  have := hχ a b (V a ⊓ V b) le_top inf_le_left inf_le_right
  rw [rs_self] at this
  exact this.trans (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm
end GlobalTheory.KuennethOne
