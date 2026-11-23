-- Prove2me | solution 1 for GlobalTheory.TorusTrivial.isAffine_and_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:57.497127+00:00
-- url     : https://prove2.me/submissions/512815f6-a571-49dc-9287-1417e747b497

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusTrivial
namespace GlobalTheory.TorusTrivial
theorem _root_.solution {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W V : Over S}
    [IsAffine V.left] (τ : W ⟶ splitTorus S X) (q : W ⟶ V) [IsIso (lift τ q)]
    {A : CommRingCat.{0}} (e : A ≅ Γ(V.left, ⊤)) (f : AddMonoidAlgebra A X →+* Γ(W.left, ⊤))
    (hf₁ : ∀ a : A, f (AddMonoidAlgebra.single 0 a) = q.left.appTop.hom (e.hom.hom a))
    (hf₂ : ∀ χ : X, f (AddMonoidAlgebra.single χ 1) = τ.left.appTop.hom (charUnit S X χ).val) :
    IsAffine W.left ∧ Function.Bijective f := by
  let R : CommRingCat.{0} := .of (AddMonoidAlgebra A X)
  let F : R ⟶ Γ(W.left, ⊤) := CommRingCat.ofHom f
  let φ : W.left ⟶ Spec R := W.left.toSpecΓ ≫ Spec.map F
  have hφ : (Scheme.ΓSpecIso R).inv ≫ φ.appTop = F := by
    rw [SplitTorusPoints.ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
      Category.comp_id]
  have hφ' : ∀ x, φ.appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = f x := fun x =>
    congrArg (fun g => g.hom x) hφ
  let c : A ⟶ R := CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom)
  let v : Spec R ⟶ V.left := Spec.map (e.inv ≫ c) ≫ V.left.isoSpec.inv
  have hv : e.hom ≫ v.appTop = c ≫ (Scheme.ΓSpecIso R).inv := by
    have : V.left.isoSpec.inv.appTop = (Scheme.ΓSpecIso _).inv := by
      rw [← cancel_epi (Scheme.ΓSpecIso Γ(V.left, ⊤)).hom, Iso.hom_inv_id,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg Scheme.Hom.appTop V.left.isoSpec.inv_hom_id
    rw [Scheme.Hom.comp_appTop, this, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Iso.hom_inv_id_assoc]
  have hv' : ∀ a : A, v.appTop.hom (e.hom.hom a) =
      (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single 0 a) := fun a =>
    congrArg (fun g => g.hom a) hv
  let P : Over S := Over.mk (v ≫ V.hom)
  let v' : P ⟶ V := Over.homMk v rfl
  let t : P ⟶ splitTorus S X := (splitTorusPointsEquiv S X P).symm
    ((Scheme.ΓSpecIso R).inv.hom.toMonoidHom.comp (AddMonoidAlgebra.of A X)).toHomUnits
  have ht : ∀ χ : X, t.left.appTop.hom (charUnit S X χ).val =
      (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single χ 1) := by
    intro χ
    rw [← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  have hφv : φ ≫ v = q.left := by
    apply ext_of_isAffine
    rw [← cancel_epi e.hom, Scheme.Hom.comp_appTop, reassoc_of% hv, hφ]
    ext a
    exact hf₁ a
  let φ' : W ⟶ P := Over.homMk φ (by
    change φ ≫ v ≫ V.hom = _
    rw [reassoc_of% hφv, Over.w])
  have h₁ : φ' ≫ v' = q := Over.OverMorphism.ext hφv
  have h₂ : φ' ≫ t = τ := by
    apply (splitTorusPointsEquiv S X W).injective
    ext χ
    change (splitTorusPointsEquiv S X W _ (Multiplicative.ofAdd χ)).val =
      (splitTorusPointsEquiv S X W _ (Multiplicative.ofAdd χ)).val
    rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, ← hf₂, ← hφ', ← ht]
    rfl
  let σ : P ⟶ W := lift t v' ≫ inv (lift τ q)
  have hσ : σ ≫ lift τ q = lift t v' := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hσ₁ : σ ≫ τ = t := by simpa using hσ =≫ fst _ _
  have hσ₂ : σ ≫ q = v' := by simpa using hσ =≫ snd _ _
  have h₃ : φ' ≫ σ = 𝟙 _ := by
    rw [← cancel_mono (lift τ q), Category.assoc, hσ, comp_lift, h₁, h₂, Category.id_comp]
  let σ' : Spec R ⟶ W.left := σ.left
  have h₄ : σ' ≫ φ = 𝟙 _ := by
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso R).inv, Scheme.Hom.comp_appTop, reassoc_of% hφ]
    ext1
    apply AddMonoidAlgebra.ringHom_ext
    · intro a
      change σ'.appTop.hom (f (AddMonoidAlgebra.single 0 a)) =
        (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single 0 a)
      rw [hf₁, ← hv']
      exact congrArg (fun g : P ⟶ V => g.left.appTop.hom (e.hom.hom a)) hσ₂
    · intro χ
      change σ'.appTop.hom (f (AddMonoidAlgebra.single χ 1)) =
        (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single χ 1)
      rw [hf₂, ← ht]
      exact congrArg (fun g : P ⟶ _ => g.left.appTop.hom (charUnit S X χ).val) hσ₁
  have : IsIso φ := ⟨σ', congrArg CommaMorphism.left h₃, h₄⟩
  refine ⟨.of_isIso φ, ?_⟩
  have : IsIso φ.appTop := inferInstanceAs (IsIso (φ.app ⊤))
  have : IsIso F := by rw [← hφ]; infer_instance
  exact ConcreteCategory.bijective_of_isIso F
end GlobalTheory.TorusTrivial
