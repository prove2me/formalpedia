-- Prove2me | solution 1 for GlobalTheory.isIso_fromNormalization_of_birational
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:38.831204+00:00
-- url     : https://prove2.me/submissions/23cc24b8-9901-4101-b106-f1310806795a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_sections_of_stalks
import Theorems.Thm_GlobalTheory_apply_genericPoint_of_isDominant
import Theorems.Thm_GlobalTheory_isFractionRing_stalk_of_eq_genericPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
namespace GlobalTheory
universe u
section Normal
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
private lemma app_injective_and_exists_app_eq_of_isIntegral (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    Function.Injective (f.app U) ∧ ∀ s : Γ(X, f ⁻¹ᵁ U),
      (letI := (f.app U).hom.toAlgebra; IsIntegral Γ(Y, U) s) → ∃ r, f.app U r = s := by
  have h2 : f (genericPoint X) = genericPoint Y := _root_.GlobalTheory.apply_genericPoint_of_isDominant f
  obtain ⟨y, hy⟩ := ‹Nonempty U›
  have hηU : f (genericPoint X) ∈ U := by
    rw [h2]; exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 ⟨y, trivial, hy⟩
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨_, hηU⟩
  haveI := _root_.GlobalTheory.isFractionRing_stalk_of_eq_genericPoint hU _ hηU h2
  haveI := _root_.GlobalTheory.isIntegrallyClosed_sections_of_stalks hY hU
  have hsq := f.germ_stalkMap_apply U (genericPoint X) hηU
  have hgX := germ_injective_of_isIntegral X (U := f ⁻¹ᵁ U) (genericPoint X) hηU
  have hg := ConcreteCategory.bijective_of_isIso (f.stalkMap (genericPoint X))
  have hgY : Function.Injective (Y.presheaf.germ U _ hηU) :=
    IsFractionRing.injective Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))
  refine ⟨fun a b hab => hgY (hg.1 ?_), fun s hs => ?_⟩
  · rw [hsq, hsq, hab]
  · letI := (f.app U).hom.toAlgebra
    let ψ := (inv (f.stalkMap (genericPoint X))).hom.comp (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU).hom
    have hψ : (algebraMap Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X)))).comp (RingHom.id _) =
        ψ.comp (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
      ext a
      change Y.presheaf.germ U _ hηU a = (inv (f.stalkMap (genericPoint X))).hom
        (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU (f.app U a))
      rw [← hsq, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hs.map_of_comp_eq (RingHom.id _) ψ hψ)
    have hr' : Y.presheaf.germ U _ hηU r =
        (inv (f.stalkMap (genericPoint X))).hom (X.presheaf.germ (f ⁻¹ᵁ U) _ hηU s) := hr
    refine ⟨r, hgX ?_⟩
    rw [← hsq, hr', ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology in
variable {X Y : Scheme.{u}} in
private lemma bijective_algebraMap_integralClosure_of_isIntegrallyClosed (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Function.Bijective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) := by
  letI := (f.app U).hom.toAlgebra
  rcases isEmpty_or_nonempty U with hE | hN
  · have hU0 : U = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hE.false ⟨x, hx⟩
    subst hU0
    have h01 : (0 : integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥)) = 1 := by
      rw [← map_zero (algebraMap Γ(Y, ⊥) (integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥))),
        ← map_one (algebraMap Γ(Y, ⊥) (integralClosure Γ(Y, ⊥) Γ(X, f ⁻¹ᵁ ⊥))),
        Subsingleton.elim (0 : Γ(Y, ⊥)) 1]
    haveI := subsingleton_of_zero_eq_one h01
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain ⟨hinj, hex⟩ := app_injective_and_exists_app_eq_of_isIntegral f hY hU
    refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun b => ?_⟩
    obtain ⟨r, hr⟩ := hex b.1 b.2
    exact ⟨r, Subtype.ext hr⟩
end Normal
section Constructible
end Constructible
section Etale
variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
end Etale
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f.fromNormalization := by
  have hpiece : ∀ U : Y.affineOpens,
      IsIso (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))) := by
    intro U
    haveI : IsIso ((f.normalizationDiagramMap).app (Opposite.op U.1)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_algebraMap_integralClosure_of_isIntegrallyClosed f hY U.2)
    infer_instance
  have hcomp : ∀ U : Y.affineOpens,
      IsOpenImmersion (f.normalizationOpenCover.f U ≫ f.fromNormalization) := by
    intro U
    rw [Scheme.Hom.ι_fromNormalization]
    haveI := hpiece U
    haveI : IsOpenImmersion (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))) :=
      IsOpenImmersion.of_isIso _
    exact @IsOpenImmersion.comp _ _ _ _ _ this (IsAffineOpen.isOpenImmersion_fromSpec _)
  have hinj : Function.Injective f.fromNormalization := by
    intro z₁ z₂ h
    obtain ⟨V, hV, hyV, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
      (show f.fromNormalization z₁ ∈ (⊤ : Y.Opens) from trivial)
    let U : Y.affineOpens := ⟨V, hV⟩
    have h₁ : z₁ ∈ f.fromNormalization ⁻¹ᵁ U.1 := hyV
    have h₂ : z₂ ∈ f.fromNormalization ⁻¹ᵁ U.1 := by
      show f.fromNormalization z₂ ∈ V
      rw [← h]; exact hyV
    rw [Scheme.Hom.fromNormalization_preimage] at h₁ h₂
    obtain ⟨q₁, rfl⟩ := h₁
    obtain ⟨q₂, rfl⟩ := h₂
    haveI := hcomp U
    congr 1
    apply (f.normalizationOpenCover.f U ≫ f.fromNormalization).isOpenEmbedding.injective
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h]
  haveI : IsOpenImmersion f.fromNormalization :=
    IsOpenImmersion.of_openCover_source _ f.normalizationOpenCover hinj hcomp
  haveI : Epi f.fromNormalization.base := by
    rw [TopCat.epi_iff_surjective]
    intro y
    obtain ⟨V, hV, hyV, -⟩ :=
      (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) (show y ∈ (⊤ : Y.Opens) from trivial)
    let U : Y.affineOpens := ⟨V, hV⟩
    have hV' : IsAffineOpen V := hV
    haveI := hpiece U
    obtain ⟨p, hp⟩ : y ∈ Set.range hV'.fromSpec := by
      rw [← SetLike.mem_coe, ← hV'.range_fromSpec] at hyV; exact hyV
    obtain ⟨q, rfl⟩ := (Spec.map ((f.normalizationDiagramMap).app (Opposite.op U.1))).surjective p
    refine ⟨f.normalizationOpenCover.f U q, ?_⟩
    rw [← hp]
    exact (Scheme.Hom.comp_apply _ _ q).symm.trans
      ((congrArg (fun g => g q) (Scheme.Hom.ι_fromNormalization f U)).trans
        (Scheme.Hom.comp_apply _ _ q))
  exact IsOpenImmersion.isIso _
end _root_.GlobalTheory
end GlobalTheory
