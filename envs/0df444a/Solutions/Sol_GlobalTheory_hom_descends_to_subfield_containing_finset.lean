-- Prove2me | solution 1 for GlobalTheory.hom_descends_to_subfield_containing_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:51.723829+00:00
-- url     : https://prove2.me/submissions/d5fd8b56-0442-430c-bd9e-db67cee32f47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomDescendsToSubfieldContainingFinset
import Theorems.Thm_GlobalTheory_Spread_exists_fg_comp_eq
import Theorems.Thm_GlobalTheory_quasiCompact_descendsAlong_fpqc
import Theorems.Thm_GlobalTheory_quasiSeparated_descendsAlong_fpqc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private theorem surjective_flat_quasiCompact_spMap {k K : Type} [Field k] [Field K] (σ : k →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show Surjective (Spec.map (CommRingCat.ofHom σ))
    constructor
    intro x
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
    exact ⟨y, Subsingleton.elim _ _⟩
  · show Flat (Spec.map (CommRingCat.ofHom σ))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := σ.toAlgebra
    show Module.Flat k K
    infer_instance
  · show QuasiCompact (Spec.map (CommRingCat.ofHom σ))
    infer_instance
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (X₀ Y₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → IsPullback ψ Y.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by
  intro k K _ _ σ X Y X₀ Y₀ φ ψ hX hY hqc hqs hft f
  letI : Algebra k K := σ.toAlgebra
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) :=
    surjective_flat_quasiCompact_spMap σ
  haveI := _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc
  haveI := _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc
  haveI : QuasiCompact X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqc
  haveI : QuasiSeparated X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqs
  haveI : LocallyOfFiniteType Y₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hY.flip hσ hft
  haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k)); infer_instance
  haveI : LocallyOfFinitePresentation Y₀.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have hX' : IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) := hX
  have hΦ : (hX'.isoPullback.inv ≫ f.left ≫ ψ) ≫ Y₀.hom =
      pullback.fst X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) ≫ X₀.hom := by
    simp only [Category.assoc, hY.w, Over.w_assoc]
    rw [hX'.isoPullback_inv_snd_assoc]
    exact pullback.condition.symm
  obtain ⟨R, Ψ, hRfg, hΨ, hRΨ⟩ :=
    _root_.GlobalTheory.Spread.exists_fg_comp_eq X₀.hom Y₀.hom (hX'.isoPullback.inv ≫ f.left ≫ ψ) hΦ
  obtain ⟨s, hs⟩ := hRfg
  refine ⟨s, ?_⟩
  intro k₁ _ α β hβα hsβ X₁ Y₁ φ₁ χ ψ₁ ω hX₁ hY₁ hφ₁ hψ₁ hφ₁s hψ₁s
  letI : Algebra k k₁ := α.toAlgebra
  have hβα' : ∀ r : k, β (α r) = σ r := fun r => by rw [← hβα]; rfl
  let β' : k₁ →ₐ[k] K := { β with commutes' := fun r => hβα' r }
  have hβinj : Function.Injective β' := β.injective
  have hle : R ≤ β'.range := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hsβ hx
    exact ⟨y, rfl⟩
  let g : R →ₐ[k] k₁ :=
    (AlgEquiv.ofInjective β' hβinj).symm.toAlgHom.comp (Subalgebra.inclusion hle)
  have hg : ∀ x : R, β' (g x) = R.val x := fun x =>
    congrArg Subtype.val ((AlgEquiv.ofInjective β' hβinj).apply_symm_apply (Subalgebra.inclusion hle x))
  have hX₁' : IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hX₁
  have hY₁' : IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hY₁
  have hm : (hX₁'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom g ≫ Ψ) ≫ Y₀.hom =
      X₁.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁) := by
    simp only [Category.assoc, hΨ, _root_.GlobalTheory.Spread.bcMap_fst_assoc,
      hX₁'.isoPullback_hom_fst_assoc]
    exact hX₁'.w
  have key : φ₁ ≫ hX₁'.isoPullback.hom =
      hX'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom β' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hX₁'.isoPullback_hom_fst, hφ₁, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_fst, hX'.isoPullback_hom_fst]
    · rw [Category.assoc, hX₁'.isoPullback_hom_snd, hφ₁s, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_snd, hX'.isoPullback_hom_snd_assoc]
  refine ⟨Over.homMk (hY₁'.lift _ X₁.hom hm) (hY₁'.lift_snd _ _ _), ?_⟩
  show φ₁ ≫ hY₁'.lift _ X₁.hom hm = f.left ≫ ψ₁
  apply hY₁'.hom_ext
  · rw [Category.assoc, hY₁'.lift_fst, Category.assoc, hψ₁, reassoc_of% key,
      _root_.GlobalTheory.Spread.bcMap_comp_of_eq_assoc X₀.hom g β' R.val hg, hRΨ,
      Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hY₁'.lift_snd, hφ₁s, Category.assoc, hψ₁s, Over.w_assoc]
end _root_.GlobalTheory
end GlobalTheory
