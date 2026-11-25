-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.affine_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:00.206947+00:00
-- url     : https://prove2.me/submissions/958479a1-f0df-4c7a-85a7-849cb1808b91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_P2M_GlobalTheory_VeryAmplePow_appLE_congr__5ae2369cc511
import Theorems.Thm_GlobalTheory_VeryAmplePow_appTop_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {Y W : Scheme.{0}} (f : Y ⟶ W) [IsAffine W] [IsProper f] [IsLocallyNoetherian W]
    (D : Y.Opens) {σ : Type} (r : σ → Γ(Y, D)) (hD : D ≤ f ⁻¹ᵁ ⊤)
    (hval : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
      (l : Spec (.of V) ⟶ Y) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) ⁻¹ᵁ D),
      (∀ j, ∃ ρ : Γ(Spec (.of V), ⊤), (Spec.map (CommRingCat.ofHom (algebraMap V K))).appTop.hom ρ =
        ((Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l).appLE D ⊤ h).hom (r j)) → ⊤ ≤ l ⁻¹ᵁ D)
    (hmono : ∀ (Z : Scheme.{0}) [IsLocallyNoetherian Z] (x y : Z ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ D) (hy : ⊤ ≤ y ⁻¹ᵁ D),
      x ≫ f = y ≫ f → (∀ j, (x.appLE D ⊤ hx).hom (r j) = (y.appLE D ⊤ hy).hom (r j)) → x = y) :
    IsAffineOpen D ∧ Function.Surjective (MvPolynomial.eval₂Hom (f.appLE ⊤ D hD).hom r) := by
  let B : CommRingCat.{0} := .of (MvPolynomial σ Γ(W, ⊤))
  let φ : B ⟶ Γ(Y, D) := CommRingCat.ofHom (MvPolynomial.eval₂Hom (f.appLE ⊤ D hD).hom r)
  let c : Γ(W, ⊤) ⟶ B := CommRingCat.ofHom MvPolynomial.C
  let ψ : D.toScheme ⟶ Spec B := D.toSpecΓ ≫ Spec.map φ
  let π : Spec B ⟶ W := Spec.map c ≫ W.isoSpec.inv
  have hc : c ≫ φ = f.appLE ⊤ D hD := by
    ext a; exact MvPolynomial.eval₂Hom_C _ _ a
  have hπ : ψ ≫ π = D.ι ≫ f := by
    simp only [ψ, π, Category.assoc]
    rw [← Spec.map_comp_assoc, hc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, Scheme.Opens.toSpecΓ_top,
      Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id, Scheme.Hom.resLE_comp_ι]
  have hX : ∀ {Z : Scheme.{0}} (g : Z ⟶ D.toScheme) (j : σ),
      (g ≫ ψ).appTop.hom ((Scheme.ΓSpecIso B).inv.hom (MvPolynomial.X j)) =
        ((g ≫ D.ι).appLE D ⊤ (le_pre D g)).hom (r j) := by
    intro Z g j
    rw [appTop_chart, ← CommRingCat.comp_apply, Iso.inv_hom_id_assoc, CommRingCat.comp_apply]
    exact congrArg _ (MvPolynomial.eval₂Hom_X' _ _ j)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := {}
  have : CompactSpace D.toScheme := isCompact_iff_compactSpace.1 (NoetherianSpace.isCompact (D : Set Y))
  have : QuasiCompact ψ := by
    rwa [quasiCompact_iff_compactSpace]
  have : LocallyOfFiniteType (ψ ≫ π) := hπ ▸ inferInstance
  have : LocallyOfFiniteType ψ := locallyOfFiniteType_of_comp ψ π
  have : Mono ψ := by
    have : IsLocallyNoetherian (pullback ψ ψ) := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst ψ ψ)
    have e : pullback.fst ψ ψ = pullback.snd ψ ψ := by
      rw [← cancel_mono D.ι]
      refine hmono _ _ _ (le_pre D _) (le_pre D _) ?_ fun j => ?_
      · rw [Category.assoc, Category.assoc, ← hπ, pullback.condition_assoc]
      · rw [← hX, ← hX, pullback.condition]
    exact ⟨fun a b hab => by
      rw [← pullback.lift_fst a b hab, e, pullback.lift_snd]⟩
  have : UniversallyClosed ψ := by
    refine UniversallyClosed.of_valuativeCriterion ψ fun S => ?_
    have hf : ValuativeCriterion.Existence f :=
      (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
        (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
    have w := S.commSq.w
    obtain ⟨l, h₁, h₂⟩ := (hf { R := S.R, K := S.K, i₁ := S.i₁ ≫ D.ι, i₂ := S.i₂ ≫ π, commSq := ⟨by
      rw [Category.assoc, ← hπ, reassoc_of% w]⟩ }).exists_lift
    dsimp only at l h₁ h₂
    have hl : ⊤ ≤ l ⁻¹ᵁ D := by
      refine hval S.R S.K l ((le_pre D S.i₁).trans_eq (by rw [h₁])) fun j =>
        ⟨S.i₂.appTop.hom ((Scheme.ΓSpecIso B).inv.hom (MvPolynomial.X j)), ?_⟩
      have := hX S.i₁ j
      rw [w, Scheme.Hom.comp_appTop] at this
      refine Eq.trans this ?_
      rw [appLE_congr' h₁.symm]
    let l' : Spec (.of S.R) ⟶ D.toScheme := IsOpenImmersion.lift D.ι l (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hl trivial)
    have hl' : l' ≫ D.ι = l := IsOpenImmersion.lift_fac _ _ _
    have e₁ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l' = S.i₁ := by
      rw [← cancel_mono D.ι, Category.assoc, hl', h₁]
    refine ⟨⟨l', e₁, ?_⟩⟩
    have e₂ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l' ≫ ψ =
        Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ S.i₂ := by rw [← w, reassoc_of% e₁]
    obtain ⟨a, ha⟩ := Spec.map_surjective (l' ≫ ψ)
    obtain ⟨b, hb⟩ := Spec.map_surjective S.i₂
    rw [← ha, ← hb, ← Spec.map_comp, ← Spec.map_comp] at e₂
    have : Mono (CommRingCat.ofHom (algebraMap S.R S.K)) :=
      ConcreteCategory.mono_of_injective _ (IsFractionRing.injective S.R S.K)
    rw [← ha, ← hb, (cancel_mono _).1 (Spec.map_injective e₂)]
  have : IsProper ψ := {}
  have : IsClosedImmersion ψ := (IsClosedImmersion.iff_isProper_and_mono ψ).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨h₁, h₂⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ψ
  refine ⟨h₁, ?_⟩
  have e : ψ.appTop = (Scheme.ΓSpecIso B).hom ≫ φ ≫ D.topIso.inv := by
    rw [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality_assoc]
  have e' : φ = (Scheme.ΓSpecIso B).inv ≫ ψ.appTop ≫ D.topIso.hom := by
    rw [e, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  change Function.Surjective φ.hom
  rw [e', CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso D.topIso.hom).2.comp h₂).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).2
end GlobalTheory.VeryAmplePow
