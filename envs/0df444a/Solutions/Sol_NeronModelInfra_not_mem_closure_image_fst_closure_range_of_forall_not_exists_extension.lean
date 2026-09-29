-- Prove2me | solution 1 for NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/96e095d1-1fad-5b76-bdc9-5b1e25c79e8a

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk
import Theorems.Thm_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Topology

universe u

namespace NDLocGC6

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
  {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))

theorem genericFibreRestrict_comp {A B C : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of R)}
    {b : B ⟶ Spec (CommRingCat.of R)} {c : C ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver a b) (ψ : SchemeHomOver b c) :
    (genericFibreRestrict R K c a (schemeHomOverComp φ ψ)).1 =
      (genericFibreRestrict R K b a φ).1 ≫ (genericFibreRestrict R K c b ψ).1 := by
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst, Category.assoc, genericFibreRestrict_coe_comp_fst,
      ← Category.assoc, genericFibreRestrict_coe_comp_fst, Category.assoc]
    rfl
  · rw [genericFibreRestrict_coe_comp_snd, Category.assoc, genericFibreRestrict_coe_comp_snd,
      genericFibreRestrict_coe_comp_snd]

theorem genericFibreRestrict_congr {A B : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of R)}
    {b : B ⟶ Spec (CommRingCat.of R)} (φ ψ : SchemeHomOver a b) (h : φ.1 = ψ.1) :
    (genericFibreRestrict R K b a φ).1 = (genericFibreRestrict R K b a ψ).1 := by
  have : φ = ψ := Subtype.ext h
  subst this
  rfl

end NDLocGC6

open NDLocGC6 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ : IsIso e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (hξ₁gen : ∀ y : ↥Y₁, f₁.base y = IsLocalRing.closedPoint R → ξ₁ ⤳ y)
    (hne : ∀ (U : Y₁.Opens), ξ₁ ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f₁) f₂,
      (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 ≫ e₂.1 ≠
        (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 ≫ e₁.1)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) :
    ξ₁ ∉ closure ((pullback.fst f₁ f₂).base ''
      (closure (Set.range δ.base) ∩
        {q | f₁.base ((pullback.fst f₁ f₂).base q) = IsLocalRing.closedPoint R})) := by
  intro hmem
  obtain ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩ := hf₁
  haveI := he₁
  haveI := he₂

  haveI : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian f₁
  haveI : CompactSpace ↥Y₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  haveI : IsNoetherian Y₁ := {}
  have hdom : ∀ x : ↥Y₁, IsDomain (Y₁.presheaf.stalk x) := fun x =>
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R f₁ x).1
  obtain ⟨hUopen, -⟩ := AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk hdom ξ₁
  let U₁ : Y₁.Opens := ⟨irreducibleComponent ξ₁, hUopen⟩
  have hξU : ξ₁ ∈ U₁ := mem_irreducibleComponent
  haveI : IsReduced Y₁ := by
    haveI : ∀ x : ↥Y₁, _root_.IsReduced (Y₁.presheaf.stalk x) := fun x => inferInstance
    exact isReduced_of_isReduced_stalk Y₁
  haveI : IrreducibleSpace ↥(U₁ : Scheme.{u}) :=
    Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := ξ₁))
  haveI : IsIntegral (U₁ : Scheme.{u}) := isIntegral_of_irreducibleSpace_of_isReduced _

  let f₁' : (U₁ : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := U₁.ι ≫ f₁
  have hf₁' : Smooth f₁' ∧ IsSeparated f₁' ∧ LocallyOfFiniteType f₁' ∧ QuasiCompact f₁' := by
    haveI : TopologicalSpace.NoetherianSpace ↥(U₁ : Scheme.{u}) :=
      (inferInstance : TopologicalSpace.NoetherianSpace (U₁ : Set ↥Y₁))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  let ρ : SchemeHomOver f₁' f₁ := ⟨U₁.ι, rfl⟩
  let r := (genericFibreRestrict R K f₁ f₁' ρ).1
  have hr : r ≫ pullback.fst f₁ (specGenericFibreInclusion R K) =
      pullback.fst f₁' (specGenericFibreInclusion R K) ≫ U₁.ι :=
    genericFibreRestrict_coe_comp_fst f₁ f₁' ρ
  haveI hI : IsOpenImmersion (specGenericFibreInclusion R K) := by

    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    haveI : IsLocalization.Away ϖ K := by
      refine (isLocalization_iff (Submonoid.powers ϖ) K).mpr ⟨?_, ?_, ?_⟩
      · rintro ⟨y, n, rfl⟩
        exact isUnit_iff_ne_zero.mpr
          ((IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr (pow_ne_zero n hϖ.ne_zero))
      · intro z
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
        have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
        obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
        refine ⟨⟨a * ↑v⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
        have hbK : algebraMap R K b ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr hb0
        rw [div_mul_eq_mul_div, div_eq_iff hbK, ← map_mul, ← map_mul, hv]
        congr 1
        rw [mul_assoc, ← mul_assoc (↑v⁻¹ : R), Units.inv_mul, one_mul]
      · intro x y h
        exact ⟨1, by rw [IsFractionRing.injective R K h]⟩
    rw [specGenericFibreInclusion_eq]
    exact IsOpenImmersion.of_isLocalization ϖ
  haveI hro : IsOpenImmersion r := by
    haveI : IsOpenImmersion (r ≫ pullback.fst f₁ (specGenericFibreInclusion R K)) := by
      rw [hr]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst f₁ (specGenericFibreInclusion R K))
  let e₁' : SchemeHomOver (pullback.snd f₁' (specGenericFibreInclusion R K)) gK :=
    schemeHomOverComp (genericFibreRestrict R K f₁ f₁' ρ) e₁
  have he₁' : IsOpenImmersion e₁'.1 := by
    change IsOpenImmersion (r ≫ e₁.1); infer_instance
  let ξ₁' : ↥(U₁ : Scheme.{u}) := ⟨ξ₁, hξU⟩
  have hξ₁' : f₁'.base ξ₁' = IsLocalRing.closedPoint R := by
    change f₁.base (U₁.ι.base ξ₁') = _
    rw [Scheme.Opens.ι_apply]; exact hξ₁
  have hξ₁gen' : ∀ y : ↥(U₁ : Scheme.{u}), f₁'.base y = IsLocalRing.closedPoint R → ξ₁' ⤳ y := by
    intro y hy
    exact (U₁.ι.isOpenEmbedding.isEmbedding.toIsInducing.specializes_iff).mp (hξ₁gen y.1 hy)

  have hcond : (pullback.fst e₁'.1 e₂.1 ≫ pullback.fst f₁' (specGenericFibreInclusion R K)) ≫ f₁' =
      (pullback.snd e₁'.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) ≫ f₂ := by
    have hi : pullback.fst e₁'.1 e₂.1 ≫ pullback.snd f₁' (specGenericFibreInclusion R K) =
        (pullback.fst e₁'.1 e₂.1 ≫ e₁'.1) ≫ gK := by rw [Category.assoc, e₁'.2]
    have hj : pullback.snd e₁'.1 e₂.1 ≫ pullback.snd f₂ (specGenericFibreInclusion R K) =
        (pullback.snd e₁'.1 e₂.1 ≫ e₂.1) ≫ gK := by rw [Category.assoc, e₂.2]
    rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition, ← Category.assoc,
      ← Category.assoc, hi, hj, pullback.condition]
  let δ' : pullback e₁'.1 e₂.1 ⟶ pullback f₁' f₂ :=
    pullback.lift (pullback.fst e₁'.1 e₂.1 ≫ pullback.fst f₁' (specGenericFibreInclusion R K))
      (pullback.snd e₁'.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) hcond
  have hδ'₁ : δ' ≫ pullback.fst f₁' f₂ = pullback.fst e₁'.1 e₂.1 ≫ pullback.fst f₁' _ := pullback.lift_fst _ _ _
  have hδ'₂ : δ' ≫ pullback.snd f₁' f₂ = pullback.snd e₁'.1 e₂.1 ≫ pullback.fst f₂ _ := pullback.lift_snd _ _ _

  let m : pullback f₁' f₂ ⟶ pullback f₁ f₂ :=
    pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) rfl (by rw [Category.comp_id, Category.id_comp])
  let s : pullback e₁'.1 e₂.1 ⟶ pullback e₁.1 e₂.1 :=
    pullback.map _ _ _ _ r (𝟙 _) (𝟙 XK) (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id, Category.id_comp])
  have hsm : δ' ≫ m = s ≫ δ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hδ₁]
      change δ' ≫ pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) _ _ ≫ pullback.fst f₁ f₂ =
        pullback.map _ _ _ _ r (𝟙 _) (𝟙 XK) _ _ ≫ pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ _
      rw [pullback.lift_fst, ← Category.assoc, hδ'₁, ← Category.assoc, pullback.lift_fst, Category.assoc,
        Category.assoc, hr]
    · rw [Category.assoc, Category.assoc, hδ₂]
      change δ' ≫ pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) _ _ ≫ pullback.snd f₁ f₂ =
        pullback.map _ _ _ _ r (𝟙 _) (𝟙 XK) _ _ ≫ pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ _
      rw [pullback.lift_snd, ← Category.assoc, hδ'₂, ← Category.assoc, pullback.lift_snd]
      simp only [Category.comp_id]

  have hne' : ∀ (U' : (U₁ : Scheme.{u}).Opens), ξ₁' ∈ U' → ∀ u' : SchemeHomOver (U'.ι ≫ f₁') f₂,
      (genericFibreRestrict R K f₂ (U'.ι ≫ f₁') u').1 ≫ e₂.1 ≠
        (genericFibreRestrict R K f₁' (U'.ι ≫ f₁') ⟨U'.ι, rfl⟩).1 ≫ e₁'.1 := by
    intro U' hU' u' heq'
    let U : Y₁.Opens := U₁.ι ''ᵁ U'
    have hU : ξ₁ ∈ U := ⟨ξ₁', hU', rfl⟩
    let ε := U₁.ι.isoImage U'
    let u : SchemeHomOver (U.ι ≫ f₁) f₂ := ⟨ε.inv ≫ u'.1, by
      rw [Category.assoc, u'.2, ← Category.assoc, ← Category.assoc]
      change (ε.inv ≫ U'.ι ≫ U₁.ι) ≫ f₁ = _
      rw [Scheme.Hom.isoImage_inv_ι]⟩
    let κ : SchemeHomOver (U.ι ≫ f₁) (U'.ι ≫ f₁') := ⟨ε.inv, by
      change ε.inv ≫ U'.ι ≫ U₁.ι ≫ f₁ = _
      rw [← Category.assoc U'.ι, ← Category.assoc, Scheme.Hom.isoImage_inv_ι]⟩
    apply hne U hU u
    have h1 : (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 =
        (genericFibreRestrict R K (U'.ι ≫ f₁') (U.ι ≫ f₁) κ).1 ≫
          (genericFibreRestrict R K f₂ (U'.ι ≫ f₁') u').1 := by
      rw [← genericFibreRestrict_comp]
      rfl
    have h2 : (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 =
        (genericFibreRestrict R K (U'.ι ≫ f₁') (U.ι ≫ f₁) κ).1 ≫
          (genericFibreRestrict R K f₁' (U'.ι ≫ f₁') ⟨U'.ι, rfl⟩).1 ≫
            (genericFibreRestrict R K f₁ f₁' ρ).1 := by
      have h2' : (genericFibreRestrict R K (U'.ι ≫ f₁') (U.ι ≫ f₁) κ).1 ≫
          (genericFibreRestrict R K f₁' (U'.ι ≫ f₁') ⟨U'.ι, rfl⟩).1 ≫
            (genericFibreRestrict R K f₁ f₁' ρ).1 =
          (genericFibreRestrict R K f₁ (U.ι ≫ f₁)
            (schemeHomOverComp κ (schemeHomOverComp (⟨U'.ι, rfl⟩ : SchemeHomOver (U'.ι ≫ f₁') f₁') ρ))).1 := by
        rw [genericFibreRestrict_comp, genericFibreRestrict_comp]
      rw [h2']
      exact genericFibreRestrict_congr K _ _ (Scheme.Hom.isoImage_inv_ι U₁.ι U').symm
    rw [h1, h2, Category.assoc, heq', Category.assoc, Category.assoc]
    rfl

  have key := NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral
    K gK f₁' f₂ hf₁' hf₂ e₁' he₁' e₂ he₂ ξ₁' hξ₁' hξ₁gen' hne' δ' hδ'₁ hδ'₂
  apply key

  haveI : IsOpenImmersion m := by dsimp only [m]; infer_instance
  have hrm : Set.range m.base = (pullback.fst f₁ f₂).base ⁻¹' (U₁ : Set ↥Y₁) := by
    have := Scheme.Pullback.range_map f₁' f₂ f₁ f₂ U₁.ι (𝟙 Y₂) (𝟙 _) rfl
      (by rw [Category.comp_id, Category.id_comp])
    rw [Scheme.Opens.range_ι] at this
    change Set.range m.base = _ at this
    rw [this]
    ext q; constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, ⟨(pullback.snd f₁ f₂).base q, rfl⟩⟩
  have hrr : Set.range r.base =
      (pullback.fst f₁ (specGenericFibreInclusion R K)).base ⁻¹' (U₁ : Set ↥Y₁) := by
    apply le_antisymm
    · rintro _ ⟨z', rfl⟩
      show (pullback.fst f₁ (specGenericFibreInclusion R K)).base (r.base z') ∈ (U₁ : Set ↥Y₁)
      rw [← Scheme.Hom.comp_apply, hr, Scheme.Hom.comp_apply]
      exact (pullback.fst f₁' (specGenericFibreInclusion R K) z').2
    · intro z hz
      obtain ⟨v, hv⟩ : (pullback.fst f₁ (specGenericFibreInclusion R K)).base z ∈ Set.range U₁.ι.base := by
        rw [Scheme.Opens.range_ι]; exact hz
      have hv' : v ∈ Set.range (pullback.fst f₁' (specGenericFibreInclusion R K)).base := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨(pullback.snd f₁ (specGenericFibreInclusion R K)).base z, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
        show f₁.base ((pullback.fst f₁ (specGenericFibreInclusion R K)).base z) = (U₁.ι ≫ f₁).base v
        rw [Scheme.Hom.comp_apply, hv]
      obtain ⟨z', hz'⟩ := hv'
      refine ⟨z', (pullback.fst f₁ (specGenericFibreInclusion R K)).isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hr, Scheme.Hom.comp_apply, hz', hv]
  have hmδ : m.base ⁻¹' Set.range δ.base = Set.range δ'.base := by
    apply le_antisymm
    · rintro q' ⟨x, hx⟩
      have hxs : x ∈ Set.range s.base := by
        have := Scheme.Pullback.range_map e₁'.1 e₂.1 e₁.1 e₂.1 r (𝟙 _) (𝟙 XK)
          (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id, Category.id_comp])
        change Set.range s.base = _ at this
        rw [this]
        refine ⟨?_, ⟨(pullback.snd e₁.1 e₂.1).base x, rfl⟩⟩
        show (pullback.fst e₁.1 e₂.1).base x ∈ Set.range r.base
        rw [hrr]
        show (pullback.fst f₁ (specGenericFibreInclusion R K)).base ((pullback.fst e₁.1 e₂.1).base x) ∈ (U₁ : Set ↥Y₁)
        rw [← Scheme.Hom.comp_apply, ← hδ₁, Scheme.Hom.comp_apply, hx]
        exact (show m.base q' ∈ Set.range m.base from ⟨q', rfl⟩) |> fun h => by rw [hrm] at h; exact h
      obtain ⟨x', rfl⟩ := hxs
      refine ⟨x', m.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hsm, Scheme.Hom.comp_apply, hx]
    · rintro _ ⟨x', rfl⟩
      refine ⟨s.base x', ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hsm, Scheme.Hom.comp_apply]
  have hmcl : m.base ⁻¹' closure (Set.range δ.base) = closure (Set.range δ'.base) := by
    rw [m.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage m.continuous, hmδ]

  set A : Set ↥Y₁ := (pullback.fst f₁ f₂).base ''
      (closure (Set.range δ.base) ∩ {q | f₁.base ((pullback.fst f₁ f₂).base q) = IsLocalRing.closedPoint R})
    with hA
  set A' : Set ↥(U₁ : Scheme.{u}) := (pullback.fst f₁' f₂).base ''
      (closure (Set.range δ'.base) ∩ {q | f₁'.base ((pullback.fst f₁' f₂).base q) = IsLocalRing.closedPoint R})
    with hA'
  have hAA' : (U₁ : Set ↥Y₁) ∩ A ⊆ U₁.ι.base '' A' := by
    rintro y ⟨hyU, ⟨q, ⟨hq, hqk⟩, rfl⟩⟩
    have hqm : q ∈ Set.range m.base := by rw [hrm]; exact hyU
    obtain ⟨q', rfl⟩ := hqm
    refine ⟨(pullback.fst f₁' f₂).base q', ⟨q', ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · rw [← hmcl]; exact hq
    · change f₁.base (U₁.ι.base ((pullback.fst f₁' f₂).base q')) = _
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      change ((pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) _ _ ≫ pullback.fst f₁ f₂) ≫ f₁) q' = _ at hqk
      rwa [pullback.lift_fst, Category.assoc] at hqk
    · symm
      rw [← Scheme.Hom.comp_apply]
      change (pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) _ _ ≫ pullback.fst f₁ f₂) q' = _
      rw [pullback.lift_fst, Scheme.Hom.comp_apply]
  have h1 : ξ₁ ∈ closure ((U₁ : Set ↥Y₁) ∩ A) := U₁.2.inter_closure ⟨hξU, hmem⟩
  have h2 : ξ₁ ∈ closure (U₁.ι.base '' A') := closure_mono hAA' h1
  have h3 : ξ₁' ∈ U₁.ι.base ⁻¹' closure (U₁.ι.base '' A') := h2
  rwa [← U₁.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image] at h3

end S_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension
end P2MW
export P2MW.S_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension (solution)
