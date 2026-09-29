-- Prove2me | solution 1 for NeronModelInfra.exists_nhds_extension_of_isIso_stalkMap_imageInc_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e25f68cc-773f-5671-ae12-273fa5dcf1c0

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_nhds_extension_of_isIso_stalkMap_imageInc_fst

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace Ext29

theorem isLocalizationAway_of_irreducible {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ K := by
  have h := IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers ϖ) (S := K) (nonZeroDivisors R)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)) (by
      intro n hn
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hn) hϖ
      exact ⟨ϖ ^ k, (Submonoid.mem_powers_iff _ _).mpr ⟨k, rfl⟩, ↑u⁻¹,
        (by rw [mul_comm (↑u : R), mul_assoc, Units.mul_inv, mul_one] : ↑u * ϖ ^ k * ↑u⁻¹ = ϖ ^ k).symm⟩)
  exact h.mpr inferInstance

theorem isOpenImmersion_specGenericFibreInclusion {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI := isLocalizationAway_of_irreducible K hϖ
  rw [specGenericFibreInclusion_eq]
  exact IsOpenImmersion.of_isLocalization ϖ

theorem specGenericFibreInclusion_apply_ne_closedPoint {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (s : ↥(Spec (CommRingCat.of K))) :
    (specGenericFibreInclusion R K).base s ≠ IsLocalRing.closedPoint R := by
  intro h
  have h' := congrArg PrimeSpectrum.asIdeal h
  have hs : s.asIdeal = ⊥ := @Ideal.eq_bot_of_prime K _ s.asIdeal s.isPrime
  refine IsDiscreteValuationRing.not_a_field R ?_
  change (IsLocalRing.closedPoint R).asIdeal = ⊥
  rw [← h']
  change Ideal.comap (algebraMap R K) s.asIdeal = ⊥
  rw [hs, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]

end Ext29

open Ext29

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ : IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K))
    (hopen : IsOpenImmersion δ.toImage)
    (hlocus : Set.range δ.toImage.base =
      {d | f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base d)) ≠ IsLocalRing.closedPoint R})
    (η : ↥δ.image) (hη₁ : (pullback.fst f₁ f₂).base (δ.imageι.base η) = ξ₁)
    (hiso : IsIso ((δ.imageι ≫ pullback.fst f₁ f₂).stalkMap η)) :
    ∃ (U : Y₁.Opens) (_ : ξ₁ ∈ U) (u : SchemeHomOver (U.ι ≫ f₁) f₂),
      (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 ≫ e₂.1 =
        (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 ≫ e₁.1 := by
  obtain ⟨_, _, hlft₁, _⟩ := hf₁
  obtain ⟨_, _, hlft₂, _⟩ := hf₂
  haveI := hlft₁; haveI := hlft₂; haveI := hiso
  haveI : IsOpenImmersion (specGenericFibreInclusion R K) := isOpenImmersion_specGenericFibreInclusion K
  set p₁ := pullback.fst f₁ f₂ with hp₁
  set p₂ := pullback.snd f₁ f₂ with hp₂
  set F := δ.imageι ≫ p₁ with hF
  haveI : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian f₁
  haveI : LocallyOfFiniteType F := by rw [hF]; infer_instance

  obtain ⟨W, hηW, hWimm⟩ :=
    AlgebraicGeometry.exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType F η
  haveI := hWimm
  set j := W.ι ≫ F with hj

  have hover : (j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂) ≫ f₂ = j.opensRange.ι ≫ f₁ := by
    rw [Category.assoc, Category.assoc, Category.assoc, hp₂, ← pullback.condition, ← hp₁,
      ← Category.assoc δ.imageι, ← hF, ← Category.assoc W.ι, ← hj, ← Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp]
  have hover' : j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂ ≫ f₂ = j.opensRange.ι ≫ f₁ := by
    simpa only [Category.assoc] using hover
  have hjU : j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₁ = j.opensRange.ι := by
    rw [← hF, ← hj, Scheme.Hom.isoOpensRange_inv_comp]
  refine ⟨j.opensRange, ⟨⟨η, hηW⟩, ?_⟩, ⟨j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂, hover⟩, ?_⟩
  · show (W.ι ≫ δ.imageι ≫ p₁).base ⟨η, hηW⟩ = ξ₁
    exact hη₁

  set θ : pullback (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ⟶ δ.image :=
    pullback.fst (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ≫ j.isoOpensRange.inv ≫ W.ι with hθ
  have hθF : θ ≫ δ.imageι ≫ p₁ = pullback.fst (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ≫ j.opensRange.ι := by
    rw [hθ]; simp only [Category.assoc]; rw [hjU]
  have hθrange : Set.range θ.base ⊆ Set.range δ.toImage.base := by
    rintro _ ⟨q, rfl⟩
    rw [hlocus]
    show f₁.base (p₁.base (δ.imageι.base (θ.base q))) ≠ IsLocalRing.closedPoint R
    have hq : f₁.base (p₁.base (δ.imageι.base (θ.base q))) =
        (specGenericFibreInclusion R K).base ((pullback.snd (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K)).base q) := by
      change (θ ≫ δ.imageι ≫ p₁ ≫ f₁).base q = (pullback.snd (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ≫ (specGenericFibreInclusion R K)).base q
      rw [reassoc_of% hθF, pullback.condition]
    rw [hq]
    exact specGenericFibreInclusion_apply_ne_closedPoint K _
  set θ' := IsOpenImmersion.lift δ.toImage θ hθrange with hθ'
  have hθ'τ : θ' ≫ δ.toImage = θ := IsOpenImmersion.lift_fac _ _ _
  have hθ'δ : θ' ≫ δ = θ ≫ δ.imageι := by
    rw [← hθ'τ, Category.assoc, Scheme.Hom.toImage_imageι]
  have hA : θ' ≫ pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K) =
      pullback.fst (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ≫ j.opensRange.ι := by
    rw [← hδ₁, ← Category.assoc, hθ'δ, Category.assoc, hθF]
  have hB : θ' ≫ pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K) =
      pullback.fst (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ≫ (j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂) := by
    rw [← hδ₂, ← Category.assoc, hθ'δ, hθ]; simp only [Category.assoc]
  have E1 : (genericFibreRestrict R K f₁ (j.opensRange.ι ≫ f₁) ⟨j.opensRange.ι, rfl⟩).1 =
      θ' ≫ pullback.fst e₁.1 e₂.1 := by
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, Category.assoc, hA]
    · rw [genericFibreRestrict_coe_comp_snd, ← cancel_mono (specGenericFibreInclusion R K)]
      simp only [Category.assoc]
      rw [← pullback.condition, ← pullback.condition, reassoc_of% hA]
  have E2 : (genericFibreRestrict R K f₂ (j.opensRange.ι ≫ f₁)
      ⟨j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂, hover⟩).1 = θ' ≫ pullback.snd e₁.1 e₂.1 := by
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, Category.assoc, hB]
    · rw [genericFibreRestrict_coe_comp_snd, ← cancel_mono (specGenericFibreInclusion R K)]
      simp only [Category.assoc]
      rw [← pullback.condition, ← pullback.condition, reassoc_of% hB, hover']
  rw [E1, E2, Category.assoc, Category.assoc, pullback.condition]

end S_NeronModelInfra_exists_nhds_extension_of_isIso_stalkMap_imageInc_fst
end P2MW
export P2MW.S_NeronModelInfra_exists_nhds_extension_of_isIso_stalkMap_imageInc_fst (solution)
