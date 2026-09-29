-- Prove2me | solution 1 for NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e40735bb-4b8c-5f17-8ab3-8cd00d815c2c

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes
import Theorems.Thm_NeronModelInfra_isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
import Theorems.Thm_NeronModelInfra_isIso_stalkMap_imageInc_fst_of_fst_eq
import Theorems.Thm_NeronModelInfra_exists_nhds_extension_of_isIso_stalkMap_imageInc_fst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Topology

universe u

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
    [IsIntegral Y₁]
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
  obtain ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ := hf₂

  haveI : IsLocallyNoetherian (pullback f₁ f₂) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f₁ f₂ ≫ f₁)
  haveI : CompactSpace ↥(pullback f₁ f₂) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f₁ f₂ ≫ f₁)
  haveI : IsNoetherian (pullback f₁ f₂) := {}
  haveI : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian f₁
  haveI : CompactSpace ↥Y₁ := QuasiCompact.compactSpace_of_compactSpace f₁

  set Z : Set ↥(pullback f₁ f₂) := closure (Set.range δ.base) ∩
    {q | f₁.base ((pullback.fst f₁ f₂).base q) = IsLocalRing.closedPoint R} with hZdef
  have hZclosed : IsClosed Z := isClosed_closure.inter
    ((IsLocalRing.isClosed_singleton_closedPoint (R := R)).preimage
      (f₁.continuous.comp (pullback.fst f₁ f₂).continuous))
  have hZc : IsConstructible Z :=
    isConstructible_compl.mp
      ((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZclosed.isOpen_compl)

  obtain ⟨η₀, ⟨hη₀, hη₀k⟩, hη₀₁⟩ :=
    AlgebraicGeometry.mem_image_of_mem_closure_image_of_forall_specializes (pullback.fst f₁ f₂) hZc hmem
      (fun q hq => hξ₁gen _ hq.2)

  obtain ⟨hopen, hlocus, hsupp⟩ :=
    NeronModelInfra.isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
      K gK f₁ f₂ ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩ ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ e₁ he₁ e₂ he₂ δ hδ₁ hδ₂
  have hη₀' : η₀ ∈ Set.range δ.imageι.base := by rw [hsupp]; exact hη₀
  obtain ⟨η, rfl⟩ := hη₀'

  have hiso := NeronModelInfra.isIso_stalkMap_imageInc_fst_of_fst_eq K gK f₁ f₂ ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩
    ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ e₁ he₁ e₂ he₂ ξ₁ hξ₁ hξ₁gen δ hδ₁ hδ₂ η hη₀₁

  obtain ⟨U, hU, u, hu⟩ :=
    NeronModelInfra.exists_nhds_extension_of_isIso_stalkMap_imageInc_fst K gK f₁ f₂ ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩
      ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ e₁ he₁ e₂ he₂ ξ₁ hξ₁ δ hδ₁ hδ₂ hopen hlocus η hη₀₁ hiso
  exact hne U hU u hu

end S_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral
end P2MW
export P2MW.S_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral (solution)
