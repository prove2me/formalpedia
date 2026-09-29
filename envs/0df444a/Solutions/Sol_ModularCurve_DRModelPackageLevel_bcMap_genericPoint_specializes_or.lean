-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_or
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1ff3a004-9b99-5a40-aaea-9469b26dfe71

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_or

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace ECL_SpecOr

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

private theorem isPullback_bcMap {O : Type} [CommRing O] (ρO : DRLevel.R q →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ) :
    IsPullback (DRLevel.bcMap (N₀ := N₀) ρO toκ)
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))))
      (DRLevel.XO.toBase (N₀ := N₀) ρO)
      (Spec.map (CommRingCat.ofHom toκ)) := by
  have hρι : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO) =
      Spec.map (CommRingCat.ofHom (toκ.comp ρO)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h1 : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q) _ = pullback.fst (DRLevel.toBase N₀ q) _ := by
    rw [DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
  have h2 : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ DRLevel.XO.toBase (N₀ := N₀) ρO =
      pullback.snd (DRLevel.toBase N₀ q) _ ≫ Spec.map (CommRingCat.ofHom toκ) :=
    pullback.lift_snd _ _ _
  have key : IsPullback (DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q) _)
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))) (DRLevel.toBase N₀ q)
      (Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO)) := by
    rw [h1, hρι]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right key h2 (IsPullback.of_hasPullback _ _)

variable {O : Type} [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ q] (toκ : O →+* κ)

include hϖ in

private theorem toκ_eq_zero (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) : toκ a = 0 := by
  rw [hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

include hϖ in

private theorem exists_bcMap_eq (y : ↥(DRLevel.XO (N₀ := N₀) ρO))
    (hy : y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ z, (DRLevel.bcMap (N₀ := N₀) ρO toκ).base z = y := by

  set s := (DRLevel.XO.toBase (N₀ := N₀) ρO).base y with hs
  have hps : ((q : ℕ) : O) ∈ s.asIdeal := by
    by_contra h
    exact hy h
  have hsm : s = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal O ≤ s.asIdeal := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]
      exact hps
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le s.isPrime.ne_top hle).symm

  haveI : IsLocalHom toκ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h0 : toκ a = 0 := toκ_eq_zero hϖ toκ a ((IsLocalRing.mem_maximalIdeal a).mpr hna)
    rw [h0] at ha
    exact not_isUnit_zero ha
  have hpt : (Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint κ) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint toκ
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_bcMap (N₀ := N₀) ρO toκ) y
    (IsLocalRing.closedPoint κ) (by rw [hpt])
  exact ⟨z, hz⟩

end ECL_SpecOr

open ECL_SpecOr in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (y : ↥(DRLevel.XO (N₀ := N₀) ρO)) (hy : y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    𝔛.ξinf ρO toκ ⤳ y ∨ 𝔛.ξzero ρO toκ ⤳ y := by
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  obtain ⟨z, rfl⟩ := ECL_SpecOr.exists_bcMap_eq ρO hϖ toκ y hy
  rcases 𝔛.comp_jointly_surjective κ (toκ.comp ρO) z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · left
    rw [← Scheme.Hom.comp_apply]
    exact (genericPoint_specializes c).map (Scheme.Hom.continuous _)
  · right
    rw [← Scheme.Hom.comp_apply]
    exact (genericPoint_specializes c).map (Scheme.Hom.continuous _)

end S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_or
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_or (solution)
