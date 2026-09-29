-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.genericFibreRestrict_surjective_of_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d29027e0-476b-511d-81f0-7dd583350bc4

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_extension_of_subset_opens
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace NGlue

theorem specGenericFibreInclusion_base_ne_closedPoint
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] (p : Spec (CommRingCat.of K)) :
    (specGenericFibreInclusion R K).base p ≠ IsLocalRing.closedPoint R := by
  intro h
  have hid : ((specGenericFibreInclusion R K).base p).asIdeal = ⊥ := by
    change (PrimeSpectrum.comap (algebraMap R K) p).asIdeal = ⊥
    rw [PrimeSpectrum.comap_asIdeal]
    have hp : p.asIdeal = ⊥ := by
      haveI := p.isPrime
      exact Ideal.eq_bot_of_prime p.asIdeal
    rw [hp, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)
  rw [h] at hid
  have hmax : IsLocalRing.maximalIdeal R = ⊥ := hid
  exact IsDiscreteValuationRing.not_isField R ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hmax)

end NGlue

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t] :
    Function.Surjective (genericFibreRestrict R K f t) := by
  intro uK
  haveI : IsProper f := hA.proper

  obtain ⟨V, v, hVη, hVs, hcompat⟩ :=
    NeronModelInfra.exists_opens_extension_of_isProper_of_smooth R K f t uK

  obtain ⟨φ, hφ⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_extension_of_subset_opens R hA t V hVη hVs v
  refine ⟨φ, ?_⟩

  have hrange : Set.range (pullback.fst t (specGenericFibreInclusion R K)).base ⊆ Set.range V.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hVη
    have hc : (pullback.fst t (specGenericFibreInclusion R K) ≫ t).base p =
        (pullback.snd t (specGenericFibreInclusion R K) ≫ specGenericFibreInclusion R K).base p := by
      rw [pullback.condition]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hc
    rw [hc]
    exact NGlue.specGenericFibreInclusion_base_ne_closedPoint R K _

  let l : pullback t (specGenericFibreInclusion R K) ⟶ (V : Scheme.{u}) :=
    IsOpenImmersion.lift V.ι (pullback.fst t (specGenericFibreInclusion R K)) hrange
  have hl : l ≫ V.ι = pullback.fst t (specGenericFibreInclusion R K) := IsOpenImmersion.lift_fac _ _ _
  let n : pullback t (specGenericFibreInclusion R K) ⟶ pullback (V.ι ≫ t) (specGenericFibreInclusion R K) :=
    pullback.lift l (pullback.snd t (specGenericFibreInclusion R K)) (by rw [← Category.assoc, hl, pullback.condition])
  let m : pullback (V.ι ≫ t) (specGenericFibreInclusion R K) ⟶ pullback t (specGenericFibreInclusion R K) :=
    pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hnm : n ≫ m = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [m, n, Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst_assoc, hl]
    · simp only [m, n, Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

  have hmφ : m ≫ (genericFibreRestrict R K f t φ).1 = (genericFibreRestrict R K f (V.ι ≫ t) v).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst, ← hφ]
      simp only [m, pullback.lift_fst_assoc, Category.assoc]
    · rw [Category.assoc, genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]
      simp only [m, pullback.lift_snd, Category.comp_id]
  apply Subtype.ext
  calc (genericFibreRestrict R K f t φ).1
      = (n ≫ m) ≫ (genericFibreRestrict R K f t φ).1 := by rw [hnm, Category.id_comp]
    _ = n ≫ (genericFibreRestrict R K f (V.ι ≫ t) v).1 := by rw [Category.assoc, hmφ]
    _ = (n ≫ m) ≫ uK.1 := by rw [hcompat, Category.assoc]
    _ = uK.1 := by rw [hnm, Category.id_comp]

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact (solution)
