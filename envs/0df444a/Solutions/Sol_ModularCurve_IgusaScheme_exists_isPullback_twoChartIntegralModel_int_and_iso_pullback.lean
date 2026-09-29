-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_isPullback_twoChartIntegralModel_int_and_iso_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/afad3423-a470-5029-b50e-1bce63afa3fc

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_IgusaScheme_nonempty_iso_twoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isPullback_toBase_of_isLocalization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ v : IgusaScheme N ℓ ⟶
        AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull N) (jFull N),
      IsPullback v (igusaTo N ℓ)
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ∧
      ∀ (S : Type) [CommRing S] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) S],
        ∃ I : pullback (igusaTo N ℓ)
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S))) ≅
            pullback
              (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
              (Spec.map (CommRingCat.ofHom (algebraMap ℤ S))),
          I.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
          I.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ v := by
  classical

  haveI : IsScalarTower ℤ ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) :=
    IsScalarTower.of_algebraMap_eq fun z => by simp
  haveI : (Ideal.span {(ℓ : ℤ)}).IsPrime := by
    have hq : Prime (ℓ : ℤ) := by
      rw [Int.prime_iff_natAbs_prime]
      simpa using (Fact.out : ℓ.Prime)
    exact (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := ℓ) Fact.out

  obtain ⟨e, he, -, -⟩ := ModularCurve.IgusaScheme.nonempty_iso_twoChartIntegralModel N ℓ
  obtain ⟨u, -, -, hu⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_isPullback_toBase_of_isLocalization ℤ
      ↥(modularFunctionFieldFull N) (jFull N) ↥(GaloisRep.ratLocalizedAt ℓ)
      (Ideal.span {(ℓ : ℤ)}).primeCompl

  have hsq : IsPullback (e.hom ≫ u) (igusaTo N ℓ)
      (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) := by
    have h1 : IsPullback e.hom (igusaTo N ℓ)
        (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt ℓ)
          ↥(modularFunctionFieldFull N) (jFull N)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
    simpa using h1.paste_horiz hu
  refine ⟨e.hom ≫ u, hsq, ?_⟩
  · intro S _ _
    haveI : IsScalarTower ℤ ↥(GaloisRep.ratLocalizedAt ℓ) S :=
      IsScalarTower.of_algebraMap_eq fun z => by simp
    have hcomp : Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))) =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ S)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

    have big : IsPullback
        (pullback.fst (igusaTo N ℓ)
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S))) ≫ (e.hom ≫ u))
        (pullback.snd (igusaTo N ℓ)
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S))))
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ S))) := by
      rw [← hcomp]
      exact (IsPullback.of_hasPullback _ _).paste_horiz hsq
    refine ⟨big.isoPullback, ?_, ?_⟩
    · exact big.isoPullback_hom_snd
    · exact big.isoPullback_hom_fst

end S_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback (solution)
