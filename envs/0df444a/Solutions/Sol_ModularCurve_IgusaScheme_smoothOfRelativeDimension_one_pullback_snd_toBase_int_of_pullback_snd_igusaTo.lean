-- Prove2me | solution 1 for ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_pullback_snd_igusaTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2f01fc67-8890-5cdb-8e02-1bfbc7992793

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_baseChange_baseChange_of_isLocalization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_pullback_snd_igusaTo

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [CommRing k]
    (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* k)
    (h : SmoothOfRelativeDimension 1
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ)))) :
    SmoothOfRelativeDimension 1
      (pullback.snd
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by
  show SmoothOfRelativeDimension 1
    (AlgebraicCurve.TwoChartIntegralModel.baseChangeToBase ℤ ↥(modularFunctionFieldFull N) (jFull N) k)
  letI : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) k := φ.toAlgebra
  haveI : IsScalarTower ℤ ↥(GaloisRep.ratLocalizedAt ℓ) k :=
    IsScalarTower.of_algebraMap_eq fun z => by simp [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower ℤ ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) :=
    IsScalarTower.of_algebraMap_eq fun z => by simp
  haveI : (Ideal.span {(ℓ : ℤ)}).IsPrime := by
    have hq : Prime (ℓ : ℤ) := by
      rw [Int.prime_iff_natAbs_prime]
      simpa using (Fact.out : ℓ.Prime)
    exact (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := ℓ) Fact.out
  obtain ⟨u, e, -, -, he, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_baseChange_baseChange_of_isLocalization ℤ
      ↥(modularFunctionFieldFull N) (jFull N) ↥(GaloisRep.ratLocalizedAt ℓ)
      (Ideal.span {(ℓ : ℤ)}).primeCompl k
  haveI h' : SmoothOfRelativeDimension 1
      (AlgebraicCurve.TwoChartIntegralModel.baseChangeToBase ↥(GaloisRep.ratLocalizedAt ℓ)
        ↥(modularFunctionFieldFull N) (jFull N) k) := h
  rw [← (Iso.inv_comp_eq e).mpr he.symm]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (e.inv ≫ _))

end S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_pullback_snd_igusaTo
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_pullback_snd_igusaTo (solution)
