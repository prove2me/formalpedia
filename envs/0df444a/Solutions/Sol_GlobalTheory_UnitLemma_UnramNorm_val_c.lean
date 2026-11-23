-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnramNorm.val_c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:39.745997+00:00
-- url     : https://prove2.me/submissions/533f89d0-3324-4b7c-917b-8f59c6f2830e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_cO_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.UnitLemma.UnramNorm
open IsLocalRing Polynomial
variable (K : UQ)
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
private theorem valuation_algebraMap_isUnit_eq_one (u : K.O) (hu : IsUnit u) :
    IsDedekindDomain.HeightOneSpectrum.valuation K.E (IsDiscreteValuationRing.maximalIdeal K.O)
      (algebraMap K.O K.E u) = 1 := by
  obtain ⟨w, rfl⟩ := hu
  set v := IsDedekindDomain.HeightOneSpectrum.valuation K.E (IsDiscreteValuationRing.maximalIdeal K.O)
  have h1 := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one (K := K.E) (w : K.O)
  have h2 := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one (K := K.E) ((w⁻¹ : K.Oˣ) : K.O)
  have h3 : v (algebraMap K.O K.E w) * v (algebraMap K.O K.E ((w⁻¹ : K.Oˣ) : K.O)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  exact le_antisymm h1 (by
    by_contra h
    push_neg at h
    have := mul_lt_one_of_lt_of_le h h2
    rw [h3] at this
    exact lt_irrefl _ this)
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
private theorem valuation_algebraMap_irreducible_eq {p p' : K.O} (hp : Irreducible p)
    (hp' : Irreducible p') :
    IsDedekindDomain.HeightOneSpectrum.valuation K.E (IsDiscreteValuationRing.maximalIdeal K.O)
      (algebraMap K.O K.E p') =
    IsDedekindDomain.HeightOneSpectrum.valuation K.E (IsDiscreteValuationRing.maximalIdeal K.O)
      (algebraMap K.O K.E p) := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible K.O hp hp'
  rw [← hw, map_mul, map_mul, valuation_algebraMap_isUnit_eq_one K _ w.isUnit, mul_one]
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
private theorem valuation_algebraMap_cO (a : K.O) :
    IsDedekindDomain.HeightOneSpectrum.valuation K.E (IsDiscreteValuationRing.maximalIdeal K.O)
      (algebraMap K.O K.E (_root_.GlobalTheory.UnitLemma.UnramNorm.cO K a)) =
    IsDedekindDomain.HeightOneSpectrum.valuation K.E (IsDiscreteValuationRing.maximalIdeal K.O)
      (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hcϖ : Irreducible (_root_.GlobalTheory.UnitLemma.UnramNorm.cO K ϖ) :=
    (MulEquiv.irreducible_iff (_root_.GlobalTheory.UnitLemma.UnramNorm.cO K).toMulEquiv).mpr hϖ
  simp only [map_mul, map_pow]
  rw [valuation_algebraMap_isUnit_eq_one K _ (u.isUnit.map (_root_.GlobalTheory.UnitLemma.UnramNorm.cO K)),
    valuation_algebraMap_isUnit_eq_one K _ u.isUnit, valuation_algebraMap_irreducible_eq K hϖ hcϖ]
end GlobalTheory.UnitLemma.UnramNorm
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnramNorm
open IsLocalRing Polynomial
variable (K : UQ)
open IsLocalRing Polynomial
variable (K : _root_.GlobalTheory.UnitLemma.UQ)
namespace GlobalTheory.UnitLemma.UnramNorm
namespace _root_.GlobalTheory.UnitLemma.UnramNorm
theorem _root_.solution (x : K.E) :
    _root_.GlobalTheory.UnitLemma.val K.O (K.c x) = _root_.GlobalTheory.UnitLemma.val K.O x := by
  unfold _root_.GlobalTheory.UnitLemma.val
  congr 2
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K.O) x
  rw [map_div₀, ← _root_.GlobalTheory.UnitLemma.UnramNorm.cO_spec, ← _root_.GlobalTheory.UnitLemma.UnramNorm.cO_spec,
    map_div₀, map_div₀, valuation_algebraMap_cO, valuation_algebraMap_cO]
end _root_.GlobalTheory.UnitLemma.UnramNorm
end GlobalTheory.UnitLemma.UnramNorm
