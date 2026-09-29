-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/990bf06a-aa2c-5f0a-9833-96e291e54512

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff
import Theorems.Thm_ModularCurve_UVCrossingModel_leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf
import Theorems.Thm_ModularCurve_UVCrossingModel_norm_quotient_span_eq_finprod_norm_quotient_pow_length
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff

set_option autoImplicit false

universe u

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const inU inV nfCoeff dominantIndices isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete setOf_horizontal_mem_finite U_mul_V free_finite_finrank_quotient_span_of_isUnit_coeff leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf norm_quotient_span_eq_finprod_norm_quotient_pow_length"
p2m_open "ModularCurve.UVCrossingModel ModularCurve"

open IsLocalRing

section LeadingResidue

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ϖ : W) (hϖ : Irreducible ϖ)
include hϖ

theorem multiplicity_eq_and_unitPart_eq_of_eq_pow_mul {c u : W} {n : ℕ} (hu : IsUnit u) (h : c = ϖ ^ n * u) :
    multiplicity ϖ c = n ∧ unitPart ϖ c = u := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hmul : multiplicity ϖ c = n := by
    apply multiplicity_eq_of_dvd_of_not_dvd
    · exact ⟨u, h⟩
    · rintro ⟨t, ht⟩
      apply hϖ.not_isUnit
      apply isUnit_of_dvd_unit _ hu
      refine ⟨t, mul_left_cancel₀ (pow_ne_zero n hϖ0) ?_⟩
      rw [← h, ht, pow_succ, mul_assoc]
  refine ⟨hmul, ?_⟩
  have h2 := pow_multiplicity_mul_unitPart ϖ c
  rw [hmul] at h2
  exact mul_left_cancel₀ (pow_ne_zero n hϖ0) (h2.trans h)

theorem exists_eq_pow_mul_of_ne_zero {c : W} (hc : c ≠ 0) : ∃ (n : ℕ) (u : W), IsUnit u ∧ c = ϖ ^ n * u := by
  obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  exact ⟨n, u, u.isUnit, h.trans (mul_comm _ _)⟩

theorem isUnit_unitPart {c : W} (hc : c ≠ 0) : IsUnit (unitPart ϖ c) := by
  obtain ⟨n, u, hu, h⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  rw [(multiplicity_eq_and_unitPart_eq_of_eq_pow_mul ϖ hϖ hu h).2]
  exact hu

omit hϖ in
theorem leadingResidue_of_ne_zero {c : W} (hc : c ≠ 0) : leadingResidue ϖ c = residue W (unitPart ϖ c) := by
  rw [leadingResidue, if_neg hc]

theorem leadingResidue_eq_zero_iff (c : W) : leadingResidue ϖ c = 0 ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [leadingResidue_of_ne_zero ϖ hc, residue_eq_zero_iff] at h
    exact h (isUnit_unitPart ϖ hϖ hc)
  · rintro rfl
    rw [leadingResidue, if_pos rfl]

theorem leadingResidue_pow_mul_of_isUnit {u : W} (hu : IsUnit u) (n : ℕ) :
    leadingResidue ϖ (ϖ ^ n * u) = residue W u := by
  have hne : ϖ ^ n * u ≠ 0 := mul_ne_zero (pow_ne_zero n hϖ.ne_zero) hu.ne_zero
  rw [leadingResidue_of_ne_zero ϖ hne, (multiplicity_eq_and_unitPart_eq_of_eq_pow_mul ϖ hϖ hu rfl).2]

theorem leadingResidue_of_isUnit {u : W} (hu : IsUnit u) : leadingResidue ϖ u = residue W u := by
  simpa using leadingResidue_pow_mul_of_isUnit ϖ hϖ hu 0

theorem leadingResidue_mul (c d : W) : leadingResidue ϖ (c * d) = leadingResidue ϖ c * leadingResidue ϖ d := by
  by_cases hc : c = 0
  · rw [hc, zero_mul, (leadingResidue_eq_zero_iff ϖ hϖ 0).2 rfl, zero_mul]
  by_cases hd : d = 0
  · rw [hd, mul_zero, (leadingResidue_eq_zero_iff ϖ hϖ 0).2 rfl, mul_zero]
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  obtain ⟨n, v, hv, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hd
  rw [show ϖ ^ m * u * (ϖ ^ n * v) = ϖ ^ (m + n) * (u * v) by ring, leadingResidue_pow_mul_of_isUnit ϖ hϖ (hu.mul hv),
    leadingResidue_pow_mul_of_isUnit ϖ hϖ hu, leadingResidue_pow_mul_of_isUnit ϖ hϖ hv, map_mul]

theorem leadingResidue_uniformizer_pow_mul (n : ℕ) (c : W) : leadingResidue ϖ (ϖ ^ n * c) = leadingResidue ϖ c := by
  by_cases hc : c = 0
  · rw [hc, mul_zero]
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  rw [show ϖ ^ n * (ϖ ^ m * u) = ϖ ^ (n + m) * u by ring, leadingResidue_pow_mul_of_isUnit ϖ hϖ hu,
    leadingResidue_pow_mul_of_isUnit ϖ hϖ hu]

theorem leadingResidue_neg (c : W) : leadingResidue ϖ (-c) = -leadingResidue ϖ c := by
  by_cases hc : c = 0
  · rw [hc, neg_zero, (leadingResidue_eq_zero_iff ϖ hϖ 0).2 rfl, neg_zero]
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  rw [← mul_neg, leadingResidue_pow_mul_of_isUnit ϖ hϖ hu.neg, leadingResidue_pow_mul_of_isUnit ϖ hϖ hu, map_neg]

theorem leadingResidue_add_of_addVal_lt {c d : W}
    (h : IsDiscreteValuationRing.addVal W c < IsDiscreteValuationRing.addVal W d) :
    leadingResidue ϖ (c + d) = leadingResidue ϖ c := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [IsDiscreteValuationRing.addVal_zero] at h
    exact not_top_lt h
  by_cases hd : d = 0
  · rw [hd, add_zero]
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  obtain ⟨n, v, hv, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hd
  have hm : IsDiscreteValuationRing.addVal W (ϖ ^ m * u) = m :=
    IsDiscreteValuationRing.addVal_def _ hu.unit hϖ m (by rw [IsUnit.unit_spec, mul_comm])
  have hn : IsDiscreteValuationRing.addVal W (ϖ ^ n * v) = n :=
    IsDiscreteValuationRing.addVal_def _ hv.unit hϖ n (by rw [IsUnit.unit_spec, mul_comm])
  rw [hm, hn] at h
  have hmn : m < n := by exact_mod_cast h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn

  have hsum : ϖ ^ m * u + ϖ ^ (m + k + 1) * v = ϖ ^ m * (u + ϖ ^ (k + 1) * v) := by ring
  have hmem : ϖ ^ (k + 1) * v ∈ maximalIdeal W := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).2 hϖ.not_isUnit))
  have hres : residue W (u + ϖ ^ (k + 1) * v) = residue W u := by
    rw [map_add, (residue_eq_zero_iff _).2 hmem, add_zero]
  have hu' : IsUnit (u + ϖ ^ (k + 1) * v) := by
    rw [← residue_ne_zero_iff_isUnit, hres]
    exact (residue_ne_zero_iff_isUnit u).2 hu
  rw [show m + k + 1 = m + (k + 1) by ring] at hsum ⊢
  rw [show ϖ ^ m * u + ϖ ^ (m + (k + 1)) * v = ϖ ^ m * (u + ϖ ^ (k + 1) * v) by ring,
    leadingResidue_pow_mul_of_isUnit ϖ hϖ hu', leadingResidue_pow_mul_of_isUnit ϖ hϖ hu, hres]

end LeadingResidue

end ModularCurve.UVCrossingModel

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const inU inV nfCoeff dominantIndices isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete setOf_horizontal_mem_finite U_mul_V free_finite_finrank_quotient_span_of_isUnit_coeff leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf norm_quotient_span_eq_finprod_norm_quotient_pow_length"
p2m_open "ModularCurve.UVCrossingModel ModularCurve"

section AResidueAlgebra

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ϖ : W) (hϖ : Irreducible ϖ)
include hϖ

theorem leadingResidue_one : leadingResidue ϖ (1 : W) = 1 := by
  rw [leadingResidue_of_isUnit ϖ hϖ isUnit_one, map_one]

theorem leadingResidue_prod {ι : Type*} (s : Finset ι) (f : ι → W) :
    leadingResidue ϖ (∏ i ∈ s, f i) = ∏ i ∈ s, leadingResidue ϖ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, leadingResidue_one ϖ hϖ]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, leadingResidue_mul ϖ hϖ, ih]

theorem leadingResidue_pow (c : W) (n : ℕ) : leadingResidue ϖ (c ^ n) = leadingResidue ϖ c ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, leadingResidue_one ϖ hϖ]
  | succ n ih => rw [pow_succ, pow_succ, leadingResidue_mul ϖ hϖ, ih]

end AResidueAlgebra

end ModularCurve.UVCrossingModel

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff.ModularCurve _root_.ModularCurve.UVCrossingModel _root_.P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hgood0 : ∃ i, IsUnit (PowerSeries.coeff i ab.1))
    (hgoodE : IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) :
    leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) *
        ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
          (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
          residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
            (Module.length (Localization.AtPrime Q.asIdeal)
              (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat =
      (-1) ^ (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
          sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)).toNat *
        leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) := by
  classical
  haveI : IsDomain (UVCrossingModel W (ϖ ^ e)) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he).1
  obtain ⟨hfree, hfinite, hrk⟩ := free_finite_finrank_quotient_span_of_isUnit_coeff ϖ hϖ e he x hx ab hb habx hgood0 hgoodE
  haveI := hfree
  haveI := hfinite
  have hsym := leadingResidue_charpoly_coeff_zero_mul_leadingResidue_nfCoeff_sInf ϖ hϖ e he x hx ab hb habx hgood0 hgoodE hrk
  set h := Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) with hh
  set χ := (LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly with hχ

  have hNU : Algebra.norm W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e))) = (-1) ^ h * χ.coeff 0 := by
    rw [Algebra.norm_apply]
    have e1 : (Algebra.lmul W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e))) :
        (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) =
        LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e))) := LinearMap.ext fun _ => rfl
    rw [e1, LinearMap.det_eq_sign_charpoly_coeff]
  have hNUV : Algebra.norm W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e))) *
      Algebra.norm W (Ideal.Quotient.mk (Ideal.span {x}) (V (ϖ ^ e))) = (ϖ ^ e) ^ h := by
    have hc : Ideal.Quotient.mk (Ideal.span {x}) (const (ϖ ^ e) (ϖ ^ e)) = _ :=
      Ideal.Quotient.mk_algebraMap W (Ideal.span {x}) (ϖ ^ e)
    rw [← map_mul, ← map_mul, U_mul_V, hc, Algebra.norm_algebraMap]

  have hSfin := setOf_horizontal_mem_finite ϖ hϖ e he x hx
  have hbr := norm_quotient_span_eq_finprod_norm_quotient_pow_length ϖ hϖ e he x hx (V (ϖ ^ e))
  change _ = ∏ᶠ Q ∈ {Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) | Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal}, _ at hbr
  rw [finprod_mem_eq_finite_toFinset_prod _ hSfin] at hbr
  change leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) * ∏ᶠ Q ∈ {Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) | Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal},
      IsLocalRing.residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^ (Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat = _
  rw [finprod_mem_eq_finite_toFinset_prod _ hSfin]

  set P := ∏ Q ∈ hSfin.toFinset,
    leadingResidue ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e)))) ^ (Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat with hPdef
  have hP : leadingResidue ϖ (Algebra.norm W (Ideal.Quotient.mk (Ideal.span {x}) (V (ϖ ^ e)))) = P := by
    rw [hbr, leadingResidue_prod ϖ hϖ]
    exact Finset.prod_congr rfl fun Q _ => leadingResidue_pow ϖ hϖ _ _
  have hsign : leadingResidue ϖ ((-1 : W) ^ h) = (-1) ^ h := by
    rw [leadingResidue_of_isUnit ϖ hϖ (isUnit_one.neg.pow h), map_pow, map_neg, map_one]
  have key : (-1) ^ h * leadingResidue ϖ (χ.coeff 0) * P = 1 := by
    have h1 := congrArg (leadingResidue ϖ) hNUV
    rw [leadingResidue_mul ϖ hϖ, hNU, leadingResidue_mul ϖ hϖ, hsign, hP, ← pow_mul, ← mul_one (ϖ ^ (e * h)),
      leadingResidue_pow_mul_of_isUnit ϖ hϖ isUnit_one, map_one] at h1
    exact h1
  have key2 : leadingResidue ϖ (χ.coeff 0) * P = (-1) ^ h := by
    have hsq : ((-1 : IsLocalRing.ResidueField W) ^ h) * (-1) ^ h = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc leadingResidue ϖ (χ.coeff 0) * P = ((-1) ^ h * (-1) ^ h) * (leadingResidue ϖ (χ.coeff 0) * P) := by
          rw [hsq, one_mul]
      _ = (-1) ^ h * ((-1) ^ h * leadingResidue ϖ (χ.coeff 0) * P) := by ring
      _ = (-1) ^ h := by rw [key, mul_one]

  have hP0 : P ≠ 0 := by
    intro h0; rw [h0, mul_zero] at key2; exact (pow_ne_zero h (neg_ne_zero.mpr one_ne_zero)) key2.symm
  have hP' : ∏ Q ∈ hSfin.toFinset,
      IsLocalRing.residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^ (Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat = P := by
    refine Finset.prod_congr rfl fun Q hQ => ?_
    rcases Nat.eq_zero_or_pos (Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat with hl | hl
    · rw [hl, pow_zero, pow_zero]
    · have hfac : leadingResidue ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e)))) ^ (Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp (hPdef ▸ hP0)) Q hQ
      have hne : Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))) ≠ 0 := by
        intro h0
        apply hfac
        rw [h0, (leadingResidue_eq_zero_iff ϖ hϖ 0).mpr rfl, zero_pow (by omega)]
      rw [← leadingResidue_of_ne_zero ϖ hne]
  rw [hP']

  have htoNat : (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) - sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)).toNat = h := by
    rw [← hrk, Int.toNat_natCast]
  rw [htoNat, ← hsym]
  calc leadingResidue ϖ (χ.coeff 0) * leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) * P
      = leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) * (leadingResidue ϖ (χ.coeff 0) * P) := by ring
    _ = leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) * (-1) ^ h := by rw [key2]
    _ = (-1) ^ h * leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) := mul_comm _ _

end S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff (solution)
