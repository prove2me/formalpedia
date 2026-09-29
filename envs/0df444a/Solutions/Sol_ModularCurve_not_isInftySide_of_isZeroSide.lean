-- Prove2me | solution 1 for ModularCurve.not_isInftySide_of_isZeroSide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8b26024e-d71f-5e1b-8aa3-34b50c4cce8c

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_frickeInvolutionBar_comp_heckeBetaBar_one
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve"
namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq coeff_jq_neg_one ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar cuspZeroBar cuspZeroBar_def cuspInftyBar cuspInftyBar_toValuationSubring qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff coeffMap_qExpand deg_eq_one_modularFunctionFieldBar frickeInvolutionBar_comp_heckeBetaBar_one"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsInftySide IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization"
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q]

theorem liesOverPrime_of_ringHom (red : A →+* k) : A.LiesOverPrime q := by
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff]
  have hmem : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hle : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hu : IsUnit ((⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ : A)) := (A.valuation_eq_one_iff _).mpr h
    have h2 := hu.map red
    have h3 : red ⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ = ((q : ℕ) : k) := by
      rw [← map_natCast red q]
      congr 1
    rw [h3, CharP.cast_eq_zero k q] at h2
    exact not_isUnit_zero h2

end PlaceSpecialization
end ModularCurve
end

noncomputable section
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve"
namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq coeff_jq_neg_one ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar cuspZeroBar cuspZeroBar_def cuspInftyBar cuspInftyBar_toValuationSubring qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff coeffMap_qExpand deg_eq_one_modularFunctionFieldBar frickeInvolutionBar_comp_heckeBetaBar_one"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsInftySide IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization"
variable {q : ℕ} [Fact q.Prime]

theorem heckeBetaBar_j_eq_jqFun :
    heckeBetaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jqFun (q := q) := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand (AlgebraicClosure ℚ) q (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq) =
    coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (1 * q) jq)
  rw [coeffMap_qExpand]
  exact (qExpand_congr (one_mul q) _).symm
end PlaceSpecialization
end ModularCurve
end

noncomputable section
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve.PlaceSpecialization"
namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq coeff_jq_neg_one ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar cuspZeroBar cuspZeroBar_def cuspInftyBar cuspInftyBar_toValuationSubring qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff coeffMap_qExpand deg_eq_one_modularFunctionFieldBar frickeInvolutionBar_comp_heckeBetaBar_one"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsInftySide IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization"
variable {q : ℕ} [Fact q.Prime]

theorem ord_cuspZeroBar_jFun_neg : (cuspZeroBar (1 * q)).ord (jFun (q := q)) < 0 := by
  have hjα : heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jFun (q := q) :=
    Subtype.ext (coe_heckeAlphaBar (L := AlgebraicClosure ℚ) 1 q _)
  have hw : frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) := by
    have h := congrArg (fun φ => φ (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1))
      (frickeInvolutionBar_comp_heckeBetaBar_one q)
    simp only [AlgHom.comp_apply] at h
    rw [heckeBetaBar_j_eq_jqFun, hjα] at h
    exact h
  rw [cuspZeroBar_def, ← hw, Place.ord_smul]
  have hc : (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (jqFun (q := q))).coeff
      ((((1 * q : ℕ)) : ℤ) * (-1)) ≠ 0 := by
    show (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)).coeff _ ≠ 0
    rw [coeffEmb_coeff, qExpand_coeff_mul, coeff_jq_neg_one, map_one]
    exact one_ne_zero
  have hne : (jqFun (q := q) : modularFunctionFieldBar (1 * q)) ≠ 0 := by
    intro h0
    apply hc
    rw [h0, qSeriesBar_zero, HahnSeries.coeff_zero]
  have hnot : (jqFun (q := q) : modularFunctionFieldBar (1 * q)) ∉
      (cuspInftyBar (1 * q)).toValuationSubring := by
    rw [cuspInftyBar_toValuationSubring, mem_qIntegersBar_iff, not_le]
    have hle := HahnSeries.order_le_of_coeff_ne_zero hc
    have hq : (0 : ℤ) < ((1 * q : ℕ) : ℤ) := by
      have := (Fact.out : q.Prime).pos
      omega
    nlinarith
  by_contra hge
  push_neg at hge
  exact hnot ((cuspInftyBar (1 * q)).mem_of_ord_nonneg hne hge)

end PlaceSpecialization
end ModularCurve
end

noncomputable section
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve"
namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq coeff_jq_neg_one ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar cuspZeroBar cuspZeroBar_def cuspInftyBar cuspInftyBar_toValuationSubring qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff coeffMap_qExpand deg_eq_one_modularFunctionFieldBar frickeInvolutionBar_comp_heckeBetaBar_one"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsInftySide IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization"
variable {q : ℕ} [Fact q.Prime]

theorem ord_cuspInftyBar_jqFun_neg : (cuspInftyBar (1 * q)).ord (jqFun (q := q)) < 0 := by
  have hc : (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (jqFun (q := q))).coeff
      ((((1 * q : ℕ)) : ℤ) * (-1)) ≠ 0 := by
    show (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)).coeff _ ≠ 0
    rw [coeffEmb_coeff, qExpand_coeff_mul, coeff_jq_neg_one, map_one]
    exact one_ne_zero
  have hne : (jqFun (q := q) : modularFunctionFieldBar (1 * q)) ≠ 0 := by
    intro h0
    apply hc
    rw [h0, qSeriesBar_zero, HahnSeries.coeff_zero]
  have hnot : (jqFun (q := q) : modularFunctionFieldBar (1 * q)) ∉
      (cuspInftyBar (1 * q)).toValuationSubring := by
    rw [cuspInftyBar_toValuationSubring, mem_qIntegersBar_iff, not_le]
    have hle := HahnSeries.order_le_of_coeff_ne_zero hc
    have hq : (0 : ℤ) < ((1 * q : ℕ) : ℤ) := by
      have := (Fact.out : q.Prime).pos
      omega
    nlinarith
  by_contra hge
  push_neg at hge
  exact hnot ((cuspInftyBar (1 * q)).mem_of_ord_nonneg hne hge)
end PlaceSpecialization
end ModularCurve
end

noncomputable section
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve.PlaceSpecialization"
namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq coeff_jq_neg_one ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar cuspZeroBar cuspZeroBar_def cuspInftyBar cuspInftyBar_toValuationSubring qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff coeffMap_qExpand deg_eq_one_modularFunctionFieldBar frickeInvolutionBar_comp_heckeBetaBar_one"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsInftySide IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization"
variable {q : ℕ} [Fact q.Prime]

theorem hasValue_of_ord_sub_algebraMap_pos (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (g : modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)
    (h : 0 < W.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c)) :
    W.HasValue g c := by
  have hne : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hm : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c ∈ W.toValuationSubring :=
    W.mem_of_ord_nonneg hne h.le
  have hgm : g ∈ W.toValuationSubring := by
    have := add_mem hm (W.algebraMap_mem' c)
    simpa using this
  refine ⟨hgm, ?_⟩

  have hmax : (⟨_, hm⟩ : W.toValuationSubring) ∈ IsLocalRing.maximalIdeal W.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 := W.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change W.ord (g - _) = 0 at h0
    omega
  have hres : IsLocalRing.residue W.toValuationSubring ⟨_, hm⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  have hsplit : (⟨_, hm⟩ : W.toValuationSubring) = ⟨g, hgm⟩ - algebraMap (AlgebraicClosure ℚ) W.toValuationSubring c :=
    Subtype.ext rfl
  have h2 : IsLocalRing.residue W.toValuationSubring ⟨g, hgm⟩ - algebraMap (AlgebraicClosure ℚ) W.ResidueField c = 0 := by
    rw [← Place.residue_algebraMap, ← map_sub, ← hsplit, hres]
  exact sub_eq_zero.mp h2

theorem ord_sub_algebraMap_pos_of_hasValue (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (g : modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) (h : W.HasValue g c)
    (hne : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c ≠ 0) :
    0 < W.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c) := by
  have hm : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c ∈ W.toValuationSubring :=
    sub_mem h.mem (W.algebraMap_mem' c)
  have hres : IsLocalRing.residue W.toValuationSubring ⟨_, hm⟩ = 0 := by
    have hsplit : (⟨_, hm⟩ : W.toValuationSubring) = ⟨g, h.mem⟩ - algebraMap (AlgebraicClosure ℚ) W.toValuationSubring c :=
      Subtype.ext rfl
    rw [hsplit, map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]
  have hnn := W.ord_nonneg_of_mem hm
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := W.exists_isUnit_of_ord_eq_zero hne heq.symm
    have := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
    exact this hres

end PlaceSpecialization
end ModularCurve
end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq coeff_jq_neg_one ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar cuspZeroBar cuspZeroBar_def cuspInftyBar cuspInftyBar_toValuationSubring qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff coeffMap_qExpand deg_eq_one_modularFunctionFieldBar frickeInvolutionBar_comp_heckeBetaBar_one"
p2m_open "ModularCurve"

namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun tInfty tZero IsInftySide IsZeroSide"
p2m_open "ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem hasValue_pow' {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))}
    {g : modularFunctionFieldBar (1 * q)} {a : AlgebraicClosure ℚ} (h : W.HasValue g a) (n : ℕ) :
    W.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using W.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem inv_mem_nonunits_of_not_mem {e : AlgebraicClosure ℚ} (he : e ∉ A) : e⁻¹ ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have h1 : ¬ A.valuation e ≤ 1 := fun h => he ((A.valuation_le_one_iff e).mp h)
  push_neg at h1
  have he0 : e ≠ 0 := fun h => he (h ▸ A.zero_mem)
  rw [map_inv₀]
  exact inv_lt_one_of_one_lt₀ h1

theorem pow_succ_mem_nonunits {x : AlgebraicClosure ℚ} (hx : x ∈ A.nonunits) (m : ℕ) : x ^ (m + 1) ∈ A.nonunits := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [pow_succ]; exact mul_mem ih hx

end PlaceSpecialization

end ModularCurve

end

noncomputable section
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide.ModularCurve.PlaceSpecialization"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsZeroSide W) :
    ¬ P.IsInftySide W := by
  rintro ⟨hc, τ₁, hτ₁, hv₁⟩
  obtain ⟨hc', τ₀, hτ₀, hv₀⟩ := hW
  have hA : A.LiesOverPrime q := liesOverPrime_of_ringHom red
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 * q = m + 1 + 1 := ⟨q - 2, by omega⟩

  suffices hnu : (((τ₁ * τ₀ : A)) : AlgebraicClosure ℚ) ∈ A.nonunits by
    have hlt : A.valuation (((τ₁ * τ₀ : A)) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hnu
    have h0 := ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q hA red (τ₁ * τ₀) hlt
    rw [map_mul, hτ₁, hτ₀, mul_one] at h0
    exact one_ne_zero h0
  set j : modularFunctionFieldBar (1 * q) := jFun (q := q) with hj
  set j' : modularFunctionFieldBar (1 * q) := jqFun (q := q) with hj'

  have hval0 : ∀ {g : modularFunctionFieldBar (1 * q)} {τ : A}, red τ = 1 → W.HasValue g (τ : AlgebraicClosure ℚ) → g ≠ 0 := by
    intro g τ hτ hg h0
    rw [h0] at hg
    have h00 : W.HasValue (0 : modularFunctionFieldBar (1 * q)) 0 := by simpa using W.hasValue_algebraMap 0
    have : (τ : AlgebraicClosure ℚ) = 0 := hg.unique h00
    have hτ0 : τ = 0 := Subtype.ext this
    rw [hτ0, map_zero] at hτ
    exact zero_ne_one hτ
  have hj0 : j ≠ 0 := by
    intro h0
    apply hval0 hτ₁ hv₁
    show jqFun (q := q) / jFun (q := q) ^ (1 * q) = 0
    rw [← hj, h0, zero_pow (by omega), div_zero]
  have hj'0 : j' ≠ 0 := by
    intro h0
    apply hval0 hτ₀ hv₀
    show jFun (q := q) / jqFun (q := q) ^ (1 * q) = 0
    rw [← hj', h0, zero_pow (by omega), div_zero]
  set u : modularFunctionFieldBar (1 * q) := j * j' with hu
  have hu0 : u ≠ 0 := mul_ne_zero hj0 hj'0
  have hprod : tInfty (q := q) * tZero (q := q) = u * (u ^ (1 * q))⁻¹ := by
    show jqFun (q := q) / jFun (q := q) ^ (1 * q) * (jFun (q := q) / jqFun (q := q) ^ (1 * q)) = _
    rw [hu, mul_pow, mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← hj, ← hj']
    ring
  have hv : W.HasValue (u * (u ^ (1 * q))⁻¹) ((τ₁ : AlgebraicClosure ℚ) * τ₀) := hprod ▸ hv₁.mul hv₀
  have hτne : ((τ₁ : AlgebraicClosure ℚ) * τ₀) ≠ 0 := by
    intro h0
    have : τ₁ * τ₀ = 0 := Subtype.ext (by push_cast; exact h0)
    have h1 : red (τ₁ * τ₀) = 1 := by rw [map_mul, hτ₁, hτ₀, mul_one]
    rw [this, map_zero] at h1
    exact zero_ne_one h1

  have hordu : W.ord u = 0 := by
    have h1 := hv.ord_eq_zero hτne
    rw [W.ord_mul hu0 (inv_ne_zero (pow_ne_zero _ hu0)), Place.ord_inv, ← zpow_natCast, Place.ord_zpow] at h1
    push_cast at h1
    have : (1 - (q : ℤ)) * W.ord u = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · exact h
  have hordj : W.ord j ≤ 0 := by have h := hc 0; simpa using h
  have hordj' : W.ord j' ≤ 0 := by have h := hc' 0; simpa using h
  rw [hu, W.ord_mul hj0 hj'0] at hordu
  have hj_ord : W.ord j = 0 := by omega
  have hj'_ord : W.ord j' = 0 := by omega

  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField W).mp (deg_eq_one_modularFunctionFieldBar (1 * q) W)
  obtain ⟨hjm, hju⟩ := W.exists_isUnit_of_ord_eq_zero hj0 hj_ord
  obtain ⟨e, he, he0⟩ := W.exists_hasValue_of_surjective hsurj hjm
  have he0 := he0 hju
  obtain ⟨hjm', hju'⟩ := W.exists_isUnit_of_ord_eq_zero hj'0 hj'_ord
  obtain ⟨e', he', he'0⟩ := W.exists_hasValue_of_surjective hsurj hjm'
  have he'0 := he'0 hju'

  have heA : e ∉ A := by
    intro heA
    have h1 := hc ⟨e, heA⟩
    have hne : j - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) e ≠ 0 := by
      intro h0
      have hconst : j = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) e := sub_eq_zero.mp h0
      have h2 := ord_cuspZeroBar_jFun_neg (q := q)
      rw [← hj, hconst] at h2
      have h3 := (cuspZeroBar (1 * q)).ord_nonneg_of_mem ((cuspZeroBar (1 * q)).algebraMap_mem' e)
      omega
    have h2 := ord_sub_algebraMap_pos_of_hasValue W j e he hne
    change W.ord (j - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) e) ≤ 0 at h1
    omega
  have he'A : e' ∉ A := by
    intro he'A
    have h1 := hc' ⟨e', he'A⟩
    have hne : j' - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) e' ≠ 0 := by
      intro h0
      have hconst : j' = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) e' := sub_eq_zero.mp h0
      have h2 := ord_cuspInftyBar_jqFun_neg (q := q)
      rw [← hj', hconst] at h2
      have h3 := (cuspInftyBar (1 * q)).ord_nonneg_of_mem ((cuspInftyBar (1 * q)).algebraMap_mem' e')
      omega
    have h2 := ord_sub_algebraMap_pos_of_hasValue W j' e' he' hne
    change W.ord (j' - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) e') ≤ 0 at h1
    omega

  set x : AlgebraicClosure ℚ := e * e' with hx
  have hx0 : x ≠ 0 := mul_ne_zero he0 he'0
  have hxu : W.HasValue u x := he.mul he'
  have hval : W.HasValue (u * (u ^ (1 * q))⁻¹) (x * (x ^ (1 * q))⁻¹) :=
    hxu.mul ((hasValue_pow' hxu (1 * q)).inv (pow_ne_zero _ hx0))
  have hτx : ((τ₁ : AlgebraicClosure ℚ) * τ₀) = x * (x ^ (1 * q))⁻¹ := hv.unique hval
  have hid : x * (x ^ (1 * q))⁻¹ = (x⁻¹) ^ (m + 1) := by
    rw [hm, pow_succ, mul_inv, mul_comm ((x ^ (m + 1))⁻¹), ← mul_assoc, mul_inv_cancel₀ hx0, one_mul, inv_pow]
  have hxn : x⁻¹ ∈ A.nonunits := by
    rw [hx, mul_inv]
    exact mul_mem (inv_mem_nonunits_of_not_mem heA) (inv_mem_nonunits_of_not_mem he'A)
  show ((τ₁ : AlgebraicClosure ℚ) * τ₀) ∈ A.nonunits
  rw [hτx, hid]
  exact pow_succ_mem_nonunits hxn m

end

end S_ModularCurve_not_isInftySide_of_isZeroSide
end P2MW
export P2MW.S_ModularCurve_not_isInftySide_of_isZeroSide (solution)
