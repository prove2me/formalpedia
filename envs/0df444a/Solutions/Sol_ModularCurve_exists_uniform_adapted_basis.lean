-- Prove2me | solution 1 for ModularCurve.exists_uniform_adapted_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ea2598df-f2dd-5448-8ae1-3b56522c0c4a

import Theorems.Thm_AlgebraicCurve_abs_prox_evalVec_sub_prox_le_of_coordinate_change
import Theorems.Thm_ModularCurve_exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL
import Theorems.Thm_ModularCurve_exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg
import Theorems.Thm_ValuationSubring_exists_window_and_adapted_basis
import Theorems.Thm_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_uniform_adapted_basis
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve IsLocalRing

noncomputable section

namespace UniformAdaptedBasisSol

section Valuation

variable {L : Type*} [Field L]

theorem mem_of_isIntegral_int (A : ValuationSubring L) {x : L} (hx : IsIntegral ℤ x) : x ∈ A := by
  by_contra hxA
  have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
  have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
  obtain ⟨f, hf, hfx⟩ := hx
  set n := f.natDegree with hn
  have hlead : f.coeff n = 1 := hf.coeff_natDegree
  have hn0 : n ≠ 0 := by
    intro h0
    have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
    rw [hC, Polynomial.eval₂_C] at hfx
    have h01 : f.coeff 0 = 1 := by rw [← h0]; exact hlead
    rw [h01, map_one] at hfx
    exact one_ne_zero hfx
  have hsum : x ^ n = -∑ i ∈ Finset.range n, (algebraMap ℤ L (f.coeff i)) * x ^ i := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hfx
    rw [hlead, map_one, one_mul] at hfx
    linear_combination hfx
  have hxpow : ∀ i ∈ Finset.range n,
      (algebraMap ℤ L (f.coeff i)) * x ^ i * (x⁻¹) ^ (n - 1) ∈ A := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : x ^ i * (x⁻¹) ^ (n - 1) = (x⁻¹) ^ (n - 1 - i) := by
      rw [show n - 1 = i + (n - 1 - i) by omega, pow_add, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hx0, one_pow, one_mul]
      congr 1; omega
    rw [mul_assoc, this]
    refine mul_mem ?_ (pow_mem hxi _)
    rw [eq_intCast]
    exact intCast_mem A _
  have hx_eq : x = -(∑ i ∈ Finset.range n,
      (algebraMap ℤ L (f.coeff i)) * x ^ i * (x⁻¹) ^ (n - 1)) := by
    have h1 : x = x ^ n * (x⁻¹) ^ (n - 1) := by
      conv_lhs => rw [← mul_one x, ← one_pow (n - 1), ← mul_inv_cancel₀ hx0, mul_pow, ← mul_assoc,
        ← pow_succ', show n - 1 + 1 = n by omega]
    calc x = x ^ n * x⁻¹ ^ (n - 1) := h1
      _ = _ := by rw [hsum, neg_mul, Finset.sum_mul]
  apply hxA
  rw [hx_eq]
  exact neg_mem (sum_mem fun i hi => hxpow i hi)

theorem inv_natCast_mem_of_coprime (A : ValuationSubring L) {p m : ℕ} (hp : (p : L) ∈ A.nonunits)
    (hm : Nat.Coprime m p) : (m : L)⁻¹ ∈ A := by
  by_contra hmi
  have hmA : (m : L) ∈ A := natCast_mem A m
  have hmnu : (m : L) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    rcases ((A.valuation_le_one_iff _).mpr hmA).lt_or_eq with h | h
    · exact h
    · exfalso; apply hmi
      have : A.valuation (m : L)⁻¹ ≤ 1 := by rw [map_inv₀, h, inv_one]
      exact (A.valuation_le_one_iff _).mp this
  have hbez := Nat.Coprime.gcd_eq_one hm
  have h1 : (1 : L) = (m : L) * (Nat.gcdA m p : L) + (p : L) * (Nat.gcdB m p : L) := by
    have h := Nat.gcd_eq_gcd_ab m p
    rw [hbez] at h
    have h' := congrArg (fun z : ℤ => (z : L)) h
    push_cast at h'
    exact h'
  rw [ValuationSubring.mem_nonunits_iff] at hmnu hp
  have hlt : A.valuation ((m : L) * (Nat.gcdA m p : L) + (p : L) * (Nat.gcdB m p : L)) < 1 := by
    refine lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hmnu
        ((A.valuation_le_one_iff _).mpr (intCast_mem A _))
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hp
        ((A.valuation_le_one_iff _).mpr (intCast_mem A _))
  rw [← h1, map_one] at hlt
  exact lt_irrefl _ hlt

theorem exists_pow_mul_inv_mem_of_isIntegral [CharZero L] {p : ℕ} (hp : p.Prime) {δ : L}
    (hδ : IsIntegral ℤ δ) (hδ0 : δ ≠ 0) :
    ∃ B : ℕ, ∀ A : ValuationSubring L, (p : L) ∈ A.nonunits → (p : L) ^ B * δ⁻¹ ∈ A := by
  have hδ' := hδ
  obtain ⟨f, hf, hfδ⟩ := hδ
  have hf0 : f ≠ 0 := hf.ne_zero
  obtain ⟨g, hfg, hg⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  rw [map_zero, sub_zero] at hfg hg
  have hgmonic : g.Monic := by
    have hXm : (Polynomial.X ^ Polynomial.rootMultiplicity 0 f : Polynomial ℤ).Monic :=
      Polynomial.monic_X_pow _
    have h := hf
    rw [hfg] at h
    exact hXm.of_mul_monic_left h
  have hg0 : g.coeff 0 ≠ 0 := fun h0 => hg (Polynomial.X_dvd_iff.mpr h0)
  have hgδ : Polynomial.aeval δ g = 0 := by
    have h : Polynomial.aeval δ f = 0 := by rwa [Polynomial.aeval_def]
    rw [hfg, map_mul, map_pow, Polynomial.aeval_X, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd (eq_zero_of_pow_eq_zero h) hδ0
    · exact h
  set a₀ : ℤ := g.coeff 0 with ha₀
  have hint : IsIntegral ℤ ((a₀ : L) * δ⁻¹) := by
    have hdecomp := Polynomial.X_mul_divX_add g
    have h1 : δ * Polynomial.aeval δ g.divX + (a₀ : L) = 0 := by
      have h := congrArg (Polynomial.aeval δ) hdecomp
      rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hgδ] at h
      simpa using h
    have h2 : (a₀ : L) * δ⁻¹ = -Polynomial.aeval δ g.divX := by
      have h3 : (a₀ : L) = -(δ * Polynomial.aeval δ g.divX) := by linear_combination h1
      rw [h3, neg_mul, mul_comm δ, mul_assoc, mul_inv_cancel₀ hδ0, mul_one]
    rw [h2]
    refine IsIntegral.neg ?_
    have hle : Algebra.adjoin ℤ {δ} ≤ integralClosure ℤ L := by
      rw [Algebra.adjoin_le_iff]; rintro _ rfl; exact hδ'
    exact hle (Polynomial.aeval_mem_adjoin_singleton ℤ δ)
  have ha₀0 : a₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hg0
  obtain ⟨B, m, hpm, hBm⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha₀0 p hp.ne_one
  refine ⟨B, fun A hpA => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hBm
    exact ha₀0 hBm
  have hcop : Nat.Coprime m p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have hmi : (m : L)⁻¹ ∈ A := inv_natCast_mem_of_coprime A hpA hcop
  have habs : ((a₀.natAbs : ℤ) : L) = (p : L) ^ B * (m : L) := by
    rw [hBm]; push_cast; ring
  have hsign : (a₀ : L) = (a₀.sign : L) * ((a₀.natAbs : ℤ) : L) := by
    rw [← Int.cast_mul, Int.sign_mul_natAbs]
  have hs2 : (a₀.sign : L) * (a₀.sign : L) = 1 := by
    rw [← Int.cast_mul]
    rcases lt_or_gt_of_ne hg0 with h1 | h1
    · simp [Int.sign_eq_neg_one_of_neg h1]
    · simp [Int.sign_eq_one_of_pos h1]
  have hm0' : (m : L) ≠ 0 := by exact_mod_cast hm0
  have key : (p : L) ^ B * δ⁻¹ = ((a₀ : L) * δ⁻¹) * ((a₀.sign : L) * (m : L)⁻¹) := by
    rw [hsign, habs]
    calc (p : L) ^ B * δ⁻¹
        = ((a₀.sign : L) * (a₀.sign : L)) * ((p : L) ^ B * δ⁻¹) * ((m : L) * (m : L)⁻¹) := by
          rw [hs2, one_mul, mul_inv_cancel₀ hm0', mul_one]
      _ = (a₀.sign : L) * ((p : L) ^ B * (m : L)) * δ⁻¹ * ((a₀.sign : L) * (m : L)⁻¹) := by ring
  rw [key]
  exact mul_mem (mem_of_isIntegral_int A hint) (mul_mem (intCast_mem A _) hmi)

theorem exists_pow_mul_inv_natCast_mem [CharZero L] {p : ℕ} (hp : p.Prime) {d : ℕ} (hd : d ≠ 0) :
    ∃ B : ℕ, ∀ A : ValuationSubring L, (p : L) ∈ A.nonunits → (p : L) ^ B * (d : L)⁻¹ ∈ A := by
  have hint : IsIntegral ℤ (d : L) := by
    have : (d : L) = algebraMap ℤ L (d : ℤ) := by simp
    rw [this]; exact isIntegral_algebraMap
  exact exists_pow_mul_inv_mem_of_isIntegral hp hint (by exact_mod_cast hd)

end Valuation

section General

theorem isRational_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (h : v.deg = 1) : v.IsRational := by
  intro w
  have h1 : Module.finrank K v.ResidueField = 1 := h
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp h1 w
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

variable {L : Type*} [Field L]

def packVal (A : ValuationSubring L) (z : LaurentSeries L) (hz : ∀ n, z.coeff n ∈ A) :
    LaurentSeries A where
  coeff := fun n => ⟨z.coeff n, hz n⟩
  isPWO_support' := z.isPWO_support.mono fun _ hn h => hn (Subtype.ext h)

theorem packVal_coeff (A : ValuationSubring L) (z : LaurentSeries L) (hz : ∀ n, z.coeff n ∈ A) (n : ℤ) :
    (packVal A z hz).coeff n = ⟨z.coeff n, hz n⟩ := rfl

theorem coeffMap_subtype_packVal (A : ValuationSubring L) (z : LaurentSeries L)
    (hz : ∀ n, z.coeff n ∈ A) : coeffMap A.subtype (packVal A z hz) = z := by
  ext n
  rw [coeffMap_coeff, packVal_coeff]
  rfl

theorem coeff_coe_smul {K : Type*} [Field K] (S : IntermediateField K (LaurentSeries K)) (c : K) (z : S)
    (n : ℤ) : ((c • z : S) : LaurentSeries K).coeff n = c * (z : LaurentSeries K).coeff n := by
  rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
    HahnSeries.coeff_single_zero_mul]

theorem coeff_coe_sum_smul {K : Type*} [Field K] (S : IntermediateField K (LaurentSeries K)) {ι : Type*}
    (T : Finset ι) (c : ι → K) (z : ι → S) (n : ℤ) :
    ((∑ i ∈ T, c i • z i : S) : LaurentSeries K).coeff n = ∑ i ∈ T, c i * (z i : LaurentSeries K).coeff n := by
  rw [AddSubmonoidClass.coe_finsetSum, HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun i _ => coeff_coe_smul S (c i) (z i) n

end General

section Main

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable (N : ℕ) [NeZero N]

def jB : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

theorem jB_ne_zero : jB N ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : modularFunctionFieldBar N => (z : LaurentSeries (AlgebraicClosure ℚ))) h
  simp only [jB, ZeroMemClass.coe_zero] at h1
  have h2 := order_coeffEmb_jq (AlgebraicClosure ℚ)
  rw [h1, HahnSeries.order_zero] at h2
  norm_num at h2

theorem jB_notMem_cuspInftyBar : (jB N) ∉ (cuspInftyBar N).toValuationSubring :=
  notMem_qIntegersBar_of_order_eq_neg_one (order_coeffEmb_jq (AlgebraicClosure ℚ))

theorem ord_nonneg_of_isEmbBasis {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i : Fin r) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hv : 0 ≤ v.ord (jB N)) : 0 ≤ v.ord (s i) := by
  have hmem : s i ∈ riemannRochSpace (embDivisor N) := by
    rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩
  rw [mem_riemannRochSpace_iff] at hmem
  have hvne : v ≠ cuspInftyBar N := by
    rintro rfl
    exact jB_notMem_cuspInftyBar N
      ((cuspInftyBar N).mem_toValuationSubring_of_ord_nonneg_alt (jB_ne_zero N) hv)
  rcases hmem v with h | h
  · rw [h, Place.ord_zero]
  · have h0 : (embDivisor N) v = 0 := by
      classical
      simp only [embDivisor, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hvne), smul_zero]
    rw [h0, neg_zero] at h
    exact h

variable {N}

theorem main {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ)
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      R.IsGood → IsPlaceReductionModL A N R.placeMap →
    ∃ t : Fin r → modularFunctionFieldBar N, IsEmbBasis N t ∧
      ∃ hint : ∀ l, t l ∈ R.integers,
        LinearIndependent (IsLocalRing.ResidueField A) (fun l => R.residue ⟨t l, hint l⟩) ∧
        ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
          (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
          ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ cP cQ : Fin r,
            (∀ j, 0 ≤ P.ord (t j * (t cP)⁻¹)) → (∀ j, 0 ≤ Q.ord (t j * (t cQ)⁻¹)) →
            (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
            |prox (μ : AlgebraicClosure ℚ → ℝ) (evalVec s P) (evalVec s Q)
                - prox (μ : AlgebraicClosure ℚ → ℝ) (fun j => P.evalAt (t j * (t cP)⁻¹))
                    (fun j => Q.evalAt (t j * (t cQ)⁻¹))|
              ≤ (B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  have hordJ : ∀ i (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      0 ≤ v.ord (jB N) → 0 ≤ v.ord (s i) := fun i v hv => ord_nonneg_of_isEmbBasis N s hs i v hv
  choose Kf df hKfd hdf hcoef using fun i =>
    ModularCurve.exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg N (s i) (hordJ i)
  haveI : ∀ i, FiniteDimensional ℚ (Kf i) := hKfd
  set K : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ i, Kf i with hK
  haveI hKfin : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_iSup_of_finite
  haveI : NumberField K :=
    { to_charZero := inferInstance, to_finiteDimensional := hKfin }
  set d : ℕ := ∏ i, df i with hd
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hdf i
  have hdQ0 : (d : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hd0
  have hcoefK : ∀ i n,
      ((s i : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K :=
    fun i n => (le_iSup Kf i) (hcoef i n).1
  have hcoefInt : ∀ i n, IsIntegral ℤ ((d : AlgebraicClosure ℚ) *
      ((s i : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff n) := by
    intro i n
    have hsplit : (d : AlgebraicClosure ℚ)
        = ((∏ j ∈ Finset.univ.erase i, df j : ℕ) : AlgebraicClosure ℚ) * (df i : AlgebraicClosure ℚ) := by
      rw [hd, ← Finset.prod_erase_mul Finset.univ df (Finset.mem_univ i)]
      push_cast; ring
    rw [hsplit, mul_assoc]
    refine IsIntegral.mul ?_ (hcoef i n).2
    have h1 : ((∏ j ∈ Finset.univ.erase i, df j : ℕ) : AlgebraicClosure ℚ)
        = algebraMap ℤ (AlgebraicClosure ℚ) ((∏ j ∈ Finset.univ.erase i, df j : ℕ) : ℤ) := by simp
    rw [h1]; exact isIntegral_algebraMap

  set O : Subring (AlgebraicClosure ℚ) :=
    (integralClosure ℤ K).toSubring.map (algebraMap K (AlgebraicClosure ℚ)) with hO
  have eO : (integralClosure ℤ K).toSubring ≃+* O :=
    Subring.equivMapOfInjective _ _ (algebraMap K _).injective
  haveI : IsNoetherianRing (integralClosure ℤ K) :=
    inferInstanceAs (IsNoetherianRing (NumberField.RingOfIntegers K))
  haveI : IsNoetherianRing O := isNoetherianRing_of_ringEquiv _ eO
  have hinjK : Function.Injective ((algebraMap K (AlgebraicClosure ℚ)).toIntAlgHom) :=
    (algebraMap K _).injective
  have hmemO : ∀ c : AlgebraicClosure ℚ, c ∈ K → IsIntegral ℤ c → c ∈ O := by
    intro c hcK hci
    refine ⟨⟨c, hcK⟩, ?_, rfl⟩
    show IsIntegral ℤ (⟨c, hcK⟩ : K)
    exact (isIntegral_algHom_iff _ hinjK).mp hci
  have hOint : ∀ c ∈ O, IsIntegral ℤ c := by
    rintro c ⟨y, hy, rfl⟩
    have hy' : IsIntegral ℤ y := hy
    exact (isIntegral_algHom_iff _ hinjK).mpr hy'
  have hOA : ∀ A : ValuationSubring (AlgebraicClosure ℚ), O ≤ A.toSubring :=
    fun A c hc => mem_of_isIntegral_int A (hOint c hc)

  set x : Fin r → ℤ → AlgebraicClosure ℚ :=
    fun i n => (d : AlgebraicClosure ℚ) *
      ((s i : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff n with hx
  have hxLI : ∀ a : Fin r → AlgebraicClosure ℚ, (∀ n, ∑ i, a i * x i n = 0) → ∀ i, a i = 0 := by
    intro a ha
    have hz : (∑ i, (a i * (d : AlgebraicClosure ℚ)) • s i : modularFunctionFieldBar N) = 0 := by
      apply Subtype.val_injective
      apply HahnSeries.ext
      funext n
      rw [coeff_coe_sum_smul, ZeroMemClass.coe_zero, HahnSeries.coeff_zero, ← ha n]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hx]; ring
    have h := (Fintype.linearIndependent_iff.mp hs.1) (fun i => a i * (d : AlgebraicClosure ℚ)) hz
    intro i
    exact (mul_eq_zero.mp (h i)).resolve_right hdQ0
  have hxO : ∀ i n, x i n ∈ O := fun i n =>
    hmemO _ (mul_mem (natCast_mem K d) (hcoefK i n)) (hcoefInt i n)
  obtain ⟨W, δ, hδO, hδ0, -, hbas⟩ := ValuationSubring.exists_window_and_adapted_basis O x hxLI hxO

  obtain ⟨Bδ, hBδ⟩ := exists_pow_mul_inv_mem_of_isIntegral (L := AlgebraicClosure ℚ) hp (hOint δ hδO) hδ0
  obtain ⟨Bd, hBd⟩ := exists_pow_mul_inv_natCast_mem (L := AlgebraicClosure ℚ) hp hd0
  set B₀ := max Bδ Bd with hB₀
  refine ⟨4 * B₀, fun A hA R hgood hR => ?_⟩
  have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA

  obtain ⟨t, M, M', htM, hxM', hδM, hM'A, horth, htA, hLI⟩ := hbas A (hOA A)
  set tF : Fin r → modularFunctionFieldBar N :=
    fun j => ∑ i, (M j i * (d : AlgebraicClosure ℚ)) • s i with htF
  have hcoe_tF : ∀ j n,
      ((tF j : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = t j n := by
    intro j n
    rw [htM j n, htF, coeff_coe_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hx]; ring
  have htFA : ∀ j n,
      ((tF j : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A :=
    fun j n => (hcoe_tF j n) ▸ htA j n

  have hpk : ∀ j, coeffMap A.subtype (packVal A _ (htFA j))
      = ((tF j : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun j => coeffMap_subtype_packVal A _ (htFA j)
  have hy : ∀ j, coeffMap A.subtype (packVal A _ (htFA j)) ∈ modularFunctionFieldBar N := by
    intro j; rw [hpk j]; exact (tF j).2
  have helt : ∀ j, (⟨coeffMap A.subtype (packVal A _ (htFA j)), hy j⟩ : modularFunctionFieldBar N)
      = tF j := fun j => Subtype.ext (hpk j)
  have hq := fun j =>
    ModularCurve.exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL N hpN A hA R hR
      (packVal A _ (htFA j)) (hy j)
  choose hmem hres using hq
  have hint : ∀ j, tF j ∈ R.integers := fun j => helt j ▸ hmem j
  have hres' : ∀ j (n : ℤ),
      ((R.residue ⟨tF j, hint j⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)).coeff n
        = IsLocalRing.residue A ⟨t j n, htA j n⟩ := by
    intro j n
    have h1 : (⟨tF j, hint j⟩ : R.integers) = ⟨_, hmem j⟩ := Subtype.ext (helt j).symm
    rw [h1, hres j, coeffMap_coeff, packVal_coeff]
    congr 1
    exact Subtype.ext (hcoe_tF j n)

  have hLIres : LinearIndependent (IsLocalRing.ResidueField A) (fun j => R.residue ⟨tF j, hint j⟩) := by
    let φ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N →ₗ[IsLocalRing.ResidueField A]
        (ℤ → IsLocalRing.ResidueField A) :=
      { toFun := fun z n => (z : LaurentSeries (IsLocalRing.ResidueField A)).coeff n
        map_add' := fun z w => by
          funext n
          simp only [IntermediateField.coe_add, HahnSeries.coeff_add, Pi.add_apply]
        map_smul' := fun c z => by
          funext n
          rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, coeff_coe_smul] }
    refine LinearIndependent.of_comp φ ?_
    have hcomp : (φ ∘ fun j => R.residue ⟨tF j, hint j⟩)
        = fun j => fun n : ℤ => IsLocalRing.residue A ⟨t j n, htA j n⟩ := by
      funext j n
      exact hres' j n
    rw [hcomp]
    exact hLI

  have htLI : LinearIndependent (AlgebraicClosure ℚ) tF :=
    ConstantReduction.linearIndependent_of_linearIndependent_residue R
      (fun j => (⟨tF j, hint j⟩ : R.integers)) hLIres
  have hsM' : ∀ i, s i = ∑ j, ((d : AlgebraicClosure ℚ)⁻¹ * M' i j) • tF j := by
    intro i
    apply Subtype.val_injective
    apply HahnSeries.ext
    funext n
    rw [coeff_coe_sum_smul]
    simp_rw [hcoe_tF, mul_assoc, ← Finset.mul_sum, ← hxM' i n]
    simp only [hx]
    rw [← mul_assoc, inv_mul_cancel₀ hdQ0, one_mul]
  have htEmb : IsEmbBasis N tF := by
    refine ⟨htLI, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← hs.2]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [← hs.2, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hsM' i]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine ⟨tF, htEmb, hint, hLIres, ?_⟩

  intro μ hμ hμA P Q cP cQ hcP hcQ hne
  have hpQ0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hμp_pos : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hpQ0
  have hμp_le : μ (p : AlgebraicClosure ℚ) ≤ 1 := (hμA _).mp (natCast_mem A p)
  have hμpi : 1 ≤ (μ (p : AlgebraicClosure ℚ))⁻¹ := (one_le_inv₀ hμp_pos).mpr hμp_le
  set C : ℝ := ((μ (p : AlgebraicClosure ℚ))⁻¹) ^ B₀ with hC
  have hC1 : 1 ≤ C := one_le_pow₀ hμpi
  have hbound : ∀ (B' : ℕ) (z : AlgebraicClosure ℚ), B' ≤ B₀ →
      (p : AlgebraicClosure ℚ) ^ B' * z⁻¹ ∈ A → μ z⁻¹ ≤ C := by
    intro B' z hB' hz
    have h1 : μ ((p : AlgebraicClosure ℚ) ^ B' * z⁻¹) ≤ 1 := (hμA _).mp hz
    rw [map_mul, map_pow] at h1
    have hpB : 0 < μ (p : AlgebraicClosure ℚ) ^ B' := pow_pos hμp_pos _
    have h2 : μ z⁻¹ ≤ (μ (p : AlgebraicClosure ℚ) ^ B')⁻¹ := by
      rw [inv_eq_one_div (μ (p : AlgebraicClosure ℚ) ^ B'), le_div_iff₀ hpB, mul_comm]; exact h1
    refine h2.trans ?_
    rw [← inv_pow]
    exact pow_le_pow_right₀ hμpi hB'
  have hμδ : μ δ⁻¹ ≤ C := hbound Bδ δ (le_max_left _ _) (hBδ A hpA)
  have hμd : μ (d : AlgebraicClosure ℚ)⁻¹ ≤ C := hbound Bd d (le_max_right _ _) (hBd A hpA)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hMC : ∀ j i, μ (M j i * (d : AlgebraicClosure ℚ)) ≤ C := by
    intro j i
    rw [map_mul]
    have hμd1 : μ (d : AlgebraicClosure ℚ) ≤ 1 := (hμA _).mp (natCast_mem A d)
    have hδμ0 : 0 < μ δ := μ.pos hδ0
    have h1 : μ (δ * M j i) ≤ 1 := (hμA _).mp (hδM j i)
    rw [map_mul] at h1
    have h2 : μ (M j i) ≤ (μ δ)⁻¹ := by
      rw [inv_eq_one_div (μ δ), le_div_iff₀ hδμ0, mul_comm]; exact h1
    rw [← map_inv₀] at h2
    calc μ (M j i) * μ (d : AlgebraicClosure ℚ) ≤ C * 1 :=
          mul_le_mul (h2.trans hμδ) hμd1 (μ.nonneg _) hC0
      _ = C := mul_one C
  have hM'C : ∀ i j, μ ((d : AlgebraicClosure ℚ)⁻¹ * M' i j) ≤ C := by
    intro i j
    rw [map_mul]
    have h1 : μ (M' i j) ≤ 1 := (hμA _).mp (hM'A i j)
    calc μ (d : AlgebraicClosure ℚ)⁻¹ * μ (M' i j) ≤ C * 1 := mul_le_mul hμd h1 (μ.nonneg _) hC0
      _ = C := mul_one C
  have hrat : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.IsRational :=
    fun v => isRational_of_deg_eq_one v (ModularCurve.deg_eq_one_modularFunctionFieldBar N v)
  have key := AlgebraicCurve.abs_prox_evalVec_sub_prox_le_of_coordinate_change s tF
    (fun i => hs.1.ne_zero i) (fun j => htLI.ne_zero j)
    (Matrix.of fun j i => M j i * (d : AlgebraicClosure ℚ))
    (Matrix.of fun i j => (d : AlgebraicClosure ℚ)⁻¹ * M' i j)
    (fun j => by simp only [Matrix.of_apply]; rfl) (fun i => by simp only [Matrix.of_apply]; exact hsM' i)
    μ hμ C hC1 (fun j i => by simp only [Matrix.of_apply]; exact hMC j i)
    (fun i j => by simp only [Matrix.of_apply]; exact hM'C i j)
    P Q (hrat P) (hrat Q) cP cQ hcP hcQ hne
  refine key.trans (le_of_eq ?_)
  rw [hC, Real.log_pow, Real.log_inv]
  push_cast
  ring

end Main

end UniformAdaptedBasisSol

end

set_option synthInstance.maxHeartbeats 1600000 in
open AlgebraicCurve ModularCurve in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ N) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      R.IsGood → IsPlaceReductionModL A N R.placeMap →
    ∃ t : Fin r → modularFunctionFieldBar N, IsEmbBasis N t ∧
      ∃ hint : ∀ l, t l ∈ R.integers,
        LinearIndependent (IsLocalRing.ResidueField A) (fun l => R.residue ⟨t l, hint l⟩) ∧
        ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
          (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
          ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ cP cQ : Fin r,
            (∀ j, 0 ≤ P.ord (t j * (t cP)⁻¹)) → (∀ j, 0 ≤ Q.ord (t j * (t cQ)⁻¹)) →
            (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
            |prox (μ : AlgebraicClosure ℚ → ℝ) (evalVec s P) (evalVec s Q)
                - prox (μ : AlgebraicClosure ℚ → ℝ) (fun j => P.evalAt (t j * (t cP)⁻¹))
                    (fun j => Q.evalAt (t j * (t cQ)⁻¹))|
              ≤ (B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) :=
  UniformAdaptedBasisSol.main s hs p hp hpN

end S_ModularCurve_exists_uniform_adapted_basis
end P2MW
export P2MW.S_ModularCurve_exists_uniform_adapted_basis (solution)
