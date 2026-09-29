-- Prove2me | solution 1 for NumberField.archTermDerived_le_log_abs_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e86d9f81-2e87-5277-a481-af28024c2e6e

import Mathlib
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Theorems.Thm_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_archTermDerived_le_log_abs_discr

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

namespace Asymptotics
p2m_export "Asymptotics" "IsBigO IsBigO.of_bound isBigO_atTop_natCast_rpow_of_tendsto_div_rpow"
p2m_open "Asymptotics"
end Asymptotics
namespace Complex
p2m_export "Complex" "log_im abs_re_le_norm ofReal_sub reCLM one_re continuous_re abs_im_le_norm differentiable_exp re dist_eq sqrt norm_cpow_eq_rpow_re_of_pos div_ofNat_im differentiableOn_tsum_of_summable_norm re_ofNat ofReal_re hasDerivAt_exp add_re normSq_pos natCast_im natCast_log reCLM_apply ofReal_ne_zero re_add_im norm_real summable_ofReal one_im arctan ofReal_inv cpow_ne_zero_iff re_le_norm Gammaℝ exp_ne_zero normSq_add_mul_I log_ofReal_re add_im ofReal_natCast norm_natCast re_ofReal_mul ofReal_sum cpow_one ofReal_neg GammaSeq im mul_I_re norm_ofNat abs_arg_le_pi ofRealCLM hasSum_iff ofReal_intCast sin exp_sum Gamma_ne_zero Gamma_mul_Gamma_add_half arg inv_im log_inv hasSum_re ofReal_eq_zero norm_le_abs_re_add_abs_im normSq normSq_apply Gamma rank_real_complex differentiableAt_Gamma cpow_neg zero_re mk.injEq norm_natCast_cpow_le_norm_natCast_cpow_of_pos ofReal ofReal_zero ofReal_mul exp_neg neg_im neg_re sub_re I_re norm_natCast_cpow_of_pos div_ofNat_re cpow_def_of_ne_zero cpow_add div_ofReal_re sin_zero continuous_exp measurable_cos mul_cpow_ofReal_nonneg exp mk inv_re arg_ofReal_of_nonneg norm_exp hasStrictDerivAt_const_cpow cos_zero sin_neg hasSum_deriv_of_summable_norm sub_im imCLM norm_log_one_add_sub_self_le log_re Gammaℝ_ne_zero_of_re_pos exp_re exp_zero norm_log_one_add_half_le_self measurable_exp ofReal_div exp_ofReal_mul_I_re cos_neg ofReal_inj exp_sub exp_log natCast_re Gammaℂ ofReal_cpow continuous_ofReal cos_sub I_im cpow_nat_mul ofReal_one mul_re log_mul ofReal_im log deriv_const_cpow continuous_im mem_slitPlane_iff ofReal_exp Gammaℂ_def ext I GammaSeq_tendsto_Gamma continuous_sin ofReal_log exp_nat_mul mul_im slitPlane re_tsum cos continuous_cos hasDerivAt_log exp_add"
p2m_open "Complex"
end Complex
namespace FLT
namespace Gapsw48T2OdlyzkoDeg24PinCarrier
end FLT.Gapsw48T2OdlyzkoDeg24PinCarrier
namespace FLT
namespace Gapsw50T2ExplicitFormulaDecompositionPin
end FLT.Gapsw50T2ExplicitFormulaDecompositionPin
namespace FLT
namespace Gapsw52T2CarrierContentAtoms
end FLT.Gapsw52T2CarrierContentAtoms
namespace FLT
namespace Gapsw80T10DedekindZetaBridgeA1Discharge
end FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
namespace FLT
namespace Gapsw80T11ExplicitFormulaA34Decomp
end FLT.Gapsw80T11ExplicitFormulaA34Decomp
namespace FLT
namespace Gapsw80T13AffineArchTermA34Redecomp
end FLT.Gapsw80T13AffineArchTermA34Redecomp
namespace FLT
namespace Gapsw80T18ArchDerivedA34Redecomp
end FLT.Gapsw80T18ArchDerivedA34Redecomp
namespace FLT
namespace Gapsw80T19B2ppHadamardDecomp
end FLT.Gapsw80T19B2ppHadamardDecomp
namespace FLT
namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition
end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
namespace FLT
namespace Gapsw80T20LambdaLogDerivProductRule
end FLT.Gapsw80T20LambdaLogDerivProductRule
namespace FLT
namespace Gapsw80T21D2SubDecompWire
end FLT.Gapsw80T21D2SubDecompWire
namespace FLT
namespace Gapsw80T22AdmissibilityStripGapProbe
end FLT.Gapsw80T22AdmissibilityStripGapProbe
namespace FLT
namespace Gapsw80T23OdlyzkoKernelStripRemint
end FLT.Gapsw80T23OdlyzkoKernelStripRemint
namespace FLT
namespace Gapsw80T24StripMigrationChainStart
end FLT.Gapsw80T24StripMigrationChainStart
namespace FLT
namespace Gapsw80T25B4pppStripSinglePointAbsorption
end FLT.Gapsw80T25B4pppStripSinglePointAbsorption
namespace FLT
namespace Gapsw80T26D2dTwoConjunctDecomp
end FLT.Gapsw80T26D2dTwoConjunctDecomp
namespace FLT
namespace Gapsw80T27D2d0EulerProductAncestor
end FLT.Gapsw80T27D2d0EulerProductAncestor
namespace FLT
namespace Gapsw80T28D2d0aSummabilityProof
end FLT.Gapsw80T28D2d0aSummabilityProof
namespace FLT
namespace Gapsw80T29D2d0bNatEulerProductBridge
end FLT.Gapsw80T29D2d0bNatEulerProductBridge
namespace FLT
namespace Gapsw80T30D2d0cLocalEulerFactorProof
end FLT.Gapsw80T30D2d0cLocalEulerFactorProof
namespace FLT
namespace Gapsw80T31D1HadamardSubDecomp
end FLT.Gapsw80T31D1HadamardSubDecomp
namespace FLT
namespace Gapsw80T32D1aBoundaryCaseDecomp
end FLT.Gapsw80T32D1aBoundaryCaseDecomp
namespace FLT
namespace Gapsw80T33D1apZetaExtQuotientDecomp
end FLT.Gapsw80T33D1apZetaExtQuotientDecomp
namespace FLT
namespace Gapsw80T34D1apaThreeFourOneIneqDecomp
end FLT.Gapsw80T34D1apaThreeFourOneIneqDecomp
namespace FLT
namespace Gapsw80T35D1apa0ThreeFourOneIneqProof
end FLT.Gapsw80T35D1apa0ThreeFourOneIneqProof
namespace FLT
namespace Gapsw80T36D1appXiEndpointResidueProof
end FLT.Gapsw80T36D1appXiEndpointResidueProof
namespace FLT
namespace Gapsw80T37D1bGenericHadamardDecomp
end FLT.Gapsw80T37D1bGenericHadamardDecomp
namespace FLT
namespace Gapsw80T38D1b1CanonicalProductLogDerivProof
end FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
namespace FLT
namespace Gapsw80T39D1b0HadamardQuotientDecomp
end FLT.Gapsw80T39D1b0HadamardQuotientDecomp
namespace FLT
namespace Gapsw80T40D1b0bZeroFreeExpLinearProof
end FLT.Gapsw80T40D1b0bZeroFreeExpLinearProof
namespace FLT
namespace Gapsw80T41D1b0aHadamardFactorSubDecomp
end FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
namespace FLT
namespace Gapsw80T42D1b0a0XiNonzeroInfZerosProof
end FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
namespace FLT
namespace Gapsw80T43CompletedZetaRealSuperlinearProof
end FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
namespace FLT
namespace Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
end FLT.Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
namespace FLT
namespace Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof
end FLT.Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof
namespace FLT
namespace Gapsw80T46D1b0a1cEntireQuotientOfOrderMatchProof
end FLT.Gapsw80T46D1b0a1cEntireQuotientOfOrderMatchProof
namespace FLT
namespace Gapsw80T47D1b0a1aZeroEnumSummableSubDecomp
end FLT.Gapsw80T47D1b0a1aZeroEnumSummableSubDecomp
namespace FLT
namespace Gapsw80T48D1b0a1aiZeroEnumWithMultProof
end FLT.Gapsw80T48D1b0a1aiZeroEnumWithMultProof
namespace FLT
namespace Gapsw80T49D1b0a1aiiEnumNormSqSummableProof
end FLT.Gapsw80T49D1b0a1aiiEnumNormSqSummableProof
namespace FLT
namespace Gapsw80T50D1b0a2MinModulusSubDecomp
end FLT.Gapsw80T50D1b0a2MinModulusSubDecomp
namespace FLT
namespace Gapsw80T51D1b0a2bNonvanishSubTwoExpLinearProof
end FLT.Gapsw80T51D1b0a2bNonvanishSubTwoExpLinearProof
namespace FLT
namespace Gapsw80T52D1b0a2aBoasMinModulusSubDecomp
end FLT.Gapsw80T52D1b0a2aBoasMinModulusSubDecomp
namespace FLT
namespace Gapsw80T53D1b0a2aiiAnnulusToGlobalGrowthProof
end FLT.Gapsw80T53D1b0a2aiiAnnulusToGlobalGrowthProof
namespace FLT
namespace Gapsw80T54D1b0a2aiZeroCountBoasCoreSubDecomp
end FLT.Gapsw80T54D1b0a2aiZeroCountBoasCoreSubDecomp
namespace FLT
namespace Gapsw80T55D1b0a2aiAZeroCountJensenBoundProof
end FLT.Gapsw80T55D1b0a2aiAZeroCountJensenBoundProof
namespace FLT
namespace Gapsw80T56D1b0a2aiBBoasCartanMinModulusSubDecomp
end FLT.Gapsw80T56D1b0a2aiBBoasCartanMinModulusSubDecomp
namespace FLT
namespace Gapsw80T57D1b0a2aiBGammaCartanGoodRadiusProof
end FLT.Gapsw80T57D1b0a2aiBGammaCartanGoodRadiusProof
namespace FLT
namespace Gapsw80T58D1b0a2aiBAlphaFarTailProductLowerBoundProof
end FLT.Gapsw80T58D1b0a2aiBAlphaFarTailProductLowerBoundProof
namespace FLT
namespace Gapsw80T59D1b0a2aiBBetaMinModulusAssemblyProof
end FLT.Gapsw80T59D1b0a2aiBBetaMinModulusAssemblyProof
namespace FLT
namespace Gapsw80T60D2cArchGammaKernelSubDecomp
end FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
namespace FLT
namespace Gapsw80T61D2cbArchGammaParsevalFalseprobe
end FLT.Gapsw80T61D2cbArchGammaParsevalFalseprobe
namespace FLT
namespace Gapsw80T62ArchGammaKernelRemintWire
end FLT.Gapsw80T62ArchGammaKernelRemintWire
namespace FLT
namespace Gapsw80T63CosineInversionWire
end FLT.Gapsw80T63CosineInversionWire
namespace FLT
namespace Gapsw80T64D2fGaussianMollificationProof
end FLT.Gapsw80T64D2fGaussianMollificationProof
namespace FLT
namespace Gapsw80T65D2caDigammaSeriesSubDecomp
end FLT.Gapsw80T65D2caDigammaSeriesSubDecomp
namespace FLT
namespace Gapsw80T66D2caiDigammaSeriesProof
end FLT.Gapsw80T66D2caiDigammaSeriesProof
namespace FLT
namespace Gapsw80T67D2bpPrimeSumFalseprobeRemint
end FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint
namespace FLT
namespace Gapsw80T68D2bppExplicitFormulaSubDecomp
end FLT.Gapsw80T68D2bppExplicitFormulaSubDecomp
namespace FLT
namespace Gapsw80T69AdmC2RemintZktSummable
end FLT.Gapsw80T69AdmC2RemintZktSummable
namespace FLT
namespace Gapsw80T70D2bpppZeroSideEvalSubDecomp
end FLT.Gapsw80T70D2bpppZeroSideEvalSubDecomp
namespace FLT
namespace Gapsw80T9ClassSumA1Closure
end FLT.Gapsw80T9ClassSumA1Closure
namespace Filter
p2m_export "Filter" "eventually_atTop mk pi Tendsto.atTop_div_const Tendsto mem_comap atBot tendsto_neg_atTop_atBot EventuallyEq.deriv_eq tendsto_add_atTop_nat map_congr eventuallyEq_of_mem tendsto_congr atTop Tendsto.congr' eventually_of_mem eventuallyEq_iff_exists_mem unique mk.injEq Tendsto.div_atTop map_id EventuallyEq map eventually_ge_atTop cofinite tendsto_id Eventually.of_forall"
p2m_open "Filter"
end Filter
namespace MeasureTheory
p2m_export "MeasureTheory" "HasFiniteIntegral tendsto_integral_of_dominated_convergence Measure integral_div integral_mono setIntegral_congr_fun ae_restrict_iff' integral_mono_of_nonneg integral_sub integral_nonneg integral_mul_const setIntegral_nonneg IntegrableOn Integrable.mono' integral_neg ae_restrict_mem integrableOn_const continuous_of_dominated Measure.integral_comp_mul_left ae_lt_top' integral_integral_swap ae AEStronglyMeasurable.mul integral_const integral_Ioi_of_hasDerivAt_of_tendsto' integrable_prod_iff integral_congr_ae lintegral_tsum integrableOn_Ioi_deriv_of_nonneg setIntegral_mono_on norm_integral_le_integral_norm IntegrableOn.union ae_restrict_of_forall_mem integrableOn_univ integral_add_right_eq_self Integrable integral_tsum_of_summable_integral_norm Integrable.const_mul lintegral_mono_ae integral_Ioi_of_hasDerivAt_of_tendsto lintegral_tendsto_of_tendsto_of_monotone integral_add integral_const_mul AEStronglyMeasurable ofReal_integral_eq_lintegral_ofReal integral_neg_eq_self setIntegral_univ ae_of_all setIntegral_union"
p2m_open "MeasureTheory"
end MeasureTheory
namespace Metric
p2m_export "Metric" "tendsto_nhdsWithin_nhds mem_ball ball mem_ball_self ball_mem_nhds isOpen_ball"
p2m_open "Metric"
end Metric
namespace Module
p2m_export "Module" "Injective support Free.chooseBasis finrank Free mk Finite.of_injective restrictScalars finrank_pos finrank_eq_card_chooseBasisIndex IsPrincipal"
p2m_open "Module"
end Module
namespace Nat
p2m_export "Nat" "Primes Coprime.pow_left succ_ne_zero le_of_dvd cast_nonneg cast_ne_zero log_pos card_eq_fintype_card log_pow log div_pos dvd_prime_pow add_le_add count succ sqrt_pos prime_dvd_prime_iff_eq card_eq_zero cast_sum Coprime Coprime.coprime_dvd_left choose factorial_succ dist_eq card_prod Prime card_univ sqrt zero_le cast_add_one_ne_zero div_le_self div_mul_div_comm dist eq_zero_or_pos cast_le ne_of_gt cast_mul le_ceil cast_zero one_le_cast succ_le_succ factorial_ne_zero card_eq_one_iff_exists one_le_iff_ne_zero card_congr pow_succ' card_unique cast_add zero clog cast_one one_le_pow"
p2m_open "Nat"
end Nat
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces IsTotallyComplex discr mk IsTotallyComplex.nrRealPlaces_eq_zero RingOfIntegers InfinitePlace.nrComplexPlaces dedekindZeta InfinitePlace discr_ne_zero Ideal.tendsto_norm_le_div_atTop₀ exists_completedDedekindZeta_package exists_hadamard_logDeriv_expansion_of_completedZeta_package"
p2m_open "NumberField"
end NumberField
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces IsTotallyComplex discr mk IsTotallyComplex.nrRealPlaces_eq_zero RingOfIntegers InfinitePlace.nrComplexPlaces dedekindZeta InfinitePlace discr_ne_zero Ideal.tendsto_norm_le_div_atTop₀ exists_completedDedekindZeta_package exists_hadamard_logDeriv_expansion_of_completedZeta_package"
namespace InfinitePlace
p2m_export "NumberField.InfinitePlace" "nrRealPlaces smul_apply mk ext nrComplexPlaces apply card_add_two_mul_card_eq_rank"
p2m_open "NumberField.InfinitePlace NumberField"
end NumberField.InfinitePlace
namespace Real
p2m_export "Real" "arctan_nonneg tendsto_exp_atBot rpow_le_rpow sqrt_pos log_pos differentiable_exp norm norm_natCast GammaSeq exp_lt_one_iff log_nonneg exp_zero log_le_rpow_div pi_ne_zero rpow_def_of_pos exp_sub rpow_nonneg continuous_sin one_le_exp tendsto_exp_neg_atTop_nhds_zero tendsto_harmonic_sub_log sin_neg measurable_exp tendsto_sqrt_atTop tendsto_log_comp_add_sub_log exp_ne_zero sqrt_ne_zero' Gamma arctan_lt_pi_div_two log_inv exp_nat_mul measurable_cos arctan exp Gamma_ne_zero cos_neg Gamma_mul_Gamma_add_half rpow_two abs_exp exp_pos exp_le_exp hasDerivAt_arctan neg_one_le_cos eulerMascheroniConstant sin rpow_le_rpow_of_exponent_le continuous_cos abs_cos_le_one sqrt_eq_rpow rpow_add log_le_log_iff exp_sum rpow_neg log_natCast_nonneg cos_sub rpow_pos_of_pos pi_lt_four rpow_natCast sin_zero differentiableAt_Gamma continuous_exp log norm_of_nonneg norm_eq_abs exp_neg mk pi_pos log_nonpos exp_log norm_ofNat exp_le_one_iff exp_lt_exp log_mul rpow_one sq_sqrt log_le_log summable_one_div_nat_add_rpow sqrt_mul cos_zero cos hasDerivAt_exp cos_le_one hasDerivAt_log dist_eq add_one_le_exp GammaSeq_tendsto_Gamma exp_add rpow_lt_one_of_one_lt_of_neg log_pow two_mul_cos_mul_cos sqrt abs_sin_le_one"
p2m_open "Real"
end Real
namespace Set
p2m_export "Set" "toFinite eq_univ_of_forall Iic_disjoint_Ioi neg_Ici restrict finite_Iio mem_Ici_of_Ioi Ioi_subset_Ioi Icc Iic Icc_succ_left_eq_Ioc mem_compl_iff image subset_univ ext mem_toFinset coe_eq_subtype mem_nsmul pi Ioo toFinset Ioc MapsTo mem_singleton_iff Ioi_subset_Ici_self mem_univ Finite.subset Ioi mem_image prod_insert mapsTo_univ Countable.isConnected_compl_of_one_lt_rank Iic_union_Ioi mem_singleton InjOn Ici Ioc_union_Ioi_eq_Ioi mem_setOf_eq Ioc_subset_Ioi_self mem_insert_iff countable_univ_iff univ prod_singleton prod prod_empty range mem_Ioi"
p2m_open "Set"
end Set
namespace Topology
p2m_open "Topology"
end Topology
namespace UniqueFactorizationMonoid
p2m_export "UniqueFactorizationMonoid" "mk mem_normalizedFactors_iff normalizedFactors_prod_eq prod_normalizedFactors_eq normalizedFactors"
p2m_open "UniqueFactorizationMonoid"
end UniqueFactorizationMonoid

section

namespace FLT
namespace Gapsw50T2ExplicitFormulaDecompositionPin

def gapsw50_t2_OdlyzkoAdmissibleKernel (F : ℝ → ℝ) : Prop :=
  Differentiable ℝ F ∧ (∀ x : ℝ, F (-x) = F x) ∧ F 0 = 1 ∧ (∀ x : ℝ, 0 ≤ F x) ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧
    ∀ t : ℝ, 0 ≤ ∫ x : ℝ, F x * Real.cos (t * x)

set_option maxHeartbeats 3200000 in

theorem gapsw50_t2_row20_wire_core (n : ℕ) (D M P Z : ℝ) (hD : 0 < D)
    (hM : (n : ℝ) * Real.log (9805 / 1000) ≤ M)
    (hP : 0 ≤ P) (hZ : 0 ≤ Z) (hEq : Real.log D = M + P + Z) :
    (9805 : ℝ) ^ n ≤ 1000 ^ n * D := by
  have _em := Classical.em
  have hpow : (0 : ℝ) < ((9805 : ℝ) / 1000) ^ n := by positivity
  have hlog : Real.log (((9805 : ℝ) / 1000) ^ n) ≤ Real.log D := by
    rw [Real.log_pow]
    linarith
  have hle : ((9805 : ℝ) / 1000) ^ n ≤ D := (Real.log_le_log_iff hpow hD).mp hlog
  have key : (1000 : ℝ) ^ n * ((9805 / 1000 : ℝ) ^ n) = 9805 ^ n := by
    rw [← mul_pow]
    norm_num
  calc (9805 : ℝ) ^ n = 1000 ^ n * ((9805 / 1000 : ℝ) ^ n) := key.symm
    _ ≤ 1000 ^ n * D := mul_le_mul_of_nonneg_left hle (by positivity)

end FLT.Gapsw50T2ExplicitFormulaDecompositionPin

end

section

namespace FLT
namespace Gapsw52T2CarrierContentAtoms

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin

noncomputable def gapsw52_t2_odlyzkoPrimeIdealTerm (F : ℝ → ℝ) (N m : ℕ) : ℝ :=
  Real.log N * F (((m : ℝ) + 1) * Real.log N) * (N : ℝ) ^ (-((m : ℝ) + 1) / 2)

set_option maxHeartbeats 3200000 in

theorem gapsw52_t2_odlyzkoPrimeIdealTerm_nonneg (F : ℝ → ℝ) (hF : ∀ x : ℝ, 0 ≤ F x)
    (N m : ℕ) : 0 ≤ gapsw52_t2_odlyzkoPrimeIdealTerm F N m := by
  have _em := Classical.em
  exact mul_nonneg (mul_nonneg (Real.log_natCast_nonneg N) (hF _))
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)

noncomputable def gapsw52_t2_OdlyzkoPrimeIdealSum
    (F : ℝ → ℝ) (K : Type) [Field K] [NumberField K] : ℝ :=
  ∑' p : {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥} × ℕ,
    gapsw52_t2_odlyzkoPrimeIdealTerm F (Ideal.absNorm p.1.1) p.2

set_option maxHeartbeats 3200000 in

theorem gapsw52_t2_odlyzkoPrimeIdealSum_nonneg (F : ℝ → ℝ) (hF : ∀ x : ℝ, 0 ≤ F x)
    (K : Type) [Field K] [NumberField K] :
    0 ≤ gapsw52_t2_OdlyzkoPrimeIdealSum F K := by
  have _em := Classical.em
  exact tsum_nonneg fun p =>
    gapsw52_t2_odlyzkoPrimeIdealTerm_nonneg F hF (Ideal.absNorm p.1.1) p.2

end FLT.Gapsw52T2CarrierContentAtoms

end

section

namespace FLT
namespace Gapsw80T13AffineArchTermA34Redecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module"

noncomputable def gapsw80_t13_poleTerm (F : ℝ → ℝ) : ℝ :=
  2 * ∫ x in Set.Ioi (0:ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2)))

set_option maxHeartbeats 3200000 in

theorem gapsw80_t13_poleTerm_pin (F : ℝ → ℝ) :
    gapsw80_t13_poleTerm F =
      2 * ∫ x in Set.Ioi (0:ℝ),
        F x * (Real.exp (x / 2) + Real.exp (-(x / 2))) := by
  have _em := Classical.em
  rfl

end FLT.Gapsw80T13AffineArchTermA34Redecomp

end

section

namespace FLT
namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition

open FLT.Gapsw48T2OdlyzkoDeg24PinCarrier
open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"

noncomputable def gapsw80_t1_completedDedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|discr K| : ℤ) : ℂ)) ^ (s / 2)
    * Gammaℝ s ^ nrRealPlaces K
    * Gammaℂ s ^ nrComplexPlaces K
    * dedekindZeta K s

end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

end

namespace FLT
namespace Gapsw80T9ClassSumA1Closure

p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"

variable (K : Type) [Field K] [NumberField K]

noncomputable def gapsw80_t9_completedDedekindZeta (s : ℂ) : ℂ :=
  Classical.choose (NumberField.exists_completedDedekindZeta_package K) s

theorem gapsw80_t9_pkg_spec :
    DifferentiableOn ℂ (gapsw80_t9_completedDedekindZeta K) ({(0 : ℂ), 1}ᶜ) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
        gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s) ∧
      (∀ s : ℂ, 1 < s.re → gapsw80_t9_completedDedekindZeta K s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) ∧
      (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
      (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
          ξ 0 ≠ 0 ∧ ξ 1 ≠ 0) ∧
      (∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * gapsw80_t9_completedDedekindZeta K s‖) :=
  Classical.choose_spec (NumberField.exists_completedDedekindZeta_package K)

theorem gapsw80_t9_isClosed_pair : IsClosed ({(0:ℂ), 1} : Set ℂ) :=
  (Set.toFinite _).isClosed

theorem gapsw80_t9_isPreconnected_compl :
    IsPreconnected ({(0:ℂ), 1}ᶜ : Set ℂ) :=
  (IsConnected.isPreconnected (Set.Countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) (Set.toFinite _).countable))

theorem gapsw80_t9_differentiableOn_completedDedekindZeta :
    DifferentiableOn ℂ (gapsw80_t9_completedDedekindZeta K) {(0:ℂ), 1}ᶜ :=
  (gapsw80_t9_pkg_spec K).1

theorem gapsw80_t9_analyticOnNhd_completedDedekindZeta :
    AnalyticOnNhd ℂ (gapsw80_t9_completedDedekindZeta K) {(0:ℂ), 1}ᶜ :=
  (gapsw80_t9_differentiableOn_completedDedekindZeta K).analyticOnNhd
    gapsw80_t9_isClosed_pair.isOpen_compl

theorem gapsw80_t9_completedDedekindZeta_FE {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s :=
  (gapsw80_t9_pkg_spec K).2.1 s hs0 hs1

end FLT.Gapsw80T9ClassSumA1Closure

namespace FLT
namespace Gapsw80T10DedekindZetaBridgeA1Discharge

p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace"
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
p2m_open "Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Real P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Real MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory Filter P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Filter Set P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Set Ideal NumberField.Ideal Asymptotics P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Asymptotics"
p2m_open_scoped "Classical nonZeroDivisors Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology"

variable (K : Type) [Field K] [NumberField K]

noncomputable def gapsw80_t10_fiberEquiv {n : ℕ} (hn : n ≠ 0) :
    {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n}
      ≃ {I : Ideal (𝓞 K) // absNorm I = n} where
  toFun J := ⟨J.1.1, J.2⟩
  invFun I := ⟨⟨I.1, Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mp
    (by rw [I.2]; exact hn)⟩, I.2⟩
  left_inv J := by ext; rfl
  right_inv I := rfl

theorem gapsw80_t10_fiberCard {n : ℕ} (hn : n ≠ 0) :
    Nat.card {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n}
      = Nat.card {I : Ideal (𝓞 K) // absNorm I = n} :=
  Nat.card_congr (gapsw80_t10_fiberEquiv K hn)

scoped instance gapsw80_t10_fiberFinite (n : ℕ) :
    Finite {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n} := by
  haveI : Finite {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq n).to_subtype
  exact Finite.of_injective
    (fun J => (⟨J.1.1, J.2⟩ : {I : Ideal (𝓞 K) // absNorm I = n}))
    (fun J₁ J₂ h => Subtype.ext (Subtype.ext (by
      simpa only [Subtype.mk.injEq] using h)))

theorem gapsw80_t10_LSeriesSummable_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  have key : LSeriesSummable
      (fun n ↦ ((Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) : ℂ)) s := by
    refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (fun _ => Nat.cast_nonneg _)
      zero_le_one hs

    exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ) (r := 1) <| by
      simp only [Real.rpow_one]
      refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp
        tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
      simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
      congr
      rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
        show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
        show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by
          simp [Ideal.absNorm_eq_zero_iff],
        Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
        ← Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
      simp [Set.coe_eq_subtype]
  exact (LSeriesSummable_congr s (fun {n} _ => by push_cast; ring)).mp key

theorem gapsw80_t10_term_eq (s : ℂ) (n : ℕ) :
    (Nat.card {J : (Ideal (𝓞 K))⁰ // Ideal.absNorm (J : Ideal (𝓞 K)) = n} : ℂ)
        * ((n : ℂ)) ^ (-s)
      = LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · haveI hE : IsEmpty {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = 0} :=
      ⟨fun J => (Ideal.absNorm_ne_zero_of_nonZeroDivisors J.1) J.2⟩
    simp [LSeries.term_zero, Nat.card_eq_zero.mpr (Or.inl hE)]
  · rw [LSeries.term_of_ne_zero hn, gapsw80_t10_fiberCard K hn, div_eq_mul_inv,
      ← Complex.cpow_neg]

theorem gapsw80_t10_fiber_hasSum (s : ℂ) (n : ℕ) :
    HasSum (fun J : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
        ((absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n) := by
  haveI : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} :=
    Fintype.ofFinite _
  have h1 : (fun J : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
      ((absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) = fun _ => (n : ℂ) ^ (-s) := by
    funext J; rw [J.2]
  rw [h1, ← gapsw80_t10_term_eq K s n, ← nsmul_eq_mul, Nat.card_eq_fintype_card,
    ← Finset.card_univ, ← Finset.sum_const]
  exact hasSum_fintype _

theorem gapsw80_t10_summable_idealNorm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : (Ideal (𝓞 K))⁰ ↦
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) := by
  rw [← (Equiv.sigmaFiberEquiv
    (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).summable_iff]
  refine Summable.of_norm ?_
  refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨?_, ?_⟩
  · exact fun n =>
      haveI : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} := Fintype.ofFinite _
      (hasSum_fintype _).summable
  · refine ((gapsw80_t10_LSeriesSummable_dedekindZeta K hs).norm).congr fun n => ?_
    haveI : Fintype {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} :=
      Fintype.ofFinite _
    rw [tsum_fintype]
    calc ‖LSeries.term (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℂ)) s n‖
        = ‖(Nat.card {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} : ℂ)
            * (n : ℂ) ^ (-s)‖ := by rw [gapsw80_t10_term_eq K s n]
      _ = (Nat.card {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} : ℝ)
            * ‖(n : ℂ) ^ (-s)‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ∑ c : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n},
            ‖((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
              (Equiv.sigmaFiberEquiv
                (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K))))) ⟨n, c⟩‖ := by
          rw [show (fun c : {J : (Ideal (𝓞 K))⁰ // absNorm (J : Ideal (𝓞 K)) = n} =>
              ‖((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
                (Equiv.sigmaFiberEquiv _)) ⟨n, c⟩‖)
              = fun _ => ‖(n : ℂ) ^ (-s)‖ from funext fun c => by
            simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, c.2]]
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem gapsw80_t10_discrCoercion :
    (((|discr K| : ℤ) : ℂ)) = (((|(discr K : ℝ)| : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_intCast, Int.cast_abs]

theorem gapsw80_t10_completedDedekindZeta_eq_T1 {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K s
      = gapsw80_t1_completedDedekindZeta K s := by
  rw [gapsw80_t1_completedDedekindZeta]
  exact (gapsw80_t9_pkg_spec K).2.2.1 s hs

end FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT"

section

namespace FLT
namespace Gapsw80T60D2cArchGammaKernelSubDecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T59D1b0a2aiBBetaMinModulusAssemblyProof
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex Filter P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Filter Set P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Set Metric P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology"

set_option maxHeartbeats 6400000 in

theorem gapsw80_t60_re_logDeriv_Gammaℂ_critical_line (t : ℝ) :
    (logDeriv Gammaℂ (1 / 2 + (t : ℂ) * I)).re
      = -Real.log (2 * Real.pi)
        + (logDeriv Complex.Gamma (1 / 2 + (t : ℂ) * I)).re := by
  have _em := Classical.em
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs_def
  have hs_re : s.re = 1 / 2 := by
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hs_nm : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m hsm
    have h1 : s.re = (-(m : ℂ)).re := by rw [hsm]
    simp only [Complex.neg_re, Complex.natCast_re] at h1
    rw [hs_re] at h1
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hΓ_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs_nm
  have hΓ_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s hs_nm
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, two_ne_zero]
  have hg_diff : DifferentiableAt ℂ (fun z => (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    (differentiable_neg.differentiableAt).const_cpow (Or.inl h2π)
  have hg_ne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero h2π]; exact Complex.exp_ne_zero _
  have hg_ld : logDeriv (fun z => (2 * (Real.pi : ℂ)) ^ (-z)) s
      = -Complex.log (2 * (Real.pi : ℂ)) := by
    have hd : HasDerivAt (fun z => (2 * (Real.pi : ℂ)) ^ (-z))
        (-(2 * (Real.pi : ℂ)) ^ (-s) * Complex.log (2 * (Real.pi : ℂ))) s := by
      have h1 : HasDerivAt (fun z : ℂ => -z) (-1) s := hasDerivAt_neg s
      have h2 := (hasStrictDerivAt_const_cpow (x := 2 * (Real.pi : ℂ)) (y := -s)
        (Or.inl h2π)).hasDerivAt
      have := h2.comp s h1
      simp [mul_comm, mul_neg, neg_mul] at this ⊢
      exact this
    rw [logDeriv_apply, hd.deriv]
    field_simp
  have hfact : Gammaℂ = fun z => (2:ℂ) * ((2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z) := by
    funext z; rw [Gammaℂ_def]; ring
  have hld : logDeriv Gammaℂ s
      = -Complex.log (2 * (Real.pi : ℂ)) + logDeriv Complex.Gamma s := by
    rw [hfact, logDeriv_const_mul _ _ (two_ne_zero),
      logDeriv_mul s hg_ne hΓ_ne hg_diff hΓ_diff, hg_ld]
  rw [hld, Complex.add_re, Complex.neg_re]
  congr 1
  have hcast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.log_ofReal_re]

def gapsw80_t60_DigammaReCriticalLineCosKernel : Prop :=
  ∀ t : ℝ, (logDeriv Complex.Gamma (1 / 2 + (t : ℂ) * I)).re
    = -Real.eulerMascheroniConstant - 2 * Real.log 2
      + ∫ x in Set.Ioi (0:ℝ),
          (1 - Real.cos (t * x)) / (Real.exp (x / 2) - Real.exp (-(x / 2)))

end FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T61D2cbArchGammaParsevalFalseprobe

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T22AdmissibilityStripGapProbe
open FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
p2m_open "Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory Filter P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Filter"

set_option maxHeartbeats 6400000 in

theorem gapsw80_t61_integral_gaussian_cos {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ∫ x : ℝ, Real.exp (-(a * x ^ 2)) * Real.cos (t * x)
      = Real.sqrt (Real.pi / a) * Real.exp (-(t ^ 2 / (4 * a))) := by
  have _em := Classical.em
  have hb : 0 < ((a : ℂ)).re := by simp [ha]
  have hint : Integrable
      (fun x : ℝ => Complex.exp (I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ) ^ 2)) := by
    have h := integrable_cexp_quadratic (b := (a : ℂ)) hb (I * (t : ℂ)) 0
    apply h.congr
    filter_upwards with x
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hpoint : (fun x : ℝ => Real.exp (-(a * x ^ 2)) * Real.cos (t * x))
      = fun x : ℝ => (Complex.exp (I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ) ^ 2)).re := by
    funext x
    have hx : Complex.exp (I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ) ^ 2)
        = ((Real.exp (-(a * x ^ 2)) : ℝ) : ℂ) *
            Complex.exp (((t * x : ℝ) : ℂ) * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hx, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hre : ∫ x : ℝ, (Complex.exp (I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ) ^ 2)).re
      = (∫ x : ℝ, Complex.exp (I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ) ^ 2)).re := by
    have h := Complex.reCLM.integral_comp_comm hint
    simpa using h
  rw [hpoint, hre, fourierIntegral_gaussian hb ((t : ℝ) : ℂ)]
  have h1 : ((Real.pi : ℂ) / (a : ℂ)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) := by
    rw [show ((Real.pi : ℂ) / (a : ℂ)) = ((Real.pi / a : ℝ) : ℂ) by push_cast; ring,
      show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), Complex.ofReal_inj,
      ← Real.sqrt_eq_rpow]
  have h2 : Complex.exp (-((t : ℝ) : ℂ) ^ 2 / (4 * (a : ℂ)))
      = ((Real.exp (-(t ^ 2 / (4 * a))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [h1, h2, ← Complex.ofReal_mul, Complex.ofReal_re]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t61_integral_Ioi_exp_neg_half (a : ℝ) :
    IntegrableOn (fun x => Real.exp (-(x / 2))) (Set.Ioi a)
    ∧ ∫ x in Set.Ioi a, Real.exp (-(x / 2)) = 2 * Real.exp (-(a / 2)) := by
  have _em := Classical.em
  have hderiv : ∀ x ∈ Set.Ici a,
      HasDerivAt (fun y => -(2 : ℝ) * Real.exp (-(y / 2))) (Real.exp (-(x / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(y / 2)) (-(1 / 2)) x :=
      ((hasDerivAt_id x).div_const 2).neg
    have h3 := ((Real.hasDerivAt_exp (-(x / 2))).comp x h1).const_mul (-2 : ℝ)
    convert h3 using 1 <;> first | (with_reducible_and_instances rfl) | rfl | ring
  have htend : Tendsto (fun y : ℝ => -(2 : ℝ) * Real.exp (-(y / 2))) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => -(y / 2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp
        (Tendsto.atTop_div_const (by norm_num : (0:ℝ) < 2) tendsto_id)
    have h2 : Tendsto (fun y : ℝ => Real.exp (-(y / 2))) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul (-2 : ℝ)
  have hcont : ContinuousWithinAt
      (fun y => -(2:ℝ) * Real.exp (-(y / 2))) (Set.Ici a) a :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2).neg).const_mul
      (-2:ℝ)).continuousWithinAt
  have hint : IntegrableOn (fun x => Real.exp (-(x / 2))) (Set.Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg hcont (fun x hx => hderiv x (Set.mem_Ici_of_Ioi hx))
      (fun x _ => (Real.exp_pos _).le) htend
  exact ⟨hint, by
    have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
    simp only [neg_mul] at this; linarith⟩

end FLT.Gapsw80T61D2cbArchGammaParsevalFalseprobe
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T18ArchDerivedA34Redecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T13AffineArchTermA34Redecomp
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t18_poleTerm_nonneg {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) :
    0 ≤ gapsw80_t13_poleTerm F := by
  have _em := Classical.em
  have hFpos : ∀ x : ℝ, 0 ≤ F x := hF.2.2.2.1
  have hInt : 0 ≤ ∫ x in Set.Ioi (0:ℝ),
      F x * (Real.exp (x / 2) + Real.exp (-(x / 2))) := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro x _
    exact mul_nonneg (hFpos x)
      (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  simp only [gapsw80_t13_poleTerm]
  linarith [hInt]

noncomputable def gapsw80_t18_archDerived (F : ℝ → ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
    - ∫ x in Set.Ioi (0:ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2)))

noncomputable def gapsw80_t18_archTermDerived (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * gapsw80_t18_archDerived F - gapsw80_t13_poleTerm F

set_option maxHeartbeats 3200000 in

theorem gapsw80_t18_archTermDerived_pin (F : ℝ → ℝ) (n : ℕ) :
    gapsw80_t18_archTermDerived F n =
      (n : ℝ) * gapsw80_t18_archDerived F - gapsw80_t13_poleTerm F := by
  have _em := Classical.em
  rfl

end FLT.Gapsw80T18ArchDerivedA34Redecomp
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T65D2caDigammaSeriesSubDecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
open FLT.Gapsw80T61D2cbArchGammaParsevalFalseprobe
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T63CosineInversionWire
open FLT.Gapsw80T64D2fGaussianMollificationProof
p2m_open "Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex Real P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Real MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory Filter P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Filter Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology Set P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Set"
p2m_open_scoped "Nat P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Nat Filter.Nat Set.Nat"

set_option maxHeartbeats 12800000 in

theorem gapsw80_t65_integral_exp_neg_one_sub_cos {a : ℝ} (ha : 0 < a) (t : ℝ) :
    IntegrableOn (fun x => Real.exp (-(a * x)) * (1 - Real.cos (t * x))) (Ioi (0:ℝ))
    ∧ ∫ x in Ioi (0:ℝ), Real.exp (-(a * x)) * (1 - Real.cos (t * x))
        = 1 / a - a / (a ^ 2 + t ^ 2) := by
  have _em := Classical.em

  have hexp_int : IntegrableOn (fun x => Real.exp (-(a * x))) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
    simpa only [neg_mul] using this

  have hint : IntegrableOn
      (fun x => Real.exp (-(a * x)) * (1 - Real.cos (t * x))) (Ioi (0:ℝ)) := by
    apply hexp_int.mul_const 2 |>.mono'
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (continuous_const.sub (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
      have hc : |1 - Real.cos (t * x)| ≤ 2 := by
        have h1 := Real.neg_one_le_cos (t * x)
        have h2 := Real.cos_le_one (t * x)
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
  refine ⟨hint, ?_⟩

  have hI1 : ∫ x in Ioi (0:ℝ), Real.exp (-(a * x)) = 1 / a := by
    have := integral_exp_mul_Ioi (a := -a) (by linarith) 0
    simp only [neg_mul, mul_zero, Real.exp_zero, neg_neg] at this
    rw [this]; ring

  have hcz : ((-(a:ℂ) - I * t)).re < 0 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, sub_zero]
    linarith
  have hcint : IntegrableOn (fun x : ℝ => Complex.exp ((-(a:ℂ) - I * t) * x))
      (Ioi (0:ℝ)) := integrableOn_exp_mul_complex_Ioi hcz 0
  have hCI : ∫ x in Ioi (0:ℝ), Complex.exp ((-(a:ℂ) - I * t) * x)
      = 1 / ((a:ℂ) + I * t) := by
    rw [integral_exp_mul_complex_Ioi hcz]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    rw [show (-(a:ℂ) - I * t) = -((a:ℂ) + I * t) by ring, neg_div_neg_eq, one_div]
  have hre_pt : ∀ x : ℝ,
      (Complex.exp ((-(a:ℂ) - I * t) * x)).re
        = Real.exp (-(a * x)) * Real.cos (t * x) := by
    intro x
    rw [Complex.exp_re]
    congr 1
    · congr 1
      simp only [Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, Complex.I_im,
        mul_zero, sub_zero, Complex.sub_im, Complex.neg_im, Complex.mul_im, one_mul,
        zero_add, _root_.neg_zero, zero_sub]
      ring
    · have : ((-(a:ℂ) - I * t) * x).im = -(t * x) := by
        simp only [Complex.mul_im, Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, Complex.I_im,
          mul_zero, sub_zero, Complex.sub_im, Complex.neg_im, Complex.mul_im, one_mul,
          zero_add, _root_.neg_zero, zero_sub]
        ring
      rw [this, Real.cos_neg]
  have hI2 : ∫ x in Ioi (0:ℝ), Real.exp (-(a * x)) * Real.cos (t * x)
      = a / (a ^ 2 + t ^ 2) := by
    have hre := (Complex.reCLM.integral_comp_comm hcint).symm
    simp only [Complex.reCLM_apply] at hre
    rw [hCI] at hre
    have hre_rhs : (1 / ((a:ℂ) + I * t)).re = a / (a ^ 2 + t ^ 2) := by
      rw [one_div, Complex.inv_re, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, zero_mul, Complex.I_im, mul_zero, sub_zero, add_zero,
        Complex.add_im, Complex.ofReal_im, Complex.mul_im, one_mul, zero_add]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => (hre_pt x).symm),
      ← hre, hre_rhs]

  have hcos_int : IntegrableOn
      (fun x => Real.exp (-(a * x)) * Real.cos (t * x)) (Ioi (0:ℝ)) := by
    apply hexp_int.mono'
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
      calc Real.exp (-(a * x)) * |Real.cos (t * x)|
          ≤ Real.exp (-(a * x)) * 1 :=
            mul_le_mul_of_nonneg_left (abs_cos_le_one _) (Real.exp_pos _).le
        _ = Real.exp (-(a * x)) := mul_one _
  calc ∫ x in Ioi (0:ℝ), Real.exp (-(a * x)) * (1 - Real.cos (t * x))
      = ∫ x in Ioi (0:ℝ),
          (Real.exp (-(a * x)) - Real.exp (-(a * x)) * Real.cos (t * x)) := by
        congr 1; ext x; ring
    _ = (∫ x in Ioi (0:ℝ), Real.exp (-(a * x)))
        - ∫ x in Ioi (0:ℝ), Real.exp (-(a * x)) * Real.cos (t * x) :=
        integral_sub hexp_int hcos_int
    _ = 1 / a - a / (a ^ 2 + t ^ 2) := by rw [hI1, hI2]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t65_hasSum_exp_neg_half_shift {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-(((n:ℝ) + 1/2) * x)))
      (1 / (Real.exp (x/2) - Real.exp (-(x/2)))) := by
  have _em := Classical.em
  have h1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h0 : (0:ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hgeo : HasSum (fun n : ℕ => Real.exp (-x) ^ n) (1 - Real.exp (-x))⁻¹ :=
    hasSum_geometric_of_lt_one h0 h1
  have hmul := hgeo.mul_left (Real.exp (-(x/2)))
  have hfun : ∀ n : ℕ, Real.exp (-(x/2)) * Real.exp (-x) ^ n
      = Real.exp (-(((n:ℝ) + 1/2) * x)) := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have hval : Real.exp (-(x/2)) * (1 - Real.exp (-x))⁻¹
      = 1 / (Real.exp (x/2) - Real.exp (-(x/2))) := by
    have hden : Real.exp (x/2) - Real.exp (-(x/2)) > 0 := by
      have := Real.exp_lt_exp.mpr (show -(x/2) < x/2 by linarith)
      linarith
    have hne : (1 : ℝ) - Real.exp (-x) ≠ 0 := by linarith
    rw [eq_div_iff hden.ne', mul_comm, ← mul_assoc, sub_mul,
      ← Real.exp_add, ← Real.exp_add]
    have : x/2 + -(x/2) = (0:ℝ) := by ring
    rw [this, Real.exp_zero]
    have h2 : -(x/2) + -(x/2) = -x := by ring
    rw [h2, mul_inv_cancel₀ hne]
  rw [← hval]
  exact hmul.congr_fun (fun n => (hfun n).symm)

set_option maxHeartbeats 25600000 in

theorem gapsw80_t65_series_eq_K1 (t : ℝ) :
    HasSum (fun n : ℕ => 1 / ((n:ℝ) + 1/2) - ((n:ℝ) + 1/2) / (((n:ℝ) + 1/2)^2 + t^2))
      (∫ x in Ioi (0:ℝ),
        (1 - Real.cos (t * x)) / (Real.exp (x/2) - Real.exp (-(x/2)))) := by
  have _em := Classical.em

  have hpos : ∀ n : ℕ, (0:ℝ) < (n:ℝ) + 1/2 := fun n => by positivity
  have hnonneg : ∀ n : ℕ,
      (0:ℝ) ≤ 1 / ((n:ℝ) + 1/2) - ((n:ℝ) + 1/2) / (((n:ℝ) + 1/2)^2 + t^2) := by
    intro n
    have hp := hpos n
    have hd : (0:ℝ) < ((n:ℝ) + 1/2)^2 + t^2 := by positivity
    have : 1 / ((n:ℝ) + 1/2) - ((n:ℝ) + 1/2) / (((n:ℝ) + 1/2)^2 + t^2)
        = t^2 / (((n:ℝ) + 1/2) * (((n:ℝ) + 1/2)^2 + t^2)) := by
      field_simp; ring
    rw [this]; positivity

  have hterm : ∀ n : ℕ,
      1 / ((n:ℝ) + 1/2) - ((n:ℝ) + 1/2) / (((n:ℝ) + 1/2)^2 + t^2)
        = ∫ x in Ioi (0:ℝ), Real.exp (-(((n:ℝ)+1/2) * x)) * (1 - Real.cos (t * x)) :=
    fun n => (gapsw80_t65_integral_exp_neg_one_sub_cos (hpos n) t).2.symm

  have hsum_bd : Summable (fun n : ℕ => t^2 / ((n:ℝ) + 1/2)^3) := by
    have h3 := (Real.summable_one_div_nat_add_rpow (1/2) 3).mpr (by norm_num)
    apply (h3.mul_left (t^2)).congr
    intro n
    rw [abs_of_pos (hpos n), show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    push_cast; ring
  have hsum : Summable (fun n : ℕ =>
      1 / ((n:ℝ) + 1/2) - ((n:ℝ) + 1/2) / (((n:ℝ) + 1/2)^2 + t^2)) := by
    refine Summable.of_nonneg_of_le hnonneg (fun n => ?_) hsum_bd
    have hp := hpos n
    have hd : (0:ℝ) < ((n:ℝ) + 1/2)^2 + t^2 := by positivity
    have heq : 1 / ((n:ℝ) + 1/2) - ((n:ℝ) + 1/2) / (((n:ℝ) + 1/2)^2 + t^2)
        = t^2 / (((n:ℝ) + 1/2) * (((n:ℝ) + 1/2)^2 + t^2)) := by field_simp; ring
    rw [heq]
    apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
    have : ((n:ℝ) + 1/2)^3 = ((n:ℝ) + 1/2) * ((n:ℝ) + 1/2)^2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg t]) hp.le

  set f : ℕ → ℝ → ℝ :=
    fun n x => Real.exp (-(((n:ℝ)+1/2) * x)) * (1 - Real.cos (t * x)) with hf_def
  have hf_meas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Ioi (0:ℝ))) :=
    fun n => ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).neg)).mul
      (continuous_const.sub (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)))).aestronglyMeasurable.restrict
  have hf_nn : ∀ n, ∀ x ∈ Ioi (0:ℝ), 0 ≤ f n x := by
    intro n x _
    apply mul_nonneg (Real.exp_pos _).le
    linarith [Real.cos_le_one (t * x)]
  have hf_int : ∀ n, IntegrableOn (f n) (Ioi (0:ℝ)) :=
    fun n => (gapsw80_t65_integral_exp_neg_one_sub_cos (hpos n) t).1
  have hf_norm : Summable (fun n => ∫ x in Ioi (0:ℝ), ‖f n x‖) := by
    apply hsum.congr
    intro n
    rw [hterm n]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
      (Real.norm_of_nonneg (hf_nn n x hx)).symm)

  have htsum_int : ∫ x in Ioi (0:ℝ), ∑' n, f n x = ∑' n, ∫ x in Ioi (0:ℝ), f n x :=
    (integral_tsum_of_summable_integral_norm hf_int hf_norm).symm

  have hpoint : ∀ x ∈ Ioi (0:ℝ),
      ∑' n, f n x = (1 - Real.cos (t * x)) / (Real.exp (x/2) - Real.exp (-(x/2))) := by
    intro x hx
    have h0b := gapsw80_t65_hasSum_exp_neg_half_shift (mem_Ioi.mp hx)
    have hmr := h0b.mul_right (1 - Real.cos (t * x))
    rw [div_mul_eq_mul_div, one_mul] at hmr
    exact hmr.tsum_eq

  have hInt : (∫ x in Ioi (0:ℝ),
      (1 - Real.cos (t * x)) / (Real.exp (x/2) - Real.exp (-(x/2))))
        = ∑' n : ℕ,
            (1 / ((n:ℝ) + 1/2) - ((n:ℝ) + 1/2) / (((n:ℝ) + 1/2)^2 + t^2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => (hpoint x hx).symm),
      htsum_int]
    exact tsum_congr (fun n => (hterm n).symm)
  rw [hInt]
  exact hsum.hasSum

def gapsw80_t65_DigammaReSeriesHalfLine : Prop :=
  ∀ t : ℝ,
    HasSum (fun n : ℕ => 1 / ((n:ℝ) + 1/2) - ((n:ℝ) + 1/2) / (((n:ℝ) + 1/2)^2 + t^2))
      ((logDeriv Complex.Gamma (1/2 + (t:ℂ) * I)).re
        + Real.eulerMascheroniConstant + 2 * Real.log 2)

set_option maxHeartbeats 6400000 in

theorem gapsw80_t65_D2ca_of_D2cai
    (hD2cai : gapsw80_t65_DigammaReSeriesHalfLine) :
    gapsw80_t60_DigammaReCriticalLineCosKernel := by
  have _em := Classical.em
  intro t
  have h1 := (hD2cai t).unique (gapsw80_t65_series_eq_K1 t)
  linarith [h1]

end FLT.Gapsw80T65D2caDigammaSeriesSubDecomp
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T66D2caiDigammaSeriesProof

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
open FLT.Gapsw80T61D2cbArchGammaParsevalFalseprobe
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T63CosineInversionWire
open FLT.Gapsw80T64D2fGaussianMollificationProof
open FLT.Gapsw80T65D2caDigammaSeriesSubDecomp
p2m_open "Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex Real P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Real MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory Filter P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Filter Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology Set P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Set"
p2m_open_scoped "Nat P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Nat Filter.Nat Set.Nat"

local notation "ψ" => logDeriv Complex.Gamma
local notation "γ" => Real.eulerMascheroniConstant

private noncomputable def wF (n : ℕ) (z : ℂ) : ℂ :=
  Complex.log (1 + (z - 1)/((n:ℂ)+1)) - (z - 1)/((n:ℂ)+1)

private lemma wF_arg_eq (n : ℕ) (z : ℂ) :
    1 + (z - 1)/((n:ℂ)+1) = (z + n)/((n:ℂ)+1) := by
  field_simp [Nat.cast_add_one_ne_zero n]; ring

private lemma wF_arg_re_pos {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    0 < (1 + (z - 1)/((n:ℂ)+1)).re := by
  rw [wF_arg_eq, show ((n:ℂ)+1 : ℂ) = (((n:ℝ)+1 : ℝ) : ℂ) by push_cast; ring,
    Complex.div_ofReal_re, Complex.add_re, Complex.natCast_re]
  have : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
  exact div_pos (by linarith) (by linarith)

private lemma hasDerivAt_wF {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    HasDerivAt (wF n) (1/(z + n) - 1/((n:ℂ)+1)) z := by
  have hslit : 1 + (z-1)/((n:ℂ)+1) ∈ Complex.slitPlane := Or.inl (wF_arg_re_pos hz n)
  have hlin : HasDerivAt (fun w => 1 + (w-1)/((n:ℂ)+1)) (1/((n:ℂ)+1)) z :=
    (((hasDerivAt_id z).sub_const 1).div_const _).const_add 1
  have hlog := (Complex.hasDerivAt_log hslit).comp z hlin
  have h1 : HasDerivAt (fun w => Complex.log (1 + (w-1)/((n:ℂ)+1))) (1/(z+n)) z := by
    convert hlog using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    rw [wF_arg_eq]; field_simp [Nat.cast_add_one_ne_zero n]
  exact (h1.sub (((hasDerivAt_id z).sub_const 1).div_const _) : _)

private lemma summable_wF {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n => wF n z) := by
  apply summable_of_isBigO_nat (g := fun n => 1/((n:ℝ)+1)^2)
    (((Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two).congr
      (fun n => by rw [abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1), one_div]; norm_num))
  apply Asymptotics.IsBigO.of_bound (c := ‖z-1‖^2)
  filter_upwards [Filter.eventually_ge_atTop (⌈2*‖z-1‖⌉₊)] with n hn
  have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
  have hwbd : ‖(z-1)/((n:ℂ)+1)‖ ≤ ‖z-1‖/((n:ℝ)+1) := by
    rw [norm_div, show ((n:ℂ)+1:ℂ) = (((n:ℝ)+1:ℝ):ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hw12 : ‖(z-1)/((n:ℂ)+1)‖ ≤ 1/2 := hwbd.trans (by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    have hc : (2*‖z-1‖:ℝ) ≤ ⌈2*‖z-1‖⌉₊ := Nat.le_ceil _
    have hnn : ((⌈2*‖z-1‖⌉₊:ℕ):ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith)
  have hw1 : ‖(z-1)/((n:ℂ)+1)‖ < 1 := hw12.trans_lt (by norm_num)
  have hbd := Complex.norm_log_one_add_sub_self_le hw1
  simp only [wF]
  refine hbd.trans ?_
  rw [Real.norm_of_nonneg (by positivity)]
  have hinv : (1 - ‖(z-1)/((n:ℂ)+1)‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]; linarith
  calc ‖(z-1)/((n:ℂ)+1)‖^2 * (1-‖(z-1)/((n:ℂ)+1)‖)⁻¹ / 2
      ≤ (‖z-1‖/((n:ℝ)+1))^2 * 2 / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hwbd 2) hinv
            (by positivity) (by positivity)) two_pos.le
    _ = ‖z-1‖^2 * (1/((n:ℝ)+1)^2) := by field_simp

set_option maxHeartbeats 12800000 in

private lemma exp_partial_wF_eq {z : ℂ} (hz : 0 < z.re) (N : ℕ) (hN : 1 ≤ N) :
    Complex.exp (∑ n ∈ Finset.range (N+1), wF n z)
      = ((N:ℂ)/(N+1)) * Complex.exp ((z-1) * (Real.log N - (harmonic (N+1) : ℝ)))
          / Complex.GammaSeq z N := by
  have hNc : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hN)
  have hN1c : ((N:ℂ)+1) ≠ 0 := Nat.cast_add_one_ne_zero N
  have hprod_ne : ∏ j ∈ Finset.range (N+1), (z+(j:ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ h => ?_
    have hre : (z+(i:ℂ)).re = 0 := by rw [h]; rfl
    simp only [Complex.add_re, Complex.natCast_re] at hre
    linarith [hz, (i.cast_nonneg : (0:ℝ) ≤ (i:ℝ))]

  have hstep1 : Complex.exp (∑ n ∈ Finset.range (N+1), wF n z)
      = (∏ n ∈ Finset.range (N+1), ((z+n)/((n:ℂ)+1)))
          * Complex.exp (-(z-1) * ((harmonic (N+1) : ℝ) : ℂ)) := by
    rw [Complex.exp_sum]
    have hexp_wF : ∀ n ∈ Finset.range (N+1), Complex.exp (wF n z)
        = (z+n)/((n:ℂ)+1) * Complex.exp (-((z-1)/((n:ℂ)+1))) := fun n _ => by
      have hne : 1 + (z-1)/((n:ℂ)+1) ≠ 0 := fun h => by
        have := wF_arg_re_pos hz n; rw [h] at this; simp at this
      rw [wF, sub_eq_add_neg, Complex.exp_add, Complex.exp_log hne, wF_arg_eq,
        ← neg_div]
    rw [Finset.prod_congr rfl hexp_wF, Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 2
    have hsum_eq : ∑ x ∈ Finset.range (N+1), -((z-1)/((x:ℂ)+1))
        = -(z-1) * ((harmonic (N+1) : ℝ) : ℂ) := by
      rw [show ((harmonic (N+1) : ℝ) : ℂ) = ∑ i ∈ Finset.range (N+1), ((i:ℂ)+1)⁻¹ by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          Complex.ofReal_sum, Complex.ofReal_inv, Complex.ofReal_natCast]
        exact Finset.sum_congr rfl fun n _ => by push_cast; ring,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    exact hsum_eq

  have hstep2 : (∏ n ∈ Finset.range (N+1), ((z+n)/((n:ℂ)+1)))
      = (N:ℂ)^z / (((N:ℂ)+1) * Complex.GammaSeq z N) := by
    have hfact : (∏ n ∈ Finset.range (N+1), ((n:ℂ)+1)) = ((N+1)! : ℂ) := by
      have := Finset.prod_range_add_one_eq_factorial (N+1)
      exact_mod_cast this
    have hcpow_ne : (N:ℂ)^z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hNc)
    have hfactN : ((N ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
    rw [Finset.prod_div_distrib, hfact, Complex.GammaSeq,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [hstep1, hstep2]

  have hNz : (N:ℂ)^z = (N:ℂ) * Complex.exp ((z-1) * (Real.log N : ℂ)) := by
    conv_lhs => rw [show z = (z-1) + 1 by ring]
    rw [Complex.cpow_add _ _ hNc, Complex.cpow_one,
      Complex.cpow_def_of_ne_zero hNc, ← Complex.natCast_log]
    ring_nf
  have hGSne : Complex.GammaSeq z N ≠ 0 := by
    rw [Complex.GammaSeq]; exact div_ne_zero
      (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hNc))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))) hprod_ne
  rw [hNz, mul_sub, Complex.exp_sub, show -(z-1) * ((harmonic (N+1):ℝ):ℂ)
    = -((z-1) * ((harmonic (N+1):ℝ):ℂ)) by ring, Complex.exp_neg]
  field_simp

set_option maxHeartbeats 25600000 in

private lemma exp_tsum_wF_eq {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (∑' n, wF n z) = Complex.exp (-(γ:ℂ) * (z-1)) / Complex.Gamma z := by
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero fun m h => by
    rw [h] at hz; simp only [Complex.neg_re, Complex.natCast_re] at hz
    linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]

  have hsum := summable_wF hz
  have htend1 : Tendsto (fun N => Complex.exp (∑ n ∈ Finset.range N, wF n z))
      atTop (𝓝 (Complex.exp (∑' n, wF n z))) :=
    (Complex.continuous_exp.tendsto _).comp hsum.hasSum.tendsto_sum_nat

  have htend1' : Tendsto (fun N => Complex.exp (∑ n ∈ Finset.range (N+1), wF n z))
      atTop (𝓝 (Complex.exp (∑' n, wF n z))) :=
    htend1.comp (tendsto_add_atTop_nat 1)

  have htend_frac : Tendsto (fun N : ℕ => ((N:ℂ)/((N:ℂ)+1))) atTop (𝓝 1) := by
    have hℝ : Tendsto (fun N : ℕ => ((N:ℝ)/((N:ℝ)+1))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun N : ℕ => (1:ℝ)/((N:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun N : ℕ => (1:ℝ) - 1/((N:ℝ)+1)) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1:ℝ))).sub h0
        simpa using this
      refine h1.congr fun n => ?_
      have hpos : ((n:ℝ)+1) ≠ 0 := by positivity
      rw [one_sub_div hpos, add_sub_cancel_right]
    have hc := (Complex.continuous_ofReal.tendsto (1:ℝ)).comp hℝ
    simp only [Complex.ofReal_one] at hc
    refine hc.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast; ring
  have htend_logH : Tendsto (fun N : ℕ => (Real.log N - (harmonic (N+1) : ℝ) : ℝ))
      atTop (𝓝 (-γ)) := by
    have h1 : Tendsto (fun N : ℕ => ((harmonic N : ℝ) - Real.log N)) atTop (𝓝 γ) :=
      Real.tendsto_harmonic_sub_log
    have h2 : Tendsto (fun N : ℕ => ((harmonic (N+1) : ℝ) - Real.log ((N:ℝ)+1))) atTop
        (𝓝 γ) := by
      refine (h1.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have h3 : Tendsto (fun N : ℕ => Real.log ((N:ℝ)+1) - Real.log N) atTop (𝓝 0) := by
      have hlog := Real.tendsto_log_comp_add_sub_log 1
      refine (hlog.comp tendsto_natCast_atTop_atTop).congr fun n => ?_
      simp only [Function.comp_apply]
    have h4 := (h2.neg).sub h3
    rw [show -γ - (0:ℝ) = -γ from sub_zero _] at h4
    refine h4.congr fun n => ?_
    push_cast; ring
  have htend_exp : Tendsto
      (fun N : ℕ => Complex.exp ((z-1) * ↑(Real.log N - (harmonic (N+1) : ℝ))))
      atTop (𝓝 (Complex.exp (-(γ:ℂ) * (z-1)))) := by
    have hc : Continuous (fun r : ℝ => Complex.exp ((z-1) * (r:ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    have hcomp := (hc.tendsto (-γ)).comp htend_logH
    refine Tendsto.congr' (Filter.Eventually.of_forall fun n => rfl)
      (hcomp.mono_right (le_of_eq ?_))
    congr 1; push_cast; ring_nf
  have htend_GS : Tendsto (fun N : ℕ => Complex.GammaSeq z N) atTop (𝓝 (Complex.Gamma z)) :=
    Complex.GammaSeq_tendsto_Gamma z
  have htend2 : Tendsto
      (fun N : ℕ => ((N:ℂ)/((N:ℂ)+1))
        * Complex.exp ((z-1) * ↑(Real.log N - (harmonic (N+1):ℝ)))
        / Complex.GammaSeq z N)
      atTop (𝓝 (Complex.exp (-(γ:ℂ) * (z-1)) / Complex.Gamma z)) := by
    have := (htend_frac.mul htend_exp).div htend_GS hΓne
    simp at this ⊢
    exact this

  have heq : ∀ᶠ N in atTop, Complex.exp (∑ n ∈ Finset.range (N+1), wF n z)
      = ((N:ℂ)/((N:ℂ)+1))
          * Complex.exp ((z-1) * ↑(Real.log N - (harmonic (N+1):ℝ)))
          / Complex.GammaSeq z N := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [exp_partial_wF_eq hz N hN, Complex.ofReal_sub]
  exact tendsto_nhds_unique htend1' (htend2.congr' (heq.mono fun N h => h.symm))

set_option maxHeartbeats 51200000 in

theorem gapsw80_t66_hasSum_psi_series {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => 1/((n:ℂ)+1) - 1/((n:ℂ)+s)) (ψ s + γ) := by
  have _em := Classical.em

  set r := s.re / 2
  have hr : 0 < r := by positivity
  set B : Set ℂ := Metric.ball s r
  have hB_open : IsOpen B := Metric.isOpen_ball
  have hs_in : s ∈ B := Metric.mem_ball_self hr
  have hB_re_ge : ∀ z ∈ B, r ≤ z.re := fun z hzB => by
    have hd : dist z s < r := hzB
    have hre : |z.re - s.re| ≤ dist z s := by
      rw [Complex.dist_eq, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have habs := (hre.trans_lt hd).le
    have h1 := (abs_le.mp habs).1
    have hreq : r = s.re / 2 := rfl
    linarith
  have hB_re : ∀ z ∈ B, 0 < z.re := fun z hzB => hr.trans_le (hB_re_ge z hzB)

  set R := ‖s - 1‖ + r
  have hR0 : 0 < R := by positivity
  have hR_bd : ∀ z ∈ B, ‖z - (1:ℂ)‖ ≤ R := fun z hzB => by
    have hzs : ‖z - s‖ < r := by rw [← Complex.dist_eq]; exact hzB
    calc ‖z - 1‖ = ‖(z - s) + (s - 1)‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s - 1‖ := norm_add_le _ _
      _ ≤ R := by linarith

  set N₀ : ℕ := ⌈2*R⌉₊
  set δ := min r (1/2)
  have hδ : 0 < δ := lt_min hr one_half_pos
  set M := |Real.log δ| + Real.log (1 + R) + 4 + R
  set u : ℕ → ℝ := fun n => R^2 / ((n:ℝ)+1)^2 + if n < N₀ then M else 0
  have hu_sum : Summable u := by
    apply Summable.add
    · have hs2 := ((Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two).mul_left (R^2)
      refine hs2.congr (fun n => ?_)
      rw [abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1), mul_one_div]
      norm_num
    · exact summable_of_finite_support
        (Set.Finite.subset (Set.finite_Iio N₀) (fun n hn => by
          simp only [Function.mem_support, ite_ne_right_iff] at hn; exact hn.1))
  have hwF_bd : ∀ (n : ℕ) (z : ℂ), z ∈ B → ‖wF n z‖ ≤ u n := by
    intro n z hzB
    have hzre := hB_re z hzB
    have hzre_ge := hB_re_ge z hzB
    have hw : ‖(z-1)/((n:ℂ)+1)‖ ≤ R / ((n:ℝ)+1) := by
      rw [norm_div, show ((n:ℂ)+1 : ℂ) = (((n:ℝ)+1:ℝ):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (hR_bd z hzB) (by positivity)
    by_cases hn : n < N₀
    ·
      simp only [wF, u, if_pos hn]
      have hwR : ‖(z-1)/((n:ℂ)+1)‖ ≤ R := hw.trans
        (div_le_self hR0.le (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]))
      set ζ := 1 + (z-1)/((n:ℂ)+1) with hζ_def
      have hζre : 0 < ζ.re := wF_arg_re_pos hzre n
      have hζre_ge : δ ≤ ζ.re := by
        rw [hζ_def, wF_arg_eq,
          show ((n:ℂ)+1:ℂ) = (((n:ℝ)+1:ℝ):ℂ) by push_cast; ring,
          Complex.div_ofReal_re, Complex.add_re, Complex.natCast_re]
        have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
        rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · subst hn0; simp only [Nat.cast_zero, add_zero, zero_add, div_one]
          exact (min_le_left _ _).trans hzre_ge
        · refine (min_le_right _ _).trans ?_
          have hn1r : (1:ℝ) ≤ (n:ℝ) := Nat.one_le_cast.mpr hn1
          rw [le_div_iff₀ (by linarith)]
          linarith
      have hζnorm_le : ‖ζ‖ ≤ 1 + R := by
        calc ‖ζ‖ = ‖1 + (z-1)/((n:ℂ)+1)‖ := rfl
          _ ≤ ‖(1:ℂ)‖ + ‖(z-1)/((n:ℂ)+1)‖ := norm_add_le _ _
          _ ≤ 1 + R := by rw [norm_one]; linarith
      have hζnorm_ge : δ ≤ ‖ζ‖ := hζre_ge.trans
        ((le_abs_self _).trans (Complex.abs_re_le_norm ζ))
      have hlogζ : ‖Complex.log ζ‖ ≤ |Real.log δ| + Real.log (1+R) + 4 := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [Complex.log_re, Complex.log_im]
        have harg : |ζ.arg| ≤ π := Complex.abs_arg_le_pi ζ
        have hπ4 : π < 4 := Real.pi_lt_four
        have hlognorm : |Real.log ‖ζ‖| ≤ |Real.log δ| + Real.log (1+R) := by
          have hlog_le : Real.log ‖ζ‖ ≤ Real.log (1+R) :=
            Real.log_le_log (hδ.trans_le hζnorm_ge) hζnorm_le
          have hlog_ge : Real.log δ ≤ Real.log ‖ζ‖ :=
            Real.log_le_log hδ hζnorm_ge
          have hlogδ_neg : Real.log δ ≤ 0 :=
            Real.log_nonpos hδ.le ((min_le_right r (1/2)).trans (by norm_num))
          have hlogR_pos : 0 ≤ Real.log (1+R) := Real.log_nonneg (by linarith)
          rcases le_or_gt 0 (Real.log ‖ζ‖) with hpos | hneg
          · rw [abs_of_nonneg hpos]
            calc Real.log ‖ζ‖ ≤ Real.log (1+R) := hlog_le
              _ ≤ |Real.log δ| + Real.log (1+R) := le_add_of_nonneg_left (abs_nonneg _)
          · rw [abs_of_neg hneg]
            have : -Real.log ‖ζ‖ ≤ -Real.log δ := neg_le_neg hlog_ge
            calc -Real.log ‖ζ‖ ≤ -Real.log δ := this
              _ = |Real.log δ| := (abs_of_nonpos hlogδ_neg).symm
              _ ≤ |Real.log δ| + Real.log (1+R) := le_add_of_nonneg_right hlogR_pos
        linarith
      calc ‖Complex.log ζ - (z-1)/((n:ℂ)+1)‖
          ≤ ‖Complex.log ζ‖ + ‖(z-1)/((n:ℂ)+1)‖ := norm_sub_le _ _
        _ ≤ (|Real.log δ| + Real.log (1+R) + 4) + R := add_le_add hlogζ hwR
        _ = M := by ring
        _ ≤ R^2/((n:ℝ)+1)^2 + M := le_add_of_nonneg_left (by positivity)
    ·
      have hwn : ‖(z-1)/((n:ℂ)+1)‖ ≤ 1/2 := by
        refine hw.trans ?_
        rw [div_le_div_iff₀ (by positivity) two_pos]
        have hc : (2*R:ℝ) ≤ N₀ := Nat.le_ceil _
        have hnn : (N₀:ℝ) ≤ n := Nat.cast_le.mpr (not_lt.mp hn)
        linarith
      have hwn1 : ‖(z-1)/((n:ℂ)+1)‖ < 1 := hwn.trans_lt (by norm_num)
      have hbd := Complex.norm_log_one_add_sub_self_le hwn1
      simp only [wF, u, if_neg hn, add_zero]
      refine hbd.trans ?_
      have hsq : ‖(z-1)/((n:ℂ)+1)‖^2 ≤ (R/((n:ℝ)+1))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hw 2
      have hinv : (1 - ‖(z-1)/((n:ℂ)+1)‖)⁻¹ ≤ (2:ℝ) := by
        rw [inv_le_comm₀ (by linarith) two_pos]
        linarith
      have hrhs_eq : (R/((n:ℝ)+1))^2 * 2 / 2 = R^2/((n:ℝ)+1)^2 := by
        rw [mul_div_cancel_right₀ _ two_ne_zero, div_pow]
      rw [← hrhs_eq]
      apply div_le_div_of_nonneg_right _ two_pos.le
      apply mul_le_mul hsq hinv (by positivity) (by positivity)
  have hwF_diff : ∀ n, DifferentiableOn ℂ (wF n) B := fun n z hzB =>
    (hasDerivAt_wF (hB_re z hzB) n).differentiableAt.differentiableWithinAt

  have hsd := hasSum_deriv_of_summable_norm hu_sum hwF_diff hB_open hwF_bd hs_in

  have hderiv_eq : ∀ n, deriv (wF n) s = 1/(s+n) - 1/((n:ℂ)+1) := fun n =>
    (hasDerivAt_wF hs n).deriv

  set G : ℂ → ℂ := fun z => ∑' n, wF n z
  set Q : ℂ → ℂ := fun z => Complex.exp (-(γ:ℂ) * (z-1)) / Complex.Gamma z
  have hG_diff : DifferentiableOn ℂ G B :=
    differentiableOn_tsum_of_summable_norm hu_sum hwF_diff hB_open hwF_bd
  have hGs_diff : DifferentiableAt ℂ G s :=
    (hG_diff s hs_in).differentiableAt (hB_open.mem_nhds hs_in)
  have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (fun m h => by
    rw [h] at hs; simp only [Complex.neg_re, Complex.natCast_re] at hs
    linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
  have hQ_diff : DifferentiableAt ℂ Q s := by
    apply DifferentiableAt.div
    · exact (Complex.differentiable_exp.comp
        (differentiable_id.sub_const 1 |>.const_mul _)).differentiableAt
    · exact Complex.differentiableAt_Gamma s (fun m h => by
        rw [h] at hs; simp only [Complex.neg_re, Complex.natCast_re] at hs
        linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
    · exact hΓne

  have hEG_eq : (fun z => Complex.exp (G z)) =ᶠ[𝓝 s] Q := by
    filter_upwards [hB_open.mem_nhds hs_in] with z hzB
    exact exp_tsum_wF_eq (hB_re z hzB)

  have hexpG_deriv : HasDerivAt (fun z => Complex.exp (G z))
      (Complex.exp (G s) * deriv G s) s :=
    (Complex.hasDerivAt_exp (G s)).comp s hGs_diff.hasDerivAt
  have hQ_deriv : HasDerivAt Q (deriv Q s) s := hQ_diff.hasDerivAt
  have heq_deriv : Complex.exp (G s) * deriv G s = deriv Q s := by
    have := hEG_eq.deriv_eq
    rw [← hexpG_deriv.deriv, this]
  have hexpGs : Complex.exp (G s) = Q s := hEG_eq.eq_of_nhds
  have hQs_ne : Q s ≠ 0 := by
    simp only [Q, ne_eq, div_eq_zero_iff, Complex.exp_ne_zero, false_or]
    exact hΓne
  have hG'_eq : deriv G s = logDeriv Q s := by
    rw [logDeriv_apply, eq_div_iff hQs_ne, ← hexpGs, mul_comm]
    exact heq_deriv

  have hlogDerivQ : logDeriv Q s = -(γ:ℂ) - ψ s := by
    have hexp_diff : DifferentiableAt ℂ (fun z => Complex.exp (-(γ:ℂ)*(z-1))) s :=
      (Complex.differentiable_exp.comp
        (differentiable_id.sub_const 1 |>.const_mul _)).differentiableAt
    have hΓ_diff : DifferentiableAt ℂ Complex.Gamma s :=
      Complex.differentiableAt_Gamma s (fun m h => by
        rw [h] at hs; simp only [Complex.neg_re, Complex.natCast_re] at hs
        linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
    have hexp_ne : (fun z => Complex.exp (-(γ:ℂ)*(z-1))) s ≠ 0 := Complex.exp_ne_zero _
    rw [show Q = fun z => Complex.exp (-(γ:ℂ)*(z-1)) / Complex.Gamma z from rfl,
      logDeriv_div s hexp_ne hΓne hexp_diff hΓ_diff]
    congr 1
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun z => Complex.exp (-(γ:ℂ)*(z-1)))
        (Complex.exp (-(γ:ℂ)*(s-1)) * (-(γ:ℂ))) s := by
      have := (Complex.hasDerivAt_exp (-(γ:ℂ)*(s-1))).comp s
        (((hasDerivAt_id s).sub_const 1).const_mul (-(γ:ℂ)))
      simp at this ⊢
      exact this
    rw [hd.deriv]
    field_simp

  have hfinal : HasSum (fun n : ℕ => 1/(s+(n:ℂ)) - 1/((n:ℂ)+1)) (-(γ:ℂ) - ψ s) := by
    rw [← hlogDerivQ, ← hG'_eq]
    exact hsd.congr_fun (fun n => (hderiv_eq n).symm)
  have hneg := hfinal.neg
  have hfeq : (fun n:ℕ => -(1/(s+(n:ℂ)) - 1/((n:ℂ)+1)))
      = (fun n:ℕ => 1/((n:ℂ)+1) - 1/((n:ℂ)+s)) := by
    ext n; ring
  have hteq : -(-(γ:ℂ) - ψ s) = ψ s + γ := by ring
  rw [hfeq, hteq] at hneg
  exact hneg

set_option maxHeartbeats 3200000 in

theorem gapsw80_t66_psi_one : ψ 1 = -(γ:ℂ) := by
  have _em := Classical.em
  have h := gapsw80_t66_hasSum_psi_series (s := 1) (by simp)
  have heq : (fun n:ℕ => 1/((n:ℂ)+1) - 1/((n:ℂ)+(1:ℂ))) = fun _ => (0:ℂ) :=
    funext fun n => sub_self _
  rw [heq] at h
  have h0 : (0:ℂ) = ψ 1 + γ := hasSum_zero.unique h
  have : ψ 1 = -(γ:ℂ) := by linear_combination -h0
  exact this

set_option maxHeartbeats 12800000 in

theorem gapsw80_t66_psi_half :
    ψ (1/2 : ℂ) = -(γ:ℂ) - 2 * Real.log 2 := by
  have _em := Classical.em
  have hnonz : ∀ s : ℂ, 0 < s.re → Complex.Gamma s ≠ 0 := fun s hs =>
    Complex.Gamma_ne_zero fun m h => by
      rw [h] at hs; simp only [Complex.neg_re, Complex.natCast_re] at hs
      linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hdiff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Complex.Gamma s := fun s hs =>
    Complex.differentiableAt_Gamma s fun m h => by
      rw [h] at hs; simp only [Complex.neg_re, Complex.natCast_re] at hs
      linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]

  set fL : ℂ → ℂ := fun s => Complex.Gamma s * Complex.Gamma (s + 1/2)
  set fR : ℂ → ℂ := fun s => Complex.Gamma (2*s) * (2:ℂ)^(1 - 2*s) * (↑(√π) : ℂ)
  have hfeq : fL = fR := funext Complex.Gamma_mul_Gamma_add_half
  have h12re : (0:ℝ) < ((1:ℂ)/2).re := by norm_num
  have h1re : (0:ℝ) < ((1:ℂ)).re := by norm_num
  have hΓ12 := hnonz _ h12re
  have hΓ1 := hnonz _ h1re
  have hd12 := hdiff _ h12re
  have hd1 := hdiff _ h1re
  have hadd : ((1:ℂ)/2 + 1/2) = 1 := by norm_num
  have h2mul : (2:ℂ) * (1/2) = 1 := by norm_num
  have hΓadd : Complex.Gamma ((1:ℂ)/2 + 1/2) ≠ 0 := by rw [hadd]; exact hΓ1
  have hΓ2mul : Complex.Gamma ((2:ℂ)*(1/2)) ≠ 0 := by rw [h2mul]; exact hΓ1
  have hdadd : DifferentiableAt ℂ Complex.Gamma ((1:ℂ)/2 + 1/2) := by rw [hadd]; exact hd1
  have hd2mul : DifferentiableAt ℂ Complex.Gamma ((2:ℂ)*(1/2)) := by rw [h2mul]; exact hd1
  have hgcomp : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s + 1/2)) (1/2) :=
    DifferentiableAt.comp (f := fun s : ℂ => s + 1/2) (1/2:ℂ) hdadd
      ((differentiableAt_id).add_const _)
  have hg2comp : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (2*s)) (1/2) :=
    DifferentiableAt.comp (f := fun s : ℂ => 2*s) (1/2:ℂ) hd2mul
      ((differentiableAt_id).const_mul 2)
  have h2ne : (2:ℂ) ≠ 0 := two_ne_zero
  have hcpow_diff : DifferentiableAt ℂ (fun s : ℂ => (2:ℂ)^(1 - 2*s)) (1/2) :=
    (((differentiableAt_id).const_mul 2).const_sub 1).const_cpow (Or.inl h2ne)
  have hcpow_ne : ((2:ℂ)^(1 - 2*(1/2:ℂ))) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl h2ne)
  have hsqrtπ : ((√π : ℝ):ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr Real.pi_pos

  have hLHS : logDeriv fL (1/2:ℂ) = ψ (1/2:ℂ) + ψ 1 := by
    rw [show fL = fun s => Complex.Gamma s * Complex.Gamma (s + 1/2) from rfl,
      logDeriv_mul (1/2:ℂ) hΓ12 hΓadd hd12 hgcomp]
    congr 1
    rw [show (fun s : ℂ => Complex.Gamma (s + 1/2)) = Complex.Gamma ∘ (· + 1/2) from rfl,
      logDeriv_comp (g := fun s : ℂ => s + 1/2) hdadd
        ((differentiableAt_id).add_const _),
      deriv_add_const, deriv_id'', mul_one, hadd]

  have hRHS : logDeriv fR (1/2:ℂ) = 2 * ψ 1 - 2 * (Real.log 2 : ℂ) := by
    rw [show fR = fun s => (Complex.Gamma (2*s) * (2:ℂ)^(1-2*s)) * (↑(√π):ℂ) from rfl,
      logDeriv_mul_const (1/2:ℂ) _ hsqrtπ,
      logDeriv_mul (1/2:ℂ) hΓ2mul hcpow_ne hg2comp hcpow_diff]
    have hlog1 : logDeriv (fun s : ℂ => Complex.Gamma (2*s)) (1/2:ℂ) = 2 * ψ 1 := by
      rw [show (fun s : ℂ => Complex.Gamma (2*s)) = Complex.Gamma ∘ (2 * ·) from rfl,
        logDeriv_comp (g := fun s : ℂ => 2*s) hd2mul
          ((differentiableAt_id).const_mul 2),
        deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one, h2mul, mul_comm]
    have hlog2 : logDeriv (fun s : ℂ => (2:ℂ)^(1 - 2*s)) (1/2:ℂ)
        = -2 * (Real.log 2 : ℂ) := by
      have hd : HasDerivAt (fun s : ℂ => (2:ℂ)^(1-2*s))
          ((2:ℂ)^(1-2*(1/2:ℂ)) * Complex.log 2 * (-2)) (1/2:ℂ) := by
        have h1 := (hasStrictDerivAt_const_cpow (x := (2:ℂ)) (y := 1-2*(1/2:ℂ))
          (Or.inl h2ne)).hasDerivAt
        have h2 : HasDerivAt (fun s : ℂ => 1 - 2*s) (-2) (1/2:ℂ) := by
          have := (((hasDerivAt_id (1/2:ℂ)).const_mul 2).const_sub 1)
          simpa using this
        exact HasDerivAt.comp (h := fun s : ℂ => 1 - 2*s) (1/2:ℂ) h1 h2
      rw [logDeriv_apply, hd.deriv]
      have hval : (2:ℂ)^(1-2*(1/2:ℂ)) = 1 := by norm_num
      rw [hval]
      have hlog2eq : Complex.log (2:ℂ) = ((Real.log 2 : ℝ):ℂ) := by
        rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,
          ← Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
      rw [hlog2eq]; ring
    rw [hlog1, hlog2]; ring
  have heq : ψ (1/2) + ψ 1 = 2 * ψ 1 - 2 * (Real.log 2 : ℂ) := by
    rw [← hLHS, hfeq, hRHS]
  have hψ1 := gapsw80_t66_psi_one
  linear_combination heq + hψ1

set_option maxHeartbeats 12800000 in

theorem gapsw80_t66_D2cai_proved : gapsw80_t65_DigammaReSeriesHalfLine := by
  have _em := Classical.em
  intro t
  have hhalf : (0:ℝ) < ((1:ℂ)/2).re := by norm_num
  have hht : (0:ℝ) < ((1:ℂ)/2 + (t:ℂ)*I).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.div_ofNat_re]
    norm_num
  have h1 := gapsw80_t66_hasSum_psi_series hht
  have h2 := gapsw80_t66_hasSum_psi_series hhalf
  have hdiff := h1.sub h2
  have hsimp : (fun n:ℕ => (1/((n:ℂ)+1) - 1/((n:ℂ)+(1/2+↑t*I)))
      - (1/((n:ℂ)+1) - 1/((n:ℂ)+1/2)))
    = fun n:ℕ => 1/((n:ℂ)+1/2) - 1/((n:ℂ)+1/2+↑t*I) := by
    ext n; ring
  rw [hsimp] at hdiff
  have hre := Complex.hasSum_re hdiff

  have htgt : (ψ (1/2 + ↑t*I) + ↑γ - (ψ (1/2:ℂ) + ↑γ)).re
      = (ψ (1/2 + (t:ℂ)*I)).re + γ + 2 * Real.log 2 := by
    rw [show ψ (1/2 + ↑t*I) + ↑γ - (ψ (1/2:ℂ) + ↑γ) = ψ (1/2 + ↑t*I) - ψ (1/2:ℂ) by ring,
      Complex.sub_re, gapsw80_t66_psi_half,
      show (-(γ:ℂ) - 2*↑(Real.log 2)).re = -γ - 2*Real.log 2 by
        simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.re_ofNat]]
    ring
  rw [htgt] at hre

  have hsummand : ∀ n : ℕ, (1/((n:ℂ)+1/2) - 1/((n:ℂ)+1/2+↑t*I)).re
      = 1/((n:ℝ)+1/2) - ((n:ℝ)+1/2)/(((n:ℝ)+1/2)^2+t^2) := fun n => by
    have hnc : ((n:ℂ)+1/2) = (((n:ℝ)+1/2 : ℝ) : ℂ) := by push_cast; ring
    rw [Complex.sub_re, one_div ((n:ℂ)+1/2), one_div ((n:ℂ)+1/2+_),
      Complex.inv_re, Complex.inv_re, Complex.normSq_apply, Complex.normSq_apply]
    have hre1 : ((n:ℂ)+1/2).re = (n:ℝ)+1/2 := by
      rw [hnc, Complex.ofReal_re]
    have him1 : ((n:ℂ)+1/2).im = 0 := by
      rw [hnc, Complex.ofReal_im]
    have hre2 : ((n:ℂ)+1/2+↑t*I).re = (n:ℝ)+1/2 := by
      rw [Complex.add_re, hre1, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im]
      ring
    have him2 : ((n:ℂ)+1/2+↑t*I).im = t := by
      rw [Complex.add_im, him1, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re]
      ring
    rw [hre1, him1, hre2, him2]
    have hn12 : (0:ℝ) < (n:ℝ)+1/2 := by positivity
    field_simp
    ring
  exact (hre.congr_fun fun n => (hsummand n).symm)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t66_D2ca_proved : gapsw80_t60_DigammaReCriticalLineCosKernel :=
  gapsw80_t65_D2ca_of_D2cai gapsw80_t66_D2cai_proved

end FLT.Gapsw80T66D2caiDigammaSeriesProof
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T19B2ppHadamardDecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module"

def gapsw80_t19_HadamardExpansionAt (K : Type) [Field K] [NumberField K] :
    Prop :=
  ∃ (B : ℂ) (ρ : ℕ → ℂ),
    (∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) ∧
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
      logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
        = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t19_sat_logDeriv_polyFactor {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    logDeriv (fun z => z * (z - 1)) s = s⁻¹ + (s - 1)⁻¹ := by
  have _em := Classical.em
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [logDeriv_apply]
  have hd : deriv (fun z : ℂ => z * (z - 1)) s = (s - 1) + s := by
    have h1 : HasDerivAt (fun z : ℂ => z) 1 s := hasDerivAt_id s
    have h2 : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have hmul := h1.mul h2
    simpa using hmul.deriv
  rw [hd]
  field_simp

end FLT.Gapsw80T19B2ppHadamardDecomp
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T20LambdaLogDerivProductRule

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T19B2ppHadamardDecomp
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"

variable (K : Type) [Field K] [NumberField K]

theorem gapsw80_t20_discrBase_ne_zero :
    (((|discr K| : ℤ) : ℂ)) ≠ 0 := by
  have _em := Classical.em
  exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_logDeriv_discrPow (s : ℂ) :
    logDeriv (fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2)) s
      = Complex.log (((|discr K| : ℤ) : ℂ)) / 2 := by
  have _em := Classical.em
  have hD := gapsw80_t20_discrBase_ne_zero K
  have hne : (((|discr K| : ℤ) : ℂ)) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hD]; exact Complex.exp_ne_zero _
  have hhd : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  rw [logDeriv_apply, Complex.deriv_const_cpow hhd.differentiableAt, hhd.deriv]
  field_simp

theorem gapsw80_t20_two_pi_ne_zero : (2 * (Real.pi : ℝ) : ℂ) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_Gammaℂ_ne_zero {s : ℂ} (hs : 1 < s.re) :
    Gammaℂ s ≠ 0 := by
  have _em := Classical.em
  have hnot : ∀ m : ℕ, s ≠ -m := fun m h => by
    have hm : (0:ℝ) ≤ (m:ℝ) := m.cast_nonneg
    rw [h, Complex.neg_re, Complex.natCast_re] at hs; linarith
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero hnot)
  rw [Complex.cpow_def_of_ne_zero gapsw80_t20_two_pi_ne_zero]
  exact Complex.exp_ne_zero _

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_differentiableAt_Gammaℂ {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ Gammaℂ s := by
  have _em := Classical.em
  have hnot : ∀ m : ℕ, s ≠ -m := fun m h => by
    have hm : (0:ℝ) ≤ (m:ℝ) := m.cast_nonneg
    rw [h, Complex.neg_re, Complex.natCast_re] at hs; linarith
  unfold Gammaℂ
  exact ((differentiableAt_const 2).mul
    ((differentiableAt_neg_iff.mpr (hasDerivAt_id s).differentiableAt).const_cpow
      (Or.inl gapsw80_t20_two_pi_ne_zero))).mul
    (Complex.differentiableAt_Gamma s hnot)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_differentiableAt_Gammaℝ {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have _em := Classical.em
  have hnot : ∀ m : ℕ, s / 2 ≠ -m := fun m h => by
    have hm : (0:ℝ) ≤ (m:ℝ) := m.cast_nonneg
    have hre : (s / 2).re = s.re / 2 := Complex.div_ofNat_re s 2
    rw [h, Complex.neg_re, Complex.natCast_re] at hre; linarith
  unfold Gammaℝ
  refine DifferentiableAt.mul ?_ ((Complex.differentiableAt_Gamma (s/2) hnot).comp s
    ((hasDerivAt_id s).div_const 2).differentiableAt)
  exact ((hasDerivAt_id s).neg.div_const 2).differentiableAt.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_eventuallyEq_T1 {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t9_completedDedekindZeta K) =ᶠ[nhds s]
      (gapsw80_t1_completedDedekindZeta K) := by
  have _em := Classical.em
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨{z : ℂ | 1 < z.re}, hopen.mem_nhds hs,
      fun z hz => gapsw80_t10_completedDedekindZeta_eq_T1 K hz⟩

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_abscissa_le_one :
    LSeries.abscissaOfAbsConv
        (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ))
      ≤ 1 := by
  have _em := Classical.em
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (fun y hy => gapsw80_t10_LSeriesSummable_dedekindZeta K (by simpa using hy))

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_differentiableAt_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (dedekindZeta K) s := by
  have _em := Classical.em
  have habs : LSeries.abscissaOfAbsConv
      (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) < s.re :=
    lt_of_le_of_lt (gapsw80_t20_abscissa_le_one K) (by exact_mod_cast hs)
  exact (LSeries_hasDerivAt habs).differentiableAt

set_option maxHeartbeats 3200000 in

theorem gapsw80_t20_completedZeta_ne_zero {s : ℂ} (hs : 1 < s.re)
    (hζ : dedekindZeta K s ≠ 0) :
    gapsw80_t9_completedDedekindZeta K s ≠ 0 := by
  have _em := Classical.em
  rw [(gapsw80_t20_eventuallyEq_T1 K hs).eq_of_nhds, gapsw80_t1_completedDedekindZeta]
  have hD := gapsw80_t20_discrBase_ne_zero K
  have hDne : (((|discr K| : ℤ) : ℂ)) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hD]; exact Complex.exp_ne_zero _
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hDne
    (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos (by linarith))))
    (pow_ne_zero _ (gapsw80_t20_Gammaℂ_ne_zero hs))) hζ

set_option maxHeartbeats 6400000 in

theorem gapsw80_t20_logDeriv_completedZeta_product {s : ℂ} (hs : 1 < s.re)
    (hζ : dedekindZeta K s ≠ 0) :
    logDeriv (gapsw80_t9_completedDedekindZeta K) s
      = Complex.log (((|discr K| : ℤ) : ℂ)) / 2
        + (nrRealPlaces K : ℂ) * logDeriv Gammaℝ s
        + (nrComplexPlaces K : ℂ) * logDeriv Gammaℂ s
        + logDeriv (dedekindZeta K) s := by
  have _em := Classical.em

  have hEE := gapsw80_t20_eventuallyEq_T1 K hs
  have hLD : logDeriv (gapsw80_t9_completedDedekindZeta K) s
      = logDeriv (gapsw80_t1_completedDedekindZeta K) s := by
    rw [logDeriv_apply, logDeriv_apply, hEE.deriv_eq, hEE.eq_of_nhds]
  rw [hLD]

  have hD := gapsw80_t20_discrBase_ne_zero K
  have hDne : (((|discr K| : ℤ) : ℂ)) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hD]; exact Complex.exp_ne_zero _
  have hDdiff : DifferentiableAt ℂ (fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2)) s :=
    ((hasDerivAt_id s).div_const 2).differentiableAt.const_cpow (Or.inl hD)
  have hRne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hRdiff : DifferentiableAt ℂ Gammaℝ s := gapsw80_t20_differentiableAt_Gammaℝ hs
  have hCne : Gammaℂ s ≠ 0 := gapsw80_t20_Gammaℂ_ne_zero hs
  have hCdiff : DifferentiableAt ℂ Gammaℂ s := gapsw80_t20_differentiableAt_Gammaℂ hs
  have hZdiff : DifferentiableAt ℂ (dedekindZeta K) s :=
    gapsw80_t20_differentiableAt_dedekindZeta K hs

  have step1 : logDeriv (fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2)
        * Gammaℝ z ^ nrRealPlaces K) s
      = Complex.log (((|discr K| : ℤ) : ℂ)) / 2
        + (nrRealPlaces K : ℂ) * logDeriv Gammaℝ s := by
    rw [logDeriv_mul (f := fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2))
          (g := fun z => Gammaℝ z ^ nrRealPlaces K) s
          hDne (pow_ne_zero _ hRne) hDdiff (hRdiff.pow _),
        gapsw80_t20_logDeriv_discrPow, logDeriv_fun_pow hRdiff]
  have step2 : logDeriv (fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2)
        * Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K) s
      = Complex.log (((|discr K| : ℤ) : ℂ)) / 2
        + (nrRealPlaces K : ℂ) * logDeriv Gammaℝ s
        + (nrComplexPlaces K : ℂ) * logDeriv Gammaℂ s := by
    rw [logDeriv_mul (f := fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2)
            * Gammaℝ z ^ nrRealPlaces K)
          (g := fun z => Gammaℂ z ^ nrComplexPlaces K) s
          (mul_ne_zero hDne (pow_ne_zero _ hRne)) (pow_ne_zero _ hCne)
          (hDdiff.mul (hRdiff.pow _)) (hCdiff.pow _),
        step1, logDeriv_fun_pow hCdiff]
  rw [show logDeriv (gapsw80_t1_completedDedekindZeta K) s
      = logDeriv (fun z => ((((|discr K| : ℤ) : ℂ)) ^ (z / 2)
          * Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K)
          * dedekindZeta K z) s from rfl,
    logDeriv_mul
      (f := fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2)
          * Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K)
      (g := fun z => dedekindZeta K z) s
      (mul_ne_zero (mul_ne_zero hDne (pow_ne_zero _ hRne))
        (pow_ne_zero _ hCne)) hζ
      ((hDdiff.mul (hRdiff.pow _)).mul (hCdiff.pow _)) hZdiff,
    step2]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t20_logDeriv_polyLambda_product {s : ℂ} (hs : 1 < s.re)
    (hζ : dedekindZeta K s ≠ 0) :
    logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
      = s⁻¹ + (s - 1)⁻¹ + Complex.log (((|discr K| : ℤ) : ℂ)) / 2
        + (nrRealPlaces K : ℂ) * logDeriv Gammaℝ s
        + (nrComplexPlaces K : ℂ) * logDeriv Gammaℂ s
        + logDeriv (dedekindZeta K) s := by
  have _em := Classical.em
  have hs0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs; exact absurd hs (by norm_num)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΛ : gapsw80_t9_completedDedekindZeta K s ≠ 0 :=
    gapsw80_t20_completedZeta_ne_zero K hs hζ
  have hΛdiff : DifferentiableAt ℂ (gapsw80_t9_completedDedekindZeta K) s := by
    refine (gapsw80_t9_differentiableOn_completedDedekindZeta K).differentiableAt ?_
    exact (gapsw80_t9_isClosed_pair).isOpen_compl.mem_nhds
      (by simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or]; exact ⟨hs0, hs1⟩)
  have hPdiff : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s :=
    (hasDerivAt_id s).differentiableAt.mul
      ((hasDerivAt_id s).sub_const 1).differentiableAt
  rw [show (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z)
        = (fun z => (fun w => w * (w - 1)) z
            * (gapsw80_t9_completedDedekindZeta K) z) from rfl,
    logDeriv_mul s (show s * (s - 1) ≠ 0 from mul_ne_zero hs0 hs1') hΛ hPdiff hΛdiff,
    gapsw80_t19_sat_logDeriv_polyFactor hs0 hs1,
    gapsw80_t20_logDeriv_completedZeta_product K hs hζ]
  ring

end FLT.Gapsw80T20LambdaLogDerivProductRule
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T21D2SubDecompWire

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T20LambdaLogDerivProductRule
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"

noncomputable def gapsw80_t21_zeroKernelTransform (F : ℝ → ℝ) (ρ : ℂ) : ℝ :=
  ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t21_zeroKernelTransform_pin (F : ℝ → ℝ) (ρ : ℂ) :
    gapsw80_t21_zeroKernelTransform F ρ =
      ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x) := by
  have _em := Classical.em
  rfl

noncomputable def gapsw80_t21_zeroKernelSum (F : ℝ → ℝ) (ρ : ℕ → ℂ) : ℝ :=
  ∑' j, gapsw80_t21_zeroKernelTransform F (ρ j)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t21_zeroKernelSum_pin (F : ℝ → ℝ) (ρ : ℕ → ℂ) :
    gapsw80_t21_zeroKernelSum F ρ =
      ∑' j, gapsw80_t21_zeroKernelTransform F (ρ j) := by
  have _em := Classical.em
  rfl

def gapsw80_t21_DedekindZetaEulerExpansion : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ s : ℂ, 1 < s.re →
    dedekindZeta K s ≠ 0 ∧
    -logDeriv (dedekindZeta K) s =
      ∑' (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) (m : ℕ),
        Complex.log ((Ideal.absNorm p.1 : ℕ) : ℂ)
          * ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-((m : ℂ) + 1) * s)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t21_sat_logDeriv_polyLambda_totallyComplex
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    {s : ℂ} (hs : 1 < s.re) (hζ : dedekindZeta K s ≠ 0) :
    logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
      = s⁻¹ + (s - 1)⁻¹ + Complex.log (((|discr K| : ℤ) : ℂ)) / 2
        + (nrComplexPlaces K : ℂ) * logDeriv Gammaℂ s
        + logDeriv (dedekindZeta K) s := by
  have _em := Classical.em
  have h := gapsw80_t20_logDeriv_polyLambda_product K hs hζ
  rw [IsTotallyComplex.nrRealPlaces_eq_zero (K := K)] at h
  simp only [Nat.cast_zero, zero_mul, add_zero] at h
  exact h

end FLT.Gapsw80T21D2SubDecompWire
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T23OdlyzkoKernelStripRemint

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T22AdmissibilityStripGapProbe
p2m_open "Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"

def gapsw80_t23_OdlyzkoAdmissibleKernelStrip (F : ℝ → ℝ) : Prop :=
  Differentiable ℝ F ∧ (∀ x : ℝ, F (-x) = F x) ∧ F 0 = 1 ∧ (∀ x : ℝ, 0 ≤ F x) ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → 0 ≤ gapsw80_t21_zeroKernelTransform F ρ

set_option maxHeartbeats 3200000 in

theorem gapsw80_t23_sat_zeroKernelTransform_on_line_eq (F : ℝ → ℝ) (t : ℝ) :
    gapsw80_t21_zeroKernelTransform F (1 / 2 + (t : ℂ) * I)
      = ∫ x : ℝ, F x * Real.cos (t * x) := by
  have _em := Classical.em
  have hre : (1 / 2 + (t : ℂ) * I).re - 1 / 2 = 0 := by
    simp [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have him : (1 / 2 + (t : ℂ) * I).im = t := by
    simp [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [gapsw80_t21_zeroKernelTransform, hre, him]
  simp only [zero_mul, Real.exp_zero, mul_one]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t23_stripAdmissible_implies_lineAdmissible {F : ℝ → ℝ}
    (hF : gapsw80_t23_OdlyzkoAdmissibleKernelStrip F) :
    gapsw50_t2_OdlyzkoAdmissibleKernel F := by
  have _em := Classical.em
  obtain ⟨hdiff, heven, h0, hpos, hdecay, hstrip⟩ := hF
  refine ⟨hdiff, heven, h0, hpos, hdecay, ?_⟩
  intro t
  have hre : (0 : ℝ) < (1 / 2 + (t : ℂ) * I).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    norm_num
  have hre' : (1 / 2 + (t : ℂ) * I).re < 1 := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    norm_num
  have h := hstrip (1 / 2 + (t : ℂ) * I) hre hre'
  rwa [gapsw80_t23_sat_zeroKernelTransform_on_line_eq] at h

end FLT.Gapsw80T23OdlyzkoKernelStripRemint
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T26D2dTwoConjunctDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T20LambdaLogDerivProductRule
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T24StripMigrationChainStart
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"

def gapsw80_t26_DedekindZetaNeZeroReGtOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ s : ℂ, 1 < s.re →
    dedekindZeta K s ≠ 0

def gapsw80_t26_DedekindZetaLogDerivVonMangoldt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ s : ℂ, 1 < s.re →
    dedekindZeta K s ≠ 0 →
    -logDeriv (dedekindZeta K) s =
      ∑' (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) (m : ℕ),
        Complex.log ((Ideal.absNorm p.1 : ℕ) : ℂ)
          * ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-((m : ℂ) + 1) * s)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t26_D2d_of_D2d1_D2d2
    (hd1 : gapsw80_t26_DedekindZetaNeZeroReGtOne)
    (hd2 : gapsw80_t26_DedekindZetaLogDerivVonMangoldt) :
    gapsw80_t21_DedekindZetaEulerExpansion := by
  have _em := Classical.em
  intro K _ _ s hs
  exact ⟨hd1 K s hs, hd2 K s hs (hd1 K s hs)⟩

end FLT.Gapsw80T26D2dTwoConjunctDecomp
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T24StripMigrationChainStart

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t24_zeroKernelSum_nonneg_of_stripAdmissible
    {F : ℝ → ℝ} (hF : gapsw80_t23_OdlyzkoAdmissibleKernelStrip F)
    {ρ : ℕ → ℂ} (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) :
    0 ≤ gapsw80_t21_zeroKernelSum F ρ := by
  have _em := Classical.em
  rw [gapsw80_t21_zeroKernelSum_pin]
  exact tsum_nonneg (fun j => hF.2.2.2.2.2 (ρ j) (hstrip j).1 (hstrip j).2)

end FLT.Gapsw80T24StripMigrationChainStart
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T27D2d0EulerProductAncestor

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T20LambdaLogDerivProductRule
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T26D2dTwoConjunctDecomp
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex Filter P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Filter Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology"

theorem gapsw80_t27_one_lt_absNorm_prime {K : Type} [Field K] [NumberField K]
    (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    1 < Ideal.absNorm p.1 := by
  have _em := Classical.em
  by_contra! h
  have hfin : Finite (𝓞 K ⧸ p.1) := p.1.finiteQuotientOfFreeOfNeBot p.2.2
  have hpos : 0 < Ideal.absNorm p.1 :=
    Nat.pos_iff_ne_zero.mpr ((Ideal.absNorm_ne_zero_iff p.1).mpr hfin)
  have h1 : Ideal.absNorm p.1 = 1 := Nat.le_antisymm h hpos
  exact p.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h1)

theorem gapsw80_t27_norm_natCast_cpow_lt_one {N : ℕ} (hN : 2 ≤ N) {s : ℂ}
    (hs : 1 < s.re) : ‖(N : ℂ) ^ (-s)‖ < 1 := by
  have _em := Classical.em
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)

theorem gapsw80_t27_norm_absNorm_cpow_lt_one {K : Type} [Field K]
    [NumberField K] (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) {s : ℂ}
    (hs : 1 < s.re) :
    ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)‖ < 1 :=
  gapsw80_t27_norm_natCast_cpow_lt_one (gapsw80_t27_one_lt_absNorm_prime p) hs

theorem gapsw80_t27_hasDerivAt_neg_log_one_sub_cpow {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun w => -Complex.log (1 - (N : ℂ) ^ (-w)))
      (-(Complex.log (N : ℂ) * (N : ℂ) ^ (-s) / (1 - (N : ℂ) ^ (-s)))) s := by
  have _em := Classical.em
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlt : ‖(N : ℂ) ^ (-s)‖ < 1 := gapsw80_t27_norm_natCast_cpow_lt_one hN hs

  have h1 : HasDerivAt (fun w => (N : ℂ) ^ (-w))
      ((N : ℂ) ^ (-s) * Complex.log (N : ℂ) * (-1)) s :=
    (hasDerivAt_neg' s).const_cpow (Or.inl hN0)

  have h2 : HasDerivAt (fun w => 1 - (N : ℂ) ^ (-w))
      (Complex.log (N : ℂ) * (N : ℂ) ^ (-s)) s := by
    have := h1.const_sub 1; simpa [mul_comm] using this

  have hslit : 1 - (N : ℂ) ^ (-s) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : (((N : ℂ) ^ (-s)).re) ≤ ‖(N : ℂ) ^ (-s)‖ := Complex.re_le_norm _
    simp only [Complex.sub_re, Complex.one_re]; linarith
  exact (h2.clog hslit).neg

set_option maxHeartbeats 3200000 in

theorem gapsw80_t27_sat_geom_cpow_series {N : ℕ} (hN : 2 ≤ N) {s : ℂ}
    (hs : 1 < s.re) :
    ∑' m : ℕ, (N : ℂ) ^ (-((m : ℂ) + 1) * s)
      = (N : ℂ) ^ (-s) / (1 - (N : ℂ) ^ (-s)) := by
  have _em := Classical.em
  have hlt : ‖(N : ℂ) ^ (-s)‖ < 1 := gapsw80_t27_norm_natCast_cpow_lt_one hN hs
  have key : ∀ m : ℕ, (N : ℂ) ^ (-((m : ℂ) + 1) * s) = ((N : ℂ) ^ (-s)) ^ (m + 1) := by
    intro m
    rw [show (-((m : ℂ) + 1) * s) = ((m + 1 : ℕ) : ℂ) * (-s) by push_cast; ring,
      Complex.cpow_nat_mul]
  simp_rw [key, pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hlt, div_eq_mul_inv]

def gapsw80_t27_DedekindZetaEulerProductExpForm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ s : ℂ, 1 < s.re →
    Summable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)‖) ∧
    dedekindZeta K s = Complex.exp
      (∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥},
        -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)))

set_option maxHeartbeats 3200000 in

theorem gapsw80_t27_D2d1_of_D2d0
    (hd0 : gapsw80_t27_DedekindZetaEulerProductExpForm) :
    gapsw80_t26_DedekindZetaNeZeroReGtOne := by
  have _em := Classical.em
  intro K _ _ s hs
  rw [(hd0 K s hs).2]
  exact Complex.exp_ne_zero _

set_option maxHeartbeats 12800000 in

theorem gapsw80_t27_D2d2_of_D2d0
    (hd0 : gapsw80_t27_DedekindZetaEulerProductExpForm) :
    gapsw80_t26_DedekindZetaLogDerivVonMangoldt := by
  have _em := Classical.em
  intro K _ _ s hs _hζ

  set σ₀ : ℝ := (1 + s.re) / 2 with hσ₀_def
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀_def]; linarith
  have hσ₀s : σ₀ < s.re := by rw [hσ₀_def]; linarith
  set U : Set ℂ := {w | σ₀ < w.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hσ₀s
  let F : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} → ℂ → ℂ :=
    fun p w => -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-w))
  let g : ℂ → ℂ := fun w => ∑' p, F p w

  have hEE : dedekindZeta K =ᶠ[𝓝 s] (fun w => Complex.exp (g w)) := by
    filter_upwards [hUopen.mem_nhds hsU] with w hw
    exact (hd0 K w (hσ₀1.trans hw)).2

  have hσ₀C : 1 < (σ₀ : ℂ).re := by simp; exact hσ₀1
  let u : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} → ℝ :=
    fun p => (3 / 2) * ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-(σ₀ : ℂ))‖
  have hu : Summable u := ((hd0 K (σ₀ : ℂ) hσ₀C).1).mul_left (3 / 2)

  have hFdiff : ∀ p, DifferentiableOn ℂ (F p) U := fun p w hw =>
    (gapsw80_t27_hasDerivAt_neg_log_one_sub_cpow
      (gapsw80_t27_one_lt_absNorm_prime p)
      (hσ₀1.trans hw)).differentiableAt.differentiableWithinAt
  have hFbound : ∀ p w, w ∈ U → ‖F p w‖ ≤ u p := by
    intro p w hw
    have hNp := gapsw80_t27_one_lt_absNorm_prime p
    have hN0 : 0 < Ideal.absNorm p.1 := lt_trans one_pos hNp
    have hw' : σ₀ < w.re := hw
    have hmono : ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-w)‖
        ≤ ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-(σ₀ : ℂ))‖ := by
      refine Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hN0 ?_
      simp only [Complex.neg_re, Complex.ofReal_re]; linarith
    have hhalf : ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-(σ₀ : ℂ))‖ ≤ 1 / 2 := by
      rw [Complex.norm_natCast_cpow_of_pos hN0, Complex.neg_re, Complex.ofReal_re]
      have h2σ : (2 : ℝ) ^ σ₀ ≤ (Ideal.absNorm p.1 : ℝ) ^ σ₀ :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hNp) (by linarith)
      have h2σ1 : (2 : ℝ) ≤ (2 : ℝ) ^ σ₀ := by
        calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ 2 ^ σ₀ := Real.rpow_le_rpow_of_exponent_le one_le_two hσ₀1.le
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
      rw [inv_le_comm₀ (Real.rpow_pos_of_pos (by exact_mod_cast hN0) σ₀) (by norm_num)]
      linarith
    have hhalf' : ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-w)‖ ≤ 1 / 2 := hmono.trans hhalf
    calc ‖F p w‖
        = ‖Complex.log (1 + -(((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-w)))‖ := by
          simp only [F, norm_neg, sub_eq_add_neg]
      _ ≤ 3 / 2 * ‖-(((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-w))‖ :=
          Complex.norm_log_one_add_half_le_self (by rwa [norm_neg])
      _ = 3 / 2 * ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-w)‖ := by rw [norm_neg]
      _ ≤ u p := by
          exact mul_le_mul_of_nonneg_left hmono (by norm_num)

  have hgdiff : DifferentiableOn ℂ g U :=
    Complex.differentiableOn_tsum_of_summable_norm hu hFdiff hUopen hFbound
  have hSD : HasSum (fun p => deriv (F p) s) (deriv g s) :=
    Complex.hasSum_deriv_of_summable_norm hu hFdiff hUopen hFbound hsU

  have hgds : DifferentiableAt ℂ g s :=
    (hgdiff s hsU).differentiableAt (hUopen.mem_nhds hsU)
  have hLD : logDeriv (dedekindZeta K) s = deriv g s := by
    rw [logDeriv_apply, hEE.deriv_eq, hEE.eq_of_nhds, deriv_cexp hgds,
      mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]

  have hderivF : ∀ p, deriv (F p) s
      = -(Complex.log ((Ideal.absNorm p.1 : ℕ) : ℂ)
          * ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)
          / (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))) := fun p =>
    (gapsw80_t27_hasDerivAt_neg_log_one_sub_cpow
      (gapsw80_t27_one_lt_absNorm_prime p) hs).deriv

  rw [hLD, ← hSD.neg.tsum_eq]
  refine tsum_congr fun p => ?_
  rw [hderivF p, neg_neg, mul_div_assoc,
    ← gapsw80_t27_sat_geom_cpow_series (gapsw80_t27_one_lt_absNorm_prime p) hs,
    ← tsum_mul_left]

end FLT.Gapsw80T27D2d0EulerProductAncestor
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T28D2d0aSummabilityProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T27D2d0EulerProductAncestor
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"
open scoped nonZeroDivisors

theorem gapsw80_t28_one_sub_absNorm_cpow_ne_zero {K : Type} [Field K]
    [NumberField K] (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) {s : ℂ}
    (hs : 1 < s.re) :
    1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  have _em := Classical.em
  have hlt := gapsw80_t27_norm_absNorm_cpow_lt_one p hs
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem gapsw80_t28_exp_neg_log_one_sub_absNorm_cpow {K : Type} [Field K]
    [NumberField K] (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) {s : ℂ}
    (hs : 1 < s.re) :
    Complex.exp (-Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)))
      = (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
  have _em := Classical.em
  rw [Complex.exp_neg,
    Complex.exp_log (gapsw80_t28_one_sub_absNorm_cpow_ne_zero p hs)]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t28_summable_norm_absNorm_cpow {K : Type} [Field K]
    [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)‖) := by
  have _em := Classical.em

  let e : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} → (Ideal (𝓞 K))⁰ :=
    fun p => ⟨p.1, Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mp
      (lt_trans Nat.one_pos (gapsw80_t27_one_lt_absNorm_prime p)).ne'⟩
  have he : Function.Injective e := fun p q h => Subtype.ext (by
    have h' : (e p).1 = (e q).1 := Subtype.ext_iff.mp h
    simpa only [e] using h')

  have hσ : 1 < ((s.re : ℂ)).re := by rw [Complex.ofReal_re]; exact hs
  have hT10 := gapsw80_t10_summable_idealNorm K (s := (s.re : ℂ)) hσ

  have hterm : ∀ J : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-(s.re : ℂ))
        = Complex.ofReal
            (((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ^ (-s.re)) := by
    intro J
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast,
      Complex.ofReal_neg]

  have hℝ : Summable (fun J : (Ideal (𝓞 K))⁰ =>
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ^ (-s.re)) :=
    Complex.summable_ofReal.mp (hT10.congr hterm)

  have hPr : Summable
      ((fun J : (Ideal (𝓞 K))⁰ =>
        ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ^ (-s.re)) ∘ e) :=
    hℝ.comp_injective he

  refine hPr.congr fun p => ?_
  show ((Ideal.absNorm p.1 : ℕ) : ℝ) ^ (-s.re) = ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)‖
  rw [Complex.norm_natCast_cpow_of_pos
    (lt_trans Nat.one_pos (gapsw80_t27_one_lt_absNorm_prime p)), Complex.neg_re]

def gapsw80_t28_DedekindZetaEulerProductHasProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ s : ℂ, 1 < s.re →
    HasProd (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹) (dedekindZeta K s)

set_option maxHeartbeats 6400000 in

theorem gapsw80_t28_D2d0_of_D2d0b
    (hb : gapsw80_t28_DedekindZetaEulerProductHasProd) :
    gapsw80_t27_DedekindZetaEulerProductExpForm := by
  have _em := Classical.em
  intro K _ _ s hs
  refine ⟨gapsw80_t28_summable_norm_absNorm_cpow hs, ?_⟩

  have hsum : Summable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)) :=
    (gapsw80_t28_summable_norm_absNorm_cpow hs).of_norm
  have hfun : (Complex.exp ∘ fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
        -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)))
      = fun p => (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹ :=
    funext fun p => gapsw80_t28_exp_neg_log_one_sub_absNorm_cpow p hs
  exact HasProd.unique (hb K s hs) (hfun ▸ hsum.clog_one_sub.neg.hasSum.cexp)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t28_sat_multipliable_one_sub_inv {K : Type} [Field K]
    [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹) := by
  have _em := Classical.em
  have hsum : Summable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)) :=
    (gapsw80_t28_summable_norm_absNorm_cpow hs).of_norm
  have hfun : (Complex.exp ∘ fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
        -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)))
      = fun p => (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹ :=
    funext fun p => gapsw80_t28_exp_neg_log_one_sub_absNorm_cpow p hs
  exact (hfun ▸ hsum.clog_one_sub.neg.hasSum.cexp).multipliable

end FLT.Gapsw80T28D2d0aSummabilityProof
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T29D2d0bNatEulerProductBridge

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T27D2d0EulerProductAncestor
open FLT.Gapsw80T28D2d0aSummabilityProof
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"
open scoped nonZeroDivisors

theorem gapsw80_t29_card_absNorm_eq_one (K : Type) [Field K] [NumberField K] :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
  have _em := Classical.em
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun J => Subtype.ext
    (Ideal.absNorm_eq_one_iff.mp J.2)⟩

theorem gapsw80_t29_under_ne_bot {K : Type} [Field K] [NumberField K]
    (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    Ideal.under ℤ p.1 ≠ ⊥ := by
  have _em := Classical.em
  have hN : Ideal.absNorm p.1 ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (le_of_lt (gapsw80_t27_one_lt_absNorm_prime p))
  rw [Submodule.ne_bot_iff]
  refine ⟨(Ideal.absNorm p.1 : ℤ), ?_, by exact_mod_cast hN⟩
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact Ideal.absNorm_mem p.1

noncomputable def gapsw80_t29_primeBelow {K : Type} [Field K] [NumberField K]
    (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) : Nat.Primes :=
  ⟨(Submodule.IsPrincipal.generator (Ideal.under ℤ p.1)).natAbs, by
    have _em := Classical.em
    have hPr : (Ideal.under ℤ p.1).IsPrime :=
      @Ideal.IsPrime.under ℤ _ _ _ _ p.1 p.2.1
    have hnb := gapsw80_t29_under_ne_bot p
    rw [← Int.prime_iff_natAbs_prime]
    refine (Ideal.span_singleton_prime ?_).mp ?_
    · intro hg0
      exact hnb (by
        rw [← Ideal.span_singleton_generator (Ideal.under ℤ p.1), hg0,
          Ideal.span_singleton_zero])
    · rw [Ideal.span_singleton_generator]; exact hPr⟩

theorem gapsw80_t29_under_eq_span_primeBelow {K : Type} [Field K]
    [NumberField K] (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    Ideal.under ℤ p.1
      = Ideal.span {((gapsw80_t29_primeBelow p : ℕ) : ℤ)} := by
  have _em := Classical.em
  rw [show ((gapsw80_t29_primeBelow p : ℕ) : ℤ)
      = (Submodule.IsPrincipal.generator (Ideal.under ℤ p.1)).natAbs from rfl,
    Int.span_natAbs, Ideal.span_singleton_generator]

section IdealCountCoprime
variable (K : Type) [Field K] [NumberField K]

theorem gapsw80_t29_span_natCast_sup_eq_top {m n : ℕ} (hmn : Nat.Coprime m n) :
    Ideal.span {(m : 𝓞 K)} ⊔ Ideal.span {(n : 𝓞 K)} = ⊤ := by
  have _em := Classical.em
  have hZ : IsCoprime (m : ℤ) (n : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]; simpa using hmn
  have hO : IsCoprime (m : 𝓞 K) (n : 𝓞 K) := by
    have h := hZ.map (algebraMap ℤ (𝓞 K))
    rwa [map_natCast, map_natCast] at h
  exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hO).sup_eq

theorem gapsw80_t29_sup_mul_sup_eq_self {m n : ℕ} (hmn : Nat.Coprime m n)
    (I : Ideal (𝓞 K)) (hI : Ideal.absNorm I = m * n) :
    (I ⊔ Ideal.span {(m : 𝓞 K)}) * (I ⊔ Ideal.span {(n : 𝓞 K)}) = I := by
  have _em := Classical.em
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact Ideal.mul_le_left
    · exact Ideal.mul_le_left
    · exact Ideal.mul_le_right
    · rw [Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_le_iff_mem]
      have hmem : ((m * n : ℕ) : 𝓞 K) ∈ I := by
        rw [← hI]; exact Ideal.absNorm_mem I
      push_cast at hmem; exact hmem
  · have hsup : (I ⊔ Ideal.span {(m : 𝓞 K)}) ⊔ (I ⊔ Ideal.span {(n : 𝓞 K)})
        = ⊤ := by
      rw [eq_top_iff, ← gapsw80_t29_span_natCast_sup_eq_top K hmn]
      exact sup_le (le_sup_of_le_left le_sup_right)
        (le_sup_of_le_right le_sup_right)
    have hmul := Ideal.sup_mul_inf (I ⊔ Ideal.span {(m : 𝓞 K)})
      (I ⊔ Ideal.span {(n : 𝓞 K)})
    rw [hsup, Ideal.top_mul] at hmul
    rw [← hmul]; exact le_inf le_sup_left le_sup_left

theorem gapsw80_t29_absNorm_span_natCast (m : ℕ) :
    Ideal.absNorm (Ideal.span {(m : 𝓞 K)})
      = m ^ Module.finrank ℤ (𝓞 K) := by
  have _em := Classical.em
  have h := Algebra.norm_algebraMap_of_basis
    (Module.Free.chooseBasis ℤ (𝓞 K)) ((m : ℕ) : ℤ)
  rw [map_natCast, ← Module.finrank_eq_card_chooseBasisIndex] at h
  rw [Ideal.absNorm_span_singleton, h]; simp [Int.natAbs_pow]

theorem gapsw80_t29_absNorm_sup_span_dvd_pow (I : Ideal (𝓞 K)) (m : ℕ) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 K)})
      ∣ m ^ Module.finrank ℤ (𝓞 K) := by
  have _em := Classical.em
  rw [← gapsw80_t29_absNorm_span_natCast K m]
  exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right

theorem gapsw80_t29_eq_of_dvd_pow_mul_eq {m n a b d : ℕ}
    (hmn : Nat.Coprime m n) (ha : a ∣ m ^ d) (hb : b ∣ n ^ d)
    (hab : a * b = m * n) : a = m ∧ b = n := by
  have _em := Classical.em
  have han : Nat.Coprime a n :=
    Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.pow_left d hmn)
  have hbm : Nat.Coprime b m :=
    Nat.Coprime.coprime_dvd_left hb (Nat.Coprime.pow_left d hmn.symm)
  have ham : a ∣ m := han.dvd_of_dvd_mul_right (hab ▸ dvd_mul_right a b)
  have hma : m ∣ a := hbm.symm.dvd_of_dvd_mul_right (hab ▸ dvd_mul_right m n)
  have hbn : b ∣ n := hbm.dvd_of_dvd_mul_left (hab ▸ dvd_mul_left b a)
  have hnb : n ∣ b := han.symm.dvd_of_dvd_mul_left (hab ▸ dvd_mul_left n m)
  exact ⟨Nat.dvd_antisymm ham hma, Nat.dvd_antisymm hbn hnb⟩

theorem gapsw80_t29_absNorm_sup_pair {m n : ℕ} (hmn : Nat.Coprime m n)
    (I : Ideal (𝓞 K)) (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 K)}) = m
      ∧ Ideal.absNorm (I ⊔ Ideal.span {(n : 𝓞 K)}) = n := by
  have _em := Classical.em
  have hab : Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 K)})
      * Ideal.absNorm (I ⊔ Ideal.span {(n : 𝓞 K)}) = m * n := by
    rw [← map_mul, gapsw80_t29_sup_mul_sup_eq_self K hmn I hI, hI]
  exact gapsw80_t29_eq_of_dvd_pow_mul_eq hmn
    (gapsw80_t29_absNorm_sup_span_dvd_pow K I m)
    (gapsw80_t29_absNorm_sup_span_dvd_pow K I n) hab

theorem gapsw80_t29_mul_sup_span_left {m n : ℕ} (hmn : Nat.Coprime m n)
    (J K' : Ideal (𝓞 K)) (hJ : Ideal.absNorm J = m)
    (hK : Ideal.absNorm K' = n) :
    J * K' ⊔ Ideal.span {(m : 𝓞 K)} = J := by
  have _em := Classical.em
  have hspanJ : Ideal.span {(m : 𝓞 K)} ≤ J := by
    rw [Ideal.span_singleton_le_iff_mem, ← hJ]; exact Ideal.absNorm_mem J
  have hspanK : Ideal.span {(n : 𝓞 K)} ≤ K' := by
    rw [Ideal.span_singleton_le_iff_mem, ← hK]; exact Ideal.absNorm_mem K'
  apply le_antisymm
  · exact sup_le Ideal.mul_le_left hspanJ
  · have htop : K' ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ := by
      rw [eq_top_iff, ← gapsw80_t29_span_natCast_sup_eq_top K hmn.symm]
      exact sup_le (le_sup_of_le_left hspanK) le_sup_right
    calc J = J * (K' ⊔ Ideal.span {(m : 𝓞 K)}) := by rw [htop, Ideal.mul_top]
      _ ≤ J * K' ⊔ Ideal.span {(m : 𝓞 K)} := by
          rw [Ideal.mul_sup]
          exact sup_le le_sup_left (le_sup_of_le_right Ideal.mul_le_right)

theorem gapsw80_t29_mul_sup_span_right {m n : ℕ} (hmn : Nat.Coprime m n)
    (J K' : Ideal (𝓞 K)) (hJ : Ideal.absNorm J = m)
    (hK : Ideal.absNorm K' = n) :
    J * K' ⊔ Ideal.span {(n : 𝓞 K)} = K' := by
  have _em := Classical.em
  rw [mul_comm J K']
  exact gapsw80_t29_mul_sup_span_left K hmn.symm K' J hK hJ

noncomputable def gapsw80_t29_normFiberSplitEquiv {m n : ℕ}
    (hmn : Nat.Coprime m n) :
    {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n}
      ≃ {J : Ideal (𝓞 K) // Ideal.absNorm J = m}
        × {K' : Ideal (𝓞 K) // Ideal.absNorm K' = n} where
  toFun I :=
    ⟨⟨I.1 ⊔ Ideal.span {(m : 𝓞 K)},
        (gapsw80_t29_absNorm_sup_pair K hmn I.1 I.2).1⟩,
      ⟨I.1 ⊔ Ideal.span {(n : 𝓞 K)},
        (gapsw80_t29_absNorm_sup_pair K hmn I.1 I.2).2⟩⟩
  invFun JK := ⟨JK.1.1 * JK.2.1, by rw [map_mul, JK.1.2, JK.2.2]⟩
  left_inv I := by
    have _em := Classical.em
    exact Subtype.ext (gapsw80_t29_sup_mul_sup_eq_self K hmn I.1 I.2)
  right_inv JK := by
    have _em := Classical.em
    exact Prod.ext
      (Subtype.ext
        (gapsw80_t29_mul_sup_span_left K hmn JK.1.1 JK.2.1 JK.1.2 JK.2.2))
      (Subtype.ext
        (gapsw80_t29_mul_sup_span_right K hmn JK.1.1 JK.2.1 JK.1.2 JK.2.2))

theorem gapsw80_t29_idealCount_coprime_mul {m n : ℕ} (hmn : Nat.Coprime m n) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n}
      = Nat.card {J : Ideal (𝓞 K) // Ideal.absNorm J = m}
        * Nat.card {K' : Ideal (𝓞 K) // Ideal.absNorm K' = n} := by
  have _em := Classical.em
  rw [Nat.card_congr (gapsw80_t29_normFiberSplitEquiv K hmn), Nat.card_prod]

end IdealCountCoprime
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

theorem gapsw80_t29_term_coprime_mul (K : Type) [Field K] [NumberField K]
    (s : ℂ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        s (m * n)
      = LSeries.term
          (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
          s m
        * LSeries.term
            (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
            s n := by
  have _em := Classical.em
  rcases eq_or_ne m 0 with rfl | hm
  · simp [LSeries.term_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero (Nat.mul_ne_zero hm hn),
    LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
    gapsw80_t29_idealCount_coprime_mul K hmn, Nat.cast_mul, Nat.cast_mul,
    div_mul_div_comm]
  congr 1
  rw [← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

theorem gapsw80_t29_dedekindZeta_nat_eulerProduct (K : Type) [Field K]
    [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
        ∑' e : ℕ, LSeries.term
          (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
          s ((p : ℕ) ^ e))
      (dedekindZeta K s) := by
  have _em := Classical.em
  have hf1 : LSeries.term
      (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
      s 1 = 1 := by
    simp [LSeries.term_of_ne_zero one_ne_zero,
      gapsw80_t29_card_absNorm_eq_one K]
  have hf0 : LSeries.term
      (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
      s 0 = 0 := LSeries.term_zero _ _
  have hsum := (gapsw80_t10_LSeriesSummable_dedekindZeta K hs).norm
  have hEP := EulerProduct.eulerProduct_hasProd hf1
    (fun {m n} hmn => gapsw80_t29_term_coprime_mul K s hmn) hsum hf0

  rwa [show (∑' n, LSeries.term
      (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ)) s n)
      = dedekindZeta K s from rfl] at hEP

def gapsw80_t29_LocalEulerFactorPerNatPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ s : ℂ, 1 < s.re →
    ∀ p : Nat.Primes,
    HasProd
      (fun q : {q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} //
          gapsw80_t29_primeBelow q = p} =>
        (1 - ((Ideal.absNorm q.1.1 : ℕ) : ℂ) ^ (-s))⁻¹)
      (∑' e : ℕ, LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        s ((p : ℕ) ^ e))

set_option maxHeartbeats 12800000 in

theorem gapsw80_t29_D2d0b_of_D2d0c
    (hc : gapsw80_t29_LocalEulerFactorPerNatPrime) :
    gapsw80_t28_DedekindZetaEulerProductHasProd := by
  have _em := Classical.em
  intro K _ _ s hs
  set h : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} → ℂ :=
    fun p => (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹ with hh_def

  have hmult : Multipliable h :=
    gapsw80_t28_sat_multipliable_one_sub_inv (K := K) hs

  let e := Equiv.sigmaFiberEquiv (@gapsw80_t29_primeBelow K _ _)

  have hmult' : Multipliable (h ∘ e) :=
    (e.multipliable_iff).mpr hmult

  have hflat : HasProd (h ∘ e) (∏' q, (h ∘ e) q) := hmult'.hasProd

  have hg : HasProd
      (fun p : Nat.Primes => ∑' e' : ℕ, LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        s ((p : ℕ) ^ e'))
      (∏' q, (h ∘ e) q) :=
    hflat.sigma (fun p => hc K s hs p)

  have heq : (∏' q, (h ∘ e) q) = dedekindZeta K s :=
    HasProd.unique hg (gapsw80_t29_dedekindZeta_nat_eulerProduct K hs)

  have hfinal : HasProd h (dedekindZeta K s) :=
    (e.hasProd_iff).mp (heq ▸ hflat)
  exact hfinal

end FLT.Gapsw80T29D2d0bNatEulerProductBridge
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T30D2d0cLocalEulerFactorProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T27D2d0EulerProductAncestor
open FLT.Gapsw80T28D2d0aSummabilityProof
open FLT.Gapsw80T29D2d0bNatEulerProductBridge
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex UniqueFactorizationMonoid P2MW.S_NumberField_archTermDerived_le_log_abs_discr.UniqueFactorizationMonoid"
open scoped nonZeroDivisors

abbrev gapsw80_t30_Fiber (K : Type) [Field K] [NumberField K]
    (p : Nat.Primes) : Type :=
  {q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} //
    gapsw80_t29_primeBelow q = p}

theorem gapsw80_t30_primeBelow_dvd_absNorm {K : Type} [Field K]
    [NumberField K] (q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    (gapsw80_t29_primeBelow q : ℕ) ∣ Ideal.absNorm q.1 := by
  have _em := Classical.em
  have hmem : (Ideal.absNorm q.1 : ℤ) ∈ Ideal.under ℤ q.1 := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem q.1
  rw [gapsw80_t29_under_eq_span_primeBelow, Ideal.mem_span_singleton]
    at hmem
  exact Int.natCast_dvd_natCast.mp hmem

theorem gapsw80_t30_natCast_mem_fiber {K : Type} [Field K] [NumberField K]
    {p : Nat.Primes} (q : gapsw80_t30_Fiber K p) :
    ((p : ℕ) : 𝓞 K) ∈ q.1.1 := by
  have _em := Classical.em
  have hpb : ((gapsw80_t29_primeBelow q.1 : ℕ) : ℤ) = ((p : ℕ) : ℤ) := by
    exact_mod_cast congrArg Subtype.val q.2
  have hgen : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ q.1.1 := by
    rw [gapsw80_t29_under_eq_span_primeBelow q.1, hpb]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.under_def, Ideal.mem_comap] at hgen
  simpa using hgen

theorem gapsw80_t30_absNorm_fiber_dvd_pow {K : Type} [Field K]
    [NumberField K] {p : Nat.Primes} (q : gapsw80_t30_Fiber K p) :
    Ideal.absNorm q.1.1 ∣ (p : ℕ) ^ Module.finrank ℤ (𝓞 K) := by
  have _em := Classical.em
  have hle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ q.1.1 :=
    (Ideal.span_singleton_le_iff_mem _).mpr (gapsw80_t30_natCast_mem_fiber q)
  calc Ideal.absNorm q.1.1
      ∣ Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) :=
        Ideal.absNorm_dvd_absNorm_of_le hle
    _ = (p : ℕ) ^ Module.finrank ℤ (𝓞 K) :=
        gapsw80_t29_absNorm_span_natCast K (p : ℕ)

noncomputable scoped instance gapsw80_t30_instFintypeFiber {K : Type} [Field K]
    [NumberField K] (p : Nat.Primes) : Fintype (gapsw80_t30_Fiber K p) := by
  have _em := Classical.em
  refine @Fintype.ofFinite _ ?_
  refine @Finite.of_injective _
    {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ (p : ℕ) ^ Module.finrank ℤ (𝓞 K)}
    (Ideal.finite_setOf_absNorm_le _).to_subtype
    (fun q => ⟨q.1.1, Nat.le_of_dvd (Nat.one_le_pow _ _ p.2.pos)
      (gapsw80_t30_absNorm_fiber_dvd_pow q)⟩)
    ?_
  intro q₁ q₂ h
  exact Subtype.ext (Subtype.ext (by injection h))

theorem gapsw80_t30_primeBelow_eq_of_absNorm_dvd_pow {K : Type} [Field K]
    [NumberField K] (q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥})
    {p : Nat.Primes} {e : ℕ} (hN : Ideal.absNorm q.1 ∣ (p : ℕ) ^ e) :
    gapsw80_t29_primeBelow q = p := by
  have _em := Classical.em
  have hpp : (gapsw80_t29_primeBelow q : ℕ) ∣ (p : ℕ) ^ e :=
    (gapsw80_t30_primeBelow_dvd_absNorm q).trans hN
  exact Subtype.ext (((Nat.prime_dvd_prime_iff_eq
    (gapsw80_t29_primeBelow q).2 p.2).mp
      ((gapsw80_t29_primeBelow q).2.prime.dvd_of_dvd_pow hpp)))

theorem gapsw80_t30_irreducible_of_primeSubtype {K : Type} [Field K]
    [NumberField K] (q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    Irreducible q.1 :=
  (Ideal.prime_of_isPrime q.2.2 q.2.1).irreducible

private def gapsw80_t30_GeomP (α : Type) [Fintype α] : Prop :=
  ∀ (ζ : α → ℂ), (∀ i, ‖ζ i‖ < 1) →
    HasSum (fun k : α → ℕ => ∏ i, ζ i ^ k i) (∏ i, (1 - ζ i)⁻¹)
      ∧ Summable (fun k : α → ℕ => ‖∏ i, ζ i ^ k i‖)

private theorem gapsw80_t30_geomP_pempty : gapsw80_t30_GeomP PEmpty.{1} := by
  have _em := Classical.em
  intro ζ _
  have hfin : (fun k : PEmpty.{1} → ℕ => ∏ i, ζ i ^ k i)
      = fun _ => (1 : ℂ) :=
    funext fun _ => by rw [Finset.univ_eq_empty, Finset.prod_empty]
  rw [hfin, Finset.univ_eq_empty, Finset.prod_empty]
  have h1 := hasSum_fintype (fun _ : PEmpty.{1} → ℕ => (1 : ℂ))
  have h1N := hasSum_fintype (fun _ : PEmpty.{1} → ℕ => ‖(1 : ℂ)‖)
  rw [show (∑ _ : PEmpty.{1} → ℕ, (1 : ℂ)) = 1 by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]]
    at h1
  exact ⟨h1, h1N.summable⟩

set_option maxHeartbeats 3200000 in

private theorem gapsw80_t30_geomP_ofEquiv {α β : Type} [Fintype β]
    (e : α ≃ β) (IH : @gapsw80_t30_GeomP α (Fintype.ofEquiv β e.symm)) :
    gapsw80_t30_GeomP β := by
  have _em := Classical.em
  letI : Fintype α := Fintype.ofEquiv β e.symm
  intro ζ hζ
  obtain ⟨hIH, hIHs⟩ := IH (ζ ∘ e) (fun i => hζ (e i))
  let eqv : (α → ℕ) ≃ (β → ℕ) := Equiv.piCongrLeft' (fun _ => ℕ) e
  have hfe : (fun k : α → ℕ => ∏ i, (ζ ∘ e) i ^ k i)
      = (fun k' : β → ℕ => ∏ i, ζ i ^ k' i) ∘ eqv := by
    funext k
    have hk : ∀ i, k i = eqv k (e i) := fun i =>
      ((Equiv.piCongrLeft'_apply _ e k (e i)).trans
        (congrArg k (e.symm_apply_apply i))).symm
    calc ∏ i, (ζ ∘ e) i ^ k i
        = ∏ i, ζ (e i) ^ eqv k (e i) :=
          Finset.prod_congr rfl fun i _ => by rw [← hk i]; rfl
      _ = ∏ i, ζ i ^ eqv k i := e.prod_comp (fun i => ζ i ^ eqv k i)
  have hfe' : (fun k : α → ℕ => ‖∏ i, (ζ ∘ e) i ^ k i‖)
      = (fun k' : β → ℕ => ‖∏ i, ζ i ^ k' i‖) ∘ eqv := by
    funext k; exact congrArg norm (congrFun hfe k)
  have hL : (∏ i, (1 - (ζ ∘ e) i)⁻¹) = ∏ i, (1 - ζ i)⁻¹ :=
    e.prod_comp (fun i => (1 - ζ i)⁻¹)
  exact ⟨hL ▸ eqv.hasSum_iff.mp (hfe ▸ hIH),
    eqv.summable_iff.mp (hfe' ▸ hIHs)⟩

private def gapsw80_t30_optPiEquiv (α : Type) :
    (Option α → ℕ) ≃ ℕ × (α → ℕ) where
  toFun k := (k none, fun i => k (some i))
  invFun x o := o.elim x.1 x.2
  left_inv k := funext fun o => by cases o <;> rfl
  right_inv _ := rfl

set_option maxHeartbeats 3200000 in

private theorem gapsw80_t30_geomP_option {α : Type} [Fintype α]
    (IH : gapsw80_t30_GeomP α) : gapsw80_t30_GeomP (Option α) := by
  have _em := Classical.em
  intro ζ hζ
  obtain ⟨hIH, hIHs⟩ := IH (ζ ∘ some) (fun i => hζ (some i))
  set F : (α → ℕ) → ℂ := fun k => ∏ i, (ζ ∘ some) i ^ k i with hF_def
  have hgeom : HasSum (fun m : ℕ => ζ none ^ m) (1 - ζ none)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (hζ none)
  have hgeomN : Summable (fun m : ℕ => ‖ζ none ^ m‖) := by
    have hrw : (fun m : ℕ => ‖ζ none ^ m‖) = fun m => ‖ζ none‖ ^ m :=
      funext fun m => norm_pow _ _
    exact hrw ▸ summable_geometric_of_lt_one (norm_nonneg _) (hζ none)
  have hfg : Summable (fun x : ℕ × (α → ℕ) => ζ none ^ x.1 * F x.2) :=
    summable_mul_of_summable_norm (f := fun m => ζ none ^ m) (g := F)
      hgeomN hIHs
  have hmul : HasSum (fun x : ℕ × (α → ℕ) => ζ none ^ x.1 * F x.2)
      ((1 - ζ none)⁻¹ * ∏ i, (1 - (ζ ∘ some) i)⁻¹) :=
    HasSum.mul hgeom hIH hfg
  have hfe : (fun x : ℕ × (α → ℕ) => ζ none ^ x.1 * F x.2)
      = (fun k : Option α → ℕ => ∏ i, ζ i ^ k i)
        ∘ (gapsw80_t30_optPiEquiv α).symm := by
    funext x
    show ζ none ^ x.1 * F x.2 = ∏ i, ζ i ^ (gapsw80_t30_optPiEquiv α).symm x i
    rw [Fintype.prod_option, hF_def]
    rfl
  have hL : (1 - ζ none)⁻¹ * ∏ i, (1 - (ζ ∘ some) i)⁻¹
      = ∏ i, (1 - ζ i)⁻¹ :=
    (Fintype.prod_option (fun i => (1 - ζ i)⁻¹)).symm
  refine ⟨?_, ?_⟩
  · exact hL ▸ (gapsw80_t30_optPiEquiv α).symm.hasSum_iff.mp (hfe ▸ hmul)
  · have hfe' : (fun x : ℕ × (α → ℕ) => ‖ζ none ^ x.1 * F x.2‖)
        = (fun k : Option α → ℕ => ‖∏ i, ζ i ^ k i‖)
          ∘ (gapsw80_t30_optPiEquiv α).symm := by
      funext x; exact congrArg norm (congrFun hfe x)
    exact (gapsw80_t30_optPiEquiv α).symm.summable_iff.mp (hfe' ▸ hfg.norm)

theorem gapsw80_t30_hasSum_piNat_geometric {ι : Type} [Fintype ι]
    (ξ : ι → ℂ) (hξ : ∀ i, ‖ξ i‖ < 1) :
    HasSum (fun k : ι → ℕ => ∏ i, ξ i ^ k i) (∏ i, (1 - ξ i)⁻¹)
      ∧ Summable (fun k : ι → ℕ => ‖∏ i, ξ i ^ k i‖) :=
  Fintype.induction_empty_option (P := @gapsw80_t30_GeomP)
    (fun _ _ _ e => gapsw80_t30_geomP_ofEquiv e)
    gapsw80_t30_geomP_pempty
    (fun _ _ => gapsw80_t30_geomP_option) ι ξ hξ

section PSupp
variable {K : Type} [Field K] [NumberField K] {p : Nat.Primes}

abbrev gapsw80_t30_pSupp (K : Type) [Field K] [NumberField K]
    (p : Nat.Primes) : Type :=
  {J : (Ideal (𝓞 K))⁰ // ∃ e, Ideal.absNorm (J : Ideal (𝓞 K)) = (p : ℕ) ^ e}

noncomputable scoped instance : DecidableEq (Ideal (𝓞 K)) := Classical.decEq _

noncomputable def gapsw80_t30_fibProd (k : gapsw80_t30_Fiber K p → ℕ) :
    Ideal (𝓞 K) :=
  ∏ q : gapsw80_t30_Fiber K p, q.1.1 ^ k q

theorem gapsw80_t30_absNorm_fibProd (k : gapsw80_t30_Fiber K p → ℕ) :
    Ideal.absNorm (gapsw80_t30_fibProd k)
      = ∏ q : gapsw80_t30_Fiber K p, Ideal.absNorm q.1.1 ^ k q := by
  have _em := Classical.em
  unfold gapsw80_t30_fibProd
  rw [map_prod]
  exact Finset.prod_congr rfl fun q _ => map_pow _ _ _

theorem gapsw80_t30_absNorm_fibProd_isPow (k : gapsw80_t30_Fiber K p → ℕ) :
    ∃ e, Ideal.absNorm (gapsw80_t30_fibProd k) = (p : ℕ) ^ e := by
  have _em := Classical.em
  rw [gapsw80_t30_absNorm_fibProd]
  have hDvd : (∏ q, Ideal.absNorm q.1.1 ^ k q)
      ∣ (p : ℕ) ^ (Module.finrank ℤ (𝓞 K) * ∑ q, k q) := by
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun q _ =>
      pow_dvd_pow_of_dvd (gapsw80_t30_absNorm_fiber_dvd_pow q) (k q)
        |>.trans (by rw [← pow_mul])
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow p.2).mp hDvd
  exact ⟨e, he⟩

theorem gapsw80_t30_fibProd_mem_nZD (k : gapsw80_t30_Fiber K p → ℕ) :
    gapsw80_t30_fibProd k ∈ (Ideal (𝓞 K))⁰ := by
  have _em := Classical.em
  rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
  obtain ⟨e, he⟩ := gapsw80_t30_absNorm_fibProd_isPow k
  rw [he]; exact pow_ne_zero e p.2.pos.ne'

theorem gapsw80_t30_fibProd_eq_multisetProd (k : gapsw80_t30_Fiber K p → ℕ) :
    gapsw80_t30_fibProd k
      = (∑ q : gapsw80_t30_Fiber K p,
          k q • ({q.1.1} : Multiset (Ideal (𝓞 K)))).prod := by
  have _em := Classical.em
  rw [Multiset.prod_sum]
  unfold gapsw80_t30_fibProd
  exact Finset.prod_congr rfl fun q _ => by
    rw [Multiset.prod_nsmul, Multiset.prod_singleton]

theorem gapsw80_t30_normalizedFactors_fibProd
    (k : gapsw80_t30_Fiber K p → ℕ) :
    normalizedFactors (gapsw80_t30_fibProd k)
      = ∑ q : gapsw80_t30_Fiber K p,
          k q • ({q.1.1} : Multiset (Ideal (𝓞 K))) := by
  have _em := Classical.em
  rw [gapsw80_t30_fibProd_eq_multisetProd,
    normalizedFactors_prod_eq _ (fun a ha => ?_)]
  · refine (Multiset.map_congr rfl fun a _ => normalize_eq a).trans ?_
    exact Multiset.map_id _
  · simp only [Multiset.mem_sum, Multiset.mem_nsmul, Multiset.mem_singleton]
      at ha
    obtain ⟨q, _, _, rfl⟩ := ha
    exact gapsw80_t30_irreducible_of_primeSubtype q.1

theorem gapsw80_t30_ne_bot_of_absNorm_pow {e : ℕ} {I : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = (p : ℕ) ^ e) : I ≠ ⊥ := fun hbot => by
  rw [hbot, Ideal.absNorm_bot] at hI
  exact pow_ne_zero e p.2.pos.ne' hI.symm

theorem gapsw80_t30_factor_primeBelow_eq {I : Ideal (𝓞 K)} {e : ℕ}
    (hI : Ideal.absNorm I = (p : ℕ) ^ e) (hI0 : I ≠ 0)
    {x : Ideal (𝓞 K)} (hx : x ∈ normalizedFactors I) :
    ∃ q : gapsw80_t30_Fiber K p, q.1.1 = x := by
  have _em := Classical.em
  have hPrime : Prime x := ((mem_normalizedFactors_iff hI0).mp hx).1
  have hDvd : x ∣ I := ((mem_normalizedFactors_iff hI0).mp hx).2
  have hNdvd : Ideal.absNorm x ∣ (p : ℕ) ^ e := hI ▸
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hDvd)
  have hxPr : x.IsPrime := Ideal.isPrime_of_prime hPrime
  have hxNb : x ≠ ⊥ := hPrime.ne_zero
  exact ⟨⟨⟨x, hxPr, hxNb⟩,
    gapsw80_t30_primeBelow_eq_of_absNorm_dvd_pow ⟨x, hxPr, hxNb⟩ hNdvd⟩, rfl⟩

set_option maxHeartbeats 6400000 in

noncomputable def gapsw80_t30_pSuppEquiv :
    (gapsw80_t30_Fiber K p → ℕ) ≃ gapsw80_t30_pSupp K p where
  toFun k := ⟨⟨gapsw80_t30_fibProd k, gapsw80_t30_fibProd_mem_nZD k⟩,
    gapsw80_t30_absNorm_fibProd_isPow k⟩
  invFun I q := Multiset.count q.1.1 (normalizedFactors (I.1 : Ideal (𝓞 K)))
  left_inv k := by
    have _em := Classical.em
    funext q
    show Multiset.count q.1.1 (normalizedFactors (gapsw80_t30_fibProd k)) = k q
    rw [gapsw80_t30_normalizedFactors_fibProd, Multiset.count_sum']
    rw [Finset.sum_eq_single q]
    · rw [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
    · intro q' _ hq'
      rw [Multiset.count_nsmul, Multiset.count_singleton,
        if_neg (fun h => hq' (Subtype.ext (Subtype.ext h.symm))), mul_zero]
    · intro hq; exact (hq (Finset.mem_univ q)).elim
  right_inv I := by
    have _em := Classical.em
    obtain ⟨e, he⟩ := I.2
    have hI0 : (I.1 : Ideal (𝓞 K)) ≠ 0 :=
      gapsw80_t30_ne_bot_of_absNorm_pow he
    refine Subtype.ext (Subtype.ext ?_)
    show gapsw80_t30_fibProd _ = (I.1 : Ideal (𝓞 K))

    have hProd : (normalizedFactors (I.1 : Ideal (𝓞 K))).prod
        = (I.1 : Ideal (𝓞 K)) :=
      (prod_normalizedFactors_eq hI0).trans (normalize_eq _)
    rw [← hProd]

    have hInj : Set.InjOn (fun q : gapsw80_t30_Fiber K p => q.1.1)
        (Finset.univ : Finset (gapsw80_t30_Fiber K p)) := fun a _ b _ h =>
      Subtype.ext (Subtype.ext h)
    have hSub : (normalizedFactors (I.1 : Ideal (𝓞 K))).toFinset
        ⊆ Finset.image (fun q : gapsw80_t30_Fiber K p => q.1.1)
            Finset.univ := by
      intro x hx
      obtain ⟨q, hq⟩ := gapsw80_t30_factor_primeBelow_eq he hI0
        (Multiset.mem_toFinset.mp hx)
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩
    rw [Finset.prod_multiset_count_of_subset _ _ hSub, Finset.prod_image hInj]
    rfl

theorem gapsw80_t30_absNorm_pSuppEquiv (k : gapsw80_t30_Fiber K p → ℕ) :
    Ideal.absNorm ((gapsw80_t30_pSuppEquiv k).1 : Ideal (𝓞 K))
      = ∏ q : gapsw80_t30_Fiber K p, Ideal.absNorm q.1.1 ^ k q :=
  gapsw80_t30_absNorm_fibProd k

end PSupp
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section Regroup
variable {K : Type} [Field K] [NumberField K] {p : Nat.Primes}

private noncomputable def gapsw80_t30_sigF (K : Type) [Field K] [NumberField K]
    (p : Nat.Primes) (s : ℂ) :
    (Σ e, {J : (Ideal (𝓞 K))⁰ //
      Ideal.absNorm (J : Ideal (𝓞 K)) = (p : ℕ) ^ e}) → ℂ :=
  fun x => ((Ideal.absNorm (x.2.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)

noncomputable def gapsw80_t30_pSuppSigma :
    gapsw80_t30_pSupp K p ≃ Σ e, {J : (Ideal (𝓞 K))⁰ //
      Ideal.absNorm (J : Ideal (𝓞 K)) = (p : ℕ) ^ e} where
  toFun J := ⟨Nat.log p (Ideal.absNorm (J.1 : Ideal (𝓞 K))),
    ⟨J.1, by
      obtain ⟨e, he⟩ := J.2
      rw [he, Nat.log_pow p.2.one_lt]⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  left_inv J := Subtype.ext rfl
  right_inv := by
    rintro ⟨e, J, hJ⟩
    have h1 : Nat.log p (Ideal.absNorm (J : Ideal (𝓞 K))) = e := by
      rw [hJ, Nat.log_pow p.2.one_lt]
    subst h1; rfl

set_option maxHeartbeats 6400000 in

theorem gapsw80_t30_hasSum_pSupp_absNorm {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun J : gapsw80_t30_pSupp K p =>
        ((Ideal.absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (∑' e : ℕ, LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        s ((p : ℕ) ^ e)) := by
  have _em := Classical.em

  have hInj : Function.Injective
      (fun x : Σ e, {J : (Ideal (𝓞 K))⁰ //
          Ideal.absNorm (J : Ideal (𝓞 K)) = (p : ℕ) ^ e} =>
        (x.2.1 : (Ideal (𝓞 K))⁰)) := by
    rintro ⟨e₁, J₁, hJ₁⟩ ⟨e₂, J₂, hJ₂⟩ h
    simp only at h; subst h
    obtain rfl : e₁ = e₂ := Nat.pow_right_injective p.2.two_le
      (hJ₁.symm.trans hJ₂)
    rfl
  have hSum : Summable (gapsw80_t30_sigF K p s) := by
    have h := (gapsw80_t10_summable_idealNorm K hs).comp_injective hInj
    exact h

  have hFib : ∀ e : ℕ, HasSum
      (fun J : {J : (Ideal (𝓞 K))⁰ //
          Ideal.absNorm (J : Ideal (𝓞 K)) = (p : ℕ) ^ e} =>
        gapsw80_t30_sigF K p s ⟨e, J⟩)
      (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        s ((p : ℕ) ^ e)) := fun e =>
    gapsw80_t10_fiber_hasSum K s ((p : ℕ) ^ e)

  have hOuter := hSum.hasSum.sigma hFib
  have hSigma : HasSum (gapsw80_t30_sigF K p s)
      (∑' e : ℕ, LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        s ((p : ℕ) ^ e)) :=
    hOuter.tsum_eq ▸ hSum.hasSum

  have hfe : gapsw80_t30_sigF K p s
      = (fun J : gapsw80_t30_pSupp K p =>
          ((Ideal.absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
        ∘ gapsw80_t30_pSuppSigma.symm :=
    funext fun x => rfl
  exact (gapsw80_t30_pSuppSigma.symm.hasSum_iff).mp (hfe ▸ hSigma)

end Regroup
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

theorem gapsw80_t30_natCast_finsetProd_cpow {ι : Type} (s : Finset ι)
    (n : ι → ℕ) (w : ℂ) :
    ((∏ i ∈ s, n i : ℕ) : ℂ) ^ w = ∏ i ∈ s, ((n i : ℂ) ^ w) := by
  have _em := Classical.em
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' ha IH =>
    rw [Finset.prod_insert ha, Nat.cast_mul, ← Complex.ofReal_natCast (n a),
      ← Complex.ofReal_natCast (∏ i ∈ s', n i),
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      Complex.ofReal_natCast, Complex.ofReal_natCast, Finset.prod_insert ha,
      IH]

theorem gapsw80_t30_natCast_pow_cpow (n k : ℕ) (w : ℂ) :
    ((n ^ k : ℕ) : ℂ) ^ w = ((n : ℂ) ^ w) ^ k := by
  have _em := Classical.em
  induction k with
  | zero => simp
  | succ k IH =>
    rw [pow_succ, Nat.cast_mul, ← Complex.ofReal_natCast (n ^ k),
      ← Complex.ofReal_natCast n,
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      Complex.ofReal_natCast, Complex.ofReal_natCast, IH, pow_succ]

set_option maxHeartbeats 12800000 in

theorem gapsw80_t30_localEulerFactorPerNatPrime :
    gapsw80_t29_LocalEulerFactorPerNatPrime := by
  have _em := Classical.em
  intro K _ _ s hs p

  obtain ⟨hGeom, _⟩ := gapsw80_t30_hasSum_piNat_geometric
    (ι := gapsw80_t30_Fiber K p)
    (fun q => ((Ideal.absNorm q.1.1 : ℕ) : ℂ) ^ (-s))
    (fun q => gapsw80_t27_norm_absNorm_cpow_lt_one q.1 hs)

  have hfe : (fun k : gapsw80_t30_Fiber K p → ℕ =>
        ∏ q, (((Ideal.absNorm q.1.1 : ℕ) : ℂ) ^ (-s)) ^ k q)
      = (fun J : gapsw80_t30_pSupp K p =>
          ((Ideal.absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
        ∘ gapsw80_t30_pSuppEquiv := by
    funext k
    show _ = ((Ideal.absNorm
      ((gapsw80_t30_pSuppEquiv k).1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)
    rw [gapsw80_t30_absNorm_pSuppEquiv,
      gapsw80_t30_natCast_finsetProd_cpow Finset.univ _ (-s)]
    exact (Finset.prod_congr rfl fun q _ =>
      gapsw80_t30_natCast_pow_cpow (Ideal.absNorm q.1.1) (k q) (-s)).symm
  have hPSupp : HasSum (fun J : gapsw80_t30_pSupp K p =>
        ((Ideal.absNorm (J.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (∏ q : gapsw80_t30_Fiber K p,
        (1 - ((Ideal.absNorm q.1.1 : ℕ) : ℂ) ^ (-s))⁻¹) :=
    gapsw80_t30_pSuppEquiv.hasSum_iff.mp (hfe ▸ hGeom)

  have hEq : (∏ q : gapsw80_t30_Fiber K p,
        (1 - ((Ideal.absNorm q.1.1 : ℕ) : ℂ) ^ (-s))⁻¹)
      = ∑' e : ℕ, LSeries.term
          (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
          s ((p : ℕ) ^ e) :=
    HasSum.unique hPSupp (gapsw80_t30_hasSum_pSupp_absNorm hs)

  exact hEq ▸ hasProd_fintype _

end FLT.Gapsw80T30D2d0cLocalEulerFactorProof
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T62ArchGammaKernelRemintWire

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
open FLT.Gapsw80T24StripMigrationChainStart
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T26D2dTwoConjunctDecomp
open FLT.Gapsw80T27D2d0EulerProductAncestor
open FLT.Gapsw80T28D2d0aSummabilityProof
open FLT.Gapsw80T29D2d0bNatEulerProductBridge
open FLT.Gapsw80T30D2d0cLocalEulerFactorProof
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T33D1apZetaExtQuotientDecomp
open FLT.Gapsw80T34D1apaThreeFourOneIneqDecomp
open FLT.Gapsw80T35D1apa0ThreeFourOneIneqProof
open FLT.Gapsw80T36D1appXiEndpointResidueProof
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T40D1b0bZeroFreeExpLinearProof
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
open FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
open FLT.Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
open FLT.Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof
open FLT.Gapsw80T46D1b0a1cEntireQuotientOfOrderMatchProof
open FLT.Gapsw80T47D1b0a1aZeroEnumSummableSubDecomp
open FLT.Gapsw80T48D1b0a1aiZeroEnumWithMultProof
open FLT.Gapsw80T49D1b0a1aiiEnumNormSqSummableProof
open FLT.Gapsw80T50D1b0a2MinModulusSubDecomp
open FLT.Gapsw80T51D1b0a2bNonvanishSubTwoExpLinearProof
open FLT.Gapsw80T52D1b0a2aBoasMinModulusSubDecomp
open FLT.Gapsw80T53D1b0a2aiiAnnulusToGlobalGrowthProof
open FLT.Gapsw80T54D1b0a2aiZeroCountBoasCoreSubDecomp
open FLT.Gapsw80T55D1b0a2aiAZeroCountJensenBoundProof
open FLT.Gapsw80T56D1b0a2aiBBoasCartanMinModulusSubDecomp
open FLT.Gapsw80T57D1b0a2aiBGammaCartanGoodRadiusProof
open FLT.Gapsw80T58D1b0a2aiBAlphaFarTailProductLowerBoundProof
open FLT.Gapsw80T59D1b0a2aiBBetaMinModulusAssemblyProof
open FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
open FLT.Gapsw80T61D2cbArchGammaParsevalFalseprobe
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t62_D2d_closed : gapsw80_t21_DedekindZetaEulerExpansion := by
  have _em := Classical.em
  have hd0 := gapsw80_t28_D2d0_of_D2d0b
    (gapsw80_t29_D2d0b_of_D2d0c gapsw80_t30_localEulerFactorPerNatPrime)
  exact gapsw80_t26_D2d_of_D2d1_D2d2
    (gapsw80_t27_D2d1_of_D2d0 hd0) (gapsw80_t27_D2d2_of_D2d0 hd0)

def gapsw80_t62_ArchGammaKernelIdentityCorrected : Prop :=
  ∀ (F : ℝ → ℝ), gapsw50_t2_OdlyzkoAdmissibleKernel F →
    -(1 / Real.pi) * ∫ t : ℝ,
        (logDeriv Gammaℂ (1 / 2 + t * I)).re
          * (∫ x : ℝ, F x * Real.cos (t * x))
      = 2 * gapsw80_t18_archDerived F + 2 * Real.log 2

def gapsw80_t62_ArchGammaParsevalAssemblyCorrected : Prop :=
  ∀ (F : ℝ → ℝ), gapsw50_t2_OdlyzkoAdmissibleKernel F →
    -(1 / Real.pi) * ∫ t : ℝ,
        (-Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 2 * Real.log 2
          + ∫ x in Set.Ioi (0:ℝ),
              (1 - Real.cos (t * x)) / (Real.exp (x / 2) - Real.exp (-(x / 2))))
        * (∫ x : ℝ, F x * Real.cos (t * x))
      = 2 * gapsw80_t18_archDerived F + 2 * Real.log 2

set_option maxHeartbeats 6400000 in

theorem gapsw80_t62_D2cp_of_D2ca_D2cbp
    (hca : gapsw80_t60_DigammaReCriticalLineCosKernel)
    (hcb' : gapsw80_t62_ArchGammaParsevalAssemblyCorrected) :
    gapsw80_t62_ArchGammaKernelIdentityCorrected := by
  have _em := Classical.em
  intro F hF
  rw [← hcb' F hF]
  congr 1
  congr 1
  funext t
  congr 1
  rw [gapsw80_t60_re_logDeriv_Gammaℂ_critical_line t, hca t]
  ring

end FLT.Gapsw80T62ArchGammaKernelRemintWire
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T63CosineInversionWire

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
open FLT.Gapsw80T61D2cbArchGammaParsevalFalseprobe
open FLT.Gapsw80T62ArchGammaKernelRemintWire
p2m_open "Real P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Real MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory Filter P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Filter Asymptotics P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Asymptotics Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology"

set_option maxHeartbeats 12800000 in

theorem gapsw80_t63_J_integrableOn {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) :
    IntegrableOn (fun x => (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2))))
      (Set.Ioi (0:ℝ)) := by
  have _em := Classical.em
  obtain ⟨hdiff, heven, hF0, _, ⟨c, ε, hc, hε, hdecay⟩, _⟩ := hF
  set D : ℝ → ℝ := fun x => Real.exp (x / 2) - Real.exp (-(x / 2)) with hD_def
  have hD_pos : ∀ x, 0 < x → 0 < D x := fun x hx =>
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hD_ge : ∀ x, 0 < x → x / 2 ≤ D x := fun x hx => by
    have h1 := Real.add_one_le_exp (x/2)
    have h2 : Real.exp (-(x/2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    simp only [hD_def]; linarith
  have hcont : ContinuousOn (fun x => (1 - F x) / D x) (Set.Ioi (0:ℝ)) :=
    ContinuousOn.div (continuous_const.sub hdiff.continuous).continuousOn
      ((Real.continuous_exp.comp (continuous_id.div_const 2)).sub
        (Real.continuous_exp.comp (continuous_id.div_const 2).neg)).continuousOn
      (fun x hx => (hD_pos x hx).ne')

  have hquo : Tendsto (fun x => (1 - F x) / x) (𝓝[≠] 0) (𝓝 0) := by
    have hF'0 : deriv F 0 = 0 := by
      have h1 : (fun x => F (-x)) = F := funext heven
      have h2 := deriv_comp_neg F 0; rw [h1, _root_.neg_zero] at h2; linarith
    have hDA : HasDerivAt F 0 0 := by
      have := (hdiff 0).hasDerivAt; rwa [hF'0] at this
    have hlo : (fun x => F x - 1) =o[𝓝 0] (fun x => x) := by
      have := hDA.isLittleO; simpa [hF0] using this
    have heq : (fun x => (1 - F x)/x) = fun x => -((F x - 1)/x) := by funext x; ring
    rw [heq]
    simpa using (hlo.tendsto_div_nhds_zero.mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))).neg
  rw [Metric.tendsto_nhdsWithin_nhds] at hquo
  obtain ⟨δ₀, hδ₀, hball⟩ := hquo 1 one_pos
  have hcbound : |F 0| ≤ c := by
    have := hdecay 0; simpa using this
  have h1c : (0:ℝ) ≤ 1 + c := by linarith [abs_nonneg (F 0)]

  set M : ℝ := 2 + 2 * (1 + c) / δ₀ with hM_def
  have hM_pos : 0 < M := by positivity
  have hbdd : ∀ x ∈ Set.Ioc (0:ℝ) (2 * Real.log 2),
      ‖(1 - F x) / D x‖ ≤ M := by
    intro x hx
    have hx1 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hD_pos x hx1)]
    rcases lt_or_ge x δ₀ with hxδ | hxδ
    ·
      have hne : x ∈ ({0}ᶜ : Set ℝ) := by simp; exact hx1.ne'
      have hd : dist x 0 < δ₀ := by rw [Real.dist_eq, sub_zero, abs_of_pos hx1]; exact hxδ
      have hb : |(1 - F x) / x| < 1 := by
        have := hball hne hd; rwa [Real.dist_eq, sub_zero] at this
      rw [abs_div, abs_of_pos hx1] at hb
      have h1Fx : |1 - F x| < x := (div_lt_one hx1).mp hb
      calc |1 - F x| / D x ≤ x / (x / 2) :=
            div_le_div₀ hx1.le h1Fx.le (by linarith) (hD_ge x hx1)
        _ = 2 := by field_simp
        _ ≤ M := le_add_of_nonneg_right (by positivity)
    ·
      have h1F : |1 - F x| ≤ 1 + c := by
        calc |1 - F x| ≤ |(1:ℝ)| + |F x| := abs_sub _ _
          _ ≤ 1 + c := by
              rw [abs_one]; gcongr
              calc |F x| ≤ c * Real.exp (-(1/2+ε) * |x|) := hdecay x
                _ ≤ c * 1 := by
                    gcongr
                    exact Real.exp_le_one_iff.mpr
                      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg _))
                _ = c := mul_one c
      calc |1 - F x| / D x ≤ (1 + c) / (δ₀ / 2) := by
            apply div_le_div₀ h1c h1F (by linarith)
            calc δ₀ / 2 ≤ x / 2 := by linarith
              _ ≤ D x := hD_ge x hx1
        _ = 2 * (1 + c) / δ₀ := by ring
        _ ≤ M := by rw [hM_def]; linarith

  have hlog2 : 0 < (2:ℝ) * Real.log 2 := by positivity
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 (2*Real.log 2) ∪ Set.Ioi (2*Real.log 2) from
    (Set.Ioc_union_Ioi_eq_Ioi hlog2.le).symm]
  refine IntegrableOn.union ?_ ?_
  ·
    exact (integrableOn_const measure_Ioc_lt_top.ne).mono'
      ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hbdd))
  ·
    apply ((gapsw80_t61_integral_Ioi_exp_neg_half (2*Real.log 2)).1.const_mul
      (2 * (1 + c))).mono'
      ((hcont.mono (Set.Ioi_subset_Ioi hlog2.le)).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 0 < x := hlog2.trans hx
    have hx2 : 2 * Real.log 2 < x := hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hD_pos x hx1)]
    have hDx2 : Real.exp (x/2) / 2 ≤ D x := by
      have hex : Real.exp (-(x/2)) ≤ (2:ℝ)⁻¹ := by
        rw [show ((2:ℝ)⁻¹) = Real.exp (-Real.log 2) by
          rw [Real.exp_neg, Real.exp_log two_pos]]
        exact Real.exp_le_exp.mpr (by linarith)
      simp only [hD_def]
      have hex1 : Real.exp (x/2) ≥ 1 := Real.one_le_exp (by linarith)
      linarith
    have h1F : |1 - F x| ≤ 1 + c := by
      calc |1 - F x| ≤ |(1:ℝ)| + |F x| := abs_sub _ _
        _ ≤ 1 + c := by
            rw [abs_one]; gcongr
            calc |F x| ≤ c * Real.exp (-(1/2+ε) * |x|) := hdecay x
              _ ≤ c * 1 := by
                  gcongr
                  exact Real.exp_le_one_iff.mpr
                    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg _))
              _ = c := mul_one c
    calc |1 - F x| / D x ≤ (1 + c) / (Real.exp (x/2) / 2) :=
          div_le_div₀ h1c h1F (by positivity) hDx2
      _ = 2 * (1 + c) * Real.exp (-(x/2)) := by
          rw [Real.exp_neg]; field_simp

def gapsw80_t63_CosineInversionAdmissible : Prop :=
  ∀ (F : ℝ → ℝ), gapsw50_t2_OdlyzkoAdmissibleKernel F →
    Integrable (fun t => ∫ x : ℝ, F x * Real.cos (t * x))
    ∧ ∀ u : ℝ,
        ∫ t : ℝ, (∫ x : ℝ, F x * Real.cos (t * x)) * Real.cos (u * t)
          = 2 * Real.pi * F u

set_option maxHeartbeats 6400000 in

theorem gapsw80_t63_integral_one_sub_cos_mul_fhat {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hint : Integrable (fun t => ∫ x : ℝ, F x * Real.cos (t * x)))
    (hinv : ∀ u, ∫ t : ℝ, (∫ x : ℝ, F x * Real.cos (t * x)) * Real.cos (u * t)
      = 2 * Real.pi * F u) (x : ℝ) :
    ∫ t : ℝ, (1 - Real.cos (t * x)) * (∫ y : ℝ, F y * Real.cos (t * y))
      = 2 * Real.pi * (1 - F x) := by
  have _em := Classical.em
  set Fh : ℝ → ℝ := fun t => ∫ y : ℝ, F y * Real.cos (t * y) with hFh_def
  have hFh_nn : ∀ t, 0 ≤ Fh t := hF.2.2.2.2.2
  have hcint : Integrable (fun t => Real.cos (t * x) * Fh t) := by
    refine hint.mono' ?_ ?_
    · exact ((Real.continuous_cos.comp (continuous_id.mul
        continuous_const)).aestronglyMeasurable).mul hint.1
    · filter_upwards with t
      simp only [Real.norm_eq_abs]
      rw [show |Real.cos (t * x) * Fh t| = |Real.cos (t * x)| * Fh t from by
        rw [abs_mul, abs_of_nonneg (hFh_nn t)]]
      exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _)
        (hFh_nn t)).trans_eq (one_mul _)
  have hint0 : ∫ t, Fh t = 2 * Real.pi := by
    have h := hinv 0
    simp only [zero_mul, Real.cos_zero, mul_one, hF.2.2.1] at h
    exact h
  have hintx : ∫ t, Real.cos (t * x) * Fh t = 2 * Real.pi * F x := by
    have h := hinv x
    rw [← h]; congr 1; funext t; rw [mul_comm t x, mul_comm]
  calc ∫ t, (1 - Real.cos (t * x)) * Fh t
      = (∫ t, Fh t) - ∫ t, Real.cos (t * x) * Fh t := by
        rw [← integral_sub hint hcint]; congr 1; funext t; ring
    _ = 2 * Real.pi - 2 * Real.pi * F x := by rw [hint0, hintx]
    _ = 2 * Real.pi * (1 - F x) := by ring

set_option maxHeartbeats 25600000 in

theorem gapsw80_t63_fubini_K1 {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hint : Integrable (fun t => ∫ x : ℝ, F x * Real.cos (t * x)))
    (hinv : ∀ u, ∫ t : ℝ, (∫ x : ℝ, F x * Real.cos (t * x)) * Real.cos (u * t)
      = 2 * Real.pi * F u) :
    Integrable (fun t : ℝ =>
      (∫ x in Set.Ioi (0:ℝ),
        (1 - Real.cos (t * x)) / (Real.exp (x / 2) - Real.exp (-(x / 2))))
      * (∫ y : ℝ, F y * Real.cos (t * y)))
    ∧ ∫ t : ℝ,
        (∫ x in Set.Ioi (0:ℝ),
          (1 - Real.cos (t * x)) / (Real.exp (x / 2) - Real.exp (-(x / 2))))
        * (∫ y : ℝ, F y * Real.cos (t * y))
      = 2 * Real.pi
        * ∫ x in Set.Ioi (0:ℝ),
            (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2))) := by
  have _em := Classical.em
  set Fh : ℝ → ℝ := fun t => ∫ y : ℝ, F y * Real.cos (t * y) with hFh_def
  have hFh_nn : ∀ t, 0 ≤ Fh t := hF.2.2.2.2.2
  set D : ℝ → ℝ := fun x => Real.exp (x / 2) - Real.exp (-(x / 2)) with hD_def
  have hD_pos : ∀ x ∈ Set.Ioi (0:ℝ), 0 < D x := fun x hx =>
    sub_pos.mpr (Real.exp_lt_exp.mpr (by simp at hx; linarith))
  set f : ℝ → ℝ → ℝ := fun x t => (1 - Real.cos (t * x)) * Fh t / D x with hf_def
  have hFh_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Fh p.2)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod volume) := hint.1.comp_snd
  have hf_meas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod volume) := by
    have hrest : Measurable
        (fun p : ℝ × ℝ => (1 - Real.cos (p.2 * p.1)) / D p.1) :=
      ((measurable_const.sub (Real.measurable_cos.comp
        (measurable_snd.mul measurable_fst))).div
        ((Real.measurable_exp.comp (measurable_fst.div_const 2)).sub
          (Real.measurable_exp.comp (measurable_fst.div_const 2).neg)))
    refine (hrest.aestronglyMeasurable.mul hFh_aesm).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hf_def, Pi.mul_apply]; ring
  have hf_nn : ∀ x ∈ Set.Ioi (0:ℝ), ∀ t, 0 ≤ f x t := by
    intro x hx t
    apply div_nonneg ?_ (hD_pos x hx).le
    exact mul_nonneg (by linarith [Real.cos_le_one (t * x)]) (hFh_nn t)
  have hfib : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0:ℝ))),
      Integrable (fun t => f x t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    refine (hint.const_mul (2 / D x)).mono' ?_ ?_
    · have h1 : AEStronglyMeasurable
          (fun t : ℝ => (1 - Real.cos (t * x)) * Fh t) volume := by
        refine AEStronglyMeasurable.mul ?_ hint.1
        exact (continuous_const.sub (Real.continuous_cos.comp
          (continuous_id.mul continuous_const))).aestronglyMeasurable
      refine (h1.mul_const (D x)⁻¹).congr (Eventually.of_forall fun t => ?_)
      simp only [hf_def]; ring
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn x hx t), hf_def]
    rw [show (2:ℝ) / D x * Fh t = 2 * Fh t / D x from by ring]
    apply div_le_div_of_nonneg_right ?_ (hD_pos x hx).le
    apply mul_le_mul_of_nonneg_right ?_ (hFh_nn t)
    linarith [Real.neg_one_le_cos (t * x), Real.cos_le_one (t * x)]
  have hfib_eval : ∀ x ∈ Set.Ioi (0:ℝ),
      ∫ t, f x t = 2 * Real.pi * (1 - F x) / D x := by
    intro x hx
    rw [hf_def, show (fun t => (1 - Real.cos (t * x)) * Fh t / D x)
        = fun t => (1 - Real.cos (t * x)) * Fh t * (D x)⁻¹ by funext t; ring,
      integral_mul_const, gapsw80_t63_integral_one_sub_cos_mul_fhat hF hint hinv x]
    ring
  have hfib_norm_int : Integrable (fun x => ∫ t, ‖f x t‖)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply ((gapsw80_t63_J_integrableOn hF).const_mul (2 * Real.pi)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : ∫ t, ‖f x t‖ = ∫ t, f x t := by
      congr 1; funext t; rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn x hx t)]
    rw [this, hfib_eval x hx, hD_def]; ring
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod volume) :=
    (integrable_prod_iff hf_meas).mpr ⟨hfib, hfib_norm_int⟩
  have hswap := integral_integral_swap hprod
  have hLHS : ∫ x, (∫ t, f x t) ∂(volume.restrict (Set.Ioi (0:ℝ)))
      = 2 * Real.pi * ∫ x in Set.Ioi (0:ℝ), (1 - F x) / D x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx; simp only; rw [hfib_eval x hx]; ring
  have hRHS : ∫ t, (∫ x, f x t ∂(volume.restrict (Set.Ioi (0:ℝ))))
      = ∫ t : ℝ, (∫ x in Set.Ioi (0:ℝ), (1 - Real.cos (t * x)) / D x) * Fh t := by
    congr 1; funext t
    rw [show (fun x => f x t) = fun x => (1 - Real.cos (t * x)) / D x * Fh t by
      funext x; rw [hf_def]; ring]
    rw [integral_mul_const]
  have htmarg : Integrable
      (fun t => ∫ x, f x t ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
    hprod.swap.integral_prod_left
  refine ⟨?_, ?_⟩
  · apply htmarg.congr
    filter_upwards with t
    rw [show (fun x => f x t) = fun x => (1 - Real.cos (t * x)) / D x * Fh t by
      funext x; rw [hf_def]; ring]
    rw [integral_mul_const]
  · rw [← hRHS, ← hswap, hLHS, hD_def]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t63_D2cbp_of_D2f
    (hD2f : gapsw80_t63_CosineInversionAdmissible) :
    gapsw80_t62_ArchGammaParsevalAssemblyCorrected := by
  have _em := Classical.em
  intro F hF
  obtain ⟨hint, hinv⟩ := hD2f F hF
  set Fh : ℝ → ℝ := fun t => ∫ y : ℝ, F y * Real.cos (t * y) with hFh_def
  set K₀ : ℝ := -Real.log (2 * Real.pi) - Real.eulerMascheroniConstant
    - 2 * Real.log 2 with hK₀
  set K₁ : ℝ → ℝ := fun t => ∫ x in Set.Ioi (0:ℝ),
    (1 - Real.cos (t * x)) / (Real.exp (x / 2) - Real.exp (-(x / 2))) with hK₁
  set J : ℝ := ∫ x in Set.Ioi (0:ℝ),
    (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2))) with hJ

  have hint0 : ∫ t, Fh t = 2 * Real.pi := by
    have h := hinv 0
    simp only [zero_mul, Real.cos_zero, mul_one, hF.2.2.1] at h
    exact h
  have hK₀_int : Integrable (fun t => K₀ * Fh t) := hint.const_mul K₀

  obtain ⟨hK₁_int, hK₁_eval⟩ := gapsw80_t63_fubini_K1 hF hint hinv

  have hsplit : ∫ t : ℝ, (K₀ + K₁ t) * Fh t
      = K₀ * (2 * Real.pi) + 2 * Real.pi * J := by
    calc ∫ t : ℝ, (K₀ + K₁ t) * Fh t
        = ∫ t : ℝ, K₀ * Fh t + K₁ t * Fh t := by congr 1; funext t; ring
      _ = (∫ t, K₀ * Fh t) + ∫ t, K₁ t * Fh t := integral_add hK₀_int hK₁_int
      _ = K₀ * (2 * Real.pi) + 2 * Real.pi * J := by
          rw [integral_const_mul, hint0, hK₁_eval]

  rw [hsplit]
  have heval : -(1/Real.pi) * (K₀ * (2*Real.pi) + 2*Real.pi * J)
      = -2 * K₀ - 2 * J := by field_simp; ring
  rw [heval, gapsw80_t18_archDerived, hK₀, ← hJ]
  have hlog4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [show (4:ℝ) * Real.pi = 2 ^ 2 * Real.pi by ring,
      Real.log_mul (by norm_num) Real.pi_ne_zero, Real.log_pow]; ring
  have hlog2π : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul two_ne_zero Real.pi_ne_zero
  rw [hlog4, hlog2π]; ring

end FLT.Gapsw80T63CosineInversionWire
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T69AdmC2RemintZktSummable

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
open FLT.Gapsw80T24StripMigrationChainStart
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T64D2fGaussianMollificationProof
open FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint
open FLT.Gapsw80T68D2bppExplicitFormulaSubDecomp
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory"

def gapsw80_t69_KernelC2Decay (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 F ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))

def gapsw80_t69_OdlyzkoAdmissibleKernelStripC2 (F : ℝ → ℝ) : Prop :=
  gapsw80_t23_OdlyzkoAdmissibleKernelStrip F ∧ gapsw80_t69_KernelC2Decay F

set_option maxHeartbeats 3200000 in

theorem gapsw80_t69_stripC2_implies_line {F : ℝ → ℝ}
    (hF : gapsw80_t69_OdlyzkoAdmissibleKernelStripC2 F) :
    gapsw50_t2_OdlyzkoAdmissibleKernel F := by
  have _em := Classical.em
  exact gapsw80_t23_stripAdmissible_implies_lineAdmissible hF.1

def gapsw80_t69_ContourPairedExplicitFormulaC2 : Prop :=
  gapsw80_t62_ArchGammaKernelIdentityCorrected →
  gapsw80_t21_DedekindZetaEulerExpansion →
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K],
    ∀ (B : ℂ) (ρ : ℕ → ℂ),
      (∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) →
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv
            (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
          = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)) →
      ∀ (F : ℝ → ℝ), gapsw50_t2_OdlyzkoAdmissibleKernel F →
        gapsw80_t69_KernelC2Decay F →
        Real.log |(discr K : ℝ)| =
          (gapsw80_t18_archTermDerived F (finrank ℚ K)
            + (finrank ℚ K : ℝ) * Real.log 2)
            + 2 * gapsw52_t2_OdlyzkoPrimeIdealSum F K
            + gapsw80_t21_zeroKernelSum F ρ

end FLT.Gapsw80T69AdmC2RemintZktSummable
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T64D2fGaussianMollificationProof

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
open FLT.Gapsw80T61D2cbArchGammaParsevalFalseprobe
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T63CosineInversionWire
p2m_open "Real P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Real MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory Filter P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Filter Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology"

set_option maxHeartbeats 6400000 in

theorem gapsw80_t64_integrable_F {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) : Integrable F := by
  have _em := Classical.em
  obtain ⟨hdiff, _, _, _, ⟨c, δ, hc, hδ, hdecay⟩, _⟩ := hF
  have ha : (0:ℝ) < 1/2 + δ := by linarith

  have hexp_Ici : IntegrableOn
      (fun x : ℝ => Real.exp (-((1/2 + δ) * |x|))) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine (exp_neg_integrableOn_Ioi 0 ha).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp only [Set.mem_Ioi] at hx
    beta_reduce
    rw [abs_of_pos hx, neg_mul]
  have hexp_Iic : IntegrableOn
      (fun x : ℝ => Real.exp (-((1/2 + δ) * |x|))) (Set.Iic 0) := by
    have hc2 := hexp_Ici.comp_neg
    rw [Set.neg_Ici, _root_.neg_zero] at hc2
    exact hc2.congr_fun (fun x _ => by beta_reduce; rw [abs_neg]) measurableSet_Iic
  have hmaj : Integrable (fun x => c * Real.exp (-((1/2 + δ) * |x|))) := by
    apply Integrable.const_mul
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
    exact hexp_Iic.union (hexp_Ici.mono_set Set.Ioi_subset_Ici_self)
  refine hmaj.mono' hdiff.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  calc |F x| ≤ c * Real.exp (-(1/2 + δ) * |x|) := hdecay x
    _ = c * Real.exp (-((1/2 + δ) * |x|)) := by rw [neg_mul]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t64_continuous_Fhat {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) :
    Continuous (fun t => ∫ x : ℝ, F x * Real.cos (t * x)) := by
  have _em := Classical.em
  have hFint := gapsw80_t64_integrable_F hF
  apply continuous_of_dominated
  · intro t
    exact (hF.1.continuous.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  · intro t
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    calc |F x| * |Real.cos (t * x)| ≤ |F x| * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = |F x| := mul_one _
  · exact hFint.abs
  · filter_upwards with x
    exact (continuous_const.mul (Real.continuous_cos.comp
      (continuous_id.mul continuous_const)))

set_option maxHeartbeats 25600000 in

theorem gapsw80_t64_mollified_identity {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    Integrable (fun t =>
      (∫ x : ℝ, F x * Real.cos (t * x)) * Real.cos (u * t) * Real.exp (-(ε * t ^ 2)))
    ∧ ∫ t : ℝ, (∫ x : ℝ, F x * Real.cos (t * x)) * Real.cos (u * t)
        * Real.exp (-(ε * t ^ 2))
      = Real.sqrt (Real.pi / ε) * ∫ x : ℝ, F x * Real.exp (-((x - u) ^ 2 / (4 * ε))) := by
  have _em := Classical.em
  have hdiff := hF.1
  have heven := hF.2.1
  have hFint := gapsw80_t64_integrable_F hF

  set G : ℝ → ℝ → ℝ := fun t x =>
    F x * Real.cos (t * x) * Real.cos (u * t) * Real.exp (-(ε * t ^ 2)) with hG_def

  have hG_meas : AEStronglyMeasurable (Function.uncurry G)
      ((volume : Measure ℝ).prod volume) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    apply Continuous.mul
    apply Continuous.mul
    · exact hdiff.continuous.comp continuous_snd
    · exact Real.continuous_cos.comp (continuous_fst.mul continuous_snd)
    · exact Real.continuous_cos.comp (continuous_const.mul continuous_fst)
    · exact Real.continuous_exp.comp (continuous_const.mul (continuous_fst.pow 2)).neg

  have hmaj : Integrable (fun p : ℝ × ℝ => Real.exp (-(ε * p.1 ^ 2)) * |F p.2|)
      ((volume : Measure ℝ).prod volume) := by
    refine ((integrable_exp_neg_mul_sq hε).mul_prod hFint.abs).congr
      (Eventually.of_forall fun p => ?_)
    simp only [neg_mul]
  have hG_int : Integrable (Function.uncurry G)
      ((volume : Measure ℝ).prod volume) := by
    refine hmaj.mono' hG_meas (Eventually.of_forall fun ⟨t, x⟩ => ?_)
    show ‖G t x‖ ≤ Real.exp (-(ε * t ^ 2)) * |F x|
    simp only [hG_def, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |F x| * |Real.cos (t * x)| * |Real.cos (u * t)| * Real.exp (-(ε * t^2))
        ≤ |F x| * 1 * 1 * Real.exp (-(ε * t^2)) := by
          gcongr <;> exact Real.abs_cos_le_one _
      _ = Real.exp (-(ε * t^2)) * |F x| := by ring

  have hmarg_eq : ∀ t, (∫ x, G t x) =
      (∫ x, F x * Real.cos (t * x)) * Real.cos (u * t) * Real.exp (-(ε * t^2)) := by
    intro t; simp only [hG_def]
    rw [show (fun x => F x * Real.cos (t*x) * Real.cos (u*t) * Real.exp (-(ε*t^2)))
        = fun x => (F x * Real.cos (t*x)) * (Real.cos (u*t) * Real.exp (-(ε*t^2)))
        from funext fun x => by ring,
      integral_mul_const]
    ring
  have hconj1 : Integrable (fun t =>
      (∫ x, F x * Real.cos (t * x)) * Real.cos (u * t) * Real.exp (-(ε * t^2))) := by
    have h := hG_int.integral_prod_left
    exact h.congr (Eventually.of_forall hmarg_eq)
  refine ⟨hconj1, ?_⟩

  have hswap : ∫ t, (∫ x, G t x) = ∫ x, (∫ t, G t x) :=
    integral_integral_swap hG_int

  have hinner : ∀ x, ∫ t, G t x
      = F x * (Real.sqrt (Real.pi / ε) / 2
        * (Real.exp (-((x - u)^2 / (4*ε))) + Real.exp (-((x + u)^2 / (4*ε))))) := by
    intro x
    simp only [hG_def]
    rw [show (fun t => F x * Real.cos (t*x) * Real.cos (u*t) * Real.exp (-(ε*t^2)))
        = fun t => F x * (Real.cos (t*x) * Real.cos (u*t) * Real.exp (-(ε*t^2)))
        from funext fun t => by ring,
      integral_const_mul]
    congr 1

    have hpts : ∀ t, Real.cos (t*x) * Real.cos (u*t)
        = (Real.cos ((x-u)*t) + Real.cos ((x+u)*t)) / 2 := by
      intro t
      have h := Real.two_mul_cos_mul_cos (t*x) (u*t)
      have heq : Real.cos (t*x - u*t) = Real.cos ((x-u)*t) := by ring_nf
      have heq2 : Real.cos (t*x + u*t) = Real.cos ((x+u)*t) := by ring_nf
      rw [heq, heq2] at h; linarith
    rw [show (fun t => Real.cos (t*x) * Real.cos (u*t) * Real.exp (-(ε*t^2)))
        = fun t => (Real.exp (-(ε*t^2)) * Real.cos ((x-u)*t)
            + Real.exp (-(ε*t^2)) * Real.cos ((x+u)*t)) / 2
        from funext fun t => by rw [hpts t]; ring,
      integral_div,
      integral_add ?_ ?_]
    · rw [gapsw80_t61_integral_gaussian_cos hε (x-u),
        gapsw80_t61_integral_gaussian_cos hε (x+u)]
      ring

    all_goals
      refine (integrable_exp_neg_mul_sq hε).mono' ?_ ?_
      · apply Continuous.aestronglyMeasurable
        exact (Real.continuous_exp.comp (continuous_const.mul
          (continuous_pow 2)).neg).mul (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))
      · filter_upwards with t
        simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
        calc Real.exp (-(ε*t^2)) * |Real.cos (_*t)|
            ≤ Real.exp (-(ε*t^2)) * 1 := by gcongr; exact Real.abs_cos_le_one _
          _ = Real.exp (-(ε*t^2)) := mul_one _

  calc ∫ t, (∫ x, F x * Real.cos (t*x)) * Real.cos (u*t) * Real.exp (-(ε*t^2))
      = ∫ t, (∫ x, G t x) := by
        congr 1; funext t; exact (hmarg_eq t).symm
    _ = ∫ x, (∫ t, G t x) := hswap
    _ = ∫ x, F x * (Real.sqrt (Real.pi / ε) / 2
        * (Real.exp (-((x - u)^2 / (4*ε))) + Real.exp (-((x + u)^2 / (4*ε))))) := by
        congr 1; funext x; exact hinner x
    _ = Real.sqrt (Real.pi / ε) * ∫ x, F x * Real.exp (-((x - u)^2 / (4*ε))) := by

        have hint1 : Integrable (fun x => F x * Real.exp (-((x - u)^2 / (4*ε)))) :=
          hFint.abs.mono' (hdiff.continuous.mul (Real.continuous_exp.comp
            (((continuous_id.sub continuous_const).pow 2).div_const
            (4*ε)).neg)).aestronglyMeasurable
            (Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
              calc |F x| * Real.exp (-((x - u)^2 / (4*ε))) ≤ |F x| * 1 := by
                    gcongr
                    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
                _ = |F x| := mul_one _)
        have hint2 : Integrable (fun x => F x * Real.exp (-((x + u)^2 / (4*ε)))) :=
          hFint.abs.mono' (hdiff.continuous.mul (Real.continuous_exp.comp
            (((continuous_id.add continuous_const).pow 2).div_const
            (4*ε)).neg)).aestronglyMeasurable
            (Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
              calc |F x| * Real.exp (-((x + u)^2 / (4*ε))) ≤ |F x| * 1 := by
                    gcongr
                    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
                _ = |F x| := mul_one _)

        have h2nd : ∫ x, F x * Real.exp (-((x + u)^2 / (4*ε)))
            = ∫ x, F x * Real.exp (-((x - u)^2 / (4*ε))) := by
          rw [← integral_neg_eq_self (fun x => F x * Real.exp (-((x - u)^2 / (4*ε))))]
          congr 1; funext x
          rw [heven x]; congr 2; ring
        rw [show (fun x => F x * (Real.sqrt (Real.pi / ε) / 2
              * (Real.exp (-((x - u)^2 / (4*ε))) + Real.exp (-((x + u)^2 / (4*ε))))))
            = fun x => Real.sqrt (Real.pi / ε) / 2
              * (F x * Real.exp (-((x - u)^2 / (4*ε)))
                + F x * Real.exp (-((x + u)^2 / (4*ε)))) from funext fun x => by ring,
          integral_const_mul, integral_add hint1 hint2, h2nd]
        ring

set_option maxHeartbeats 12800000 in

theorem gapsw80_t64_heatkernel_limit {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) (u : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (Real.pi / (1 / (n + 1 : ℝ)))
        * ∫ x : ℝ, F x * Real.exp (-((x - u) ^ 2 / (4 * (1 / (n + 1 : ℝ))))))
      atTop (𝓝 (2 * Real.pi * F u)) := by
  have _em := Classical.em
  have hdiff := hF.1
  obtain ⟨c, δ, hc, hδ, hdecay⟩ := hF.2.2.2.2.1
  have hFbd : ∀ x, |F x| ≤ c := fun x => (hdecay x).trans (by
    calc c * Real.exp (-(1/2+δ) * |x|) ≤ c * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
            (by linarith) (abs_nonneg _))
      _ = c := mul_one _)

  have hcv : ∀ n : ℕ, Real.sqrt (Real.pi / (1 / (n + 1 : ℝ)))
        * ∫ x, F x * Real.exp (-((x - u) ^ 2 / (4 * (1 / (n + 1 : ℝ)))))
      = 2 * Real.sqrt Real.pi
        * ∫ v : ℝ, F (u + 2 / Real.sqrt (n + 1 : ℝ) * v) * Real.exp (-v ^ 2) := by
    intro n
    have hn1 : (0:ℝ) < n + 1 := by positivity
    have hsn : (0:ℝ) < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr hn1
    set a : ℝ := 2 / Real.sqrt (n + 1 : ℝ) with ha_def
    have ha : (0:ℝ) < a := by rw [ha_def]; positivity

    have hshift : ∫ x, F x * Real.exp (-((x - u) ^ 2 / (4 * (1 / (n + 1 : ℝ)))))
        = ∫ y, F (y + u) * Real.exp (-(y ^ 2 * (n + 1 : ℝ) / 4)) := by
      rw [← integral_add_right_eq_self
        (fun x => F x * Real.exp (-((x - u) ^ 2 / (4 * (1 / (n + 1 : ℝ)))))) u]
      congr 1; funext y
      congr 2; field_simp; ring

    have hscale : ∫ y, F (y + u) * Real.exp (-(y ^ 2 * (n + 1 : ℝ) / 4))
        = a * ∫ v, F (u + a * v) * Real.exp (-v ^ 2) := by
      have h := MeasureTheory.Measure.integral_comp_mul_left
        (fun y => F (y + u) * Real.exp (-(y ^ 2 * (n + 1 : ℝ) / 4))) a
      rw [abs_of_pos (inv_pos.mpr ha), smul_eq_mul] at h
      have heq : (fun v : ℝ => F (a * v + u) * Real.exp (-((a * v) ^ 2 * (n + 1 : ℝ) / 4)))
          = fun v => F (u + a * v) * Real.exp (-v ^ 2) := by
        funext v
        rw [show a * v + u = u + a * v from by ring]
        congr 2
        rw [ha_def, mul_pow, div_pow, Real.sq_sqrt hn1.le]
        field_simp; ring
      rw [heq, eq_inv_mul_iff_mul_eq₀ ha.ne'] at h
      exact h.symm
    rw [hshift, hscale, ha_def]
    have hπε : Real.sqrt (Real.pi / (1 / (↑n + 1)))
        = Real.sqrt Real.pi * Real.sqrt (n + 1 : ℝ) := by
      rw [div_div_eq_mul_div, div_one, Real.sqrt_mul Real.pi_pos.le]
    rw [hπε, ← mul_assoc,
      show Real.sqrt Real.pi * Real.sqrt (↑n + 1) * (2 / Real.sqrt (↑n + 1))
        = 2 * Real.sqrt Real.pi from by field_simp]

  have hdct : Tendsto (fun n : ℕ =>
      ∫ v : ℝ, F (u + 2 / Real.sqrt (n + 1 : ℝ) * v) * Real.exp (-v ^ 2))
      atTop (𝓝 (F u * Real.sqrt Real.pi)) := by
    have hgauss : Integrable (fun v : ℝ => c * Real.exp (-v ^ 2)) :=
      ((integrable_exp_neg_mul_sq (b := 1) one_pos).congr
        (Eventually.of_forall fun v => by ring_nf)).const_mul c
    have hlim : F u * Real.sqrt Real.pi = ∫ v : ℝ, F u * Real.exp (-v ^ 2) := by
      rw [integral_const_mul]
      congr 1
      have h := integral_gaussian (1 : ℝ)
      rw [div_one] at h
      rw [← h]
      congr 1; funext v; ring_nf
    rw [hlim]
    apply tendsto_integral_of_dominated_convergence (bound := fun v => c * Real.exp (-v ^ 2))
    · intro n
      exact ((hdiff.continuous.comp (continuous_const.add
        (continuous_const.mul continuous_id))).mul
        (Real.continuous_exp.comp (continuous_pow 2).neg)).aestronglyMeasurable
    · exact hgauss
    · intro n
      filter_upwards with v
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hFbd _) (Real.exp_pos _).le
    · filter_upwards with v
      have hsto : Tendsto (fun n : ℕ => u + 2 / Real.sqrt (n + 1 : ℝ) * v)
          atTop (𝓝 u) := by
        have h1 : Tendsto (fun n : ℕ => (2:ℝ) / Real.sqrt (n + 1 : ℝ))
            atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          exact (tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add
            tendsto_const_nhds))
        have := (h1.mul_const v).const_add u
        simpa using this
      exact ((hdiff.continuous.tendsto u).comp hsto).mul tendsto_const_nhds

  have hpi_eq : (2 * Real.pi * F u : ℝ)
      = 2 * Real.sqrt Real.pi * (F u * Real.sqrt Real.pi) := by
    conv_lhs => rw [← Real.sq_sqrt Real.pi_pos.le]
    ring
  rw [hpi_eq]
  exact (tendsto_congr hcv).mpr (hdct.const_mul (2 * Real.sqrt Real.pi))

set_option maxHeartbeats 12800000 in

theorem gapsw80_t64_integrable_Fhat {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) :
    Integrable (fun t => ∫ x : ℝ, F x * Real.cos (t * x))
    ∧ ∫ t : ℝ, (∫ x : ℝ, F x * Real.cos (t * x)) = 2 * Real.pi := by
  have _em := Classical.em
  have hFh_nn := hF.2.2.2.2.2
  set Fh : ℝ → ℝ := fun t => ∫ x : ℝ, F x * Real.cos (t * x) with hFh_def
  have hFh_cont : Continuous Fh := gapsw80_t64_continuous_Fhat hF

  set g : ℕ → ℝ → ℝ := fun n t => Fh t * Real.exp (-(1 / (n + 1 : ℝ) * t ^ 2)) with hg_def
  have hg_nn : ∀ n t, 0 ≤ g n t := fun n t =>
    mul_nonneg (hFh_nn t) (Real.exp_pos _).le
  have hg_meas : ∀ n, AEStronglyMeasurable (g n) volume := fun n =>
    (hFh_cont.mul (Real.continuous_exp.comp (continuous_const.mul
      (continuous_pow 2)).neg)).aestronglyMeasurable
  have hg_int : ∀ n, Integrable (g n) := by
    intro n
    have h := (gapsw80_t64_mollified_identity hF
      (show (0:ℝ) < 1/(n+1:ℝ) from by positivity) 0).1
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [hg_def, hFh_def, zero_mul, Real.cos_zero, mul_one]
  have hg_mono : ∀ t, Monotone (fun n => g n t) := by
    intro t i j hij
    simp only [hg_def]
    apply mul_le_mul_of_nonneg_left _ (hFh_nn t)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
    apply div_le_div_of_nonneg_left one_pos.le (by positivity)
    exact_mod_cast Nat.succ_le_succ hij
  have hg_tend : ∀ t, Tendsto (fun n => g n t) atTop (𝓝 (Fh t)) := by
    intro t
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(1/(n+1:ℝ) * t^2)))
        atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => -(1/(n+1:ℝ) * t^2)) atTop (𝓝 0) := by
        rw [show (0:ℝ) = -(0 * t^2) from by ring]
        exact (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (t^2)).neg
      have := (Real.continuous_exp.tendsto 0).comp h0
      simp at this ⊢
      exact this
    have h := tendsto_const_nhds (x := Fh t) (f := atTop) |>.mul hexp
    simpa [hg_def] using h

  have hintg_lim : Tendsto (fun n => ∫ t, g n t) atTop (𝓝 (2 * Real.pi)) := by
    have hrw : ∀ n, ∫ t, g n t
        = Real.sqrt (Real.pi / (1/(n+1:ℝ)))
          * ∫ x, F x * Real.exp (-((x - 0)^2 / (4 * (1/(n+1:ℝ))))) := by
      intro n
      have h := (gapsw80_t64_mollified_identity hF
        (show (0:ℝ) < 1/(n+1:ℝ) from by positivity) 0).2
      rw [← h]
      simp only [hg_def, hFh_def, zero_mul, Real.cos_zero, mul_one]
    rw [show (2 * Real.pi : ℝ) = 2 * Real.pi * F 0 from by rw [hF.2.2.1, mul_one]]
    exact (tendsto_congr hrw).mpr (gapsw80_t64_heatkernel_limit hF 0)

  have hlint_g : ∀ n, ∫⁻ t, ENNReal.ofReal (g n t)
      = ENNReal.ofReal (∫ t, g n t) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hg_int n)
      (Eventually.of_forall (hg_nn n))).symm
  have hlint_tend : Tendsto (fun n => ∫⁻ t, ENNReal.ofReal (g n t))
      atTop (𝓝 (∫⁻ t, ENNReal.ofReal (Fh t))) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · exact fun n => ((hg_meas n).aemeasurable).ennreal_ofReal
    · exact Eventually.of_forall fun t => fun i j hij =>
        ENNReal.ofReal_le_ofReal (hg_mono t hij)
    · exact Eventually.of_forall fun t =>
        (ENNReal.continuous_ofReal.tendsto (Fh t)).comp (hg_tend t)
  have hlint_Fh : ∫⁻ t, ENNReal.ofReal (Fh t) = ENNReal.ofReal (2 * Real.pi) := by
    have h1 : Tendsto (fun n => ∫⁻ t, ENNReal.ofReal (g n t))
        atTop (𝓝 (ENNReal.ofReal (2 * Real.pi))) := by
      simp only [hlint_g]
      exact (ENNReal.continuous_ofReal.tendsto (2 * Real.pi)).comp hintg_lim
    exact tendsto_nhds_unique hlint_tend h1

  have hFh_int : Integrable Fh := by
    refine ⟨hFh_cont.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, show (fun a => ‖Fh a‖ₑ) = fun a => ENNReal.ofReal (Fh a) from
      funext fun t => by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (hFh_nn t)],
      hlint_Fh]
    exact ENNReal.ofReal_lt_top
  refine ⟨hFh_int, ?_⟩
  rw [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hFh_nn) (by positivity),
    ofReal_integral_eq_lintegral_ofReal hFh_int (Eventually.of_forall hFh_nn), hlint_Fh]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t64_cosine_inversion {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) (u : ℝ) :
    ∫ t : ℝ, (∫ x : ℝ, F x * Real.cos (t * x)) * Real.cos (u * t)
      = 2 * Real.pi * F u := by
  have _em := Classical.em
  have hFh_nn := hF.2.2.2.2.2
  have ⟨hFh_int, _⟩ := gapsw80_t64_integrable_Fhat hF
  set Fh : ℝ → ℝ := fun t => ∫ x : ℝ, F x * Real.cos (t * x) with hFh_def

  have hLHS : Tendsto (fun n : ℕ =>
      ∫ t, Fh t * Real.cos (u * t) * Real.exp (-(1/(n+1:ℝ) * t^2)))
      atTop (𝓝 (∫ t, Fh t * Real.cos (u * t))) := by
    apply tendsto_integral_of_dominated_convergence (bound := Fh)
    · intro n
      exact ((gapsw80_t64_continuous_Fhat hF).mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_pow 2)).neg) |>.aestronglyMeasurable
    · exact hFh_int
    · intro n
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hFh_nn t),
        abs_of_pos (Real.exp_pos _)]
      have hc1 : |Real.cos (u*t)| ≤ 1 := Real.abs_cos_le_one _
      have he1 : Real.exp (-(1/(n+1:ℝ) * t^2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      nlinarith [hFh_nn t, mul_nonneg (hFh_nn t) (abs_nonneg (Real.cos (u*t)))]
    · filter_upwards with t
      have h0 : Tendsto (fun n : ℕ => -((1:ℝ)/(n+1:ℝ) * t^2)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (t^2)).neg
        simpa using this
      have hexp : Tendsto (fun n : ℕ => Real.exp (-(1/(n+1:ℝ) * t^2)))
          atTop (𝓝 1) := by
        have := (Real.continuous_exp.tendsto 0).comp h0
        simp at this ⊢
        exact this
      have := tendsto_const_nhds (x := Fh t * Real.cos (u*t)) (f := atTop) |>.mul hexp
      simpa using this

  have hRHS : Tendsto (fun n : ℕ =>
      ∫ t, Fh t * Real.cos (u * t) * Real.exp (-(1/(n+1:ℝ) * t^2)))
      atTop (𝓝 (2 * Real.pi * F u)) := by
    have hrw : ∀ n : ℕ, ∫ t, Fh t * Real.cos (u * t) * Real.exp (-(1/(n+1:ℝ) * t^2))
        = Real.sqrt (Real.pi / (1/(n+1:ℝ)))
          * ∫ x, F x * Real.exp (-((x - u)^2 / (4 * (1/(n+1:ℝ))))) := fun n =>
      (gapsw80_t64_mollified_identity hF (show (0:ℝ) < 1/(n+1:ℝ) from by positivity) u).2
    exact (tendsto_congr hrw).mpr (gapsw80_t64_heatkernel_limit hF u)
  exact tendsto_nhds_unique hLHS hRHS

set_option maxHeartbeats 3200000 in

theorem gapsw80_t64_D2f_proved : gapsw80_t63_CosineInversionAdmissible := by
  have _em := Classical.em
  intro F hF
  exact ⟨(gapsw80_t64_integrable_Fhat hF).1, gapsw80_t64_cosine_inversion hF⟩

end FLT.Gapsw80T64D2fGaussianMollificationProof
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T67D2bpPrimeSumFalseprobeRemint

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
open FLT.Gapsw80T24StripMigrationChainStart
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T60D2cArchGammaKernelSubDecomp
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T63CosineInversionWire
open FLT.Gapsw80T64D2fGaussianMollificationProof
open FLT.Gapsw80T66D2caiDigammaSeriesProof
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t67_D2cp_closed :
    gapsw80_t62_ArchGammaKernelIdentityCorrected :=
  gapsw80_t62_D2cp_of_D2ca_D2cbp gapsw80_t66_D2ca_proved
    (gapsw80_t63_D2cbp_of_D2f gapsw80_t64_D2f_proved)

end FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T68D2bppExplicitFormulaSubDecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T20LambdaLogDerivProductRule
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T27D2d0EulerProductAncestor
open FLT.Gapsw80T28D2d0aSummabilityProof
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T64D2fGaussianMollificationProof
open FLT.Gapsw80T65D2caDigammaSeriesSubDecomp
open FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory"
p2m_open_scoped "Real P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Real"

private theorem gapsw80_t68_laplace_cos {a : ℝ} (ha : 0 < a) (t : ℝ) :
    IntegrableOn (fun x => Real.exp (-(a * x)) * Real.cos (t * x)) (Set.Ioi (0:ℝ))
    ∧ ∫ x in Set.Ioi (0:ℝ), Real.exp (-(a * x)) * Real.cos (t * x)
        = a / (a ^ 2 + t ^ 2) := by
  have _em := Classical.em

  have hexp_int : IntegrableOn (fun x => Real.exp (-(a * x))) (Set.Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
    simpa only [neg_mul] using this
  have hcos_int : IntegrableOn
      (fun x => Real.exp (-(a * x)) * Real.cos (t * x)) (Set.Ioi (0:ℝ)) := by
    apply hexp_int.mono'
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
      calc Real.exp (-(a * x)) * |Real.cos (t * x)|
          ≤ Real.exp (-(a * x)) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
        _ = Real.exp (-(a * x)) := mul_one _
  refine ⟨hcos_int, ?_⟩
  have h1c := (gapsw80_t65_integral_exp_neg_one_sub_cos ha t).2
  have hI1 : ∫ x in Set.Ioi (0:ℝ), Real.exp (-(a * x)) = 1 / a := by
    have := integral_exp_mul_Ioi (a := -a) (by linarith) 0
    simp only [neg_mul, mul_zero, Real.exp_zero, neg_neg] at this
    rw [this]; ring
  have hsub : ∫ x in Set.Ioi (0:ℝ), Real.exp (-(a * x)) * Real.cos (t * x)
      = (∫ x in Set.Ioi (0:ℝ), Real.exp (-(a * x)))
        - ∫ x in Set.Ioi (0:ℝ), Real.exp (-(a * x)) * (1 - Real.cos (t * x)) := by
    rw [← MeasureTheory.integral_sub hexp_int
      (gapsw80_t65_integral_exp_neg_one_sub_cos ha t).1]
    congr 1; ext x; ring
  rw [hsub, hI1, h1c]; ring

private theorem gapsw80_t68_poisson_Fhat {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) {a : ℝ} (ha : 0 < a) :
    Integrable (fun t => (a / (a ^ 2 + t ^ 2)) * (∫ x : ℝ, F x * Real.cos (t * x)))
    ∧ (1 / Real.pi) * ∫ t : ℝ, (a / (a ^ 2 + t ^ 2))
          * (∫ x : ℝ, F x * Real.cos (t * x))
        = 2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(a * x)) := by
  have _em := Classical.em
  have ⟨hFh_int, _⟩ := gapsw80_t64_integrable_Fhat hF
  have hFh_nn : ∀ t, 0 ≤ ∫ x : ℝ, F x * Real.cos (t * x) := hF.2.2.2.2.2

  have hint : Integrable (fun t => (a / (a ^ 2 + t ^ 2))
      * (∫ x : ℝ, F x * Real.cos (t * x))) := by
    have hbd : ∀ t : ℝ, a / (a^2+t^2) ≤ 1/a := fun t => by
      have hden : (0:ℝ) < a^2+t^2 := by positivity
      rw [div_le_div_iff₀ hden ha]; nlinarith [sq_nonneg t]
    apply Integrable.mono' (hFh_int.const_mul (1/a))
    · exact ((continuous_const.div (by continuity)
        (fun t => by positivity)).mul (gapsw80_t64_continuous_Fhat hF))
        |>.aestronglyMeasurable
    · filter_upwards with t
      simp only [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hFh_nn t),
        abs_of_nonneg (show (0:ℝ) ≤ a/(a^2+t^2) from by positivity),
        abs_of_nonneg (show (0:ℝ) ≤ 1/a from by positivity)]
      exact mul_le_mul_of_nonneg_right (hbd t) (hFh_nn t)
  refine ⟨hint, ?_⟩

  set Fh : ℝ → ℝ := fun t => ∫ x : ℝ, F x * Real.cos (t * x)
  have hexp_int : IntegrableOn (fun x => Real.exp (-(a * x))) (Set.Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
    simpa only [neg_mul] using this

  have hg_int : Integrable (Function.uncurry
      (fun t x => Real.exp (-(a * x)) * Real.cos (t * x) * Fh t))
      ((volume : Measure ℝ).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    apply (hFh_int.mul_prod hexp_int).mono'
    · exact (((Real.continuous_exp.comp
          (continuous_const.mul continuous_snd).neg).mul
        (Real.continuous_cos.comp (continuous_fst.mul continuous_snd))).mul
        ((gapsw80_t64_continuous_Fhat hF).comp continuous_fst)).aestronglyMeasurable
    · filter_upwards with p
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.exp_pos _).le]
      have hFhp : (0:ℝ) ≤ Fh p.1 := hFh_nn p.1
      calc Real.exp (-(a * p.2)) * |Real.cos (p.1 * p.2)| * |Fh p.1|
          = Real.exp (-(a * p.2)) * |Real.cos (p.1 * p.2)| * Fh p.1 := by
            rw [abs_of_nonneg hFhp]
        _ ≤ Real.exp (-(a * p.2)) * 1 * Fh p.1 := by
            apply mul_le_mul_of_nonneg_right _ hFhp
            exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
        _ = Fh p.1 * Real.exp (-(a * p.2)) := by ring

  have hLHS : ∫ t, (a / (a^2 + t^2)) * Fh t
      = ∫ x in Set.Ioi (0:ℝ), ∫ t, Real.exp (-(a*x)) * Real.cos (t*x) * Fh t := by
    rw [← MeasureTheory.integral_integral_swap hg_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show a / (a^2 + t^2) * Fh t
      = ∫ x in Set.Ioi (0:ℝ), Real.exp (-(a*x)) * Real.cos (t*x) * Fh t
    rw [← (gapsw80_t68_laplace_cos ha t).2, ← integral_mul_const]

  have hinner : ∀ x : ℝ, ∫ t, Real.exp (-(a*x)) * Real.cos (t*x) * Fh t
      = 2 * Real.pi * (F x * Real.exp (-(a*x))) := by
    intro x
    rw [show (fun t => Real.exp (-(a*x)) * Real.cos (t*x) * Fh t)
          = (fun t => Real.exp (-(a*x)) * (Fh t * Real.cos (x*t))) from
            funext fun t => by rw [mul_comm x t]; ring,
        integral_const_mul, gapsw80_t64_cosine_inversion hF x]
    ring
  rw [hLHS]
  simp_rw [hinner]
  rw [integral_const_mul, ← mul_assoc]
  congr 1
  field_simp

private theorem gapsw80_t68_log_discr_re (K : Type) [Field K] [NumberField K] :
    (Complex.log (((|discr K| : ℤ) : ℂ))).re = Real.log |(discr K : ℝ)| := by
  have _em := Classical.em
  have hDR : (0 : ℝ) ≤ ((|discr K| : ℤ) : ℝ) := by
    exact_mod_cast (abs_nonneg (discr K))
  rw [show (((|discr K| : ℤ) : ℂ)) = (((((|discr K| : ℤ) : ℝ)) : ℂ)) from
        (Complex.ofReal_intCast _).symm,
      Complex.log_ofReal_re,
      show ((|discr K| : ℤ) : ℝ) = |(discr K : ℝ)| from by
        rw [Int.cast_abs]]

private noncomputable def gapsw80_t68_primeSumSigma (F : ℝ → ℝ) (K : Type)
    [Field K] [NumberField K] (σ : ℝ) : ℝ :=
  ∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ,
    Real.log (Ideal.absNorm p.1.1 : ℕ)
      * F (((p.2 : ℝ) + 1) * Real.log (Ideal.absNorm p.1.1 : ℕ))
      * ((Ideal.absNorm p.1.1 : ℕ) : ℝ) ^ (-(((p.2 : ℝ) + 1) * σ))

private theorem gapsw80_t68_prime_side_eval {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hd : gapsw80_t21_DedekindZetaEulerExpansion)
    (K : Type) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun t : ℝ => (logDeriv (dedekindZeta K) ((σ : ℂ) + (t : ℂ) * I)).re
        * (∫ x : ℝ, F x * Real.cos (t * x)))
    ∧ (1 / Real.pi) * ∫ t : ℝ,
          (logDeriv (dedekindZeta K) ((σ : ℂ) + (t : ℂ) * I)).re
          * (∫ x : ℝ, F x * Real.cos (t * x))
        = -2 * gapsw80_t68_primeSumSigma F K σ := by
  have _em := Classical.em
  have ⟨hFh_int, hFh_val⟩ := gapsw80_t64_integrable_Fhat hF
  have hFh_nn : ∀ t, 0 ≤ ∫ x : ℝ, F x * Real.cos (t * x) := hF.2.2.2.2.2
  set Fh : ℝ → ℝ := fun t => ∫ x : ℝ, F x * Real.cos (t * x)
  set PP : Type := {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}

  have hs_re : ∀ t : ℝ, 1 < ((σ:ℂ)+(t:ℂ)*I).re := fun t => by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]; exact hσ

  have hNp : ∀ p : PP, 1 < Ideal.absNorm p.1 := gapsw80_t27_one_lt_absNorm_prime
  have hNpR : ∀ p : PP, (1:ℝ) < (Ideal.absNorm p.1 : ℝ) := fun p => by
    exact_mod_cast hNp p
  have hNp0 : ∀ p : PP, 0 < Ideal.absNorm p.1 := fun p => lt_trans one_pos (hNp p)
  have hNpC0 : ∀ p : PP, ((Ideal.absNorm p.1 : ℕ):ℂ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (hNp0 p).ne'
  have hlogNp_nn : ∀ p : PP, 0 ≤ Real.log (Ideal.absNorm p.1 : ℕ) := fun p =>
    Real.log_nonneg (by exact_mod_cast (hNp p).le)

  let vM : PP × ℕ → ℝ := fun q => Real.log (Ideal.absNorm q.1.1 : ℕ)
    * ((Ideal.absNorm q.1.1 : ℕ) : ℝ) ^ (-(((q.2:ℝ)+1)*σ))
  let cterm : ℝ → PP × ℕ → ℂ := fun t q =>
    Complex.log ((Ideal.absNorm q.1.1 : ℕ) : ℂ)
      * ((Ideal.absNorm q.1.1 : ℕ) : ℂ) ^ (-((q.2:ℂ)+1)*((σ:ℂ)+(t:ℂ)*I))
  have hvM_nn : ∀ q, 0 ≤ vM q := fun q =>
    mul_nonneg (hlogNp_nn q.1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

  have hnorm_cterm : ∀ t q, ‖cterm t q‖ = vM q := by
    intro t q
    have hN0 := hNp0 q.1
    show ‖Complex.log ((Ideal.absNorm q.1.1 : ℕ) : ℂ)
        * ((Ideal.absNorm q.1.1 : ℕ) : ℂ) ^ (-((q.2:ℂ)+1)*((σ:ℂ)+(t:ℂ)*I))‖
      = Real.log (Ideal.absNorm q.1.1 : ℕ)
        * ((Ideal.absNorm q.1.1 : ℕ) : ℝ) ^ (-(((q.2:ℝ)+1)*σ))
    rw [norm_mul, ← Complex.natCast_log, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hlogNp_nn q.1),
      Complex.norm_natCast_cpow_of_pos hN0]
    congr 2
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im,
      zero_mul, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add, Complex.natCast_re, Complex.natCast_im,
      Complex.one_re, Complex.one_im, Complex.neg_im, Complex.sub_im, Complex.sub_re,
      _root_.neg_zero]
    push_cast; ring

  have hsum_vM : Summable vM := by
    set σ₀ : ℝ := (1+σ)/2 with hσ₀_def
    set δ : ℝ := (σ-1)/2 with hδ_def
    have hσ₀1 : 1 < σ₀ := by rw [hσ₀_def]; linarith
    have hδpos : 0 < δ := by rw [hδ_def]; linarith
    have hσ₀δ : σ₀ + δ = σ := by rw [hσ₀_def, hδ_def]; ring

    let maj : PP × ℕ → ℝ := fun q =>
      (1/δ) * ((Ideal.absNorm q.1.1 : ℕ):ℝ)^(-σ₀) * (1/2:ℝ)^q.2
    have hmaj_nn : ∀ q, 0 ≤ maj q := fun q => by
      apply mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      positivity
    have hbd : ∀ q, vM q ≤ maj q := by
      intro ⟨p, m⟩
      have hN := hNpR p
      have hN0 : (0:ℝ) < (Ideal.absNorm p.1 : ℕ) := by exact_mod_cast hNp0 p

      have hlog : Real.log (Ideal.absNorm p.1 : ℕ)
          ≤ ((Ideal.absNorm p.1 : ℕ):ℝ)^δ / δ :=
        Real.log_le_rpow_div (Nat.cast_nonneg _) hδpos
      have hsplit : ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(((m:ℝ)+1)*σ))
          = ((Ideal.absNorm p.1 : ℕ):ℝ)^(-σ)
            * ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(m:ℝ)*σ) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      have hgeom : ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(m:ℝ)*σ) ≤ (1/2:ℝ)^m := by
        have h1 : ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(m:ℝ)*σ)
            ≤ ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(m:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN.le
            (by have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m; nlinarith)
        have h2 : ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(m:ℝ)) ≤ (1/2:ℝ)^m := by
          have h2N : (2:ℝ) ≤ ((Ideal.absNorm p.1 : ℕ):ℝ) := by exact_mod_cast hNp p
          have hNm : (2:ℝ)^m ≤ ((Ideal.absNorm p.1 : ℕ):ℝ)^m :=
            pow_le_pow_left₀ zero_le_two h2N m
          calc ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(m:ℝ))
              = (((Ideal.absNorm p.1 : ℕ):ℝ)^m)⁻¹ := by
                rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
            _ ≤ ((2:ℝ)^m)⁻¹ :=
                (inv_le_inv₀ (pow_pos hN0 m) (pow_pos two_pos m)).mpr hNm
            _ = (1/2:ℝ)^m := by rw [one_div, inv_pow]
        linarith
      have heq1 : vM (p, m)
          = Real.log (Ideal.absNorm p.1 : ℕ) *
            (((Ideal.absNorm p.1 : ℕ):ℝ)^(-σ) *
             ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(m:ℝ)*σ)) := by
        show Real.log (Ideal.absNorm p.1 : ℕ)
            * ((Ideal.absNorm p.1 : ℕ):ℝ)^(-(((m:ℝ)+1)*σ)) = _
        rw [hsplit]
      have heq2 : (((Ideal.absNorm p.1 : ℕ):ℝ)^δ / δ) *
            (((Ideal.absNorm p.1 : ℕ):ℝ)^(-σ) * (1/2:ℝ)^m) = maj (p, m) := by
        show _ = (1/δ) * ((Ideal.absNorm p.1 : ℕ):ℝ)^(-σ₀) * (1/2:ℝ)^m
        rw [show (((Ideal.absNorm p.1 : ℕ):ℝ)^δ / δ)
              * (((Ideal.absNorm p.1 : ℕ):ℝ)^(-σ) * (1/2:ℝ)^m)
            = (((Ideal.absNorm p.1 : ℕ):ℝ)^δ * ((Ideal.absNorm p.1 : ℕ):ℝ)^(-σ))
              * (1/2:ℝ)^m * (1/δ) from by ring,
          ← Real.rpow_add hN0,
          show δ + -σ = -σ₀ from by rw [hσ₀_def, hδ_def]; ring]
        ring
      rw [heq1, ← heq2]
      apply mul_le_mul hlog
        (mul_le_mul_of_nonneg_left hgeom
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hδpos.le)
    apply Summable.of_nonneg_of_le hvM_nn hbd

    have hsum_p : Summable (fun p : PP =>
        (1/δ) * ((Ideal.absNorm p.1 : ℕ):ℝ)^(-σ₀)) := by
      have hσ₀re : 1 < ((σ₀:ℂ)).re := hσ₀1
      apply ((gapsw80_t28_summable_norm_absNorm_cpow
        (K := K) (s := (σ₀:ℂ)) hσ₀re).mul_left (1/δ)).congr
      intro p
      rw [Complex.norm_natCast_cpow_of_pos (hNp0 p), Complex.neg_re,
        Complex.ofReal_re]
    have hsum_m : Summable (fun m : ℕ => (1/2:ℝ)^m) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact (hsum_p.mul_of_nonneg hsum_m
        (fun p => by positivity) (fun m => by positivity)).congr
      (fun q => rfl)

  haveI hPPcount : Countable (PP × ℕ) := by
    have hpos : ∀ q, vM q ≠ 0 := fun q => (mul_pos (Real.log_pos (hNpR q.1))
      (Real.rpow_pos_of_pos (by exact_mod_cast hNp0 q.1) _)).ne'
    have := hsum_vM.countable_support
    rw [show Function.support vM = Set.univ from
      Set.eq_univ_of_forall fun q => hpos q] at this
    exact Set.countable_univ_iff.mp this

  have hsum_ct : ∀ t, Summable (cterm t) := fun t =>
    (hsum_vM.congr (fun q => (hnorm_cterm t q).symm)).of_norm

  have hptwise : ∀ t : ℝ, -logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)
      = ∑' q : PP × ℕ, cterm t q := by
    intro t
    rw [(hsum_ct t).tsum_prod]
    exact (hd K ((σ:ℂ)+(t:ℂ)*I) (hs_re t)).2

  have hre_cterm : ∀ (t : ℝ) q, (cterm t q).re = vM q
      * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) := by
    intro t q
    have hN0 := hNp0 q.1
    have hw_re : (-((q.2:ℂ)+1)*((σ:ℂ)+(t:ℂ)*I)).re = -(((q.2:ℝ)+1)*σ) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, zero_mul, sub_zero,
        add_zero, Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, Complex.neg_im, Complex.sub_im,
        Complex.sub_re, _root_.neg_zero]
      push_cast; ring
    have hw_im : (-((q.2:ℂ)+1)*((σ:ℂ)+(t:ℂ)*I)).im = -(((q.2:ℝ)+1)*t) := by
      simp only [Complex.neg_im, Complex.mul_im, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, zero_mul, sub_zero,
        add_zero, Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
        Complex.add_im, Complex.mul_re, mul_one, zero_add, Complex.neg_re, Complex.sub_im,
        Complex.sub_re, _root_.neg_zero]
      push_cast; ring
    show (Complex.log ((Ideal.absNorm q.1.1 : ℕ) : ℂ)
        * ((Ideal.absNorm q.1.1 : ℕ) : ℂ) ^ (-((q.2:ℂ)+1)*((σ:ℂ)+(t:ℂ)*I))).re
      = Real.log (Ideal.absNorm q.1.1 : ℕ)
        * ((Ideal.absNorm q.1.1 : ℕ):ℝ)^(-(((q.2:ℝ)+1)*σ))
        * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t)
    rw [← Complex.natCast_log, Complex.re_ofReal_mul,
      Complex.cpow_def_of_ne_zero (hNpC0 q.1), ← Complex.natCast_log,
      Complex.exp_re,
      show ((Real.log (Ideal.absNorm q.1.1 : ℕ) : ℂ)
            * (-((q.2:ℂ)+1)*((σ:ℂ)+(t:ℂ)*I))).re
          = Real.log (Ideal.absNorm q.1.1 : ℕ) * (-(((q.2:ℝ)+1)*σ)) from by
        rw [Complex.re_ofReal_mul, hw_re],
      show ((Real.log (Ideal.absNorm q.1.1 : ℕ) : ℂ)
            * (-((q.2:ℂ)+1)*((σ:ℂ)+(t:ℂ)*I))).im
          = Real.log (Ideal.absNorm q.1.1 : ℕ) * (-(((q.2:ℝ)+1)*t)) from by
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero, hw_im],
      show Real.exp (Real.log (Ideal.absNorm q.1.1 : ℕ) * (-(((q.2:ℝ)+1)*σ)))
          = ((Ideal.absNorm q.1.1 : ℕ):ℝ)^(-(((q.2:ℝ)+1)*σ)) from by
        rw [Real.rpow_def_of_pos (by exact_mod_cast hN0), mul_comm],
      show Real.cos (Real.log (Ideal.absNorm q.1.1 : ℕ) * (-(((q.2:ℝ)+1)*t)))
          = Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) from by
        rw [show Real.log (Ideal.absNorm q.1.1 : ℕ) * (-(((q.2:ℝ)+1)*t))
            = -((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) from by ring,
          Real.cos_neg]]
    ring

  have hptwise_re : ∀ t : ℝ, (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re
      = -∑' q : PP × ℕ, vM q
          * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) := by
    intro t
    have := congrArg Complex.re (hptwise t)
    rw [Complex.neg_re, Complex.re_tsum (hsum_ct t)] at this
    simp_rw [hre_cterm t] at this
    linarith [this]

  have hcont_re : Continuous (fun t : ℝ =>
      (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re) := by
    have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hζ_an : AnalyticOnNhd ℂ (dedekindZeta K) {s | 1 < s.re} :=
      DifferentiableOn.analyticOnNhd
        (fun s hs => (gapsw80_t20_differentiableAt_dedekindZeta K hs).differentiableWithinAt) hU
    have hld_cont : ContinuousOn (logDeriv (dedekindZeta K)) {s | 1 < s.re} := fun s hs =>
      ((hζ_an.deriv.continuousOn s hs).div (hζ_an.continuousOn s hs) ((hd K s hs).1))
    exact Complex.continuous_re.comp (hld_cont.comp_continuous
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) hs_re)

  have hint : Integrable (fun t : ℝ =>
      (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re * Fh t) := by
    apply (hFh_int.const_mul (∑' q, vM q)).mono'
      (hcont_re.mul (gapsw80_t64_continuous_Fhat hF)).aestronglyMeasurable
    filter_upwards with t
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFh_nn t),
      abs_of_nonneg (tsum_nonneg hvM_nn)]
    apply mul_le_mul_of_nonneg_right _ (hFh_nn t)
    calc |(logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re|
        ≤ ‖logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)‖ := Complex.abs_re_le_norm _
      _ = ‖∑' q : PP × ℕ, cterm t q‖ := by rw [← hptwise t, norm_neg]
      _ ≤ ∑' q, ‖cterm t q‖ := norm_tsum_le_tsum_norm
          (hsum_vM.congr fun q => (hnorm_cterm t q).symm)
      _ = ∑' q, vM q := tsum_congr (hnorm_cterm t)
  refine ⟨hint, ?_⟩

  have hmeas_q : ∀ q : PP × ℕ, Integrable (fun t : ℝ => vM q
      * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) * Fh t) := by
    intro q
    apply (hFh_int.const_mul (vM q)).mono'
      (((continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).mul
        (gapsw80_t64_continuous_Fhat hF)).aestronglyMeasurable)
    filter_upwards with t
    show ‖vM q * Real.cos ((((q.2:ℝ)+1)
        * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) * Fh t‖ ≤ vM q * Fh t
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hFh_nn t),
      abs_of_nonneg (hvM_nn q)]
    calc vM q * |Real.cos ((((q.2:ℝ)+1)
            * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t)| * Fh t
        ≤ vM q * 1 * Fh t :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hvM_nn q)) (hFh_nn t)
      _ = vM q * Fh t := by ring
  have hsum_int_norm : Summable (fun q : PP × ℕ => ∫ t, ‖vM q
      * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) * Fh t‖) := by
    apply (hsum_vM.mul_right (2*Real.pi)).of_nonneg_of_le
      (fun q => integral_nonneg fun t => norm_nonneg _)
    intro q
    calc ∫ t, ‖vM q * Real.cos ((((q.2:ℝ)+1)
              * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) * Fh t‖
        ≤ ∫ t, vM q * Fh t := by
          apply integral_mono (hmeas_q q).norm (hFh_int.const_mul _)
          intro t
          have hFht : (0:ℝ) ≤ Fh t := hFh_nn t
          simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hFht,
            abs_of_nonneg (hvM_nn q)]
          calc vM q * |Real.cos _| * Fh t ≤ vM q * 1 * Fh t :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hvM_nn q)) hFht
            _ = vM q * Fh t := by ring
      _ = vM q * (2*Real.pi) := by rw [integral_const_mul, hFh_val]

  have hval : ∫ t : ℝ, (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re * Fh t
      = -(2*Real.pi) * gapsw80_t68_primeSumSigma F K σ := by
    have hfun_eq : (fun t : ℝ => (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re * Fh t)
        = (fun t => -∑' q : PP × ℕ, vM q
            * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) * Fh t) := by
      funext t; rw [hptwise_re t, neg_mul, ← tsum_mul_right]
    have hswap : ∫ t : ℝ, ∑' q : PP × ℕ, vM q
          * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) * Fh t
        = ∑' q : PP × ℕ, ∫ t : ℝ, vM q
            * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ)) * t) * Fh t :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm hmeas_q hsum_int_norm).symm
    rw [hfun_eq, integral_neg, hswap, neg_mul, neg_inj]
    have hperq : ∀ q : PP × ℕ, ∫ t : ℝ, vM q
          * Real.cos ((((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ))*t) * Fh t
        = (2*Real.pi) * (Real.log (Ideal.absNorm q.1.1 : ℕ)
            * F (((q.2:ℝ)+1) * Real.log (Ideal.absNorm q.1.1 : ℕ))
            * ((Ideal.absNorm q.1.1 : ℕ):ℝ)^(-(((q.2:ℝ)+1)*σ))) := by
      intro q
      rw [show (fun t => vM q * Real.cos ((((q.2:ℝ)+1)
              * Real.log (Ideal.absNorm q.1.1 : ℕ))*t) * Fh t)
            = (fun t => vM q * (Fh t * Real.cos ((((q.2:ℝ)+1)
                * Real.log (Ideal.absNorm q.1.1 : ℕ))*t))) from funext fun t => by ring,
          integral_const_mul,
          gapsw80_t64_cosine_inversion hF (((q.2:ℝ)+1)*Real.log (Ideal.absNorm q.1.1 : ℕ))]
      show Real.log (Ideal.absNorm q.1.1 : ℕ)
          * ((Ideal.absNorm q.1.1 : ℕ):ℝ)^(-(((q.2:ℝ)+1)*σ))
          * (2 * Real.pi * F (((q.2:ℝ)+1)*Real.log (Ideal.absNorm q.1.1 : ℕ))) = _
      ring
    rw [tsum_congr hperq, tsum_mul_left]
    rfl
  rw [hval]; field_simp

private def gapsw80_t68_s1_identity (K : Type) [Field K] [NumberField K]
    (B : ℂ) (ρ : ℕ → ℂ) (F : ℝ → ℝ) (σ : ℝ) : Prop :=
  let Δ : ℝ → ℝ := fun t : ℝ =>
    ((finrank ℚ K : ℝ) / 2) * (logDeriv Gammaℂ ((σ : ℂ) + (t : ℂ) * I)).re
      - (B + ∑' j, (((σ : ℂ) + (t : ℂ) * I - ρ j)⁻¹ + (ρ j)⁻¹)).re
  Integrable (fun t : ℝ => Δ t * (∫ x : ℝ, F x * Real.cos (t * x)))
  ∧ (1 / Real.pi) * ∫ t : ℝ, Δ t * (∫ x : ℝ, F x * Real.cos (t * x))
      = - Real.log |(discr K : ℝ)|
        - ((2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(σ * x)))
           + (2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((σ - 1) * x))))
        + 2 * gapsw80_t68_primeSumSigma F K σ

set_option maxHeartbeats 12800000 in

theorem gapsw80_t68_ReIntegratedIdentityAtSigma
    (hd : gapsw80_t21_DedekindZetaEulerExpansion)
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (B : ℂ) (ρ : ℕ → ℂ)
    (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    (hexp : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
      logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
        = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
    (F : ℝ → ℝ) (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    {σ : ℝ} (hσ : 1 < σ) :
    gapsw80_t68_s1_identity K B ρ F σ := by
  have _em := Classical.em
  have ⟨hFh_int, hFh_val⟩ := gapsw80_t64_integrable_Fhat hF
  have hFh_nn : ∀ t, 0 ≤ ∫ x : ℝ, F x * Real.cos (t * x) := hF.2.2.2.2.2
  set Fh : ℝ → ℝ := fun t => ∫ x : ℝ, F x * Real.cos (t * x)
  have hσ0 : (0:ℝ) < σ := lt_trans one_pos hσ
  have hσ1 : (0:ℝ) < σ - 1 := sub_pos.mpr hσ

  have hs_re : ∀ t : ℝ, 1 < ((σ:ℂ)+(t:ℂ)*I).re := fun t => by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]; exact hσ
  have hne0 : ∀ t : ℝ, (σ:ℂ)+(t:ℂ)*I ≠ 0 := fun t h => by
    have := (hs_re t); rw [h, Complex.zero_re] at this; linarith
  have hne1 : ∀ t : ℝ, (σ:ℂ)+(t:ℂ)*I ≠ 1 := fun t h => by
    have := (hs_re t); rw [h, Complex.one_re] at this; linarith
  have hneρ : ∀ (t : ℝ) j, (σ:ℂ)+(t:ℂ)*I ≠ ρ j := fun t j h => by
    have h1 := (hstrip j).2
    rw [← h] at h1; exact absurd (hs_re t) (not_lt.mpr h1.le)
  have hζ : ∀ t : ℝ, dedekindZeta K ((σ:ℂ)+(t:ℂ)*I) ≠ 0 := fun t =>
    (hd K ((σ:ℂ)+(t:ℂ)*I) (hs_re t)).1

  have hr₂ : (nrComplexPlaces K : ℝ) = (finrank ℚ K : ℝ) / 2 := by
    have h2 := card_add_two_mul_card_eq_rank K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero (K := K), zero_add] at h2
    have : (2:ℝ) * (nrComplexPlaces K : ℝ) = (finrank ℚ K : ℝ) := by
      exact_mod_cast h2
    linarith

  have hΔ_pt : ∀ t : ℝ,
      ((finrank ℚ K:ℝ)/2) * (logDeriv Gammaℂ ((σ:ℂ)+(t:ℂ)*I)).re
        - (B + ∑' j, (((σ:ℂ)+(t:ℂ)*I - ρ j)⁻¹ + (ρ j)⁻¹)).re
      = -(σ/(σ^2+t^2)) - ((σ-1)/((σ-1)^2+t^2))
        - (1/2) * Real.log |(discr K : ℝ)|
        - (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re := by
    intro t
    set s : ℂ := (σ:ℂ)+(t:ℂ)*I with hs_def
    have hT20 := gapsw80_t21_sat_logDeriv_polyLambda_totallyComplex K (hs_re t) (hζ t)
    rw [← hs_def] at hT20
    have hhexp := hexp s (hne0 t) (hne1 t) (hneρ t)

    have hℂeq : (nrComplexPlaces K : ℂ) * logDeriv Gammaℂ s
          - (B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
        = -(s⁻¹ + (s-1)⁻¹ + Complex.log (((|discr K|:ℤ):ℂ)) / 2
            + logDeriv (dedekindZeta K) s) := by
      have := hT20.symm.trans hhexp
      linear_combination this

    have hre_sinv : (s⁻¹).re = σ / (σ^2+t^2) := by
      rw [hs_def, Complex.inv_re]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, _root_.neg_zero, add_zero, Complex.normSq_add_mul_I]
    have hre_s1inv : ((s-1)⁻¹).re = (σ-1) / ((σ-1)^2+t^2) := by
      rw [hs_def, show (σ:ℂ)+(t:ℂ)*I-1 = ((σ-1:ℝ):ℂ)+(t:ℂ)*I from by push_cast; ring,
        Complex.inv_re]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, _root_.neg_zero, add_zero, Complex.normSq_add_mul_I]
    have hre_logD : (Complex.log (((|discr K|:ℤ):ℂ)) / 2).re
        = (1/2) * Real.log |(discr K:ℝ)| := by
      rw [Complex.div_ofNat_re, gapsw80_t68_log_discr_re K]; ring

    have h := congrArg Complex.re hℂeq
    rw [Complex.sub_re, Complex.neg_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero, hre_sinv, hre_s1inv, hre_logD] at h
    rw [← hr₂, hs_def, Complex.add_re]
    linarith [h]

  have hint_σ' : Integrable (fun t : ℝ => σ/(σ^2+t^2) * Fh t) :=
    (gapsw80_t68_poisson_Fhat hF hσ0).1
  have hval_σ' : (1:ℝ)/Real.pi * ∫ t : ℝ, σ/(σ^2+t^2)*Fh t
      = 2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(σ*x)) :=
    (gapsw80_t68_poisson_Fhat hF hσ0).2
  have hint_σ1' : Integrable (fun t : ℝ => (σ-1)/((σ-1)^2+t^2) * Fh t) :=
    (gapsw80_t68_poisson_Fhat hF hσ1).1
  have hval_σ1' : (1:ℝ)/Real.pi * ∫ t : ℝ, (σ-1)/((σ-1)^2+t^2)*Fh t
      = 2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((σ-1)*x)) :=
    (gapsw80_t68_poisson_Fhat hF hσ1).2
  have hint_ζ' : Integrable (fun t : ℝ =>
      (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re * Fh t) :=
    (gapsw80_t68_prime_side_eval hF hd K hσ).1
  have hval_ζ' : (1:ℝ)/Real.pi
        * ∫ t : ℝ, (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re*Fh t
      = -2 * gapsw80_t68_primeSumSigma F K σ :=
    (gapsw80_t68_prime_side_eval hF hd K hσ).2
  have hint_D : Integrable (fun t : ℝ => (1/2) * Real.log |(discr K:ℝ)| * Fh t) :=
    hFh_int.const_mul _

  have hΔFh_eq : (fun t : ℝ =>
        (((finrank ℚ K:ℝ)/2) * (logDeriv Gammaℂ ((σ:ℂ)+(t:ℂ)*I)).re
          - (B + ∑' j, (((σ:ℂ)+(t:ℂ)*I - ρ j)⁻¹ + (ρ j)⁻¹)).re) * Fh t)
      = (fun t : ℝ => -(σ/(σ^2+t^2) * Fh t + (σ-1)/((σ-1)^2+t^2) * Fh t
          + (1/2)*Real.log |(discr K:ℝ)| * Fh t
          + (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re * Fh t)) :=
    funext fun t => by rw [hΔ_pt t]; ring
  have hint_AB : Integrable (fun t : ℝ => σ/(σ^2+t^2) * Fh t
      + (σ-1)/((σ-1)^2+t^2) * Fh t) := hint_σ'.add hint_σ1'
  have hint_ABC : Integrable (fun t : ℝ => σ/(σ^2+t^2) * Fh t
      + (σ-1)/((σ-1)^2+t^2) * Fh t
      + (1/2)*Real.log |(discr K:ℝ)| * Fh t) := hint_AB.add hint_D
  have hint_4 : Integrable (fun t : ℝ => σ/(σ^2+t^2) * Fh t
      + (σ-1)/((σ-1)^2+t^2) * Fh t
      + (1/2)*Real.log |(discr K:ℝ)| * Fh t
      + (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re * Fh t) :=
    hint_ABC.add hint_ζ'
  have hint_Δ : Integrable (fun t : ℝ =>
      (((finrank ℚ K:ℝ)/2) * (logDeriv Gammaℂ ((σ:ℂ)+(t:ℂ)*I)).re
        - (B + ∑' j, (((σ:ℂ)+(t:ℂ)*I - ρ j)⁻¹ + (ρ j)⁻¹)).re) * Fh t) := by
    rw [hΔFh_eq]; exact hint_4.neg
  refine ⟨?_, ?_⟩
  · exact hint_Δ

  have hI_Δ : ∫ t : ℝ, (((finrank ℚ K:ℝ)/2) * (logDeriv Gammaℂ ((σ:ℂ)+(t:ℂ)*I)).re
        - (B + ∑' j, (((σ:ℂ)+(t:ℂ)*I - ρ j)⁻¹ + (ρ j)⁻¹)).re) * Fh t
      = -((∫ t : ℝ, σ/(σ^2+t^2)*Fh t) + (∫ t : ℝ, (σ-1)/((σ-1)^2+t^2)*Fh t)
        + ((1/2)*Real.log |(discr K:ℝ)| * ∫ t : ℝ, Fh t)
        + ∫ t : ℝ, (logDeriv (dedekindZeta K) ((σ:ℂ)+(t:ℂ)*I)).re * Fh t) := by
    rw [hΔFh_eq, integral_neg, neg_inj,
      MeasureTheory.integral_add hint_ABC hint_ζ',
      MeasureTheory.integral_add hint_AB hint_D,
      MeasureTheory.integral_add hint_σ' hint_σ1',
      integral_const_mul]
  have hFh_val' : ∫ t : ℝ, Fh t = 2 * Real.pi := hFh_val
  have hπ : (1:ℝ)/Real.pi * ((1/2) * Real.log |(discr K:ℝ)| * (2*Real.pi))
      = Real.log |(discr K:ℝ)| := by field_simp
  dsimp only
  rw [hI_Δ, hFh_val', mul_neg, mul_add, mul_add, mul_add,
    hval_σ', hval_σ1', hval_ζ', hπ]
  ring

end FLT.Gapsw80T68D2bppExplicitFormulaSubDecomp
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T70D2bpppZeroSideEvalSubDecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
open FLT.Gapsw80T24StripMigrationChainStart
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T64D2fGaussianMollificationProof
open FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint
open FLT.Gapsw80T68D2bppExplicitFormulaSubDecomp
open FLT.Gapsw80T69AdmC2RemintZktSummable
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory"
p2m_open_scoped "Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology"

section Aux
variable {K : Type} [Field K] [NumberField K]

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t70_hexp_FE_neg {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) (1 - s)
      = -logDeriv
          (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s := by
  have _em := Classical.em
  set Ξ : ℂ → ℂ := fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z
    with hΞ_def
  have hΞFE : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → Ξ (1 - z) = Ξ z := by
    intro z hz0 hz1
    simp only [hΞ_def]
    rw [gapsw80_t9_completedDedekindZeta_FE K hz0 hz1]; ring
  have hΞdiff : ∀ z ∈ ({(0:ℂ), 1}ᶜ : Set ℂ), DifferentiableAt ℂ Ξ z := by
    intro z hz
    exact (differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (gapsw80_t9_analyticOnNhd_completedDedekindZeta K z hz).differentiableAt
  have hsU : s ∈ ({(0:ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs0, hs1⟩
  have h1sU : (1 - s) ∈ ({(0:ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
      sub_eq_zero, sub_eq_self]
    exact ⟨fun h => hs1 h.symm, hs0⟩
  have hopen : IsOpen ({(0:ℂ), 1}ᶜ : Set ℂ) := (gapsw80_t9_isClosed_pair).isOpen_compl
  have heq : (fun z => Ξ (1 - z)) =ᶠ[𝓝 s] Ξ :=
    Filter.eventually_of_mem (hopen.mem_nhds hsU) fun z hz => by
      have hz' : z ≠ 0 ∧ z ≠ 1 := by
        simpa [Set.mem_compl_iff, Set.mem_insert_iff, not_or] using hz
      exact hΞFE z hz'.1 hz'.2
  have hderiv1 : deriv (fun z => Ξ (1 - z)) s = deriv Ξ s := heq.deriv_eq
  have hderiv2 : deriv (fun z => Ξ (1 - z)) s = -deriv Ξ (1 - s) := by
    have hg : HasDerivAt (fun z => (1:ℂ) - z) (-1) s :=
      (hasDerivAt_id s).const_sub 1
    have hcomp := (hΞdiff (1-s) h1sU).hasDerivAt.comp s hg
    rw [show (fun z => Ξ (1 - z)) = Ξ ∘ (fun z => (1:ℂ) - z) from rfl, hcomp.deriv]
    ring
  have hdneg : deriv Ξ (1 - s) = -deriv Ξ s := by
    have h := hderiv2.symm.trans hderiv1
    exact neg_eq_iff_eq_neg.mp h
  rw [logDeriv_apply, logDeriv_apply, hΞFE s hs0 hs1, hdneg, neg_div]

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t70_summable_hadamard_term {ρ : ℕ → ℂ}
    (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    {s : ℂ} (hsρ : ∀ j, s ≠ ρ j) :
    Summable (fun j => (s - ρ j)⁻¹ + (ρ j)⁻¹) := by
  have _em := Classical.em
  have hρ0 : ∀ j, ρ j ≠ 0 := fun j h =>
    absurd (h ▸ (hstrip j).1) (lt_irrefl 0)
  have hρns : ∀ j, (0:ℝ) < Complex.normSq (ρ j) := fun j =>
    Complex.normSq_pos.mpr (hρ0 j)
  have hrw : ∀ j, (s - ρ j)⁻¹ + (ρ j)⁻¹ = s / (ρ j * (s - ρ j)) := fun j => by
    field_simp [sub_ne_zero.mpr (hsρ j), hρ0 j]; ring
  simp_rw [hrw]

  have hM : (0:ℝ) < 4 * (‖s‖+1)^2 + 1 := by positivity
  have hev : ∀ᶠ j in Filter.cofinite,
      4 * (‖s‖+1)^2 + 1 ≤ Complex.normSq (ρ j) := by
    have h0 := hsum.tendsto_cofinite_zero
    have := h0.eventually (gt_mem_nhds (inv_pos.mpr hM))
    filter_upwards [this] with j hj
    exact le_of_lt ((inv_lt_inv₀ (hρns j) hM).mp hj)
  refine Summable.of_norm_bounded_eventually (g := fun j => 4*‖s‖*(Complex.normSq (ρ j))⁻¹)
    (hsum.mul_left (4*‖s‖)) ?_
  filter_upwards [hev] with j hj

  have hns : Complex.normSq (ρ j) = (ρ j).re^2 + (ρ j).im^2 := by
    rw [Complex.normSq_apply]; ring
  have hβ2 : (ρ j).re^2 < 1 := by nlinarith [(hstrip j).1, (hstrip j).2]
  have hγbig : (2*(‖s‖+1))^2 ≤ (ρ j).im^2 := by
    have h : 4*(‖s‖+1)^2 + 1 ≤ (ρ j).re^2 + (ρ j).im^2 := hns ▸ hj
    nlinarith
  have hγabs : 2*(‖s‖+1) ≤ |(ρ j).im| := by
    have h1 : (0:ℝ) ≤ 2*(‖s‖+1) := by positivity
    have h2 := sq_abs (ρ j).im
    nlinarith [abs_nonneg (ρ j).im, sq_nonneg (|(ρ j).im| - 2*(‖s‖+1))]

  have hnρ : |(ρ j).im| ≤ ‖ρ j‖ := Complex.abs_im_le_norm _
  have hnρs : |(ρ j).im| / 2 ≤ ‖ρ j - s‖ := by
    have h1 : |(ρ j).im - s.im| ≤ ‖ρ j - s‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2 : |(ρ j).im| - |s.im| ≤ |(ρ j).im - s.im| := abs_sub_abs_le_abs_sub _ _
    have h3 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm _
    linarith
  have hprod : Complex.normSq (ρ j) / 4 ≤ ‖ρ j‖ * ‖ρ j - s‖ := by
    have h1 : |(ρ j).im|^2 / 2 ≤ ‖ρ j‖ * ‖ρ j - s‖ :=
      calc |(ρ j).im|^2 / 2 = |(ρ j).im| * (|(ρ j).im|/2) := by ring
        _ ≤ ‖ρ j‖ * ‖ρ j - s‖ :=
            mul_le_mul hnρ hnρs (by positivity) (norm_nonneg _)
    have h2 : Complex.normSq (ρ j) ≤ 2 * |(ρ j).im|^2 := by
      rw [hns, sq_abs]; nlinarith [sq_nonneg ‖s‖, norm_nonneg s]
    linarith
  rw [norm_div, norm_mul, show ‖s - ρ j‖ = ‖ρ j - s‖ from norm_sub_rev s (ρ j)]
  calc ‖s‖ / (‖ρ j‖ * ‖ρ j - s‖)
      ≤ ‖s‖ / (Complex.normSq (ρ j) / 4) :=
        div_le_div_of_nonneg_left (norm_nonneg s)
          (div_pos (hρns j) four_pos) hprod
    _ = 4 * ‖s‖ * (Complex.normSq (ρ j))⁻¹ := by
        rw [div_div_eq_mul_div, div_eq_mul_inv]; ring

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t70_hexp_Bfree {B : ℂ} {ρ : ℕ → ℂ}
    (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    (hexp : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
      logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
        = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsρ : ∀ j, s ≠ ρ j)
    (hs1ρ : ∀ j, 1 - s ≠ ρ j) :
    B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)
      = (1 / 2) * ∑' j, ((s - ρ j)⁻¹ - (1 - s - ρ j)⁻¹) := by
  have _em := Classical.em
  have h1s0 : (1:ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h1s1 : (1:ℂ) - s ≠ 1 := fun h => hs0 (sub_eq_self.mp h)
  have hsumAs := gapsw80_t70_summable_hadamard_term hstrip hsum hsρ
  have hsumA1s := gapsw80_t70_summable_hadamard_term hstrip hsum hs1ρ
  have hkey : B + ∑' j, ((1 - s - ρ j)⁻¹ + (ρ j)⁻¹)
      = -(B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)) := by
    rw [← hexp (1-s) h1s0 h1s1 hs1ρ, ← hexp s hs0 hs1 hsρ]
    exact gapsw80_t70_hexp_FE_neg (K := K) hs0 hs1
  have h2 : B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)
      = (1/2) * ((∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
          - (∑' j, ((1 - s - ρ j)⁻¹ + (ρ j)⁻¹))) := by
    linear_combination ((1:ℂ)/2) * hkey
  rw [h2, ← Summable.tsum_sub hsumAs hsumA1s]
  congr 1
  exact tsum_congr fun j => by ring

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t70_laplace_cos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ x in Set.Ioi (0:ℝ), Real.exp (-(a * x)) * Real.cos (b * x)
      = a / (a ^ 2 + b ^ 2) := by
  have _em := Classical.em
  have hden : (0:ℝ) < a^2 + b^2 := by positivity
  set f : ℝ → ℝ := fun x =>
    Real.exp (-(a*x)) * (-a * Real.cos (b*x) + b * Real.sin (b*x)) / (a^2+b^2)
    with hf_def
  have hf' : ∀ x, HasDerivAt f (Real.exp (-(a*x)) * Real.cos (b*x)) x := by
    intro x
    have he : HasDerivAt (fun y => Real.exp (-(a*y))) (-a * Real.exp (-(a*x))) x := by
      have h := ((hasDerivAt_id x).const_mul (-a)).exp
      simp only [id_eq, mul_one, neg_mul] at h
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | ring
    have hc : HasDerivAt (fun y => -a * Real.cos (b*y) + b * Real.sin (b*y))
        (a*b * Real.sin (b*x) + b^2 * Real.cos (b*x)) x := by
      have := (((hasDerivAt_id x).const_mul b).cos.const_mul (-a)).add
        (((hasDerivAt_id x).const_mul b).sin.const_mul b)
      simp only [id_eq, mul_one] at this
      convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | ring
    have := (he.mul hc).div_const (a^2+b^2)
    convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    field_simp
    ring

  have hfcont : Continuous f := by
    have : Continuous (fun x : ℝ => Real.exp (-(a*x))) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
    exact (this.mul ((continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).add (continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))))).div_const _

  have hftend : Filter.Tendsto f Filter.atTop (𝓝 0) := by
    have hbd : ∀ x, |f x| ≤ (a + |b|)/(a^2+b^2) * Real.exp (-(a*x)) := fun x => by
      have htrig : |(-a * Real.cos (b*x) + b * Real.sin (b*x))| ≤ a + |b| :=
        calc |(-a * Real.cos (b*x) + b * Real.sin (b*x))|
            ≤ |(-a) * Real.cos (b*x)| + |b * Real.sin (b*x)| :=
              abs_add_le (-a * Real.cos (b*x)) (b * Real.sin (b*x))
          _ ≤ a * 1 + |b| * 1 := by
              rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha]
              gcongr
              · exact Real.abs_cos_le_one _
              · exact Real.abs_sin_le_one _
          _ = a + |b| := by ring
      simp only [hf_def, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos hden]
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden,
        mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_right htrig (Real.exp_pos _).le
    have he0 : Filter.Tendsto (fun x => (a + |b|)/(a^2+b^2) * Real.exp (-(a*x)))
        Filter.atTop (𝓝 0) := by
      rw [show (0:ℝ) = (a+|b|)/(a^2+b^2) * 0 from (mul_zero _).symm]
      exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop ha)).const_mul _
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      ((squeeze_zero (fun x => abs_nonneg _) hbd he0).congr
        (fun x => (Real.norm_eq_abs _).symm))

  have hint : IntegrableOn (fun x => Real.exp (-(a*x)) * Real.cos (b*x))
      (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 ha).mono' ?_
      (Filter.Eventually.of_forall fun x => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable.restrict
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(a*x)) * |Real.cos (b*x)|
          ≤ Real.exp (-(a*x)) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
        _ = _ := by rw [mul_one]; ring_nf

  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (hfcont.continuousWithinAt) (fun x _ => hf' x) hint hftend
  rw [hFTC]
  simp only [hf_def, mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero,
    mul_one, _root_.neg_zero, add_zero, one_mul]
  ring

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t70_poisson_shifted {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F) {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    Integrable (fun t => (a / (a ^ 2 + (t - γ) ^ 2))
        * (∫ x : ℝ, F x * Real.cos (t * x)))
    ∧ (1 / Real.pi) * ∫ t : ℝ, (a / (a ^ 2 + (t - γ) ^ 2))
          * (∫ x : ℝ, F x * Real.cos (t * x))
        = 2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(a * x))
            * Real.cos (γ * x) := by
  have _em := Classical.em
  have ⟨hFh_int, _⟩ := gapsw80_t64_integrable_Fhat hF
  have hFh_nn : ∀ t, 0 ≤ ∫ x : ℝ, F x * Real.cos (t * x) := hF.2.2.2.2.2
  set Fh : ℝ → ℝ := fun t => ∫ x : ℝ, F x * Real.cos (t * x) with hFh_def
  have hFh_nn' : ∀ t, (0:ℝ) ≤ Fh t := hFh_nn
  have hFh_cont : Continuous Fh := gapsw80_t64_continuous_Fhat hF

  have hint : Integrable (fun t => (a / (a^2 + (t-γ)^2)) * Fh t) := by
    apply Integrable.mono' (hFh_int.const_mul (1/a))
    · exact ((continuous_const.div (by continuity)
        (fun t => by positivity)).mul hFh_cont).aestronglyMeasurable
    · filter_upwards with t
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFh_nn' t),
        abs_of_nonneg (show (0:ℝ) ≤ a/(a^2+(t-γ)^2) from by positivity),
        abs_of_nonneg (show (0:ℝ) ≤ 1/a from by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (hFh_nn' t)
      rw [div_le_div_iff₀ (by positivity) ha]; nlinarith [sq_nonneg (t-γ)]
  refine ⟨hint, ?_⟩

  have hexp_int : IntegrableOn (fun x => Real.exp (-(a*x))) (Set.Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
    simpa only [neg_mul] using this

  have hg_int : Integrable (Function.uncurry
      (fun t x => Real.exp (-(a*x)) * Real.cos ((t-γ)*x) * Fh t))
      ((volume : Measure ℝ).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    apply (hFh_int.mul_prod hexp_int).mono'
    · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_snd).neg).mul
        (Real.continuous_cos.comp ((continuous_fst.sub continuous_const).mul
          continuous_snd))).mul (hFh_cont.comp continuous_fst)).aestronglyMeasurable
    · filter_upwards with p
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (hFh_nn' p.1)]
      calc Real.exp (-(a*p.2)) * |Real.cos ((p.1-γ)*p.2)| * Fh p.1
          ≤ Real.exp (-(a*p.2)) * 1 * Fh p.1 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
                (Real.exp_pos _).le) (hFh_nn' p.1)
        _ = Fh p.1 * Real.exp (-(a*p.2)) := by ring

  have hLHS : ∫ t, (a / (a^2+(t-γ)^2)) * Fh t
      = ∫ x in Set.Ioi (0:ℝ),
          ∫ t, Real.exp (-(a*x)) * Real.cos ((t-γ)*x) * Fh t := by
    rw [← MeasureTheory.integral_integral_swap hg_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show a/(a^2+(t-γ)^2) * Fh t
      = ∫ x in Set.Ioi (0:ℝ), Real.exp (-(a*x)) * Real.cos ((t-γ)*x) * Fh t
    rw [← gapsw80_t70_laplace_cos ha (t-γ), ← integral_mul_const]

  have hFcos_int : ∀ x, Integrable (fun t => Fh t * Real.cos (x*t)) := fun x => by
    refine hFh_int.mono' (hFh_cont.mul (by continuity)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFh_nn' t)]
    exact mul_le_of_le_one_right (hFh_nn' t) (Real.abs_cos_le_one _)
  have hFsin_int : ∀ x, Integrable (fun t => Fh t * Real.sin (x*t)) := fun x => by
    refine hFh_int.mono' (hFh_cont.mul (by continuity)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFh_nn' t)]
    exact mul_le_of_le_one_right (hFh_nn' t) (Real.abs_sin_le_one _)
  have hsin0 : ∀ x, ∫ t, Fh t * Real.sin (x*t) = 0 := fun x => by
    have hFh_even : ∀ t, Fh (-t) = Fh t := fun t => by
      simp only [hFh_def]; congr 1; ext y; rw [neg_mul, Real.cos_neg]
    have hodd : ∀ t, Fh (-t) * Real.sin (x * -t) = -(Fh t * Real.sin (x*t)) :=
      fun t => by rw [hFh_even, mul_neg, Real.sin_neg]; ring
    have h := (integral_neg_eq_self (fun t => Fh t * Real.sin (x*t))
      (volume : Measure ℝ)).symm
    simp_rw [hodd, integral_neg] at h; linarith
  have hinner : ∀ x : ℝ,
      ∫ t, Real.exp (-(a*x)) * Real.cos ((t-γ)*x) * Fh t
      = 2*Real.pi * (F x * Real.exp (-(a*x)) * Real.cos (γ*x)) := fun x => by
    rw [show (fun t => Real.exp (-(a*x)) * Real.cos ((t-γ)*x) * Fh t)
        = (fun t => Real.exp (-(a*x)) * Real.cos (γ*x) * (Fh t * Real.cos (x*t))
            + Real.exp (-(a*x)) * Real.sin (γ*x) * (Fh t * Real.sin (x*t))) from
      funext fun t => by
        rw [show (t-γ)*x = x*t - γ*x from by ring, Real.cos_sub]; ring,
      integral_add ((hFcos_int x).const_mul _) ((hFsin_int x).const_mul _),
      integral_const_mul, integral_const_mul,
      show (∫ t, Fh t * Real.cos (x*t)) = 2*Real.pi*F x from
        gapsw80_t64_cosine_inversion hF x,
      hsin0 x, mul_zero, add_zero]
    ring
  rw [hLHS]; simp_rw [hinner]; rw [integral_const_mul, ← mul_assoc]
  congr 1; field_simp

private noncomputable def gapsw80_t70_zeroSideTerm
    (F : ℝ → ℝ) (ρ : ℂ) (σ : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0:ℝ),
    F x * (Real.exp (-((σ - ρ.re) * x)) + Real.exp (-((σ + ρ.re - 1) * x)))
      * Real.cos (ρ.im * x)

private noncomputable def gapsw80_t70_zeroSideSigma
    (F : ℝ → ℝ) (ρ : ℕ → ℂ) (σ : ℝ) : ℝ :=
  ∑' j, gapsw80_t70_zeroSideTerm F (ρ j) σ

set_option maxHeartbeats 12800000 in

private theorem gapsw80_t70_zeroSide_ibp_bound {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hcd : ContDiff ℝ 2 F) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hdecay : ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))
    {ρ : ℂ} (hρ1 : 0 < ρ.re) (hρ2 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    |gapsw80_t70_zeroSideTerm F ρ σ| * ρ.im ^ 2
      ≤ (2 * σ - 1) + 9 * c * σ ^ 2 / ε := by
  have _em := Classical.em
  set γ : ℝ := ρ.im with hγ_def
  set a₁ : ℝ := σ - ρ.re with ha₁_def
  set a₂ : ℝ := σ + ρ.re - 1 with ha₂_def
  have ha₁p : 0 < a₁ := by rw [ha₁_def]; linarith
  have ha₂p : 0 < a₂ := by rw [ha₂_def]; linarith
  have ha₁σ : a₁ < σ := by rw [ha₁_def]; linarith
  have ha₂σ : a₂ < σ := by rw [ha₂_def]; linarith
  have hγ0 : γ ≠ 0 := fun h => by
    rw [h, abs_zero] at hγ; linarith
  have hγ2 : (1:ℝ) ≤ γ^2 := by
    nlinarith [sq_abs γ, hγ, abs_nonneg γ]

  set E : ℝ → ℝ := fun x => Real.exp (-(a₁*x)) + Real.exp (-(a₂*x)) with hE_def
  set E' : ℝ → ℝ := fun x => -a₁*Real.exp (-(a₁*x)) + -a₂*Real.exp (-(a₂*x))
    with hE'_def
  set E'' : ℝ → ℝ := fun x => a₁^2*Real.exp (-(a₁*x)) + a₂^2*Real.exp (-(a₂*x))
    with hE''_def
  have hEd : ∀ x, HasDerivAt E (E' x) x := fun x => by
    have h1 := ((hasDerivAt_id x).const_mul (-a₁)).exp
    have h2 := ((hasDerivAt_id x).const_mul (-a₂)).exp
    simp only [id_eq, mul_one, neg_mul] at h1 h2
    convert h1.fun_add h2 using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    simp only [hE'_def]; ring
  have hE'd : ∀ x, HasDerivAt E' (E'' x) x := fun x => by
    have h1 := (((hasDerivAt_id x).const_mul (-a₁)).exp).const_mul (-a₁)
    have h2 := (((hasDerivAt_id x).const_mul (-a₂)).exp).const_mul (-a₂)
    simp only [id_eq, mul_one, neg_mul] at h1 h2
    have h := h1.fun_add h2
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    · ext y; simp only [hE'_def, Pi.add_apply, neg_mul]
    · simp only [hE''_def]; ring
  have hEcont : Continuous E := by
    simp only [hE_def]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).add
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
  have hE'cont : Continuous E' := by
    simp only [hE'_def]
    exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg)).add
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg))
  set H : ℝ → ℝ := fun x => F x * E x with hH_def
  set H' : ℝ → ℝ := fun x => deriv F x * E x + F x * E' x with hH'_def
  set H'' : ℝ → ℝ := fun x =>
    deriv (deriv F) x * E x + 2*deriv F x * E' x + F x * E'' x with hH''_def
  have hFd : ∀ x, HasDerivAt F (deriv F x) x := fun x =>
    (hcd.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hF'd : ∀ x, HasDerivAt (deriv F) (deriv (deriv F) x) x := fun x =>
    ((hcd.iterate_deriv' 1 1).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hHd : ∀ x, HasDerivAt H (H' x) x := fun x => (hFd x).mul (hEd x)
  have hH'd : ∀ x, HasDerivAt H' (H'' x) x := fun x => by
    have := ((hF'd x).mul (hEd x)).add (((hFd x).mul (hE'd x)).add
      (((hFd x).mul (hE'd x))))

    have h := ((hF'd x).fun_mul (hEd x)).fun_add ((hFd x).fun_mul (hE'd x))
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    simp only [hH''_def]; ring
  have hHcont : Continuous H := hF.1.continuous.mul hEcont
  have hH'cont : Continuous H' :=
    ((hcd.continuous_deriv (by norm_num)).mul hEcont).add (hF.1.continuous.mul hE'cont)

  have hEbd : ∀ x ∈ Set.Ioi (0:ℝ), |E x| ≤ 2 ∧ |E' x| ≤ 2*σ ∧ |E'' x| ≤ 2*σ^2 := by
    intro x hx
    have hxp : (0:ℝ) < x := hx
    have he1 : Real.exp (-(a₁*x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he2 : Real.exp (-(a₂*x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he1p := Real.exp_pos (-(a₁*x)); have he2p := Real.exp_pos (-(a₂*x))
    refine ⟨?_, ?_, ?_⟩
    · simp only [hE_def]; rw [abs_of_pos (by positivity)]; linarith
    · simp only [hE'_def]
      calc |(-a₁*Real.exp (-(a₁*x)) + -a₂*Real.exp (-(a₂*x)))|
          ≤ a₁*1 + a₂*1 := by
            rw [abs_of_nonpos (by nlinarith), neg_add, neg_mul, neg_mul, neg_neg,
              neg_neg]
            gcongr
        _ ≤ 2*σ := by linarith
    · simp only [hE''_def]; rw [abs_of_pos (by positivity)]
      calc a₁^2*Real.exp (-(a₁*x)) + a₂^2*Real.exp (-(a₂*x))
          ≤ σ^2*1 + σ^2*1 := by gcongr <;> nlinarith
        _ = 2*σ^2 := by ring

  have hH''bd : ∀ x ∈ Set.Ioi (0:ℝ),
      |H'' x| ≤ 2*(1+σ)^2 * (c*Real.exp (-(1/2+ε)*x)) := fun x hx => by
    have ⟨hEb, hE'b, hE''b⟩ := hEbd x hx
    have hd0 := hdecay 0 x; have hd1 := hdecay 1 x; have hd2 := hdecay 2 x
    have hxp : (0:ℝ) < x := hx
    simp only [show ((0:Fin 3):ℕ)=0 from rfl, show ((1:Fin 3):ℕ)=1 from rfl,
      show ((2:Fin 3):ℕ)=2 from rfl, iteratedDeriv_zero, iteratedDeriv_one,
      iteratedDeriv_succ, abs_of_pos hxp] at hd0 hd1 hd2
    simp only [hH''_def]
    calc |deriv (deriv F) x * E x + 2*deriv F x * E' x + F x * E'' x|
        ≤ |deriv (deriv F) x| * |E x| + 2 * |deriv F x| * |E' x| + |F x| * |E'' x| := by
          refine (abs_add_three _ _ _).trans ?_
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
      _ ≤ (c*Real.exp (-(1/2+ε)*x)) * 2 + 2 * (c*Real.exp (-(1/2+ε)*x)) * (2*σ)
          + (c*Real.exp (-(1/2+ε)*x)) * (2*σ^2) := by
          gcongr
      _ = 2*(1+σ)^2 * (c*Real.exp (-(1/2+ε)*x)) := by ring

  have hmaj_Ioi : IntegrableOn
      (fun x => 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x))) (Set.Ioi 0) := by
    apply Integrable.const_mul
    exact ((exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ)<1/2+ε)).const_mul c)

  have hmaj0 : Filter.Tendsto
      (fun x => 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x))) Filter.atTop (𝓝 0) := by
    have he : Filter.Tendsto (fun x : ℝ => Real.exp (-(1/2+ε)*x))
        Filter.atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop (show (0:ℝ)<1/2+ε from by linarith))
      refine h.congr (fun x => ?_)
      show Real.exp (-((1/2+ε)*x)) = Real.exp (-(1/2+ε)*x)
      rw [neg_mul]
    rw [show (0:ℝ) = 2*(1+σ)^2*(c*0) from by ring]
    exact (he.const_mul c).const_mul (2*(1+σ)^2)
  have hHbd : ∀ x ∈ Set.Ioi (0:ℝ), |H x| ≤ 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x))
      ∧ |H' x| ≤ 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x)) := fun x hx => by
    have ⟨hEb, hE'b, _⟩ := hEbd x hx
    have hxp : (0:ℝ) < x := hx
    have hd0 := hdecay 0 x; have hd1 := hdecay 1 x
    simp only [show ((0:Fin 3):ℕ)=0 from rfl, show ((1:Fin 3):ℕ)=1 from rfl,
      iteratedDeriv_zero, iteratedDeriv_one, abs_of_pos hxp] at hd0 hd1
    have hep := Real.exp_pos (-(1/2+ε)*x)
    have hσsq : (1:ℝ) ≤ (1+σ)^2 := by nlinarith
    have hce : (0:ℝ) < c*Real.exp (-(1/2+ε)*x) := by positivity
    refine ⟨?_, ?_⟩
    · simp only [hH_def, abs_mul]
      calc |F x| * |E x| ≤ (c*Real.exp (-(1/2+ε)*x)) * 2 := by gcongr
        _ ≤ 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x)) := by nlinarith [hσsq, hce]
    · simp only [hH'_def]
      calc |deriv F x * E x + F x * E' x|
          ≤ |deriv F x| * |E x| + |F x| * |E' x| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
        _ ≤ (c*Real.exp (-(1/2+ε)*x)) * 2 + (c*Real.exp (-(1/2+ε)*x)) * (2*σ) := by
            gcongr
        _ ≤ 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x)) := by nlinarith [hσsq, hce]
  have hev_Ioi : ∀ᶠ x in Filter.atTop, x ∈ Set.Ioi (0:ℝ) :=
    Filter.eventually_atTop.mpr ⟨1, fun x hx => lt_of_lt_of_le one_pos hx⟩
  have htend0 : ∀ G : ℝ → ℝ, (∀ x ∈ Set.Ioi (0:ℝ),
      |G x| ≤ 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x))) →
      Filter.Tendsto G Filter.atTop (𝓝 0) := fun G hGbd => by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' ?_ ?_ hmaj0)
    · filter_upwards with x using norm_nonneg _
    · filter_upwards [hev_Ioi] with x hx
      rw [Real.norm_eq_abs]; exact hGbd x hx
  have hHtend : Filter.Tendsto H Filter.atTop (𝓝 0) :=
    htend0 H (fun x hx => (hHbd x hx).1)
  have hH'tend : Filter.Tendsto H' Filter.atTop (𝓝 0) :=
    htend0 H' (fun x hx => (hHbd x hx).2)

  have hint_bm : ∀ G : ℝ → ℝ, Continuous G → (∀ x ∈ Set.Ioi (0:ℝ),
      |G x| ≤ 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x))) →
      ∀ tr : ℝ → ℝ, Continuous tr → (∀ x, |tr x| ≤ 1) →
      IntegrableOn (fun x => G x * tr x) (Set.Ioi 0) := by
    intro G hGc hGbd tr htrc htrb
    refine hmaj_Ioi.mono' (hGc.mul htrc).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    calc |G x| * |tr x| ≤ (2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x))) * 1 :=
          mul_le_mul (hGbd x hx) (htrb x) (abs_nonneg _) (by positivity)
      _ = 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x)) := mul_one _
  have hcos_c : Continuous (fun x => Real.cos (γ*x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin_c : Continuous (fun x => Real.sin (γ*x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hHcos := hint_bm H hHcont (fun x hx => (hHbd x hx).1)
    _ hcos_c (fun x => Real.abs_cos_le_one _)
  have hH'sin := hint_bm H' hH'cont (fun x hx => (hHbd x hx).2)
    _ hsin_c (fun x => Real.abs_sin_le_one _)
  have hE''cont : Continuous E'' := by
    simp only [hE''_def]
    exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg)).add
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg))
  have hH''cont : Continuous H'' := by
    simp only [hH''_def]
    exact (((hcd.iterate_deriv' 0 2).continuous.mul hEcont).add
      ((continuous_const.mul (hcd.continuous_deriv (by norm_num))).mul hE'cont)).add
      (hF.1.continuous.mul hE''cont)
  have hH''cos := hint_bm H'' hH''cont hH''bd
    _ hcos_c (fun x => Real.abs_cos_le_one _)

  have htend_bm : ∀ G tr : ℝ → ℝ, Filter.Tendsto G Filter.atTop (𝓝 0) →
      (∀ x, |tr x| ≤ 1) →
      Filter.Tendsto (fun x => G x * tr x) Filter.atTop (𝓝 0) := by
    intro G tr hG htr
    have hGn : Filter.Tendsto (fun x => ‖G x‖) Filter.atTop (𝓝 0) := by
      simpa using hG.norm
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _)
        (Filter.Eventually.of_forall fun x => ?_) hGn)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.norm_eq_abs _ ▸ htr x)

  have hibp1 : ∫ x in Set.Ioi (0:ℝ), H x * Real.cos (γ*x)
      = -(1/γ) * ∫ x in Set.Ioi (0:ℝ), H' x * Real.sin (γ*x) := by
    set u : ℝ → ℝ := fun x => H x * Real.sin (γ*x) / γ with hu_def
    have hud : ∀ x, HasDerivAt u
        ((1/γ) * (H' x * Real.sin (γ*x)) + H x * Real.cos (γ*x)) x := fun x => by
      have htr : HasDerivAt (fun y => Real.sin (γ*y)) (γ*Real.cos (γ*x)) x := by
        have := ((hasDerivAt_id x).const_mul γ).sin; simpa [mul_comm] using this
      have h := ((hHd x).mul htr).div_const γ
      refine (show (H' x * Real.sin (γ*x) + H x * (γ * Real.cos (γ*x))) / γ
        = (1/γ) * (H' x * Real.sin (γ*x)) + H x * Real.cos (γ*x) from by
        field_simp) ▸ h
    have hu_int : IntegrableOn
        (fun x => (1/γ) * (H' x * Real.sin (γ*x)) + H x * Real.cos (γ*x)) (Set.Ioi 0) :=
      (hH'sin.const_mul (1/γ)).add hHcos
    have hu_tend : Filter.Tendsto u Filter.atTop (𝓝 0) := by
      have h := (htend_bm H (fun x => Real.sin (γ*x)) hHtend
        (fun x => Real.abs_sin_le_one _)).div_const γ
      simpa [hu_def, zero_div] using h
    have hucont : ContinuousWithinAt u (Set.Ici 0) 0 :=
      (hHcont.mul hsin_c |>.div_const γ).continuousWithinAt
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hucont
      (fun x _ => hud x) hu_int hu_tend
    simp only [hu_def, mul_zero, Real.sin_zero, zero_div, sub_zero] at hFTC
    have hc1 : IntegrableOn (fun x => (1/γ) * (H' x * Real.sin (γ*x))) (Set.Ioi 0) :=
      hH'sin.const_mul (1/γ)
    rw [integral_add hc1 hHcos, integral_const_mul] at hFTC
    linarith [hFTC]

  have hibp2 : ∫ x in Set.Ioi (0:ℝ), H' x * Real.sin (γ*x)
      = H' 0 / γ + (1/γ) * ∫ x in Set.Ioi (0:ℝ), H'' x * Real.cos (γ*x) := by
    set v : ℝ → ℝ := fun x => -(H' x * Real.cos (γ*x)) / γ with hv_def
    have hvd : ∀ x, HasDerivAt v
        (-((1/γ) * (H'' x * Real.cos (γ*x))) + H' x * Real.sin (γ*x)) x := fun x => by
      have htr : HasDerivAt (fun y => Real.cos (γ*y)) (-(γ*Real.sin (γ*x))) x := by
        have := ((hasDerivAt_id x).const_mul γ).cos; simpa [mul_comm] using this
      have h := (((hH'd x).mul htr).neg).div_const γ
      refine (show -(H'' x * Real.cos (γ*x) + H' x * (-(γ*Real.sin (γ*x)))) / γ
        = -((1/γ) * (H'' x * Real.cos (γ*x))) + H' x * Real.sin (γ*x) from by
        field_simp; ring) ▸ h
    have hv_int : IntegrableOn
        (fun x => -((1/γ) * (H'' x * Real.cos (γ*x))) + H' x * Real.sin (γ*x))
        (Set.Ioi 0) :=
      ((hH''cos.const_mul (1/γ)).neg).add hH'sin
    have hv_tend : Filter.Tendsto v Filter.atTop (𝓝 0) := by
      have h := ((htend_bm H' (fun x => Real.cos (γ*x)) hH'tend
        (fun x => Real.abs_cos_le_one _)).neg).div_const γ
      simpa [hv_def, _root_.neg_zero, zero_div] using h
    have hvcont : ContinuousWithinAt v (Set.Ici 0) 0 :=
      ((hH'cont.mul hcos_c).neg.div_const γ).continuousWithinAt
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hvcont
      (fun x _ => hvd x) hv_int hv_tend
    simp only [hv_def, mul_zero, Real.cos_zero, mul_one,
      neg_div, zero_sub, neg_neg] at hFTC
    have hc2 : IntegrableOn (fun x => -((1/γ) * (H'' x * Real.cos (γ*x))))
        (Set.Ioi 0) := (hH''cos.const_mul (1/γ)).neg
    rw [integral_add hc2 hH'sin, integral_neg, integral_const_mul] at hFTC
    linarith [hFTC]

  have hH'0 : H' 0 = -(2*σ-1) := by
    have hF'0 : deriv F 0 = 0 := by
      have heq : (fun x => F (-x)) = F := funext hF.2.1
      have h : deriv (fun x => F (-x)) 0 = -deriv F (-0) := deriv_comp_neg F 0
      rw [heq, _root_.neg_zero] at h
      linarith
    simp only [hH'_def, hE_def, hE'_def, mul_zero, Real.exp_zero, _root_.neg_zero,
      hF'0, zero_mul, zero_add, hF.2.2.1, one_mul]
    rw [ha₁_def, ha₂_def]; ring
  have hZ_eq : gapsw80_t70_zeroSideTerm F ρ σ
      = (2*σ-1)/γ^2 - (1/γ^2) * ∫ x in Set.Ioi (0:ℝ), H'' x * Real.cos (γ*x) := by
    unfold gapsw80_t70_zeroSideTerm
    rw [show (∫ x in Set.Ioi (0:ℝ), F x * (Real.exp (-((σ-ρ.re)*x))
          + Real.exp (-((σ+ρ.re-1)*x))) * Real.cos (ρ.im*x))
        = ∫ x in Set.Ioi (0:ℝ), H x * Real.cos (γ*x) from rfl,
      hibp1, hibp2, hH'0]
    field_simp; ring

  rw [hZ_eq, abs_sub_comm]
  have hγ2p : (0:ℝ) < γ^2 := by positivity
  calc |(1/γ^2) * (∫ x in Set.Ioi (0:ℝ), H'' x * Real.cos (γ*x)) - (2*σ-1)/γ^2| * γ^2
      ≤ ((1/γ^2) * |∫ x in Set.Ioi (0:ℝ), H'' x * Real.cos (γ*x)| + (2*σ-1)/γ^2) * γ^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg γ)
        refine (abs_sub _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_of_pos (show (0:ℝ) < 1/γ^2 from by positivity),
          abs_of_nonneg (div_nonneg (show (0:ℝ) ≤ 2*σ-1 from by linarith) (sq_nonneg γ))]
    _ = |∫ x in Set.Ioi (0:ℝ), H'' x * Real.cos (γ*x)| + (2*σ-1) := by
        field_simp
    _ ≤ (∫ x in Set.Ioi (0:ℝ), 2*(1+σ)^2*(c*Real.exp (-(1/2+ε)*x))) + (2*σ-1) := by
        gcongr
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans ?_
        exact setIntegral_mono_on hH''cos.norm hmaj_Ioi measurableSet_Ioi
          (fun x hx => by
            rw [Real.norm_eq_abs, abs_mul]
            exact (mul_le_of_le_one_right (abs_nonneg _)
              (Real.abs_cos_le_one _)).trans (hH''bd x hx))
    _ ≤ 9*c*σ^2/ε + (2*σ-1) := by
        gcongr
        rw [integral_const_mul, integral_const_mul]
        have hv := integral_exp_mul_Ioi (a := -(1/2+ε)) (by linarith) 0
        simp only [mul_zero, Real.exp_zero, neg_neg] at hv
        rw [hv]
        have h1 : (1+σ)^2 ≤ 4*σ^2 := by nlinarith
        have h2 : (-(1:ℝ) / -(1/2+ε)) = 1/(1/2+ε) := neg_div_neg_eq 1 (1/2+ε)
        rw [h2]
        calc 2*(1+σ)^2 * (c * (1/(1/2+ε)))
            ≤ 2*(4*σ^2) * (c * (1/(1/2+ε))) := by
              apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = 8*c*σ^2 / (1/2+ε) := by ring
          _ ≤ 8*c*σ^2 / ε :=
              div_le_div_of_nonneg_left (by positivity) hε (by linarith)
          _ ≤ 9*c*σ^2/ε := by
              gcongr; nlinarith [hc.le, sq_nonneg σ]
    _ = (2*σ-1) + 9*c*σ^2/ε := by ring

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t70_zeroSide_summable {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hFC2 : gapsw80_t69_KernelC2Decay F) {ρ : ℕ → ℂ}
    (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable (fun j => gapsw80_t70_zeroSideTerm F (ρ j) σ) := by
  have _em := Classical.em
  obtain ⟨hcd, c, ε, hc, hε, hdecay⟩ := hFC2
  have hρ0 : ∀ j, (0:ℝ) < Complex.normSq (ρ j) := fun j => by
    rw [Complex.normSq_pos]; intro h
    exact absurd (h ▸ (hstrip j).1) (lt_irrefl 0)
  set M : ℝ := 2 * ((2*σ-1) + 9*c*σ^2/ε) + 2 * (4*c/ε) with hM_def
  have hbound : ∀ j, |gapsw80_t70_zeroSideTerm F (ρ j) σ|
      ≤ M * (Complex.normSq (ρ j))⁻¹ := fun j => by
    have hns : Complex.normSq (ρ j) = (ρ j).re ^ 2 + (ρ j).im ^ 2 := by
      rw [Complex.normSq_apply]; ring
    have hβ := hstrip j
    have hβ2 : (ρ j).re ^ 2 < 1 := by nlinarith [hβ.1, hβ.2]
    suffices hkey : |gapsw80_t70_zeroSideTerm F (ρ j) σ| * Complex.normSq (ρ j) ≤ M by
      have h := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (hρ0 j).le)
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt (hρ0 j)), mul_one] at h
    rcases le_or_gt 1 |(ρ j).im| with hγ | hγ
    · have h0e := gapsw80_t70_zeroSide_ibp_bound hF hcd hc hε hdecay
        hβ.1 hβ.2 hγ hσ
      have hns2 : Complex.normSq (ρ j) ≤ 2 * (ρ j).im^2 := by
        rw [hns]; have := sq_abs (ρ j).im; nlinarith
      calc |gapsw80_t70_zeroSideTerm F (ρ j) σ| * Complex.normSq (ρ j)
          ≤ |gapsw80_t70_zeroSideTerm F (ρ j) σ| * (2 * (ρ j).im^2) :=
            mul_le_mul_of_nonneg_left hns2 (abs_nonneg _)
        _ = 2 * (|gapsw80_t70_zeroSideTerm F (ρ j) σ| * (ρ j).im^2) := by ring
        _ ≤ 2 * ((2*σ-1) + 9*c*σ^2/ε) := by linarith
        _ ≤ M := by
            rw [hM_def]
            have h4 : (0:ℝ) ≤ 2*(4*c/ε) := by positivity
            linarith
    ·
      have hγ2 : (ρ j).im^2 < 1 := by
        have ⟨h1, h2⟩ := abs_lt.mp hγ; nlinarith
      have hns2 : Complex.normSq (ρ j) < 2 := by rw [hns]; linarith

      have ha1 : (0:ℝ) < σ - (ρ j).re := by linarith [hβ.2]
      have ha2 : (0:ℝ) < σ + (ρ j).re - 1 := by linarith [hβ.1]
      have hmaj_Ioi : IntegrableOn
          (fun x => 2*c*Real.exp (-(1/2+ε)*x)) (Set.Ioi 0) :=
        ((exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ)<1/2+ε)).const_mul (2*c))
      have hzconst : |gapsw80_t70_zeroSideTerm F (ρ j) σ| ≤ 4*c/ε := by
        unfold gapsw80_t70_zeroSideTerm
        have hpt : ∀ x ∈ Set.Ioi (0:ℝ),
            ‖F x * (Real.exp (-((σ-(ρ j).re)*x)) + Real.exp (-((σ+(ρ j).re-1)*x)))
              * Real.cos ((ρ j).im * x)‖
            ≤ 2*c*Real.exp (-(1/2+ε)*x) := fun x hx => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have hxp : (0:ℝ) < x := hx
          have hd0 := hdecay 0 x
          simp only [show ((0:Fin 3):ℕ)=0 from rfl, iteratedDeriv_zero] at hd0
          calc |F x| * |Real.exp (-((σ-(ρ j).re)*x))
                + Real.exp (-((σ+(ρ j).re-1)*x))| * |Real.cos ((ρ j).im*x)|
              ≤ c*Real.exp (-(1/2+ε)*|x|) * 2 * 1 := by
                apply mul_le_mul _ (Real.abs_cos_le_one _) (abs_nonneg _)
                  (by positivity)
                apply mul_le_mul hd0 _ (abs_nonneg _) (by positivity)
                rw [abs_of_pos (by positivity)]
                have he1 : Real.exp (-((σ-(ρ j).re)*x)) ≤ 1 :=
                  Real.exp_le_one_iff.mpr (by nlinarith)
                have he2 : Real.exp (-((σ+(ρ j).re-1)*x)) ≤ 1 :=
                  Real.exp_le_one_iff.mpr (by nlinarith)
                linarith
            _ = 2*c*Real.exp (-(1/2+ε)*x) := by
                rw [mul_one, abs_of_pos hx]; ring
        have hf_int : IntegrableOn (fun x => F x *
            (Real.exp (-((σ-(ρ j).re)*x)) + Real.exp (-((σ+(ρ j).re-1)*x)))
            * Real.cos ((ρ j).im * x)) (Set.Ioi 0) := by
          refine hmaj_Ioi.mono' ?_ ?_
          · exact ((hF.1.continuous.mul ((Real.continuous_exp.comp
              (continuous_const.mul continuous_id).neg).add
              (Real.continuous_exp.comp
                (continuous_const.mul continuous_id).neg))).mul
              (Real.continuous_cos.comp
                (continuous_const.mul continuous_id))).aestronglyMeasurable.restrict
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            exact hpt x hx
        calc |∫ x in Set.Ioi (0:ℝ), F x *
              (Real.exp (-((σ-(ρ j).re)*x)) + Real.exp (-((σ+(ρ j).re-1)*x)))
              * Real.cos ((ρ j).im * x)|
            ≤ ∫ x in Set.Ioi (0:ℝ), 2*c*Real.exp (-(1/2+ε)*x) := by
              have h1 := norm_integral_le_integral_norm
                (μ := volume.restrict (Set.Ioi 0))
                (fun x => F x * (Real.exp (-((σ-(ρ j).re)*x))
                  + Real.exp (-((σ+(ρ j).re-1)*x))) * Real.cos ((ρ j).im * x))
              rw [Real.norm_eq_abs] at h1
              refine h1.trans (setIntegral_mono_on hf_int.norm hmaj_Ioi
                measurableSet_Ioi ?_)
              exact fun x hx => hpt x hx
          _ = 2*c/(1/2+ε) := by
              rw [integral_const_mul]
              have hv := integral_exp_mul_Ioi (a := -(1/2+ε)) (by linarith) 0
              simp only [mul_zero, Real.exp_zero, neg_neg] at hv
              rw [hv]; ring_nf
              rw [show (-(1:ℝ)/2-ε) = -(1/2+ε) from by ring, inv_neg]; ring
          _ ≤ 4*c/ε := by
              rw [div_le_div_iff₀ (by linarith) hε]; nlinarith
      calc |gapsw80_t70_zeroSideTerm F (ρ j) σ| * Complex.normSq (ρ j)
          ≤ (4*c/ε) * 2 := mul_le_mul hzconst hns2.le (hρ0 j).le (by positivity)
        _ = 2*(4*c/ε) := by ring
        _ ≤ M := by
            rw [hM_def]
            have h1 : (0:ℝ) ≤ 2*((2*σ-1)+9*c*σ^2/ε) := by
              have : (0:ℝ) < 2*σ-1 := by linarith
              positivity
            linarith
  exact Summable.of_norm_bounded (hsum.mul_left M)
    (fun j => by rw [Real.norm_eq_abs]; exact hbound j)

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t70_zeroSide_at_half_term {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    {ρ : ℂ} (hρ1 : 0 < ρ.re) (hρ2 : ρ.re < 1) :
    gapsw80_t70_zeroSideTerm F ρ (1 / 2)
      = gapsw80_t21_zeroKernelTransform F ρ := by
  have _em := Classical.em
  have hFeven := hF.2.1
  obtain ⟨c, ε, hc, hε, hdecay⟩ := hF.2.2.2.2.1
  set a : ℝ := ρ.re - 1/2 with ha_def
  have ha : |a| < 1/2 := by rw [ha_def, abs_lt]; constructor <;> linarith
  set γ : ℝ := ρ.im with hγ_def
  set g : ℝ → ℝ := fun x => F x * Real.exp (a * x) * Real.cos (γ * x) with hg_def

  have hpt : ∀ x, |g x| ≤ c * Real.exp (-(ε * |x|)) := fun x => by
    simp only [hg_def, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hax : a * x ≤ (1/2) * |x| :=
      (le_abs_self _).trans ((abs_mul a x).symm ▸
        mul_le_mul_of_nonneg_right ha.le (abs_nonneg _))
    calc |F x| * Real.exp (a * x) * |Real.cos (γ * x)|
        ≤ c * Real.exp (-(1/2+ε) * |x|) * Real.exp ((1/2) * |x|) * 1 := by
          apply mul_le_mul _ (Real.abs_cos_le_one _) (abs_nonneg _)
            (mul_nonneg (mul_nonneg hc.le (Real.exp_pos _).le) (Real.exp_pos _).le)
          exact mul_le_mul (hdecay x) (Real.exp_le_exp.mpr hax)
            (Real.exp_pos _).le (mul_nonneg hc.le (Real.exp_pos _).le)
      _ = c * Real.exp (-(ε * |x|)) := by
          rw [mul_one, mul_assoc, ← Real.exp_add]; ring_nf
  have hexp_Ici : IntegrableOn (fun x : ℝ => Real.exp (-(ε * |x|))) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (exp_neg_integrableOn_Ioi 0 hε).congr_fun
      (fun x hx => by beta_reduce; rw [abs_of_pos hx, neg_mul]) measurableSet_Ioi
  have hexp_Iic : IntegrableOn (fun x : ℝ => Real.exp (-(ε * |x|))) (Set.Iic 0) := by
    have := hexp_Ici.comp_neg
    rw [Set.neg_Ici, _root_.neg_zero] at this
    exact this.congr_fun (fun x _ => by beta_reduce; rw [abs_neg]) measurableSet_Iic
  have hmaj : Integrable (fun x : ℝ => c * Real.exp (-(ε * |x|))) := by
    apply Integrable.const_mul
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
    exact hexp_Iic.union (hexp_Ici.mono_set Set.Ioi_subset_Ici_self)
  have hg_int : Integrable g := by
    refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hF.1.continuous.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hpt x

  rw [gapsw80_t21_zeroKernelTransform_pin, ← ha_def, ← hγ_def,
    show (fun x => F x * Real.exp (a * x) * Real.cos (γ * x)) = g from rfl,
    ← setIntegral_univ (μ := volume), ← Set.Iic_union_Ioi (a := (0:ℝ)),
    setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hg_int.integrableOn hg_int.integrableOn]
  have hgneg : ∀ x, g (-x) = F x * Real.exp (-(a * x)) * Real.cos (γ * x) := fun x => by
    simp only [hg_def, hFeven x, mul_neg, Real.cos_neg, neg_mul]
  have hIic : ∫ x in Set.Iic (0:ℝ), g x
      = ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(a * x)) * Real.cos (γ * x) := by
    have h := (integral_comp_neg_Ioi 0 g).symm
    simp only [_root_.neg_zero] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun x _ => hgneg x)]
  rw [hIic]

  unfold gapsw80_t70_zeroSideTerm
  have hexp_eq : ∀ x,
      Real.exp (-((1/2 - ρ.re) * x)) + Real.exp (-((1/2 + ρ.re - 1) * x))
      = Real.exp (a * x) + Real.exp (-(a * x)) := fun x => by
    simp only [ha_def]; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => by
    rw [hexp_eq x, mul_add, add_mul])]
  rw [integral_add (hg_int.integrableOn) ?_]
  · simp only [hg_def]; ring
  ·
    refine (hmaj.integrableOn).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hF.1.continuous.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg)).mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable.restrict
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hax : -(a * x) ≤ (1/2) * |x| := by
        have := (neg_le_abs (a*x)).trans
          ((abs_mul a x).symm ▸ mul_le_mul_of_nonneg_right ha.le (abs_nonneg _))
        linarith
      calc |F x| * Real.exp (-(a * x)) * |Real.cos (γ * x)|
          ≤ c * Real.exp (-(1/2+ε) * |x|) * Real.exp ((1/2) * |x|) * 1 := by
            apply mul_le_mul _ (Real.abs_cos_le_one _) (abs_nonneg _)
              (mul_nonneg (mul_nonneg hc.le (Real.exp_pos _).le) (Real.exp_pos _).le)
            exact mul_le_mul (hdecay x) (Real.exp_le_exp.mpr hax)
              (Real.exp_pos _).le (mul_nonneg hc.le (Real.exp_pos _).le)
        _ = c * Real.exp (-(ε * |x|)) := by
            rw [mul_one, mul_assoc, ← Real.exp_add]; ring_nf

end Aux
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

set_option maxHeartbeats 12800000 in

theorem gapsw80_t70_zero_eval_at_sigma
    {K : Type} [Field K] [NumberField K]
    {B : ℂ} {ρ : ℕ → ℂ}
    (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    (hexp : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
      logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
        = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
    {F : ℝ → ℝ} (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hFC2 : gapsw80_t69_KernelC2Decay F)
    {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun t : ℝ =>
        (B + ∑' j, (((σ : ℂ) + (t : ℂ) * I - ρ j)⁻¹ + (ρ j)⁻¹)).re
          * (∫ x : ℝ, F x * Real.cos (t * x)))
    ∧ (1 / Real.pi) * ∫ t : ℝ,
        (B + ∑' j, (((σ : ℂ) + (t : ℂ) * I - ρ j)⁻¹ + (ρ j)⁻¹)).re
          * (∫ x : ℝ, F x * Real.cos (t * x))
      = gapsw80_t70_zeroSideSigma F ρ σ := by
  have _em := Classical.em
  have hFh_nn : ∀ t, (0:ℝ) ≤ ∫ x : ℝ, F x * Real.cos (t * x) := hF.2.2.2.2.2
  set Fh : ℝ → ℝ := fun t => ∫ x : ℝ, F x * Real.cos (t * x) with hFh_def
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos

  have hRe : ∀ t : ℝ, ((σ:ℂ)+(t:ℂ)*I).re = σ := fun t => by
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
      _root_.neg_zero, add_zero]
  have hs0 : ∀ t : ℝ, (σ:ℂ)+(t:ℂ)*I ≠ 0 := fun t h => by
    have := hRe t; rw [h, Complex.zero_re] at this; linarith
  have hs1 : ∀ t : ℝ, (σ:ℂ)+(t:ℂ)*I ≠ 1 := fun t h => by
    have := hRe t; rw [h, Complex.one_re] at this; linarith
  have hsρ : ∀ (t : ℝ) j, (σ:ℂ)+(t:ℂ)*I ≠ ρ j := fun t j h => by
    have := hRe t; rw [h] at this; linarith [(hstrip j).2]
  have hs1ρ : ∀ (t : ℝ) j, 1-((σ:ℂ)+(t:ℂ)*I) ≠ ρ j := fun t j h => by
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, hRe t] at this
    linarith [(hstrip j).1]
  have ha1 : ∀ j, (0:ℝ) < σ-(ρ j).re := fun j => by linarith [(hstrip j).2]
  have ha2 : ∀ j, (0:ℝ) < σ+(ρ j).re-1 := fun j => by linarith [(hstrip j).1]

  obtain ⟨c₀, ε₀, hc₀, hε₀, hdec₀⟩ := hF.2.2.2.2.1
  have hFec_int : ∀ {a' : ℝ}, 0 < a' → ∀ b : ℝ, IntegrableOn
      (fun x => F x * Real.exp (-(a'*x)) * Real.cos (b*x)) (Set.Ioi 0) := by
    intro a' ha' b
    refine ((exp_neg_integrableOn_Ioi 0 (show (0:ℝ)<1/2+ε₀ from by linarith)).const_mul
      c₀).mono' ((hF.1.continuous.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg)).mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxp : (0:ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |F x| * Real.exp (-(a'*x)) * |Real.cos (b*x)|
        ≤ c₀*Real.exp (-(1/2+ε₀)*|x|) * 1 * 1 :=
          mul_le_mul (mul_le_mul (hdec₀ x)
            (Real.exp_le_one_iff.mpr (by nlinarith)) (Real.exp_pos _).le
            (mul_nonneg hc₀.le (Real.exp_pos _).le))
            (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ = c₀ * Real.exp (-((1/2+ε₀)*x)) := by rw [abs_of_pos hxp]; ring
      _ = _ := by rw [neg_mul]

  set fⱼ : ℕ → ℝ → ℝ := fun j t =>
    (1/2) * ((σ-(ρ j).re)/((σ-(ρ j).re)^2+(t-(ρ j).im)^2)
      + (σ+(ρ j).re-1)/((σ+(ρ j).re-1)^2+(t-(-(ρ j).im))^2)) * Fh t with hfj_def
  have hfj_nn : ∀ j t, 0 ≤ fⱼ j t := fun j t => by
    simp only [hfj_def]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg (ha1 j).le (by positivity))
        (div_nonneg (ha2 j).le (by positivity)))) (hFh_nn t)
  have hp1 : ∀ j, _ := fun j => gapsw80_t70_poisson_shifted hF (ha1 j) (ρ j).im
  have hp2 : ∀ j, _ := fun j => gapsw80_t70_poisson_shifted hF (ha2 j) (-(ρ j).im)
  have hfj_int : ∀ j, Integrable (fⱼ j) := fun j => by
    refine (((hp1 j).1.add (hp2 j).1).const_mul (1/2)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    show (1:ℝ)/2 * ((σ-(ρ j).re)/((σ-(ρ j).re)^2+(t-(ρ j).im)^2) * Fh t
      + (σ+(ρ j).re-1)/((σ+(ρ j).re-1)^2+(t-(-(ρ j).im))^2) * Fh t) = fⱼ j t
    simp only [hfj_def]; ring

  have hfj_val : ∀ j, ∫ t, fⱼ j t
      = Real.pi * gapsw80_t70_zeroSideTerm F (ρ j) σ := fun j => by
    have hsplit : ∫ t, fⱼ j t
        = (1/2) * ((∫ t, ((σ-(ρ j).re)/((σ-(ρ j).re)^2+(t-(ρ j).im)^2)) * Fh t)
          + ∫ t, ((σ+(ρ j).re-1)/((σ+(ρ j).re-1)^2
            +(t-(-(ρ j).im))^2)) * Fh t) := by
      rw [← integral_add (hp1 j).1 (hp2 j).1, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
        simp only [hfj_def, hFh_def]; ring)
    have hZsplit : gapsw80_t70_zeroSideTerm F (ρ j) σ
        = (∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((σ-(ρ j).re)*x))
            * Real.cos ((ρ j).im*x))
          + ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((σ+(ρ j).re-1)*x))
            * Real.cos ((ρ j).im*x) := by
      unfold gapsw80_t70_zeroSideTerm
      rw [← integral_add (hFec_int (ha1 j) (ρ j).im) (hFec_int (ha2 j) (ρ j).im)]
      exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
    have hv1 := (hp1 j).2; have hv2 := (hp2 j).2
    rw [show (fun x => F x * Real.exp (-((σ+(ρ j).re-1)*x)) * Real.cos (-(ρ j).im*x))
        = (fun x => F x * Real.exp (-((σ+(ρ j).re-1)*x)) * Real.cos ((ρ j).im*x))
      from funext fun x => by rw [neg_mul, Real.cos_neg]] at hv2
    rw [hsplit, hZsplit]; try simp only [hFh_def] at hv1 hv2
    have h1 : ∫ t, ((σ-(ρ j).re)/((σ-(ρ j).re)^2+(t-(ρ j).im)^2)) * Fh t
        = Real.pi * (2*∫ x in Set.Ioi (0:ℝ),
            F x * Real.exp (-((σ-(ρ j).re)*x)) * Real.cos ((ρ j).im*x)) := by
      field_simp at hv1 ⊢; linarith
    have h2 : ∫ t, ((σ+(ρ j).re-1)/((σ+(ρ j).re-1)^2+(t-(-(ρ j).im))^2)) * Fh t
        = Real.pi * (2*∫ x in Set.Ioi (0:ℝ),
            F x * Real.exp (-((σ+(ρ j).re-1)*x)) * Real.cos ((ρ j).im*x)) := by
      field_simp at hv2 ⊢; linarith
    rw [h1, h2]; ring

  have hfj_norm : ∀ j, ∫ t, ‖fⱼ j t‖ = Real.pi * gapsw80_t70_zeroSideTerm F (ρ j) σ :=
    fun j => (integral_congr_ae (Filter.Eventually.of_forall fun t =>
      Real.norm_of_nonneg (hfj_nn j t))).trans (hfj_val j)
  have hZsum := gapsw80_t70_zeroSide_summable hF hFC2 hstrip hsum hσ.le
  have hfj_sum : Summable (fun j => ∫ t, ‖fⱼ j t‖) := by
    simp_rw [hfj_norm]; exact hZsum.mul_left Real.pi
  have hZj_nn : ∀ j, (0:ℝ) ≤ gapsw80_t70_zeroSideTerm F (ρ j) σ := fun j => by
    have h : (0:ℝ) ≤ ∫ t, fⱼ j t :=
      MeasureTheory.integral_nonneg (fun t => hfj_nn j t)
    rw [hfj_val j] at h; nlinarith [hπ]

  have hpt : ∀ t : ℝ, (B + ∑' j, (((σ:ℂ)+(t:ℂ)*I - ρ j)⁻¹ + (ρ j)⁻¹)).re * Fh t
      = ∑' j, fⱼ j t := fun t => by
    have hBfree := gapsw80_t70_hexp_Bfree (K := K) hstrip hsum hexp
      (hs0 t) (hs1 t) (hsρ t) (hs1ρ t)
    have hsum2 : Summable (fun j =>
        (((σ:ℂ)+(t:ℂ)*I - ρ j)⁻¹ - (1-((σ:ℂ)+(t:ℂ)*I) - ρ j)⁻¹)) :=
      ((gapsw80_t70_summable_hadamard_term hstrip hsum (hsρ t)).sub
        (gapsw80_t70_summable_hadamard_term hstrip hsum (hs1ρ t))).congr
        (fun j => by ring)
    rw [hBfree, show ((1:ℂ)/2) = ((1/2:ℝ):ℂ) from by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_tsum hsum2, ← tsum_mul_left,
      ← tsum_mul_right]
    refine tsum_congr fun j => ?_
    simp only [hfj_def, Complex.sub_re, Complex.inv_re, Complex.normSq_apply,
      Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      mul_zero, mul_one, zero_mul, zero_add, add_zero, zero_sub, sub_zero]
    ring_nf

  have hswap : ∫ t, ∑' j, fⱼ j t = ∑' j, ∫ t, fⱼ j t :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hfj_int hfj_sum).symm
  have hval : ∫ t, ∑' j, fⱼ j t = Real.pi * gapsw80_t70_zeroSideSigma F ρ σ := by
    rw [hswap]; unfold gapsw80_t70_zeroSideSigma
    rw [← tsum_mul_left]; exact tsum_congr hfj_val

  have hfj_meas : ∀ j, AEMeasurable (fⱼ j) volume := fun j => (hfj_int j).1.aemeasurable
  have hlint_fin : ∑' j, ∫⁻ t, ENNReal.ofReal (fⱼ j t) < ⊤ := by
    have heq : ∀ j, ∫⁻ t, ENNReal.ofReal (fⱼ j t)
        = ENNReal.ofReal (∫ t, fⱼ j t) := fun j =>
      (ofReal_integral_eq_lintegral_ofReal (hfj_int j)
        (Filter.Eventually.of_forall (hfj_nn j))).symm
    simp_rw [heq, hfj_val]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg hπ.le (hZj_nn j)) (hZsum.mul_left Real.pi)]
    exact ENNReal.ofReal_lt_top
  have htsum_nn : ∀ t, 0 ≤ ∑' j, fⱼ j t := fun t => tsum_nonneg (fun j => hfj_nn j t)

  have henn_meas : AEMeasurable (fun t => ∑' j, ENNReal.ofReal (fⱼ j t)) volume :=
    AEMeasurable.ennreal_tsum (fun j => (hfj_meas j).ennreal_ofReal)
  have hlint : ∫⁻ t, ∑' j, ENNReal.ofReal (fⱼ j t) < ⊤ := by
    rw [lintegral_tsum (fun j => (hfj_meas j).ennreal_ofReal)]
    exact hlint_fin
  have hae_fin : ∀ᵐ t ∂volume, ∑' j, ENNReal.ofReal (fⱼ j t) ≠ ⊤ :=
    (ae_lt_top' henn_meas hlint.ne).mono (fun t ht => ht.ne)
  have heq_ae : (fun t => ∑' j, fⱼ j t)
      =ᶠ[ae volume] fun t => (∑' j, ENNReal.ofReal (fⱼ j t)).toReal := by
    filter_upwards [hae_fin] with t ht
    rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun j => (ENNReal.toReal_ofReal (hfj_nn j t)).symm
  have htsum_int : Integrable (fun t => ∑' j, fⱼ j t) := by
    refine ⟨(henn_meas.ennreal_toReal.aestronglyMeasurable).congr heq_ae.symm, ?_⟩
    rw [HasFiniteIntegral,
      show (fun t => ‖∑' j, fⱼ j t‖ₑ) = fun t => ENNReal.ofReal (∑' j, fⱼ j t) from
        funext fun t => by rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (htsum_nn t)]]
    refine lt_of_le_of_lt ?_ hlint
    refine lintegral_mono_ae (heq_ae.mono fun t ht => ?_)
    rw [show (∑' j, fⱼ j t) = (∑' j, ENNReal.ofReal (fⱼ j t)).toReal from ht]
    exact ENNReal.ofReal_toReal_le

  refine ⟨htsum_int.congr (Filter.Eventually.of_forall fun t => (hpt t).symm), ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hval]
  field_simp

private def gapsw80_t70_s2_identity (K : Type) [Field K] [NumberField K]
    (B : ℂ) (ρ : ℕ → ℂ) (F : ℝ → ℝ) (σ : ℝ) : Prop :=
  Integrable (fun t : ℝ =>
    (((finrank ℚ K : ℝ) / 2) * (logDeriv Gammaℂ ((σ : ℂ) + (t : ℂ) * I)).re)
      * (∫ x : ℝ, F x * Real.cos (t * x)))
  ∧ ((1 / Real.pi) * ∫ t : ℝ,
        (((finrank ℚ K : ℝ) / 2) * (logDeriv Gammaℂ ((σ : ℂ) + (t : ℂ) * I)).re)
          * (∫ x : ℝ, F x * Real.cos (t * x)))
      - gapsw80_t70_zeroSideSigma F ρ σ
    = - Real.log |(discr K : ℝ)|
      - ((2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(σ * x)))
         + (2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((σ - 1) * x))))
      + 2 * (∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ,
          Real.log (Ideal.absNorm p.1.1 : ℕ)
            * F (((p.2 : ℝ) + 1) * Real.log (Ideal.absNorm p.1.1 : ℕ))
            * ((Ideal.absNorm p.1.1 : ℕ) : ℝ) ^ (-(((p.2 : ℝ) + 1) * σ)))

set_option maxHeartbeats 6400000 in

theorem gapsw80_t70_s2_identity_at_sigma
    (hd : gapsw80_t21_DedekindZetaEulerExpansion)
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    {B : ℂ} {ρ : ℕ → ℂ}
    (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹))
    (hexp : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
      logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
        = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹))
    {F : ℝ → ℝ} (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hFC2 : gapsw80_t69_KernelC2Decay F)
    {σ : ℝ} (hσ : 1 < σ) :
    gapsw80_t70_s2_identity K B ρ F σ := by
  have _em := Classical.em
  have ⟨hs1_int, hs1_eq⟩ :=
    gapsw80_t68_ReIntegratedIdentityAtSigma hd K B ρ hstrip hsum hexp F hF hσ
  have ⟨hz_int, hz_eq⟩ :=
    gapsw80_t70_zero_eval_at_sigma (K := K) hstrip hsum hexp hF hFC2 hσ
  set Fh : ℝ → ℝ := fun t => ∫ x : ℝ, F x * Real.cos (t * x) with hFh_def
  set Ar : ℝ → ℝ := fun t =>
    ((finrank ℚ K : ℝ)/2) * (logDeriv Gammaℂ ((σ:ℂ)+(t:ℂ)*I)).re with hAr_def
  set Zr : ℝ → ℝ := fun t =>
    (B + ∑' j, (((σ:ℂ)+(t:ℂ)*I - ρ j)⁻¹ + (ρ j)⁻¹)).re with hZr_def

  have hAr_int : Integrable (fun t => Ar t * Fh t) := by
    refine (hs1_int.add hz_int).congr (Filter.Eventually.of_forall fun t => ?_)
    show (Ar t - Zr t) * Fh t + Zr t * Fh t = Ar t * Fh t
    ring
  refine ⟨hAr_int, ?_⟩
  have hsplit : ∫ t, Ar t * Fh t
      = (∫ t, (Ar t - Zr t) * Fh t) + ∫ t, Zr t * Fh t := by
    rw [← integral_add hs1_int hz_int]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  have hfinal :
      (1/Real.pi) * (∫ t, Ar t * Fh t) - gapsw80_t70_zeroSideSigma F ρ σ
      = (1/Real.pi) * (∫ t, (Ar t - Zr t) * Fh t) := by
    rw [hsplit, mul_add, hz_eq]; ring
  show (1/Real.pi) * (∫ t, Ar t * Fh t) - gapsw80_t70_zeroSideSigma F ρ σ = _
  rw [hfinal]; exact hs1_eq

set_option maxHeartbeats 6400000 in

theorem gapsw80_t70_zeroSideSigma_at_half {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hFC2 : gapsw80_t69_KernelC2Decay F) {ρ : ℕ → ℂ}
    (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹)) :
    gapsw80_t70_zeroSideSigma F ρ (1 / 2) = gapsw80_t21_zeroKernelSum F ρ := by
  have _em := Classical.em
  unfold gapsw80_t70_zeroSideSigma
  rw [gapsw80_t21_zeroKernelSum_pin]
  exact tsum_congr (fun j =>
    gapsw80_t70_zeroSide_at_half_term hF (hstrip j).1 (hstrip j).2)

def gapsw80_t70_AnalyticExtensionIdentityC2 : Prop :=
  gapsw80_t62_ArchGammaKernelIdentityCorrected →
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K],
    ∀ (B : ℂ) (ρ : ℕ → ℂ),
      (∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) →
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv
            (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
          = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)) →
      ∀ (F : ℝ → ℝ), gapsw50_t2_OdlyzkoAdmissibleKernel F →
        gapsw80_t69_KernelC2Decay F →
        (∀ σ : ℝ, 1 < σ → gapsw80_t70_s2_identity K B ρ F σ) →
        Real.log |(discr K : ℝ)| =
          (gapsw80_t18_archTermDerived F (finrank ℚ K)
            + (finrank ℚ K : ℝ) * Real.log 2)
            + 2 * gapsw52_t2_OdlyzkoPrimeIdealSum F K
            + gapsw80_t21_zeroKernelSum F ρ

set_option maxHeartbeats 3200000 in

theorem gapsw80_t70_analyticExtensionIdentityC2_pin :
    gapsw80_t70_AnalyticExtensionIdentityC2 =
      (gapsw80_t62_ArchGammaKernelIdentityCorrected →
       ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K],
        ∀ (B : ℂ) (ρ : ℕ → ℂ),
          (∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) →
          Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
          (∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
            logDeriv
                (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
              = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)) →
          ∀ (F : ℝ → ℝ), gapsw50_t2_OdlyzkoAdmissibleKernel F →
            gapsw80_t69_KernelC2Decay F →
            (∀ σ : ℝ, 1 < σ → gapsw80_t70_s2_identity K B ρ F σ) →
            Real.log |(discr K : ℝ)| =
              (gapsw80_t18_archTermDerived F (finrank ℚ K)
                + (finrank ℚ K : ℝ) * Real.log 2)
                + 2 * gapsw52_t2_OdlyzkoPrimeIdealSum F K
                + gapsw80_t21_zeroKernelSum F ρ) := by
  have _em := Classical.em
  rfl

set_option maxHeartbeats 6400000 in

theorem gapsw80_t70_D2bpppb_implies_D2bppp
    (hb'''b : gapsw80_t70_AnalyticExtensionIdentityC2) :
    gapsw80_t69_ContourPairedExplicitFormulaC2 := by
  have _em := Classical.em
  intro hc' hd K _ _ _ B ρ hstrip hsum hexp F hF hFC2
  exact hb'''b hc' K B ρ hstrip hsum hexp F hF hFC2
    (fun σ hσ => gapsw80_t70_s2_identity_at_sigma
      hd hstrip hsum hexp hF hFC2 hσ)

end FLT.Gapsw80T70D2bpppZeroSideEvalSubDecomp
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T71D2bpppbAnalyticContinuationProof

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T64D2fGaussianMollificationProof
open FLT.Gapsw80T66D2caiDigammaSeriesProof
open FLT.Gapsw80T68D2bppExplicitFormulaSubDecomp
open FLT.Gapsw80T69AdmC2RemintZktSummable
open FLT.Gapsw80T70D2bpppZeroSideEvalSubDecomp
open FLT.Gapsw80T27D2d0EulerProductAncestor
open FLT.Gapsw80T28D2d0aSummabilityProof
p2m_open "NumberField P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField NumberField.InfinitePlace P2MW.S_NumberField_archTermDerived_le_log_abs_discr.NumberField.InfinitePlace Module P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Module Complex P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Complex MeasureTheory P2MW.S_NumberField_archTermDerived_le_log_abs_discr.MeasureTheory"
p2m_open_scoped "Topology P2MW.S_NumberField_archTermDerived_le_log_abs_discr.Topology"

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t71_laplace_analytic {F : ℝ → ℝ} (hF : Continuous F)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hdecay : ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))
    (γ : ℝ) :
    AnalyticOnNhd ℂ
      (fun s : ℂ => ∫ x in Set.Ioi (0:ℝ),
        (F x : ℂ) * Complex.exp (-(s * x)) * (Real.cos (γ * x) : ℂ))
      {s : ℂ | -(1 / 2 + ε) < s.re} := by
  have _em := Classical.em
  set fd : ℂ → ℝ → ℂ :=
    fun s x => (F x : ℂ) * Complex.exp (-(s * x)) * (Real.cos (γ * x) : ℂ)
  set fd' : ℂ → ℝ → ℂ :=
    fun s x => (F x : ℂ) * ((-(x:ℂ)) * Complex.exp (-(s * x))) * (Real.cos (γ * x) : ℂ)
  have hU_open : IsOpen {s : ℂ | -(1/2+ε) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun s₀ hs₀ => ?_) hU_open

  set r : ℝ := (s₀.re + (1/2+ε)) / 2
  have hr : 0 < r := by
    have : -(1/2+ε) < s₀.re := hs₀
    simp only [r]; linarith
  set a : ℝ := s₀.re - r + (1/2+ε)
  have ha : 0 < a := by simp only [a, r]; have : -(1/2+ε) < s₀.re := hs₀; linarith
  have hball_re : ∀ s ∈ Metric.ball s₀ r, -(1/2+ε) < s.re - r + (1/2+ε) ∧
      s.re - r + (1/2+ε) ≥ 0 ∧ a ≤ s.re + (1/2+ε) := fun s hsb => by
    have hd : ‖s - s₀‖ < r := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hsb
    have hre : |s.re - s₀.re| < r :=
      lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hd
    have := abs_lt.mp hre
    refine ⟨?_, ?_, ?_⟩ <;> simp only [a, r] at * <;> linarith

  have hfd_cont : ∀ s : ℂ, Continuous (fd s) := fun s =>
    ((Complex.continuous_ofReal.comp hF).mul ((Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg)))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)))
  have hfd'_cont : ∀ s : ℂ, Continuous (fd' s) := fun s =>
    ((Complex.continuous_ofReal.comp hF).mul (((Complex.continuous_ofReal).neg).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)))
  have hF_meas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (fd s)
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    Filter.Eventually.of_forall (fun s => (hfd_cont s).aestronglyMeasurable)
  have hF'_meas : AEStronglyMeasurable (fd' s₀) (volume.restrict (Set.Ioi (0:ℝ))) :=
    (hfd'_cont s₀).aestronglyMeasurable

  have hpt : ∀ s : ℂ, ∀ x : ℝ, 0 < x →
      ‖fd s x‖ ≤ c * Real.exp (-((s.re + (1/2+ε)) * x)) := fun s x hx => by
    simp only [fd, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    calc |F x| * Real.exp (-(s.re * x)) * |Real.cos (γ*x)|
        ≤ (c * Real.exp (-(1/2+ε)*|x|)) * Real.exp (-(s.re * x)) * 1 :=
          mul_le_mul (mul_le_mul (hdecay x) le_rfl (Real.exp_pos _).le
            (le_trans (abs_nonneg _) (hdecay x))) (Real.abs_cos_le_one _)
            (abs_nonneg _) (mul_nonneg (mul_nonneg hc.le (Real.exp_pos _).le)
              (Real.exp_pos _).le)
      _ = c * Real.exp (-((s.re + (1/2+ε)) * x)) := by
          rw [abs_of_pos hx, mul_one, mul_assoc, ← Real.exp_add]; ring_nf

  have hmaj0 : IntegrableOn (fun x => c * Real.exp (-(a * x))) (Set.Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 ha).congr_fun
      (fun x _ => by rw [neg_mul]) measurableSet_Ioi).const_mul c
  have hF_int : IntegrableOn (fd s₀) (Set.Ioi 0) := by
    refine hmaj0.mono' (hfd_cont s₀).aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    refine (hpt s₀ x hx).trans ?_
    have hre := (hball_re s₀ (Metric.mem_ball_self hr)).2.2
    have hx0 : (0:ℝ) < x := hx
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc.le
    nlinarith

  set bound : ℝ → ℝ := fun x => x * (c * Real.exp (-(a * x)))
  have h_bound : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ∀ s ∈ Metric.ball s₀ r, ‖fd' s x‖ ≤ bound x := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx s hsb => ?_)
    have hx0 : (0:ℝ) < x := hx
    have heq : ‖fd' s x‖ = |F x| * (x * Real.exp (-(s.re * x))) * |Real.cos (γ*x)| := by
      simp only [fd', norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg,
        Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, abs_of_pos hx0]
    rw [heq]; simp only [bound]
    calc |F x| * (x * Real.exp (-(s.re * x))) * |Real.cos (γ*x)|
        ≤ (c * Real.exp (-(1/2+ε)*x)) * (x * Real.exp (-(s.re * x))) * 1 := by
          apply mul_le_mul _ (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
          refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
          exact (hdecay x).trans_eq (by rw [abs_of_pos hx0])
      _ = x * (c * Real.exp (-((s.re+(1/2+ε))*x))) := by
          rw [mul_one, mul_assoc c, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
          ring_nf
      _ ≤ x * (c * Real.exp (-(a * x))) := by
          have hre := (hball_re s hsb).2.2
          have : -(s.re+(1/2+ε))*x ≤ -(a*x) := by nlinarith
          gcongr

  have bound_integrable : IntegrableOn bound (Set.Ioi 0) := by
    have hmaj1 : IntegrableOn (fun x => (2/a) * (c * Real.exp (-(a/2 * x))))
        (Set.Ioi 0) :=
      (((exp_neg_integrableOn_Ioi 0 (by positivity : (0:ℝ) < a/2)).congr_fun
        (fun x _ => by rw [neg_mul]) measurableSet_Ioi).const_mul c).const_mul (2/a)
    refine hmaj1.mono' ((continuous_id.mul (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul
      continuous_id).neg))).aestronglyMeasurable.restrict)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hx
    have hxe : x ≤ (2/a) * Real.exp (a/2 * x) := by
      have := Real.add_one_le_exp (a/2 * x)
      have h1 : a/2 * x ≤ Real.exp (a/2 * x) := by linarith [mul_nonneg ha.le hx0.le]
      calc x = (2/a) * (a/2 * x) := by field_simp
        _ ≤ (2/a) * Real.exp (a/2 * x) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    simp only [bound, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    calc x * (c * Real.exp (-(a*x)))
        ≤ ((2/a) * Real.exp (a/2*x)) * (c * Real.exp (-(a*x))) :=
          mul_le_mul_of_nonneg_right hxe (by positivity)
      _ = (2/a) * (c * Real.exp (-(a/2*x))) := by
          rw [mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; ring_nf

  have h_diff : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ∀ s ∈ Metric.ball s₀ r, HasDerivAt (fd · x) (fd' s x) s := by
    refine Filter.Eventually.of_forall (fun x s _ => ?_)
    have he : HasDerivAt (fun s : ℂ => Complex.exp (-(s * x)))
        ((-(x:ℂ)) * Complex.exp (-(s * x))) s := by
      have h1 : HasDerivAt (fun s : ℂ => -(s * (x:ℂ))) (-(x:ℂ)) s :=
        ((hasDerivAt_id s).mul_const (x:ℂ)).neg.congr_deriv (by ring)
      have := h1.cexp
      convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | ring
    simp only [fd, fd']
    exact (he.const_mul (F x : ℂ)).mul_const (Real.cos (γ*x) : ℂ)
  have ⟨_, hdA⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s₀ hr) hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  exact hdA.differentiableAt.differentiableWithinAt

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t71_zeroSideTerm_analytic {F : ℝ → ℝ} (hF : Continuous F)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hdecay : ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))
    {ρ : ℂ} (hρ1 : 0 < ρ.re) (hρ2 : ρ.re < 1) {ε' : ℝ} (hε' : ε' < ε) :
    AnalyticOnNhd ℂ
      (fun s : ℂ => ∫ x in Set.Ioi (0:ℝ),
        (F x : ℂ) * (Complex.exp (-((s - ρ.re) * x)) + Complex.exp (-((s + ρ.re - 1) * x)))
          * (Real.cos (ρ.im * x) : ℂ))
      {s : ℂ | 1 / 2 - ε' < s.re} := by
  have _em := Classical.em
  have hL := gapsw80_t71_laplace_analytic hF hc hε hdecay ρ.im

  have hmap1 : Set.MapsTo (fun s : ℂ => s - (ρ.re:ℂ))
      {s : ℂ | 1/2 - ε' < s.re} {s : ℂ | -(1/2+ε) < s.re} := fun s hs => by
    simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.ofReal_re] at *; linarith
  have hmap2 : Set.MapsTo (fun s : ℂ => s + (ρ.re:ℂ) - 1)
      {s : ℂ | 1/2 - ε' < s.re} {s : ℂ | -(1/2+ε) < s.re} := fun s hs => by
    simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.one_re] at *; linarith
  have hV_open : IsOpen {s : ℂ | 1/2 - ε' < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hL1 := hL.comp ((analyticOnNhd_id (𝕜:=ℂ) (E:=ℂ)).sub analyticOnNhd_const) hmap1
  have hL2 := hL.comp (((analyticOnNhd_id (𝕜:=ℂ) (E:=ℂ)).add analyticOnNhd_const).sub
    analyticOnNhd_const) hmap2
  refine (hL1.add hL2).congr hV_open (fun s hs => ?_)

  have hint : ∀ w : ℂ, -(1/2+ε) < w.re → IntegrableOn
      (fun x => (F x:ℂ) * Complex.exp (-(w * x)) * (Real.cos (ρ.im*x):ℂ))
      (Set.Ioi 0) := fun w hw => by
    refine (((exp_neg_integrableOn_Ioi 0 (show (0:ℝ) < w.re + (1/2+ε) by linarith)
      ).congr_fun (fun x _ => by rw [neg_mul]) measurableSet_Ioi).const_mul c).mono'
      (((Complex.continuous_ofReal.comp hF).mul ((Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)))).mul
        (Complex.continuous_ofReal.comp (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)))).aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hx
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    calc |F x| * Real.exp (-(w.re * x)) * |Real.cos (ρ.im*x)|
        ≤ (c * Real.exp (-(1/2+ε)*|x|)) * Real.exp (-(w.re * x)) * 1 :=
          mul_le_mul (mul_le_mul (hdecay x) le_rfl (Real.exp_pos _).le
            (le_trans (abs_nonneg _) (hdecay x))) (Real.abs_cos_le_one _)
            (abs_nonneg _) (by positivity)
      _ = c * Real.exp (-((w.re + (1/2+ε)) * x)) := by
          rw [abs_of_pos hx0, mul_one, mul_assoc, ← Real.exp_add]; ring_nf
  simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, id_eq]
  rw [← integral_add (hint _ (hmap1 hs)) (hint _ (hmap2 hs))]
  exact (setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)).symm

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t71_psi_deriv_series {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => ((n:ℂ)+s)⁻¹ ^ 2) (deriv (logDeriv Complex.Gamma) s)
    ∧ ‖deriv (logDeriv Complex.Gamma) s‖ ≤ ∑' n : ℕ, ((n:ℝ)+s.re)⁻¹ ^ 2 := by
  have _em := Classical.em
  set r : ℝ := s.re/2 with hr_def
  have hr : 0 < r := by positivity
  set U : Set ℂ := Metric.ball s r with hU_def
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hs_in : s ∈ U := Metric.mem_ball_self hr
  have hU_re : ∀ z ∈ U, r < z.re := fun z hz => by
    have hd : ‖z - s‖ < r := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
    have hre : |z.re - s.re| < r :=
      lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hd
    have := abs_lt.mp hre
    linarith [hr_def ▸ hr]
  set fₙ : ℕ → ℂ → ℂ := fun n z => 1/((n:ℂ)+1) - 1/((n:ℂ)+z) with hfₙ_def
  have hnz0 : ∀ n : ℕ, ∀ z ∈ U, (n:ℂ)+z ≠ 0 := fun n z hz h => by
    have h1 : ((n:ℂ)+z).re = 0 := by rw [h]; rfl
    simp only [Complex.add_re, Complex.natCast_re] at h1
    linarith [hU_re z hz, Nat.cast_nonneg (α := ℝ) n]

  have hfₙ_hasDeriv : ∀ n, ∀ z ∈ U, HasDerivAt (fₙ n) (((n:ℂ)+z)⁻¹^2) z := by
    intro n z hz
    have h1 : HasDerivAt (fun w : ℂ => (n:ℂ)+w) 1 z :=
      (hasDerivAt_id z).const_add (n:ℂ)
    have h2 := h1.inv (hnz0 n z hz)
    have h3 : HasDerivAt (fₙ n) (0 - (-1/((n:ℂ)+z)^2)) z := by
      refine (hasDerivAt_const z (1/((n:ℂ)+1))).sub ?_
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.inv_apply, one_div]
    refine h3.congr_deriv ?_
    rw [zero_sub, neg_div, neg_neg, one_div, inv_pow]
  have hfₙ_diff : ∀ n, DifferentiableOn ℂ (fₙ n) U := fun n z hz =>
    (hfₙ_hasDeriv n z hz).differentiableAt.differentiableWithinAt
  have hfₙ_deriv : ∀ n, ∀ z ∈ U, deriv (fₙ n) z = ((n:ℂ)+z)⁻¹^2 := fun n z hz =>
    (hfₙ_hasDeriv n z hz).deriv

  set C : ℝ := r + ‖s - 1‖ with hC_def
  set u : ℕ → ℝ := fun n => C / (((n:ℝ)+1) * ((n:ℝ)+r)) with hu_def
  have hfₙ_bd : ∀ n, ∀ z ∈ U, ‖fₙ n z‖ ≤ u n := fun n z hz => by
    have hn1 : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have heq : fₙ n z = (z-1) / (((n:ℂ)+1) * ((n:ℂ)+z)) := by
      simp only [fₙ]; field_simp [hn1, hnz0 n z hz]; ring
    rw [heq, norm_div, norm_mul]
    refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · calc ‖z-1‖ = ‖(z-s) + (s-1)‖ := by ring_nf
        _ ≤ ‖z-s‖ + ‖s-1‖ := norm_add_le _ _
        _ ≤ r + ‖s-1‖ := by
            refine add_le_add ?_ le_rfl
            rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hz).le
    · refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · rw [show ((n:ℂ)+1) = (((n:ℝ)+1:ℝ):ℂ) from by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      · calc ((n:ℝ)+r) ≤ ((n:ℝ)+z.re) := by linarith [hU_re z hz]
          _ = ((n:ℂ)+z).re := by simp [Complex.add_re, Complex.natCast_re]
          _ ≤ |((n:ℂ)+z).re| := le_abs_self _
          _ ≤ ‖(n:ℂ)+z‖ := Complex.abs_re_le_norm _
  have hu_sum : Summable u := by

    have hC_nn : 0 ≤ C := by positivity
    have hm : (0:ℝ) < min 1 r := lt_min one_pos hr
    have hcomp : ∀ n:ℕ, u n ≤ C / (((n:ℝ)+min 1 r)^2) := by
      intro n
      have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
      simp only [u]
      apply div_le_div_of_nonneg_left hC_nn (by positivity)
      rw [sq]
      exact mul_le_mul (by linarith [min_le_left 1 r]) (by linarith [min_le_right 1 r])
        (by positivity) (by linarith)
    refine Summable.of_nonneg_of_le (fun n => ?_) hcomp ?_
    · have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
      simp only [u]; positivity
    · refine (((Real.summable_one_div_nat_add_rpow (min 1 r) 2).mpr one_lt_two).congr
        (fun n => ?_)).mul_left C
      have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
      rw [abs_of_pos (by linarith), one_div]
      norm_num

  have hsd := hasSum_deriv_of_summable_norm hu_sum hfₙ_diff hU_open hfₙ_bd hs_in

  have htsum_eq : ∀ z ∈ U, (∑' n, fₙ n z)
      = logDeriv Complex.Gamma z + (Real.eulerMascheroniConstant:ℂ) :=
    fun z hz => (gapsw80_t66_hasSum_psi_series (hr.trans (hU_re z hz))).tsum_eq
  have hderiv_eq : deriv (fun w => ∑' n, fₙ n w) s
      = deriv (logDeriv Complex.Gamma) s := by
    have heq := Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (hU_open.mem_nhds hs_in) htsum_eq)
    rw [heq, deriv_add_const]
  rw [← hderiv_eq]

  have hsd' : HasSum (fun n : ℕ => ((n:ℂ)+s)⁻¹^2)
      (deriv (fun w => ∑' n, fₙ n w) s) := by
    refine hsd.congr_fun (fun n => ?_)
    exact (hfₙ_deriv n s hs_in).symm
  refine ⟨hsd', ?_⟩

  rw [← hsd'.tsum_eq]
  have hbd_n : ∀ n:ℕ, ‖((n:ℂ)+s)⁻¹^2‖ ≤ ((n:ℝ)+s.re)⁻¹^2 := fun n => by
    have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
    have hnsr : (0:ℝ) < (n:ℝ)+s.re := by linarith
    have hle : (n:ℝ)+s.re ≤ ‖(n:ℂ)+s‖ := by
      calc (n:ℝ)+s.re = ((n:ℂ)+s).re := by simp [Complex.add_re, Complex.natCast_re]
        _ ≤ |((n:ℂ)+s).re| := le_abs_self _
        _ ≤ ‖(n:ℂ)+s‖ := Complex.abs_re_le_norm _
    rw [norm_pow, norm_inv]
    gcongr
  have hsum_re : Summable (fun n:ℕ => ((n:ℝ)+s.re)⁻¹^2) := by
    refine ((Real.summable_one_div_nat_add_rpow s.re 2).mpr one_lt_two).congr (fun n => ?_)
    have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
    rw [abs_of_pos (by linarith), one_div]
    norm_num
  have hsum_norm : Summable (fun n:ℕ => ‖((n:ℂ)+s)⁻¹^2‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbd_n hsum_re
  calc ‖∑' (n:ℕ), ((n:ℂ)+s)⁻¹^2‖
      ≤ ∑' (n:ℕ), ‖((n:ℂ)+s)⁻¹^2‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' (n:ℕ), ((n:ℝ)+s.re)⁻¹^2 := hsum_norm.tsum_le_tsum hbd_n hsum_re

set_option maxHeartbeats 3200000 in

private theorem gapsw80_t71_psi_im_bound {σ t : ℝ} (hσ : 0 < σ) :
    |(logDeriv Complex.Gamma ((σ:ℂ)+(t:ℂ)*I)).im| ≤ Real.pi / 2 + 1/(2*σ) := by
  have _em := Classical.em
  set s : ℂ := (σ:ℂ)+(t:ℂ)*I with hs_def
  have hs_re : s.re = σ := by simp [hs_def, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hs_im : s.im = t := by simp [hs_def, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hs0 : (0:ℝ) < s.re := hs_re ▸ hσ

  have hser := gapsw80_t66_hasSum_psi_series hs0

  have hser_im : HasSum (fun n : ℕ => (1/((n:ℂ)+1) - 1/((n:ℂ)+s)).im)
      (logDeriv Complex.Gamma s).im := by
    have h := (Complex.imCLM.hasSum hser)
    simpa [Complex.add_im, Complex.ofReal_im] using h

  have hterm : ∀ n : ℕ, (1/((n:ℂ)+1) - 1/((n:ℂ)+s)).im
      = t / (((n:ℝ)+σ)^2 + t^2) := by
    intro n
    have hn1 : ((1:ℂ)/((n:ℂ)+1)).im = 0 := by
      rw [show ((n:ℂ)+1 : ℂ) = (((n:ℝ)+1:ℝ):ℂ) by push_cast; ring,
        ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_im]
    have hns_re : ((n:ℂ)+s).re = (n:ℝ)+σ := by
      simp [Complex.add_re, Complex.natCast_re, hs_re]
    have hns_im : ((n:ℂ)+s).im = t := by
      simp [Complex.add_im, Complex.natCast_im, hs_im]
    rw [Complex.sub_im, hn1, zero_sub, one_div, Complex.inv_im, hns_im,
      Complex.normSq_apply, hns_re, hns_im]
    ring
  rw [show (logDeriv Complex.Gamma s).im
      = ∑' n : ℕ, t / (((n:ℝ)+σ)^2 + t^2) from
    (hser_im.tsum_eq.symm.trans (tsum_congr hterm))]

  rcases eq_or_ne t 0 with ht0 | ht0
  · simp only [ht0, zero_div, tsum_zero, abs_zero]; positivity
  have hden : ∀ n : ℕ, (0:ℝ) < ((n:ℝ)+σ)^2 + t^2 :=
    fun n => add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero ht0)
  have hdenL : ∀ n : ℕ, (0:ℝ) < ((n:ℝ)+σ)^2 := fun n => by positivity

  have hsm : Summable (fun n : ℕ => |t| / (((n:ℝ)+σ)^2 + t^2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by
        apply div_le_div_of_nonneg_left (abs_nonneg t) (hdenL n)
        linarith [sq_nonneg t]) ?_
    have hbase : Summable (fun n : ℕ => (1:ℝ) / ((n:ℝ)+σ)^2) := by
      have h := (Real.summable_one_div_nat_add_rpow σ 2).mpr one_lt_two
      refine h.congr (fun n => ?_)
      rw [Real.rpow_two, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)+σ)]
    simpa [div_eq_mul_inv] using hbase.const_smul |t|

  have hsum_bd : (∑' n : ℕ, |t| / (((n:ℝ)+σ)^2 + t^2))
      ≤ Real.pi/2 + 1/(2*σ) := by
    have ht' : (0:ℝ) < |t| := abs_pos.mpr ht0
    have ht2 : t^2 = |t|^2 := (sq_abs t).symm

    have h0 : |t| / (σ^2 + t^2) ≤ 1/(2*σ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (σ - |t|), sq_abs t]

    set f : ℝ → ℝ := fun x => |t| / ((x+σ)^2 + t^2) with hf_def
    set g : ℝ → ℝ := fun x => Real.arctan ((x+σ)/|t|) with hg_def
    have hdn : ∀ x : ℝ, (0:ℝ) < (x+σ)^2 + t^2 :=
      fun x => add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero ht0)
    have hderiv : ∀ x, HasDerivAt g (f x) x := by
      intro x
      have h1 : HasDerivAt (fun y:ℝ => (y+σ)/|t|) (1/|t|) x :=
        ((hasDerivAt_id x).add_const σ).div_const |t|
      have h2 := (Real.hasDerivAt_arctan ((x+σ)/|t|)).comp x h1
      convert h2 using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
      simp only [f, div_pow, ht2]; field_simp; ring
    have hsm_tail : Summable (fun m : ℕ => f (((m:ℕ)+1 : ℕ))) := by
      have h := (summable_nat_add_iff (f := fun n : ℕ =>
        |t| / (((n:ℝ)+σ)^2 + t^2)) 1).mpr hsm
      exact h.congr (fun m => by simp only [f])
    have hf_cont : Continuous f := continuous_const.div
      (((continuous_id.add continuous_const).pow 2).add continuous_const)
      (fun x => ne_of_gt (hdn x))
    have hfanti : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → f b ≤ f a := fun a b ha hab => by
      have hap : 0 < a + σ := by linarith
      exact div_le_div_of_nonneg_left (abs_nonneg t) (hdn a)
        (by nlinarith [sq_nonneg t])
    have htail : (∑' m : ℕ, f (((m:ℕ)+1 : ℕ))) ≤ Real.pi/2 := by
      refine le_of_tendsto hsm_tail.hasSum.tendsto_sum_nat
        (Filter.Eventually.of_forall fun N => ?_)

      have hperterm : ∀ i ∈ Finset.range N,
          f ((i+1:ℕ)) ≤ g ((i+1:ℕ):ℝ) - g ((i:ℕ):ℝ) := fun i _ => by
        have hic : ((i+1:ℕ):ℝ) = (i:ℝ)+1 := by push_cast; ring
        rw [hic,
          (intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (i:ℝ)) (b := (i:ℝ)+1)
            (fun x _ => hderiv x) (hf_cont.intervalIntegrable _ _)).symm]
        calc f ((i:ℝ)+1) = ∫ _ in (i:ℝ)..((i:ℝ)+1), f ((i:ℝ)+1) := by
              rw [intervalIntegral.integral_const]; ring
          _ ≤ ∫ x in (i:ℝ)..((i:ℝ)+1), f x := by
              refine intervalIntegral.integral_mono_on (by linarith)
                intervalIntegrable_const (hf_cont.intervalIntegrable _ _)
                (fun x hx => ?_)
              exact hfanti (le_trans (Nat.cast_nonneg i) hx.1) hx.2
      calc (∑ i ∈ Finset.range N, f ((i+1:ℕ)))
          ≤ ∑ i ∈ Finset.range N, (g ((i+1:ℕ):ℝ) - g ((i:ℕ):ℝ)) :=
            Finset.sum_le_sum hperterm
        _ = g ((N:ℕ):ℝ) - g ((0:ℕ):ℝ) := Finset.sum_range_sub (fun i => g (i:ℝ)) N
        _ ≤ Real.pi/2 - 0 := by
            refine sub_le_sub (Real.arctan_lt_pi_div_two _).le ?_
            simp only [g, Nat.cast_zero, zero_add]
            exact Real.arctan_nonneg.mpr (div_nonneg hσ.le ht'.le)
        _ = Real.pi/2 := sub_zero _
    calc (∑' n : ℕ, |t| / (((n:ℝ)+σ)^2 + t^2))
        = |t|/(σ^2+t^2) + ∑' m : ℕ, f (((m:ℕ)+1:ℕ)) := by
          rw [hsm.tsum_eq_zero_add]
          simp only [f, Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one]
      _ ≤ 1/(2*σ) + Real.pi/2 := add_le_add h0 htail
      _ = Real.pi/2 + 1/(2*σ) := add_comm _ _
  have hsm' : Summable (fun n : ℕ => ‖t / (((n:ℝ)+σ)^2 + t^2)‖) :=
    hsm.congr (fun n => by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hden n)])
  calc |∑' n : ℕ, t / (((n:ℝ)+σ)^2 + t^2)|
      = ‖∑' n : ℕ, t / (((n:ℝ)+σ)^2 + t^2)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖t / (((n:ℝ)+σ)^2 + t^2)‖ := norm_tsum_le_tsum_norm hsm'
    _ = ∑' n : ℕ, |t| / (((n:ℝ)+σ)^2 + t^2) := tsum_congr fun n => by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (hden n)]
    _ ≤ Real.pi/2 + 1/(2*σ) := hsum_bd

set_option maxHeartbeats 3200000 in

private theorem gapsw80_t71_logDeriv_Gammaℂ_eq {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℂ s
    = -Complex.log (2 * (Real.pi : ℂ)) + logDeriv Complex.Gamma s := by
  have _em := Classical.em
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero, two_ne_zero]
  have hs_nm : ∀ m : ℕ, s ≠ -(m : ℂ) := fun m h => by
    have h1 : s.re = (-(m : ℂ)).re := by rw [h]
    simp only [Complex.neg_re, Complex.natCast_re] at h1
    linarith [Nat.cast_nonneg (α := ℝ) m, hs.trans_eq h1]
  have hΓ_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs_nm
  have hΓ_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s hs_nm
  have hg_diff : DifferentiableAt ℂ (fun z => (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    (differentiable_neg.differentiableAt).const_cpow (Or.inl h2π)
  have hg_ne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero h2π]; exact Complex.exp_ne_zero _
  have hg_ld : logDeriv (fun z => (2 * (Real.pi : ℂ)) ^ (-z)) s
      = -Complex.log (2 * (Real.pi : ℂ)) := by
    have hd : HasDerivAt (fun z => (2 * (Real.pi : ℂ)) ^ (-z))
        (-(2 * (Real.pi : ℂ)) ^ (-s) * Complex.log (2 * (Real.pi : ℂ))) s := by
      have := (hasStrictDerivAt_const_cpow (x := 2 * (Real.pi : ℂ)) (y := -s)
        (Or.inl h2π)).hasDerivAt.comp s (hasDerivAt_neg s)
      simpa [mul_comm, mul_neg, neg_mul, Function.comp_def] using this
    rw [logDeriv_apply, hd.deriv]; field_simp
  have hfact : Gammaℂ = fun z => (2:ℂ) * ((2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z) := by
    funext z; rw [Gammaℂ_def]; ring
  rw [hfact, logDeriv_const_mul _ _ (two_ne_zero),
    logDeriv_mul s hg_ne hΓ_ne hg_diff hΓ_diff, hg_ld]

set_option maxHeartbeats 3200000 in

private theorem gapsw80_t71_cont_logDeriv_Gammaℂ_vertLine {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun t : ℝ => logDeriv Gammaℂ ((σ:ℂ) + (t:ℂ)*I)) := by
  have _em := Classical.em
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero, two_ne_zero]
  have hU : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hs_nm : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z ≠ -(m : ℂ) := fun z hz m h => by
    have h1 : z.re = (-(m : ℂ)).re := by rw [h]
    simp only [Complex.neg_re, Complex.natCast_re] at h1
    have := Set.mem_setOf_eq ▸ hz
    linarith [Nat.cast_nonneg (α := ℝ) m, this.trans_eq h1]
  have hGℂ_an : AnalyticOnNhd ℂ Gammaℂ {z : ℂ | 0 < z.re} := by
    refine (DifferentiableOn.analyticOnNhd ?_ hU)
    intro z hz
    refine (DifferentiableAt.differentiableWithinAt ?_)
    have hfact : Gammaℂ
        = fun w => (2:ℂ) * ((2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w) :=
      funext fun w => by rw [Gammaℂ_def]; ring
    rw [hfact]
    exact (differentiableAt_const _).mul
      (((differentiable_neg.differentiableAt).const_cpow (Or.inl h2π)).mul
       (Complex.differentiableAt_Gamma z (hs_nm z hz)))
  have hGℂ_ne : ∀ z ∈ {z : ℂ | 0 < z.re}, Gammaℂ z ≠ 0 := fun z hz => by
    rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_)
      (Complex.Gamma_ne_zero (hs_nm z hz))
    rw [Complex.cpow_def_of_ne_zero h2π]; exact Complex.exp_ne_zero _
  have hld_cont : ContinuousOn (logDeriv Gammaℂ) {z : ℂ | 0 < z.re} := fun z hz =>
    (hGℂ_an.deriv.continuousOn z hz).div (hGℂ_an.continuousOn z hz) (hGℂ_ne z hz)
  exact hld_cont.comp_continuous
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (fun t => by simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hσ])

set_option maxHeartbeats 6400000 in

private theorem gapsw80_t71_arch_integrable_C_at_two {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hint2 : Integrable (fun t : ℝ =>
      (logDeriv Gammaℂ (((2:ℝ):ℂ)+(t:ℂ)*I)).re * (∫ x, F x * Real.cos (t*x)))) :
    Integrable (fun t : ℝ =>
      logDeriv Gammaℂ (((2:ℝ):ℂ)+(t:ℂ)*I) * ((∫ x, F x * Real.cos (t*x)):ℂ)) := by
  have _em := Classical.em
  set Fh : ℝ → ℝ := fun t => ∫ x, F x * Real.cos (t*x) with hFh_def
  have hFh_int : Integrable Fh := (gapsw80_t64_integrable_Fhat hF).1

  have hre : Integrable (fun t : ℝ =>
      ((logDeriv Gammaℂ (((2:ℝ):ℂ)+(t:ℂ)*I)).re * Fh t : ℝ)) := hint2
  have him : Integrable (fun t : ℝ =>
      ((logDeriv Gammaℂ (((2:ℝ):ℂ)+(t:ℂ)*I)).im * Fh t : ℝ)) := by
    refine (hFh_int.const_mul (Real.pi/2 + 1/(2*2))).mono'
      ?_ (Filter.Eventually.of_forall fun t => ?_)
    · exact ((Complex.continuous_im.comp (gapsw80_t71_cont_logDeriv_Gammaℂ_vertLine
        (by norm_num))).mul (gapsw80_t64_continuous_Fhat hF)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hF.2.2.2.2.2 t)]
      refine mul_le_mul_of_nonneg_right ?_ (hF.2.2.2.2.2 t)

      have him_eq : (logDeriv Gammaℂ (((2:ℝ):ℂ)+(t:ℂ)*I)).im
          = (logDeriv Complex.Gamma (((2:ℝ):ℂ)+(t:ℂ)*I)).im := by
        rw [gapsw80_t71_logDeriv_Gammaℂ_eq (by simp),
          Complex.add_im, Complex.neg_im,
          show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by push_cast; ring,
          Complex.log_im, Complex.arg_ofReal_of_nonneg (by positivity), _root_.neg_zero,
          zero_add]
      rw [him_eq]
      exact gapsw80_t71_psi_im_bound (σ := 2) (t := t) (by norm_num)
  refine ((hre.ofReal.add ((him.ofReal).smul I))).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  set z : ℂ := logDeriv Gammaℂ (((2:ℝ):ℂ)+(t:ℂ)*I) with hz
  calc ((z.re * Fh t : ℝ) : ℂ) + I * ((z.im * Fh t : ℝ) : ℂ)
      = (((z.re:ℂ) + (z.im:ℂ)*I)) * ((Fh t : ℝ):ℂ) := by push_cast; ring
    _ = z * ((Fh t : ℝ):ℂ) := by rw [Complex.re_add_im]
    _ = _ := by
        congr 1
        rw [show ((Fh t : ℝ):ℂ) = ∫ x, ((F x * Real.cos (t*x) : ℝ):ℂ) from
          integral_ofReal.symm]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        push_cast; ring

set_option maxHeartbeats 25600000 in

private theorem gapsw80_t71_arch_integral_analytic {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hint2 : Integrable (fun t : ℝ =>
      (logDeriv Gammaℂ ((2:ℝ)+(t:ℂ)*I)).re * (∫ x, F x * Real.cos (t*x))))
    {ε' : ℝ} (hε'p : 0 < ε') (hε' : ε' < 1 / 2) :
    AnalyticOnNhd ℝ
      (fun σ : ℝ => ∫ t : ℝ, (logDeriv Gammaℂ ((σ:ℂ)+(t:ℂ)*I)).re
        * (∫ x, F x * Real.cos (t*x)))
      (Set.Ioo (1 / 2 - ε') (7 / 2)) := by
  have _em := Classical.em
  set Fh : ℝ → ℝ := fun t => ∫ x, F x * Real.cos (t*x) with hFh_def
  have hFh_int : Integrable Fh := (gapsw80_t64_integrable_Fhat hF).1
  have hFh_cont : Continuous Fh := gapsw80_t64_continuous_Fhat hF
  set r : ℝ := 3/2 + ε' with hr_def
  have hr : 0 < r := by positivity
  have hha : (0:ℝ) < 1/2-ε' := by linarith
  have hU_open : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re

  have hre_ball : ∀ s ∈ Metric.ball (2:ℂ) r, 1/2 - ε' < s.re := fun s hsb => by
    have hd : ‖s - 2‖ < r := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hsb
    have hre : |s.re - 2| < r := by
      have h1 : |s.re - 2| = |(s - 2).re| := by simp
      rw [h1]; exact lt_of_le_of_lt (Complex.abs_re_le_norm _) hd
    have := abs_lt.mp hre; rw [hr_def] at this; linarith
  have hmem_hp : ∀ s ∈ Metric.ball (2:ℂ) r, ∀ t : ℝ,
      (s + (t:ℂ)*I) ∈ {z : ℂ | 0 < z.re} := fun s hsb t => by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one,
      sub_self, add_zero]
    linarith [hre_ball s hsb]

  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero, two_ne_zero]
  have hs_nm : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z ≠ -(m : ℂ) := fun z hz m h => by
    have h1 : z.re = (-(m : ℂ)).re := by rw [h]
    simp only [Complex.neg_re, Complex.natCast_re] at h1
    linarith [Nat.cast_nonneg (α := ℝ) m, (Set.mem_setOf_eq ▸ hz).trans_eq h1]
  have hfact : Gammaℂ = fun w => (2:ℂ) * ((2*(Real.pi:ℂ))^(-w) * Complex.Gamma w) :=
    funext fun w => by rw [Gammaℂ_def]; ring
  have hGℂ_an : AnalyticOnNhd ℂ Gammaℂ {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    rw [hfact]
    exact ((differentiableAt_const _).mul
      (((differentiable_neg.differentiableAt).const_cpow (Or.inl h2π)).mul
       (Complex.differentiableAt_Gamma z (hs_nm z hz)))).differentiableWithinAt
  have hGℂ_ne : ∀ z ∈ {z : ℂ | 0 < z.re}, Gammaℂ z ≠ 0 := fun z hz => by
    rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_)
      (Complex.Gamma_ne_zero (hs_nm z hz))
    rw [Complex.cpow_def_of_ne_zero h2π]; exact Complex.exp_ne_zero _
  have hψℂ_an : AnalyticOnNhd ℂ (logDeriv Gammaℂ) {z : ℂ | 0 < z.re} := fun z hz =>
    (hGℂ_an.deriv z hz).div (hGℂ_an z hz) (hGℂ_ne z hz)

  have hderiv_eq : ∀ z ∈ {z : ℂ | 0 < z.re},
      deriv (logDeriv Gammaℂ) z = deriv (logDeriv Complex.Gamma) z := fun z hz => by
    have heq : logDeriv Gammaℂ =ᶠ[𝓝 z]
        (fun w => -Complex.log (2*(Real.pi:ℂ)) + logDeriv Complex.Gamma w) := by
      filter_upwards [hU_open.mem_nhds hz] with w hw
      exact gapsw80_t71_logDeriv_Gammaℂ_eq hw
    rw [heq.deriv_eq, deriv_const_add]

  set Cε' : ℝ := ∑' n : ℕ, ((n:ℝ)+(1/2-ε'))⁻¹^2 with hCε'_def
  have hCε'_sum : Summable (fun n : ℕ => ((n:ℝ)+(1/2-ε'))⁻¹^2) := by
    refine ((Real.summable_one_div_nat_add_rpow (1/2-ε') 2).mpr one_lt_two).congr
      (fun n => ?_)
    have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
    rw [abs_of_pos (by linarith), one_div]; norm_num
  have hCε'_pos : 0 ≤ Cε' := tsum_nonneg (fun n => sq_nonneg _)

  set fd : ℂ → ℝ → ℂ := fun s t => logDeriv Gammaℂ (s+(t:ℂ)*I) * (Fh t : ℂ)
    with hfd_def
  set fd' : ℂ → ℝ → ℂ := fun s t => deriv (logDeriv Gammaℂ) (s+(t:ℂ)*I) * (Fh t : ℂ)
    with hfd'_def
  have hfd_cont : ∀ s ∈ Metric.ball (2:ℂ) r, Continuous (fd s) := fun s hsb =>
    ((hψℂ_an.continuousOn.comp_continuous
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
      (hmem_hp s hsb)).mul (Complex.continuous_ofReal.comp hFh_cont))
  have h_diff : ∀ t, ∀ s ∈ Metric.ball (2:ℂ) r,
      HasDerivAt (fd · t) (fd' s t) s := fun t s hsb => by
    have hz := hmem_hp s hsb t
    have hinner : HasDerivAt (fun w : ℂ => w+(t:ℂ)*I) 1 s :=
      (hasDerivAt_id s).add_const _
    have houter := (hψℂ_an (s+(t:ℂ)*I) hz).differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun w : ℂ => logDeriv Gammaℂ (w+(t:ℂ)*I))
        (deriv (logDeriv Gammaℂ) (s+(t:ℂ)*I)) s := by
      simpa [Function.comp_def] using houter.comp s hinner
    exact h1.mul_const (Fh t : ℂ)
  have h_bound : ∀ t, ∀ s ∈ Metric.ball (2:ℂ) r,
      ‖fd' s t‖ ≤ Cε' * |Fh t| := fun t s hsb => by
    have hz := hmem_hp s hsb t
    simp only [hfd'_def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [hderiv_eq _ hz]
    refine (gapsw80_t71_psi_deriv_series hz).2.trans ?_
    have hre_eq : (s+(t:ℂ)*I).re = s.re := by
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have hsb' := hre_ball s hsb
    rw [hre_eq, hCε'_def]
    have hmon : ∀ n:ℕ, ((n:ℝ)+s.re)⁻¹^2 ≤ ((n:ℝ)+(1/2-ε'))⁻¹^2 := fun n => by
      have hnr : (0:ℝ) ≤ (n:ℝ) := n.cast_nonneg
      have hp1 : (0:ℝ) < (n:ℝ)+(1/2-ε') := by linarith
      have hp2 : (0:ℝ) < (n:ℝ)+s.re := by linarith
      gcongr
    exact (hCε'_sum.of_nonneg_of_le (fun n => sq_nonneg _) hmon).tsum_le_tsum hmon hCε'_sum
  have bound_integrable : Integrable (fun t => Cε' * |Fh t|) :=
    (hFh_int.norm.const_mul Cε').congr
      (Filter.Eventually.of_forall fun t => by simp only [Real.norm_eq_abs])

  have hF_int_2 : Integrable (fd (2:ℂ)) :=
    (gapsw80_t71_arch_integrable_C_at_two hF hint2).congr
      (Filter.Eventually.of_forall fun t => by
        simp only [hfd_def, hFh_def]; norm_cast)
  have h2b : (2:ℂ) ∈ Metric.ball (2:ℂ) r := Metric.mem_ball_self hr
  have hF_int_all : ∀ s₀ ∈ Metric.ball (2:ℂ) r, Integrable (fd s₀) := by
    intro s₀ hs₀
    refine (hF_int_2.norm.add (bound_integrable.mul_const r)).mono'
      (hfd_cont s₀ hs₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have hmvt : ‖fd s₀ t - fd 2 t‖ ≤ Cε' * |Fh t| * ‖s₀ - 2‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f' := (fd' · t))
        (fun s hsb => (h_diff t s hsb).hasDerivWithinAt)
        (fun s hsb => h_bound t s hsb) (convex_ball _ _) h2b hs₀
    have hrs : ‖s₀ - (2:ℂ)‖ ≤ r := by
      rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hs₀).le
    calc ‖fd s₀ t‖ ≤ ‖fd 2 t‖ + ‖fd s₀ t - fd 2 t‖ := norm_le_insert' _ _
      _ ≤ ‖fd 2 t‖ + Cε' * |Fh t| * r := by
          have h1 : Cε' * |Fh t| * ‖s₀-(2:ℂ)‖ ≤ Cε' * |Fh t| * r :=
            mul_le_mul_of_nonneg_left hrs (by positivity)
          linarith [hmvt]

  set G : ℂ → ℂ := fun s => ∫ t : ℝ, fd s t with hG_def
  have hG_an : AnalyticOnNhd ℂ G (Metric.ball (2:ℂ) r) := by
    refine DifferentiableOn.analyticOnNhd (fun s₀ hs₀ => ?_) Metric.isOpen_ball

    set r₀ : ℝ := r - dist s₀ 2 with hr₀_def
    have hr₀ : 0 < r₀ := by rw [hr₀_def]; linarith [Metric.mem_ball.mp hs₀]
    have hsub : Metric.ball s₀ r₀ ⊆ Metric.ball (2:ℂ) r := fun s hsb => by
      rw [Metric.mem_ball] at *
      calc dist s 2 ≤ dist s s₀ + dist s₀ 2 := dist_triangle _ _ _
        _ < r₀ + dist s₀ 2 := by linarith
        _ = r := by rw [hr₀_def]; ring
    have ⟨_, hdA⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds s₀ hr₀)
      (by filter_upwards [Metric.ball_mem_nhds s₀ hr₀] with s hsb
          using (hfd_cont s (hsub hsb)).aestronglyMeasurable)
      (hF_int_all s₀ hs₀)
      (((hψℂ_an.deriv.continuousOn.comp_continuous
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        (hmem_hp s₀ hs₀)).mul
        (Complex.continuous_ofReal.comp hFh_cont)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t s hsb => h_bound t s (hsub hsb)))
      bound_integrable
      (Filter.Eventually.of_forall (fun t s hsb => h_diff t s (hsub hsb)))
    exact hdA.differentiableAt.differentiableWithinAt

  have hmap : Set.MapsTo (fun σ : ℝ => (σ:ℂ)) (Set.Ioo (1/2-ε') (7/2))
      (Metric.ball (2:ℂ) r) := fun σ hσ => by
    rw [Metric.mem_ball, Complex.dist_eq, show ((σ:ℂ)-(2:ℂ)) = ((σ-2:ℝ):ℂ) from by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, hr_def]
    obtain ⟨h1, h2⟩ := hσ; rw [abs_lt]; constructor <;> linarith
  have hReG_an : AnalyticOnNhd ℝ (fun σ : ℝ => (G (σ:ℂ)).re)
      (Set.Ioo (1/2-ε') (7/2)) :=
    (Complex.reCLM.analyticOnNhd _).comp
      ((hG_an.restrictScalars).comp (Complex.ofRealCLM.analyticOnNhd _) hmap)
      (Set.mapsTo_univ _ _)

  refine hReG_an.congr isOpen_Ioo (fun σ hσ => ?_)
  have hint_σ := hF_int_all (σ:ℂ) (hmap hσ)
  have heq1 : (G (σ:ℂ)).re = ∫ t : ℝ, (fd (σ:ℂ) t).re := by
    rw [hG_def]; exact (integral_re hint_σ).symm
  rw [heq1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hfd_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, hFh_def]

set_option maxHeartbeats 12800000 in

private theorem gapsw80_t71_zeroSide_ibp_bound_ext {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hcd : ContDiff ℝ 2 F) {c ε ε' : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hε'p : 0 < ε') (hε' : ε' < ε)
    (hdecay : ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))
    {ρ : ℂ} (hρ1 : 0 < ρ.re) (hρ2 : ρ.re < 1) (hγ : 1 ≤ |ρ.im|)
    {s : ℂ} (hs : 1 / 2 - ε' < s.re) :
    ‖∫ x in Set.Ioi (0:ℝ),
        (F x : ℂ) * (Complex.exp (-((s - ρ.re) * x)) + Complex.exp (-((s + ρ.re - 1) * x)))
          * Real.cos (ρ.im * x)‖ * ρ.im ^ 2
      ≤ ‖2 * s - 1‖ + 2 * (2 + ‖s‖) ^ 2 * c / (ε - ε') := by
  have _em := Classical.em
  set γ : ℝ := ρ.im with hγ_def
  set β : ℝ := ρ.re with hβ_def
  set a₁ : ℂ := s - (β:ℂ) with ha₁_def
  set a₂ : ℂ := s + (β:ℂ) - 1 with ha₂_def
  set δ : ℝ := ε - ε' with hδ_def
  have hδp : 0 < δ := by rw [hδ_def]; linarith
  have hγ0 : γ ≠ 0 := fun h => by rw [h, abs_zero] at hγ; linarith
  have hγC0 : (γ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ0
  have hγ2p : (0:ℝ) < γ^2 := by positivity

  have hRea₁ : -(1/2+ε') < a₁.re := by
    simp only [ha₁_def, Complex.sub_re, Complex.ofReal_re]; linarith
  have hRea₂ : -(1/2+ε') < a₂.re := by
    simp only [ha₂_def, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.one_re]; linarith
  have ha₁bd : ‖a₁‖ ≤ ‖s‖ + 1 := by
    rw [ha₁_def]
    calc ‖s - (β:ℂ)‖ ≤ ‖s‖ + ‖(β:ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖s‖ + 1 := by
          simp only [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hρ1]; linarith
  have ha₂bd : ‖a₂‖ ≤ ‖s‖ + 1 := by
    rw [ha₂_def]
    calc ‖s + (β:ℂ) - 1‖ = ‖s + ((β:ℂ) - 1)‖ := by ring_nf
      _ ≤ ‖s‖ + ‖(β:ℂ) - 1‖ := norm_add_le _ _
      _ ≤ ‖s‖ + 1 := by
          have : ‖(β:ℂ) - 1‖ = |β - 1| := by
            rw [show ((β:ℂ) - 1) = ((β - 1 : ℝ):ℂ) from by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs]
          rw [this, abs_of_nonpos (by linarith)]; linarith

  set E : ℝ → ℂ := fun x => Complex.exp (-(a₁*x)) + Complex.exp (-(a₂*x)) with hE_def
  set E' : ℝ → ℂ := fun x => -a₁*Complex.exp (-(a₁*x)) + -a₂*Complex.exp (-(a₂*x))
    with hE'_def
  set E'' : ℝ → ℂ := fun x => a₁^2*Complex.exp (-(a₁*x)) + a₂^2*Complex.exp (-(a₂*x))
    with hE''_def
  have hcexp_d : ∀ (a:ℂ) (x:ℝ), HasDerivAt (fun y:ℝ => Complex.exp (-(a*(y:ℂ))))
      (-a * Complex.exp (-(a*x))) x := fun a x => by
    have h1 : HasDerivAt (fun y:ℝ => -(a*(y:ℂ))) (-a) x := by
      have := ((hasDerivAt_id (x:ℝ)).ofReal_comp.const_mul a).neg
      simpa [Pi.neg_def] using this
    have := h1.cexp
    convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | ring
  have hEd : ∀ x, HasDerivAt E (E' x) x := fun x => by
    have h := (hcexp_d a₁ x).fun_add (hcexp_d a₂ x)
    convert h using 2 <;> first | (with_reducible_and_instances rfl) | (simp only [hE_def, hE'_def]) | skip
  have hE'd : ∀ x, HasDerivAt E' (E'' x) x := fun x => by
    have h := ((hcexp_d a₁ x).const_mul (-a₁)).fun_add ((hcexp_d a₂ x).const_mul (-a₂))
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    simp only [hE''_def]; ring
  have hEcont : Continuous E := by
    refine Continuous.add ?_ ?_ <;>
      exact Complex.continuous_exp.comp ((continuous_const.mul
        Complex.continuous_ofReal).neg)
  have hE'cont : Continuous E' := by
    refine Continuous.add ?_ ?_ <;>
      exact continuous_const.mul (Complex.continuous_exp.comp ((continuous_const.mul
        Complex.continuous_ofReal).neg))
  have hE''cont : Continuous E'' := by
    refine Continuous.add ?_ ?_ <;>
      exact continuous_const.mul (Complex.continuous_exp.comp ((continuous_const.mul
        Complex.continuous_ofReal).neg))
  set H : ℝ → ℂ := fun x => (F x : ℂ) * E x with hH_def
  set H' : ℝ → ℂ := fun x => ((deriv F x : ℝ) : ℂ) * E x + (F x : ℂ) * E' x with hH'_def
  set H'' : ℝ → ℂ := fun x =>
    ((deriv (deriv F) x : ℝ) : ℂ) * E x + 2*((deriv F x : ℝ) : ℂ)*E' x + (F x : ℂ)*E'' x
    with hH''_def
  have hFd : ∀ x, HasDerivAt F (deriv F x) x := fun x =>
    (hcd.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hF'd : ∀ x, HasDerivAt (deriv F) (deriv (deriv F) x) x := fun x =>
    ((hcd.iterate_deriv' 1 1).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hHd : ∀ x, HasDerivAt H (H' x) x := fun x =>
    ((hFd x).ofReal_comp.mul (hEd x))
  have hH'd : ∀ x, HasDerivAt H' (H'' x) x := fun x => by
    have h := ((hF'd x).ofReal_comp.fun_mul (hEd x)).fun_add ((hFd x).ofReal_comp.fun_mul (hE'd x))
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    simp only [hH''_def]; ring
  have hFcont : Continuous F := hcd.continuous
  have hHcont : Continuous H := (Complex.continuous_ofReal.comp hFcont).mul hEcont
  have hH'cont : Continuous H' :=
    ((Complex.continuous_ofReal.comp (hcd.continuous_deriv (by norm_num))).mul
      hEcont).add ((Complex.continuous_ofReal.comp hFcont).mul hE'cont)
  have hH''cont : Continuous H'' :=
    (((Complex.continuous_ofReal.comp (hcd.iterate_deriv' 0 2).continuous).mul
      hEcont).add ((continuous_const.mul (Complex.continuous_ofReal.comp
      (hcd.continuous_deriv (by norm_num)))).mul hE'cont)).add
      ((Complex.continuous_ofReal.comp hFcont).mul hE''cont)

  have hexp_bd : ∀ (a:ℂ), -(1/2+ε') < a.re → ∀ x ∈ Set.Ioi (0:ℝ),
      ‖Complex.exp (-(a*x))‖ ≤ Real.exp ((1/2+ε')*x) := fun a hRe x hx => by
    have hxp : (0:ℝ) < x := hx
    rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hEbd : ∀ x ∈ Set.Ioi (0:ℝ),
      ‖E x‖ ≤ 2*Real.exp ((1/2+ε')*x)
      ∧ ‖E' x‖ ≤ 2*(‖s‖+1)*Real.exp ((1/2+ε')*x)
      ∧ ‖E'' x‖ ≤ 2*(‖s‖+1)^2*Real.exp ((1/2+ε')*x) := fun x hx => by
    have he1 := hexp_bd a₁ hRea₁ x hx; have he2 := hexp_bd a₂ hRea₂ x hx
    have hep : (0:ℝ) < Real.exp ((1/2+ε')*x) := Real.exp_pos _
    refine ⟨?_, ?_, ?_⟩
    · simp only [hE_def]
      calc ‖Complex.exp (-(a₁*x)) + Complex.exp (-(a₂*x))‖
          ≤ ‖Complex.exp (-(a₁*x))‖ + ‖Complex.exp (-(a₂*x))‖ := norm_add_le _ _
        _ ≤ Real.exp ((1/2+ε')*x) + Real.exp ((1/2+ε')*x) := by gcongr
        _ = 2*Real.exp ((1/2+ε')*x) := by ring
    · simp only [hE'_def]
      calc ‖(-a₁)*Complex.exp (-(a₁*x)) + (-a₂)*Complex.exp (-(a₂*x))‖
          ≤ ‖a₁‖*‖Complex.exp (-(a₁*x))‖ + ‖a₂‖*‖Complex.exp (-(a₂*x))‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            rw [norm_mul, norm_mul, norm_neg, norm_neg]
        _ ≤ (‖s‖+1)*Real.exp ((1/2+ε')*x) + (‖s‖+1)*Real.exp ((1/2+ε')*x) := by
            gcongr
        _ = 2*(‖s‖+1)*Real.exp ((1/2+ε')*x) := by ring
    · simp only [hE''_def]
      calc ‖a₁^2*Complex.exp (-(a₁*x)) + a₂^2*Complex.exp (-(a₂*x))‖
          ≤ ‖a₁‖^2*‖Complex.exp (-(a₁*x))‖ + ‖a₂‖^2*‖Complex.exp (-(a₂*x))‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            rw [norm_mul, norm_mul, norm_pow, norm_pow]
        _ ≤ (‖s‖+1)^2*Real.exp ((1/2+ε')*x)
            + (‖s‖+1)^2*Real.exp ((1/2+ε')*x) := by
            gcongr <;> exact pow_le_pow_left₀ (norm_nonneg _) (by assumption) 2
        _ = 2*(‖s‖+1)^2*Real.exp ((1/2+ε')*x) := by ring

  set Cs : ℝ := 2*(2+‖s‖)^2 with hCs_def
  have hCs1 : (2:ℝ) ≤ Cs := by
    rw [hCs_def]; nlinarith [norm_nonneg s]
  have hCsp : (0:ℝ) < Cs := by linarith
  have hHbd : ∀ x ∈ Set.Ioi (0:ℝ),
      ‖H x‖ ≤ Cs*(c*Real.exp (-(δ*x))) ∧ ‖H' x‖ ≤ Cs*(c*Real.exp (-(δ*x)))
      ∧ ‖H'' x‖ ≤ Cs*(c*Real.exp (-(δ*x))) := fun x hx => by
    have ⟨hEb, hE'b, hE''b⟩ := hEbd x hx
    have hxp : (0:ℝ) < x := hx
    have hd0 := hdecay 0 x; have hd1 := hdecay 1 x; have hd2 := hdecay 2 x
    simp only [show ((0:Fin 3):ℕ)=0 from rfl, show ((1:Fin 3):ℕ)=1 from rfl,
      show ((2:Fin 3):ℕ)=2 from rfl, iteratedDeriv_zero, iteratedDeriv_one,
      iteratedDeriv_succ, abs_of_pos hxp] at hd0 hd1 hd2
    have hprod : Real.exp (-(1/2+ε)*x) * Real.exp ((1/2+ε')*x) = Real.exp (-(δ*x)) := by
      rw [← Real.exp_add, hδ_def]; ring_nf
    have hce : (0:ℝ) < c*Real.exp (-(δ*x)) := by positivity
    have hns : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
    refine ⟨?_, ?_, ?_⟩
    · simp only [hH_def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |F x| * ‖E x‖
          ≤ (c*Real.exp (-(1/2+ε)*x)) * (2*Real.exp ((1/2+ε')*x)) := by gcongr
        _ = 2*(c*Real.exp (-(δ*x))) := by rw [← hprod]; ring
        _ ≤ Cs*(c*Real.exp (-(δ*x))) := by gcongr
    · simp only [hH'_def]
      calc ‖((deriv F x:ℝ):ℂ) * E x + (F x:ℂ) * E' x‖
          ≤ |deriv F x| * ‖E x‖ + |F x| * ‖E' x‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (c*Real.exp (-(1/2+ε)*x)) * (2*Real.exp ((1/2+ε')*x))
            + (c*Real.exp (-(1/2+ε)*x)) * (2*(‖s‖+1)*Real.exp ((1/2+ε')*x)) := by
            gcongr
        _ = 2*(1+(‖s‖+1))*(c*Real.exp (-(δ*x))) := by rw [← hprod]; ring
        _ ≤ Cs*(c*Real.exp (-(δ*x))) := by
            apply mul_le_mul_of_nonneg_right _ hce.le
            rw [hCs_def]; nlinarith
    · simp only [hH''_def]
      calc ‖((deriv (deriv F) x:ℝ):ℂ) * E x + 2*((deriv F x:ℝ):ℂ)*E' x + (F x:ℂ)*E'' x‖
          ≤ |deriv (deriv F) x| * ‖E x‖ + 2 * |deriv F x| * ‖E' x‖
            + |F x| * ‖E'' x‖ := by
            refine (norm_add₃_le).trans (le_of_eq ?_)
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_ofNat]
        _ ≤ (c*Real.exp (-(1/2+ε)*x)) * (2*Real.exp ((1/2+ε')*x))
            + 2*(c*Real.exp (-(1/2+ε)*x))*(2*(‖s‖+1)*Real.exp ((1/2+ε')*x))
            + (c*Real.exp (-(1/2+ε)*x))*(2*(‖s‖+1)^2*Real.exp ((1/2+ε')*x)) := by
            gcongr
        _ = Cs*(c*Real.exp (-(δ*x))) := by rw [← hprod, hCs_def]; ring

  have hmaj_Ioi : IntegrableOn (fun x => Cs*(c*Real.exp (-(δ*x)))) (Set.Ioi 0) :=
    (((exp_neg_integrableOn_Ioi 0 hδp).congr_fun
      (fun x _ => by rw [neg_mul]) measurableSet_Ioi).const_mul c).const_mul Cs

  have hmaj0 : Filter.Tendsto (fun x => Cs*(c*Real.exp (-(δ*x))))
      Filter.atTop (𝓝 0) := by
    have he : Filter.Tendsto (fun x:ℝ => Real.exp (-(δ*x))) Filter.atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop hδp)
      exact this.congr (fun x => by simp only [Function.comp_apply, id_eq])
    rw [show (0:ℝ) = Cs*(c*0) from by ring]
    exact (he.const_mul c).const_mul Cs
  have hev_Ioi : ∀ᶠ x in Filter.atTop, x ∈ Set.Ioi (0:ℝ) :=
    Filter.eventually_atTop.mpr ⟨1, fun x hx => lt_of_lt_of_le one_pos hx⟩
  have htend0 : ∀ G : ℝ → ℂ, (∀ x ∈ Set.Ioi (0:ℝ),
      ‖G x‖ ≤ Cs*(c*Real.exp (-(δ*x)))) →
      Filter.Tendsto G Filter.atTop (𝓝 0) := fun G hGbd => by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_ hmaj0)
    filter_upwards [hev_Ioi] with x hx using hGbd x hx
  have hHtend : Filter.Tendsto H Filter.atTop (𝓝 0) :=
    htend0 H (fun x hx => (hHbd x hx).1)
  have hH'tend : Filter.Tendsto H' Filter.atTop (𝓝 0) :=
    htend0 H' (fun x hx => (hHbd x hx).2.1)

  have hint_bm : ∀ G : ℝ → ℂ, Continuous G → (∀ x ∈ Set.Ioi (0:ℝ),
      ‖G x‖ ≤ Cs*(c*Real.exp (-(δ*x)))) →
      ∀ tr : ℝ → ℝ, Continuous tr → (∀ x, |tr x| ≤ 1) →
      IntegrableOn (fun x => G x * (tr x : ℂ)) (Set.Ioi 0) := by
    intro G hGc hGbd tr htrc htrb
    refine hmaj_Ioi.mono' ((hGc.mul (Complex.continuous_ofReal.comp
      htrc)).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖G x‖ * |tr x| ≤ (Cs*(c*Real.exp (-(δ*x)))) * 1 :=
          mul_le_mul (hGbd x hx) (htrb x) (abs_nonneg _) (by positivity)
      _ = Cs*(c*Real.exp (-(δ*x))) := mul_one _
  have hcos_c : Continuous (fun x => Real.cos (γ*x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin_c : Continuous (fun x => Real.sin (γ*x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hHcos := hint_bm H hHcont (fun x hx => (hHbd x hx).1)
    _ hcos_c (fun x => Real.abs_cos_le_one _)
  have hH'sin := hint_bm H' hH'cont (fun x hx => (hHbd x hx).2.1)
    _ hsin_c (fun x => Real.abs_sin_le_one _)
  have hH''cos := hint_bm H'' hH''cont (fun x hx => (hHbd x hx).2.2)
    _ hcos_c (fun x => Real.abs_cos_le_one _)

  have htend_bm : ∀ (G:ℝ→ℂ) (tr:ℝ→ℝ), Filter.Tendsto G Filter.atTop (𝓝 0) →
      (∀ x, |tr x| ≤ 1) →
      Filter.Tendsto (fun x => G x * (tr x:ℂ)) Filter.atTop (𝓝 0) := by
    intro G tr hG htr
    have hGn : Filter.Tendsto (fun x => ‖G x‖) Filter.atTop (𝓝 0) := by
      simpa using hG.norm
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _)
        (Filter.Eventually.of_forall fun x => ?_) hGn)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (htr x)

  have hibp1 : ∫ x in Set.Ioi (0:ℝ), H x * (Real.cos (γ*x):ℂ)
      = -(1/(γ:ℂ)) * ∫ x in Set.Ioi (0:ℝ), H' x * (Real.sin (γ*x):ℂ) := by
    set u : ℝ → ℂ := fun x => H x * (Real.sin (γ*x):ℂ) / (γ:ℂ) with hu_def
    have hud : ∀ x, HasDerivAt u
        ((1/(γ:ℂ)) * (H' x * (Real.sin (γ*x):ℂ)) + H x * (Real.cos (γ*x):ℂ)) x :=
      fun x => by
      have htr : HasDerivAt (fun y:ℝ => (Real.sin (γ*y):ℂ))
          ((γ*Real.cos (γ*x):ℝ):ℂ) x := by
        have h := ((hasDerivAt_id x).const_mul γ).sin
        simp only [id_eq, mul_one] at h
        have h2 := h.ofReal_comp
        convert h2 using 1 <;> first | (with_reducible_and_instances rfl) | rfl | (push_cast; ring)
      have h := ((hHd x).mul htr).div_const (γ:ℂ)
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
      have : ((γ*Real.cos (γ*x):ℝ):ℂ) = (γ:ℂ)*(Real.cos (γ*x):ℂ) := by push_cast; ring
      rw [this]; field_simp
    have hu_int : IntegrableOn
        (fun x => (1/(γ:ℂ)) * (H' x * (Real.sin (γ*x):ℂ)) + H x * (Real.cos (γ*x):ℂ))
        (Set.Ioi 0) := (hH'sin.const_mul (1/(γ:ℂ))).add hHcos
    have hu_tend : Filter.Tendsto u Filter.atTop (𝓝 0) := by
      have h := (htend_bm H (fun x => Real.sin (γ*x)) hHtend
        (fun x => Real.abs_sin_le_one _)).div_const (γ:ℂ)
      simpa [hu_def, zero_div] using h
    have hucont : ContinuousWithinAt u (Set.Ici 0) 0 :=
      ((hHcont.mul (Complex.continuous_ofReal.comp hsin_c)).div_const
        (γ:ℂ)).continuousWithinAt
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hucont
      (fun x _ => hud x) hu_int hu_tend
    have hu0 : u 0 = 0 := by simp [hu_def, mul_zero, Real.sin_zero]
    rw [hu0, sub_zero] at hFTC
    rw [integral_add (hH'sin.const_mul (1/(γ:ℂ))) hHcos, integral_const_mul] at hFTC
    linear_combination hFTC

  have hibp2 : ∫ x in Set.Ioi (0:ℝ), H' x * (Real.sin (γ*x):ℂ)
      = H' 0 / (γ:ℂ) + (1/(γ:ℂ)) * ∫ x in Set.Ioi (0:ℝ), H'' x * (Real.cos (γ*x):ℂ) := by
    set v : ℝ → ℂ := fun x => -(H' x * (Real.cos (γ*x):ℂ)) / (γ:ℂ) with hv_def
    have hvd : ∀ x, HasDerivAt v
        (H' x * (Real.sin (γ*x):ℂ) - (1/(γ:ℂ)) * (H'' x * (Real.cos (γ*x):ℂ))) x :=
      fun x => by
      have htr : HasDerivAt (fun y:ℝ => (Real.cos (γ*y):ℂ))
          ((-(γ*Real.sin (γ*x)):ℝ):ℂ) x := by
        have h := ((hasDerivAt_id x).const_mul γ).cos
        simp only [id_eq, mul_one] at h
        have h2 := h.ofReal_comp
        convert h2 using 1 <;> first | (with_reducible_and_instances rfl) | rfl | (push_cast; ring)
      have h := (((hH'd x).mul htr).neg).div_const (γ:ℂ)
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
      have hc : ((-(γ*Real.sin (γ*x)):ℝ):ℂ) = -((γ:ℂ)*(Real.sin (γ*x):ℂ)) := by
        push_cast; ring
      rw [hc]; field_simp; ring
    have hv_int : IntegrableOn
        (fun x => H' x * (Real.sin (γ*x):ℂ)
          - (1/(γ:ℂ)) * (H'' x * (Real.cos (γ*x):ℂ))) (Set.Ioi 0) :=
      hH'sin.sub (hH''cos.const_mul (1/(γ:ℂ)))
    have hv_tend : Filter.Tendsto v Filter.atTop (𝓝 0) := by
      have h := ((htend_bm H' (fun x => Real.cos (γ*x)) hH'tend
        (fun x => Real.abs_cos_le_one _)).neg).div_const (γ:ℂ)
      simpa [hv_def, _root_.neg_zero, zero_div] using h
    have hvcont : ContinuousWithinAt v (Set.Ici 0) 0 :=
      (((hH'cont.mul (Complex.continuous_ofReal.comp hcos_c)).neg).div_const
        (γ:ℂ)).continuousWithinAt
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hvcont
      (fun x _ => hvd x) hv_int hv_tend
    have hv0 : v 0 = -(H' 0) / (γ:ℂ) := by
      simp only [hv_def, mul_zero, Real.cos_zero, Complex.ofReal_one, mul_one]
    rw [hv0, integral_sub hH'sin (hH''cos.const_mul (1/(γ:ℂ))),
      integral_const_mul] at hFTC
    linear_combination hFTC

  have hH'0 : H' 0 = -(2*s-1) := by
    have hF'0 : deriv F 0 = 0 := by
      have heq : (fun x => F (-x)) = F := funext hF.2.1
      have h : deriv (fun x => F (-x)) 0 = -deriv F (-0) := deriv_comp_neg F 0
      rw [heq, _root_.neg_zero] at h; linarith
    have hF0 : F 0 = 1 := hF.2.2.1
    simp only [hH'_def, hE_def, hE'_def, Complex.ofReal_zero, mul_zero, _root_.neg_zero,
      Complex.exp_zero, hF'0, Complex.ofReal_zero, zero_mul, zero_add,
      hF0, Complex.ofReal_one, one_mul]
    rw [ha₁_def, ha₂_def]; push_cast; ring

  have hZ_eq : (∫ x in Set.Ioi (0:ℝ), H x * (Real.cos (γ*x):ℂ))
      = (2*s-1)/(γ:ℂ)^2
        - (1/(γ:ℂ)^2) * ∫ x in Set.Ioi (0:ℝ), H'' x * (Real.cos (γ*x):ℂ) := by
    rw [hibp1, hibp2, hH'0]; field_simp; ring

  have hgoal_eq : (∫ x in Set.Ioi (0:ℝ),
        (F x : ℂ) * (Complex.exp (-((s - ρ.re) * x)) + Complex.exp (-((s + ρ.re - 1) * x)))
          * Real.cos (ρ.im * x))
      = ∫ x in Set.Ioi (0:ℝ), H x * (Real.cos (γ*x):ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [hH_def, hE_def, ha₁_def, ha₂_def, hβ_def, hγ_def]
  rw [hgoal_eq, hZ_eq]
  have hγ2C : ((γ:ℂ)^2) = ((γ^2:ℝ):ℂ) := by push_cast; ring
  have hγ2C0 : ((γ:ℂ)^2) ≠ 0 := pow_ne_zero 2 hγC0
  calc ‖(2*s-1)/(γ:ℂ)^2
        - (1/(γ:ℂ)^2) * ∫ x in Set.Ioi (0:ℝ), H'' x * (Real.cos (γ*x):ℂ)‖ * γ^2
      ≤ (‖2*s-1‖/γ^2
          + (1/γ^2) * ‖∫ x in Set.Ioi (0:ℝ), H'' x * (Real.cos (γ*x):ℂ)‖) * γ^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg γ)
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_div, norm_mul, norm_div, norm_one, hγ2C, Complex.norm_real,
          Real.norm_of_nonneg (sq_nonneg γ)]
    _ = ‖2*s-1‖ + ‖∫ x in Set.Ioi (0:ℝ), H'' x * (Real.cos (γ*x):ℂ)‖ := by
        field_simp
    _ ≤ ‖2*s-1‖ + (∫ x in Set.Ioi (0:ℝ), Cs*(c*Real.exp (-(δ*x)))) := by
        gcongr
        refine (norm_integral_le_integral_norm _).trans ?_
        refine setIntegral_mono_on hH''cos.norm hmaj_Ioi measurableSet_Ioi
          (fun x hx => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (norm_nonneg _)
          (Real.abs_cos_le_one _)).trans (hHbd x hx).2.2
    _ = ‖2*s-1‖ + Cs*c/δ := by
        have hv := integral_exp_mul_Ioi (a := -δ) (by linarith) 0
        simp only [mul_zero, Real.exp_zero, neg_neg] at hv
        rw [integral_const_mul, integral_const_mul,
          show (fun x => Real.exp (-(δ*x))) = (fun x => Real.exp (-δ*x)) from
            funext (fun x => by rw [neg_mul]),
          hv]
        field_simp
    _ = ‖2*s-1‖ + 2*(2+‖s‖)^2*c/(ε-ε') := by rw [hCs_def, hδ_def]

set_option maxHeartbeats 12800000 in

private theorem gapsw80_t71_zeroSideSigma_analytic {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hFC2 : gapsw80_t69_KernelC2Decay F) {ρ : ℕ → ℂ}
    (hstrip : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1)
    (hsum : Summable (fun j => (Complex.normSq (ρ j))⁻¹)) :
    ∃ δ > (0:ℝ), AnalyticOnNhd ℝ
      (fun σ : ℝ => ∑' j, ∫ x in Set.Ioi (0:ℝ),
        F x * (Real.exp (-((σ - (ρ j).re) * x)) + Real.exp (-((σ + (ρ j).re - 1) * x)))
          * Real.cos ((ρ j).im * x))
      (Set.Ioo (1 / 2 - δ) (7 / 2)) := by
  have _em := Classical.em
  obtain ⟨hcd, c, ε, hc, hε, hdecay⟩ := hFC2
  have hcontF : Continuous F := hcd.continuous
  have hdecay0 : ∀ x, |F x| ≤ c * Real.exp (-(1/2+ε)*|x|) := fun x => by
    have h := hdecay 0 x; simpa using h
  set ε'' : ℝ := ε/2 with hε''_def
  have hε''p : 0 < ε'' := half_pos hε
  have hε''lt : ε'' < ε := half_lt_self hε
  set δ : ℝ := ε - ε'' with hδ_def
  have hδp : 0 < δ := by rw [hδ_def]; linarith
  refine ⟨ε'', hε''p, ?_⟩

  set r : ℝ := 3/2 + ε'' with hr_def
  set V : Set ℂ := Metric.ball (2:ℂ) r
  have hV_open : IsOpen V := Metric.isOpen_ball
  have hV_re : ∀ s ∈ V, 1/2 - ε'' < s.re := fun s hsV => by
    have hd : ‖s - 2‖ < r := by rw [← dist_eq_norm]; exact hsV
    have hre : |s.re - 2| ≤ ‖s - 2‖ := by
      rw [show s.re - 2 = (s - 2).re by simp]; exact Complex.abs_re_le_norm _
    have := hre.trans_lt hd; rw [hr_def] at this
    have ⟨h1, _⟩ := abs_lt.mp this; linarith
  set R : ℝ := 2 + r with hR_def
  have hV_norm : ∀ s ∈ V, ‖s‖ ≤ R := fun s hsV => by
    have hd : ‖s - 2‖ < r := by rw [← dist_eq_norm]; exact hsV
    calc ‖s‖ = ‖(s - 2) + 2‖ := by ring_nf
      _ ≤ ‖s - 2‖ + ‖(2:ℂ)‖ := norm_add_le _ _
      _ ≤ r + 2 := by
          have h2 : ‖(2:ℂ)‖ = 2 := by simp
          linarith
      _ = R := by rw [hR_def]; ring

  set Zℂ : ℕ → ℂ → ℂ := fun j s => ∫ x in Set.Ioi (0:ℝ),
    (F x:ℂ) * (Complex.exp (-((s-(ρ j).re)*x)) + Complex.exp (-((s+(ρ j).re-1)*x)))
      * (Real.cos ((ρ j).im*x):ℂ)
  have hZℂ_diff : ∀ j, DifferentiableOn ℂ (Zℂ j) V := fun j =>
    ((gapsw80_t71_zeroSideTerm_analytic hcontF hc hε hdecay0
      (hstrip j).1 (hstrip j).2 hε''lt).mono (fun s hs => hV_re s hs)).differentiableOn

  have hρ0 : ∀ j, (0:ℝ) < Complex.normSq (ρ j) := fun j =>
    Complex.normSq_pos.mpr (fun h => absurd (h ▸ (hstrip j).1) (lt_irrefl 0))

  have hcrude : ∀ j s, 1/2-ε'' < s.re → ‖Zℂ j s‖ ≤ 2*c/δ := fun j s hs => by
    have hmaj : IntegrableOn (fun x => 2*c*Real.exp (-(δ*x))) (Set.Ioi 0) :=
      ((exp_neg_integrableOn_Ioi 0 hδp).congr_fun (fun x _ => by rw [neg_mul])
        measurableSet_Ioi).const_mul (2*c)
    have hmaj_val : ∫ x in Set.Ioi (0:ℝ), 2*c*Real.exp (-(δ*x)) = 2*c/δ := by
      have hv := integral_exp_mul_Ioi (a := -δ) (by linarith) 0
      simp only [mul_zero, Real.exp_zero, neg_neg] at hv
      rw [integral_const_mul,
        show (fun x => Real.exp (-(δ*x))) = (fun x => Real.exp (-δ*x)) from
          funext (fun x => by rw [neg_mul]), hv]
      field_simp
    calc ‖Zℂ j s‖ ≤ ∫ x in Set.Ioi (0:ℝ),
            ‖(F x:ℂ) * (Complex.exp (-((s-(ρ j).re)*x))
              + Complex.exp (-((s+(ρ j).re-1)*x))) * (Real.cos ((ρ j).im*x):ℂ)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x in Set.Ioi (0:ℝ), 2*c*Real.exp (-(δ*x)) := by
          refine integral_mono_of_nonneg (ae_of_all _ (fun x => norm_nonneg _))
            hmaj (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
          have hx0 : (0:ℝ) < x := hx
          have hβ := hstrip j
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hexp_bd : ∀ a : ℂ, -(1/2+ε'') < a.re →
              ‖Complex.exp (-(a*x))‖ ≤ Real.exp ((1/2+ε'')*x) := fun a ha => by
            rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            exact Real.exp_le_exp.mpr (by nlinarith)
          have ha1 : -(1/2+ε'') < (s-(ρ j).re).re := by
            simp only [Complex.sub_re, Complex.ofReal_re]; linarith [hβ.2]
          have ha2 : -(1/2+ε'') < (s+(ρ j).re-1).re := by
            simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re,
              Complex.one_re]; linarith [hβ.1]
          calc |F x| * ‖Complex.exp (-((s-(ρ j).re)*x))
                  + Complex.exp (-((s+(ρ j).re-1)*x))‖ * |Real.cos ((ρ j).im*x)|
              ≤ (c*Real.exp (-(1/2+ε)*|x|))
                  * (Real.exp ((1/2+ε'')*x) + Real.exp ((1/2+ε'')*x)) * 1 :=
                mul_le_mul (mul_le_mul (hdecay0 x)
                  ((norm_add_le _ _).trans (add_le_add (hexp_bd _ ha1) (hexp_bd _ ha2)))
                  (norm_nonneg _) (le_trans (abs_nonneg _) (hdecay0 x)))
                  (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
            _ = 2*c*Real.exp (-(δ*x)) := by
                rw [abs_of_pos hx0, mul_one,
                  show Real.exp ((1/2+ε'')*x) + Real.exp ((1/2+ε'')*x)
                    = 2 * Real.exp ((1/2+ε'')*x) from (two_mul _).symm,
                  show c*Real.exp (-(1/2+ε)*x) * (2*Real.exp ((1/2+ε'')*x))
                    = 2*c*(Real.exp (-(1/2+ε)*x)*Real.exp ((1/2+ε'')*x))
                    from by ring,
                  ← Real.exp_add]
                congr 1; rw [hδ_def]; ring
      _ = 2*c/δ := hmaj_val

  set C : ℝ := (2*R+1) + 2*(2+R)^2*c/δ with hC_def
  have hCpos : 0 < C := by rw [hC_def, hR_def, hr_def]; positivity

  set M₀ : ℝ := 2*C + 4*c/δ with hM₀_def
  set u : ℕ → ℝ := fun j => M₀ * (Complex.normSq (ρ j))⁻¹
  have hu_sum : Summable u := hsum.mul_left M₀
  have hF_le : ∀ j (s : ℂ), s ∈ V → ‖Zℂ j s‖ ≤ u j := fun j s hsV => by
    have hns := hρ0 j
    have hns_eq : Complex.normSq (ρ j) = (ρ j).re^2 + (ρ j).im^2 := by
      rw [Complex.normSq_apply]; ring
    have hβ := hstrip j
    have hβ2 : (ρ j).re^2 < 1 := by nlinarith [hβ.1, hβ.2]
    simp only [u]
    rcases le_or_gt 1 |(ρ j).im| with hγ | hγ
    ·
      have h0e' := gapsw80_t71_zeroSide_ibp_bound_ext hF hcd hc hε hε''p hε''lt
        hdecay hβ.1 hβ.2 hγ (hV_re s hsV)
      have hsR := hV_norm s hsV
      have hbd : ‖2*s-1‖ + 2*(2+‖s‖)^2*c/(ε-ε'') ≤ C := by
        have h1 : ‖2*s-1‖ ≤ 2*R+1 :=
          (norm_sub_le _ _).trans (by
            rw [norm_mul, show ‖(2:ℂ)‖ = 2 from by simp, norm_one]; linarith)
        have h2 : (2+‖s‖)^2 ≤ (2+R)^2 := by gcongr
        rw [hC_def, ← hδ_def]
        gcongr
      have hγ2 : (0:ℝ) < (ρ j).im^2 := by
        have := sq_abs (ρ j).im; nlinarith
      have hkey : ‖Zℂ j s‖ ≤ C / (ρ j).im^2 := by
        have h := h0e'.trans hbd
        rwa [← le_div_iff₀ hγ2] at h
      have hns2 : Complex.normSq (ρ j) ≤ 2*(ρ j).im^2 := by
        rw [hns_eq]; have := sq_abs (ρ j).im; nlinarith
      calc ‖Zℂ j s‖ ≤ C / (ρ j).im^2 := hkey
        _ = (2*C) / (2*(ρ j).im^2) := by ring
        _ ≤ (2*C) / Complex.normSq (ρ j) :=
            div_le_div_of_nonneg_left (by positivity) hns hns2
        _ = 2*C * (Complex.normSq (ρ j))⁻¹ := div_eq_mul_inv _ _
        _ ≤ M₀ * (Complex.normSq (ρ j))⁻¹ := by
            have h4c : (0:ℝ) ≤ 4*c/δ := by positivity
            gcongr; rw [hM₀_def]; linarith
    ·
      have hγ2 : (ρ j).im^2 < 1 := by
        have ⟨h1, h2⟩ := abs_lt.mp hγ; nlinarith
      have hns2 : Complex.normSq (ρ j) < 2 := by rw [hns_eq]; linarith
      calc ‖Zℂ j s‖ ≤ 2*c/δ := hcrude j s (hV_re s hsV)
        _ = (4*c/δ) * (2:ℝ)⁻¹ := by ring
        _ ≤ (4*c/δ) * (Complex.normSq (ρ j))⁻¹ := by gcongr
        _ ≤ M₀ * (Complex.normSq (ρ j))⁻¹ := by
            gcongr; rw [hM₀_def]; linarith

  have hGℂ : AnalyticOnNhd ℂ (fun s => ∑' j, Zℂ j s) V :=
    (differentiableOn_tsum_of_summable_norm hu_sum hZℂ_diff hV_open
      hF_le).analyticOnNhd hV_open

  have hmap : Set.MapsTo ((↑) : ℝ → ℂ) (Set.Ioo (1/2-ε'') (7/2)) V := fun σ hσ => by
    rw [Metric.mem_ball, Complex.dist_eq,
      show ((σ:ℂ)-(2:ℂ)) = ((σ-2:ℝ):ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, hr_def]
    obtain ⟨h1, h2⟩ := hσ; rw [abs_lt]; constructor <;> linarith
  have hGℝ : AnalyticOnNhd ℝ (fun σ : ℝ => (∑' j, Zℂ j (σ:ℂ)).re)
      (Set.Ioo (1/2-ε'') (7/2)) :=
    (Complex.reCLM.analyticOnNhd _).comp
      ((hGℂ.restrictScalars).comp (Complex.ofRealCLM.analyticOnNhd _) hmap)
      (Set.mapsTo_univ _ _)

  refine hGℝ.congr isOpen_Ioo (fun σ hσ => ?_)
  have hsum_σ : Summable (fun j => Zℂ j (σ:ℂ)) :=
    .of_norm_bounded hu_sum (fun j => hF_le j σ (hmap hσ))
  rw [Complex.re_tsum hsum_σ]
  refine tsum_congr (fun j => ?_)

  have hZreal : Zℂ j (σ:ℂ)
      = ((∫ x in Set.Ioi (0:ℝ),
          F x * (Real.exp (-((σ-(ρ j).re)*x)) + Real.exp (-((σ+(ρ j).re-1)*x)))
            * Real.cos ((ρ j).im*x) : ℝ) : ℂ) := by
    simp only [Zℂ]
    have hpt : ∀ x : ℝ, (F x:ℂ)
        * (Complex.exp (-(((σ:ℂ)-(ρ j).re)*x)) + Complex.exp (-(((σ:ℂ)+(ρ j).re-1)*x)))
        * (Real.cos ((ρ j).im*x):ℂ)
      = ((F x * (Real.exp (-((σ-(ρ j).re)*x)) + Real.exp (-((σ+(ρ j).re-1)*x)))
          * Real.cos ((ρ j).im*x) : ℝ) : ℂ) := fun x => by
      push_cast; ring
    simp_rw [hpt]
    exact integral_ofReal
  rw [hZreal, Complex.ofReal_re]

set_option maxHeartbeats 12800000 in

private theorem gapsw80_t71_primeSum_analytic {F : ℝ → ℝ}
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hdecay : ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))
    (K : Type) [Field K] [NumberField K] {ε' : ℝ} (hε' : ε' < ε) :
    AnalyticOnNhd ℝ
      (fun σ : ℝ => ∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ,
        Real.log (Ideal.absNorm p.1.1 : ℕ)
          * F (((p.2 : ℝ) + 1) * Real.log (Ideal.absNorm p.1.1 : ℕ))
          * ((Ideal.absNorm p.1.1 : ℕ) : ℝ) ^ (-(((p.2 : ℝ) + 1) * σ)))
      (Set.Ioi (1 / 2 - ε')) := by
  have _em := Classical.em
  set δ : ℝ := ε - ε' with hδ_def
  have hδp : 0 < δ := by rw [hδ_def]; linarith

  have hN2 : ∀ (P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}),
      (2:ℝ) ≤ ((Ideal.absNorm P.1 : ℕ) : ℝ) := fun P => by
    have h : 2 ≤ Ideal.absNorm P.1 := gapsw80_t27_one_lt_absNorm_prime P
    exact_mod_cast h
  have hNpos : ∀ (P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}),
      (0:ℝ) < ((Ideal.absNorm P.1 : ℕ) : ℝ) := fun P =>
    lt_of_lt_of_le two_pos (hN2 P)
  have hlNpos : ∀ (P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}),
      0 < Real.log ((Ideal.absNorm P.1 : ℕ) : ℝ) := fun P =>
    Real.log_pos (by linarith [hN2 P])
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two

  set U : Set ℂ := {s : ℂ | 1/2 - ε' < s.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set fℂ : ({P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ) → ℂ → ℂ := fun q s =>
    ((Real.log ((Ideal.absNorm q.1.1:ℕ):ℝ)
      * F (((q.2:ℝ)+1) * Real.log ((Ideal.absNorm q.1.1:ℕ):ℝ))) : ℂ)
    * Complex.exp (-((((q.2:ℝ)+1) * Real.log ((Ideal.absNorm q.1.1:ℕ):ℝ) : ℂ) * s))

  have hf_diff : ∀ q, DifferentiableOn ℂ (fℂ q) U := fun q =>
    ((Complex.differentiable_exp.comp
      (((differentiable_const _).mul differentiable_id).neg)).const_mul _).differentiableOn

  set u : ({P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ) → ℝ := fun q =>
    (2*c/δ) * ((Ideal.absNorm q.1.1:ℕ):ℝ)^(-(1+δ/2):ℝ) * ((1:ℝ)/2)^q.2
  have hu_nn : ∀ q, 0 ≤ u q := fun q =>
    mul_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (hNpos q.1).le _)) (by positivity)
  have hT28 : Summable (fun P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      ((Ideal.absNorm P.1:ℕ):ℝ)^(-(1+δ/2):ℝ)) := by
    refine (gapsw80_t28_summable_norm_absNorm_cpow (K:=K)
      (s := ((1+δ/2:ℝ):ℂ)) (by rw [Complex.ofReal_re]; linarith)).congr (fun P => ?_)
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (hNpos P), Complex.neg_re,
      Complex.ofReal_re]
  have hu_sum : Summable u := by
    rw [summable_prod_of_nonneg hu_nn]
    refine ⟨fun P => ?_, ?_⟩
    · simp only [u]; exact summable_geometric_two.mul_left _
    · refine (hT28.mul_left ((2*c/δ) * (∑' m:ℕ, ((1:ℝ)/2)^m))).congr (fun P => ?_)
      simp only [u]; rw [tsum_mul_left]; ring
  have hF_le : ∀ q (s : ℂ), s ∈ U → ‖fℂ q s‖ ≤ u q := fun q s hs => by
    obtain ⟨P, m⟩ := q
    have hsre : 1/2 - ε' < s.re := hs
    set lN := Real.log ((Ideal.absNorm P.1:ℕ):ℝ) with hlN_def
    have hlN : 0 < lN := hlNpos P
    have hm1lN : 0 < ((m:ℝ)+1) * lN := by positivity
    simp only [fℂ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im,
      mul_zero, zero_mul, sub_zero, add_zero, _root_.neg_zero, abs_mul, ← hlN_def]
    rw [abs_of_pos hlN]

    have hFd : |F (((m:ℝ)+1)*lN)|
        ≤ c * Real.exp (-(1/2+ε) * (((m:ℝ)+1)*lN)) :=
      (hdecay _).trans_eq (by rw [abs_of_pos hm1lN])
    have hexp_comb : Real.exp (-(1/2+ε)*(((m:ℝ)+1)*lN))
          * Real.exp (-(((m:ℝ)+1)*lN*(1/2-ε')))
        = Real.exp (-(((m:ℝ)+1)*lN*(1+δ))) := by
      rw [← Real.exp_add]; congr 1; rw [hδ_def]; ring
    have h1 : lN * |F (((m:ℝ)+1)*lN)| * Real.exp (-(((m:ℝ)+1)*lN*s.re))
        ≤ c * lN * Real.exp (-(((m:ℝ)+1)*lN*(1+δ))) := by
      calc lN * |F (((m:ℝ)+1)*lN)| * Real.exp (-(((m:ℝ)+1)*lN*s.re))
          ≤ lN * (c * Real.exp (-(1/2+ε)*(((m:ℝ)+1)*lN)))
              * Real.exp (-(((m:ℝ)+1)*lN*(1/2-ε'))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hFd hlN.le)
              (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
              (by positivity)
        _ = c * lN * (Real.exp (-(1/2+ε)*(((m:ℝ)+1)*lN))
              * Real.exp (-(((m:ℝ)+1)*lN*(1/2-ε')))) := by ring
        _ = c * lN * Real.exp (-(((m:ℝ)+1)*lN*(1+δ))) := by rw [hexp_comb]

    have h2 : c * lN * Real.exp (-(((m:ℝ)+1)*lN*(1+δ))) ≤ u (P, m) := by

      have hu_eq : u (P, m)
          = (2*c/δ) * Real.exp (-(1+δ/2)*lN) * ((1:ℝ)/2)^m := by
        simp only [u]; congr 1; congr 1
        rw [Real.rpow_def_of_pos (hNpos P), ← hlN_def]; ring_nf
      rw [hu_eq]

      have hsplit : Real.exp (-(((m:ℝ)+1)*lN*(1+δ)))
          = Real.exp (-(1+δ/2)*lN) * Real.exp (-(δ/2)*lN)
            * Real.exp (-(m:ℝ)*((1+δ)*lN)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      rw [hsplit]

      have ha : lN * Real.exp (-(δ/2)*lN) ≤ 2/δ := by
        set t : ℝ := (δ/2)*lN with ht_def
        have hte_le : t ≤ Real.exp t :=
          le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp t)
        have hte : t * Real.exp (-t) ≤ 1 := by
          have h := mul_le_mul_of_nonneg_right hte_le (Real.exp_pos (-t)).le
          rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
        have heq : lN * Real.exp (-(δ/2)*lN) = (2/δ) * (t * Real.exp (-t)) := by
          simp only [ht_def, neg_mul]; field_simp
        linarith [mul_le_mul_of_nonneg_left hte (show (0:ℝ) ≤ 2/δ by positivity),
          heq]

      have hb : Real.exp (-(m:ℝ)*((1+δ)*lN)) ≤ ((1:ℝ)/2)^m := by
        have hkey : Real.log 2 ≤ (1+δ)*lN := by
          have hll : Real.log 2 ≤ lN := Real.log_le_log two_pos (hN2 P)
          nlinarith
        have hhalf : ((1:ℝ)/2)^m = Real.exp (-(m:ℝ)*Real.log 2) := by
          rw [← Real.rpow_natCast (1/2 : ℝ) m,
            Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/2),
            one_div, Real.log_inv]
          ring_nf
        rw [hhalf]
        have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
        exact Real.exp_le_exp.mpr (by nlinarith)
      calc c * lN * (Real.exp (-(1+δ/2)*lN) * Real.exp (-(δ/2)*lN)
              * Real.exp (-(m:ℝ)*((1+δ)*lN)))
          = (c * Real.exp (-(1+δ/2)*lN)) * (lN * Real.exp (-(δ/2)*lN))
              * Real.exp (-(m:ℝ)*((1+δ)*lN)) := by ring
        _ ≤ (c * Real.exp (-(1+δ/2)*lN)) * (2/δ)
              * Real.exp (-(m:ℝ)*((1+δ)*lN)) := by gcongr
        _ ≤ (c * Real.exp (-(1+δ/2)*lN)) * (2/δ) * ((1:ℝ)/2)^m := by
            gcongr
        _ = (2*c/δ) * Real.exp (-(1+δ/2)*lN) * ((1:ℝ)/2)^m := by ring
    exact h1.trans h2

  have hGℂ : AnalyticOnNhd ℂ (fun s => ∑' q, fℂ q s) U :=
    (differentiableOn_tsum_of_summable_norm hu_sum hf_diff hU_open
      hF_le).analyticOnNhd hU_open

  have hmap : Set.MapsTo ((↑) : ℝ → ℂ) (Set.Ioi (1/2-ε')) U := fun σ hσ => by
    simp only [U, Set.mem_setOf_eq, Complex.ofReal_re]; exact hσ
  have hGℝ : AnalyticOnNhd ℝ (fun σ : ℝ => (∑' q, fℂ q (σ:ℂ)).re)
      (Set.Ioi (1/2-ε')) :=
    (Complex.reCLM.analyticOnNhd _).comp
      ((hGℂ.restrictScalars).comp (Complex.ofRealCLM.analyticOnNhd _) hmap)
      (Set.mapsTo_univ _ _)

  refine hGℝ.congr isOpen_Ioi (fun σ hσ => ?_)
  have hsum_σ : Summable (fun q => fℂ q (σ:ℂ)) :=
    .of_norm_bounded hu_sum (fun q => hF_le q σ (hmap hσ))
  have hre_tsum : (∑' q, fℂ q (σ:ℂ)).re = ∑' q, (fℂ q (σ:ℂ)).re :=
    Complex.re_tsum hsum_σ
  rw [hre_tsum]
  refine tsum_congr (fun q => ?_)
  obtain ⟨P, m⟩ := q

  have hreal : fℂ (P, m) (σ:ℂ)
      = ((Real.log ((Ideal.absNorm P.1:ℕ):ℝ)
          * F (((m:ℝ)+1) * Real.log ((Ideal.absNorm P.1:ℕ):ℝ))
          * Real.exp (-(((m:ℝ)+1) * Real.log ((Ideal.absNorm P.1:ℕ):ℝ) * σ)) : ℝ) : ℂ) := by
    simp only [fℂ]; push_cast; ring
  rw [hreal, Complex.ofReal_re, Real.rpow_def_of_pos (hNpos P),
    show Real.log ((Ideal.absNorm P.1:ℕ):ℝ) * (-(((m:ℝ)+1)*σ))
      = -(((m:ℝ)+1) * Real.log ((Ideal.absNorm P.1:ℕ):ℝ) * σ) from by ring]

set_option maxHeartbeats 3200000 in

private theorem gapsw80_t71_primeSum_at_half {F : ℝ → ℝ}
    (K : Type) [Field K] [NumberField K] :
    (∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ,
      Real.log (Ideal.absNorm p.1.1 : ℕ)
        * F (((p.2 : ℝ) + 1) * Real.log (Ideal.absNorm p.1.1 : ℕ))
        * ((Ideal.absNorm p.1.1 : ℕ) : ℝ) ^ (-(((p.2 : ℝ) + 1) * (1/2:ℝ))))
    = gapsw52_t2_OdlyzkoPrimeIdealSum F K := by
  have _em := Classical.em
  unfold gapsw52_t2_OdlyzkoPrimeIdealSum gapsw52_t2_odlyzkoPrimeIdealTerm
  refine tsum_congr (fun q => ?_)
  congr 1
  ring_nf

set_option maxHeartbeats 3200000 in

private theorem gapsw80_t71_poleTilde_at_half {F : ℝ → ℝ} (hcont : Continuous F)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hdecay : ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) :
    ((2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((1/2:ℝ) * x)))
       + (2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(((1/2:ℝ) - 1) * x))))
    = gapsw80_t13_poleTerm F := by
  have _em := Classical.em

  have hint : ∀ s : ℝ, |s| ≤ 1/2 →
      IntegrableOn (fun x => F x * Real.exp (s * x)) (Set.Ioi 0) := by
    intro s hs
    refine Integrable.mono'
      (((exp_neg_integrableOn_Ioi 0 hε).congr_fun
        (fun x _ => by rw [neg_mul]) measurableSet_Ioi).const_mul c)
      ((hcont.mul (Real.continuous_exp.comp (continuous_const.mul
        continuous_id))).aestronglyMeasurable.restrict)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    calc |F x| * Real.exp (s*x)
        ≤ (c * Real.exp (-(1/2+ε) * |x|)) * Real.exp ((1/2) * x) :=
          mul_le_mul (hdecay x)
            (Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_right ((abs_le.mp hs).2) hx0.le))
            (Real.exp_pos _).le (le_trans (abs_nonneg _) (hdecay x))
      _ = c * Real.exp (-(ε*x)) := by
          rw [abs_of_pos hx0, mul_assoc, ← Real.exp_add]; ring_nf
  have hi1 : IntegrableOn (fun x => F x * Real.exp (-(x/2))) (Set.Ioi 0) :=
    (hint (-(1/2)) (by norm_num)).congr_fun
      (fun x _ => by ring_nf) measurableSet_Ioi
  have hi2 : IntegrableOn (fun x => F x * Real.exp (x/2)) (Set.Ioi 0) :=
    (hint (1/2) (by norm_num)).congr_fun
      (fun x _ => by ring_nf) measurableSet_Ioi

  have hL1 : (∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((1/2:ℝ)*x)))
           = ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(x/2)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring_nf)
  have hL2 : (∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(((1/2:ℝ)-1)*x)))
           = ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (x/2) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring_nf)
  rw [hL1, hL2, gapsw80_t13_poleTerm_pin, ← mul_add, ← integral_add hi1 hi2]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)

set_option maxHeartbeats 3200000 in

private theorem gapsw80_t71_arch_at_half {F : ℝ → ℝ}
    (hF : gapsw50_t2_OdlyzkoAdmissibleKernel F)
    (hc' : gapsw80_t62_ArchGammaKernelIdentityCorrected) (n : ℕ) :
    -(1 / Real.pi) * ∫ t : ℝ,
        (((n:ℝ)/2) * (logDeriv Gammaℂ ((1/2:ℝ)+(t:ℂ)*I)).re)
          * (∫ x, F x * Real.cos (t*x))
      = (n:ℝ) * gapsw80_t18_archDerived F + (n:ℝ) * Real.log 2 := by
  have _em := Classical.em
  have hkey := hc' F hF

  have hcoe : (((1/2:ℝ):ℂ) : ℂ) = (1/2:ℂ) := by push_cast; ring

  have hint_eq :
      (∫ t : ℝ, (((n:ℝ)/2) * (logDeriv Gammaℂ (((1/2:ℝ):ℂ)+(t:ℂ)*I)).re)
          * (∫ x, F x * Real.cos (t*x)))
        = ((n:ℝ)/2) * ∫ t : ℝ, (logDeriv Gammaℂ (1/2+(t:ℂ)*I)).re
            * (∫ x, F x * Real.cos (t*x)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [hcoe]; ring
  rw [hint_eq, ← mul_assoc, mul_comm (-(1/Real.pi)) ((n:ℝ)/2), mul_assoc, hkey]
  ring

set_option maxHeartbeats 25600000 in

theorem gapsw80_t71_analyticExtensionIdentityC2 :
    gapsw80_t70_AnalyticExtensionIdentityC2 := by
  have _em := Classical.em
  rw [gapsw80_t70_analyticExtensionIdentityC2_pin]
  intro hc' K _ _ _ B ρ hstrip hsum hexp F hF hFC2 hs2
  obtain ⟨hcd, c, ε, hc, hε, hdecay⟩ := id hFC2
  have hcontF : Continuous F := hcd.continuous
  have hdecay0 : ∀ x, |F x| ≤ c * Real.exp (-(1/2+ε)*|x|) := fun x => by
    have h := hdecay 0 x; simpa using h
  set n := finrank ℚ K with hn_def
  have hnpos : 0 < n := Module.finrank_pos
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'

  set Aσ : ℝ → ℝ := fun σ => ∫ t : ℝ,
    (((n:ℝ)/2) * (logDeriv Gammaℂ ((σ:ℂ)+(t:ℂ)*I)).re)
      * (∫ x, F x * Real.cos (t*x))
  set Zσ : ℝ → ℝ := fun σ => ∑' j, ∫ x in Set.Ioi (0:ℝ),
    F x * (Real.exp (-((σ-(ρ j).re)*x)) + Real.exp (-((σ+(ρ j).re-1)*x)))
      * Real.cos ((ρ j).im*x)
  set Ptσ : ℝ → ℝ := fun σ =>
    (2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(σ*x)))
    + (2 * ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((σ-1)*x)))
  set Psσ : ℝ → ℝ := fun σ => ∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ,
    Real.log (Ideal.absNorm p.1.1:ℕ)
      * F (((p.2:ℝ)+1) * Real.log (Ideal.absNorm p.1.1:ℕ))
      * ((Ideal.absNorm p.1.1:ℕ):ℝ)^(-(((p.2:ℝ)+1)*σ))
  set H : ℝ → ℝ := fun σ => -(1/Real.pi)*Aσ σ + Zσ σ - Ptσ σ + 2*Psσ σ

  have hsec1 : ∀ σ ∈ Set.Ioi (1:ℝ), H σ = Real.log |(discr K:ℝ)| := fun σ hσ => by
    have heq : (1/Real.pi) * Aσ σ - Zσ σ
        = -Real.log |(discr K:ℝ)| - Ptσ σ + 2 * Psσ σ := (hs2 σ hσ).2
    simp only [H]; linarith

  obtain ⟨δf, hδfp, hZan⟩ :=
    gapsw80_t71_zeroSideSigma_analytic hF hFC2 hstrip hsum
  set ε' : ℝ := min δf (min (ε/2) (1/4)) with hε'_def
  have hε'p : 0 < ε' := lt_min hδfp (lt_min (half_pos hε) (by norm_num))
  have hε'f : ε' ≤ δf := min_le_left _ _
  have hε'ε : ε' < ε := (min_le_right _ _).trans_lt
    ((min_le_left _ _).trans_lt (half_lt_self hε))
  have hε'h : ε' < 1/2 := (min_le_right _ _).trans_lt
    ((min_le_right _ _).trans_lt (by norm_num))
  set W : Set ℝ := Set.Ioo (1/2-ε') (7/2)
  have hW_open : IsOpen W := isOpen_Ioo
  have hW2 : (2:ℝ) ∈ W := ⟨by linarith, by norm_num⟩
  have hWhalf : (1/2:ℝ) ∈ W := ⟨by linarith, by norm_num⟩

  have hint2 : Integrable (fun t:ℝ => (logDeriv Gammaℂ ((2:ℝ)+(t:ℂ)*I)).re
      * (∫ x, F x * Real.cos (t*x))) := by
    have h1 : Integrable (fun t:ℝ =>
        (((n:ℝ)/2) * (logDeriv Gammaℂ (((2:ℝ):ℂ)+(t:ℂ)*I)).re)
          * (∫ x, F x * Real.cos (t*x))) := (hs2 2 one_lt_two).1
    refine (h1.const_mul (2/(n:ℝ))).congr
      (Filter.Eventually.of_forall fun t => ?_)
    field_simp

  have hA_an : AnalyticOnNhd ℝ Aσ W := by
    have h := gapsw80_t71_arch_integral_analytic hF hint2 hε'p hε'h
    refine ((analyticOnNhd_const (v:=(n:ℝ)/2)).mul h).congr
      hW_open (fun σ hσ => ?_)
    simp only [Aσ, Pi.mul_apply]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring

  have hZ_an : AnalyticOnNhd ℝ Zσ W :=
    hZan.mono (fun σ hσ => ⟨by linarith [hσ.1, hε'f], hσ.2⟩)

  have hPs_an : AnalyticOnNhd ℝ Psσ W :=
    (gapsw80_t71_primeSum_analytic hc hε hdecay0 K hε'ε).mono (fun σ hσ => hσ.1)

  have hPt_an : AnalyticOnNhd ℝ Ptσ W := by
    have hL0 := gapsw80_t71_laplace_analytic hcontF hc hε hdecay0 0
    have hUL_open : IsOpen {s:ℂ | -(1/2+ε) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re

    have hL0' : AnalyticOnNhd ℂ
        (fun s:ℂ => ∫ x in Set.Ioi (0:ℝ), (F x:ℂ) * Complex.exp (-(s*x)))
        {s:ℂ | -(1/2+ε) < s.re} :=
      hL0.congr hUL_open (fun s _ => setIntegral_congr_fun measurableSet_Ioi
        (fun x _ => by simp [Real.cos_zero]))

    have hmapL : Set.MapsTo ((↑):ℝ→ℂ) W {s:ℂ | -(1/2+ε) < s.re} := fun σ hσ => by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith [hσ.1, hε'p]

    have hmk : ∀ (g : ℝ → ℝ) (shift : ℂ),
        (∀ σ ∈ W, -(1/2+ε) < ((σ:ℂ)+shift).re) →
        (∀ (σ:ℝ) (x:ℝ), (F x:ℂ) * Complex.exp (-(((σ:ℂ)+shift)*x))
          = ((F x * Real.exp (-(g σ*x)):ℝ):ℂ)) →
        AnalyticOnNhd ℝ
          (fun σ:ℝ => ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(g σ*x))) W := by
      intro g shift hmaps hpt
      have haf : AnalyticOnNhd ℝ (fun σ:ℝ => (σ:ℂ)+shift) Set.univ :=
        (Complex.ofRealCLM.analyticOnNhd _).add analyticOnNhd_const
      have h := (Complex.reCLM.analyticOnNhd _).comp
        ((hL0'.restrictScalars).comp (haf.mono (Set.subset_univ _))
          (fun σ hσ => hmaps σ hσ)) (Set.mapsTo_univ _ _)
      refine h.congr hW_open (fun σ _ => ?_)
      show (∫ x in Set.Ioi (0:ℝ),
        (F x:ℂ) * Complex.exp (-(((σ:ℂ)+shift)*x))).re = _
      simp_rw [hpt σ]
      rw [show (∫ x in Set.Ioi (0:ℝ),
            ((F x * Real.exp (-(g σ*x)):ℝ):ℂ))
          = ((∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(g σ*x)):ℝ):ℂ)
          from integral_ofReal, Complex.ofReal_re]
    have hLr1 : AnalyticOnNhd ℝ
        (fun σ:ℝ => ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-(σ*x))) W :=
      hmk (fun σ => σ) 0
        (fun σ hσ => by simp only [add_zero, Complex.ofReal_re]; linarith [hσ.1, hε'p])
        (fun σ x => by push_cast; ring_nf)
    have hLr2 : AnalyticOnNhd ℝ
        (fun σ:ℝ => ∫ x in Set.Ioi (0:ℝ), F x * Real.exp (-((σ-1)*x))) W :=
      hmk (fun σ => σ-1) (-1)
        (fun σ hσ => by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re]
          linarith [hσ.1, hε'p])
        (fun σ x => by push_cast; ring_nf)
    exact ((analyticOnNhd_const (v:=(2:ℝ))).mul hLr1).add
      ((analyticOnNhd_const (v:=(2:ℝ))).mul hLr2)

  have hH_an : AnalyticOnNhd ℝ H W :=
    (((((analyticOnNhd_const (v:=-(1/Real.pi))).mul hA_an).add hZ_an).sub hPt_an).add
      ((analyticOnNhd_const (v:=(2:ℝ))).mul hPs_an))

  have hsec3 : H (1/2) = Real.log |(discr K:ℝ)| := by
    have hnhds2 : Set.Ioo (1:ℝ) (7/2) ∈ nhds (2:ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    have hfg : H =ᶠ[nhds (2:ℝ)] (fun _ => Real.log |(discr K:ℝ)|) :=
      Filter.eventuallyEq_of_mem hnhds2 (fun σ hσ => hsec1 σ hσ.1)
    have heqOn := hH_an.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const isPreconnected_Ioo hW2 hfg
    exact heqOn hWhalf

  simp only [H, Aσ, Zσ, Ptσ, Psσ] at hsec3

  have hAhalf := gapsw80_t71_arch_at_half hF hc' n

  have hZhalf : Zσ (1/2) = gapsw80_t21_zeroKernelSum F ρ :=
    gapsw80_t70_zeroSideSigma_at_half hF hFC2 hstrip hsum

  have hPthalf := gapsw80_t71_poleTilde_at_half hcontF hc hε hdecay0

  have hPshalf := gapsw80_t71_primeSum_at_half (F:=F) K

  rw [gapsw80_t18_archTermDerived_pin]
  simp only [Zσ, Ptσ, Psσ] at hZhalf hPthalf hPshalf
  linarith [hsec3, hAhalf, hZhalf, hPthalf, hPshalf]

end FLT.Gapsw80T71D2bpppbAnalyticContinuationProof
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_archTermDerived_le_log_abs_discr.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

theorem solution
    (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (F : ℝ → ℝ)
    (h1 : Differentiable ℝ F) (h2 : ∀ x : ℝ, F (-x) = F x) (h3 : F 0 = 1) (h4 : ∀ x : ℝ, 0 ≤ F x)
    (h5 : ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))
    (h6 : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      0 ≤ ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x))
    (h7 : ContDiff ℝ 2 F)
    (h8 : ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) :
    ((Module.finrank ℚ K : ℝ) * (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
        - ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2))))
      - 2 * ∫ x in Set.Ioi (0 : ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2))))
      + (Module.finrank ℚ K : ℝ) * Real.log 2 ≤ Real.log |(NumberField.discr K : ℝ)| := by
  classical

  obtain ⟨B, ρ, hstrip, hsum, hexp⟩ :
      FLT.Gapsw80T19B2ppHadamardDecomp.gapsw80_t19_HadamardExpansionAt K := by
    have h := FLT.Gapsw80T9ClassSumA1Closure.gapsw80_t9_pkg_spec K
    exact NumberField.exists_hadamard_logDeriv_expansion_of_completedZeta_package K
      (FLT.Gapsw80T9ClassSumA1Closure.gapsw80_t9_completedDedekindZeta K)
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

  have hFStrip : FLT.Gapsw80T23OdlyzkoKernelStripRemint.gapsw80_t23_OdlyzkoAdmissibleKernelStrip F :=
    ⟨h1, h2, h3, h4, h5, h6⟩
  have hFC2 : FLT.Gapsw80T69AdmC2RemintZktSummable.gapsw80_t69_KernelC2Decay F := ⟨h7, h8⟩
  have hFLine : FLT.Gapsw50T2ExplicitFormulaDecompositionPin.gapsw50_t2_OdlyzkoAdmissibleKernel F :=
    FLT.Gapsw80T23OdlyzkoKernelStripRemint.gapsw80_t23_stripAdmissible_implies_lineAdmissible hFStrip

  have hb''' : FLT.Gapsw80T69AdmC2RemintZktSummable.gapsw80_t69_ContourPairedExplicitFormulaC2 :=
    FLT.Gapsw80T70D2bpppZeroSideEvalSubDecomp.gapsw80_t70_D2bpppb_implies_D2bppp
      FLT.Gapsw80T71D2bpppbAnalyticContinuationProof.gapsw80_t71_analyticExtensionIdentityC2
  have hid := hb''' FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint.gapsw80_t67_D2cp_closed
    FLT.Gapsw80T62ArchGammaKernelRemintWire.gapsw80_t62_D2d_closed K B ρ hstrip hsum hexp F hFLine hFC2
  have hPnn : 0 ≤ 2 * FLT.Gapsw52T2CarrierContentAtoms.gapsw52_t2_OdlyzkoPrimeIdealSum F K :=
    mul_nonneg (by norm_num)
      (FLT.Gapsw52T2CarrierContentAtoms.gapsw52_t2_odlyzkoPrimeIdealSum_nonneg F h4 K)
  have hZnn : 0 ≤ FLT.Gapsw80T21D2SubDecompWire.gapsw80_t21_zeroKernelSum F ρ :=
    FLT.Gapsw80T24StripMigrationChainStart.gapsw80_t24_zeroKernelSum_nonneg_of_stripAdmissible
      hFStrip hstrip
  simp only [FLT.Gapsw80T18ArchDerivedA34Redecomp.gapsw80_t18_archTermDerived,
    FLT.Gapsw80T18ArchDerivedA34Redecomp.gapsw80_t18_archDerived,
    FLT.Gapsw80T13AffineArchTermA34Redecomp.gapsw80_t13_poleTerm] at hid
  linarith

end S_NumberField_archTermDerived_le_log_abs_discr
end P2MW
export P2MW.S_NumberField_archTermDerived_le_log_abs_discr (solution)
