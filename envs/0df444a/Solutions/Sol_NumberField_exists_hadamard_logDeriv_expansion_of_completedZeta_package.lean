-- Prove2me | solution 1 for NumberField.exists_hadamard_logDeriv_expansion_of_completedZeta_package
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6cfa588d-7126-5e19-9a19-e2880c8f31a5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

namespace Asymptotics
p2m_export "Asymptotics" "isBigO_atTop_natCast_rpow_of_tendsto_div_rpow"
p2m_open "Asymptotics"
end Asymptotics
namespace Classical
p2m_export "Classical" "em by_cases decEq not_not"
p2m_open "Classical"
end Classical
namespace Complex
p2m_export "Complex" "abs_re_le_norm log_exp differentiableAt_exp one_re continuous_re re sqrt re_ofNat ofReal_re add_re normSq_pos sqrt_one borelCaratheodory_zero ofReal_ne_zero norm_real hasSum_taylorSeries_neg_log div_natCast_re summable_ofReal im_ofNat normSq_nonneg re_le_norm Gammaℝ exp_ne_zero ofReal_natCast norm_exp_sub_one_le norm_natCast ofReal_neg im hasSum_iff normSq_zero ofReal_intCast exp_sum Gamma_ne_zero normSq_eq_norm_sq hasSum_re normSq normSq_apply differentiableOn_compl_singleton_and_continuousAt_iff differentiableAt_Gamma cpow_neg exists zero_re mk.injEq norm_exp_sub_one_sub_id_le ofReal exp_neg neg_re sub_re norm_natCast_cpow_of_pos div_ofNat_re cpow_def_of_ne_zero cpow_add mul_cpow_ofReal_nonneg exp mk norm_exp norm_log_one_add_sub_self_le Gammaℝ_ne_zero_of_re_pos exp_zero norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le norm_le_of_forall_mem_frontier_norm_le ofReal_inj exp_log natCast_re Gammaℂ ofReal_cpow continuous_ofReal log_zero logDeriv_exp cpow_nat_mul mul_re log_mul ofReal_im log Gammaℂ_def ext I exp_nat_mul re_tsum exp_add"
p2m_open "Complex"
end Complex
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
namespace Gapsw80T16XiRightHalfBoundProof
end FLT.Gapsw80T16XiRightHalfBoundProof
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
namespace Gapsw80T8MellinGammaPartialZeta
end FLT.Gapsw80T8MellinGammaPartialZeta
namespace FLT
namespace Gapsw80T9ClassSumA1Closure
end FLT.Gapsw80T9ClassSumA1Closure
namespace Filter
p2m_export "Filter" "frequently_cofinite_iff_infinite NeBot eventually_atTop mk pi Tendsto mem_comap map_congr univ_mem eventually_cofinite atTop tendsto_pow_atTop eventuallyEq_iff_exists_mem unique mk.injEq map_id Tendsto.const_mul_atTop map cofinite tendsto_id Eventually.of_forall"
p2m_open "Filter"
end Filter
namespace Ideal
p2m_export "Ideal" "mem_span_singleton prime_of_isPrime under_def top_mul span_singleton_generator span_singleton_zero IsPrime.under absNorm_span_singleton absNorm_eq_zero_iff pi absNorm_top span isCoprime_span_singleton_iff sup_mul_inf prod mem_normalizedFactors_iff sup_mul mul_le_left span_singleton_prime absNorm_ne_zero_iff span_singleton_mul_span_singleton finite_setOf_absNorm_le dvd_iff_le map_id map span_singleton_le_iff_mem absNorm_ne_zero_iff_mem_nonZeroDivisors mul_top ext absNorm absNorm_bot le_of_dvd map_coe IsPrime mem_comap finite_setOf_absNorm_eq finiteQuotientOfFreeOfNeBot under absNorm_mem isPrime_of_prime mul_sup card_norm_le_eq_card_norm_le_add_one absNorm_ne_zero_of_nonZeroDivisors absNorm_eq_one_iff absNorm_dvd_absNorm_of_le mul_le_right mem_span_singleton_self"
p2m_open "Ideal"
end Ideal
namespace MeasureTheory
p2m_open "MeasureTheory"
end MeasureTheory
namespace Metric
p2m_export "Metric" "sphere isBounded_ball mem_closedBall nonempty_closedBall closedBall_subset_closedBall ball closedBall isOpen_ball"
p2m_open "Metric"
end Metric
namespace Module
p2m_export "Module" "Injective support Free.chooseBasis finrank Free mk Finite.of_injective End finrank_eq_card_chooseBasisIndex IsPrincipal"
p2m_open "Module"
end Module
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces discr mk InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace discr_ne_zero Ideal.tendsto_norm_le_div_atTop₀"
p2m_open "NumberField"
end NumberField
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces discr mk InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace discr_ne_zero Ideal.tendsto_norm_le_div_atTop₀"
namespace InfinitePlace
p2m_export "NumberField.InfinitePlace" "nrRealPlaces card_mono mk ext nrComplexPlaces apply"
p2m_open "NumberField.InfinitePlace NumberField"
end NumberField.InfinitePlace
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces discr mk InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace discr_ne_zero Ideal.tendsto_norm_le_div_atTop₀"
namespace mixedEmbedding
p2m_export "NumberField.mixedEmbedding" "norm_real"
p2m_open "NumberField.mixedEmbedding NumberField"
end NumberField.mixedEmbedding
namespace Real
p2m_export "Real" "tendsto_pow_log_div_mul_add_atTop sqrt_pos log_le_sub_one_of_pos log_pos norm norm_natCast log_nonneg exp_zero sqrt_le_sqrt log_le_rpow_div rpow_mul pi_ne_zero norm_exp_sub_one_sub_id_le sqrt_div_self log_zero log_exp one_le_exp tendsto_sqrt_atTop exp_ne_zero mul_self_sqrt log_sqrt exp_nat_mul exp_one_lt_d9 exp Gamma_ne_zero exp_pos exp_le_exp sqrt_nonneg sqrt_eq_rpow logDeriv_exp exp_sum differentiableAt_exp sqrt_one rpow_pos_of_pos rpow_natCast differentiableAt_Gamma log norm_of_nonneg norm_eq_abs exp_neg mk log_nonpos exp_log log_le_iff_le_exp log_mul rpow_one log_le_log sqrt_mul le_exp_of_log_le exp_add rpow_lt_one_of_one_lt_of_neg log_pow log_div sqrt"
p2m_open "Real"
end Real
namespace Set
p2m_export "Set" "toFinite Countable.mono card_empty ncard_le_ncard Finite.mem_toFinset preimage Icc not_subset ncard_eq_toFinset_card Icc_succ_left_eq_Ioc mem_compl_iff image subset_univ ext mem_toFinset notMem_empty coe_eq_subtype mem_nsmul countable_iUnion pi isEmpty_coe_sort Ioo eq_empty_iff_forall_notMem toFinset Ioc finite_empty not_infinite mem_singleton_iff mem_biUnion mem_univ Finite.subset Infinite.exists_accPt_of_subset_isCompact mem_Ioo EqOn mem_image prod_insert inter_subset_inter_right mem_singleton InjOn mem_insert_of_mem finite_coe_iff mem_setOf_eq mem_preimage mem_iUnion mem_insert_iff univ prod_singleton inter_subset_right mem_insert prod prod_empty left_mem_Icc"
p2m_open "Set"
end Set
namespace Topology
p2m_open "Topology"
end Topology
namespace UniqueFactorizationMonoid
p2m_export "UniqueFactorizationMonoid" "mk mem_normalizedFactors_iff normalizedFactors_prod_eq prod_normalizedFactors_eq normalizedFactors"
p2m_open "UniqueFactorizationMonoid"
end UniqueFactorizationMonoid

namespace FLT
namespace Gapsw80T36D1appXiEndpointResidueProof
end FLT.Gapsw80T36D1appXiEndpointResidueProof
namespace FLT
namespace Gapsw80T43CompletedZetaRealSuperlinearProof
end FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
namespace FLT
namespace Gapsw80T9ClassSumA1Closure
end FLT.Gapsw80T9ClassSumA1Closure

class S18.HADPkg (K : Type) [Field K] [NumberField K] where
  Λ : ℂ → ℂ
  diff : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ)
  FE : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s
  eqT1 : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s
  B1 : ∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖
  End : ∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0
  SL : ∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖

section
namespace FLT
namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"

noncomputable def gapsw80_t1_completedDedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|discr K| : ℤ) : ℂ)) ^ (s / 2)
    * Gammaℝ s ^ nrRealPlaces K
    * Gammaℂ s ^ nrComplexPlaces K
    * dedekindZeta K s
end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
end

section
namespace FLT
namespace Gapsw80T9ClassSumA1Closure
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"
variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

noncomputable def gapsw80_t9_completedDedekindZeta (s : ℂ) : ℂ := S18.HADPkg.Λ (K := K) s

noncomputable abbrev gapsw80_t9_gammaFactor (s : ℂ) : ℂ :=
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
theorem gapsw80_t9_completedDedekindZeta_FE {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s :=
  S18.HADPkg.FE s hs0 hs1
theorem gapsw80_t9_FE_halfplane {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s :=
  S18.HADPkg.FE s (fun h => by rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num))
    (fun h => by rw [h, Complex.one_re] at hs; exact absurd hs (lt_irrefl 1))
theorem gapsw80_t9_isClosed_pair : IsClosed ({(0:ℂ), 1} : Set ℂ) :=
  (Set.toFinite _).isClosed
theorem gapsw80_t9_differentiableOn_completedDedekindZeta :
    DifferentiableOn ℂ (gapsw80_t9_completedDedekindZeta K) {(0:ℂ), 1}ᶜ :=
  S18.HADPkg.diff
theorem gapsw80_t9_analyticOnNhd_completedDedekindZeta :
    AnalyticOnNhd ℂ (gapsw80_t9_completedDedekindZeta K) {(0:ℂ), 1}ᶜ :=
  (gapsw80_t9_differentiableOn_completedDedekindZeta K).analyticOnNhd
    (gapsw80_t9_isClosed_pair).isOpen_compl
end FLT.Gapsw80T9ClassSumA1Closure
end

section
namespace FLT
namespace Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T9ClassSumA1Closure

def gapsw80_t11_XiOrderOneHadamard : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K],
    ∃ ξ : ℂ → ℂ,
      Differentiable ℂ ξ ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
        ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) ∧
      (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖)
end FLT.Gapsw80T11ExplicitFormulaA34Decomp
namespace FLT
namespace Gapsw80T16XiRightHalfBoundProof
open FLT.Gapsw80T11ExplicitFormulaA34Decomp

theorem gapsw80_t16_B1_closed : gapsw80_t11_XiOrderOneHadamard :=
  fun K _ _ _ => S18.HADPkg.B1
end FLT.Gapsw80T16XiRightHalfBoundProof
end

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T10DedekindZetaBridgeA1Discharge

p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.mixedEmbedding"
open FLT.Gapsw80T8MellinGammaPartialZeta FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
p2m_open "Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Module P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Module Real P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.MeasureTheory Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Ideal P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Ideal NumberField.Ideal Asymptotics P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Asymptotics"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Classical nonZeroDivisors Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

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
      = gapsw80_t1_completedDedekindZeta K s :=
  S18.HADPkg.eqT1 s hs

end FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T19B2ppHadamardDecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace Module P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Module"

def gapsw80_t19_HadamardExpansionAt (K : Type) [Field K] [NumberField K] [S18.HADPkg K] :
    Prop :=
  ∃ (B : ℂ) (ρ : ℕ → ℂ),
    (∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) ∧
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
      logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
        = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)

def gapsw80_t19_XiLogDerivZeroExpansion : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], gapsw80_t19_HadamardExpansionAt K

end FLT.Gapsw80T19B2ppHadamardDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T27D2d0EulerProductAncestor

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T20LambdaLogDerivProductRule
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T26D2dTwoConjunctDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

theorem gapsw80_t27_one_lt_absNorm_prime {K : Type} [Field K] [NumberField K] [S18.HADPkg K]
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
    [NumberField K] [S18.HADPkg K] (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) {s : ℂ}
    (hs : 1 < s.re) :
    ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)‖ < 1 :=
  gapsw80_t27_norm_natCast_cpow_lt_one (gapsw80_t27_one_lt_absNorm_prime p) hs

def gapsw80_t27_DedekindZetaEulerProductExpForm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ s : ℂ, 1 < s.re →
    Summable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      ‖((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)‖) ∧
    dedekindZeta K s = Complex.exp
      (∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥},
        -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)))

end FLT.Gapsw80T27D2d0EulerProductAncestor
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T20LambdaLogDerivProductRule

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T19B2ppHadamardDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace Module P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Module Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

theorem gapsw80_t20_discrBase_ne_zero :
    (((|discr K| : ℤ) : ℂ)) ≠ 0 := by
  have _em := Classical.em
  exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)

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

end FLT.Gapsw80T20LambdaLogDerivProductRule
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T28D2d0aSummabilityProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T27D2d0EulerProductAncestor
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"
open scoped nonZeroDivisors

theorem gapsw80_t28_one_sub_absNorm_cpow_ne_zero {K : Type} [Field K]
    [NumberField K] [S18.HADPkg K] (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) {s : ℂ}
    (hs : 1 < s.re) :
    1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  have _em := Classical.em
  have hlt := gapsw80_t27_norm_absNorm_cpow_lt_one p hs
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem gapsw80_t28_exp_neg_log_one_sub_absNorm_cpow {K : Type} [Field K]
    [NumberField K] [S18.HADPkg K] (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) {s : ℂ}
    (hs : 1 < s.re) :
    Complex.exp (-Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s)))
      = (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
  have _em := Classical.em
  rw [Complex.exp_neg,
    Complex.exp_log (gapsw80_t28_one_sub_absNorm_cpow_ne_zero p hs)]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t28_summable_norm_absNorm_cpow {K : Type} [Field K]
    [NumberField K] [S18.HADPkg K] {s : ℂ} (hs : 1 < s.re) :
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
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ s : ℂ, 1 < s.re →
    HasProd (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹) (dedekindZeta K s)

set_option maxHeartbeats 6400000 in

theorem gapsw80_t28_D2d0_of_D2d0b
    (hb : gapsw80_t28_DedekindZetaEulerProductHasProd) :
    gapsw80_t27_DedekindZetaEulerProductExpForm := by
  have _em := Classical.em
  intro K _ _ _ s hs
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
    [NumberField K] [S18.HADPkg K] {s : ℂ} (hs : 1 < s.re) :
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

set_option maxHeartbeats 3200000 in

theorem gapsw80_t28_falsif_D2d0b_loadbearing
    (K : Type) [Field K] [NumberField K] [S18.HADPkg K] {s : ℂ} (hs : 1 < s.re)
    (hζ0 : dedekindZeta K s = 0) :
    ¬ gapsw80_t28_DedekindZetaEulerProductHasProd := by
  have _em := Classical.em
  intro hb
  exact Complex.exp_ne_zero _
    (((gapsw80_t28_D2d0_of_D2d0b hb) K s hs).2 ▸ hζ0)

end FLT.Gapsw80T28D2d0aSummabilityProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"
open scoped nonZeroDivisors

theorem gapsw80_t29_card_absNorm_eq_one (K : Type) [Field K] [NumberField K] [S18.HADPkg K] :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
  have _em := Classical.em
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun J => Subtype.ext
    (Ideal.absNorm_eq_one_iff.mp J.2)⟩

theorem gapsw80_t29_under_ne_bot {K : Type} [Field K] [NumberField K] [S18.HADPkg K]
    (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    Ideal.under ℤ p.1 ≠ ⊥ := by
  have _em := Classical.em
  have hN : Ideal.absNorm p.1 ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (le_of_lt (gapsw80_t27_one_lt_absNorm_prime p))
  rw [Submodule.ne_bot_iff]
  refine ⟨(Ideal.absNorm p.1 : ℤ), ?_, by exact_mod_cast hN⟩
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact Ideal.absNorm_mem p.1

noncomputable def gapsw80_t29_primeBelow {K : Type} [Field K] [NumberField K] [S18.HADPkg K]
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
    [NumberField K] [S18.HADPkg K] (p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    Ideal.under ℤ p.1
      = Ideal.span {((gapsw80_t29_primeBelow p : ℕ) : ℤ)} := by
  have _em := Classical.em
  rw [show ((gapsw80_t29_primeBelow p : ℕ) : ℤ)
      = (Submodule.IsPrincipal.generator (Ideal.under ℤ p.1)).natAbs from rfl,
    Int.span_natAbs, Ideal.span_singleton_generator]

section IdealCountCoprime
variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

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
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

theorem gapsw80_t29_term_coprime_mul (K : Type) [Field K] [NumberField K] [S18.HADPkg K]
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
    [NumberField K] [S18.HADPkg K] {s : ℂ} (hs : 1 < s.re) :
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
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ s : ℂ, 1 < s.re →
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
  intro K _ _ _ s hs
  set h : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} → ℂ :=
    fun p => (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-s))⁻¹ with hh_def

  have hmult : Multipliable h :=
    gapsw80_t28_sat_multipliable_one_sub_inv (K := K) hs

  let e := Equiv.sigmaFiberEquiv (@gapsw80_t29_primeBelow K _ _ _)

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
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex UniqueFactorizationMonoid P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.UniqueFactorizationMonoid"
open scoped nonZeroDivisors

abbrev gapsw80_t30_Fiber (K : Type) [Field K] [NumberField K] [S18.HADPkg K]
    (p : Nat.Primes) : Type :=
  {q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} //
    gapsw80_t29_primeBelow q = p}

theorem gapsw80_t30_primeBelow_dvd_absNorm {K : Type} [Field K]
    [NumberField K] [S18.HADPkg K] (q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    (gapsw80_t29_primeBelow q : ℕ) ∣ Ideal.absNorm q.1 := by
  have _em := Classical.em
  have hmem : (Ideal.absNorm q.1 : ℤ) ∈ Ideal.under ℤ q.1 := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem q.1
  rw [gapsw80_t29_under_eq_span_primeBelow, Ideal.mem_span_singleton]
    at hmem
  exact Int.natCast_dvd_natCast.mp hmem

theorem gapsw80_t30_natCast_mem_fiber {K : Type} [Field K] [NumberField K] [S18.HADPkg K]
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
    [NumberField K] [S18.HADPkg K] {p : Nat.Primes} (q : gapsw80_t30_Fiber K p) :
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
    [NumberField K] [S18.HADPkg K] (p : Nat.Primes) : Fintype (gapsw80_t30_Fiber K p) := by
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
    [NumberField K] [S18.HADPkg K] (q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥})
    {p : Nat.Primes} {e : ℕ} (hN : Ideal.absNorm q.1 ∣ (p : ℕ) ^ e) :
    gapsw80_t29_primeBelow q = p := by
  have _em := Classical.em
  have hpp : (gapsw80_t29_primeBelow q : ℕ) ∣ (p : ℕ) ^ e :=
    (gapsw80_t30_primeBelow_dvd_absNorm q).trans hN
  exact Subtype.ext (((Nat.prime_dvd_prime_iff_eq
    (gapsw80_t29_primeBelow q).2 p.2).mp
      ((gapsw80_t29_primeBelow q).2.prime.dvd_of_dvd_pow hpp)))

theorem gapsw80_t30_irreducible_of_primeSubtype {K : Type} [Field K]
    [NumberField K] [S18.HADPkg K] (q : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}) :
    Irreducible q.1 :=
  (Ideal.prime_of_isPrime q.2.2 q.2.1).irreducible

private def gapsw80_t30_GeomP (α : Type) [Fintype α] : Prop :=
  ∀ (ζ : α → ℂ), (∀ i, ‖ζ i‖ < 1) →
    HasSum (fun k : α → ℕ => ∏ i, ζ i ^ k i) (∏ i, (1 - ζ i)⁻¹)
      ∧ Summable (fun k : α → ℕ => ‖∏ i, ζ i ^ k i‖)

private theorem gapsw80_t30_geomP_pempty : gapsw80_t30_GeomP PEmpty := by
  have _em := Classical.em
  intro ζ _
  have hfin : (fun k : PEmpty → ℕ => ∏ i, ζ i ^ k i)
      = fun _ => (1 : ℂ) :=
    funext fun _ => by rw [Finset.univ_eq_empty, Finset.prod_empty]
  rw [hfin, Finset.univ_eq_empty, Finset.prod_empty]
  have h1 := hasSum_fintype (fun _ : PEmpty.{1} → ℕ => (1 : ℂ))
  have h1N := hasSum_fintype (fun _ : PEmpty.{1} → ℕ => ‖(1 : ℂ)‖)
  rw [show (∑ _ : PEmpty → ℕ, (1 : ℂ)) = 1 by
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
variable {K : Type} [Field K] [NumberField K] [S18.HADPkg K] {p : Nat.Primes}

abbrev gapsw80_t30_pSupp (K : Type) [Field K] [NumberField K] [S18.HADPkg K]
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
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section Regroup
variable {K : Type} [Field K] [NumberField K] [S18.HADPkg K] {p : Nat.Primes}

private noncomputable def gapsw80_t30_sigF (K : Type) [Field K] [NumberField K] [S18.HADPkg K]
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
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

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
  intro K _ _ _ s hs p

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

theorem gapsw80_t30_sat_D2d0b_unconditional :
    gapsw80_t28_DedekindZetaEulerProductHasProd :=
  gapsw80_t29_D2d0b_of_D2d0c gapsw80_t30_localEulerFactorPerNatPrime

theorem gapsw80_t30_sat_dedekindZeta_ne_zero (K : Type) [Field K]
    [NumberField K] [S18.HADPkg K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s ≠ 0 := fun h0 =>
  gapsw80_t28_falsif_D2d0b_loadbearing K hs h0
    gapsw80_t30_sat_D2d0b_unconditional

end FLT.Gapsw80T30D2d0cLocalEulerFactorProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T31D1HadamardSubDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T16XiRightHalfBoundProof
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T20LambdaLogDerivProductRule
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T30D2d0cLocalEulerFactorProof
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace Module P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Module Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"

section PerK

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t31_completedZeta_ne_zero_unconditional {s : ℂ}
    (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K s ≠ 0 := by
  have _em := Classical.em
  exact gapsw80_t20_completedZeta_ne_zero K hs
    (gapsw80_t30_sat_dedekindZeta_ne_zero K hs)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t31_polyLambda_ne_zero_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    s * (s - 1) * gapsw80_t9_completedDedekindZeta K s ≠ 0 := by
  have _em := Classical.em
  have hs0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs; exact absurd hs (by norm_num)
  exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
    (gapsw80_t31_completedZeta_ne_zero_unconditional K hs)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t31_polyLambda_ne_zero_of_re_lt_zero {s : ℂ}
    (hs : s.re < 0) :
    s * (s - 1) * gapsw80_t9_completedDedekindZeta K s ≠ 0 := by
  have _em := Classical.em
  have hs0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs; exact absurd hs (by norm_num)
  have hs' : 1 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith
  have hFE : gapsw80_t9_completedDedekindZeta K (1 - (1 - s))
      = gapsw80_t9_completedDedekindZeta K (1 - s) :=
    gapsw80_t9_FE_halfplane K hs'
  rw [sub_sub_cancel] at hFE
  refine mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) ?_
  rw [hFE]
  exact gapsw80_t31_completedZeta_ne_zero_unconditional K hs'

end PerK
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

def gapsw80_t31_XiZerosInOpenStrip : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
    ∀ s : ℂ, ξ s = 0 → 0 < s.re ∧ s.re < 1

def gapsw80_t31_HadamardLogDerivExpansion : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ∃ (B : ℂ) (ρ : ℕ → ℂ),
      (∀ j, ξ (ρ j) = 0) ∧
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) s
          = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t31_D1_of_D1ab
    (ha : gapsw80_t31_XiZerosInOpenStrip)
    (hb : gapsw80_t31_HadamardLogDerivExpansion) :
    gapsw80_t19_XiLogDerivZeroExpansion := by
  have _em := Classical.em
  intro K _ _ _
  obtain ⟨ξ, hdiff, hagr, hord⟩ := gapsw80_t16_B1_closed K
  obtain ⟨B, ρ, hzero, hsum, hexp⟩ := hb K ξ hdiff hagr hord
  exact ⟨B, ρ, fun j => ha K ξ hdiff hagr (ρ j) (hzero j), hsum, hexp⟩

end FLT.Gapsw80T31D1HadamardSubDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T32D1aBoundaryCaseDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T30D2d0cLocalEulerFactorProof
open FLT.Gapsw80T31D1HadamardSubDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"

section PerK

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t32_xi_ne_zero_of_one_lt_re (ξ : ℂ → ℂ)
    (hagr : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
    {s : ℂ} (hs : 1 < s.re) : ξ s ≠ 0 := by
  have _em := Classical.em
  have hs0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs; exact absurd hs (by norm_num)
  rw [hagr s hs0 hs1]
  exact gapsw80_t31_polyLambda_ne_zero_of_one_lt_re K hs

set_option maxHeartbeats 3200000 in

theorem gapsw80_t32_xi_ne_zero_of_re_lt_zero (ξ : ℂ → ℂ)
    (hagr : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
    {s : ℂ} (hs : s.re < 0) : ξ s ≠ 0 := by
  have _em := Classical.em
  have hs0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs; exact absurd hs (by norm_num)
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs; exact absurd hs (by norm_num)
  rw [hagr s hs0 hs1]
  exact gapsw80_t31_polyLambda_ne_zero_of_re_lt_zero K hs

end PerK
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

def gapsw80_t32_CompletedZetaReOneNonvanishing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ s : ℂ,
    s.re = 1 → s ≠ 1 → gapsw80_t9_completedDedekindZeta K s ≠ 0

def gapsw80_t32_XiEndpointNonvanishing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
    ξ 0 ≠ 0 ∧ ξ 1 ≠ 0

set_option maxHeartbeats 3200000 in

theorem gapsw80_t32_D1a_of_D1aSub
    (hD1a' : gapsw80_t32_CompletedZetaReOneNonvanishing)
    (hD1a'' : gapsw80_t32_XiEndpointNonvanishing) :
    gapsw80_t31_XiZerosInOpenStrip := by
  have _em := Classical.em
  intro K _ _ _ ξ hdiff hagr s hzero
  refine ⟨?_, ?_⟩
  ·
    rcases lt_trichotomy s.re 0 with h | h | h
    · exact absurd hzero (gapsw80_t32_xi_ne_zero_of_re_lt_zero K ξ hagr h)
    · rcases eq_or_ne s 0 with rfl | hs0
      · exact absurd hzero (hD1a'' K ξ hdiff hagr).1
      ·
        have hs1 : s ≠ 1 := fun heq => by
          rw [heq, Complex.one_re] at h; exact one_ne_zero h
        have hre1s : (1 - s).re = 1 := by
          rw [Complex.sub_re, Complex.one_re, h, sub_zero]
        have h1s1 : (1 : ℂ) - s ≠ 1 := fun heq => hs0 (sub_eq_self.mp heq)
        have hΛ : gapsw80_t9_completedDedekindZeta K s ≠ 0 := by
          rw [← gapsw80_t9_completedDedekindZeta_FE K hs0 hs1]
          exact hD1a' K (1 - s) hre1s h1s1
        refine absurd hzero ?_
        rw [hagr s hs0 hs1]
        exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hΛ
    · exact h
  ·
    rcases lt_trichotomy s.re 1 with h | h | h
    · exact h
    · rcases eq_or_ne s 1 with rfl | hs1
      · exact absurd hzero (hD1a'' K ξ hdiff hagr).2
      ·
        have hs0 : s ≠ 0 := fun heq => by
          rw [heq, Complex.zero_re] at h; exact zero_ne_one h
        refine absurd hzero ?_
        rw [hagr s hs0 hs1]
        exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
          (hD1a' K s h hs1)
    · exact absurd hzero (gapsw80_t32_xi_ne_zero_of_one_lt_re K ξ hagr h)

end FLT.Gapsw80T32D1aBoundaryCaseDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section
namespace FLT
namespace Gapsw80T36D1appXiEndpointResidueProof
open FLT.Gapsw80T32D1aBoundaryCaseDecomp FLT.Gapsw80T9ClassSumA1Closure

theorem gapsw80_t36_D1app_closed : gapsw80_t32_XiEndpointNonvanishing := by
  intro K _ _ _ ξ hξ hagr
  exact S18.HADPkg.End ξ hξ hagr
end FLT.Gapsw80T36D1appXiEndpointResidueProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T37D1bGenericHadamardDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T36D1appXiEndpointResidueProof
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t37_eventuallyEq_logDeriv_eq {F G : ℂ → ℂ} {s : ℂ}
    (h : F =ᶠ[𝓝 s] G) : logDeriv F s = logDeriv G s := by
  have _em := Classical.em
  unfold logDeriv
  rw [Pi.div_apply, Pi.div_apply, h.deriv_eq, h.eq_of_nhds]

section PerK

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t37_polyLambda_eventuallyEq_xi (ξ : ℂ → ℂ)
    (hagr : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (fun z => z * (z - 1) * gapsw80_t9_completedDedekindZeta K z) =ᶠ[𝓝 s] ξ := by
  have _em := Classical.em
  filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with z hz0 hz1
  exact (hagr z hz0 hz1).symm

set_option maxHeartbeats 3200000 in

theorem gapsw80_t37_xi_zero_ne_zero (ξ : ℂ → ℂ)
    (hdiff : Differentiable ℂ ξ)
    (hagr : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
    {z : ℂ} (hzero : ξ z = 0) : z ≠ 0 := by
  have _em := Classical.em
  exact fun h => (gapsw80_t36_D1app_closed K ξ hdiff hagr).1 (h ▸ hzero)

end PerK
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

def gapsw80_t37_XiHadamardProductForm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ∃ (A B : ℂ) (ρ : ℕ → ℂ),
      (∀ j, ξ (ρ j) = 0) ∧
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
      ∀ s : ℂ, ξ s = Complex.exp (A + B * s)
          * ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))

def gapsw80_t37_CanonicalProductLogDeriv : Prop :=
  ∀ (A B : ℂ) (ρ : ℕ → ℂ),
    (∀ j, ρ j ≠ 0) →
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    ∀ s : ℂ, (∀ j, s ≠ ρ j) →
      logDeriv (fun z => Complex.exp (A + B * z)
          * ∏' j, ((1 - z / ρ j) * Complex.exp (z / ρ j))) s
        = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t37_D1b_of_D1b0_D1b1
    (hD1b0 : gapsw80_t37_XiHadamardProductForm)
    (hD1b1 : gapsw80_t37_CanonicalProductLogDeriv) :
    gapsw80_t31_HadamardLogDerivExpansion := by
  have _em := Classical.em
  intro K _ _ _ ξ hdiff hagr hord
  obtain ⟨A, B, ρ, hzero, hsum, hprod⟩ := hD1b0 K ξ hdiff hagr hord
  have hρ0 : ∀ j, ρ j ≠ 0 :=
    fun j => gapsw80_t37_xi_zero_ne_zero K ξ hdiff hagr (hzero j)
  refine ⟨B, ρ, hzero, hsum, fun s hs0 hs1 hsρ => ?_⟩
  have hξ : ξ = (fun z => Complex.exp (A + B * z)
      * ∏' j, ((1 - z / ρ j) * Complex.exp (z / ρ j))) := funext hprod
  rw [gapsw80_t37_eventuallyEq_logDeriv_eq
        (gapsw80_t37_polyLambda_eventuallyEq_xi K ξ hagr hs0 hs1), hξ]
  exact hD1b1 A B ρ hρ0 hsum s hsρ

end FLT.Gapsw80T37D1bGenericHadamardDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T33D1apZetaExtQuotientDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T20LambdaLogDerivProductRule
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"

section PerK

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t33_Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
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

theorem gapsw80_t33_archFactor_ne_zero {s : ℂ} (hs : 0 < s.re) :
    (((|discr K| : ℤ) : ℂ)) ^ (s / 2) * gapsw80_t9_gammaFactor K s ≠ 0 := by
  have _em := Classical.em
  have hD := gapsw80_t20_discrBase_ne_zero K
  have hDne : (((|discr K| : ℤ) : ℂ)) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hD]; exact Complex.exp_ne_zero _
  exact mul_ne_zero hDne (mul_ne_zero
    (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs))
    (pow_ne_zero _ (gapsw80_t33_Gammaℂ_ne_zero_of_re_pos hs)))

noncomputable def gapsw80_t33_dedekindZetaExt (s : ℂ) : ℂ :=
  gapsw80_t9_completedDedekindZeta K s /
    ((((|discr K| : ℤ) : ℂ)) ^ (s / 2) * gapsw80_t9_gammaFactor K s)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t33_dedekindZetaExt_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t33_dedekindZetaExt K s = dedekindZeta K s := by
  have _em := Classical.em
  have hD := gapsw80_t20_discrBase_ne_zero K
  have hDne : (((|discr K| : ℤ) : ℂ)) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hD]; exact Complex.exp_ne_zero _
  have hR : Gammaℝ s ^ nrRealPlaces K ≠ 0 :=
    pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos (by linarith))
  have hC : Gammaℂ s ^ nrComplexPlaces K ≠ 0 :=
    pow_ne_zero _ (gapsw80_t33_Gammaℂ_ne_zero_of_re_pos (by linarith))
  unfold gapsw80_t33_dedekindZetaExt
  rw [gapsw80_t10_completedDedekindZeta_eq_T1 K hs, gapsw80_t1_completedDedekindZeta,
    gapsw80_t9_gammaFactor]
  field_simp

set_option maxHeartbeats 3200000 in

theorem gapsw80_t33_differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
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

theorem gapsw80_t33_differentiableAt_Gammaℂ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
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

theorem gapsw80_t33_differentiableOn_dedekindZetaExt :
    DifferentiableOn ℂ (gapsw80_t33_dedekindZetaExt K)
      ({z : ℂ | 0 < z.re} \ {1}) := by
  have _em := Classical.em
  have hsub : ({z : ℂ | 0 < z.re} \ {1}) ⊆ ({(0:ℂ), 1}ᶜ : Set ℂ) := by
    rintro z ⟨hre, hn1⟩
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or]
    refine ⟨?_, hn1⟩
    rintro rfl
    simp at hre
  have hnum : DifferentiableOn ℂ (gapsw80_t9_completedDedekindZeta K)
      ({z : ℂ | 0 < z.re} \ {1}) :=
    (gapsw80_t9_differentiableOn_completedDedekindZeta K).mono hsub
  have hden : DifferentiableOn ℂ
      (fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2) * gapsw80_t9_gammaFactor K z)
      ({z : ℂ | 0 < z.re} \ {1}) := by
    intro z ⟨hre, _⟩
    refine (DifferentiableAt.mul ?_ ?_).differentiableWithinAt
    · exact ((hasDerivAt_id z).div_const 2).differentiableAt.const_cpow
        (Or.inl (gapsw80_t20_discrBase_ne_zero K))
    · exact ((gapsw80_t33_differentiableAt_Gammaℝ_of_re_pos hre).pow _).mul
        ((gapsw80_t33_differentiableAt_Gammaℂ_of_re_pos hre).pow _)
  exact hnum.div hden (fun z ⟨hre, _⟩ => gapsw80_t33_archFactor_ne_zero K hre)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t33_completedZeta_eq_archFactor_mul_ext {s : ℂ}
    (hs : 0 < s.re) :
    gapsw80_t9_completedDedekindZeta K s =
      ((((|discr K| : ℤ) : ℂ)) ^ (s / 2) * gapsw80_t9_gammaFactor K s)
        * gapsw80_t33_dedekindZetaExt K s := by
  have _em := Classical.em
  exact (mul_div_cancel₀ _ (gapsw80_t33_archFactor_ne_zero K hs)).symm

end PerK
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

def gapsw80_t33_DedekindZetaExtReOneNonvanishing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ s : ℂ,
    s.re = 1 → s ≠ 1 → gapsw80_t33_dedekindZetaExt K s ≠ 0

set_option maxHeartbeats 3200000 in

theorem gapsw80_t33_D1ap_of_D1apa
    (hD1apa : gapsw80_t33_DedekindZetaExtReOneNonvanishing) :
    gapsw80_t32_CompletedZetaReOneNonvanishing := by
  have _em := Classical.em
  intro K _ _ _ s hre hs1
  have h0 : (0:ℝ) < s.re := hre ▸ one_pos
  rw [gapsw80_t33_completedZeta_eq_archFactor_mul_ext K h0]
  exact mul_ne_zero (gapsw80_t33_archFactor_ne_zero K h0) (hD1apa K s hre hs1)

end FLT.Gapsw80T33D1apZetaExtQuotientDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T38D1b1CanonicalProductLogDerivProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T37D1bGenericHadamardDecomp
p2m_open "Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t38_logDeriv_E1_factor {ρ s : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    logDeriv (fun z => (1 - z / ρ) * Complex.exp (z / ρ)) s
      = (s - ρ)⁻¹ + ρ⁻¹ := by
  have _em := Classical.em
  have h1 : (1 : ℂ) - s / ρ ≠ 0 :=
    sub_ne_zero.mpr fun h => hs ((div_eq_one_iff_eq hρ).mp h.symm)
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have hρs : ρ - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hmul := logDeriv_mul (f := fun w => 1 - w / ρ)
    (g := fun w => Complex.exp (w / ρ)) s h1 (Complex.exp_ne_zero _)
    (by fun_prop) (by fun_prop)
  rw [hmul]
  have hlin : logDeriv (fun w => (1 : ℂ) - w / ρ) s = (s - ρ)⁻¹ := by
    rw [logDeriv_apply]
    simp only [deriv_const_sub, deriv_div_const, deriv_id'']
    field_simp
    ring
  have hexp : logDeriv (fun w => Complex.exp (w / ρ)) s = ρ⁻¹ := by
    rw [show (fun w => Complex.exp (w / ρ)) = Complex.exp ∘ (· / ρ) from rfl,
      logDeriv_comp Complex.differentiableAt_exp (by fun_prop), Complex.logDeriv_exp,
      Pi.one_apply, one_mul, deriv_div_const, deriv_id'', one_div]
  rw [hlin, hexp]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t38_logDeriv_exp_affine {A B s : ℂ} :
    logDeriv (fun z => Complex.exp (A + B * z)) s = B := by
  have _em := Classical.em
  rw [show (fun z => Complex.exp (A + B * z)) = Complex.exp ∘ (fun z => A + B * z)
        from rfl,
    logDeriv_comp Complex.differentiableAt_exp (by fun_prop), Complex.logDeriv_exp,
    Pi.one_apply, one_mul]
  simp [deriv_const_mul_field]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t38_norm_E1_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 - w) * Complex.exp w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have _em := Classical.em
  have key : (1 - w) * Complex.exp w - 1
      = (Complex.exp w - 1 - w) - w * (Complex.exp w - 1) := by ring
  rw [key]
  calc ‖(Complex.exp w - 1 - w) - w * (Complex.exp w - 1)‖
      ≤ ‖Complex.exp w - 1 - w‖ + ‖w * (Complex.exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by
        gcongr
        · exact Complex.norm_exp_sub_one_sub_id_le hw
        · rw [norm_mul]; gcongr; exact Complex.norm_exp_sub_one_le hw
    _ = 3 * ‖w‖ ^ 2 := by ring

set_option maxHeartbeats 3200000 in

theorem gapsw80_t38_eventually_large_norm {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ j in atTop, R ≤ ‖ρ j‖ := by
  have _em := Classical.em
  have h0 := hsum.tendsto_atTop_zero
  simp_rw [Complex.normSq_eq_norm_sq] at h0
  have hR2 : (0 : ℝ) < (R ^ 2)⁻¹ := by positivity
  filter_upwards [h0.eventually_lt_const hR2] with j hj
  have hnj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsq : R ^ 2 ≤ ‖ρ j‖ ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact le_of_lt (by simpa using hj)
  nlinarith [sq_nonneg (R - ‖ρ j‖), sq_nonneg (R + ‖ρ j‖)]

set_option maxHeartbeats 9600000 in

theorem gapsw80_t38_D1b1_closed : gapsw80_t37_CanonicalProductLogDeriv := by
  have _em := Classical.em
  intro A B ρ hρ0 hsum s hsρ

  set F : ℕ → ℂ → ℂ := fun j z => (1 - z / ρ j) * Complex.exp (z / ρ j) with hF
  set R : ℝ := ‖s‖ + 1 with hR
  have hR0 : (0 : ℝ) < R := by positivity
  have hsK : s ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr (by rw [hR]; linarith [norm_nonneg s])

  have hFne : ∀ j, F j s ≠ 0 := fun j =>
    mul_ne_zero
      (sub_ne_zero.mpr fun h => hsρ j ((div_eq_one_iff_eq (hρ0 j)).mp h.symm))
      (Complex.exp_ne_zero _)

  have hlarge : ∀ᶠ j in atTop, 2 * R ≤ ‖ρ j‖ :=
    gapsw80_t38_eventually_large_norm hρ0 hsum (by positivity)

  have hbound : ∀ᶠ j in atTop, ∀ z ∈ ball (0 : ℂ) R,
      ‖F j z - 1‖ ≤ 3 * R ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
    filter_upwards [hlarge] with j hj z hz
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
    have hρj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
    have hzρ : ‖z / ρ j‖ ≤ 1 := by
      rw [norm_div, div_le_one hρj]; linarith
    have hnn : (0 : ℝ) ≤ (Complex.normSq (ρ j))⁻¹ :=
      inv_nonneg.mpr (Complex.normSq_nonneg _)
    calc ‖F j z - 1‖ = ‖(1 - z / ρ j) * Complex.exp (z / ρ j) - 1‖ := by rw [hF]
      _ ≤ 3 * ‖z / ρ j‖ ^ 2 := gapsw80_t38_norm_E1_sub_one_le hzρ
      _ = 3 * ‖z‖ ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
          rw [norm_div, div_pow, Complex.normSq_eq_norm_sq]; ring
      _ ≤ 3 * R ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
          have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
          nlinarith
  have husum : Summable fun j => 3 * R ^ 2 * (Complex.normSq (ρ j))⁻¹ :=
    hsum.mul_left _

  have hMLU : MultipliableLocallyUniformlyOn F (ball (0 : ℂ) R) := by
    have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add
      (f := fun j z => F j z - 1) isOpen_ball husum hbound
      (fun j => by simp only [hF]; fun_prop)
    simp only [add_sub_cancel] at hprod
    exact hprod.multipliableLocallyUniformlyOn

  have hSnorm : Summable fun j => ‖F j s - 1‖ := by
    refine husum.of_norm_bounded_eventually ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hbound] with j hj
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hj s hsK

  have hprod_ne : ∏' j, F j s ≠ 0 := by
    have h := tprod_one_add_ne_zero_of_summable (f := fun j => F j s - 1)
      (fun j => by simpa using hFne j) hSnorm
    simpa using h

  have hterm_eq : ∀ j, logDeriv (F j) s = (s - ρ j)⁻¹ + (ρ j)⁻¹ := fun j => by
    simp only [hF]; exact gapsw80_t38_logDeriv_E1_factor (hρ0 j) (hsρ j)
  have hSlog : Summable fun j => logDeriv (F j) s := by
    simp_rw [hterm_eq]
    refine (hsum.mul_left (2 * ‖s‖)).of_norm_bounded_eventually ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hlarge] with j hj
    have hρj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
    have hsub : ‖ρ j‖ / 2 ≤ ‖s - ρ j‖ := by
      have h1 : ‖ρ j‖ - ‖s‖ ≤ ‖s - ρ j‖ := by
        rw [norm_sub_rev]; exact norm_sub_norm_le _ _
      nlinarith
    have hsubpos : 0 < ‖s - ρ j‖ := lt_of_lt_of_le (by positivity) hsub
    have hsρj : s - ρ j ≠ 0 := sub_ne_zero.mpr (hsρ j)
    have hρj0 : ρ j ≠ 0 := hρ0 j
    have heq : (s - ρ j)⁻¹ + (ρ j)⁻¹ = s * ((s - ρ j) * ρ j)⁻¹ := by
      field_simp; ring
    rw [heq, norm_mul, norm_inv, norm_mul, Complex.normSq_eq_norm_sq]
    have hρjne : ‖ρ j‖ ≠ 0 := ne_of_gt hρj
    calc ‖s‖ * (‖s - ρ j‖ * ‖ρ j‖)⁻¹
        ≤ ‖s‖ * (‖ρ j‖ / 2 * ‖ρ j‖)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          exact mul_le_mul_of_nonneg_right hsub hρj.le
        _ = 2 * ‖s‖ * (‖ρ j‖ ^ 2)⁻¹ := by field_simp

  have hdiff_prod : DifferentiableAt ℂ (fun z => ∏' j, F j z) s := by
    have h1 : TendstoLocallyUniformlyOn (fun (t : Finset ℕ) z => ∏ j ∈ t, F j z)
        (fun z => ∏' j, F j z) atTop (ball (0 : ℂ) R) :=
      hMLU.hasProdLocallyUniformlyOn
    exact (h1.differentiableOn
        (Filter.Eventually.of_forall fun t => by simp only [hF]; fun_prop)
        isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hsK)

  have hmul := logDeriv_mul (f := fun w => Complex.exp (A + B * w))
    (g := fun w => ∏' j, F j w) s (Complex.exp_ne_zero _) hprod_ne
    (by fun_prop) hdiff_prod
  show logDeriv (fun z => Complex.exp (A + B * z) * ∏' j, F j z) s
    = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹)
  rw [hmul, gapsw80_t38_logDeriv_exp_affine,
    logDeriv_tprod_eq_tsum isOpen_ball hsK hFne
      (fun j => by simp only [hF]; fun_prop) hSlog hMLU hprod_ne,
    tsum_congr hterm_eq]

end FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T39D1b0HadamardQuotientDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

def gapsw80_t39_XiCanonicalQuotient : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ∃ (ρ : ℕ → ℂ) (g : ℂ → ℂ),
      (∀ j, ξ (ρ j) = 0) ∧
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
      Differentiable ℂ g ∧
      (∀ s : ℂ, g s ≠ 0) ∧
      (∀ s : ℂ, ξ s = g s
          * ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) ∧
      (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
        Real.log ‖g s‖ ≤ C * ‖s‖ * Real.log ‖s‖)

def gapsw80_t39_ZeroFreeOrderOneExpForm : Prop :=
  ∀ g : ℂ → ℂ,
    Differentiable ℂ g →
    (∀ s : ℂ, g s ≠ 0) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖g s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ∃ A B : ℂ, ∀ s : ℂ, g s = Complex.exp (A + B * s)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t39_D1b0_of_D1b0a_D1b0b
    (hA : gapsw80_t39_XiCanonicalQuotient)
    (hB : gapsw80_t39_ZeroFreeOrderOneExpForm) :
    gapsw80_t37_XiHadamardProductForm := by
  have _em := Classical.em
  intro K _ _ _ ξ hdiff hagr hord
  obtain ⟨ρ, g, hzero, hsum, hgdiff, hgne, hfact, hgord⟩ :=
    hA K ξ hdiff hagr hord
  obtain ⟨A, B, hgexp⟩ := hB g hgdiff hgne hgord
  exact ⟨A, B, ρ, hzero, hsum, fun s => by rw [hfact s, hgexp s]⟩

end FLT.Gapsw80T39D1b0HadamardQuotientDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T34D1apaThreeFourOneIneqDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T16XiRightHalfBoundProof
open FLT.Gapsw80T20LambdaLogDerivProductRule
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T33D1apZetaExtQuotientDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

theorem gapsw80_t34_isOpen_rePosDiffOne :
    IsOpen ({z : ℂ | 0 < z.re} \ {1}) :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton

section PerK

variable (K : Type) [Field K] [NumberField K] [S18.HADPkg K]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t34_differentiableAt_archFactor {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun z => (((|discr K| : ℤ) : ℂ)) ^ (z / 2) * gapsw80_t9_gammaFactor K z)
      s := by
  have _em := Classical.em
  refine DifferentiableAt.mul ?_ ?_
  · exact ((hasDerivAt_id s).div_const 2).differentiableAt.const_cpow
      (Or.inl (gapsw80_t20_discrBase_ne_zero K))
  · exact ((gapsw80_t33_differentiableAt_Gammaℝ_of_re_pos hs).pow _).mul
      ((gapsw80_t33_differentiableAt_Gammaℂ_of_re_pos hs).pow _)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t34_sub_one_mul_zetaExt_eq (ξ : ℂ → ℂ)
    (hagr : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
    {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1) :
    (s - 1) * gapsw80_t33_dedekindZetaExt K s =
      ξ s / (s * ((((|discr K| : ℤ) : ℂ)) ^ (s / 2)
        * gapsw80_t9_gammaFactor K s)) := by
  have _em := Classical.em
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl 0 hre
  have harch := gapsw80_t33_archFactor_ne_zero K hre
  have key : ξ s = s * ((((|discr K| : ℤ) : ℂ)) ^ (s / 2)
      * gapsw80_t9_gammaFactor K s) * ((s - 1) * gapsw80_t33_dedekindZetaExt K s) := by
    rw [hagr s hs0 hs1, gapsw80_t33_completedZeta_eq_archFactor_mul_ext K hre]; ring
  rw [key, mul_div_cancel_left₀ _ (mul_ne_zero hs0 harch)]

end PerK
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t34_tendsto_ofReal_add_constI (c : ℝ) :
    Tendsto (fun σ : ℝ ↦ (↑σ : ℂ) + c * I) (𝓝[>] (1:ℝ))
      (𝓝[≠] ((1:ℂ) + c * I)) := by
  have _em := Classical.em
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_nhdsWithin_of_tendsto_nhds
    ((Complex.continuous_ofReal.tendsto 1).add tendsto_const_nhds), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with σ hσ h
  exact absurd (Complex.ofReal_inj.mp (add_right_cancel h)) (ne_of_gt hσ)

def gapsw80_t34_DedekindZetaThreeFourOneIneq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ t : ℝ, t ≠ 0 → ∀ σ : ℝ, 1 < σ →
    1 ≤ ‖dedekindZeta K (↑σ : ℂ)‖ ^ 3 * ‖dedekindZeta K (↑σ + t * I)‖ ^ 4
      * ‖dedekindZeta K (↑σ + 2 * t * I)‖

set_option maxHeartbeats 8000000 in

theorem gapsw80_t34_D1apa_of_D1apa0
    (h341 : gapsw80_t34_DedekindZetaThreeFourOneIneq) :
    gapsw80_t33_DedekindZetaExtReOneNonvanishing := by
  have _em := Classical.em
  intro K _ _ _ s hre hs1 hext0

  obtain ⟨ξ, hdiff, hagr, _⟩ := gapsw80_t16_B1_closed K

  set t := s.im with ht_def
  have hst : s = 1 + t * I := by
    rw [Complex.ext_iff]; constructor <;> simp [hre, ht_def]
  have ht : t ≠ 0 := fun h0 => hs1 (by rw [hst, h0]; simp)
  haveI hNB : (𝓝[>] (1:ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl

  have hmem_s : s ∈ ({z : ℂ | 0 < z.re} \ {1}) :=
    ⟨by show (0:ℝ) < s.re; rw [hre]; exact one_pos, hs1⟩
  have h2t : (2:ℝ) * t ≠ 0 := mul_ne_zero two_ne_zero ht
  have hmem_2t : ((1:ℂ) + 2*t*I) ∈ ({z : ℂ | 0 < z.re} \ {1}) := by
    refine ⟨by simp, fun h => h2t ?_⟩
    have himeq := congrArg Complex.im h
    simpa using himeq

  have hnorm : ∀ σ : ℝ, 1 < σ → ‖((↑σ : ℂ) - 1)‖ = σ - 1 := fun σ hσ => by
    rw [show ((↑σ:ℂ)-1) = ↑(σ-1) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]

  have hA : Tendsto (fun σ : ℝ ↦ (σ - 1) * ‖gapsw80_t33_dedekindZetaExt K ↑σ‖)
      (𝓝[>] (1:ℝ)) (𝓝 ‖ξ 1 / ((1:ℂ) * ((((|discr K| : ℤ) : ℂ)) ^ ((1:ℂ) / 2)
        * gapsw80_t9_gammaFactor K 1))‖) := by

    have hden1 : ((1:ℂ) * ((((|discr K| : ℤ) : ℂ)) ^ ((1:ℂ) / 2)
        * gapsw80_t9_gammaFactor K 1)) ≠ 0 :=
      mul_ne_zero one_ne_zero (gapsw80_t33_archFactor_ne_zero K (by simp))
    have hg : ContinuousAt
        (fun z : ℂ ↦ ξ z / (z * ((((|discr K| : ℤ) : ℂ)) ^ (z / 2)
          * gapsw80_t9_gammaFactor K z))) 1 :=
      hdiff.continuous.continuousAt.div
        (continuousAt_id.mul (gapsw80_t34_differentiableAt_archFactor K
          (by simp)).continuousAt) hden1
    refine (tendsto_nhdsWithin_of_tendsto_nhds
      (hg.tendsto.comp (Complex.continuous_ofReal.tendsto 1))).norm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1:ℝ) < σ := hσ
    have hreσ0 : 0 < ((↑σ:ℂ)).re := by simp; linarith
    have hσne1 : ((↑σ:ℂ)) ≠ 1 := by exact_mod_cast hσ1.ne'
    rw [Function.comp_apply,
      ← gapsw80_t34_sub_one_mul_zetaExt_eq K ξ hagr hreσ0 hσne1, norm_mul,
      hnorm σ hσ1]

  have hB : Tendsto (fun σ : ℝ ↦ ‖gapsw80_t33_dedekindZetaExt K (↑σ + t * I)‖
        / (σ - 1)) (𝓝[>] (1:ℝ))
      (𝓝 ‖deriv (gapsw80_t33_dedekindZetaExt K) s‖) := by
    have hdA : DifferentiableAt ℂ (gapsw80_t33_dedekindZetaExt K) s :=
      (gapsw80_t33_differentiableOn_dedekindZetaExt K).differentiableAt
        (gapsw80_t34_isOpen_rePosDiffOne.mem_nhds hmem_s)
    have hslope := (hasDerivAt_iff_tendsto_slope.mp hdA.hasDerivAt).comp
      (hst ▸ gapsw80_t34_tendsto_ofReal_add_constI t)
    refine hslope.norm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1:ℝ) < σ := hσ
    rw [Function.comp_apply, slope_def_field, hext0, sub_zero,
      show ((↑σ:ℂ) + t*I) - s = ↑σ - 1 by rw [hst]; ring, norm_div, hnorm σ hσ1]

  have hC : Tendsto (fun σ : ℝ ↦ ‖gapsw80_t33_dedekindZetaExt K (↑σ + 2*t*I)‖)
      (𝓝[>] (1:ℝ)) (𝓝 ‖gapsw80_t33_dedekindZetaExt K (1 + 2*t*I)‖) := by
    have hcA : ContinuousAt (gapsw80_t33_dedekindZetaExt K) ((1:ℂ) + 2*t*I) :=
      (gapsw80_t33_differentiableOn_dedekindZetaExt K).continuousOn.continuousAt
        (gapsw80_t34_isOpen_rePosDiffOne.mem_nhds hmem_2t)
    have hmap : Tendsto (fun σ : ℝ ↦ (↑σ:ℂ) + 2*t*I) (𝓝[>] (1:ℝ))
        (𝓝 ((1:ℂ) + 2*t*I)) :=
      tendsto_nhdsWithin_of_tendsto_nhds
        ((Complex.continuous_ofReal.tendsto 1).add tendsto_const_nhds)
    exact (hcA.tendsto.comp hmap).norm

  have hsub : Tendsto (fun σ : ℝ ↦ σ - 1) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have h := (continuous_sub_right (1:ℝ)).tendsto (1:ℝ)
    simpa using h
  have hD : Tendsto (fun σ : ℝ ↦
      ((σ - 1) * ‖gapsw80_t33_dedekindZetaExt K ↑σ‖) ^ 3
        * (‖gapsw80_t33_dedekindZetaExt K (↑σ + t*I)‖ / (σ - 1)) ^ 4
        * ‖gapsw80_t33_dedekindZetaExt K (↑σ + 2*t*I)‖
        * (σ - 1)) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    have := ((hA.pow 3).mul (hB.pow 4)).mul hC |>.mul hsub
    simpa using this

  have hE : ∀ᶠ (σ : ℝ) in 𝓝[>] (1:ℝ),
      ((σ - 1) * ‖gapsw80_t33_dedekindZetaExt K ↑σ‖) ^ 3
        * (‖gapsw80_t33_dedekindZetaExt K (↑σ + t*I)‖ / (σ - 1)) ^ 4
        * ‖gapsw80_t33_dedekindZetaExt K (↑σ + 2*t*I)‖ * (σ - 1)
      = ‖dedekindZeta K (↑σ : ℂ)‖ ^ 3 * ‖dedekindZeta K (↑σ + t*I)‖ ^ 4
        * ‖dedekindZeta K (↑σ + 2*t*I)‖ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1:ℝ) < σ := hσ
    have hne : σ - 1 ≠ 0 := (sub_pos.mpr hσ1).ne'
    rw [← gapsw80_t33_dedekindZetaExt_eq_dedekindZeta K
          (show 1 < ((↑σ:ℂ)).re by simpa using hσ1),
      ← gapsw80_t33_dedekindZetaExt_eq_dedekindZeta K
          (show 1 < ((↑σ:ℂ) + t*I).re by simp; exact hσ1),
      ← gapsw80_t33_dedekindZetaExt_eq_dedekindZeta K
          (show 1 < ((↑σ:ℂ) + 2*t*I).re by simp; exact hσ1)]
    field_simp

  have hP : Tendsto (fun σ : ℝ ↦
      ‖dedekindZeta K (↑σ : ℂ)‖ ^ 3 * ‖dedekindZeta K (↑σ + t*I)‖ ^ 4
        * ‖dedekindZeta K (↑σ + 2*t*I)‖) (𝓝[>] (1:ℝ)) (𝓝 0) := hD.congr' hE
  have hge1 : ∀ᶠ (σ : ℝ) in 𝓝[>] (1:ℝ), (1:ℝ) ≤
      ‖dedekindZeta K (↑σ : ℂ)‖ ^ 3 * ‖dedekindZeta K (↑σ + t*I)‖ ^ 4
        * ‖dedekindZeta K (↑σ + 2*t*I)‖ :=
    eventually_nhdsWithin_of_forall (fun σ hσ => h341 K t ht σ hσ)
  have hlt1 : ∀ᶠ (σ : ℝ) in 𝓝[>] (1:ℝ),
      ‖dedekindZeta K (↑σ : ℂ)‖ ^ 3 * ‖dedekindZeta K (↑σ + t*I)‖ ^ 4
        * ‖dedekindZeta K (↑σ + 2*t*I)‖ < 1 :=
    hP.eventually_lt tendsto_const_nhds zero_lt_one
  obtain ⟨σ, h1σ, hltσ⟩ := (hge1.and hlt1).exists
  exact absurd hltσ (not_lt.mpr h1σ)

end FLT.Gapsw80T34D1apaThreeFourOneIneqDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T40D1b0bZeroFreeExpLinearProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
p2m_open "Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t40_logDeriv_primitive {g : ℂ → ℂ} (hgdiff : Differentiable ℂ g)
    (hgne : ∀ s, g s ≠ 0) :
    ∃ h : ℂ → ℂ, h 0 = 0 ∧ ∀ s, HasDerivAt h (deriv g s / g s) s := by
  have _em := Classical.em
  have hdg : Differentiable ℂ (deriv g) :=
    differentiableOn_univ.mp (hgdiff.differentiableOn.deriv isOpen_univ)
  have hgg' : Differentiable ℂ (fun s => deriv g s / g s) := hdg.div hgdiff hgne
  obtain ⟨h, hh0, hhd⟩ := hgg'.isExactOn_univ.with_val_at 0 0
  exact ⟨h, hh0, fun s => hhd s (mem_univ s)⟩

set_option maxHeartbeats 3200000 in

theorem gapsw80_t40_eq_const_mul_exp {g h : ℂ → ℂ} (hgdiff : Differentiable ℂ g)
    (hgne : ∀ s, g s ≠ 0) (hh0 : h 0 = 0)
    (hhd : ∀ s, HasDerivAt h (deriv g s / g s) s) :
    ∀ s, g s = g 0 * Complex.exp (h s) := by
  have _em := Classical.em
  set φ := fun s => g s * Complex.exp (-h s) with hφdef
  have hφ' : ∀ s, HasDerivAt φ 0 s := by
    intro s
    have h1 : HasDerivAt g (deriv g s) s := hgdiff.differentiableAt.hasDerivAt
    have h3 : HasDerivAt (fun z => Complex.exp (-h z))
        (Complex.exp (-h s) * (-(deriv g s / g s))) s := ((hhd s).neg).cexp
    have h4 := h1.mul h3
    have key : deriv g s * Complex.exp (-h s) +
        g s * (Complex.exp (-h s) * (-(deriv g s / g s))) = 0 := by
      field_simp [hgne s]; ring
    exact key ▸ h4
  have hφdiff : Differentiable ℂ φ := fun s => (hφ' s).differentiableAt
  have hφc : ∀ s, φ s = φ 0 := fun s =>
    is_const_of_deriv_eq_zero hφdiff (fun z => (hφ' z).deriv) s 0
  intro s
  have hφ0 : φ 0 = g 0 := by simp [hφdef, hh0]
  have hφs : g s * Complex.exp (-h s) = g 0 := (hφc s).trans hφ0
  have hexp_ne : Complex.exp (-h s) ≠ 0 := Complex.exp_ne_zero _
  calc g s = g s * Complex.exp (-h s) * Complex.exp (h s) := by
        rw [mul_assoc, ← Complex.exp_add, _root_.neg_add_cancel, Complex.exp_zero,
          mul_one]
    _ = g 0 * Complex.exp (h s) := by rw [hφs]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t40_linear_of_iteratedDeriv_two_eq_zero {h : ℂ → ℂ}
    (hhdiff : Differentiable ℂ h) (hh2 : ∀ c, iteratedDeriv 2 h c = 0) :
    ∀ s, h s = h 0 + deriv h 0 * s := by
  have _em := Classical.em
  have hdh : Differentiable ℂ (deriv h) :=
    differentiableOn_univ.mp (hhdiff.differentiableOn.deriv isOpen_univ)
  have hdd0 : ∀ c, deriv (deriv h) c = 0 := by
    intro c
    have : iteratedDeriv 2 h = deriv (deriv h) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [← this]; exact hh2 c
  have hB : ∀ s, deriv h s = deriv h 0 :=
    fun s => is_const_of_deriv_eq_zero hdh hdd0 s 0
  set B := deriv h 0
  have hψ' : ∀ s, HasDerivAt (fun z => h z - B * z) 0 s := by
    intro s
    have h1 : HasDerivAt h (deriv h s) s := hhdiff.differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun z => B * z) B s := by
      simpa using (hasDerivAt_id s).const_mul B
    have h3 := h1.sub h2
    rw [hB s, sub_self] at h3
    exact h3
  have hψdiff : Differentiable ℂ (fun z => h z - B * z) :=
    fun s => (hψ' s).differentiableAt
  intro s
  have hψc := is_const_of_deriv_eq_zero hψdiff (fun z => (hψ' z).deriv) s 0
  simp only [mul_zero, sub_zero] at hψc
  linear_combination hψc

set_option maxHeartbeats 9600000 in

theorem gapsw80_t40_iteratedDeriv_two_eq_zero_of_re_growth {h : ℂ → ℂ}
    (hhdiff : Differentiable ℂ h) (hh0 : h 0 = 0)
    (hord : ∃ C D : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      (h s).re ≤ C * ‖s‖ * Real.log ‖s‖ + D) :
    ∀ c, iteratedDeriv 2 h c = 0 := by
  have _em := Classical.em
  obtain ⟨C, D, hord'⟩ := hord
  set C₁ := max C 0 with hC₁def
  have hC₁nn : 0 ≤ C₁ := le_max_right _ _
  have hC₁C : C ≤ C₁ := le_max_left _ _

  obtain ⟨x₀, _, hx₀⟩ := (isCompact_closedBall (0:ℂ) 2).exists_isMaxOn
    ⟨0, by simp⟩ (continuous_re.comp hhdiff.continuous).continuousOn
  set C₀ := (h x₀).re
  set D₂ := |C₀| + |D| + 1 with hD₂def
  have hD₂pos : 0 < D₂ := by positivity
  set M : ℝ → ℝ := fun R => C₁ * R * Real.log R + D₂ with hMdef

  have hMapsTo : ∀ R : ℝ, 3 ≤ R → ∀ z ∈ ball (0:ℂ) R, (h z).re ≤ M R := by
    intro R hR z hz
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
    rcases le_or_gt ‖z‖ 2 with hle | hgt
    · have : (h z).re ≤ C₀ := hx₀ (mem_closedBall_zero_iff.mpr hle)
      calc (h z).re ≤ C₀ := this
        _ ≤ |C₀| := le_abs_self _
        _ ≤ D₂ := by simp only [hD₂def]; linarith [abs_nonneg D]
        _ ≤ M R := by
            simp only [hMdef]
            have hlog : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
            nlinarith [mul_nonneg (mul_nonneg hC₁nn
              (by linarith : (0:ℝ) ≤ R)) hlog]
    · have h2z : (2:ℝ) ≤ ‖z‖ := le_of_lt hgt
      have hlogz : 0 < Real.log ‖z‖ := Real.log_pos (by linarith)
      have hzl : (0:ℝ) ≤ ‖z‖ * Real.log ‖z‖ :=
        mul_nonneg (by linarith) hlogz.le
      have hzlogz : ‖z‖ * Real.log ‖z‖ ≤ R * Real.log R := by
        apply mul_le_mul hzR.le
          (Real.log_le_log (by linarith) hzR.le)
          hlogz.le (by linarith)
      calc (h z).re ≤ C * ‖z‖ * Real.log ‖z‖ + D := hord' z h2z
        _ ≤ M R := by
            simp only [hMdef]
            nlinarith [mul_nonneg (sub_nonneg.mpr hC₁C) hzl,
              mul_nonneg hC₁nn (sub_nonneg.mpr hzlogz),
              le_abs_self D, abs_nonneg C₀]
  have hMpos : ∀ R : ℝ, 3 ≤ R → 0 < M R := by
    intro R hR
    simp only [hMdef]
    have hlog : 0 < Real.log R := Real.log_pos (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hC₁nn
      (by linarith : (0:ℝ) ≤ R)) hlog.le]

  have hBC : ∀ R : ℝ, 3 ≤ R → ∀ z ∈ ball (0:ℂ) R,
      ‖h z‖ ≤ 2 * M R * ‖z‖ / (R - ‖z‖) := by
    intro R hR z hz
    exact borelCaratheodory_zero (hMpos R hR) hhdiff.differentiableOn
      (fun w hw => hMapsTo R hR w hw) (by linarith) hz hh0

  have hsphere : ∀ c : ℂ, ∀ r : ℝ, 2 ≤ r → ∀ z ∈ sphere c r,
      ‖h z‖ ≤ 2 * M (2 * (‖c‖ + r)) := by
    intro c r hr z hz
    set R := 2 * (‖c‖ + r) with hRdef
    have hRge : (3:ℝ) ≤ R := by
      simp only [hRdef]; nlinarith [norm_nonneg c]
    have hMRpos : 0 < M R := hMpos R hRge
    have hzle : ‖z‖ ≤ ‖c‖ + r := by
      have hzc := mem_sphere_iff_norm.mp hz
      calc ‖z‖ = ‖z - c + c‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = r + ‖c‖ := by rw [hzc]
        _ = ‖c‖ + r := by ring
    have hz2 : 2 * ‖z‖ ≤ R := by simp only [hRdef]; linarith
    have hzlt : ‖z‖ < R := by nlinarith [norm_nonneg z]
    have hzmem : z ∈ ball (0:ℂ) R := mem_ball_zero_iff.mpr hzlt
    have hfrac : ‖z‖ / (R - ‖z‖) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    calc ‖h z‖ ≤ 2 * M R * ‖z‖ / (R - ‖z‖) := hBC R hRge z hzmem
      _ = 2 * M R * (‖z‖ / (R - ‖z‖)) := by ring
      _ ≤ 2 * M R * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 2 * M R := by ring

  have hCauchy : ∀ c : ℂ, ∀ r : ℝ, 2 ≤ r →
      ‖iteratedDeriv 2 h c‖ ≤ 4 * M (2 * (‖c‖ + r)) / r ^ 2 := by
    intro c r hr
    have hest := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
      (by linarith : (0:ℝ) < r) hhdiff.diffContOnCl (hsphere c r hr)
    calc ‖iteratedDeriv 2 h c‖
        ≤ ↑(Nat.factorial 2) * (2 * M (2 * (‖c‖ + r))) / r ^ 2 := hest
      _ = 4 * M (2 * (‖c‖ + r)) / r ^ 2 := by
          rw [Nat.factorial_two]; push_cast; ring

  intro c
  have hub : ∀ r : ℝ, max ‖c‖ 2 ≤ r →
      ‖iteratedDeriv 2 h c‖
        ≤ 16 * C₁ * Real.log (4 * r) / r + 4 * D₂ / r ^ 2 := by
    intro r hr
    have hr2 : (2:ℝ) ≤ r := (le_max_right _ _).trans hr
    have hrc : ‖c‖ ≤ r := (le_max_left _ _).trans hr
    have hrpos : (0:ℝ) < r := by linarith
    have h4rpos : (0:ℝ) < 4 * r := by linarith
    have hlog4r : 0 ≤ Real.log (4 * r) := Real.log_nonneg (by linarith)
    have hMub : M (2 * (‖c‖ + r)) ≤ C₁ * (4 * r) * Real.log (4 * r) + D₂ := by
      simp only [hMdef]
      have harg : 2 * (‖c‖ + r) ≤ 4 * r := by linarith
      have hargpos : (0:ℝ) < 2 * (‖c‖ + r) := by nlinarith [norm_nonneg c]
      have hlogle : Real.log (2 * (‖c‖ + r)) ≤ Real.log (4 * r) :=
        Real.log_le_log hargpos harg
      have hlogpos : 0 ≤ Real.log (2 * (‖c‖ + r)) :=
        Real.log_nonneg (by nlinarith [norm_nonneg c])
      nlinarith [mul_le_mul harg hlogle hlogpos (by linarith),
        mul_nonneg hC₁nn (mul_nonneg (by linarith : (0:ℝ) ≤ 4*r) hlog4r)]
    calc ‖iteratedDeriv 2 h c‖
        ≤ 4 * M (2 * (‖c‖ + r)) / r ^ 2 := hCauchy c r hr2
      _ ≤ 4 * (C₁ * (4 * r) * Real.log (4 * r) + D₂) / r ^ 2 := by
          gcongr
      _ = 16 * C₁ * Real.log (4 * r) / r + 4 * D₂ / r ^ 2 := by
          field_simp; ring
  have hlim : Tendsto
      (fun r : ℝ => 16 * C₁ * Real.log (4 * r) / r + 4 * D₂ / r ^ 2)
      atTop (𝓝 0) := by
    have hlog : Tendsto (fun r : ℝ => Real.log (4 * r) / r) atTop (𝓝 0) := by
      have hbase := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simp only [pow_one, one_mul, add_zero] at hbase
      have h4r : Tendsto (fun r : ℝ => 4 * r) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) tendsto_id
      have hcomp := hbase.comp h4r
      have hcomp4 := hcomp.const_mul 4
      simp only [Function.comp_def, mul_zero] at hcomp4
      convert hcomp4 using 2 with r; ring
    have h1 : Tendsto (fun r : ℝ => 16 * C₁ * Real.log (4 * r) / r)
        atTop (𝓝 0) := by
      have := hlog.const_mul (16 * C₁)
      simpa [mul_div_assoc] using this
    have h2 : Tendsto (fun r : ℝ => 4 * D₂ / r ^ 2) atTop (𝓝 0) := by
      have hpow : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
        tendsto_pow_atTop two_ne_zero
      have := hpow.inv_tendsto_atTop.const_mul (4 * D₂)
      simpa [div_eq_mul_inv] using this
    have := h1.add h2
    simpa using this
  have hle0 : ‖iteratedDeriv 2 h c‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.mpr ⟨max ‖c‖ 2, hub⟩)
  exact norm_le_zero_iff.mp hle0

set_option maxHeartbeats 9600000 in

theorem gapsw80_t40_D1b0b_closed : gapsw80_t39_ZeroFreeOrderOneExpForm := by
  have _em := Classical.em
  intro g hgdiff hgne hord
  obtain ⟨C, hord'⟩ := hord

  obtain ⟨h, hh0, hhd⟩ := gapsw80_t40_logDeriv_primitive hgdiff hgne
  have hhdiff : Differentiable ℂ h := fun s => (hhd s).differentiableAt

  have hgexp := gapsw80_t40_eq_const_mul_exp hgdiff hgne hh0 hhd

  have hg0ne : g 0 ≠ 0 := hgne 0
  have hReH : ∀ s, (h s).re = Real.log ‖g s‖ - Real.log ‖g 0‖ := by
    intro s
    have hnorm : ‖g s‖ = ‖g 0‖ * Real.exp (h s).re := by
      rw [hgexp s, norm_mul, Complex.norm_exp]
    have hg0pos : (0:ℝ) < ‖g 0‖ := norm_pos_iff.mpr hg0ne
    rw [hnorm, Real.log_mul hg0pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

  have hh2 : ∀ c, iteratedDeriv 2 h c = 0 := by
    apply gapsw80_t40_iteratedDeriv_two_eq_zero_of_re_growth hhdiff hh0
    refine ⟨C, -Real.log ‖g 0‖, fun s hs => ?_⟩
    rw [hReH s]
    linarith [hord' s hs]

  have hlin : ∀ s, h s = deriv h 0 * s := by
    intro s
    have := gapsw80_t40_linear_of_iteratedDeriv_two_eq_zero hhdiff hh2 s
    simpa [hh0] using this

  refine ⟨Complex.log (g 0), deriv h 0, fun s => ?_⟩
  rw [Complex.exp_add, Complex.exp_log hg0ne, ← hlin s, ← hgexp s]

end FLT.Gapsw80T40D1b0bZeroFreeExpLinearProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T41D1b0aHadamardFactorSubDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T40D1b0bZeroFreeExpLinearProof
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

def gapsw80_t41_XiNonzeroInfiniteZeros : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ξ 0 ≠ 0 ∧ Set.Infinite {s | ξ s = 0}

def gapsw80_t41_EntireOrderOneCanonicalFactor : Prop :=
  ∀ f : ℂ → ℂ,
    Differentiable ℂ f →
    f 0 ≠ 0 →
    Set.Infinite {s | f s = 0} →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ∃ (ρ : ℕ → ℂ) (g : ℂ → ℂ),
      (∀ j, f (ρ j) = 0) ∧
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
      Differentiable ℂ g ∧
      (∀ s : ℂ, g s ≠ 0) ∧
      (∀ s : ℂ, f s = g s
          * ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j)))

def gapsw80_t41_CanonicalQuotientOrderBound : Prop :=
  ∀ (f g : ℂ → ℂ) (ρ : ℕ → ℂ),
    Differentiable ℂ f →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    Differentiable ℂ g →
    (∀ s : ℂ, g s ≠ 0) →
    (∀ s : ℂ, f s = g s
        * ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖g s‖ ≤ C * ‖s‖ * Real.log ‖s‖)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t41_D1b0a_of_D1b0a012
    (h0 : gapsw80_t41_XiNonzeroInfiniteZeros)
    (h1 : gapsw80_t41_EntireOrderOneCanonicalFactor)
    (h2 : gapsw80_t41_CanonicalQuotientOrderBound) :
    gapsw80_t39_XiCanonicalQuotient := by
  have _em := Classical.em
  intro K _ _ _ ξ hdiff hagr hord
  obtain ⟨hξ0, hinf⟩ := h0 K ξ hdiff hagr hord
  obtain ⟨ρ, g, hzero, hsum, hgdiff, hgne, hfact⟩ := h1 ξ hdiff hξ0 hinf hord
  exact ⟨ρ, g, hzero, hsum, hgdiff, hgne, hfact,
    h2 ξ g ρ hdiff hord hsum hgdiff hgne hfact⟩

end FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T35D1apa0ThreeFourOneIneqProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T27D2d0EulerProductAncestor
open FLT.Gapsw80T28D2d0aSummabilityProof
open FLT.Gapsw80T30D2d0cLocalEulerFactorProof
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T34D1apaThreeFourOneIneqDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t35_nonneg_three_four_one_re_sq {z : ℂ} (h : ‖z‖ = 1) :
    (0:ℝ) ≤ 3 + 4 * z.re + (z^2).re := by
  have _em := Classical.em
  have h2 : z.re^2 + z.im^2 = 1 := by
    have hsn := Complex.sq_norm z
    rw [h, Complex.normSq_apply] at hsn; nlinarith
  have hsq : (z^2).re = z.re^2 - z.im^2 := by rw [sq, Complex.mul_re]; ring
  have hid : 3 + 4 * z.re + (z^2).re = 2 * (1 + z.re)^2 := by
    rw [hsq]; nlinarith [h2]
  rw [hid]; positivity

set_option maxHeartbeats 3200000 in

theorem gapsw80_t35_natCast_cpow_neg_ofReal (N : ℕ) (σ : ℝ) :
    (N:ℂ)^(-(↑σ:ℂ)) = (((N:ℝ)^(-σ) : ℝ) : ℂ) := by
  have _em := Classical.em
  rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg N)]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t35_norm_natCast_cpow_neg_mul_I {N : ℕ} (hN : 0 < N) (y : ℝ) :
    ‖(N:ℂ)^(-(↑y * I))‖ = 1 := by
  have _em := Classical.em
  rw [Complex.norm_natCast_cpow_of_pos hN]; simp

set_option maxHeartbeats 8000000 in

theorem gapsw80_t35_re_threeFourOne_log_nonneg {N : ℕ} (hN : 2 ≤ N)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ (3 * (-Complex.log (1 - (N:ℂ)^(-(↑σ:ℂ))))
        + 4 * (-Complex.log (1 - (N:ℂ)^(-((↑σ:ℂ) + ↑t * I))))
        + (-Complex.log (1 - (N:ℂ)^(-((↑σ:ℂ) + 2 * ↑t * I))))).re := by
  have _em := Classical.em
  have hN0 : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNR : (0:ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le two_pos hN)

  set r := (N:ℝ)^(-σ) with hr_def
  set w := (N:ℂ)^(-((↑t:ℂ) * I)) with hw_def
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hNR _
  have hw_norm : ‖w‖ = 1 := gapsw80_t35_norm_natCast_cpow_neg_mul_I (by omega) t

  have hx0 : (N:ℂ)^(-(↑σ:ℂ)) = (↑r:ℂ) :=
    gapsw80_t35_natCast_cpow_neg_ofReal N σ
  have hx1 : (N:ℂ)^(-((↑σ:ℂ) + ↑t * I)) = (↑r:ℂ) * w := by
    rw [show (-((↑σ:ℂ) + ↑t * I)) = (-(↑σ:ℂ)) + (-(↑t * I)) by ring,
      Complex.cpow_add _ _ hN0, hx0, hw_def]
  have hx2 : (N:ℂ)^(-((↑σ:ℂ) + 2 * ↑t * I)) = (↑r:ℂ) * w^2 := by
    rw [show (-((↑σ:ℂ) + 2 * ↑t * I)) = (-(↑σ:ℂ)) + ((2:ℕ):ℂ)*(-(↑t * I)) by
          push_cast; ring,
      Complex.cpow_add _ _ hN0, hx0, Complex.cpow_nat_mul, hw_def]

  have hn0 : ‖(↑r:ℂ)‖ < 1 := by
    rw [← hx0]; exact gapsw80_t27_norm_natCast_cpow_lt_one hN (by simpa using hσ)
  have hn1 : ‖(↑r:ℂ) * w‖ < 1 := by rw [norm_mul, hw_norm, mul_one]; exact hn0
  have hn2 : ‖(↑r:ℂ) * w^2‖ < 1 := by
    rw [norm_mul, norm_pow, hw_norm, one_pow, mul_one]; exact hn0

  have hcomb : HasSum
      (fun n : ℕ => 3 * ((↑r:ℂ)^n / n) + (4 * (((↑r:ℂ)*w)^n / n)
        + (((↑r:ℂ)*w^2)^n / n)))
      (3 * (-Complex.log (1 - (↑r:ℂ))) + (4 * (-Complex.log (1 - (↑r:ℂ)*w))
        + (-Complex.log (1 - (↑r:ℂ)*w^2)))) :=
    ((Complex.hasSum_taylorSeries_neg_log hn0).mul_left 3).add
      (((Complex.hasSum_taylorSeries_neg_log hn1).mul_left 4).add
        (Complex.hasSum_taylorSeries_neg_log hn2))

  rw [hx0, hx1, hx2, show ((3:ℂ) * _ + 4 * _ + _) = (3 * _ + (4 * _ + _)) from
    (add_assoc _ _ _)]
  refine (Complex.hasSum_re hcomb).nonneg (fun n => ?_)

  show 0 ≤ (3 * ((↑r:ℂ)^n / n) + (4 * (((↑r:ℂ)*w)^n / n)
    + (((↑r:ℂ)*w^2)^n / n))).re
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hncC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hkey : 3 * ((↑r:ℂ)^n / n) + (4 * (((↑r:ℂ)*w)^n / n)
          + (((↑r:ℂ)*w^2)^n / n))
        = (↑(r^n) : ℂ) * (3 + 4*w^n + (w^n)^2) / n := by
      push_cast
      rw [mul_pow, mul_pow, ← pow_mul]
      field_simp; ring
    rw [hkey, Complex.div_natCast_re]
    refine div_nonneg ?_ (Nat.cast_nonneg n)
    have hre : ((↑(r^n) : ℂ) * (3 + 4*w^n + (w^n)^2)).re
        = r^n * (3 + 4*(w^n).re + ((w^n)^2).re) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      simp only [zero_mul, sub_zero, Complex.add_re, Complex.mul_re,
        Complex.re_ofNat, Complex.im_ofNat]
    rw [hre]
    exact mul_nonneg (pow_pos hr_pos n).le
      (gapsw80_t35_nonneg_three_four_one_re_sq
        (by rw [norm_pow, hw_norm, one_pow]))

set_option maxHeartbeats 8000000 in

theorem gapsw80_t35_D1apa0_closed :
    gapsw80_t34_DedekindZetaThreeFourOneIneq := by
  have _em := Classical.em
  intro K _ _ _ t _ht σ hσ

  have hD2d0 : gapsw80_t27_DedekindZetaEulerProductExpForm :=
    gapsw80_t28_D2d0_of_D2d0b gapsw80_t30_sat_D2d0b_unconditional

  have hre0 : 1 < ((↑σ:ℂ)).re := by simpa using hσ
  have hre1 : 1 < ((↑σ:ℂ) + ↑t * I).re := by simp; exact hσ
  have hre2 : 1 < ((↑σ:ℂ) + 2 * ↑t * I).re := by simp; exact hσ

  obtain ⟨hsm0, hexp0⟩ := hD2d0 K _ hre0
  obtain ⟨hsm1, hexp1⟩ := hD2d0 K _ hre1
  obtain ⟨hsm2, hexp2⟩ := hD2d0 K _ hre2

  set S₀ := ∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥},
    -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-(↑σ:ℂ))) with hS0
  set S₁ := ∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥},
    -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-((↑σ:ℂ) + ↑t * I))) with hS1
  set S₂ := ∑' p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥},
    -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-((↑σ:ℂ) + 2 * ↑t * I)))
    with hS2

  have hs0 : Summable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-(↑σ:ℂ)))) :=
    hsm0.of_norm.clog_one_sub.neg
  have hs1 : Summable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-((↑σ:ℂ) + ↑t * I)))) :=
    hsm1.of_norm.clog_one_sub.neg
  have hs2 : Summable (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      -Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-((↑σ:ℂ) + 2*↑t*I)))) :=
    hsm2.of_norm.clog_one_sub.neg

  have hG : HasSum (fun p : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      3 * (-Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-(↑σ:ℂ))))
        + 4 * (-Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-((↑σ:ℂ)+↑t*I))))
        + (-Complex.log (1 - ((Ideal.absNorm p.1 : ℕ) : ℂ) ^ (-((↑σ:ℂ)+2*↑t*I)))))
      (3 * S₀ + 4 * S₁ + S₂) := by
    have := ((hs0.hasSum.mul_left 3).add (hs1.hasSum.mul_left 4)).add hs2.hasSum
    simpa only [hS0, hS1, hS2] using this

  have hRe_nonneg : 0 ≤ (3 * S₀ + 4 * S₁ + S₂).re :=
    (Complex.hasSum_re hG).nonneg (fun p =>
      gapsw80_t35_re_threeFourOne_log_nonneg
        (gapsw80_t27_one_lt_absNorm_prime p) hσ t)

  have hProd : ‖dedekindZeta K (↑σ : ℂ)‖ ^ 3 * ‖dedekindZeta K (↑σ + t * I)‖ ^ 4
        * ‖dedekindZeta K (↑σ + 2 * t * I)‖
      = Real.exp (3 * S₀.re + 4 * S₁.re + S₂.re) := by
    rw [hexp0, hexp1, hexp2,
      Complex.norm_exp, Complex.norm_exp, Complex.norm_exp,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    push_cast; ring_nf
  have hReEq : 3 * S₀.re + 4 * S₁.re + S₂.re = (3 * S₀ + 4 * S₁ + S₂).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero]
  rw [hProd, hReEq]
  exact Real.one_le_exp hRe_nonneg

end FLT.Gapsw80T35D1apa0ThreeFourOneIneqProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T42D1b0a0XiNonzeroInfZerosProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T36D1appXiEndpointResidueProof
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T40D1b0bZeroFreeExpLinearProof
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

theorem gapsw80_t42_not_locally_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) (z : ℂ) : ¬ (∀ᶠ w in 𝓝 z, f w = 0) := by
  intro hev
  have hAn : AnalyticOnNhd ℂ f univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hEq : EqOn f 0 univ :=
    hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) hev
  exact hz₀ (hEq (mem_univ z₀))

set_option maxHeartbeats 9600000 in

theorem gapsw80_t42_exists_quotient_at_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) {ρ : ℂ} (hρ : f ρ = 0) :
    ∃ f₁ : ℂ → ℂ, Differentiable ℂ f₁ ∧ f₁ ρ ≠ 0 ∧
      ∀ s, f s = (s - ρ) ^ (analyticOrderNatAt f ρ) * f₁ s := by
  have hAn : AnalyticAt ℂ f ρ := hf.analyticAt _
  have hnt : analyticOrderAt f ρ ≠ ⊤ :=
    fun h => gapsw80_t42_not_locally_zero hf hz₀ ρ (analyticOrderAt_eq_top.mp h)
  set m := analyticOrderNatAt f ρ with hm
  obtain ⟨g, hgA, hgρ, hev⟩ := (hAn.analyticOrderNatAt_eq_iff hnt (n := m)).mp rfl

  refine ⟨Function.update (fun s => f s / (s - ρ) ^ m) ρ (g ρ), ?_, ?_, ?_⟩
  ·
    rw [← differentiableOn_univ,
      ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (univ_mem)]
    refine ⟨fun s hs => ?_, ?_⟩
    ·

      have hsρ : s ≠ ρ := hs.2
      have hq : DifferentiableAt ℂ (fun w => f w / (w - ρ) ^ m) s :=
        hf.differentiableAt.div (by fun_prop)
          (pow_ne_zero _ (sub_ne_zero.mpr hsρ))
      refine hq.differentiableWithinAt.congr_of_eventuallyEq
        ?_ (Function.update_of_ne hsρ _ _)
      exact eventually_nhdsWithin_of_forall
        fun w hw => Function.update_of_ne hw.2 _ _
    ·

      refine ContinuousAt.congr hgA.continuousAt ?_
      filter_upwards [hev] with w hw
      rcases eq_or_ne w ρ with rfl | hwρ
      · simp [Function.update_self]
      · rw [Function.update_of_ne hwρ, hw, smul_eq_mul,
          mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hwρ))]
  ·
    simp [Function.update_self, hgρ]
  ·

    have hm1 : m ≠ 0 := by
      rw [hm]; intro h0
      have h0' : analyticOrderAt f ρ = (0 : ℕ) := by
        rw [← Nat.cast_analyticOrderNatAt hnt, h0]
      exact (hAn.analyticOrderAt_eq_zero.mp h0') hρ
    intro s
    rcases eq_or_ne s ρ with hsρ | hsρ
    ·
      rw [hsρ, hρ, Function.update_self, sub_self, zero_pow hm1, zero_mul]
    · rw [Function.update_of_ne hsρ,
        mul_div_cancel₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hsρ))]

set_option maxHeartbeats 9600000 in

theorem gapsw80_t42_hord_of_factor {f f₁ : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hf₁ : Differentiable ℂ f₁) (hfact : ∀ s, f s = (s - ρ) ^ m * f₁ s)
    (hord : ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) :
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖f₁ s‖ ≤ C * ‖s‖ * Real.log ‖s‖ := by
  obtain ⟨C, hC⟩ := hord
  set R : ℝ := 2 * (‖ρ‖ + 1) with hR
  have hR2 : 2 ≤ R := by rw [hR]; nlinarith [norm_nonneg ρ]

  obtain ⟨zmax, -, hmax⟩ :=
    (isCompact_closedBall (0:ℂ) R).exists_isMaxOn (Metric.nonempty_closedBall.mpr
        (le_trans (by norm_num) hR2))
      hf₁.continuous.norm.continuousOn
  set D : ℝ := Real.log ‖f₁ zmax‖ with hD
  have hslog : (0:ℝ) < 2 * Real.log 2 :=
    mul_pos two_pos (Real.log_pos one_lt_two)
  refine ⟨max C (max 0 D / (2 * Real.log 2)), fun s hs => ?_⟩
  have hslog' : 2 * Real.log 2 ≤ ‖s‖ * Real.log ‖s‖ := by
    have h1 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log two_pos hs
    nlinarith [Real.log_pos one_lt_two, le_trans (by norm_num : (0:ℝ) ≤ 2) hs]
  have hslog'' : 0 ≤ ‖s‖ * Real.log ‖s‖ :=
    le_trans (mul_nonneg two_pos.le (Real.log_pos one_lt_two).le) hslog'
  rcases le_or_gt ‖s‖ R with hle | hgt
  ·
    have hmem : s ∈ Metric.closedBall (0:ℂ) R :=
      Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hle)
    have hDle : Real.log ‖f₁ s‖ ≤ max 0 D := by
      rcases le_or_gt ‖f₁ s‖ 1 with h1 | h1
      · exact le_trans (Real.log_nonpos (norm_nonneg _) h1) (le_max_left _ _)
      · exact le_trans (Real.log_le_log (lt_trans one_pos h1) (hmax hmem))
          (le_max_right _ _)
    calc Real.log ‖f₁ s‖
        ≤ max 0 D := hDle
      _ = (max 0 D / (2 * Real.log 2)) * (2 * Real.log 2) :=
            (div_mul_cancel₀ _ hslog.ne').symm
      _ ≤ (max 0 D / (2 * Real.log 2)) * (‖s‖ * Real.log ‖s‖) :=
            mul_le_mul_of_nonneg_left hslog'
              (div_nonneg (le_max_left _ _) hslog.le)
      _ ≤ max C (max 0 D / (2 * Real.log 2)) * ‖s‖ * Real.log ‖s‖ := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) hslog''
  ·

    have hsρ : 1 ≤ ‖s - ρ‖ := by
      have : ‖s‖ - ‖ρ‖ ≤ ‖s - ρ‖ := by
        have := norm_sub_norm_le s ρ; linarith [abs_le.mp (abs_norm_sub_norm_le s ρ)]
      nlinarith
    have hsρ' : s ≠ ρ := fun h => by simp [h] at hsρ; linarith
    have hne : (s - ρ) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hsρ')
    have hlog : Real.log ‖f₁ s‖ ≤ Real.log ‖f s‖ := by
      rcases eq_or_ne (f₁ s) 0 with h0 | hn0
      · rw [h0, norm_zero, Real.log_zero, hfact, h0, mul_zero, norm_zero, Real.log_zero]
      · rw [hfact, norm_mul, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hn0),
          norm_pow, Real.log_pow]
        nlinarith [Real.log_nonneg hsρ]
    calc Real.log ‖f₁ s‖ ≤ Real.log ‖f s‖ := hlog
      _ ≤ C * ‖s‖ * Real.log ‖s‖ := hC s hs
      _ ≤ max C (max 0 D / (2 * Real.log 2)) * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hslog''

set_option maxHeartbeats 12800000 in

theorem gapsw80_t42_finiteZeros_linear_bound :
    ∀ (F : Finset ℂ), ∀ f : ℂ → ℂ, Differentiable ℂ f → f 0 ≠ 0 →
    (0 : ℂ) ∉ F → (∀ s, f s = 0 → s ∈ F) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ := by
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro f hdiff hf0 _ hzero hord

    have hne : ∀ s, f s ≠ 0 := fun s hs => (Finset.notMem_empty s) (hzero s hs)
    obtain ⟨A, B, hAB⟩ := gapsw80_t40_D1b0b_closed f hdiff hne hord
    refine ⟨max 0 (‖A‖ / 2 + ‖B‖), fun s hs => ?_⟩
    rw [hAB, Complex.norm_exp, Real.log_exp]
    calc (A + B * s).re ≤ |(A + B * s).re| := le_abs_self _
      _ ≤ ‖A + B * s‖ := Complex.abs_re_le_norm _
      _ ≤ ‖A‖ + ‖B‖ * ‖s‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (‖A‖ / 2) * ‖s‖ + ‖B‖ * ‖s‖ := by nlinarith [norm_nonneg A]
      _ = (‖A‖ / 2 + ‖B‖) * ‖s‖ := by ring
      _ ≤ max 0 (‖A‖ / 2 + ‖B‖) * ‖s‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  | insert ρ F' hρF' IH =>
    intro f hdiff hf0 h0F hzero hord
    have h0F' : (0 : ℂ) ∉ F' := fun h => h0F (Finset.mem_insert_of_mem h)
    have hρ0 : ρ ≠ 0 := fun h => h0F (h ▸ Finset.mem_insert_self ρ F')

    rcases eq_or_ne (f ρ) 0 with hfρ | hfρ
    ·
      obtain ⟨f₁, hf₁diff, hf₁ρ, hfact⟩ :=
        gapsw80_t42_exists_quotient_at_zero hdiff hf0 hfρ
      set m := analyticOrderNatAt f ρ with hm
      have hf₁0 : f₁ 0 ≠ 0 := fun h => hf0 (by rw [hfact, h, mul_zero])
      have hzero₁ : ∀ s, f₁ s = 0 → s ∈ F' := by
        intro s hs
        rcases eq_or_ne s ρ with rfl | hsρ
        · exact absurd hs hf₁ρ
        · have : f s = 0 := by rw [hfact, hs, mul_zero]
          have hsF := hzero s this
          rcases Finset.mem_insert.mp hsF with h | h
          · exact absurd h hsρ
          · exact h
      have hord₁ := gapsw80_t42_hord_of_factor hf₁diff hfact hord
      obtain ⟨C₁, hC₁⟩ := IH f₁ hf₁diff hf₁0 h0F' hzero₁ hord₁

      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · exfalso; apply hf₁ρ
          have hf' := hfact ρ
          rw [h0, pow_zero, one_mul] at hf'
          exact hf' ▸ hfρ
        · exact hpos

      set L := Real.log (1 + ‖ρ‖ / 2) with hL
      have hLnn : 0 ≤ L := Real.log_nonneg (by linarith [norm_nonneg ρ])
      refine ⟨max 0 (m * L / 2 + m + C₁), fun s hs => ?_⟩
      have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
      rcases eq_or_ne (f s) 0 with hfs0 | hfsn
      ·
        rw [hfs0, norm_zero, Real.log_zero]
        exact mul_nonneg (le_max_left _ _) hspos.le
      ·
        rw [hfact] at hfsn
        have hne : (s - ρ) ^ m ≠ 0 := left_ne_zero_of_mul hfsn
        have hn0 : f₁ s ≠ 0 := right_ne_zero_of_mul hfsn
        have hsρ : s ≠ ρ := fun h =>
          hne (by rw [h, sub_self]; exact zero_pow (Nat.one_le_iff_ne_zero.mp hm1))

        have hsub_ub : ‖s - ρ‖ ≤ (1 + ‖ρ‖ / 2) * ‖s‖ := by
          calc ‖s - ρ‖ ≤ ‖s‖ + ‖ρ‖ := norm_sub_le s ρ
            _ ≤ ‖s‖ + (‖ρ‖ / 2) * ‖s‖ := by nlinarith [norm_nonneg ρ]
            _ = (1 + ‖ρ‖ / 2) * ‖s‖ := by ring
        have hsub_pos : (0:ℝ) < ‖s - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsρ)
        have hlog_sub : Real.log ‖s - ρ‖ ≤ L + ‖s‖ := by
          calc Real.log ‖s - ρ‖
              ≤ Real.log ((1 + ‖ρ‖ / 2) * ‖s‖) :=
                Real.log_le_log hsub_pos hsub_ub
            _ = L + Real.log ‖s‖ :=
                Real.log_mul (by linarith [norm_nonneg ρ]) hspos.ne'
            _ ≤ L + ‖s‖ := by
                linarith [Real.log_le_sub_one_of_pos hspos]
        calc Real.log ‖f s‖
            = Real.log ‖(s - ρ) ^ m * f₁ s‖ := by rw [hfact]
          _ = m * Real.log ‖s - ρ‖ + Real.log ‖f₁ s‖ := by
              rw [norm_mul, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hn0),
                norm_pow, Real.log_pow]
          _ ≤ m * (L + ‖s‖) + C₁ * ‖s‖ := by
              gcongr; exact hC₁ s hs
          _ = (m * L / 2) * 2 + (m + C₁) * ‖s‖ := by push_cast; ring
          _ ≤ (m * L / 2) * ‖s‖ + (m + C₁) * ‖s‖ := by
              have hmL2 : (0:ℝ) ≤ m * L / 2 := by positivity
              nlinarith
          _ = (m * L / 2 + m + C₁) * ‖s‖ := by ring
          _ ≤ max 0 (m * L / 2 + m + C₁) * ‖s‖ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hspos.le
    ·
      have hzero' : ∀ s, f s = 0 → s ∈ F' := by
        intro s hs
        rcases Finset.mem_insert.mp (hzero s hs) with h | h
        · exact absurd (h ▸ hs) hfρ
        · exact h
      exact IH f hdiff hf0 h0F' hzero' hord

def gapsw80_t42_CompletedZetaRealSuperlinear : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [S18.HADPkg K], ∀ C : ℝ, ∃ s : ℂ,
    2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
    C * ‖s‖ < Real.log ‖s * (s - 1) * gapsw80_t9_completedDedekindZeta K s‖

set_option maxHeartbeats 9600000 in

theorem gapsw80_t42_D1b0a0_closed
    (hSL : gapsw80_t42_CompletedZetaRealSuperlinear) :
    gapsw80_t41_XiNonzeroInfiniteZeros := by
  have _em := Classical.em
  intro K _ _ _ ξ hdiff hagr hord

  have hξ0 : ξ 0 ≠ 0 := (gapsw80_t36_D1app_closed K ξ hdiff hagr).1
  refine ⟨hξ0, ?_⟩

  by_contra hfin'
  have hfin : Set.Finite {s | ξ s = 0} := Set.not_infinite.mp hfin'
  have h0F : (0:ℂ) ∉ hfin.toFinset := fun h => hξ0 (hfin.mem_toFinset.mp h)
  have hzero : ∀ s, ξ s = 0 → s ∈ hfin.toFinset :=
    fun s hs => hfin.mem_toFinset.mpr hs
  obtain ⟨C₀, hub⟩ :=
    gapsw80_t42_finiteZeros_linear_bound hfin.toFinset ξ hdiff hξ0 h0F hzero hord

  obtain ⟨s, hs2, hs0, hs1, hlt⟩ := hSL K C₀
  rw [← hagr s hs0 hs1] at hlt
  exact absurd (hub s hs2) (not_le.mpr hlt)

end FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section
namespace FLT
namespace Gapsw80T43CompletedZetaRealSuperlinearProof
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof FLT.Gapsw80T9ClassSumA1Closure

theorem gapsw80_t43_SL_closed : gapsw80_t42_CompletedZetaRealSuperlinear := by
  intro K _ _ _ C
  exact S18.HADPkg.SL C
end FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T44D1b0a1HadamardSansOrderSubDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
open FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

def gapsw80_t44_ZeroEnumWithMultSummable : Prop :=
  ∀ f : ℂ → ℂ,
    Differentiable ℂ f →
    f 0 ≠ 0 →
    Set.Infinite {s | f s = 0} →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ∃ ρ : ℕ → ℂ,
      (∀ j, f (ρ j) = 0) ∧
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
      (∀ z, Nat.card {j | ρ j = z} = analyticOrderNatAt f z)

def gapsw80_t44_CanonicalProductEntireOrder : Prop :=
  ∀ ρ : ℕ → ℂ,
    (∀ j, ρ j ≠ 0) →
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    Differentiable ℂ (fun s => ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) ∧
    (∀ z, analyticOrderNatAt
            (fun s => ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) z
          = Nat.card {j | ρ j = z})

def gapsw80_t44_EntireQuotientOfOrderMatch : Prop :=
  ∀ f P : ℂ → ℂ,
    Differentiable ℂ f →
    f 0 ≠ 0 →
    Differentiable ℂ P →
    P 0 ≠ 0 →
    (∀ z, analyticOrderNatAt f z = analyticOrderNatAt P z) →
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ s, g s ≠ 0) ∧ (∀ s, f s = g s * P s)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t44_D1b0a1_of_abc
    (ha : gapsw80_t44_ZeroEnumWithMultSummable)
    (hb : gapsw80_t44_CanonicalProductEntireOrder)
    (hc : gapsw80_t44_EntireQuotientOfOrderMatch) :
    gapsw80_t41_EntireOrderOneCanonicalFactor := by
  have _em := Classical.em
  intro f hdiff hf0 hinf hord
  obtain ⟨ρ, hzero, hsum, hcount⟩ := ha f hdiff hf0 hinf hord
  have hρ0 : ∀ j, ρ j ≠ 0 := fun j h => hf0 (h ▸ hzero j)
  obtain ⟨hPdiff, hPord⟩ := hb ρ hρ0 hsum
  have hP0 :
      (fun s => ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) 0 ≠ 0 := by
    simp
  have hom : ∀ z, analyticOrderNatAt f z
      = analyticOrderNatAt
          (fun s => ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) z :=
    fun z => (hcount z).symm.trans (hPord z).symm
  obtain ⟨g, hgdiff, hgne, hfact⟩ := hc f _ hdiff hf0 hPdiff hP0 hom
  exact ⟨ρ, g, hzero, hsum, hgdiff, hgne, hfact⟩

end FLT.Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T50D1b0a2MinModulusSubDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

def gapsw80_t50_QuotientLogSubTwoGrowth : Prop :=
  ∀ (f g : ℂ → ℂ) (ρ : ℕ → ℂ),
    Differentiable ℂ f →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    Differentiable ℂ g →
    (∀ s : ℂ, g s ≠ 0) →
    (∀ s : ℂ, f s = g s
        * ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖g s‖ ≤ C * ‖s‖ * Real.sqrt ‖s‖)

def gapsw80_t50_NonvanishOrderSubTwoExpLinear : Prop :=
  ∀ g : ℂ → ℂ,
    Differentiable ℂ g →
    (∀ s : ℂ, g s ≠ 0) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖g s‖ ≤ C * ‖s‖ * Real.sqrt ‖s‖) →
    ∃ A B : ℂ, ∀ s : ℂ, g s = Complex.exp (A + B * s)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t50_D1b0a2_of_D1b0a2ab
    (ha : gapsw80_t50_QuotientLogSubTwoGrowth)
    (hb : gapsw80_t50_NonvanishOrderSubTwoExpLinear) :
    gapsw80_t41_CanonicalQuotientOrderBound := by
  have _em := Classical.em
  intro f g ρ hfdiff hford hsum hgdiff hgne hfact
  obtain ⟨A, B, hexp⟩ :=
    hb g hgdiff hgne (ha f g ρ hfdiff hford hsum hgdiff hgne hfact)
  refine ⟨(‖A‖ + 2 * ‖B‖) / (2 * Real.log 2), fun s hs => ?_⟩
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlogs : Real.log 2 ≤ Real.log ‖s‖ :=
    Real.log_le_log two_pos hs
  have hlogs0 : (0:ℝ) < Real.log ‖s‖ := lt_of_lt_of_le hlog2 hlogs
  have hnorm : Real.log ‖g s‖ = (A + B * s).re := by
    rw [hexp s, Complex.norm_exp, Real.log_exp]
  rw [hnorm, Complex.add_re]
  have hA : A.re ≤ ‖A‖ := Complex.re_le_norm A
  have hB : (B * s).re ≤ ‖B‖ * ‖s‖ :=
    (Complex.re_le_norm _).trans_eq (norm_mul B s)
  have h2s : (2:ℝ) ≤ ‖s‖ := hs
  have hAn : (0:ℝ) ≤ ‖A‖ := norm_nonneg A
  have hBn : (0:ℝ) ≤ ‖B‖ := norm_nonneg B
  have hkey : (2:ℝ) * Real.log 2 ≤ ‖s‖ * Real.log ‖s‖ :=
    mul_le_mul h2s hlogs hlog2.le (by linarith)
  have hstep : ‖A‖ + ‖B‖ * ‖s‖
      ≤ (‖A‖ + 2 * ‖B‖) / (2 * Real.log 2) * ‖s‖ * Real.log ‖s‖ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hAn (sub_nonneg.mpr hkey),
      mul_nonneg (mul_nonneg hBn (by linarith : (0:ℝ) ≤ ‖s‖))
        (sub_nonneg.mpr hlogs)]
  linarith

end FLT.Gapsw80T50D1b0a2MinModulusSubDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
open FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
open FLT.Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t45_eventually_large_norm_cofinite {ι : Type*} {ρ : ι → ℂ}
    (hρ0 : ∀ j, ρ j ≠ 0) (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    {R : ℝ} (hR : 0 < R) : ∀ᶠ j in cofinite, R ≤ ‖ρ j‖ := by
  have _em := Classical.em
  have h0 := hsum.tendsto_cofinite_zero
  simp_rw [Complex.normSq_eq_norm_sq] at h0
  have hR2 : (0 : ℝ) < (R ^ 2)⁻¹ := by positivity
  filter_upwards [h0.eventually_lt_const hR2] with j hj
  have hnj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsq : R ^ 2 ≤ ‖ρ j‖ ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact le_of_lt (by simpa using hj)
  nlinarith [sq_nonneg (R - ‖ρ j‖), sq_nonneg (R + ‖ρ j‖)]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t45_summable_norm_E1_sub_one {ι : Type*} {ρ : ι → ℂ}
    (hρ0 : ∀ j, ρ j ≠ 0) (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    (s : ℂ) :
    Summable fun j => ‖(1 - s / ρ j) * Complex.exp (s / ρ j) - 1‖ := by
  have _em := Classical.em
  set R : ℝ := ‖s‖ + 1 with hR
  have hR0 : (0 : ℝ) < R := by positivity
  have hlarge := gapsw80_t45_eventually_large_norm_cofinite hρ0 hsum
    (R := 2 * R) (by positivity)
  refine (hsum.mul_left (3 * R ^ 2)).of_norm_bounded_eventually ?_
  filter_upwards [hlarge] with j hj
  have hρj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsρ : ‖s / ρ j‖ ≤ 1 := by
    rw [norm_div, div_le_one hρj]; have : ‖s‖ < R := by rw [hR]; linarith
    linarith
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖(1 - s / ρ j) * Complex.exp (s / ρ j) - 1‖
      ≤ 3 * ‖s / ρ j‖ ^ 2 := gapsw80_t38_norm_E1_sub_one_le hsρ
    _ = 3 * ‖s‖ ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
        rw [norm_div, div_pow, Complex.normSq_eq_norm_sq]; ring
    _ ≤ 3 * R ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
        have hs2 : ‖s‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg s]
        have hnn : (0 : ℝ) ≤ (Complex.normSq (ρ j))⁻¹ :=
          inv_nonneg.mpr (Complex.normSq_nonneg _)
        nlinarith

set_option maxHeartbeats 9600000 in

theorem gapsw80_t45_tprod_E1_differentiable {ι : Type*} {ρ : ι → ℂ}
    (hρ0 : ∀ j, ρ j ≠ 0) (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) :
    Differentiable ℂ
      (fun s => ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) := by
  have _em := Classical.em
  intro s
  set F : ι → ℂ → ℂ := fun j z => (1 - z / ρ j) * Complex.exp (z / ρ j) with hF
  set R : ℝ := ‖s‖ + 1 with hR
  have hR0 : (0 : ℝ) < R := by positivity
  have hsK : s ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr (by rw [hR]; linarith [norm_nonneg s])
  have hlarge := gapsw80_t45_eventually_large_norm_cofinite hρ0 hsum
    (R := 2 * R) (by positivity)
  have hbound : ∀ᶠ j in cofinite, ∀ z ∈ ball (0 : ℂ) R,
      ‖F j z - 1‖ ≤ 3 * R ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
    filter_upwards [hlarge] with j hj z hz
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
    have hρj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
    have hzρ : ‖z / ρ j‖ ≤ 1 := by
      rw [norm_div, div_le_one hρj]; linarith
    have hnn : (0 : ℝ) ≤ (Complex.normSq (ρ j))⁻¹ :=
      inv_nonneg.mpr (Complex.normSq_nonneg _)
    calc ‖F j z - 1‖ = ‖(1 - z / ρ j) * Complex.exp (z / ρ j) - 1‖ := by rw [hF]
      _ ≤ 3 * ‖z / ρ j‖ ^ 2 := gapsw80_t38_norm_E1_sub_one_le hzρ
      _ = 3 * ‖z‖ ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
          rw [norm_div, div_pow, Complex.normSq_eq_norm_sq]; ring
      _ ≤ 3 * R ^ 2 * (Complex.normSq (ρ j))⁻¹ := by
          have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
          nlinarith
  have husum : Summable fun j => 3 * R ^ 2 * (Complex.normSq (ρ j))⁻¹ :=
    hsum.mul_left _
  have hprod := Summable.hasProdLocallyUniformlyOn_one_add
    (f := fun j z => F j z - 1) isOpen_ball husum hbound
    (fun j => by simp only [hF]; fun_prop)
  simp only [add_sub_cancel] at hprod
  have h1 : TendstoLocallyUniformlyOn (fun t z => ∏ j ∈ t, F j z)
      (fun z => ∏' j, F j z) atTop (ball (0 : ℂ) R) := hprod
  exact (h1.differentiableOn
      (Filter.Eventually.of_forall fun t => by simp only [hF]; fun_prop)
      isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hsK)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t45_tprod_E1_ne_zero {ι : Type*} {ρ : ι → ℂ}
    (hρ0 : ∀ j, ρ j ≠ 0) (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    {z : ℂ} (hz : ∀ j, ρ j ≠ z) :
    (∏' j, ((1 - z / ρ j) * Complex.exp (z / ρ j))) ≠ 0 := by
  have _em := Classical.em
  have hfac : ∀ j, (1 - z / ρ j) * Complex.exp (z / ρ j) ≠ 0 := fun j =>
    mul_ne_zero
      (sub_ne_zero.mpr fun h =>
        hz j (((div_eq_one_iff_eq (hρ0 j)).mp h.symm).symm))
      (Complex.exp_ne_zero _)
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun j => (1 - z / ρ j) * Complex.exp (z / ρ j) - 1)
    (fun j => by simpa using hfac j)
    (gapsw80_t45_summable_norm_E1_sub_one hρ0 hsum z)
  simpa using h

set_option maxHeartbeats 3200000 in

theorem gapsw80_t45_fiber_finite {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) (z : ℂ) :
    {j | ρ j = z}.Finite := by
  have _em := Classical.em
  rcases eq_or_ne z 0 with rfl | hz
  · exact Set.finite_empty.subset fun j hj => hρ0 j hj
  · by_contra hinf
    rw [← not_infinite, not_not] at hinf
    have hpos : (0 : ℝ) < (Complex.normSq z)⁻¹ :=
      inv_pos.mpr (Complex.normSq_pos.mpr hz)
    have hev : ∀ᶠ j in cofinite, (Complex.normSq (ρ j))⁻¹ < (Complex.normSq z)⁻¹ :=
      hsum.tendsto_cofinite_zero.eventually_lt_const hpos
    have hfreq : ∃ᶠ j in cofinite, ρ j = z :=
      frequently_cofinite_iff_infinite.mpr hinf
    rcases (hfreq.and_eventually hev).exists with ⟨j, hjz, hjlt⟩
    rw [hjz] at hjlt
    exact lt_irrefl _ hjlt

set_option maxHeartbeats 3200000 in

theorem gapsw80_t45_analyticOrderAt_E1_eq_one {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt (fun s => (1 - s / z) * Complex.exp (s / z)) z = 1 := by
  have _em := Classical.em
  have hAn : AnalyticAt ℂ (fun s => (1 - s / z) * Complex.exp (s / z)) z :=
    Differentiable.analyticAt (by fun_prop) z
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, hAn.analyticOrderAt_eq_natCast]
  refine ⟨fun s => -(z⁻¹) * Complex.exp (s / z), ?_, ?_, ?_⟩
  · exact Differentiable.analyticAt (by fun_prop) z
  · exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hz)) (Complex.exp_ne_zero _)
  · filter_upwards with s
    simp only [pow_one, smul_eq_mul]; field_simp; ring

set_option maxHeartbeats 9600000 in

theorem gapsw80_t45_analyticOrderAt_head {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    {z : ℂ} {S : Finset ℕ} (hS : ∀ j ∈ S, ρ j = z) :
    analyticOrderAt (fun s => ∏ j ∈ S, ((1 - s / ρ j) * Complex.exp (s / ρ j))) z
      = (S.card : ℕ∞) := by
  have _em := Classical.em
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero]
      exact (analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero
  | insert a T haT IH =>
      have hSa : ρ a = z := hS a (Finset.mem_insert_self a T)
      have hz : z ≠ 0 := hSa ▸ hρ0 a
      have hST : ∀ j ∈ T, ρ j = z := fun j hj => hS j (Finset.mem_insert_of_mem hj)
      have heq : (fun s => ∏ j ∈ insert a T,
            ((1 - s / ρ j) * Complex.exp (s / ρ j)))
          = (fun s => (1 - s / z) * Complex.exp (s / z))
            * (fun s => ∏ j ∈ T, ((1 - s / ρ j) * Complex.exp (s / ρ j))) := by
        funext s; simp only [Pi.mul_apply, Finset.prod_insert haT, hSa]
      rw [heq, analyticOrderAt_mul
          (Differentiable.analyticAt (by fun_prop) z)
          (Differentiable.analyticAt (by fun_prop) z),
        gapsw80_t45_analyticOrderAt_E1_eq_one hz, IH hST,
        Finset.card_insert_of_notMem haT]
      push_cast; ring

set_option maxHeartbeats 9600000 in

theorem gapsw80_t45_D1b0a1b_closed : gapsw80_t44_CanonicalProductEntireOrder := by
  have _em := Classical.em
  intro ρ hρ0 hsum
  set F : ℕ → ℂ → ℂ := fun j s => (1 - s / ρ j) * Complex.exp (s / ρ j) with hF
  refine ⟨gapsw80_t45_tprod_E1_differentiable hρ0 hsum, ?_⟩
  intro z

  have hfin : {j | ρ j = z}.Finite := gapsw80_t45_fiber_finite hρ0 hsum z
  set S : Finset ℕ := hfin.toFinset with hSdef
  have hSmem : ∀ j, j ∈ S ↔ ρ j = z := fun j => by
    rw [hSdef]; exact hfin.mem_toFinset

  have hmulc : ∀ s, Multipliable
      (fun j : ↥((↑S : Set ℕ)ᶜ) => F (↑j) s) := fun s => by
    have h := multipliable_one_add_of_summable
      (f := fun j : ↥((↑S : Set ℕ)ᶜ) => F (↑j) s - 1)
      ((gapsw80_t45_summable_norm_E1_sub_one hρ0 hsum s).subtype _)
    simpa using h

  have hsplit : (fun s => ∏' j, F j s)
      = (fun s => ∏ j ∈ S, F j s)
        * (fun s => ∏' j : ↥((↑S : Set ℕ)ᶜ), F (↑j) s) := by
    funext s; simp only [Pi.mul_apply]
    rw [← S.tprod_subtype (fun j => F j s)]
    exact ((S.multipliable (fun j => F j s)).tprod_mul_tprod_compl (hmulc s)).symm

  have hρ0' : ∀ j : ↥((↑S : Set ℕ)ᶜ), ρ (↑j) ≠ 0 := fun j => hρ0 _
  have hsum' : Summable fun j : ↥((↑S : Set ℕ)ᶜ) =>
      (Complex.normSq (ρ (↑j)))⁻¹ := hsum.subtype _
  have hz' : ∀ j : ↥((↑S : Set ℕ)ᶜ), ρ (↑j) ≠ z := fun j h =>
    j.2 (Finset.mem_coe.mpr ((hSmem _).mpr h))

  have hTdiff : Differentiable ℂ
      (fun s => ∏' j : ↥((↑S : Set ℕ)ᶜ), F (↑j) s) := by
    simp only [hF]
    exact gapsw80_t45_tprod_E1_differentiable hρ0' hsum'
  have hTz : (∏' j : ↥((↑S : Set ℕ)ᶜ), F (↑j) z) ≠ 0 := by
    simp only [hF]
    exact gapsw80_t45_tprod_E1_ne_zero hρ0' hsum' hz'
  have hTord : analyticOrderAt
      (fun s => ∏' j : ↥((↑S : Set ℕ)ᶜ), F (↑j) s) z = 0 :=
    (hTdiff.analyticAt z).analyticOrderAt_eq_zero.mpr hTz

  have hHord : analyticOrderAt (fun s => ∏ j ∈ S, F j s) z = (S.card : ℕ∞) := by
    simp only [hF]
    exact gapsw80_t45_analyticOrderAt_head hρ0 (fun j hj => (hSmem j).mp hj)

  have hHan : AnalyticAt ℂ (fun s => ∏ j ∈ S, F j s) z := by
    refine Differentiable.analyticAt ?_ z
    simp only [hF]; fun_prop

  have hPord : analyticOrderAt (fun s => ∏' j, F j s) z = (S.card : ℕ∞) := by
    rw [hsplit, analyticOrderAt_mul hHan (hTdiff.analyticAt z), hHord, hTord,
      add_zero]

  show analyticOrderNatAt (fun s => ∏' j, F j s) z = Nat.card {j | ρ j = z}
  unfold analyticOrderNatAt
  rw [hPord, Nat.card_eq_card_finite_toFinset hfin, ← hSdef]
  rfl

end FLT.Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T46D1b0a1cEntireQuotientOfOrderMatchProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
open FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
open FLT.Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
open FLT.Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t46_meromorphicOrderAt_eq_intCast {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) (z : ℂ) :
    meromorphicOrderAt f z = ((analyticOrderNatAt f z : ℤ) : WithTop ℤ) := by
  have hnt : analyticOrderAt f z ≠ ⊤ := fun h =>
    gapsw80_t42_not_locally_zero hf hz₀ z (analyticOrderAt_eq_top.mp h)
  rw [(hf.analyticAt z).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hnt, ENat.map_coe]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t46_meromorphicOrderAt_quotient_eq_zero {f P : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hP : Differentiable ℂ P) (hP0 : P 0 ≠ 0)
    (hord : ∀ z, analyticOrderNatAt f z = analyticOrderNatAt P z) (z : ℂ) :
    meromorphicOrderAt (f / P) z = 0 := by
  rw [meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hP.analyticAt z).meromorphicAt,
    gapsw80_t46_meromorphicOrderAt_eq_intCast hf hf0 z,
    gapsw80_t46_meromorphicOrderAt_eq_intCast hP hP0 z, hord z]
  simp

set_option maxHeartbeats 3200000 in

theorem gapsw80_t46_analyticOrderNatAt_ne_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) {s : ℂ} (hfs : f s = 0) :
    analyticOrderNatAt f s ≠ 0 := by
  have hnt : analyticOrderAt f s ≠ ⊤ := fun h =>
    gapsw80_t42_not_locally_zero hf hz₀ s (analyticOrderAt_eq_top.mp h)
  intro h0
  have : analyticOrderAt f s = 0 := by
    rw [← Nat.cast_analyticOrderNatAt hnt, h0]; rfl
  exact ((hf.analyticAt s).analyticOrderAt_eq_zero.mp this) hfs

set_option maxHeartbeats 9600000 in

theorem gapsw80_t46_D1b0a1c_closed : gapsw80_t44_EntireQuotientOfOrderMatch := by
  intro f P hf hf0 hP hP0 hord
  have hMer : MeromorphicOn (f / P) univ :=
    fun z _ => (hf.analyticAt z).meromorphicAt.div (hP.analyticAt z).meromorphicAt
  set g := toMeromorphicNFOn (f / P) univ with hg_def
  have hgNF : MeromorphicNFOn g univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hgord : ∀ z, meromorphicOrderAt g z = 0 := fun z =>
    (meromorphicOrderAt_toMeromorphicNFOn hMer (mem_univ z)).trans
      (gapsw80_t46_meromorphicOrderAt_quotient_eq_zero hf hf0 hP hP0 hord z)
  refine ⟨g, fun z => ?_, fun s => ?_, fun s => ?_⟩
  ·
    exact ((hgNF (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (hgord z).ge).differentiableAt
  ·
    exact (hgNF (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mp (hgord s)
  ·
    rcases eq_or_ne (P s) 0 with hPs | hPs
    ·

      have hfs : f s = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero
        (hord s ▸ gapsw80_t46_analyticOrderNatAt_ne_zero hP hP0 hPs)
      rw [hfs, hPs, mul_zero]
    ·
      have hAn : AnalyticAt ℂ (f / P) s := (hf.analyticAt s).div (hP.analyticAt s) hPs
      rw [hg_def, toMeromorphicNFOn_eq_toMeromorphicNFAt hMer (mem_univ s),
        congrFun (toMeromorphicNFAt_eq_self.2 hAn.meromorphicNFAt) s]
      exact (div_mul_cancel₀ (f s) hPs).symm

end FLT.Gapsw80T46D1b0a1cEntireQuotientOfOrderMatchProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T47D1b0a1aZeroEnumSummableSubDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
open FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
open FLT.Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
open FLT.Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof
open FLT.Gapsw80T46D1b0a1cEntireQuotientOfOrderMatchProof
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

def gapsw80_t47_ZeroEnumWithMult : Prop :=
  ∀ f : ℂ → ℂ,
    Differentiable ℂ f →
    f 0 ≠ 0 →
    Set.Infinite {s | f s = 0} →
    ∃ ρ : ℕ → ℂ,
      (∀ j, f (ρ j) = 0) ∧
      (∀ z, Nat.card {j | ρ j = z} = analyticOrderNatAt f z)

def gapsw80_t47_EnumNormSqSummable : Prop :=
  ∀ f : ℂ → ℂ,
    Differentiable ℂ f →
    f 0 ≠ 0 →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    ∀ ρ : ℕ → ℂ,
      (∀ j, f (ρ j) = 0) →
      (∀ z, Nat.card {j | ρ j = z} = analyticOrderNatAt f z) →
      Summable (fun j => (Complex.normSq (ρ j))⁻¹)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t47_D1b0a1a_of_i_ii
    (hi : gapsw80_t47_ZeroEnumWithMult)
    (hii : gapsw80_t47_EnumNormSqSummable) :
    gapsw80_t44_ZeroEnumWithMultSummable := by
  have _em := Classical.em
  intro f hdiff hf0 hinf hord
  obtain ⟨ρ, hzero, hcount⟩ := hi f hdiff hf0 hinf
  exact ⟨ρ, hzero, hii f hdiff hf0 hord ρ hzero hcount, hcount⟩

end FLT.Gapsw80T47D1b0a1aZeroEnumSummableSubDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T51D1b0a2bNonvanishSubTwoExpLinearProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 9600000 in

theorem gapsw80_t51_iteratedDeriv_two_eq_zero_of_re_sqrt_growth {h : ℂ → ℂ}
    (hhdiff : Differentiable ℂ h) (hh0 : h 0 = 0)
    (hord : ∃ C D : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      (h s).re ≤ C * ‖s‖ * Real.sqrt ‖s‖ + D) :
    ∀ c, iteratedDeriv 2 h c = 0 := by
  have _em := Classical.em
  obtain ⟨C, D, hord'⟩ := hord
  set C₁ := max C 0 with hC₁def
  have hC₁nn : 0 ≤ C₁ := le_max_right _ _
  have hC₁C : C ≤ C₁ := le_max_left _ _

  obtain ⟨x₀, _, hx₀⟩ := (isCompact_closedBall (0:ℂ) 2).exists_isMaxOn
    ⟨0, by simp⟩ (continuous_re.comp hhdiff.continuous).continuousOn
  set C₀ := (h x₀).re
  set D₂ := |C₀| + |D| + 1 with hD₂def
  have hD₂pos : 0 < D₂ := by positivity
  set M : ℝ → ℝ := fun R => C₁ * R * Real.sqrt R + D₂ with hMdef

  have hMapsTo : ∀ R : ℝ, 3 ≤ R → ∀ z ∈ ball (0:ℂ) R, (h z).re ≤ M R := by
    intro R hR z hz
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
    rcases le_or_gt ‖z‖ 2 with hle | hgt
    · have : (h z).re ≤ C₀ := hx₀ (mem_closedBall_zero_iff.mpr hle)
      calc (h z).re ≤ C₀ := this
        _ ≤ |C₀| := le_abs_self _
        _ ≤ D₂ := by simp only [hD₂def]; linarith [abs_nonneg D]
        _ ≤ M R := by
            simp only [hMdef]
            have hsqrt : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
            nlinarith [mul_nonneg (mul_nonneg hC₁nn
              (by linarith : (0:ℝ) ≤ R)) hsqrt]
    · have h2z : (2:ℝ) ≤ ‖z‖ := le_of_lt hgt
      have hsqrtz : 0 ≤ Real.sqrt ‖z‖ := Real.sqrt_nonneg _
      have hzl : (0:ℝ) ≤ ‖z‖ * Real.sqrt ‖z‖ :=
        mul_nonneg (by linarith) hsqrtz
      have hzsqrtz : ‖z‖ * Real.sqrt ‖z‖ ≤ R * Real.sqrt R := by
        apply mul_le_mul hzR.le (Real.sqrt_le_sqrt hzR.le)
          hsqrtz (by linarith)
      calc (h z).re ≤ C * ‖z‖ * Real.sqrt ‖z‖ + D := hord' z h2z
        _ ≤ M R := by
            simp only [hMdef]
            nlinarith [mul_nonneg (sub_nonneg.mpr hC₁C) hzl,
              mul_nonneg hC₁nn (sub_nonneg.mpr hzsqrtz),
              le_abs_self D, abs_nonneg C₀]
  have hMpos : ∀ R : ℝ, 3 ≤ R → 0 < M R := by
    intro R hR
    simp only [hMdef]
    have hsqrt : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
    nlinarith [mul_nonneg (mul_nonneg hC₁nn
      (by linarith : (0:ℝ) ≤ R)) hsqrt]

  have hBC : ∀ R : ℝ, 3 ≤ R → ∀ z ∈ ball (0:ℂ) R,
      ‖h z‖ ≤ 2 * M R * ‖z‖ / (R - ‖z‖) := by
    intro R hR z hz
    exact borelCaratheodory_zero (hMpos R hR) hhdiff.differentiableOn
      (fun w hw => hMapsTo R hR w hw) (by linarith) hz hh0

  have hsphere : ∀ c : ℂ, ∀ r : ℝ, 2 ≤ r → ∀ z ∈ sphere c r,
      ‖h z‖ ≤ 2 * M (2 * (‖c‖ + r)) := by
    intro c r hr z hz
    set R := 2 * (‖c‖ + r) with hRdef
    have hRge : (3:ℝ) ≤ R := by
      simp only [hRdef]; nlinarith [norm_nonneg c]
    have hMRpos : 0 < M R := hMpos R hRge
    have hzle : ‖z‖ ≤ ‖c‖ + r := by
      have hzc := mem_sphere_iff_norm.mp hz
      calc ‖z‖ = ‖z - c + c‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = r + ‖c‖ := by rw [hzc]
        _ = ‖c‖ + r := by ring
    have hz2 : 2 * ‖z‖ ≤ R := by simp only [hRdef]; linarith
    have hzlt : ‖z‖ < R := by nlinarith [norm_nonneg z]
    have hzmem : z ∈ ball (0:ℂ) R := mem_ball_zero_iff.mpr hzlt
    have hfrac : ‖z‖ / (R - ‖z‖) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    calc ‖h z‖ ≤ 2 * M R * ‖z‖ / (R - ‖z‖) := hBC R hRge z hzmem
      _ = 2 * M R * (‖z‖ / (R - ‖z‖)) := by ring
      _ ≤ 2 * M R * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 2 * M R := by ring

  have hCauchy : ∀ c : ℂ, ∀ r : ℝ, 2 ≤ r →
      ‖iteratedDeriv 2 h c‖ ≤ 4 * M (2 * (‖c‖ + r)) / r ^ 2 := by
    intro c r hr
    have hest := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
      (by linarith : (0:ℝ) < r) hhdiff.diffContOnCl (hsphere c r hr)
    calc ‖iteratedDeriv 2 h c‖
        ≤ ↑(Nat.factorial 2) * (2 * M (2 * (‖c‖ + r))) / r ^ 2 := hest
      _ = 4 * M (2 * (‖c‖ + r)) / r ^ 2 := by
          rw [Nat.factorial_two]; push_cast; ring

  intro c
  have hub : ∀ r : ℝ, max ‖c‖ 2 ≤ r →
      ‖iteratedDeriv 2 h c‖
        ≤ 16 * C₁ * Real.sqrt (4 * r) / r + 4 * D₂ / r ^ 2 := by
    intro r hr
    have hr2 : (2:ℝ) ≤ r := (le_max_right _ _).trans hr
    have hrc : ‖c‖ ≤ r := (le_max_left _ _).trans hr
    have hrpos : (0:ℝ) < r := by linarith
    have h4rpos : (0:ℝ) < 4 * r := by linarith
    have hsqrt4r : 0 ≤ Real.sqrt (4 * r) := Real.sqrt_nonneg _
    have hMub : M (2 * (‖c‖ + r))
        ≤ C₁ * (4 * r) * Real.sqrt (4 * r) + D₂ := by
      simp only [hMdef]
      have harg : 2 * (‖c‖ + r) ≤ 4 * r := by linarith
      have hargpos : (0:ℝ) < 2 * (‖c‖ + r) := by nlinarith [norm_nonneg c]
      have hsqrtle : Real.sqrt (2 * (‖c‖ + r)) ≤ Real.sqrt (4 * r) :=
        Real.sqrt_le_sqrt harg
      have hsqrtpos : 0 ≤ Real.sqrt (2 * (‖c‖ + r)) := Real.sqrt_nonneg _
      nlinarith [mul_le_mul harg hsqrtle hsqrtpos (by linarith),
        mul_nonneg hC₁nn
          (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * r) hsqrt4r)]
    calc ‖iteratedDeriv 2 h c‖
        ≤ 4 * M (2 * (‖c‖ + r)) / r ^ 2 := hCauchy c r hr2
      _ ≤ 4 * (C₁ * (4 * r) * Real.sqrt (4 * r) + D₂) / r ^ 2 := by
          gcongr
      _ = 16 * C₁ * Real.sqrt (4 * r) / r + 4 * D₂ / r ^ 2 := by
          field_simp; ring
  have hlim : Tendsto
      (fun r : ℝ => 16 * C₁ * Real.sqrt (4 * r) / r + 4 * D₂ / r ^ 2)
      atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun r : ℝ => Real.sqrt (4 * r) / r)
        atTop (𝓝 0) := by
      have hbase : Tendsto (fun r : ℝ => Real.sqrt r / r) atTop (𝓝 0) :=
        (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).congr
          fun r => Real.sqrt_div_self.symm
      have h4r : Tendsto (fun r : ℝ => 4 * r) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) tendsto_id
      have hcomp := (hbase.comp h4r).const_mul 4
      simp only [Function.comp_def, mul_zero] at hcomp
      refine hcomp.congr' (eventually_atTop.mpr ⟨1, fun r hr => ?_⟩)
      have h4rpos : (0:ℝ) < 4 * r := by linarith
      field_simp
    have h1 : Tendsto (fun r : ℝ => 16 * C₁ * Real.sqrt (4 * r) / r)
        atTop (𝓝 0) := by
      have := hsqrt.const_mul (16 * C₁)
      simpa [mul_div_assoc] using this
    have h2 : Tendsto (fun r : ℝ => 4 * D₂ / r ^ 2) atTop (𝓝 0) := by
      have hpow : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
        tendsto_pow_atTop two_ne_zero
      have := hpow.inv_tendsto_atTop.const_mul (4 * D₂)
      simpa [div_eq_mul_inv] using this
    have := h1.add h2
    simpa using this
  have hle0 : ‖iteratedDeriv 2 h c‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.mpr ⟨max ‖c‖ 2, hub⟩)
  exact norm_le_zero_iff.mp hle0

set_option maxHeartbeats 9600000 in

theorem gapsw80_t51_D1b0a2b_closed :
    gapsw80_t50_NonvanishOrderSubTwoExpLinear := by
  have _em := Classical.em
  intro g hgdiff hgne hord
  obtain ⟨C, hord'⟩ := hord

  obtain ⟨h, hh0, hhd⟩ := gapsw80_t40_logDeriv_primitive hgdiff hgne
  have hhdiff : Differentiable ℂ h := fun s => (hhd s).differentiableAt

  have hgexp := gapsw80_t40_eq_const_mul_exp hgdiff hgne hh0 hhd

  have hg0ne : g 0 ≠ 0 := hgne 0
  have hReH : ∀ s, (h s).re = Real.log ‖g s‖ - Real.log ‖g 0‖ := by
    intro s
    have hnorm : ‖g s‖ = ‖g 0‖ * Real.exp (h s).re := by
      rw [hgexp s, norm_mul, Complex.norm_exp]
    have hg0pos : (0:ℝ) < ‖g 0‖ := norm_pos_iff.mpr hg0ne
    rw [hnorm, Real.log_mul hg0pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

  have hh2 : ∀ c, iteratedDeriv 2 h c = 0 := by
    apply gapsw80_t51_iteratedDeriv_two_eq_zero_of_re_sqrt_growth hhdiff hh0
    refine ⟨C, -Real.log ‖g 0‖, fun s hs => ?_⟩
    rw [hReH s]
    linarith [hord' s hs]

  have hlin : ∀ s, h s = deriv h 0 * s := by
    intro s
    have := gapsw80_t40_linear_of_iteratedDeriv_two_eq_zero hhdiff hh2 s
    simpa [hh0] using this

  refine ⟨Complex.log (g 0), deriv h 0, fun s => ?_⟩
  rw [Complex.exp_add, Complex.exp_log hg0ne, ← hlin s, ← hgexp s]

end FLT.Gapsw80T51D1b0a2bNonvanishSubTwoExpLinearProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T52D1b0a2aBoasMinModulusSubDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

def gapsw80_t52_CanonicalProductAnnulusMinModulus : Prop :=
  ∀ (f g : ℂ → ℂ) (ρ : ℕ → ℂ),
    Differentiable ℂ f →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    Differentiable ℂ g →
    (∀ s : ℂ, g s ≠ 0) →
    (∀ s : ℂ, f s = g s
        * ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) →
    (∃ C : ℝ, ∀ R : ℝ, 2 ≤ R → ∃ r ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = r →
      Real.exp (-(C * r * Real.sqrt r))
        ≤ ‖∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))‖)

def gapsw80_t52_EntireGrowthFromAnnulusCircles : Prop :=
  ∀ (g : ℂ → ℂ),
    Differentiable ℂ g →
    (∃ C : ℝ, ∀ R : ℝ, 2 ≤ R → ∃ r ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = r →
      Real.log ‖g s‖ ≤ C * r * Real.sqrt r) →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖g s‖ ≤ C * ‖s‖ * Real.sqrt ‖s‖)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t52_D1b0a2a_of_D1b0a2ai_ii
    (hi : gapsw80_t52_CanonicalProductAnnulusMinModulus)
    (hii : gapsw80_t52_EntireGrowthFromAnnulusCircles) :
    gapsw80_t50_QuotientLogSubTwoGrowth := by
  have _em := Classical.em
  intro f g ρ hfdiff hford hsum hgdiff hgne hfact
  apply hii g hgdiff
  obtain ⟨C₁, hmin⟩ := hi f g ρ hfdiff hford hsum hgdiff hgne hfact
  obtain ⟨C₀, hf⟩ := hford
  refine ⟨2 * |C₀| + C₁, fun R hR => ?_⟩
  obtain ⟨r, hrR, hPlow⟩ := hmin R hR
  refine ⟨r, hrR, fun s hsr => ?_⟩
  have hr2 : (2:ℝ) ≤ r := le_trans hR hrR.1
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le two_pos hr2
  have hs2 : (2:ℝ) ≤ ‖s‖ := hsr ▸ hr2
  have hsqr0 : (0:ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hPpos : (0:ℝ) < ‖∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))‖ :=
    (Real.exp_pos _).trans_le (hPlow s hsr)
  have hgpos : (0:ℝ) < ‖g s‖ := norm_pos_iff.mpr (hgne s)
  have hlog_eq : Real.log ‖g s‖
      = Real.log ‖f s‖
        - Real.log ‖∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))‖ := by
    have hnorm : ‖f s‖
        = ‖g s‖ * ‖∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))‖ := by
      rw [hfact s, norm_mul]
    rw [hnorm, Real.log_mul hgpos.ne' hPpos.ne']; ring
  have hlogP : -(C₁ * r * Real.sqrt r)
      ≤ Real.log ‖∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))‖ := by
    have h := Real.log_le_log (Real.exp_pos _) (hPlow s hsr)
    rwa [Real.log_exp] at h
  have hlogf : Real.log ‖f s‖ ≤ C₀ * r * Real.log r := by
    have h := hf s hs2; rwa [hsr] at h
  have hlogr0 : (0:ℝ) < Real.log r :=
    Real.log_pos (lt_of_lt_of_le one_lt_two hr2)
  have hlog_sqrt : Real.log r ≤ 2 * Real.sqrt r := by
    have h1 : Real.log (Real.sqrt r) ≤ Real.sqrt r - 1 :=
      Real.log_le_sub_one_of_pos hsqr0
    have h2 : Real.log r = 2 * Real.log (Real.sqrt r) := by
      rw [Real.log_sqrt hr0.le]; ring
    linarith
  have hstep : C₀ * r * Real.log r ≤ 2 * |C₀| * r * Real.sqrt r := by
    have h12 : C₀ * Real.log r ≤ |C₀| * (2 * Real.sqrt r) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hlogr0.le).trans
        (mul_le_mul_of_nonneg_left hlog_sqrt (abs_nonneg _))
    nlinarith [mul_le_mul_of_nonneg_left h12 hr0.le]
  have hdist : (2 * |C₀| + C₁) * r * Real.sqrt r
      = 2 * |C₀| * r * Real.sqrt r + C₁ * r * Real.sqrt r := by ring
  linarith [hlog_eq, hlogP, hlogf, hstep, hdist]

end FLT.Gapsw80T52D1b0a2aBoasMinModulusSubDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T48D1b0a1aiZeroEnumWithMultProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
open FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
open FLT.Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
open FLT.Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof
open FLT.Gapsw80T46D1b0a1cEntireQuotientOfOrderMatchProof
open FLT.Gapsw80T47D1b0a1aZeroEnumSummableSubDecomp
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t48_zeroSet_inter_closedBall_finite {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) (n : ℕ) :
    ({s | f s = 0} ∩ closedBall 0 n).Finite := by
  by_contra h
  obtain ⟨w, -, hAcc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact h (isCompact_closedBall 0 n)
      Set.inter_subset_right
  have hfreq : ∃ᶠ y in 𝓝[≠] w, f y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hAcc).mono fun _ hy => hy.1
  have hAn : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  exact hz₀ <| hAn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (mem_univ w) hfreq (mem_univ z₀)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t48_zeroSet_countable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) :
    {s | f s = 0}.Countable := by
  have hcover : {s | f s = 0} ⊆ ⋃ n : ℕ, ({s | f s = 0} ∩ closedBall 0 n) :=
    fun s hs => Set.mem_iUnion.mpr
      ⟨⌈‖s‖⌉₊, hs, mem_closedBall_zero_iff.mpr (Nat.le_ceil _)⟩
  exact Set.Countable.mono hcover <| Set.countable_iUnion fun n =>
    (gapsw80_t48_zeroSet_inter_closedBall_finite hf hz₀ n).countable

set_option maxHeartbeats 3200000 in

theorem gapsw80_t48_card_sigma_fiber {ι : Type*} {β : ι → Type*} (i₀ : ι) :
    Nat.card {p : Σ i, β i // p.1 = i₀} = Nat.card (β i₀) :=
  Nat.card_congr
    { toFun := fun p => p.2 ▸ p.1.2
      invFun := fun b => ⟨⟨i₀, b⟩, rfl⟩
      left_inv := by rintro ⟨⟨i, b⟩, rfl⟩; rfl
      right_inv := fun _ => rfl }

set_option maxHeartbeats 9600000 in

theorem gapsw80_t48_D1b0a1ai_closed : gapsw80_t47_ZeroEnumWithMult := by
  intro f hdiff hf0 hinf
  haveI : Countable {s : ℂ // f s = 0} :=
    (gapsw80_t48_zeroSet_countable hdiff hf0).to_subtype
  haveI : Infinite {s : ℂ // f s = 0} := hinf.to_subtype
  have hm : ∀ z : {s : ℂ // f s = 0}, 0 < analyticOrderNatAt f z := fun z =>
    Nat.pos_of_ne_zero (gapsw80_t46_analyticOrderNatAt_ne_zero hdiff hf0 z.2)
  let SigT := Σ z : {s : ℂ // f s = 0}, Fin (analyticOrderNatAt f (z : ℂ))
  haveI : Countable SigT := inferInstance
  haveI : Infinite SigT :=
    Infinite.of_injective (fun z => (⟨z, ⟨0, hm z⟩⟩ : SigT))
      fun _ _ h => congrArg Sigma.fst h
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := SigT)
  refine ⟨fun j => (e j).1.1, fun j => (e j).1.2, fun z => ?_⟩
  by_cases hz : f z = 0
  ·
    calc Nat.card {j | (e j).1.1 = z}
        = Nat.card {p : SigT // p.1.1 = z} :=
          Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
      _ = Nat.card {p : SigT // p.1 = ⟨z, hz⟩} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
            ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
      _ = Nat.card (Fin (analyticOrderNatAt f z)) :=
          gapsw80_t48_card_sigma_fiber (⟨z, hz⟩ : {s : ℂ // f s = 0})
      _ = analyticOrderNatAt f z := Nat.card_fin _
  ·
    have hord0 : analyticOrderNatAt f z = 0 := by
      unfold analyticOrderNatAt
      rw [(hdiff.analyticAt z).analyticOrderAt_eq_zero.mpr hz]; rfl
    rw [hord0, Nat.card_eq_zero]
    exact Or.inl <| Set.isEmpty_coe_sort.mpr <|
      Set.eq_empty_iff_forall_notMem.mpr fun j hj => hz (hj ▸ (e j).1.2)

end FLT.Gapsw80T48D1b0a1aiZeroEnumWithMultProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T53D1b0a2aiiAnnulusToGlobalGrowthProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t53_entireGrowthFromAnnulusCircles :
    gapsw80_t52_EntireGrowthFromAnnulusCircles := by
  have _em := Classical.em
  intro g hgdiff hC
  obtain ⟨C, hcirc⟩ := hC
  refine ⟨2 * Real.sqrt 2 * |C|, fun s hs => ?_⟩
  obtain ⟨r, hrR, hbd⟩ := hcirc ‖s‖ hs
  have hs0 : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hr2 : (2:ℝ) ≤ r := le_trans hs hrR.1
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le two_pos hr2
  have hrsr0 : (0:ℝ) ≤ r * Real.sqrt r := mul_nonneg hr0.le (Real.sqrt_nonneg r)
  have hM0 : (0:ℝ) ≤ |C| * r * Real.sqrt r :=
    mul_nonneg (mul_nonneg (abs_nonneg C) hr0.le) (Real.sqrt_nonneg r)

  have habsC : ∀ z : ℂ, ‖z‖ = r → ‖g z‖ ≤ Real.exp (|C| * r * Real.sqrt r) := by
    intro z hzr
    refine Real.le_exp_of_log_le ((hbd z hzr).trans ?_)
    have hCabs : C * (r * Real.sqrt r) ≤ |C| * (r * Real.sqrt r) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hrsr0
    linarith [mul_assoc C r (Real.sqrt r), mul_assoc |C| r (Real.sqrt r), hCabs]

  have hAbs : ‖g s‖ ≤ Real.exp (|C| * r * Real.sqrt r) := by
    have hfront : ∀ z ∈ frontier (ball (0:ℂ) r),
        ‖g z‖ ≤ Real.exp (|C| * r * Real.sqrt r) := by
      intro z hz
      rw [frontier_ball 0 hr0.ne'] at hz
      exact habsC z (mem_sphere_zero_iff_norm.mp hz)
    have hcl : s ∈ closure (ball (0:ℂ) r) := by
      rw [closure_ball 0 hr0.ne']
      exact mem_closedBall_zero_iff.mpr hrR.1
    exact Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hgdiff.diffContOnCl hfront hcl

  have hlog : Real.log ‖g s‖ ≤ |C| * r * Real.sqrt r := by
    rcases (norm_nonneg (g s)).eq_or_lt with h | h
    · rw [← h, Real.log_zero]; exact hM0
    · calc Real.log ‖g s‖
          ≤ Real.log (Real.exp (|C| * r * Real.sqrt r)) := Real.log_le_log h hAbs
        _ = |C| * r * Real.sqrt r := Real.log_exp _

  have hrsr : r * Real.sqrt r ≤ 2 * Real.sqrt 2 * ‖s‖ * Real.sqrt ‖s‖ := by
    have h1 : r * Real.sqrt r ≤ (2 * ‖s‖) * Real.sqrt (2 * ‖s‖) :=
      mul_le_mul hrR.2 (Real.sqrt_le_sqrt hrR.2) (Real.sqrt_nonneg _) (by linarith)
    have h2 : Real.sqrt (2 * ‖s‖) = Real.sqrt 2 * Real.sqrt ‖s‖ :=
      Real.sqrt_mul (by norm_num) ‖s‖
    calc r * Real.sqrt r ≤ (2 * ‖s‖) * Real.sqrt (2 * ‖s‖) := h1
      _ = 2 * Real.sqrt 2 * ‖s‖ * Real.sqrt ‖s‖ := by rw [h2]; ring

  have hfin : |C| * r * Real.sqrt r
      ≤ 2 * Real.sqrt 2 * |C| * ‖s‖ * Real.sqrt ‖s‖ := by
    have h := mul_le_mul_of_nonneg_left hrsr (abs_nonneg C)
    nlinarith [h]
  linarith [hlog, hfin]

end FLT.Gapsw80T53D1b0a2aiiAnnulusToGlobalGrowthProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T54D1b0a2aiZeroCountBoasCoreSubDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

def gapsw80_t54_ZeroCountJensenBound : Prop :=
  ∀ (f g : ℂ → ℂ) (ρ : ℕ → ℂ),
    Differentiable ℂ f →
    (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) →
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    Differentiable ℂ g →
    (∀ s : ℂ, g s ≠ 0) →
    (∀ s : ℂ, f s = g s
        * ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))) →
    (∃ A : ℝ, ∀ r : ℝ, 2 ≤ r →
      (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ A * (r * Real.log (2 * r) + 1))

def gapsw80_t54_MinModulusOfCountAndSummable : Prop :=
  ∀ (ρ : ℕ → ℂ),
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    (∃ A : ℝ, ∀ r : ℝ, 2 ≤ r →
      (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ A * (r * Real.log (2 * r) + 1)) →
    (∃ C : ℝ, ∀ R : ℝ, 2 ≤ R → ∃ r ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = r →
      Real.exp (-(C * r * Real.sqrt r))
        ≤ ‖∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))‖)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t54_D1b0a2ai_of_D1b0a2aiA_iB
    (hiA : gapsw80_t54_ZeroCountJensenBound)
    (hiB : gapsw80_t54_MinModulusOfCountAndSummable) :
    gapsw80_t52_CanonicalProductAnnulusMinModulus := by
  have _em := Classical.em
  intro f g ρ hfdiff hford hsum hgdiff hgne hfact
  exact hiB ρ hsum (hiA f g ρ hfdiff hford hsum hgdiff hgne hfact)

end FLT.Gapsw80T54D1b0a2aiZeroCountBoasCoreSubDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T49D1b0a1aiiEnumNormSqSummableProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T37D1bGenericHadamardDecomp
open FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof
open FLT.Gapsw80T39D1b0HadamardQuotientDecomp
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
open FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
open FLT.Gapsw80T44D1b0a1HadamardSansOrderSubDecomp
open FLT.Gapsw80T45D1b0a1bCanonicalProductEntireOrderProof
open FLT.Gapsw80T46D1b0a1cEntireQuotientOfOrderMatchProof
open FLT.Gapsw80T47D1b0a1aZeroEnumSummableSubDecomp
open FLT.Gapsw80T48D1b0a1aiZeroEnumWithMultProof
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t49_divisor_eq_ordNat {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} {z : ℂ} (hz : z ∈ closedBall (0:ℂ) r) :
    MeromorphicOn.divisor f (closedBall 0 r) z = (analyticOrderNatAt f z : ℤ) := by
  have hAn : AnalyticOnNhd ℂ f (closedBall 0 r) :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  rw [hAn.meromorphicOn.divisor_apply hz, (hAn z hz).meromorphicOrderAt_eq]
  unfold analyticOrderNatAt
  cases h : analyticOrderAt f z with
  | top => simp
  | coe n => simp

set_option maxHeartbeats 3200000 in

theorem gapsw80_t49_enum_ball_finite {f : ℂ → ℂ} (hdiff : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {ρ : ℕ → ℂ} (hzero : ∀ j, f (ρ j) = 0)
    (hcount : ∀ z, Nat.card {j | ρ j = z} = analyticOrderNatAt f z) (r : ℝ) :
    {j | ‖ρ j‖ ≤ r}.Finite := by
  have hZr : ({s | f s = 0} ∩ closedBall 0 ⌈r⌉₊).Finite :=
    gapsw80_t48_zeroSet_inter_closedBall_finite hdiff hf0 ⌈r⌉₊
  have hfib : ∀ z ∈ ({s | f s = 0} : Set ℂ), {j | ρ j = z}.Finite := fun z hz =>
    Set.finite_coe_iff.mp <| Nat.finite_of_card_ne_zero <| (hcount z).symm ▸
      gapsw80_t46_analyticOrderNatAt_ne_zero hdiff hf0 hz
  refine Set.Finite.subset (hZr.biUnion fun z hz => hfib z hz.1) ?_
  intro j hj
  exact Set.mem_biUnion ⟨hzero j, mem_closedBall_zero_iff.mpr (hj.trans (Nat.le_ceil r))⟩ rfl

set_option maxHeartbeats 6400000 in

theorem gapsw80_t49_enum_ball_card_eq_finsum_divisor {f : ℂ → ℂ}
    (hdiff : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {ρ : ℕ → ℂ}
    (hzero : ∀ j, f (ρ j) = 0)
    (hcount : ∀ z, Nat.card {j | ρ j = z} = analyticOrderNatAt f z) (r : ℝ) :
    (Nat.card {j | ‖ρ j‖ ≤ r} : ℤ) =
      ∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u := by
  classical
  have h0b := gapsw80_t49_enum_ball_finite hdiff hf0 hzero hcount r
  set Zr : Set ℂ := {s | f s = 0} ∩ closedBall 0 r with hZr_def
  have hZr : Zr.Finite := (gapsw80_t48_zeroSet_inter_closedBall_finite hdiff hf0
    ⌈r⌉₊).subset (Set.inter_subset_inter_right _
      (closedBall_subset_closedBall (Nat.le_ceil r)))

  have hfilter : ∀ z ∈ hZr.toFinset,
      (h0b.toFinset.filter (ρ · = z)).card = analyticOrderNatAt f z := by
    intro z hz
    have hzZr := hZr.mem_toFinset.mp hz
    have hfin_fib : {j | ρ j = z}.Finite := Set.finite_coe_iff.mp <|
      Nat.finite_of_card_ne_zero <| (hcount z).symm ▸
        gapsw80_t46_analyticOrderNatAt_ne_zero hdiff hf0 hzZr.1
    have hset : h0b.toFinset.filter (ρ · = z) = hfin_fib.toFinset := by
      ext j
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
        and_iff_right_iff_imp]
      intro hj; rw [hj]; exact mem_closedBall_zero_iff.mp hzZr.2
    rw [hset, ← Set.ncard_eq_toFinset_card _ hfin_fib, ← Nat.card_coe_set_eq,
      hcount z]

  have hsupp : Function.support (MeromorphicOn.divisor f (closedBall 0 r)) ⊆
      ↑hZr.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    have huBall : u ∈ closedBall (0:ℂ) r :=
      (MeromorphicOn.divisor f (closedBall 0 r)).supportWithinDomain hu
    refine hZr.mem_toFinset.mpr ⟨?_, huBall⟩
    by_contra hfu
    refine hu ?_
    rw [gapsw80_t49_divisor_eq_ordNat hdiff huBall]
    unfold analyticOrderNatAt
    rw [(hdiff.analyticAt u).analyticOrderAt_eq_zero.mpr hfu]; rfl

  calc (Nat.card {j | ‖ρ j‖ ≤ r} : ℤ)
      = (h0b.toFinset.card : ℤ) := by
        rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ h0b]
    _ = ∑ z ∈ hZr.toFinset, ((h0b.toFinset.filter (ρ · = z)).card : ℤ) := by
        rw [Finset.card_eq_sum_card_fiberwise (f := ρ) (t := hZr.toFinset)
          (fun j hj => hZr.mem_toFinset.mpr
            ⟨hzero j, mem_closedBall_zero_iff.mpr (h0b.mem_toFinset.mp hj)⟩)]
        push_cast; ring
    _ = ∑ z ∈ hZr.toFinset, (analyticOrderNatAt f z : ℤ) :=
        Finset.sum_congr rfl fun z hz => by rw [hfilter z hz]
    _ = ∑ z ∈ hZr.toFinset, MeromorphicOn.divisor f (closedBall 0 r) z :=
        Finset.sum_congr rfl fun z hz =>
          (gapsw80_t49_divisor_eq_ordNat hdiff (hZr.mem_toFinset.mp hz).2).symm
    _ = ∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u :=
        (finsum_eq_finset_sum_of_support_subset _ hsupp).symm

set_option maxHeartbeats 6400000 in

theorem gapsw80_t49_enum_ball_card_le {f : ℂ → ℂ} (hdiff : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0)
    (hord : ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖)
    {ρ : ℕ → ℂ} (hzero : ∀ j, f (ρ j) = 0)
    (hcount : ∀ z, Nat.card {j | ρ j = z} = analyticOrderNatAt f z) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 1 ≤ r →
      (Nat.card {j | ‖ρ j‖ ≤ r} : ℝ) ≤ A * (r * Real.log (2 * r) + 1) := by
  obtain ⟨C, hC⟩ := hord
  set C₁ := max C 0 with hC₁_def
  have hC₁ : 0 ≤ C₁ := le_max_right C 0
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨(2 * C₁ + |Real.log ‖f 0‖|) / Real.log 2,
    div_nonneg (add_nonneg (mul_nonneg two_pos.le hC₁) (abs_nonneg _)) hlog2.le,
    fun r hr => ?_⟩
  have hr_pos : 0 < r := zero_lt_one.trans_le hr
  have h2r_pos : 0 < 2 * r := mul_pos two_pos hr_pos
  have h2r_ge : (2:ℝ) ≤ 2 * r := by linarith
  have hlog2r : 0 < Real.log (2 * r) :=
    Real.log_pos (by linarith : (1:ℝ) < 2 * r)
  have habs_r : |r| = r := abs_of_pos hr_pos
  have habs_2r : |2 * r| = 2 * r := abs_of_pos h2r_pos
  set M := Real.exp (C₁ * (2 * r) * Real.log (2 * r)) with hM_def
  have hM_one : 1 ≤ M :=
    Real.one_le_exp (mul_nonneg (mul_nonneg hC₁ h2r_pos.le) hlog2r.le)
  have hAn : AnalyticOnNhd ℂ f (closedBall 0 |2 * r|) :=
    (hdiff.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hfbound : ∀ z ∈ sphere (0:ℂ) |2 * r|, ‖f z‖ ≤ M := by
    rw [habs_2r]
    intro z hz
    have hznorm : ‖z‖ = 2 * r := mem_sphere_zero_iff_norm.mp hz
    rcases eq_or_lt_of_le (norm_nonneg (f z)) with hfz | hfz
    · exact hfz ▸ zero_le_one.trans hM_one
    · refine (Real.log_le_iff_le_exp hfz).mp ?_
      have hlog_le : Real.log ‖f z‖ ≤ C * ‖z‖ * Real.log ‖z‖ := hC z (hznorm ▸ h2r_ge)
      calc Real.log ‖f z‖ ≤ C * ‖z‖ * Real.log ‖z‖ := hlog_le
        _ ≤ C₁ * ‖z‖ * Real.log ‖z‖ := by
            have hzpos : 0 ≤ ‖z‖ * Real.log ‖z‖ :=
              mul_nonneg (hznorm ▸ h2r_pos.le) (hznorm ▸ hlog2r.le)
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left C 0) hzpos
        _ = C₁ * (2 * r) * Real.log (2 * r) := by rw [hznorm]

  have hJF := AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := 2 * r) (M := M)
    (by rw [habs_r]; exact hr_pos) (by rw [habs_r, habs_2r]; linarith)
    hM_one hAn hf0 hfbound
  rw [habs_r] at hJF

  have h0c := gapsw80_t49_enum_ball_card_eq_finsum_divisor hdiff hf0 hzero hcount r
  have hf0_pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hRr : (2 * r) / r = 2 := by field_simp
  calc (Nat.card {j | ‖ρ j‖ ≤ r} : ℝ)
      = ((Nat.card {j | ‖ρ j‖ ≤ r} : ℤ) : ℝ) := by push_cast; ring
    _ = ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) := by rw [h0c]
    _ ≤ Real.log (M / ‖f 0‖) / Real.log (2 * r / r) := by exact_mod_cast hJF
    _ = (C₁ * (2 * r) * Real.log (2 * r) - Real.log ‖f 0‖) / Real.log 2 := by
        rw [hRr, Real.log_div (Real.exp_pos _).ne' hf0_pos.ne', Real.log_exp]
    _ ≤ (2 * C₁ + |Real.log ‖f 0‖|) / Real.log 2 * (r * Real.log (2 * r) + 1) := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog2]
        have h1 : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := neg_le_abs _
        have h2 : 0 ≤ r * Real.log (2 * r) := mul_nonneg hr_pos.le hlog2r.le
        nlinarith [abs_nonneg (Real.log ‖f 0‖)]

set_option maxHeartbeats 12800000 in

theorem gapsw80_t49_D1b0a1aii_closed : gapsw80_t47_EnumNormSqSummable := by
  intro f hdiff hf0 hord ρ hzero hcount
  obtain ⟨A, hA0, hA⟩ := gapsw80_t49_enum_ball_card_le hdiff hf0 hord hzero hcount
  have hg0 : 0 ≤ fun j => (normSq (ρ j))⁻¹ :=
    fun j => inv_nonneg.mpr (normSq_nonneg _)
  rw [summable_partition hg0 (s := fun k => {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k})
      (fun j => ⟨_, rfl, fun _ h => h.symm⟩)]

  have hshell_sub : ∀ k, {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k} ⊆ {j | ‖ρ j‖ ≤ 2^(k+1)} := by
    intro k j hj
    have h1 : ⌊‖ρ j‖⌋₊ < 2 ^ (k+1) := hj ▸ Nat.lt_pow_succ_log_self one_lt_two _
    have h2 : (⌊‖ρ j‖⌋₊ : ℝ) + 1 ≤ (2:ℝ)^(k+1) := by
      exact_mod_cast Nat.succ_le_of_lt h1
    exact le_of_lt <| (Nat.lt_floor_add_one _).trans_le h2
  have hshell_fin : ∀ k, {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k}.Finite := fun k =>
    (gapsw80_t49_enum_ball_finite hdiff hf0 hzero hcount (2^(k+1))).subset
      (hshell_sub k)
  refine ⟨fun k => (hshell_fin k).summable (fun j => (normSq (ρ j))⁻¹), ?_⟩

  rw [← summable_nat_add_iff 1]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow24 : ∀ k : ℕ, (2:ℝ)^(k+2) * (1/4:ℝ)^(k+1) = (1/2:ℝ)^k := by
    intro k
    have h1 : (1/4:ℝ)^(k+1) = (1/2:ℝ)^(k+2) * (1/2:ℝ)^k := by
      rw [show (1/4:ℝ) = (1/2)^2 by norm_num, ← pow_mul, ← pow_add]
      congr 1; ring
    rw [h1, ← mul_assoc, ← mul_pow, show (2:ℝ)*(1/2)=1 by norm_num, one_pow,
      one_mul]
  refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => hg0 _)
    (f := fun k : ℕ =>
      A * Real.log 2 * (((k:ℝ) + 3) * (1/2:ℝ)^k) + A * (1/4:ℝ)^k)
    (fun k => ?_) ?_
  ·

    have hshell_lo : ∀ j ∈ {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1},
        (normSq (ρ j))⁻¹ ≤ (1/4)^(k+1) := by
      intro j hj
      rw [Set.mem_setOf_eq] at hj
      have hn0 : ⌊‖ρ j‖⌋₊ ≠ 0 := by
        intro h; rw [h, Nat.log_zero_right] at hj; omega
      have hlo : (2:ℝ)^(k+1) ≤ ‖ρ j‖ := by
        calc (2:ℝ)^(k+1) = ((2^(k+1) : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (⌊‖ρ j‖⌋₊ : ℝ) := by
              exact_mod_cast hj ▸ Nat.pow_log_le_self 2 hn0
          _ ≤ ‖ρ j‖ := Nat.floor_le (norm_nonneg _)
      have hnsq : (4:ℝ)^(k+1) ≤ normSq (ρ j) := by
        rw [normSq_eq_norm_sq, show (4:ℝ)^(k+1) = ((2:ℝ)^(k+1))^2 by
          rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]]
        exact sq_le_sq' (by linarith [pow_pos (two_pos : (0:ℝ) < 2) (k+1)]) hlo
      calc (normSq (ρ j))⁻¹ ≤ ((4:ℝ)^(k+1))⁻¹ :=
            inv_anti₀ (pow_pos four_pos (k+1)) hnsq
        _ = (1/4)^(k+1) := by rw [one_div, inv_pow]

    haveI := (hshell_fin (k+1)).to_subtype
    haveI := Fintype.ofFinite ↥{j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1}
    have htsum : ∑' i : {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1}, (normSq (ρ i))⁻¹ ≤
        (Nat.card {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1} : ℝ) * (1/4)^(k+1) := by
      rw [tsum_eq_sum (s := Finset.univ) (fun i h => absurd (Finset.mem_univ i) h)]
      refine le_trans (Finset.sum_le_sum fun i _ => hshell_lo i.1 i.2) ?_
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        ← Nat.card_eq_fintype_card]

    have hcard_le : (Nat.card {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1} : ℝ) ≤
        (Nat.card {j | ‖ρ j‖ ≤ (2:ℝ)^(k+2)} : ℝ) := by
      have := Set.ncard_le_ncard (hshell_sub (k+1))
        (gapsw80_t49_enum_ball_finite hdiff hf0 hzero hcount (2^(k+2)))
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at this
      exact_mod_cast this
    have hJbound : (Nat.card {j | ‖ρ j‖ ≤ (2:ℝ)^(k+2)} : ℝ) ≤
        A * ((2:ℝ)^(k+2) * ((k:ℝ)+3) * Real.log 2 + 1) := by
      have h1 : (1:ℝ) ≤ (2:ℝ)^(k+2) := one_le_pow₀ one_le_two
      calc (Nat.card {j | ‖ρ j‖ ≤ (2:ℝ)^(k+2)} : ℝ)
          ≤ A * ((2:ℝ)^(k+2) * Real.log (2 * (2:ℝ)^(k+2)) + 1) := hA _ h1
        _ = A * ((2:ℝ)^(k+2) * ((k:ℝ)+3) * Real.log 2 + 1) := by
            rw [show (2:ℝ) * (2:ℝ)^(k+2) = (2:ℝ)^(k+3) by ring, Real.log_pow]
            push_cast; ring

    have h4pos : (0:ℝ) ≤ (1/4)^(k+1) := pow_nonneg (by norm_num) (k+1)
    have h4succ : (1/4:ℝ)^(k+1) ≤ (1/4:ℝ)^k := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg (by norm_num) k) (by norm_num)
    calc ∑' i : {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1}, (normSq (ρ (i:ℕ)))⁻¹
        ≤ (Nat.card {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1} : ℝ) * (1/4)^(k+1) := htsum
      _ ≤ A * ((2:ℝ)^(k+2) * ((k:ℝ)+3) * Real.log 2 + 1) * (1/4)^(k+1) :=
          mul_le_mul_of_nonneg_right (hcard_le.trans hJbound) h4pos
      _ = A * Real.log 2 * (((k:ℝ)+3) * (1/2)^k) + A * (1/4)^(k+1) := by
          rw [show A * ((2:ℝ)^(k+2) * ((k:ℝ)+3) * Real.log 2 + 1) * (1/4)^(k+1)
              = A * Real.log 2 * ((k:ℝ)+3) * ((2:ℝ)^(k+2) * (1/4)^(k+1))
                + A * (1/4)^(k+1) by ring, hpow24 k]
          ring
      _ ≤ A * Real.log 2 * (((k:ℝ)+3) * (1/2)^k) + A * (1/4)^k := by
          linarith [mul_le_mul_of_nonneg_left h4succ hA0]
  ·
    refine Summable.add (Summable.mul_left _ ?_) (Summable.mul_left _ ?_)
    · have h1 : Summable (fun k : ℕ => (k:ℝ) * (1/2)^k) := by
        have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (r := (1/2:ℝ)) (by norm_num)
        simpa [pow_one] using this
      have h2 : Summable (fun k : ℕ => (3:ℝ) * (1/2)^k) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3
      exact (h1.add h2).congr fun k => by push_cast; ring
    · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

end FLT.Gapsw80T49D1b0a1aiiEnumNormSqSummableProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T56D1b0a2aiBBoasCartanMinModulusSubDecomp

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

def gapsw80_t56_FarTailProductLowerBound : Prop :=
  ∀ (ρ : ℕ → ℂ),
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    (∃ A : ℝ, ∀ r : ℝ, 2 ≤ r →
      (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ A * (r * Real.log (2 * r) + 1)) →
    (∃ K : ℝ, ∀ r : ℝ, 2 ≤ r → ∀ s : ℂ, ‖s‖ = r →
      Real.exp (-(K * r * Real.sqrt r))
        ≤ ‖∏' j : {j | 2 * r < ‖ρ j‖},
            ((1 - s / ρ (j : ℕ)) * Complex.exp (s / ρ (j : ℕ)))‖)

def gapsw80_t56_MinModulusFromFarAndGoodRadius : Prop :=
  ∀ (ρ : ℕ → ℂ),
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    (∃ A : ℝ, ∀ r : ℝ, 2 ≤ r →
      (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ A * (r * Real.log (2 * r) + 1)) →
    (∃ K : ℝ, ∀ r : ℝ, 2 ≤ r → ∀ s : ℂ, ‖s‖ = r →
      Real.exp (-(K * r * Real.sqrt r))
        ≤ ‖∏' j : {j | 2 * r < ‖ρ j‖},
            ((1 - s / ρ (j : ℕ)) * Complex.exp (s / ρ (j : ℕ)))‖) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 2 ≤ R → ∃ r ∈ Set.Icc R (2 * R),
      ∀ j, ρ j ≠ 0 → ‖ρ j‖ ≤ 2 * r →
        δ * (Complex.normSq (ρ j))⁻¹ ≤ |r - ‖ρ j‖|) →
    (∃ C : ℝ, ∀ R : ℝ, 2 ≤ R → ∃ r ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = r →
      Real.exp (-(C * r * Real.sqrt r))
        ≤ ‖∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))‖)

def gapsw80_t56_CartanGoodRadiusExists : Prop :=
  ∀ (ρ : ℕ → ℂ),
    Summable (fun j => (Complex.normSq (ρ j))⁻¹) →
    (∃ A : ℝ, ∀ r : ℝ, 2 ≤ r →
      (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ A * (r * Real.log (2 * r) + 1)) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 2 ≤ R → ∃ r ∈ Set.Icc R (2 * R),
      ∀ j, ρ j ≠ 0 → ‖ρ j‖ ≤ 2 * r →
        δ * (Complex.normSq (ρ j))⁻¹ ≤ |r - ‖ρ j‖|)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t56_D1b0a2aiB_of_far_near_cartan
    (hα : gapsw80_t56_FarTailProductLowerBound)
    (hβ : gapsw80_t56_MinModulusFromFarAndGoodRadius)
    (hγ : gapsw80_t56_CartanGoodRadiusExists) :
    gapsw80_t54_MinModulusOfCountAndSummable := by
  have _em := Classical.em
  intro ρ hsum hcount
  exact hβ ρ hsum hcount (hα ρ hsum hcount) (hγ ρ hsum hcount)

end FLT.Gapsw80T56D1b0a2aiBBoasCartanMinModulusSubDecomp
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T55D1b0a2aiAZeroCountJensenBoundProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t55_tprod_E1_eq_tprod_nonzero (ρ : ℕ → ℂ) (s : ℂ) :
    ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))
      = ∏' j : {j | ρ j ≠ 0}, ((1 - s / ρ (j : ℕ)) * Complex.exp (s / ρ (j : ℕ))) := by
  have _em := Classical.em
  refine (Function.Injective.tprod_eq Subtype.val_injective ?_).symm
  rw [Subtype.range_coe]
  intro j hj
  by_contra h
  simp only [Set.mem_setOf_eq, not_not] at h
  exact hj (by simp [h, div_zero, Complex.exp_zero])

set_option maxHeartbeats 12800000 in

theorem gapsw80_t55_D1b0a2aiA_closed : gapsw80_t54_ZeroCountJensenBound := by
  have _em := Classical.em
  intro f g ρ hfdiff hford hsum hgdiff hgne hfact

  have hP0 : ∏' j, ((1 - (0:ℂ) / ρ j) * Complex.exp ((0:ℂ) / ρ j)) = 1 := by
    simp only [zero_div, sub_zero, Complex.exp_zero, mul_one]; exact tprod_one
  have hf0 : f 0 ≠ 0 := by rw [hfact 0, hP0, mul_one]; exact hgne 0

  by_cases hSfin : {j | ρ j ≠ 0}.Finite
  ·
    refine ⟨Nat.card {j | ρ j ≠ 0}, fun r hr => ?_⟩
    have hle : Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} ≤ Nat.card {j | ρ j ≠ 0} :=
      Nat.card_mono hSfin (fun j hj => hj.1)
    have hlog : 0 < Real.log (2 * r) := Real.log_pos (by linarith : (1:ℝ) < 2 * r)
    have hpos : (1:ℝ) ≤ r * Real.log (2 * r) + 1 := by nlinarith
    calc (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ (Nat.card {j | ρ j ≠ 0} : ℝ) := by exact_mod_cast hle
      _ ≤ (Nat.card {j | ρ j ≠ 0} : ℝ) * (r * Real.log (2 * r) + 1) :=
          le_mul_of_one_le_right (Nat.cast_nonneg _) hpos
  ·
    have hSinf : {j | ρ j ≠ 0}.Infinite := hSfin
    haveI : Infinite {j | ρ j ≠ 0} := hSinf.to_subtype
    obtain ⟨e⟩ : Nonempty (ℕ ≃ {j | ρ j ≠ 0}) := nonempty_equiv_of_countable
    set ρ' : ℕ → ℂ := fun k => ρ (e k : ℕ) with hρ'_def
    have hρ'0 : ∀ k, ρ' k ≠ 0 := fun k => (e k).2
    have hsum' : Summable (fun k => (Complex.normSq (ρ' k))⁻¹) :=
      e.summable_iff.mpr (hsum.subtype _)

    have hprodeq : ∀ s, ∏' j, ((1 - s / ρ j) * Complex.exp (s / ρ j))
        = ∏' k, ((1 - s / ρ' k) * Complex.exp (s / ρ' k)) := fun s =>
      (gapsw80_t55_tprod_E1_eq_tprod_nonzero ρ s).trans
        (Equiv.tprod_eq e (fun j : {j | ρ j ≠ 0} =>
          (1 - s / ρ (j : ℕ)) * Complex.exp (s / ρ (j : ℕ)))).symm

    obtain ⟨hP'diff, hP'ord⟩ := gapsw80_t45_D1b0a1b_closed ρ' hρ'0 hsum'

    have hfeq : f = g * (fun s => ∏' k, ((1 - s / ρ' k) * Complex.exp (s / ρ' k))) :=
      funext fun s => by rw [hfact s, hprodeq s]; rfl

    have hP'0 : (fun s => ∏' k, ((1 - s / ρ' k) * Complex.exp (s / ρ' k))) 0 ≠ 0 := by
      change ∏' k, ((1 - (0:ℂ) / ρ' k) * Complex.exp ((0:ℂ) / ρ' k)) ≠ 0
      rw [← hprodeq 0, hP0]; exact one_ne_zero

    have hcount : ∀ z, Nat.card {k | ρ' k = z} = analyticOrderNatAt f z := fun z => by
      have hgord0 : analyticOrderAt g z = 0 :=
        (hgdiff.analyticAt z).analyticOrderAt_eq_zero.mpr (hgne z)
      have hgNat0 : analyticOrderNatAt g z = 0 := by
        unfold analyticOrderNatAt; rw [hgord0]; rfl
      have hgordT : analyticOrderAt g z ≠ ⊤ := by simp [hgord0]
      have hP'ordT : analyticOrderAt
          (fun s => ∏' k, ((1 - s / ρ' k) * Complex.exp (s / ρ' k))) z ≠ ⊤ := fun h =>
        gapsw80_t42_not_locally_zero hP'diff hP'0 z (analyticOrderAt_eq_top.mp h)
      rw [hfeq, analyticOrderNatAt_mul (hgdiff.analyticAt z) (hP'diff.analyticAt z)
        hgordT hP'ordT, hgNat0, zero_add, hP'ord z]

    have hzero : ∀ k, f (ρ' k) = 0 := fun k => by
      have hfin := gapsw80_t45_fiber_finite hρ'0 hsum' (ρ' k)
      haveI : Finite {i | ρ' i = ρ' k} := Set.finite_coe_iff.mpr hfin
      have hne : Nat.card {i | ρ' i = ρ' k} ≠ 0 :=
        Nat.card_ne_zero.mpr ⟨⟨k, rfl⟩, inferInstance⟩
      exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (hcount (ρ' k) ▸ hne)

    obtain ⟨A, _hA0, hA⟩ := gapsw80_t49_enum_ball_card_le hfdiff hf0 hford hzero hcount

    refine ⟨A, fun r hr => ?_⟩
    have hbridge : Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} = Nat.card {k | ‖ρ' k‖ ≤ r} := by
      refine (Nat.card_congr ?_).symm
      exact (e.subtypeEquiv (p := fun k => ‖ρ' k‖ ≤ r)
          (q := fun j : {j | ρ j ≠ 0} => ‖ρ (j : ℕ)‖ ≤ r) (fun k => Iff.rfl)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun j => ρ j ≠ 0) (fun j => ‖ρ j‖ ≤ r))
    rw [hbridge]
    exact hA r (by linarith : (1:ℝ) ≤ r)

end FLT.Gapsw80T55D1b0a2aiAZeroCountJensenBoundProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T57D1b0a2aiBGammaCartanGoodRadiusProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t57_Icc_subset_biUnion_Ioo_lt_sum {ι : Type*} {b : ℝ}
    (f g : ι → ℝ) :
    ∀ (s : Finset ι), ∀ a, a ≤ b → (∀ i ∈ s, f i ≤ g i) →
      (Set.Icc a b ⊆ ⋃ i ∈ s, Set.Ioo (f i) (g i)) →
        b - a < ∑ i ∈ s, (g i - f i) := by
  classical
  intro s
  induction s using Finset.strongInductionOn with
  | _ s IH =>
    intro a hab hfg hcov
    have ha := hcov (Set.left_mem_Icc.mpr hab)
    simp only [Set.mem_iUnion, Set.mem_Ioo, exists_prop] at ha
    obtain ⟨k, hks, hfk, hgk⟩ := ha
    rcases lt_or_ge b (g k) with hbk | hbk
    · calc b - a < g k - f k := by linarith
        _ ≤ ∑ i ∈ s, (g i - f i) :=
          Finset.single_le_sum (fun i hi => sub_nonneg.mpr (hfg i hi)) hks
    · have hsub : Set.Icc (g k) b ⊆ ⋃ i ∈ s.erase k, Set.Ioo (f i) (g i) := by
        intro x ⟨hxl, hxr⟩
        have hxcov : x ∈ ⋃ i ∈ s, Set.Ioo (f i) (g i) :=
          hcov ⟨le_of_lt (lt_of_lt_of_le hgk hxl), hxr⟩
        simp only [Set.mem_iUnion, Set.mem_Ioo, exists_prop] at hxcov ⊢
        obtain ⟨m, hms, hfm, hgm⟩ := hxcov
        refine ⟨m, Finset.mem_erase.mpr ⟨?_, hms⟩, hfm, hgm⟩
        rintro rfl; exact absurd hxl (not_le.mpr hgm)
      have IHk := IH (s.erase k) (Finset.erase_ssubset hks) (g k) hbk
        (fun i hi => hfg i (Finset.mem_of_mem_erase hi)) hsub
      have hsplit := Finset.sum_erase_add s (fun i => g i - f i) hks
      linarith

set_option maxHeartbeats 3200000 in

theorem gapsw80_t57_exists_mem_Icc_forall_le_abs_sub {ι : Type*} (s : Finset ι)
    (c ε : ι → ℝ) (hε : ∀ i ∈ s, 0 ≤ ε i) {a b : ℝ} (hab : a ≤ b)
    (hlen : 2 * ∑ i ∈ s, ε i < b - a) :
    ∃ x ∈ Set.Icc a b, ∀ i ∈ s, ε i ≤ |x - c i| := by
  have _em := Classical.em
  have key : ¬ (Set.Icc a b ⊆ ⋃ i ∈ s, Set.Ioo (c i - ε i) (c i + ε i)) := by
    intro hcov
    have hlt := gapsw80_t57_Icc_subset_biUnion_Ioo_lt_sum
      (fun i => c i - ε i) (fun i => c i + ε i) s a hab
      (fun i hi => by linarith [hε i hi]) hcov
    simp only [add_sub_sub_cancel, ← two_mul, ← Finset.mul_sum] at hlt
    exact absurd hlt (not_lt.mpr hlen.le)
  rw [Set.not_subset] at key
  obtain ⟨x, hxI, hxB⟩ := key
  refine ⟨x, hxI, fun i hi => ?_⟩
  rw [← not_lt]
  intro hlt
  refine hxB (Set.mem_biUnion hi ?_)
  rw [Set.mem_Ioo]
  have h := abs_sub_lt_iff.mp hlt
  constructor <;> linarith [h.1, h.2]

set_option maxHeartbeats 12800000 in

theorem gapsw80_t57_cartanGoodRadiusExists_proof :
    gapsw80_t56_CartanGoodRadiusExists := by
  have _em := Classical.em
  intro ρ hsum _hcount
  set S := ∑' j, (Complex.normSq (ρ j))⁻¹ with hS_def
  have hS0 : 0 ≤ S := tsum_nonneg fun j => inv_nonneg.mpr (Complex.normSq_nonneg _)
  refine ⟨(S + 1)⁻¹, by positivity, fun R hR => ?_⟩
  have hR4 : (0:ℝ) < 4 * R := by linarith

  have hfin : {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ 4 * R}.Finite := by
    have h0 : Tendsto (fun j => (Complex.normSq (ρ j))⁻¹) atTop (𝓝 0) :=
      hsum.tendsto_atTop_zero
    have hε : (0:ℝ) < ((4*R)^2)⁻¹ := by positivity
    have hev : ∀ᶠ j in atTop, (Complex.normSq (ρ j))⁻¹ < ((4*R)^2)⁻¹ :=
      h0.eventually_lt_const hε
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at hev
    refine hev.subset ?_
    intro j ⟨hj0, hjR⟩
    simp only [Set.mem_setOf_eq, not_lt]
    have h1 : 0 < Complex.normSq (ρ j) := Complex.normSq_pos.mpr hj0
    have h2 : Complex.normSq (ρ j) ≤ (4*R)^2 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (ρ j)]
    exact (inv_le_inv₀ (by positivity) h1).mpr h2
  set s := hfin.toFinset with hs_def

  have hsum_s : ∑ j ∈ s, (Complex.normSq (ρ j))⁻¹ ≤ S :=
    hsum.sum_le_tsum s (fun j _ => inv_nonneg.mpr (Complex.normSq_nonneg _))
  have hlen : 2 * ∑ j ∈ s, ((S+1)⁻¹ * (Complex.normSq (ρ j))⁻¹) < 2*R - R := by
    rw [← Finset.mul_sum]
    have hstep : (S+1)⁻¹ * ∑ j ∈ s, (Complex.normSq (ρ j))⁻¹ ≤ (S+1)⁻¹ * S :=
      mul_le_mul_of_nonneg_left hsum_s (by positivity)
    have hkey : (S+1)⁻¹ * S < 1 := by
      rw [mul_comm, ← div_eq_mul_inv, div_lt_one (by positivity : (0:ℝ) < S+1)]; linarith
    linarith

  obtain ⟨r, hrI, hr_good⟩ :=
    gapsw80_t57_exists_mem_Icc_forall_le_abs_sub s
      (fun j => ‖ρ j‖) (fun j => (S+1)⁻¹ * (Complex.normSq (ρ j))⁻¹)
      (fun j _ => mul_nonneg (by positivity) (inv_nonneg.mpr (Complex.normSq_nonneg _)))
      (by linarith : R ≤ 2*R) hlen
  refine ⟨r, hrI, fun j hj0 hjr => ?_⟩
  have hjs : j ∈ s := by
    rw [hs_def, Set.Finite.mem_toFinset]
    exact ⟨hj0, hjr.trans (by linarith [hrI.2])⟩
  exact hr_good j hjs

end FLT.Gapsw80T57D1b0a2aiBGammaCartanGoodRadiusProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T58D1b0a2aiBAlphaFarTailProductLowerBoundProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t58_norm_log_one_sub_add_self_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := by
  have _em := Classical.em
  have hw1 : ‖-w‖ < 1 := by rw [norm_neg]; linarith
  have key : Complex.log (1 - w) + w = Complex.log (1 + (-w)) - (-w) := by
    ring_nf
  rw [key]
  have hle := Complex.norm_log_one_add_sub_self_le hw1
  rw [norm_neg] at hle
  calc ‖Complex.log (1 + -w) - -w‖
      ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 := hle
    _ ≤ ‖w‖ ^ 2 * 1 := by
        rw [show ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 = ‖w‖ ^ 2 * ((1 - ‖w‖)⁻¹ / 2) by ring]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [div_le_one (by norm_num : (0:ℝ) < 2)]
        calc (1 - ‖w‖)⁻¹ ≤ (1/2 : ℝ)⁻¹ :=
              inv_anti₀ (by norm_num) (by linarith)
          _ = 2 := by norm_num
    _ = ‖w‖ ^ 2 := mul_one _

set_option maxHeartbeats 3200000 in

theorem gapsw80_t58_exp_log_one_sub_add_self {w : ℂ} (hw : ‖w‖ < 1) :
    Complex.exp (Complex.log (1 - w) + w) = (1 - w) * Complex.exp w := by
  have _em := Classical.em
  have h1 : (1:ℂ) - w ≠ 0 := by
    refine sub_ne_zero.mpr (fun h => ?_)
    rw [← h, norm_one] at hw; exact lt_irrefl 1 hw
  rw [Complex.exp_add, Complex.exp_log h1]

set_option maxHeartbeats 25600000 in

theorem gapsw80_t58_summable_sqrt_norm_mul_inv_normSq {ρ : ℕ → ℂ}
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ r : ℝ, 2 ≤ r →
      (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ A * (r * Real.log (2 * r) + 1)) :
    Summable fun j => Real.sqrt ‖ρ j‖ * (Complex.normSq (ρ j))⁻¹ := by
  have _em := Classical.em
  classical
  have hg0 : 0 ≤ fun j => Real.sqrt ‖ρ j‖ * (Complex.normSq (ρ j))⁻¹ :=
    fun j => mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Complex.normSq_nonneg _))

  have hfin : ∀ M : ℝ, 0 < M → {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ M}.Finite := by
    intro M hM
    have hev : ∀ᶠ j in atTop, (Complex.normSq (ρ j))⁻¹ < (M^2)⁻¹ :=
      hsum.tendsto_atTop_zero.eventually_lt_const (by positivity)
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at hev
    refine hev.subset fun j ⟨hj0, hjM⟩ => ?_
    simp only [Set.mem_setOf_eq, not_lt]
    exact (inv_le_inv₀ (by positivity) (Complex.normSq_pos.mpr hj0)).mpr <| by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (ρ j)]

  have hsqrt_pow : ∀ n : ℕ, Real.sqrt ((2:ℝ)^n) = (Real.sqrt 2)^n := fun n => by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.sqrt 2) n,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast (2:ℝ) n,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), mul_comm]

  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hs2_ne : Real.sqrt 2 ≠ 0 := hs2_pos.ne'
  have hs2_lt2 : Real.sqrt 2 < 2 := by nlinarith
  have hs2_gt1 : (1:ℝ) < Real.sqrt 2 := by nlinarith
  have hs24_pos : (0:ℝ) < Real.sqrt 2 / 4 := by positivity
  have hs24_lt1 : Real.sqrt 2 / 4 < 1 := by linarith
  have hinv2_lt1 : (1:ℝ)/Real.sqrt 2 < 1 := by
    rw [div_lt_one hs2_pos]; exact hs2_gt1

  rw [summable_partition hg0 (s := fun k => {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k})
      (fun j => ⟨_, rfl, fun _ h => h.symm⟩)]
  have hshell_sub : ∀ k, {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k} ⊆ {j | ‖ρ j‖ ≤ 2^(k+1)} := by
    intro k j hj
    have h1 : ⌊‖ρ j‖⌋₊ < 2 ^ (k+1) := hj ▸ Nat.lt_pow_succ_log_self one_lt_two _
    have h2 : (⌊‖ρ j‖⌋₊ : ℝ) + 1 ≤ (2:ℝ)^(k+1) := by
      exact_mod_cast Nat.succ_le_of_lt h1
    exact le_of_lt <| (Nat.lt_floor_add_one _).trans_le h2

  refine ⟨fun k => ?_, ?_⟩
  · refine summable_of_ne_finset_zero
      (s := ((hfin (2^(k+1)) (by positivity)).toFinset.preimage Subtype.val
        Subtype.val_injective.injOn)) fun j hj => ?_
    rw [Finset.mem_preimage, Set.Finite.mem_toFinset] at hj
    rcases eq_or_ne (ρ (j:ℕ)) 0 with h0 | h0
    · simp [h0, Complex.normSq_zero]
    · exact absurd ⟨h0, hshell_sub k j.2⟩ hj

  rw [← summable_nat_add_iff 1]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two

  have hshell_lo : ∀ k, ∀ j ∈ {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1},
      ρ j ≠ 0 ∧ (2:ℝ)^(k+1) ≤ ‖ρ j‖ := by
    intro k j hj
    rw [Set.mem_setOf_eq] at hj
    have hn0 : ⌊‖ρ j‖⌋₊ ≠ 0 := fun h => by rw [h, Nat.log_zero_right] at hj; omega
    have hlo : (2:ℝ)^(k+1) ≤ ‖ρ j‖ :=
      calc (2:ℝ)^(k+1) = ((2^(k+1) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (⌊‖ρ j‖⌋₊ : ℝ) := by exact_mod_cast hj ▸ Nat.pow_log_le_self 2 hn0
        _ ≤ ‖ρ j‖ := Nat.floor_le (norm_nonneg _)
    have hρ0 : ρ j ≠ 0 := fun h0 => by
      simp only [h0, norm_zero] at hlo
      linarith [pow_pos (show (0:ℝ) < 2 from two_pos) (k+1)]
    exact ⟨hρ0, hlo⟩
  have hshell_fin1 : ∀ k, {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1}.Finite := fun k =>
    (hfin (2^(k+2)) (by positivity)).subset fun j hj =>
      ⟨(hshell_lo k j hj).1, hshell_sub (k+1) hj⟩

  have hkey : (2:ℝ) * (Real.sqrt 2/4) = 1/Real.sqrt 2 := by
    field_simp; linarith [hs2]
  have h2s : (2:ℝ)/Real.sqrt 2 = Real.sqrt 2 := by
    field_simp; linarith [hs2]
  have halg : ∀ k : ℕ, (2:ℝ)^(k+2) * (Real.sqrt 2/4)^(k+1)
      = Real.sqrt 2 * (1/Real.sqrt 2)^k := fun k => by
    calc (2:ℝ)^(k+2) * (Real.sqrt 2/4)^(k+1)
        = 2 * (2 * (Real.sqrt 2/4))^(k+1) := by rw [mul_pow]; ring
      _ = 2 * (1/Real.sqrt 2)^(k+1) := by rw [hkey]
      _ = (2/Real.sqrt 2) * (1/Real.sqrt 2)^k := by rw [pow_succ]; ring
      _ = Real.sqrt 2 * (1/Real.sqrt 2)^k := by rw [h2s]
  refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => hg0 _)
    (f := fun k : ℕ =>
      A * Real.log 2 * Real.sqrt 2 * (((k:ℝ) + 3) * (1/Real.sqrt 2)^k)
        + A * (Real.sqrt 2/4)^k)
    (fun k => ?_) ?_
  ·

    have hterm : ∀ j ∈ {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1},
        Real.sqrt ‖ρ j‖ * (Complex.normSq (ρ j))⁻¹ ≤ (Real.sqrt 2/4)^(k+1) := by
      intro j hj
      obtain ⟨hj0, hjlo⟩ := hshell_lo k j hj
      have hnpos : (0:ℝ) < ‖ρ j‖ := norm_pos_iff.mpr hj0
      have hspos : (0:ℝ) < Real.sqrt ‖ρ j‖ := Real.sqrt_pos.mpr hnpos
      have hssq : Real.sqrt ‖ρ j‖ * Real.sqrt ‖ρ j‖ = ‖ρ j‖ :=
        Real.mul_self_sqrt hnpos.le
      have hsqlo : (Real.sqrt 2)^(k+1) ≤ Real.sqrt ‖ρ j‖ := by
        rw [← hsqrt_pow (k+1)]; exact Real.sqrt_le_sqrt hjlo

      have hinvpow : (Real.sqrt 2/4)^(k+1)
          = ((2:ℝ)^(k+1) * (Real.sqrt 2)^(k+1))⁻¹ := by
        rw [← mul_pow, ← inv_pow]
        congr 1
        rw [eq_comm, inv_eq_one_div,
          div_eq_div_iff (mul_pos two_pos hs2_pos).ne'
            (show (4:ℝ) ≠ 0 by norm_num), one_mul]
        nlinarith [hs2]
      rw [hinvpow, Complex.normSq_eq_norm_sq,
        show Real.sqrt ‖ρ j‖ * (‖ρ j‖^2)⁻¹ = Real.sqrt ‖ρ j‖ / ‖ρ j‖^2
          from (div_eq_mul_inv _ _).symm,
        div_le_iff₀ (by positivity : (0:ℝ) < ‖ρ j‖^2), inv_mul_eq_div,
        le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(k+1) * (Real.sqrt 2)^(k+1))]
      calc Real.sqrt ‖ρ j‖ * ((2:ℝ)^(k+1) * (Real.sqrt 2)^(k+1))
          ≤ Real.sqrt ‖ρ j‖ * (‖ρ j‖ * Real.sqrt ‖ρ j‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hjlo hsqlo (pow_nonneg hs2_pos.le _) hnpos.le)
              hspos.le
        _ = ‖ρ j‖^2 := by rw [sq]; nlinarith [hssq]

    haveI := (hshell_fin1 k).to_subtype
    haveI := Fintype.ofFinite ↥{j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1}
    have htsum : ∑' i : {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1},
          Real.sqrt ‖ρ (i:ℕ)‖ * (Complex.normSq (ρ (i:ℕ)))⁻¹
        ≤ (Nat.card {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1} : ℝ)
            * (Real.sqrt 2/4)^(k+1) := by
      rw [tsum_eq_sum (s := Finset.univ) (fun i h => absurd (Finset.mem_univ i) h)]
      refine le_trans (Finset.sum_le_sum fun i _ => hterm i.1 i.2) ?_
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]

    have hcard_le : (Nat.card {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1} : ℝ)
        ≤ A * ((2:ℝ)^(k+2) * ((k:ℝ)+3) * Real.log 2 + 1) := by
      have hstep1 : (Nat.card {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1} : ℝ)
          ≤ (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ (2:ℝ)^(k+2)} : ℝ) := by
        exact_mod_cast Nat.card_mono (hfin (2^(k+2)) (by positivity))
          (fun j hj => ⟨(hshell_lo k j hj).1, hshell_sub (k+1) hj⟩)
      refine hstep1.trans ?_
      have h1 : (2:ℝ) ≤ (2:ℝ)^(k+2) := by
        calc (2:ℝ) = (2:ℝ)^1 := (pow_one _).symm
          _ ≤ (2:ℝ)^(k+2) := pow_le_pow_right₀ one_le_two (by omega)
      calc (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ (2:ℝ)^(k+2)} : ℝ)
          ≤ A * ((2:ℝ)^(k+2) * Real.log (2 * (2:ℝ)^(k+2)) + 1) := hA _ h1
        _ = A * ((2:ℝ)^(k+2) * ((k:ℝ)+3) * Real.log 2 + 1) := by
            rw [show (2:ℝ) * (2:ℝ)^(k+2) = (2:ℝ)^(k+3) by ring, Real.log_pow]
            push_cast; ring

    have hbpos : (0:ℝ) ≤ (Real.sqrt 2/4)^(k+1) := pow_nonneg hs24_pos.le _
    have hsucc : (Real.sqrt 2/4)^(k+1) ≤ (Real.sqrt 2/4)^k := by
      rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hs24_pos.le _) hs24_lt1.le
    calc ∑' i : {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1},
            Real.sqrt ‖ρ (i:ℕ)‖ * (Complex.normSq (ρ (i:ℕ)))⁻¹
        ≤ (Nat.card {j | Nat.log 2 ⌊‖ρ j‖⌋₊ = k + 1} : ℝ)
            * (Real.sqrt 2/4)^(k+1) := htsum
      _ ≤ A * ((2:ℝ)^(k+2) * ((k:ℝ)+3) * Real.log 2 + 1)
            * (Real.sqrt 2/4)^(k+1) :=
          mul_le_mul_of_nonneg_right hcard_le hbpos
      _ = A * Real.log 2 * ((k:ℝ)+3)
            * ((2:ℝ)^(k+2) * (Real.sqrt 2/4)^(k+1))
          + A * (Real.sqrt 2/4)^(k+1) := by ring
      _ = A * Real.log 2 * Real.sqrt 2 * (((k:ℝ)+3) * (1/Real.sqrt 2)^k)
          + A * (Real.sqrt 2/4)^(k+1) := by rw [halg k]; ring
      _ ≤ A * Real.log 2 * Real.sqrt 2 * (((k:ℝ)+3) * (1/Real.sqrt 2)^k)
          + A * (Real.sqrt 2/4)^k := by
          linarith [mul_le_mul_of_nonneg_left hsucc hA0]
  ·
    refine Summable.add (Summable.mul_left _ ?_) (Summable.mul_left _ ?_)
    · have hnorm : ‖(1:ℝ)/Real.sqrt 2‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; exact hinv2_lt1
      have h1 : Summable (fun k : ℕ => (k:ℝ) * (1/Real.sqrt 2)^k) := by
        have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (r := (1/Real.sqrt 2)) hnorm
        simpa [pow_one] using this
      have h2 : Summable (fun k : ℕ => (3:ℝ) * (1/Real.sqrt 2)^k) :=
        (summable_geometric_of_lt_one (by positivity) hinv2_lt1).mul_left 3
      exact (h1.add h2).congr fun k => by push_cast; ring
    · exact summable_geometric_of_lt_one hs24_pos.le hs24_lt1

set_option maxHeartbeats 25600000 in

theorem gapsw80_t58_farTailProductLowerBound_proof :
    gapsw80_t56_FarTailProductLowerBound := by
  have _em := Classical.em
  intro ρ hsum hcount

  obtain ⟨A, hA⟩ := hcount
  set A' := max A 0 with hA'_def
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hA' : ∀ r : ℝ, 2 ≤ r →
      (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ A' * (r * Real.log (2 * r) + 1) := by
    intro r hr
    refine (hA r hr).trans ?_
    have hpos : (0:ℝ) < r * Real.log (2 * r) + 1 := by
      have : (0:ℝ) < Real.log (2 * r) := Real.log_pos (by linarith)
      nlinarith
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le

  have hT := gapsw80_t58_summable_sqrt_norm_mul_inv_normSq hsum hA'0 hA'
  set T := ∑' j, Real.sqrt ‖ρ j‖ * (Complex.normSq (ρ j))⁻¹ with hT_def
  have hT0 : 0 ≤ T := tsum_nonneg fun j =>
    mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Complex.normSq_nonneg _))
  refine ⟨T, fun r hr s hs => ?_⟩
  have hr_pos : (0:ℝ) < r := by linarith
  have h2r_pos : (0:ℝ) < 2 * r := by linarith
  have hs2r_pos : (0:ℝ) < Real.sqrt (2 * r) := Real.sqrt_pos.mpr h2r_pos

  have hmem : ∀ j : {j | 2 * r < ‖ρ j‖}, 2 * r < ‖ρ (j:ℕ)‖ := fun j => j.2
  have hnpos : ∀ j : {j | 2 * r < ‖ρ j‖}, (0:ℝ) < ‖ρ (j:ℕ)‖ := fun j => by
    linarith [hmem j]
  have hρ0 : ∀ j : {j | 2 * r < ‖ρ j‖}, ρ (j:ℕ) ≠ 0 := fun j =>
    norm_pos_iff.mp (hnpos j)
  have hwlt : ∀ j : {j | 2 * r < ‖ρ j‖}, ‖s / ρ (j:ℕ)‖ < 1/2 := fun j => by
    rw [norm_div, hs, div_lt_iff₀ (hnpos j)]; linarith [hmem j]
  have hwle : ∀ j : {j | 2 * r < ‖ρ j‖}, ‖s / ρ (j:ℕ)‖ ≤ 1/2 := fun j => (hwlt j).le

  set g : {j | 2 * r < ‖ρ j‖} → ℂ :=
    fun j => Complex.log (1 - s / ρ (j:ℕ)) + s / ρ (j:ℕ) with hg_def
  have hg_bd : ∀ j, ‖g j‖ ≤ r^2 * (Complex.normSq (ρ (j:ℕ)))⁻¹ := fun j =>
    calc ‖g j‖ ≤ ‖s / ρ (j:ℕ)‖ ^ 2 :=
          gapsw80_t58_norm_log_one_sub_add_self_le (hwle j)
      _ = r^2 * (Complex.normSq (ρ (j:ℕ)))⁻¹ := by
          rw [norm_div, hs, div_pow, Complex.normSq_eq_norm_sq]; ring

  have hsub_sum :
      Summable (fun j : {j | 2 * r < ‖ρ j‖} => (Complex.normSq (ρ (j:ℕ)))⁻¹) :=
    hsum.subtype _
  have hg_sum : Summable g :=
    Summable.of_norm_bounded (hsub_sum.mul_left (r^2)) hg_bd

  have hprod : (∏' j : {j | 2 * r < ‖ρ j‖},
        ((1 - s / ρ (j:ℕ)) * Complex.exp (s / ρ (j:ℕ))))
      = Complex.exp (∑' j, g j) := by
    have hcexp : HasProd (Complex.exp ∘ g) (Complex.exp (∑' j, g j)) :=
      hg_sum.hasSum.cexp
    have heq : (Complex.exp ∘ g)
        = fun j : {j | 2 * r < ‖ρ j‖} =>
          (1 - s / ρ (j:ℕ)) * Complex.exp (s / ρ (j:ℕ)) :=
      funext fun j => gapsw80_t58_exp_log_one_sub_add_self
        (lt_of_lt_of_le (hwlt j) (by norm_num))
    rw [heq] at hcexp
    exact hcexp.tprod_eq
  rw [hprod, Complex.norm_exp]

  refine Real.exp_le_exp.mpr ?_
  rw [Complex.re_tsum hg_sum]

  have hre_bd : ∀ j : {j | 2*r < ‖ρ j‖},
      -(r^2 * (Complex.normSq (ρ (j:ℕ)))⁻¹) ≤ (g j).re := fun j =>
    calc -(r^2 * (Complex.normSq (ρ (j:ℕ)))⁻¹) ≤ -‖g j‖ := neg_le_neg (hg_bd j)
      _ ≤ -|(g j).re| := neg_le_neg (Complex.abs_re_le_norm _)
      _ ≤ (g j).re := neg_abs_le _
  have hnorm_sum :
      Summable (fun j : {j | 2*r < ‖ρ j‖} => r^2 * (Complex.normSq (ρ (j:ℕ)))⁻¹) :=
    hsub_sum.mul_left _
  have hre_sum : Summable (fun j => (g j).re) := (hasSum_re hg_sum.hasSum).summable
  have hre_ge :
      -(r^2 * ∑' j : {j | 2*r < ‖ρ j‖}, (Complex.normSq (ρ (j:ℕ)))⁻¹)
        ≤ ∑' j, (g j).re := by
    rw [← tsum_mul_left, ← tsum_neg]
    exact Summable.tsum_le_tsum hre_bd hnorm_sum.neg hre_sum
  refine le_trans ?_ hre_ge

  rw [neg_le_neg_iff]

  have hpw : ∀ j : {j | 2*r < ‖ρ j‖}, (Complex.normSq (ρ (j:ℕ)))⁻¹
      ≤ (Real.sqrt (2*r))⁻¹
        * (Real.sqrt ‖ρ (j:ℕ)‖ * (Complex.normSq (ρ (j:ℕ)))⁻¹) := fun j => by
    rw [← mul_assoc]
    refine le_mul_of_one_le_left (inv_nonneg.mpr (Complex.normSq_nonneg _)) ?_
    rw [← div_eq_inv_mul, one_le_div hs2r_pos]
    exact Real.sqrt_le_sqrt (le_of_lt (hmem j))
  have hTsub : Summable (fun j : {j | 2*r < ‖ρ j‖} =>
      Real.sqrt ‖ρ (j:ℕ)‖ * (Complex.normSq (ρ (j:ℕ)))⁻¹) := hT.subtype _
  have hsub_le : ∑' j : {j | 2*r < ‖ρ j‖}, (Complex.normSq (ρ (j:ℕ)))⁻¹
      ≤ (Real.sqrt (2*r))⁻¹ * T := by
    calc ∑' j : {j | 2*r < ‖ρ j‖}, (Complex.normSq (ρ (j:ℕ)))⁻¹
        ≤ ∑' j : {j | 2*r < ‖ρ j‖}, (Real.sqrt (2*r))⁻¹
            * (Real.sqrt ‖ρ (j:ℕ)‖ * (Complex.normSq (ρ (j:ℕ)))⁻¹) :=
          Summable.tsum_le_tsum hpw hsub_sum (hTsub.mul_left _)
      _ = (Real.sqrt (2*r))⁻¹
            * ∑' j : {j | 2*r < ‖ρ j‖},
              Real.sqrt ‖ρ (j:ℕ)‖ * (Complex.normSq (ρ (j:ℕ)))⁻¹ :=
          tsum_mul_left
      _ ≤ (Real.sqrt (2*r))⁻¹ * T :=
          mul_le_mul_of_nonneg_left
            (Summable.tsum_subtype_le _ _
              (fun j => mul_nonneg (Real.sqrt_nonneg _)
                (inv_nonneg.mpr (Complex.normSq_nonneg _))) hT)
            (by positivity)

  have hrate : r^2 * (Real.sqrt (2*r))⁻¹ ≤ r * Real.sqrt r := by
    have hsqr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr_pos.le
    have hs2rm : Real.sqrt (2*r) = Real.sqrt 2 * Real.sqrt r :=
      Real.sqrt_mul (by norm_num) r
    have hs2ge1 : (1:ℝ) ≤ Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hrhs : r * Real.sqrt r * Real.sqrt (2*r) = Real.sqrt 2 * r^2 := by
      have h : r * Real.sqrt r * (Real.sqrt 2 * Real.sqrt r)
          = Real.sqrt 2 * (r * (Real.sqrt r * Real.sqrt r)) := by ring
      rw [hs2rm, h, hsqr]; ring
    rw [← div_eq_mul_inv, div_le_iff₀ hs2r_pos, hrhs]
    nlinarith [sq_nonneg r]
  calc r^2 * ∑' j : {j | 2*r < ‖ρ j‖}, (Complex.normSq (ρ (j:ℕ)))⁻¹
      ≤ r^2 * ((Real.sqrt (2*r))⁻¹ * T) :=
        mul_le_mul_of_nonneg_left hsub_le (by positivity)
    _ = r^2 * (Real.sqrt (2*r))⁻¹ * T := by ring
    _ ≤ r * Real.sqrt r * T := mul_le_mul_of_nonneg_right hrate hT0
    _ = T * r * Real.sqrt r := by ring

end FLT.Gapsw80T58D1b0a2aiBAlphaFarTailProductLowerBoundProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

section

namespace FLT
namespace Gapsw80T59D1b0a2aiBBetaMinModulusAssemblyProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex Filter P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Filter Set P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Set Metric P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Metric"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Topology"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t59_sq_log_two_mul_le {r : ℝ} (hr : 2 ≤ r) :
    (Real.log (2*r))^2 ≤ 16 * Real.sqrt (2*r) := by
  have _em := Classical.em
  have h2r : (0:ℝ) < 2*r := by linarith
  have hl0 : 0 ≤ Real.log (2*r) := Real.log_nonneg (by linarith)
  have h1 : Real.log (2*r) ≤ 4 * (2*r) ^ (1/4 : ℝ) := by
    have := Real.log_le_rpow_div h2r.le (show (0:ℝ) < 1/4 by norm_num)
    linarith
  calc (Real.log (2*r))^2
      ≤ (4 * (2*r) ^ (1/4 : ℝ))^2 := pow_le_pow_left₀ hl0 h1 2
    _ = 16 * ((2*r) ^ (1/4 : ℝ))^2 := by ring
    _ = 16 * (2*r) ^ (1/2 : ℝ) := by
        rw [← Real.rpow_natCast ((2*r)^(1/4:ℝ)) 2,
          ← Real.rpow_mul h2r.le]; norm_num
    _ = 16 * Real.sqrt (2*r) := by rw [Real.sqrt_eq_rpow]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t59_abs_sub_norm_div_le_norm_one_sub_div
    {s ρ : ℂ} {r : ℝ} (hs : ‖s‖ = r) (hρ0 : ρ ≠ 0) :
    |r - ‖ρ‖| / ‖ρ‖ ≤ ‖1 - s/ρ‖ := by
  have _em := Classical.em
  have hρn : (0:ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hid : (1:ℂ) - s/ρ = (ρ - s)/ρ := by field_simp
  rw [hid, norm_div]
  gcongr
  calc |r - ‖ρ‖| = |‖ρ‖ - ‖s‖| := by rw [hs]; exact abs_sub_comm _ _
    _ ≤ ‖ρ - s‖ := abs_norm_sub_norm_le ρ s

set_option maxHeartbeats 51200000 in

theorem gapsw80_t59_minModulusFromFarAndGoodRadius_proof :
    gapsw80_t56_MinModulusFromFarAndGoodRadius := by
  have _em := Classical.em
  intro ρ hsum hcount hα hγ
  classical

  obtain ⟨K, hK⟩ := hα
  set K' := max K 0 with hK'_def
  have hK'0 : 0 ≤ K' := le_max_right _ _
  obtain ⟨A, hA⟩ := hcount
  set A' := max A 0 with hA'_def
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hA' : ∀ r : ℝ, 2 ≤ r →
      (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ r} : ℝ)
        ≤ A' * (r * Real.log (2 * r) + 1) := fun r hr =>
    (hA r hr).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) <| by
      have : (0:ℝ) < Real.log (2 * r) := Real.log_pos (by linarith); nlinarith
  obtain ⟨δ, hδ0, hγr⟩ := hγ

  have hT := gapsw80_t58_summable_sqrt_norm_mul_inv_normSq hsum hA'0 hA'
  set T := ∑' j, Real.sqrt ‖ρ j‖ * (Complex.normSq (ρ j))⁻¹ with hT_def
  have hT0 : 0 ≤ T := tsum_nonneg fun j =>
    mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Complex.normSq_nonneg _))

  refine ⟨K' + 480*A' + 20*A'*|Real.log δ| + 2*T, fun R hR => ?_⟩

  obtain ⟨r, hrI, hrgood⟩ := hγr R hR
  have hrR : R ≤ r := hrI.1
  have hr2 : 2 ≤ r := le_trans hR hrR
  have hr0 : (0:ℝ) < r := by linarith
  have h2r : (0:ℝ) < 2*r := by linarith
  have h2r2 : (2:ℝ) ≤ 2*r := by linarith
  have hsqrr : (0:ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs2r : Real.sqrt (2*r) = Real.sqrt 2 * Real.sqrt r :=
    Real.sqrt_mul (by norm_num) r
  have hs2eq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2le2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hs2rle : Real.sqrt (2*r) ≤ 2 * Real.sqrt r := by
    rw [hs2r]; exact mul_le_mul_of_nonneg_right hs2le2 (Real.sqrt_nonneg _)
  have hlog2r0 : (0:ℝ) < Real.log (2*r) := Real.log_pos (by linarith)
  have hlog2r_le : Real.log (2*r) ≤ 2 * Real.sqrt (2*r) := by
    have h := Real.log_le_rpow_div h2r.le (show (0:ℝ) < 1/2 by norm_num)
    have heq : (2*r)^(1/2:ℝ) / (1/2) = 2 * Real.sqrt (2*r) := by
      rw [← Real.sqrt_eq_rpow]; ring
    linarith [heq ▸ h]
  have hrsqrr1 : (1:ℝ) ≤ r * Real.sqrt r := by
    have hs2 : (1:ℝ) ≤ Real.sqrt r := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith)
    nlinarith
  refine ⟨r, hrI, fun s hs => ?_⟩

  set F : ℕ → ℂ := fun j => (1 - s / ρ j) * Complex.exp (s / ρ j) with hF_def

  have hfin : {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ 2*r}.Finite := by
    have hev : ∀ᶠ j in atTop, (Complex.normSq (ρ j))⁻¹ < ((2*r)^2)⁻¹ :=
      hsum.tendsto_atTop_zero.eventually_lt_const (by positivity)
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at hev
    refine hev.subset fun j ⟨hj0, hjM⟩ => ?_
    simp only [Set.mem_setOf_eq, not_lt]
    exact (inv_le_inv₀ (by positivity) (Complex.normSq_pos.mpr hj0)).mpr <| by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (ρ j)]
  set N := hfin.toFinset with hN_def
  have hNmem : ∀ j, j ∈ N ↔ ρ j ≠ 0 ∧ ‖ρ j‖ ≤ 2*r := fun j => by
    rw [hN_def]; exact hfin.mem_toFinset

  have hfar_mem : ∀ j : {j | 2*r < ‖ρ j‖}, 2*r < ‖ρ (j:ℕ)‖ := fun j => j.2
  have hfar_ne : ∀ j : {j | 2*r < ‖ρ j‖}, ρ (j:ℕ) ≠ 0 := fun j =>
    norm_pos_iff.mp (lt_trans h2r (hfar_mem j))

  have hmul_far : Multipliable (fun j : {j | 2*r < ‖ρ j‖} => F (j:ℕ)) := by
    have hρ0' : ∀ j : {j | 2*r < ‖ρ j‖}, (ρ ∘ Subtype.val) j ≠ 0 := hfar_ne
    have hsum' : Summable fun j : {j | 2*r < ‖ρ j‖} =>
        (Complex.normSq ((ρ ∘ Subtype.val) j))⁻¹ := hsum.subtype _
    have h := multipliable_one_add_of_summable
      (gapsw80_t45_summable_norm_E1_sub_one hρ0' hsum' s)
    simpa [Function.comp, hF_def] using h

  have hfarc_mem : ∀ j : ↥({j | 2*r < ‖ρ j‖}ᶜ), ‖ρ (j:ℕ)‖ ≤ 2*r := fun j => by
    have := j.2
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at this
    exact this

  set N' : Finset ↥({j | 2*r < ‖ρ j‖}ᶜ) :=
    N.preimage Subtype.val Subtype.val_injective.injOn with hN'_def
  have hN'_zero : ∀ j : ↥({j | 2*r < ‖ρ j‖}ᶜ), j ∉ N' → F (j:ℕ) = 1 := by
    intro j hj
    rw [hN'_def, Finset.mem_preimage, hNmem] at hj
    have hj0 : ρ (j:ℕ) = 0 := by by_contra h; exact hj ⟨h, hfarc_mem j⟩
    simp [hF_def, hj0, div_zero, Complex.exp_zero]
  have hmul_farc : Multipliable (fun j : ↥({j | 2*r < ‖ρ j‖}ᶜ) => F (j:ℕ)) :=
    multipliable_of_ne_finset_one hN'_zero

  have hsplit : ∏' j, F j
      = (∏' j : ↥({j | 2*r < ‖ρ j‖}ᶜ), F (j:ℕ))
        * (∏' j : {j | 2*r < ‖ρ j‖}, F (j:ℕ)) := by
    rw [mul_comm]; exact (hmul_far.tprod_mul_tprod_compl hmul_farc).symm

  have hN_sub : (↑N : Set ℕ) ⊆ ({j | 2*r < ‖ρ j‖}ᶜ : Set ℕ) := fun j hj => by
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ((hNmem j).mp (Finset.mem_coe.mp hj)).2
  have hfarc_eq : (∏' j : ↥({j | 2*r < ‖ρ j‖}ᶜ), F (j:ℕ)) = ∏ j ∈ N, F j := by
    rw [tprod_eq_prod (s := N') hN'_zero, hN'_def,
      Finset.prod_preimage _ _ Subtype.val_injective.injOn _
        (fun j hj hjr => absurd (hN_sub hj) (by simpa [Subtype.range_val] using hjr))]
  rw [hsplit, hfarc_eq, norm_mul]

  have hfar_bd : Real.exp (-(K' * r * Real.sqrt r))
      ≤ ‖∏' j : {j | 2*r < ‖ρ j‖}, F (j:ℕ)‖ := by
    refine le_trans ?_ (hK r hr2 s hs)
    exact Real.exp_le_exp.mpr <| neg_le_neg <|
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left K 0) hr0.le) hsqrr.le

  have hFpos : ∀ j ∈ N, (0:ℝ) < ‖F j‖ := fun j hj => by
    obtain ⟨hj0, hjr⟩ := (hNmem j).mp hj
    have hns : (0:ℝ) < Complex.normSq (ρ j) := Complex.normSq_pos.mpr hj0
    have hmargin := hrgood j hj0 hjr
    have hrne : r ≠ ‖ρ j‖ := fun heq => by
      rw [heq, sub_self, abs_zero] at hmargin
      exact absurd hmargin (not_le.mpr (by positivity))
    refine norm_pos_iff.mpr (mul_ne_zero ?_ (Complex.exp_ne_zero _))
    refine sub_ne_zero.mpr fun heq => hrne ?_
    rw [eq_comm, div_eq_one_iff_eq hj0] at heq
    rw [← hs, heq]

  have hlogF_lb : ∀ j ∈ N,
      Real.log δ - 3 * Real.log (2*r) - r * ‖ρ j‖⁻¹ ≤ Real.log ‖F j‖ := by
    intro j hj
    obtain ⟨hj0, hjr⟩ := (hNmem j).mp hj
    have hρn : (0:ℝ) < ‖ρ j‖ := norm_pos_iff.mpr hj0
    have hns : (0:ℝ) < Complex.normSq (ρ j) := Complex.normSq_pos.mpr hj0
    have hmargin := hrgood j hj0 hjr

    have hfac_lb : δ / ‖ρ j‖^3 ≤ ‖1 - s/ρ j‖ := by
      refine le_trans ?_ (gapsw80_t59_abs_sub_norm_div_le_norm_one_sub_div hs hj0)
      rw [show δ/‖ρ j‖^3 = (δ/‖ρ j‖^2)/‖ρ j‖ from by rw [div_div, ← pow_succ]]
      gcongr
      rwa [Complex.normSq_eq_norm_sq, ← div_eq_mul_inv] at hmargin
    have hfac_pos : (0:ℝ) < δ / ‖ρ j‖^3 := by positivity

    have hFeq : ‖F j‖ = ‖1 - s/ρ j‖ * Real.exp (s/ρ j).re := by
      simp only [hF_def, norm_mul, Complex.norm_exp]
    rw [hFeq, Real.log_mul (lt_of_lt_of_le hfac_pos hfac_lb).ne'
      (Real.exp_pos _).ne', Real.log_exp]

    have hlog1 : Real.log δ - 3 * Real.log (2*r) ≤ Real.log ‖1 - s/ρ j‖ := by
      refine le_trans ?_ (Real.log_le_log hfac_pos hfac_lb)
      rw [Real.log_div hδ0.ne' (by positivity),
        show ‖ρ j‖^3 = ‖ρ j‖^(3:ℕ) from rfl, Real.log_pow]
      have hρ2r : Real.log ‖ρ j‖ ≤ Real.log (2*r) := Real.log_le_log hρn hjr
      push_cast; linarith

    have hre : -(r * ‖ρ j‖⁻¹) ≤ (s/ρ j).re := by
      have h1 : |(s/ρ j).re| ≤ ‖s/ρ j‖ := Complex.abs_re_le_norm _
      have h2 : ‖s/ρ j‖ = r * ‖ρ j‖⁻¹ := by
        rw [norm_div, hs, div_eq_mul_inv]
      linarith [neg_abs_le (s/ρ j).re]
    linarith

  have hNcard : (N.card : ℝ) ≤ 5 * A' * r * Real.log (2*r) := by
    have hc1 : (N.card : ℝ) = (Nat.card {j | ρ j ≠ 0 ∧ ‖ρ j‖ ≤ 2*r} : ℝ) := by
      rw [hN_def, ← Nat.card_eq_card_finite_toFinset hfin]
    rw [hc1]
    refine (hA' (2*r) h2r2).trans ?_
    have hl4 : Real.log (2*(2*r)) ≤ 2 * Real.log (2*r) := by
      rw [Real.log_mul (by norm_num) h2r.ne']
      linarith [Real.log_le_log (show (0:ℝ) < 2 by norm_num) h2r2]
    have hm1 : (1:ℝ) ≤ r * Real.log (2*r) := by
      have he : Real.exp 1 ≤ 2*r :=
        (le_of_lt Real.exp_one_lt_d9).trans
          ((show (2.7182818286:ℝ) ≤ 4 by norm_num).trans (by linarith))
      have h1 : (1:ℝ) ≤ Real.log (2*r) := by
        rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
      nlinarith
    calc A' * (2*r * Real.log (2*(2*r)) + 1)
        ≤ A' * (2*r * (2 * Real.log (2*r)) + r * Real.log (2*r)) := by
          refine mul_le_mul_of_nonneg_left ?_ hA'0
          exact add_le_add (mul_le_mul_of_nonneg_left hl4 (by linarith)) hm1
      _ = 5 * A' * r * Real.log (2*r) := by ring

  have hNinv_sum : ∑ j ∈ N, ‖ρ j‖⁻¹ ≤ Real.sqrt (2*r) * T := by
    have hs2rpos : (0:ℝ) < Real.sqrt (2*r) := Real.sqrt_pos.mpr h2r
    calc ∑ j ∈ N, ‖ρ j‖⁻¹
        ≤ ∑ j ∈ N, Real.sqrt (2*r)
            * (Real.sqrt ‖ρ j‖ * (Complex.normSq (ρ j))⁻¹) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨hj0, hjr⟩ := (hNmem j).mp hj
          have hρn : (0:ℝ) < ‖ρ j‖ := norm_pos_iff.mpr hj0
          have hss : Real.sqrt ‖ρ j‖ * Real.sqrt ‖ρ j‖ = ‖ρ j‖ :=
            Real.mul_self_sqrt hρn.le
          rw [Complex.normSq_eq_norm_sq, ← mul_assoc,
            show ‖ρ j‖⁻¹ = Real.sqrt ‖ρ j‖ * Real.sqrt ‖ρ j‖ * (‖ρ j‖^2)⁻¹ from
              by rw [hss, sq, mul_inv, ← mul_assoc,
                mul_inv_cancel₀ hρn.ne', one_mul]]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hjr)
              (Real.sqrt_nonneg _)) (by positivity)
      _ = Real.sqrt (2*r)
            * ∑ j ∈ N, Real.sqrt ‖ρ j‖ * (Complex.normSq (ρ j))⁻¹ :=
          (Finset.mul_sum ..).symm
      _ ≤ Real.sqrt (2*r) * T := by
          gcongr
          exact hT.sum_le_tsum N (fun j _ =>
            mul_nonneg (Real.sqrt_nonneg _)
              (inv_nonneg.mpr (Complex.normSq_nonneg _)))

  have hnear_sum : -(((480*A' + 20*A'*|Real.log δ| + 2*T)) * r * Real.sqrt r)
      ≤ ∑ j ∈ N, Real.log ‖F j‖ := by
    refine le_trans ?_ (Finset.sum_le_sum hlogF_lb)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← Finset.mul_sum]
    have hA'r0 : (0:ℝ) ≤ 5*A'*r := by positivity
    have h1 : (N.card : ℝ) * (3 * Real.log (2*r))
        ≤ 480 * A' * r * Real.sqrt r := by
      calc (N.card : ℝ) * (3 * Real.log (2*r))
          ≤ 5*A'*r*Real.log (2*r) * (3 * Real.log (2*r)) :=
            mul_le_mul_of_nonneg_right hNcard (by positivity)
        _ = 15*A'*r*(Real.log (2*r))^2 := by ring
        _ ≤ 15*A'*r*(16 * Real.sqrt (2*r)) :=
            mul_le_mul_of_nonneg_left
              (gapsw80_t59_sq_log_two_mul_le hr2) (by positivity)
        _ ≤ 15*A'*r*(16 * (2 * Real.sqrt r)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hs2rle (by norm_num)) (by positivity)
        _ = 480*A'*r*Real.sqrt r := by ring
    have h2 : (N.card : ℝ) * |Real.log δ|
        ≤ 20 * A' * |Real.log δ| * r * Real.sqrt r := by
      have hstep : Real.log (2*r) ≤ 4 * Real.sqrt r :=
        hlog2r_le.trans (by linarith [hs2rle])
      calc (N.card : ℝ) * |Real.log δ|
          ≤ 5*A'*r*Real.log (2*r) * |Real.log δ| :=
            mul_le_mul_of_nonneg_right hNcard (abs_nonneg _)
        _ ≤ 5*A'*r*(4 * Real.sqrt r) * |Real.log δ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hstep hA'r0) (abs_nonneg _)
        _ = 20*A'*(|Real.log δ|)*r*Real.sqrt r := by ring
    have h3 : r * ∑ j ∈ N, ‖ρ j‖⁻¹ ≤ 2*T*r*Real.sqrt r := by
      calc r * ∑ j ∈ N, ‖ρ j‖⁻¹
          ≤ r * (Real.sqrt (2*r) * T) :=
            mul_le_mul_of_nonneg_left hNinv_sum hr0.le
        _ ≤ r * (2 * Real.sqrt r * T) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hs2rle hT0) hr0.le
        _ = 2*T*r*Real.sqrt r := by ring
    have h4 : -(N.card : ℝ) * |Real.log δ| ≤ (N.card : ℝ) * Real.log δ := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log δ))
        (show (0:ℝ) ≤ (N.card:ℝ) from Nat.cast_nonneg _)
      linarith [this]
    nlinarith [h1, h2, h3, h4]

  have hnear_prod : ‖∏ j ∈ N, F j‖ = Real.exp (∑ j ∈ N, Real.log ‖F j‖) := by
    rw [norm_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun j hj => (Real.exp_log (hFpos j hj)).symm

  have hnear_bd : Real.exp (-((480*A' + 20*A'*|Real.log δ| + 2*T) * r * Real.sqrt r))
      ≤ ‖∏ j ∈ N, F j‖ := by
    rw [hnear_prod]; exact Real.exp_le_exp.mpr hnear_sum
  calc Real.exp (-((K' + 480*A' + 20*A'*|Real.log δ| + 2*T) * r * Real.sqrt r))
      = Real.exp (-((480*A' + 20*A'*|Real.log δ| + 2*T) * r * Real.sqrt r))
          * Real.exp (-(K' * r * Real.sqrt r)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ ‖∏ j ∈ N, F j‖
          * ‖∏' j : {j | 2*r < ‖ρ j‖}, F (j:ℕ)‖ :=
        mul_le_mul hnear_bd hfar_bd (Real.exp_pos _).le (norm_nonneg _)

end FLT.Gapsw80T59D1b0a2aiBBetaMinModulusAssemblyProof
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

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
p2m_open "NumberField P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.NumberField.InfinitePlace Module P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Module Complex P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.Complex"

set_option maxHeartbeats 6400000 in

theorem gapsw80_t62_D1_closed : gapsw80_t19_XiLogDerivZeroExpansion := by
  have _em := Classical.em

  have hD1a : gapsw80_t31_XiZerosInOpenStrip :=
    gapsw80_t32_D1a_of_D1aSub
      (gapsw80_t33_D1ap_of_D1apa
        (gapsw80_t34_D1apa_of_D1apa0 gapsw80_t35_D1apa0_closed))
      gapsw80_t36_D1app_closed

  have hD1b0a1 := gapsw80_t44_D1b0a1_of_abc
    (gapsw80_t47_D1b0a1a_of_i_ii
      gapsw80_t48_D1b0a1ai_closed gapsw80_t49_D1b0a1aii_closed)
    gapsw80_t45_D1b0a1b_closed gapsw80_t46_D1b0a1c_closed
  have hD1b0a2 := gapsw80_t50_D1b0a2_of_D1b0a2ab
    (gapsw80_t52_D1b0a2a_of_D1b0a2ai_ii
      (gapsw80_t54_D1b0a2ai_of_D1b0a2aiA_iB gapsw80_t55_D1b0a2aiA_closed
        (gapsw80_t56_D1b0a2aiB_of_far_near_cartan
          gapsw80_t58_farTailProductLowerBound_proof
          gapsw80_t59_minModulusFromFarAndGoodRadius_proof
          gapsw80_t57_cartanGoodRadiusExists_proof))
      gapsw80_t53_entireGrowthFromAnnulusCircles)
    gapsw80_t51_D1b0a2b_closed
  have hD1b : gapsw80_t31_HadamardLogDerivExpansion :=
    gapsw80_t37_D1b_of_D1b0_D1b1
      (gapsw80_t39_D1b0_of_D1b0a_D1b0b
        (gapsw80_t41_D1b0a_of_D1b0a012
          (gapsw80_t42_D1b0a0_closed gapsw80_t43_SL_closed)
          hD1b0a1 hD1b0a2)
        gapsw80_t40_D1b0b_closed)
      gapsw80_t38_D1b1_closed
  exact gapsw80_t31_D1_of_D1ab hD1a hD1b

end FLT.Gapsw80T62ArchGammaKernelRemintWire
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

end
p2m_reactivate "P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.FLT.Gapsw80T30D2d0cLocalEulerFactorProof"

open FLT.Gapsw80T62ArchGammaKernelRemintWire FLT.Gapsw80T19B2ppHadamardDecomp FLT.Gapsw80T9ClassSumA1Closure in
theorem solution
    (K : Type) [Field K] [NumberField K] (Λ : ℂ → ℂ)
    (hΛdiff : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (hΛFE : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s)
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s)
    (hB1 : ∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖)
    (hEnd : ∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0)
    (hSL : ∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖) :
    ∃ (B : ℂ) (ρ : ℕ → ℂ),
      (∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1) ∧
      Summable (fun j => (Complex.normSq (ρ j))⁻¹) ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 → (∀ j, s ≠ ρ j) →
        logDeriv (fun z => z * (z - 1) * Λ z) s = B + ∑' j, ((s - ρ j)⁻¹ + (ρ j)⁻¹) := by
  letI : S18.HADPkg K := ⟨Λ, hΛdiff, hΛFE, hΛeq, hB1, hEnd, hSL⟩
  exact gapsw80_t62_D1_closed K

end S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package
end P2MW
export P2MW.S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package (solution)
