-- Prove2me | solution 1 for NumberField.exists_completedDedekindZeta_package
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4aa3dcd1-3eff-50c9-a6bc-de104c6e2762

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_completedDedekindZeta_package

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

namespace Asymptotics
p2m_export "Asymptotics" "IsBigO IsBigO.of_bound isBigO_atTop_natCast_rpow_of_tendsto_div_rpow"
p2m_open "Asymptotics"
end Asymptotics
namespace Classical
p2m_export "Classical" "choose_spec em by_cases choose"
p2m_open "Classical"
end Classical
namespace Complex
p2m_export "Complex" "ofReal_sub log_exp one_re continuous_re measurable_ofReal add_conj one_cpow re sqrt norm_cpow_eq_rpow_re_of_pos re_ofNat ofReal_re add_re ofRealHom sqrt_one natCast_im ofReal_ne_zero lift norm_real intCast_im ofReal_tsum ofReal_prod real_smul one_im im_ofNat ofReal_inv ofReal_zpow cpow_ne_zero_iff re_le_norm Gammaℝ re_sum add_im ofReal_natCast norm_natCast ofReal_eq_one Gamma_nat_eq_factorial re_ofReal_mul ofReal_sum cpow_one Gamma_eq_integral ofReal_neg im hasSum_iff ofReal_intCast exp_sum Gamma_ne_zero normSq_eq_norm_sq ofReal_pow arg log_inv Gamma_ofReal hasSum_re I_sq ofReal_eq_zero normSq_apply Gamma rank_real_complex cpow_zero cpow_neg cpow_natCast exists mk.injEq ofReal ofReal_zero ofReal_mul exp_neg intCast_re im_sum neg_re sub_re inv_cpow I_re div_ofNat_re cpow_add continuous_exp coe_smul cpow_nat_mul' mul_cpow_ofReal_nonneg exp mk arg_ofReal_of_nonneg norm_exp pos_iff sub_im ofReal_add Gammaℝ_ne_zero_of_re_pos exp_zero measurable_exp ofReal_div cpow exp_log natCast_re cpow_intCast Gammaℂ ofReal_cpow continuous_ofReal cpow_neg_one log_zero I_im tsum_exp_neg_quadratic cpow_nat_mul ofReal_one mul_re im_ofReal_mul log_mul GammaIntegral ofReal_im log Gammaℝ_def ofReal_ofNat ofReal_exp div_re Gammaℂ_def ext I Gamma_add_one exp_nat_mul I_mul_I normSq_ofNat mul_im measurable_log hasDerivAt_log exp_add"
p2m_open "Complex"
end Complex
namespace ContinuousLinearMap
p2m_export "ContinuousLinearMap" "proj coe_mk zero_apply apply toLinearMap smulRight_apply comp add coe_proj zero det_pi coe_coe sub_apply mk.injEq restrict bound det snd one_apply mul_apply pi comp_apply sub smul_apply neg smulRight ext sum_apply coe_pi single inl neg_apply ring coe_smul add_apply proj_pi single_apply inr mul mk coe_comp"
p2m_open "ContinuousLinearMap"
end ContinuousLinearMap
namespace ENNReal
p2m_export "ENNReal" "ofReal_pow tsum_const ofReal_zero log_rpow ofReal_ofNat ofReal_add coe_smul ofReal_eq_one ofReal_ne_top ofReal_le_ofReal log_zero continuous_ofReal rpow_two log_inv toReal_mono summable_toReal coe_finset_sum ofReal_pos rpow_neg_one ofReal_mul smul_def continuous_sub_right one_le_rpow inv_rpow toReal_one one_ne_top add_left_inj toReal_prod rpow_le_rpow_of_exponent_ge mul_pos eq_div_iff zpow_pos ofReal_lt_top prod_lt_top log one_lt_two log_pow div_eq_zero_iff tsum_eq_add_tsum_ite measurable_ofReal ofReal_natCast exp_log continuous_exp rpow_le_rpow_of_exponent_le ofReal_prod_of_nonneg log_le_log rpow_one ofReal_tsum_of_nonneg rpow_natCast ofReal_sub measurable_log ofReal_eq_zero one_lt_top toReal_ofReal ofReal_one Icc_mem_nhds rpow_mul rpow_neg"
p2m_open "ENNReal"
end ENNReal
namespace FLT
namespace KwDyf2RealGammaLogBound
end FLT.KwDyf2RealGammaLogBound
namespace FLT
namespace KwDyf2XiEntireOrderDecomp
end FLT.KwDyf2XiEntireOrderDecomp
namespace FLT
namespace KwDyf2XiOrderBoundDecomp
end FLT.KwDyf2XiOrderBoundDecomp
namespace FLT
namespace KwDyf2XiStripBoundAttack
end FLT.KwDyf2XiStripBoundAttack
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
namespace Gapsw80T15XiOrderOneB1Decomp
end FLT.Gapsw80T15XiOrderOneB1Decomp
namespace FLT
namespace Gapsw80T16XiRightHalfBoundProof
end FLT.Gapsw80T16XiRightHalfBoundProof
namespace FLT
namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition
end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
namespace FLT
namespace Gapsw80T21D2SubDecompWire
end FLT.Gapsw80T21D2SubDecompWire
namespace FLT
namespace Gapsw80T25B4pppStripSinglePointAbsorption
end FLT.Gapsw80T25B4pppStripSinglePointAbsorption
namespace FLT
namespace Gapsw80T2RankNGaussianPoisson
end FLT.Gapsw80T2RankNGaussianPoisson
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
namespace Gapsw80T3IdealLatticeThetaTransformation
end FLT.Gapsw80T3IdealLatticeThetaTransformation
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
namespace Gapsw80T4MultiVarIdealThetaTransformation
end FLT.Gapsw80T4MultiVarIdealThetaTransformation
namespace FLT
namespace Gapsw80T5HeckeThetaKernel
end FLT.Gapsw80T5HeckeThetaKernel
namespace FLT
namespace Gapsw80T6TraceDualBridge
end FLT.Gapsw80T6TraceDualBridge
namespace FLT
namespace Gapsw80T7ClosedFEWeakPair
end FLT.Gapsw80T7ClosedFEWeakPair
namespace FLT
namespace Gapsw80T8MellinGammaPartialZeta
end FLT.Gapsw80T8MellinGammaPartialZeta
namespace FLT
namespace Gapsw80T9ClassSumA1Closure
end FLT.Gapsw80T9ClassSumA1Closure
namespace Filter
p2m_export "Filter" "mem_bot ker mk pi Tendsto pi_mono atTop EventuallyEq.rfl eventually_gt_atTop eventually_of_mem unique mk.injEq EventuallyEq map eventually_ge_atTop Eventually.of_forall"
p2m_open "Filter"
end Filter
namespace FourierTransform
p2m_export "FourierTransform" "mk"
p2m_open "FourierTransform"
end FourierTransform
namespace Ideal
p2m_export "Ideal" "absNorm_span_singleton absNorm_eq_zero_iff pi mem_bot span prod Quotient.mk map span_singleton_eq_top absNorm_ne_zero_iff_mem_nonZeroDivisors ext absNorm Quotient.lift finite_setOf_absNorm_eq card_norm_le_eq_card_norm_le_add_one subset_span absNorm_ne_zero_of_nonZeroDivisors absNorm_eq_one_iff"
p2m_open "Ideal"
end Ideal
namespace InnerProductSpace
p2m_export "InnerProductSpace" "mk"
p2m_open "InnerProductSpace"
end InnerProductSpace
namespace Matrix
p2m_export "Matrix" "PosDef.diagonal vecMul_fromBlocks det_smul J stdBasis transpose_one diagonal_one reindex diagonal_eq_diagonal_iff invOf_eq_nonsing_inv ext diagonal_transpose add sub_apply vecMul_sub map_apply smul_mulVec det_diagonal det_reindex_self sub zero fromBlocks_apply₁₁ exp_neg fromBlocks_apply₂₂ conjTranspose_eq_transpose_of_trivial det_one repr fromBlocks₂₂Invertible one_mulVec gram dotProduct_mulVec fromBlocks_apply₁₂ det_fin_zero IsHermitian transpose_apply fromBlocks_mulVec gram_eq_conjTranspose_mul nonsing_inv_mul transpose_transpose comp submatrix_apply isUnit_iff_isUnit_det toBlocks₂₂ add_mulVec fromBlocks_apply₂₁ det_transpose neg det_apply fromBlocks rank smul inv_eq_right_inv mulVec_mulVec det_mul zero_apply of_apply posDef_gram_of_linearIndependent single det_fromBlocks₂₂ posDef_iff_dotProduct_mulVec isHermitian_fromBlocks_iff mulVec_diagonal mulVec_injective_of_isUnit mulVec_sub ext_iff diagonal_mul one_apply mulVec_transpose neg_apply smul_apply toBlocks₁₂ PosDef vecMul_transpose toBlocks₂₁ det neg_mulVec toBlocks₁₁ diagonal inv_reindex add_apply comp_apply of smul_mul sum_apply transpose_smul fromBlocks_toBlocks inv invertibleOfIsUnitDet zpow_add_one map mulVec_zero discr single_apply mul_apply unique transpose_sub trace invOf_fromBlocks₂₂_eq transpose_mul vecMul_vecMul mulVec_smul transpose_nonsing_inv diagonal_mul_diagonal reindex_apply mul_inv_rev mulVec add_vecMul"
p2m_open "Matrix"
end Matrix
namespace MeasureTheory
p2m_export "MeasureTheory" "HasFiniteIntegral Measure.quasiMeasurePreserving_snd Measure.restrict_apply_univ Measure.smul_absolutelyContinuous integrable_const volume_preserving_piUnique lintegral_image_eq_lintegral_abs_det_fderiv_mul Measure Measure.volume_eq_prod setIntegral_congr_fun continuousOn_of_dominated MeasurePreserving lintegral_comp hasFiniteIntegral_iff_enorm integral_sub lintegral_prod integral_nonneg lintegral_congr measure_preimage_add integral_tsum setIntegral_const measurePreserving_vadd withDensity_absolutelyContinuous IntegrableOn volume_pi lintegral_withDensity_eq_lintegral_mul norm_setIntegral_le_of_norm_le_const Measure.prod_restrict Measure.ext_of_lintegral Measure.pi Measure.pi_pi ae_restrict_mem integrableOn_const Measure.measurePreserving_neg Measure.map enorm_integral_le_lintegral_enorm setIntegral_prod IsAddFundamentalDomain covolume IsFiniteMeasure lintegral_mono HasFiniteIntegral.mono' setLIntegral_univ setLIntegral_congr_fun AEStronglyMeasurable.tsum lintegral_map integral_fintype_prod_eq_prod integral_smul_measure VAddInvariantMeasure measureReal_def lintegral_tsum MeasurePreserving.id setIntegral_mono_on norm_integral_le_integral_norm ae_restrict_of_forall_mem Integrable lintegral_mono_ae lintegral_smul_measure setLIntegral_prod Measure.restrict_univ integral_add integral_const_mul integral_map AEStronglyMeasurable ofReal_integral_eq_lintegral_ofReal volume_preserving_piEquivPiSubtypeProd lintegral_const_mul' integrable_const_iff Measure.restrict_pi_pi ae_of_all"
p2m_open "MeasureTheory"
end MeasureTheory
namespace Module
p2m_export "Module" "Basis.map_repr Basis.coe_span_apply Basis.mem_span_iff_repr_mem Basis.repr_reindex_apply Free.ChooseBasisIndex Basis.span finrank_eq_card_basis Basis.toMatrix_apply finrank Free mk Finite.of_injective Basis.equivFun_symm_apply Basis.det_apply Basis.map_apply Basis.coe_reindex finrank_pos finrank_eq_card_chooseBasisIndex Basis"
p2m_open "Module"
end Module
namespace Nat
p2m_export "Nat" "cast_nonneg cast_ne_zero log_pos floor_le lt_floor_add_one card_eq_fintype_card log_pow log sqrt_one le_floor div_pos one_lt_ofNat add_le_add succ sqrt_pos card_eq_zero coe_castRingHom cast_sum factorial_le choose cast_eq_zero cast_natAbs cast_sub card_ne_zero card_univ sqrt cast_injective sqrt_le_sqrt zero_le eq_zero_or_pos cast_pos cast_le ne_of_gt card_fin cast_ofNat castRingHom one_le_cast pred sub_le succ_le_succ one_le_iff_ne_zero card_congr pow_succ' factorial_le_pow zero mul_eq_zero cast_one factorial_pos dist_zero_right"
p2m_open "Nat"
end Nat
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"
p2m_open "NumberField"
end NumberField
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"
namespace InfinitePlace
p2m_export "NumberField.InfinitePlace" "nrRealPlaces mult_isReal embedding_of_isReal_apply IsReal IsComplex smul_apply mult_isComplex card_eq_nrRealPlaces_add_nrComplexPlaces not_isComplex_iff_isReal mult_pos mult mk embedding_of_isReal not_isReal_iff_isComplex ext nrComplexPlaces pos_iff isReal_or_isComplex apply prod_eq_prod_mul_prod card_add_two_mul_card_eq_rank embedding"
p2m_open "NumberField.InfinitePlace NumberField"
end NumberField.InfinitePlace
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"
namespace Units
p2m_export "NumberField.Units" "fundSystem pos_at_place rank regulator_pos torsionOrder equivFinRank exist_unique_eq_mul_prod mem_torsion torsion coe_coe regulator torsionOrder_pos"
p2m_open "NumberField.Units NumberField"
end NumberField.Units
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"
namespace Units
p2m_export "NumberField.Units" "fundSystem pos_at_place rank regulator_pos torsionOrder equivFinRank exist_unique_eq_mul_prod mem_torsion torsion coe_coe regulator torsionOrder_pos"
namespace dirichletUnitTheorem
p2m_export "NumberField.Units.dirichletUnitTheorem" "w₀ logSpace"
p2m_open "NumberField.Units.dirichletUnitTheorem NumberField.Units NumberField"
end NumberField.Units.dirichletUnitTheorem
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"
namespace mixedEmbedding
p2m_export "NumberField.mixedEmbedding" "indexEquiv mem_idealLattice covolume_idealLattice euclidean.toMixed index norm_real euclidean.stdOrthonormalBasis normAtAllPlaces indexEquiv_apply_isComplex_snd mixedEmbedding_apply_isComplex euclidean.stdOrthonormalBasis_map_eq volume_fundamentalDomain_stdBasis fundamentalCone idealLattice normAtPlace norm_eq_norm fractionalIdealLatticeBasis normAtPlace_nonneg stdBasis_apply_isReal mixedSpace mixedEmbedding_apply_isReal indexEquiv_apply_isReal euclidean.mixedSpace stdBasis unitSMul_smul indexEquiv_apply_isComplex_fst stdBasis_apply_isComplex_snd normAtPlace_apply fractionalIdealLatticeBasis_apply span_idealLatticeBasis normAtAllPlaces_apply normAtPlace_apply_of_isReal norm_smul stdBasis_apply_isComplex_fst realSpace normAtPlace_apply_of_isComplex"
p2m_open "NumberField.mixedEmbedding NumberField"
end NumberField.mixedEmbedding
namespace NumberField
p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"
namespace mixedEmbedding
p2m_export "NumberField.mixedEmbedding" "indexEquiv mem_idealLattice covolume_idealLattice euclidean.toMixed index norm_real euclidean.stdOrthonormalBasis normAtAllPlaces indexEquiv_apply_isComplex_snd mixedEmbedding_apply_isComplex euclidean.stdOrthonormalBasis_map_eq volume_fundamentalDomain_stdBasis fundamentalCone idealLattice normAtPlace norm_eq_norm fractionalIdealLatticeBasis normAtPlace_nonneg stdBasis_apply_isReal mixedSpace mixedEmbedding_apply_isReal indexEquiv_apply_isReal euclidean.mixedSpace stdBasis unitSMul_smul indexEquiv_apply_isComplex_fst stdBasis_apply_isComplex_snd normAtPlace_apply fractionalIdealLatticeBasis_apply span_idealLatticeBasis normAtAllPlaces_apply normAtPlace_apply_of_isReal norm_smul stdBasis_apply_isComplex_fst realSpace normAtPlace_apply_of_isComplex"
namespace fundamentalCone
p2m_export "NumberField.mixedEmbedding.fundamentalCone" "prod_expMapBasis_pow expMapBasis_apply completeBasis_apply_of_ne expMap_target expMap_apply setLIntegral_expMapBasis_image expMapBasis_pos expMapBasis_apply' expMap equivFinRank completeBasis continuous_expMapBasis expMapBasis expMap_add"
p2m_open "NumberField.mixedEmbedding.fundamentalCone NumberField.mixedEmbedding NumberField"
end NumberField.mixedEmbedding.fundamentalCone
namespace Real
p2m_export "Real" "sqrt_pos log_le_sub_one_of_pos log_pos continuous_const_rpow norm volume_Ico norm_natCast log_nonneg exp_zero sqrt_le_sqrt rpow_mul pi_ne_zero pi_gt_three rpow_nonneg log_zero continuousOn_log log_exp measurable_exp sqrt_sq_eq_abs Gamma convexOn_log_Gamma log_inv two_le_pi Gamma_nat_eq_factorial exp_nat_mul exp_one_lt_d9 exp Gamma_ne_zero tendsto_log_atTop rpow_two exp_pos exp_le_exp sqrt_nonneg exp_nonneg measurable_log pi_nonneg rpow_le_rpow_of_exponent_le rpow_neg_one exp_sum rpow_neg log_rpow sqrt_one rpow_pos_of_pos rpow_natCast continuousAt_rpow_const continuous_exp log norm_of_nonneg norm_eq_abs exp_neg inv_rpow inner_apply mk pi_pos exp_log Gamma_eq_integral Gamma_add_one log_mul summable_abs_int_rpow rpow_one sq_sqrt log_le_log one_le_rpow mul_rpow rpow_le_rpow_of_exponent_ge hasDerivAt_log le_log_iff_exp_le add_one_le_exp exp_add sqrt_sq log_pow log_div sqrt"
p2m_open "Real"
end Real
namespace RealInnerProductSpace
p2m_open "RealInnerProductSpace"
end RealInnerProductSpace
namespace Set
p2m_export "Set" "eq_univ_of_forall exists_min_image restrict prod_pow indicator_apply univ_nonempty Icc diagonal Icc_succ_left_eq_Ioc mem_compl_iff ext univ_prod finite_singleton coe_eq_subtype mem_univ_pi pi Ioc unit card_singleton MapsTo mem_singleton_iff mem_univ pi_mono Ioi EqOn mem_Ici prod_insert mapsTo_univ Countable.isConnected_compl_of_one_lt_rank mem_singleton InjOn Ici mem_setOf_eq Ico_subset_Icc_self mem_insert_iff univ Ico mem_insert prod prod_empty range mem_Ioi mem_iInter"
p2m_open "Set"
end Set
namespace Topology
p2m_open "Topology"
end Topology
namespace WithLp
p2m_export "WithLp" "toLp ofLp"
p2m_open "WithLp"
end WithLp

section

set_option maxHeartbeats 6400000

p2m_open "Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology FourierTransform P2MW.S_NumberField_exists_completedDedekindZeta_package.FourierTransform RealInnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.RealInnerProductSpace ENNReal P2MW.S_NumberField_exists_completedDedekindZeta_package.ENNReal"
p2m_open "_root_.Complex~exp"
p2m_open "WithLp P2MW.S_NumberField_exists_completedDedekindZeta_package.WithLp"

noncomputable section

namespace FLT
namespace GaussianFourierPosDef

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

lemma dotProduct_ofLp_eq_inner (x y : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ ofLp y = ⟪x, y⟫ := by
  simp [dotProduct, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

lemma dotProduct_mulVec_eigen (hA : A.PosDef)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) {μ : Fin n → ℝ}
    (hMb : ∀ j, M *ᵥ ofLp (hA.1.eigenvectorBasis j) = μ j • ofLp (hA.1.eigenvectorBasis j))
    (x : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ M *ᵥ ofLp x = ∑ i, μ i * (ofLp (hA.1.eigenvectorBasis.repr x) i) ^ 2 := by
  classical
  set bs := hA.1.eigenvectorBasis with hbs
  set w : EuclideanSpace ℝ (Fin n) := toLp 2 (M *ᵥ ofLp x) with hw
  have hcoe : ofLp w = M *ᵥ ofLp x := rfl
  have hMT : Mᵀ = M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hM
  have h1 : ofLp x ⬝ᵥ M *ᵥ ofLp x = ⟪w, x⟫ := by
    rw [← dotProduct_ofLp_eq_inner, hcoe, dotProduct_comm]
  have h2 : ⟪w, x⟫ = ∑ i, ofLp (bs.repr w) i * ofLp (bs.repr x) i := by
    rw [← LinearIsometryEquiv.inner_map_map bs.repr w x, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h3 : ∀ i, ofLp (bs.repr w) i = μ i * ofLp (bs.repr x) i := by
    intro i
    have hr : ofLp (bs.repr w) i = ⟪bs i, w⟫ := bs.repr_apply_apply w i
    have hr' : ofLp (bs.repr x) i = ⟪bs i, x⟫ := bs.repr_apply_apply x i
    rw [hr, hr', ← dotProduct_ofLp_eq_inner, ← dotProduct_ofLp_eq_inner, hcoe,
      dotProduct_mulVec, ← Matrix.mulVec_transpose, hMT, hMb i, smul_dotProduct]
    rfl
  rw [h1, h2]
  exact Finset.sum_congr rfl fun i _ => by rw [h3 i]; ring

lemma quadForm_eq_sum_eigen (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    ofLp x ⬝ᵥ A *ᵥ ofLp x
      = ∑ i, hA.1.eigenvalues i * (ofLp (hA.1.eigenvectorBasis.repr x) i) ^ 2 :=
  dotProduct_mulVec_eigen hA hA.1 (hA.1.mulVec_eigenvectorBasis) x

section MainComputation

variable {t : ℝ}

end MainComputation

section SATInstances

end SATInstances

section Falsifier

end Falsifier

end FLT.GaussianFourierPosDef

end

end

section

namespace FLT
namespace Gapsw80T15XiOrderOneB1Decomp

open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp

set_option maxHeartbeats 3200000 in

theorem gapsw80_t15_norm_ge_two_ne_zero_one {s : ℂ} (hs : 2 ≤ ‖s‖) :
    s ≠ 0 ∧ s ≠ 1 := by
  have _em := Classical.em
  constructor
  · intro h; rw [h, norm_zero] at hs; linarith
  · intro h; rw [h, norm_one] at hs; linarith

set_option maxHeartbeats 3200000 in

theorem gapsw80_t15_sat_polynomialFactor_orderBound :
    ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖s * (s - 1)‖ ≤ 2 * ‖s‖ * Real.log ‖s‖ := by
  have _em := Classical.em
  intro s hs
  obtain ⟨h0, h1⟩ := gapsw80_t15_norm_ge_two_ne_zero_one hs
  have hns : (0:ℝ) < ‖s‖ := lt_of_lt_of_le (by norm_num) hs
  have hprod_pos : (0:ℝ) < ‖s * (s - 1)‖ := by
    rw [norm_mul]
    exact mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr (sub_ne_zero.mpr h1))

  have hub : ‖s * (s - 1)‖ ≤ 2 * ‖s‖ ^ 2 := by
    rw [norm_mul, sq]
    have hs1 : ‖s - 1‖ ≤ 2 * ‖s‖ :=
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le s 1
        _ = ‖s‖ + 1 := by rw [norm_one]
        _ ≤ ‖s‖ + ‖s‖ := by linarith
        _ = 2 * ‖s‖ := by ring
    nlinarith [norm_nonneg s]

  have hlog1 : Real.log ‖s * (s - 1)‖ ≤ Real.log (2 * ‖s‖ ^ 2) :=
    Real.log_le_log hprod_pos hub
  have hlog2 : Real.log (2 * ‖s‖ ^ 2) = Real.log 2 + 2 * Real.log ‖s‖ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring

  have hlogs : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hs
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : Real.log 2 + 2 * Real.log ‖s‖ ≤ 2 * ‖s‖ * Real.log ‖s‖ := by
    have hprod : (1:ℝ) * Real.log 2 ≤ (‖s‖ - 1) * Real.log ‖s‖ :=
      mul_le_mul (by linarith) hlogs hlog2_pos.le (by linarith)
    nlinarith [hprod]
  linarith

end FLT.Gapsw80T15XiOrderOneB1Decomp

end

section

namespace FLT
namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition

open FLT.Gapsw48T2OdlyzkoDeg24PinCarrier
open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex"

noncomputable def gapsw80_t1_completedDedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|discr K| : ℤ) : ℂ)) ^ (s / 2)
    * Gammaℝ s ^ nrRealPlaces K
    * Gammaℂ s ^ nrComplexPlaces K
    * dedekindZeta K s

def gapsw80_t1_DedekindCompletedFE : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ {(0 : ℂ), 1}ᶜ ∧
      (∀ s : ℂ, 1 < s.re → Λ s = gapsw80_t1_completedDedekindZeta K s) ∧
      (∀ s : ℂ, Λ (1 - s) = Λ s)

end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

end

section

set_option maxHeartbeats 6400000

noncomputable section

namespace FLT
namespace Gapsw80T3IdealLatticeThetaTransformation

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T2RankNGaussianPoisson Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

abbrev nK := finrank ℚ K

def eIdx : index K ≃ Fin (nK K) :=
  Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_basis (stdBasis K), mixedEmbedding.finrank])

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def eI : Free.ChooseBasisIndex ℤ (I : FractionalIdeal (𝓞 K)⁰ K) ≃ Fin (nK K) :=
  Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank, RingOfIntegers.rank])

def latE (i : Fin (nK K)) : euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm (fractionalIdealLatticeBasis K I ((eI K I).symm i))

theorem latE_linearIndependent : LinearIndependent ℝ (latE K I) := by
  have h := (fractionalIdealLatticeBasis K I).linearIndependent
  have h' := h.map' (euclidean.toMixed K).symm.toLinearMap
    (LinearEquiv.ker _)
  exact h'.comp _ (eI K I).symm.injective

theorem fILB_linearIndependent_int :
    LinearIndependent ℤ (⇑(fractionalIdealLatticeBasis K I)) :=
  (fractionalIdealLatticeBasis K I).linearIndependent.restrict_scalars
    (by simp only [zsmul_one]; exact Int.cast_injective)

def idealZBasis : Basis (Fin (nK K)) ℤ (mixedEmbedding.idealLattice K I) :=
  ((Basis.span (fILB_linearIndependent_int K I)).map
      (LinearEquiv.ofEq _ _ (span_idealLatticeBasis K I))).reindex (eI K I)

@[scoped simp]
theorem idealZBasis_apply (i : Fin (nK K)) :
    (idealZBasis K I i : mixedSpace K)
      = fractionalIdealLatticeBasis K I ((eI K I).symm i) := by
  have h : ((Basis.span (fILB_linearIndependent_int K I)) ((eI K I).symm i) : mixedSpace K)
      = fractionalIdealLatticeBasis K I ((eI K I).symm i) :=
    Basis.coe_span_apply _ _
  simp only [idealZBasis, Basis.coe_reindex, Function.comp_apply, Basis.map_apply]
  exact h

def gapsw80_t3_idealGram : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.gram ℝ (latE K I)

theorem gapsw80_t3_idealGram_posDef : (gapsw80_t3_idealGram K I).PosDef :=
  Matrix.posDef_gram_of_linearIndependent (latE_linearIndependent K I)

def stdONBFin : OrthonormalBasis (Fin (nK K)) ℝ (euclidean.mixedSpace K) :=
  (euclidean.stdOrthonormalBasis K).reindex (eIdx K)

def stdBasisFin : Basis (Fin (nK K)) ℝ (mixedSpace K) :=
  (mixedEmbedding.stdBasis K).reindex (eIdx K)

theorem stdBasisFin_repr_eq (x : mixedSpace K) (i : Fin (nK K)) :
    (stdBasisFin K).repr x i
      = (stdONBFin K).repr ((euclidean.toMixed K).symm x) i := by
  simp only [stdBasisFin, stdONBFin, Basis.repr_reindex_apply,
    OrthonormalBasis.repr_reindex, ← euclidean.stdOrthonormalBasis_map_eq K,
    Basis.map_repr, LinearEquiv.trans_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  rfl

def coordMatrix : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.of fun i j => (stdONBFin K).repr (latE K I j) i

theorem gapsw80_t3_idealGram_eq_transpose_mul :
    gapsw80_t3_idealGram K I = (coordMatrix K I)ᵀ * (coordMatrix K I) := by
  have h := Matrix.gram_eq_conjTranspose_mul (stdONBFin K) (latE K I)
  simpa only [gapsw80_t3_idealGram, coordMatrix, Matrix.conjTranspose_eq_transpose_of_trivial]
    using h

theorem coordMatrix_eq_toMatrix :
    coordMatrix K I = (stdBasisFin K).toMatrix (fun i => ↑(idealZBasis K I i)) := by
  ext i j
  rw [coordMatrix, Matrix.of_apply, Basis.toMatrix_apply, idealZBasis_apply,
    stdBasisFin_repr_eq]
  rfl

theorem volume_fundamentalDomain_stdBasisFin :
    MeasureTheory.volume.real (ZSpan.fundamentalDomain (stdBasisFin K)) = 1 := by
  rw [stdBasisFin, ZSpan.fundamentalDomain_reindex, MeasureTheory.measureReal_def,
    volume_fundamentalDomain_stdBasis, ENNReal.toReal_one]

theorem abs_det_coordMatrix :
    |(coordMatrix K I).det| = ZLattice.covolume (mixedEmbedding.idealLattice K I) := by
  have h := ZLattice.covolume_eq_det_mul_measureReal
    (b := idealZBasis K I) (b₀ := stdBasisFin K)
  rw [volume_fundamentalDomain_stdBasisFin, mul_one] at h
  rw [coordMatrix_eq_toMatrix, ← Basis.det_apply]
  exact h.symm

def zEquiv : (Fin (nK K) → ℤ) ≃ₗ[ℤ] mixedEmbedding.idealLattice K I :=
  (idealZBasis K I).equivFun.symm

theorem coe_zEquiv_apply (v : Fin (nK K) → ℤ) :
    (zEquiv K I v : mixedSpace K)
      = ∑ i, (v i : ℝ) • fractionalIdealLatticeBasis K I ((eI K I).symm i) := by
  have h := (idealZBasis K I).equivFun_symm_apply v
  calc (zEquiv K I v : mixedSpace K)
      = ((∑ i, v i • idealZBasis K I i : idealLattice K I) : mixedSpace K) := by rw [zEquiv, h]
    _ = ∑ i, v i • (idealZBasis K I i : mixedSpace K) := by push_cast; ring_nf
    _ = ∑ i, (v i : ℝ) • fractionalIdealLatticeBasis K I ((eI K I).symm i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [idealZBasis_apply, ← Int.cast_smul_eq_zsmul ℝ]

section Census

end Census

end FLT.Gapsw80T3IdealLatticeThetaTransformation
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section

set_option maxHeartbeats 6400000

p2m_open "Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix"
p2m_open_scoped "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix"

namespace FLT
namespace Gapsw80T2RankNGaussianPoisson

noncomputable section

variable {n : ℕ}

abbrev zcastR (v : Fin n → ℤ) : Fin n → ℝ := fun i => (v i : ℝ)

abbrev rQuad (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ := v ⬝ᵥ (A *ᵥ v)

abbrev cQuad (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ := v ⬝ᵥ (A *ᵥ v)

abbrev liftC (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map ((↑) : ℝ → ℂ)

def thetaTerm (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ)
    (v : Fin n → ℤ) : ℂ :=
  cexp (-(π : ℂ) * (t : ℂ) * (rQuad A (zcastR v) : ℂ) + 2 * π * ∑ i, b i * (v i : ℂ))

def dualTerm (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ)
    (w : Fin n → ℤ) : ℂ :=
  cexp (-(π : ℂ) / (t : ℂ) *
    cQuad (liftC A⁻¹) (fun i => (w i : ℂ) + Complex.I * b i))

def PoissonLaw (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (b : Fin n → ℂ) : Prop :=
  (∑' v, thetaTerm A t b v)
    = (((t ^ n * A.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, dualTerm A t b w

section Summability

theorem gapsw80_t2_posDef_quadForm_lower {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ rQuad A x := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hE | hNE
  · exact ⟨1, one_pos, fun x => by simp [rQuad, dotProduct]⟩
  obtain ⟨i₀, hmin⟩ := Finite.exists_min hA.1.eigenvalues
  refine ⟨hA.1.eigenvalues i₀, hA.eigenvalues_pos i₀, fun x => ?_⟩
  have hquad :=
    FLT.GaussianFourierPosDef.quadForm_eq_sum_eigen hA (WithLp.toLp 2 x)
  have hxx : x ⬝ᵥ x
      = ∑ i, (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 := by
    have h1 : x ⬝ᵥ x = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 x) :=
      FLT.GaussianFourierPosDef.dotProduct_ofLp_eq_inner
        (WithLp.toLp 2 x) (WithLp.toLp 2 x)
    have h2 := (hA.1.eigenvectorBasis.repr.inner_map_map
      (WithLp.toLp 2 x) (WithLp.toLp 2 x)).symm
    have h3 := (FLT.GaussianFourierPosDef.dotProduct_ofLp_eq_inner
      (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x))
      (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x))).symm
    rw [h1, h2, h3]; simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  calc hA.1.eigenvalues i₀ * (x ⬝ᵥ x)
      = ∑ i, hA.1.eigenvalues i₀ *
          (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 := by
        rw [hxx, Finset.mul_sum]
    _ ≤ ∑ i, hA.1.eigenvalues i *
          (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
    _ = rQuad A x := hquad.symm

lemma gapsw80_t2_summable_1D {a : ℝ} (ha : 0 < a) (b : ℂ) :
    Summable fun k : ℤ =>
      ‖cexp (-(π : ℂ) * (a : ℂ) * (k : ℂ) ^ 2 + 2 * π * b * (k : ℂ))‖ := by
  have hre : (-(π : ℂ) * (a : ℂ)).re < 0 := by
    simp only [neg_mul, neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    exact neg_neg_of_pos (mul_pos pi_pos ha)
  have hO := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hre (2 * π * b)
    (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite
  simp only [Function.comp_def, Complex.ofReal_intCast] at hO
  exact (summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hO).norm

lemma gapsw80_t2_summable_prod_fin :
    ∀ {n : ℕ} {f : Fin n → ℤ → ℝ}, (∀ i k, 0 ≤ f i k) → (∀ i, Summable (f i)) →
      Summable fun v : Fin n → ℤ => ∏ i, f i (v i) := by
  intro n
  induction n with
  | zero =>
    intro f _ _
    have hU : Subsingleton (Fin 0 → ℤ) := inferInstance
    refine ⟨1, ?_⟩
    have hconst : (fun v : Fin 0 → ℤ => ∏ i, f i (v i)) = fun _ => 1 := by
      funext v; exact Finset.prod_empty
    rw [hconst]
    simpa using hasSum_ite_eq (default : Fin 0 → ℤ) (1 : ℝ)
  | succ m IH =>
    intro f hpos hsum
    set e : (Fin (m + 1) → ℤ) ≃ (Fin m → ℤ) × ℤ :=
      { toFun := fun v => ⟨v ∘ Fin.castSucc, v (Fin.last m)⟩
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun v => by
          funext i; dsimp only
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
        right_inv := fun p => by
          ext
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last] }
    have hIH : Summable fun v : Fin m → ℤ => ∏ i, f (Fin.castSucc i) (v i) :=
      IH (fun i k => hpos _ k) fun i => hsum _
    have hprod :
        Summable fun p : (Fin m → ℤ) × ℤ =>
          (∏ i, f (Fin.castSucc i) (p.1 i)) * f (Fin.last m) p.2 :=
      hIH.mul_of_nonneg (hsum _) (fun v => Finset.prod_nonneg fun i _ => hpos _ _)
        (fun k => hpos _ k)
    have hprod' :
        Summable fun p : (Fin m → ℤ) × ℤ =>
          ∏ i, f i ((Fin.snoc p.1 p.2 : Fin (m + 1) → ℤ) i) := by
      refine hprod.congr fun p => ?_
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact e.symm.summable_iff.mp hprod'

lemma gapsw80_t2_summable_1D_real {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Summable fun k : ℤ => rexp (-(a * (k : ℝ) ^ 2) + r * (k : ℝ)) := by
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  have h := gapsw80_t2_summable_1D (a := a / π) (div_pos ha pi_pos)
    (((r / (2 * π)) : ℝ) : ℂ)
  refine h.congr fun k => ?_
  have heq : (-(π : ℂ) * ((a / π : ℝ) : ℂ) * (k : ℂ) ^ 2
        + 2 * π * (((r / (2 * π)) : ℝ) : ℂ) * (k : ℂ))
      = (((-(a * (k : ℝ) ^ 2) + r * (k : ℝ)) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [heq, Complex.norm_exp, Complex.ofReal_re]

lemma gapsw80_t2_summable_gaussian_Zn {c : ℝ} (hc : 0 < c) :
    Summable fun v : Fin n → ℤ => rexp (-(c * ∑ i, (v i : ℝ) ^ 2)) := by
  have hrew : (fun v : Fin n → ℤ => rexp (-(c * ∑ i, (v i : ℝ) ^ 2)))
      = fun v => ∏ i, rexp (-(c * (v i : ℝ) ^ 2)) := by
    funext v; rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hrew]
  exact gapsw80_t2_summable_prod_fin (n := n)
    (f := fun _ k => rexp (-(c * (k : ℝ) ^ 2)))
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => (gapsw80_t2_summable_1D_real hc 0).congr fun k => by
      rw [zero_mul, add_zero])

lemma gapsw80_t2_re_cQuad_liftC (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    (cQuad (liftC A) z).re
      = rQuad A (fun i => (z i).re) - rQuad A (fun i => (z i).im) := by
  have hmv : ∀ i, ((liftC A) *ᵥ z) i = ∑ j, (A i j : ℂ) * z j := fun i => by
    simp only [Matrix.mulVec, dotProduct, liftC, Matrix.map_apply]
  have hmvR : ∀ (x : Fin n → ℝ) i, (A *ᵥ x) i = ∑ j, A i j * x j := fun x i => by
    simp only [Matrix.mulVec, dotProduct]
  unfold cQuad rQuad
  simp only [dotProduct, hmv, hmvR]
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.re_sum, Complex.im_sum]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]

theorem gapsw80_t2_summable_thetaTerm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {t : ℝ} (ht : 0 < t) (b : Fin n → ℂ) :
    Summable fun v : Fin n → ℤ => ‖thetaTerm A t b v‖ := by
  obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hA
  have hxx : ∀ v : Fin n → ℤ, zcastR v ⬝ᵥ zcastR v = ∑ i, (v i : ℝ) ^ 2 := fun v => by
    simp only [dotProduct, zcastR]; exact Finset.sum_congr rfl fun i _ => (sq _).symm
  set g : Fin n → ℤ → ℝ := fun i k =>
    rexp (-(π * t * c * (k : ℝ) ^ 2) + 2 * π * (b i).re * (k : ℝ))
  have hmajor : Summable fun v : Fin n → ℤ => ∏ i, g i (v i) :=
    gapsw80_t2_summable_prod_fin (n := n) (f := g)
      (fun _ _ => (Real.exp_pos _).le)
      (fun i => (gapsw80_t2_summable_1D_real (a := π * t * c) (by positivity)
          (2 * π * (b i).re)).congr
        fun k => by unfold g; ring_nf)
  refine hmajor.of_nonneg_of_le (fun v => norm_nonneg _) fun v => ?_
  unfold thetaTerm
  rw [Complex.norm_exp]
  have hre : (-(π : ℂ) * (t : ℂ) * (rQuad A (zcastR v) : ℂ)
        + 2 * π * ∑ i, b i * (v i : ℂ)).re
      = -(π * t * rQuad A (zcastR v)) + 2 * π * ∑ i, (b i).re * (v i : ℝ) := by
    have h1 : -(π : ℂ) * (t : ℂ) * (rQuad A (zcastR v) : ℂ)
        = (((-(π * t * rQuad A (zcastR v))) : ℝ) : ℂ) := by push_cast; ring
    have h2 : (2 : ℂ) * (π : ℂ) = (((2 * π) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.re_sum]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by
      simp [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  rw [hre, show (∏ i, g i (v i)) = rexp (∑ i,
      (-(π * t * c * (v i : ℝ) ^ 2) + 2 * π * (b i).re * (v i : ℝ))) from
    (Real.exp_sum _ _).symm]
  apply Real.exp_le_exp.mpr
  have hQv := hQ (zcastR v); rw [hxx v] at hQv
  have hsplit : (∑ i, (-(π * t * c * (v i : ℝ) ^ 2) + 2 * π * (b i).re * (v i : ℝ)))
      = -(π * t) * (c * ∑ i, (v i : ℝ) ^ 2)
        + (2 * π) * ∑ i, (b i).re * (v i : ℝ) := by
    rw [Finset.sum_add_distrib]; congr 1
    · rw [← mul_assoc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  nlinarith [mul_pos pi_pos ht]

theorem gapsw80_t2_summable_dualTerm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {t : ℝ} (ht : 0 < t) (b : Fin n → ℂ) :
    Summable fun w : Fin n → ℤ => ‖dualTerm A t b w‖ := by
  obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hA.inv
  set d : Fin n → ℝ := fun i => (b i).im
  set C₁ : ℝ := rexp (π / t * rQuad A⁻¹ (fun i => (b i).re))
  have hC₁ : 0 ≤ C₁ := (Real.exp_pos _).le

  have hconst : ∀ w : Fin n → ℤ,
      ‖dualTerm A t b w‖
        = C₁ * rexp (-(π / t) * rQuad A⁻¹ (fun i => (w i : ℝ) - d i)) := by
    intro w
    unfold dualTerm
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    have hcoef : -(π : ℂ) / (t : ℂ) = (((-(π / t)) : ℝ) : ℂ) := by push_cast; ring
    rw [hcoef, Complex.re_ofReal_mul, gapsw80_t2_re_cQuad_liftC]
    have hre : (fun i => ((w i : ℂ) + Complex.I * b i).re)
        = fun i => (w i : ℝ) - d i := by
      funext i; simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, d]; ring
    have him : (fun i => ((w i : ℂ) + Complex.I * b i).im)
        = fun i => (b i).re := by
      funext i; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [hre, him]; ring

  set g : Fin n → ℤ → ℝ := fun i k => rexp (-(π * c / t) * ((k : ℝ) - d i) ^ 2)
  have hg_sum : ∀ i, Summable (g i) := fun i => by
    refine ((gapsw80_t2_summable_1D_real (a := π * c / t) (by positivity)
        (2 * (π * c / t) * d i)).mul_left (rexp (-(π * c / t) * (d i) ^ 2))).congr
      fun k => ?_
    unfold g; rw [← Real.exp_add]; ring_nf
  have hmajor : Summable fun w : Fin n → ℤ => ∏ i, g i (w i) :=
    gapsw80_t2_summable_prod_fin (n := n) (f := g)
      (fun _ _ => (Real.exp_pos _).le) hg_sum
  refine (hmajor.mul_left C₁).of_nonneg_of_le (fun w => norm_nonneg _) fun w => ?_
  rw [hconst w]
  refine mul_le_mul_of_nonneg_left ?_ hC₁
  rw [show (∏ i, g i (w i))
      = rexp (∑ i, -(π * c / t) * ((w i : ℝ) - d i) ^ 2) from (Real.exp_sum _ _).symm]
  apply Real.exp_le_exp.mpr
  have hQw := hQ (fun i => (w i : ℝ) - d i)
  have hdot : (fun i => (w i : ℝ) - d i) ⬝ᵥ (fun i => (w i : ℝ) - d i)
      = ∑ i, ((w i : ℝ) - d i) ^ 2 := by
    simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [hdot] at hQw
  rw [← Finset.mul_sum, show -(π * c / t) = -(π / t) * c by ring, mul_assoc]
  have hnp : -(π / t) ≤ 0 := neg_nonpos_of_nonneg (div_pos pi_pos ht).le
  exact mul_le_mul_of_nonpos_left hQw hnp

end Summability
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section BilinearSchur

variable {R : Type*} [CommRing R] {m k : ℕ}

theorem gapsw80_t2_bilin_schur_eq₂₂
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin k) R)
    (D : Matrix (Fin k) (Fin k) R) [Invertible D] (hD : Dᵀ = D)
    (x : Fin m → R) (y : Fin k → R) :
    (Sum.elim x y) ᵥ* (fromBlocks P q qᵀ D) ⬝ᵥ (Sum.elim x y)
      = ((⅟D * qᵀ) *ᵥ x + y) ᵥ* D ⬝ᵥ ((⅟D * qᵀ) *ᵥ x + y)
        + x ᵥ* (P - q * ⅟D * qᵀ) ⬝ᵥ x := by

  have hDinv : (⅟D)ᵀ = ⅟D := by
    have : Dᵀ * (⅟D)ᵀ = 1 := by rw [← Matrix.transpose_mul, invOf_mul_self,
      Matrix.transpose_one]
    rw [hD] at this
    exact (invOf_eq_right_inv this).symm
  have hz : ((⅟D * qᵀ) *ᵥ x) ᵥ* D = x ᵥ* q := by
    rw [← vecMul_transpose, Matrix.transpose_mul, hDinv, Matrix.transpose_transpose,
      vecMul_vecMul, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
  have hDz : D *ᵥ ((⅟D * qᵀ) *ᵥ x) = qᵀ *ᵥ x := by
    rw [mulVec_mulVec, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have hxy : x ᵥ* q ⬝ᵥ y = y ᵥ* qᵀ ⬝ᵥ x := by
    rw [← dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hqS : x ᵥ* (q * ⅟D * qᵀ) ⬝ᵥ x = x ᵥ* q ⬝ᵥ ((⅟D * qᵀ) *ᵥ x) := by
    rw [Matrix.mul_assoc, ← vecMul_vecMul, ← dotProduct_mulVec]
  have hyDz : y ᵥ* D ⬝ᵥ ((⅟D * qᵀ) *ᵥ x) = y ᵥ* qᵀ ⬝ᵥ x := by
    rw [← dotProduct_mulVec, hDz, dotProduct_mulVec]
  simp only [vecMul_fromBlocks, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, add_vecMul, vecMul_sub, add_dotProduct,
    dotProduct_add, sub_dotProduct, hz, hyDz, hqS]
  ring

theorem gapsw80_t2_bilin_schur_eq₂₂'
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin k) R)
    (D : Matrix (Fin k) (Fin k) R) [Invertible D] (hD : Dᵀ = D)
    (x : Fin m → R) (y : Fin k → R) :
    (Sum.elim x y) ⬝ᵥ ((fromBlocks P q qᵀ D) *ᵥ (Sum.elim x y))
      = ((⅟D * qᵀ) *ᵥ x + y) ⬝ᵥ (D *ᵥ ((⅟D * qᵀ) *ᵥ x + y))
        + x ⬝ᵥ ((P - q * ⅟D * qᵀ) *ᵥ x) := by
  rw [dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec]
  exact gapsw80_t2_bilin_schur_eq₂₂ P q D hD x y

theorem gapsw80_t2_bilin_schur_inv_scalar
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin 1) R)
    (a : R) [Invertible a] (hP : Pᵀ = P)
    [Invertible (P - q * ⅟a • qᵀ)]
    (X : Fin m → R) (Y : R) :
    (Sum.elim X (fun _ => Y)) ⬝ᵥ
        ((fromBlocks P q qᵀ ((a : R) • (1 : Matrix (Fin 1) (Fin 1) R)))⁻¹
          *ᵥ (Sum.elim X (fun _ => Y)))
      = (X - (⅟a * Y) • (fun i => q i 0)) ⬝ᵥ
          ((P - q * ⅟a • qᵀ)⁻¹ *ᵥ (X - (⅟a * Y) • (fun i => q i 0)))
        + ⅟a * Y ^ 2 := by
  classical
  set D : Matrix (Fin 1) (Fin 1) R := (a : R) • 1 with hD
  haveI hDi : Invertible D :=
    ⟨⅟a • 1, by rw [hD, smul_mul_smul_comm, invOf_mul_self, one_mul, one_smul],
      by rw [hD, smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul]⟩
  have hiD : ⅟D = (⅟a : R) • (1 : Matrix (Fin 1) (Fin 1) R) :=
    invOf_eq_right_inv
      (by rw [hD, smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul])
  set S : Matrix (Fin m) (Fin m) R := P - q * ⅟a • qᵀ with hS
  have hSeq : P - q * ⅟D * qᵀ = S := by
    rw [hS, hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  haveI : Invertible (P - q * ⅟D * qᵀ) := hSeq ▸ (inferInstance : Invertible S)
  haveI hMi : Invertible (fromBlocks P q qᵀ D) := fromBlocks₂₂Invertible P q qᵀ D

  set q₀ : Fin m → R := fun i => q i 0
  have hq0T : ∀ x : Fin m → R, qᵀ *ᵥ x = fun _ => q₀ ⬝ᵥ x := fun x => by
    funext j; fin_cases j; simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, q₀]
  have hq0 : ∀ y : Fin 1 → R, q *ᵥ y = y 0 • q₀ := fun y => by
    funext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one, q₀, mul_comm]
  have hF1 : ∀ (c : R) (y : Fin 1 → R), (fun _ => c) ⬝ᵥ y = c * y 0 := fun c y => by
    simp [dotProduct, Fin.sum_univ_one]
  have hSiT : (⅟S)ᵀ = ⅟S := by
    have hST : Sᵀ = S := by
      rw [hS, Matrix.transpose_sub, hP, Matrix.transpose_mul, Matrix.transpose_smul,
        Matrix.transpose_transpose, Matrix.smul_mul, ← Matrix.mul_smul]
    have h1 : Sᵀ * (⅟S)ᵀ = 1 := by rw [← Matrix.transpose_mul, invOf_mul_self,
      Matrix.transpose_one]
    rw [hST] at h1; exact (invOf_eq_right_inv h1).symm
  have hswap : ∀ x y : Fin m → R, x ⬝ᵥ (⅟S *ᵥ y) = y ⬝ᵥ (⅟S *ᵥ x) := fun x y => by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose (⅟S) x, hSiT, dotProduct_comm]
  have hDy : ⅟D *ᵥ (fun _ => Y : Fin 1 → R) = fun _ => ⅟a * Y := by
    funext j; fin_cases j
    simp only [hiD, smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]

  rw [← Matrix.invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq, Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
  simp only [hSeq]

  have hTop : (⅟S *ᵥ X + (-(⅟S * q * ⅟D)) *ᵥ fun _ => Y)
      = ⅟S *ᵥ X - (⅟a * Y) • (⅟S *ᵥ q₀) := by
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDy,
      hq0, Matrix.mulVec_smul, sub_eq_add_neg]
  have hBot : ((-(⅟D * qᵀ * ⅟S)) *ᵥ X + (⅟D + ⅟D * qᵀ * ⅟S * q * ⅟D) *ᵥ fun _ => Y)
      = fun _ => -(⅟a * (q₀ ⬝ᵥ (⅟S *ᵥ X)))
          + (⅟a * Y + ⅟a ^ 2 * Y * (q₀ ⬝ᵥ (⅟S *ᵥ q₀))) := by
    funext j; fin_cases j
    simp only [Matrix.neg_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hDy,
      hq0, Matrix.mulVec_smul, hq0T, hiD, smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
    ring
  rw [hTop, hBot, hF1]
  rw [← Matrix.invOf_eq_nonsing_inv, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hswap X q₀]
  ring

theorem gapsw80_t2_posDef_schur
    {P : Matrix (Fin m) (Fin m) ℝ} {q : Matrix (Fin m) (Fin k) ℝ}
    {D : Matrix (Fin k) (Fin k) ℝ} [Invertible D] (hD : D.IsHermitian)
    (hM : (fromBlocks P q qᵀ D).PosDef) :
    (P - q * ⅟D * qᵀ).PosDef := by
  have hMi := (posDef_iff_dotProduct_mulVec).mp hM
  have hDT : Dᵀ = D := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hD
  have hDiT : (⅟D)ᵀ = ⅟D := by
    have : Dᵀ * (⅟D)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, invOf_mul_self, Matrix.transpose_one]
    rw [hDT] at this; exact (invOf_eq_right_inv this).symm
  have hPherm : P.IsHermitian := (Matrix.isHermitian_fromBlocks_iff.mp hMi.1).1
  have hPT : Pᵀ = P := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hPherm
  have hSH : (P - q * ⅟D * qᵀ).IsHermitian := by
    show (P - q * ⅟D * qᵀ)ᴴ = P - q * ⅟D * qᵀ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hPT, hDiT, Matrix.mul_assoc]
  refine (posDef_iff_dotProduct_mulVec).mpr ⟨hSH, fun x hx => ?_⟩

  set y : Fin k → ℝ := -((⅟D * qᵀ) *ᵥ x) with hy
  have hxy : Sum.elim x y ≠ 0 := fun h => hx (funext fun i => by
    have := congrFun h (Sum.inl i); simpa using this)
  have key : 0 < star (Sum.elim x y) ⬝ᵥ ((fromBlocks P q qᵀ D) *ᵥ Sum.elim x y) :=
    hMi.2 hxy
  rw [show star (Sum.elim x y) = Sum.elim x y from rfl,
    gapsw80_t2_bilin_schur_eq₂₂' P q D hDT x y] at key
  simp only [hy, _root_.neg_add_cancel, Matrix.mulVec_zero, dotProduct_zero,
    zero_add] at key
  simpa [show star x = x from rfl] using key

end BilinearSchur
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section InductionStep

variable {m : ℕ}

def PoissonLawBlock (M : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ)
    (t : ℝ) (b : (Fin m ⊕ Fin 1) → ℂ) : Prop :=
  (∑' v : (Fin m ⊕ Fin 1) → ℤ,
      cexp (-(π : ℂ) * t *
          (((fun i => (v i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℝ)) : ℝ) : ℂ)
        + 2 * π * ∑ i, b i * (v i : ℂ)))
    = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) *
      ∑' w : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) / t *
          ((fun i => (w i : ℂ) + Complex.I * b i) ⬝ᵥ
            ((M⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (w i : ℂ) + Complex.I * b i)))

set_option maxHeartbeats 25600000 in

theorem gapsw80_t2_poisson_step
    (IH : ∀ (S : Matrix (Fin m) (Fin m) ℝ), S.PosDef →
      ∀ {t : ℝ}, 0 < t → ∀ b : Fin m → ℂ, PoissonLaw S t b)
    (M : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ) (hM : M.PosDef)
    {t : ℝ} (ht : 0 < t) (b : (Fin m ⊕ Fin 1) → ℂ) :
    PoissonLawBlock M t b := by
  classical

  set P : Matrix (Fin m) (Fin m) ℝ := M.toBlocks₁₁
  set q : Matrix (Fin m) (Fin 1) ℝ := M.toBlocks₁₂
  set a : ℝ := M (Sum.inr 0) (Sum.inr 0)
  set b' : Fin m → ℂ := b ∘ Sum.inl
  set b₁ : ℂ := b (Sum.inr 0)
  set q₀ : Fin m → ℝ := fun i => q i 0
  have hMT : Mᵀ = M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hM.1
  have hMblock : M = fromBlocks P q qᵀ ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    conv_lhs => rw [← M.fromBlocks_toBlocks]
    congr 1
    · ext i j
      have := congrFun (congrFun hMT (Sum.inl j)) (Sum.inr i)
      simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.transpose_apply] at this
      exact this
    · ext i j; fin_cases i; fin_cases j
      simp [Matrix.toBlocks₂₂, a, Matrix.smul_apply, Matrix.one_apply]
  have ha : 0 < a := by
    set v₀ : (Fin m ⊕ Fin 1) → ℝ := Sum.elim 0 (fun _ => (1 : ℝ)) with hv₀
    have hne : v₀ ≠ 0 := fun h =>
      (one_ne_zero : (1 : ℝ) ≠ 0) (by have := congrFun h (Sum.inr 0); simpa [hv₀] using this)
    have key : 0 < star v₀ ⬝ᵥ (M *ᵥ v₀) :=
      (posDef_iff_dotProduct_mulVec.mp hM).2 hne
    have heval : star v₀ ⬝ᵥ (M *ᵥ v₀) = a := by
      rw [show (star v₀ : _ → ℝ) = v₀ from rfl, hv₀, hMblock, fromBlocks_mulVec,
        sumElim_dotProduct_sumElim]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, zero_add,
        dotProduct_zero, smul_mulVec, Matrix.one_mulVec, dotProduct,
        Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, mul_one, one_mul,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rwa [heval] at key
  haveI haI : Invertible a := invertibleOfNonzero ha.ne'
  haveI haCI : Invertible (a : ℂ) := invertibleOfNonzero (Complex.ofReal_ne_zero.mpr ha.ne')
  have hia : (⅟a : ℝ) = a⁻¹ := invOf_eq_inv a
  have hiaC : (⅟(a : ℂ) : ℂ) = (a : ℂ)⁻¹ := invOf_eq_inv (a : ℂ)
  haveI hDi : Invertible ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    ⟨⅟a • 1, by rw [smul_mul_smul_comm, invOf_mul_self, one_mul, one_smul],
      by rw [smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul]⟩
  have hiD : ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (⅟a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
    invOf_eq_right_inv (by rw [smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul])
  set S : Matrix (Fin m) (Fin m) ℝ := P - q * ⅟a • qᵀ with hS
  have hSpd : S.PosDef := by
    have hDh : ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).IsHermitian := by
      show _ = _; rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_smul, Matrix.transpose_one]
    have hSalt :
        (P - q * ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ).PosDef :=
      gapsw80_t2_posDef_schur hDh (hMblock ▸ hM)
    rwa [hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.mul_smul] at hSalt
  have hdetS : 0 < S.det := hSpd.det_pos
  haveI hSI : Invertible S :=
    Matrix.invertibleOfIsUnitDet S (isUnit_iff_ne_zero.mpr hdetS.ne')
  have hPT : Pᵀ = P := by
    ext i j
    have := congrFun (congrFun hMT (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.transpose_apply, P, Matrix.toBlocks₁₁] using this

  set e : ((Fin m ⊕ Fin 1) → ℤ) ≃ (Fin m → ℤ) × ℤ :=
    { toFun := fun v => ⟨v ∘ Sum.inl, v (Sum.inr 0)⟩
      invFun := fun p => Sum.elim p.1 (fun _ => p.2)
      left_inv := fun v => by funext i; cases i with
        | inl i => rfl
        | inr j => fin_cases j; rfl
      right_inv := fun p => rfl }
  set q₀u : (Fin m → ℤ) → ℝ := fun u => ∑ i, q₀ i * (u i : ℝ)

  have hQsplit : ∀ (u : Fin m → ℤ) (k : ℤ),
      (fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
          ⬝ᵥ (M *ᵥ fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
        = a * (a⁻¹ * q₀u u + (k : ℝ)) ^ 2 + rQuad S (zcastR u) := by
    intro u k
    have hcast : (fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
        = Sum.elim (zcastR u) (fun _ => (k : ℝ)) := by
      funext i; cases i with | inl i => rfl | inr j => rfl
    rw [hcast, hMblock,
      gapsw80_t2_bilin_schur_eq₂₂' P q ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (by rw [Matrix.transpose_smul, Matrix.transpose_one])
        (zcastR u) (fun _ => (k : ℝ))]
    have hSeq : P - q * ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ = S := by
      rw [hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_smul]
    rw [hSeq]
    congr 1
    have hv : (⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ) *ᵥ zcastR u
          + (fun _ => (k : ℝ))
        = fun _ => a⁻¹ * q₀u u + (k : ℝ) := by
      funext j
      simp only [hiD, Matrix.smul_mul, Matrix.one_mul, smul_mulVec, Matrix.mulVec,
        dotProduct, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
        q₀u, q₀, zcastR, hia, Fin.eq_zero j]
    rw [hv, smul_mulVec, Matrix.one_mulVec]
    simp only [dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
    ring

  have hLsplit : ∀ (u : Fin m → ℤ) (k : ℤ),
      (∑ i, b i * ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ))
        = (∑ i, b' i * (u i : ℂ)) + b₁ * (k : ℂ) := by
    intro u k
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, b', b₁,
      Function.comp_apply]

  set β : (Fin m → ℤ) → ℂ := fun u => b₁ - (t : ℂ) * (q₀u u : ℂ)
  have htare : 0 < ((t * a : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; exact mul_pos ht ha

  have h1D : ∀ u : Fin m → ℤ,
      (∑' k : ℤ, cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (k : ℂ) ^ 2
          + 2 * π * (β u) * (k : ℂ)))
        = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' w : ℤ, cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
              * ((w : ℂ) + Complex.I * (β u)) ^ 2) :=
    fun u => Complex.tsum_exp_neg_quadratic htare (β u)

  set β' : ℤ → (Fin m → ℂ) :=
    fun w i => b' i + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hqsum : ∀ u : Fin m → ℤ,
      (∑ i, (q₀ i : ℂ) * (u i : ℂ)) = ((q₀u u : ℝ) : ℂ) := fun u => by
    simp only [q₀u, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  have hβ'sum : ∀ (w : ℤ) (u : Fin m → ℤ), (∑ i, (β' w) i * (u i : ℂ))
      = (∑ i, b' i * (u i : ℂ))
        + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀u u : ℂ) := fun w u => by
    rw [← hqsum u]
    simp only [β', add_mul, Finset.sum_add_distrib, Finset.mul_sum]; ring_nf

  have hExpEq : ∀ (u : Fin m → ℤ) (w : ℤ),
      (-(π : ℂ) * (t : ℂ)
            * ((a * (a⁻¹ * q₀u u) ^ 2 : ℝ) : ℂ)
          + 2 * π * (∑ i, b' i * (u i : ℂ))
          + (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * (β u)) ^ 2))
        = (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
          + 2 * π * (∑ i, (β' w) i * (u i : ℂ)) := by
    intro u w
    rw [hβ'sum w u]
    simp only [β, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_inv]
    have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
    field_simp
    ring_nf
    simp only [hI2]
    ring

  set Fuw : (Fin m → ℤ) × ℤ → ℂ := fun p =>
    cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((p.2 : ℂ) + Complex.I * b₁) ^ 2)
      * thetaTerm S t (β' p.2) p.1
  have haiC : ((a : ℂ))⁻¹ = (((a⁻¹ : ℝ)) : ℂ) := by
    rw [Complex.ofReal_inv]
  have hReβ' : ∀ w i, (β' w i).re = (b' i).re - a⁻¹ * b₁.re * q₀ i := fun w i => by
    have h1 : β' w i
        = b' i + (((a⁻¹ * q₀ i : ℝ)) : ℂ) * (Complex.I * (w : ℂ) - b₁) := by
      simp only [β', haiC, Complex.I_sq]; push_cast; ring_nf; simp [Complex.I_sq]; ring
    rw [h1, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.intCast_im]
    ring
  have hR2' : Summable fun p : (Fin m → ℤ) × ℤ => ‖Fuw p‖ := by
    obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hSpd
    set gU : Fin m → ℤ → ℝ := fun i k =>
      rexp (-(π * t * c * (k : ℝ) ^ 2)
        + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (k : ℝ))
    have hUmaj : Summable fun u : Fin m → ℤ => ∏ i, gU i (u i) :=
      gapsw80_t2_summable_prod_fin (n := m) (f := gU)
        (fun _ _ => (Real.exp_pos _).le)
        (fun i => (gapsw80_t2_summable_1D_real (a := π * t * c) (by positivity)
            (2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i))).congr
          fun k => by unfold gU; ring_nf)
    have hWmaj : Summable fun w : ℤ =>
        ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
          * ((w : ℂ) + Complex.I * b₁) ^ 2)‖ := by
      have hcoef : (-(π : ℂ) / ((t * a : ℝ) : ℂ))
          = (((-(π / (t * a))) : ℝ) : ℂ) := by push_cast; ring
      have hnorm : ∀ w : ℤ,
          ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)‖
            = rexp (-(π / (t * a)) * ((w : ℝ) - b₁.im) ^ 2)
              * rexp ((π / (t * a)) * b₁.re ^ 2) := fun w => by
        rw [Complex.norm_exp, hcoef, Complex.re_ofReal_mul, ← Real.exp_add]
        congr 1
        have : ((w : ℂ) + Complex.I * b₁).re = (w : ℝ) - b₁.im ∧
            ((w : ℂ) + Complex.I * b₁).im = b₁.re := by
          refine ⟨?_, ?_⟩ <;>
            simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
              Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
              Complex.intCast_im, zero_mul, one_mul, zero_sub, sub_zero,
              mul_zero, zero_add] <;> ring
        rw [show (((w : ℂ) + Complex.I * b₁) ^ 2).re
            = ((w : ℝ) - b₁.im) ^ 2 - b₁.re ^ 2 by
          rw [sq, Complex.mul_re, this.1, this.2]; ring]
        ring
      simp_rw [hnorm]
      exact (((gapsw80_t2_summable_1D_real (a := π / (t * a))
          (div_pos pi_pos (mul_pos ht ha)) (2 * (π / (t * a)) * b₁.im)).mul_left
        (rexp (-(π / (t * a)) * b₁.im ^ 2))).congr fun w => by
          rw [← Real.exp_add]; ring_nf).mul_right _

    have hbound : ∀ p : (Fin m → ℤ) × ℤ,
        ‖Fuw p‖ ≤ ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
            * ((p.2 : ℂ) + Complex.I * b₁) ^ 2)‖ * ∏ i, gU i (p.1 i) := fun p => by
      unfold Fuw
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold thetaTerm
      rw [Complex.norm_exp,
        show (∏ i, gU i (p.1 i)) = rexp (∑ i,
          (-(π * t * c * (p.1 i : ℝ) ^ 2)
            + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ))) from
          (Real.exp_sum _ _).symm]
      apply Real.exp_le_exp.mpr
      have hre : (-(π : ℂ) * (t : ℂ) * (rQuad S (zcastR p.1) : ℂ)
            + 2 * π * ∑ i, (β' p.2) i * (p.1 i : ℂ)).re
          = -(π * t * rQuad S (zcastR p.1))
            + 2 * π * ∑ i, ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ) := by
        have h1 : -(π : ℂ) * (t : ℂ) * (rQuad S (zcastR p.1) : ℂ)
            = (((-(π * t * rQuad S (zcastR p.1))) : ℝ) : ℂ) := by push_cast; ring
        have h2 : (2 : ℂ) * (π : ℂ) = (((2 * π) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
          Complex.re_sum]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by
          rw [Complex.mul_re, hReβ' p.2 i, Complex.intCast_re, Complex.intCast_im,
            mul_zero, sub_zero]
      rw [hre]
      have hxx : zcastR p.1 ⬝ᵥ zcastR p.1 = ∑ i, (p.1 i : ℝ) ^ 2 := by
        simp only [dotProduct, zcastR]
        exact Finset.sum_congr rfl fun i _ => (sq _).symm
      have hQv := hQ (zcastR p.1); rw [hxx] at hQv
      have hsplit : (∑ i, (-(π * t * c * (p.1 i : ℝ) ^ 2)
            + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ)))
          = -(π * t) * (c * ∑ i, (p.1 i : ℝ) ^ 2)
            + (2 * π) * ∑ i, ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ) := by
        rw [Finset.sum_add_distrib]; congr 1
        · rw [← mul_assoc, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit]
      nlinarith [mul_pos pi_pos ht]
    exact (hUmaj.mul_of_nonneg hWmaj
        (fun u => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
        (fun w => norm_nonneg _)).of_nonneg_of_le
      (fun p => norm_nonneg _)
      (fun p => by rw [mul_comm]; exact hbound p)

  have hdetM : M.det = a * S.det := by
    have hdD : ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det = a := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_one]
    rw [hMblock, Matrix.det_fromBlocks₂₂, hdD, hiD, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← Matrix.mul_smul]
  have hpref : (1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ))
        * (((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
      = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) := by
    have hta : (0 : ℝ) < t * a := mul_pos ht ha
    have htmS : (0 : ℝ) < t ^ m * S.det := mul_pos (pow_pos ht m) hdetS
    rw [one_div, ← Complex.cpow_neg,
      show ((t ^ (m + 1) * M.det : ℝ) : ℂ)
        = ((t * a : ℝ) : ℂ) * ((t ^ m * S.det : ℝ) : ℂ) by
          push_cast; rw [hdetM]; push_cast; ring,
      ← Complex.mul_cpow_ofReal_nonneg hta.le htmS.le]

  set Pc : Matrix (Fin m) (Fin m) ℂ := P.map ((↑) : ℝ → ℂ)
  set qc : Matrix (Fin m) (Fin 1) ℂ := q.map ((↑) : ℝ → ℂ)
  have hqcT : qcᵀ = qᵀ.map ((↑) : ℝ → ℂ) := by
    ext i j; simp [qc, Matrix.transpose_apply, Matrix.map_apply]
  have hPcT : Pcᵀ = Pc := by
    ext i j; simp only [Pc, Matrix.transpose_apply, Matrix.map_apply]
    rw [← congrFun (congrFun hPT i) j, Matrix.transpose_apply]
  have hMc : (M.map ((↑) : ℝ → ℂ))
      = fromBlocks Pc qc qcᵀ ((a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    rw [hMblock]; ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
        Pc, qc, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
        apply_ite ((↑) : ℝ → ℂ)]

  haveI hMI : Invertible M :=
    Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hM.det_pos.ne')
  have hMinvC : (M⁻¹).map ((↑) : ℝ → ℂ) = (M.map ((↑) : ℝ → ℂ))⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    have h1 : M.map ((↑) : ℝ → ℂ) * (M⁻¹).map ((↑) : ℝ → ℂ)
        = (M * M⁻¹).map ((↑) : ℝ → ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [h1, ← Matrix.invOf_eq_nonsing_inv, mul_invOf_self]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]
  have hSinvC' : (S⁻¹).map ((↑) : ℝ → ℂ) = (S.map ((↑) : ℝ → ℂ))⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    have h1 : S.map ((↑) : ℝ → ℂ) * (S⁻¹).map ((↑) : ℝ → ℂ)
        = (S * S⁻¹).map ((↑) : ℝ → ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [h1, ← Matrix.invOf_eq_nonsing_inv, mul_invOf_self]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]
  have hdetSc : (liftC S).det = ((S.det : ℝ) : ℂ) := by
    have := (RingHom.map_det Complex.ofRealHom S).symm
    simp [liftC, RingHom.mapMatrix_apply] at this
    exact this
  have hSc : liftC S = Pc - qc * ⅟(a : ℂ) • qcᵀ := by
    unfold liftC; rw [hS]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, Pc, qc,
      Matrix.smul_apply, Matrix.transpose_apply, Fin.sum_univ_one, hiaC, hia,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv, smul_eq_mul]
  haveI hScI : Invertible (Pc - qc * ⅟(a : ℂ) • qcᵀ) := by
    rw [← hSc]
    exact (liftC S).invertibleOfIsUnitDet
      (hdetSc ▸ isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hdetS.ne'))
  have hSinvC : liftC S⁻¹ = (Pc - qc * ⅟(a : ℂ) • qcᵀ)⁻¹ := by
    have h1 : liftC S⁻¹ = (S⁻¹).map ((↑) : ℝ → ℂ) := rfl
    have h2 : S.map ((↑) : ℝ → ℂ) = liftC S := rfl
    rw [h1, hSinvC', h2, hSc]
  have hDualSplit : ∀ (w' : Fin m → ℤ) (w : ℤ),
      cexp (-(π : ℂ) / (t : ℂ)
          * ((fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
                + Complex.I * b i)
            ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
              *ᵥ fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
                + Complex.I * b i)))
        = cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
          * dualTerm S t (β' w) w' := by
    intro w' w
    set X : Fin m → ℂ := fun i => (w' i : ℂ) + Complex.I * b' i
    set Y : ℂ := (w : ℂ) + Complex.I * b₁
    have hcast : (fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
          + Complex.I * b i)
        = Sum.elim X (fun _ => Y) := by
      funext i; cases i with
      | inl i => simp [X, b']
      | inr j => fin_cases j; simp [Y, b₁]
    rw [hcast, hMinvC, hMc,
      gapsw80_t2_bilin_schur_inv_scalar Pc qc (a : ℂ) hPcT X Y]
    unfold dualTerm cQuad
    rw [hSinvC, ← Complex.exp_add]
    congr 1
    have hXshift : (X - (⅟(a : ℂ) * Y) • fun i => qc i 0)
        = fun i => (w' i : ℂ) + Complex.I * (β' w) i := by
      funext i
      have hlhs : (X - (⅟(a : ℂ) * Y) • fun i => qc i 0) i
          = ((w' i : ℂ) + Complex.I * b' i)
            - (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ) := by
        simp only [X, Y, qc, Matrix.map_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, hiaC, q₀]
      have hrhs : (w' i : ℂ) + Complex.I * (β' w) i
          = ((w' i : ℂ) + Complex.I * b' i)
            - (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ) := by
        have hβ'i : (β' w) i
            = b' i + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁)
              * (q₀ i : ℂ) := rfl
        rw [hβ'i, mul_add,
          show Complex.I * (Complex.I * (a : ℂ)⁻¹
              * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ))
            = -((a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)) by
              rw [show Complex.I * (Complex.I * (a : ℂ)⁻¹
                    * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ))
                  = (Complex.I * Complex.I) * ((a : ℂ)⁻¹
                    * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)) from by ring,
                Complex.I_mul_I]; ring]
        ring
      rw [hlhs, hrhs]
    rw [hXshift, hiaC]
    have hcoef2 : (-(π : ℂ) / ((t * a : ℝ) : ℂ))
        = (-(π : ℂ) / (t : ℂ)) * (a : ℂ)⁻¹ := by push_cast; field_simp
    rw [hcoef2, mul_add]
    ring

  set eF : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  have hA' : (Matrix.reindex eF eF M).PosDef := by
    refine (posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
    · show _ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply,
        ← congrFun (congrFun hMT (eF.symm i)) (eF.symm j), Matrix.transpose_apply]
    · intro x hx
      have hxe : (fun i => x (eF i)) ≠ 0 := fun h => hx (funext fun j => by
        have := congrFun h (eF.symm j); simpa using this)
      have key := (posDef_iff_dotProduct_mulVec.mp hM).2 hxe
      refine lt_of_lt_of_eq key ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
        Matrix.submatrix_apply, star_trivial]
      refine Fintype.sum_equiv eF (fun i => x (eF i) * ∑ j, M i j * x (eF j))
        (fun i => x i * ∑ j, M (eF.symm i) (eF.symm j) * x j) fun i => ?_
      simp only [Equiv.symm_apply_apply]
      congr 1
      exact Fintype.sum_equiv eF (fun j => M i j * x (eF j))
        (fun j => M i (eF.symm j) * x j) fun j => by
          simp only [Equiv.symm_apply_apply]

  set ePi : (Fin (m + 1) → ℤ) ≃ ((Fin m ⊕ Fin 1) → ℤ) :=
    ⟨fun w => w ∘ eF, fun v => v ∘ eF.symm,
      fun w => funext fun j => congrArg w (eF.apply_symm_apply j),
      fun v => funext fun i => congrArg v (eF.symm_apply_apply i)⟩

  have hQeq : ∀ w : Fin (m + 1) → ℤ,
      rQuad (Matrix.reindex eF eF M) (zcastR w)
        = (fun i => ((ePi w) i : ℝ)) ⬝ᵥ (M *ᵥ fun i => ((ePi w) i : ℝ)) := fun w => by
    simp only [rQuad, zcastR, dotProduct, Matrix.mulVec, Matrix.reindex_apply,
      Matrix.submatrix_apply, ePi, Equiv.coe_fn_mk, Function.comp_apply]
    exact Fintype.sum_equiv eF.symm _ _ fun i => by
      simp only [Equiv.apply_symm_apply]
      exact congrArg _ (Fintype.sum_equiv eF.symm _ _ fun i' => by
        simp only [Equiv.apply_symm_apply])
  have hLeq : ∀ w : Fin (m + 1) → ℤ,
      (∑ j, (b ∘ eF.symm) j * (w j : ℂ)) = ∑ i, b i * ((ePi w) i : ℂ) := fun w =>
    Fintype.sum_equiv eF.symm _ _ fun j => by
      simp only [ePi, Equiv.coe_fn_mk, Function.comp_apply, Equiv.apply_symm_apply]

  let LB : ((Fin m ⊕ Fin 1) → ℤ) → ℂ := fun v =>
    cexp (-(π : ℂ) * t
        * (((fun i => (v i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℝ)) : ℝ) : ℂ)
      + 2 * π * ∑ i, b i * (v i : ℂ))
  let RB : ((Fin m ⊕ Fin 1) → ℤ) → ℂ := fun v =>
    cexp (-(π : ℂ) / t *
      ((fun i => (v i : ℂ) + Complex.I * b i) ⬝ᵥ
        ((M⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (v i : ℂ) + Complex.I * b i)))
  have hLBsum : Summable LB := by
    refine (Equiv.summable_iff ePi).mp
      (((gapsw80_t2_summable_thetaTerm hA' ht (b ∘ eF.symm)).of_norm).congr fun w => ?_)
    show thetaTerm _ _ _ w = LB (ePi w)
    simp only [thetaTerm, LB, hQeq w, hLeq w]
  have hLHSsum : Summable fun p : (Fin m → ℤ) × ℤ => LB (e.symm p) :=
    (e.symm.summable_iff (f := LB)).mpr hLBsum

  have hRBsum : Summable RB := by
    refine (Equiv.summable_iff ePi).mp
      (((gapsw80_t2_summable_dualTerm hA' ht (b ∘ eF.symm)).of_norm).congr fun w => ?_)
    show dualTerm _ _ _ w = RB (ePi w)
    simp only [dualTerm, cQuad, liftC, RB, Matrix.inv_reindex]
    congr 2
    simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.map_apply, ePi, Equiv.coe_fn_mk,
      Function.comp_apply]
    exact Fintype.sum_equiv eF.symm _ _ fun i => by
      simp only [Equiv.apply_symm_apply]
      exact congrArg₂ _ rfl (Fintype.sum_equiv eF.symm _ _ fun i' => by
        simp only [Equiv.apply_symm_apply])
  have hRHSsum : Summable fun p : (Fin m → ℤ) × ℤ => RB (e.symm p) :=
    (e.symm.summable_iff (f := RB)).mpr hRBsum

  have hLHSrw : ∀ p : (Fin m → ℤ) × ℤ,
      LB (e.symm p)
        = cexp (-(π : ℂ) * t * (rQuad S (zcastR p.1) : ℂ)
              + 2 * π * (∑ i, b' i * (p.1 i : ℂ))
            + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u p.1) ^ 2 : ℝ) : ℂ)))
          * cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (p.2 : ℂ) ^ 2
              + 2 * π * (β p.1) * (p.2 : ℂ)) := fun p => by
    show cexp _ = _
    rw [show e.symm p = Sum.elim p.1 (fun _ => p.2) from rfl,
      hQsplit p.1 p.2, hLsplit p.1 p.2, ← Complex.exp_add]
    congr 1; simp only [β]; push_cast; field_simp; ring

  have hFuwEq : ∀ p : (Fin m → ℤ) × ℤ,
      cexp (-(π : ℂ) * t * (rQuad S (zcastR p.1) : ℂ)
            + 2 * π * (∑ i, b' i * (p.1 i : ℂ))
          + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u p.1) ^ 2 : ℝ) : ℂ)))
        * cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((p.2 : ℂ) + Complex.I * (β p.1)) ^ 2)
      = Fuw p := fun p => by
    unfold Fuw thetaTerm rQuad; rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have key := hExpEq p.1 p.2
    linear_combination key

  have hR2'a : Summable Fuw := hR2'.of_norm
  have hFuwcomm : (∑' u, ∑' w, Fuw (u, w)) = ∑' w, ∑' u, Fuw (u, w) :=
    (Summable.tsum_comm (f := fun u w => Fuw (u, w))
      (show Summable (Function.uncurry fun u w => Fuw (u, w)) from hR2'a)).symm
  have hRHScomm : (∑' (w' : Fin m → ℤ), ∑' (w : ℤ), RB (e.symm (w', w)))
      = ∑' (w : ℤ), ∑' (w' : Fin m → ℤ), RB (e.symm (w', w)) :=
    (Summable.tsum_comm (f := fun w' w => RB (e.symm (w', w)))
      (show Summable (Function.uncurry fun w' w => RB (e.symm (w', w))) from
        hRHSsum)).symm
  show (∑' v, LB v) = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, RB w
  calc (∑' v, LB v)
      = ∑' p : (Fin m → ℤ) × ℤ, LB (e.symm p) := (e.symm.tsum_eq LB).symm
    _ = ∑' u : Fin m → ℤ, ∑' k : ℤ,
          cexp (-(π : ℂ) * t * (rQuad S (zcastR u) : ℂ)
                + 2 * π * (∑ i, b' i * (u i : ℂ))
              + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u u) ^ 2 : ℝ) : ℂ)))
            * cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (k : ℂ) ^ 2
                + 2 * π * (β u) * (k : ℂ)) := by
        rw [tsum_congr hLHSrw, (hLHSsum.congr hLHSrw).tsum_prod]
    _ = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' u : Fin m → ℤ, ∑' w : ℤ, Fuw (u, w) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun u => by
          rw [tsum_mul_left, h1D u, ← mul_assoc,
            mul_comm _ (1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)), mul_assoc,
            ← tsum_mul_left]
          exact congrArg _ (tsum_congr fun w => hFuwEq (u, w))
    _ = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' w : ℤ, cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
                * ((w : ℂ) + Complex.I * b₁) ^ 2)
              * ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                  * ∑' w', dualTerm S t (β' w) w') := by
        rw [hFuwcomm]
        exact congrArg _ (tsum_congr fun w => by
          simp only [Fuw]; rw [tsum_mul_left]
          exact congrArg _ (IH S hSpd ht (β' w)))
    _ = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
          * ∑' w : ℤ, ∑' w' : Fin m → ℤ, RB (e.symm (w', w)) := by
        have hperm : ∀ w : ℤ,
            cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
                * ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                    * ∑' w', dualTerm S t (β' w) w')
              = (((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                * ∑' w', RB (e.symm (w', w)) := fun w => by
          rw [← mul_assoc,
            mul_comm _ ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)), mul_assoc,
            ← tsum_mul_left]
          exact congrArg _ (tsum_congr fun w' => (hDualSplit w' w).symm)
        rw [tsum_congr hperm, tsum_mul_left, ← mul_assoc, hpref]
    _ = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, RB w := by
        rw [← hRHScomm, ← hRHSsum.tsum_prod, e.symm.tsum_eq]

end InductionStep
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

lemma gapsw80_t2_poissonLaw_reindex {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (t : ℝ) (b : Fin (m + 1) → ℂ) :
    PoissonLaw A t b ↔
      PoissonLawBlock (reindex finSumFinEquiv.symm finSumFinEquiv.symm A) t
        (b ∘ finSumFinEquiv) := by
  set eF : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  set M := reindex eF.symm eF.symm A with hM
  set ePi : (Fin (m + 1) → ℤ) ≃ ((Fin m ⊕ Fin 1) → ℤ) :=
    ⟨fun w => w ∘ eF, fun v => v ∘ eF.symm,
      fun w => funext fun j => congrArg w (eF.apply_symm_apply j),
      fun v => funext fun i => congrArg v (eF.symm_apply_apply i)⟩
  have hMentry : ∀ i j, M i j = A (eF i) (eF j) := fun i j => by
    simp only [hM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  have hdet : M.det = A.det := Matrix.det_reindex_self _ _
  have hMinv : ∀ i j, M⁻¹ i j = A⁻¹ (eF i) (eF j) := fun i j => by
    rw [hM, Matrix.inv_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  have hQeq : ∀ v : Fin (m + 1) → ℤ,
      rQuad A (zcastR v)
        = (fun i => ((ePi v) i : ℝ)) ⬝ᵥ (M *ᵥ fun i => ((ePi v) i : ℝ)) := fun v => by
    simp only [rQuad, zcastR, dotProduct, Matrix.mulVec, ePi, Equiv.coe_fn_mk,
      Function.comp_apply, hMentry]
    exact (Fintype.sum_equiv eF _ _ fun i => by
      exact congrArg _ (Fintype.sum_equiv eF _ _ fun i' => rfl)).symm
  have hLeq : ∀ v : Fin (m + 1) → ℤ,
      (∑ j, b j * (v j : ℂ)) = ∑ i, (b ∘ eF) i * ((ePi v) i : ℂ) := fun v =>
    (Fintype.sum_equiv eF _ _ fun i => rfl).symm
  have hDeq : ∀ w : Fin (m + 1) → ℤ,
      cQuad (liftC A⁻¹) (fun j => (w j : ℂ) + Complex.I * b j)
        = (fun i => ((ePi w) i : ℂ) + Complex.I * (b ∘ eF) i)
          ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
            *ᵥ fun i => ((ePi w) i : ℂ) + Complex.I * (b ∘ eF) i) := fun w => by
    simp only [cQuad, liftC, dotProduct, Matrix.mulVec, Matrix.map_apply, ePi,
      Equiv.coe_fn_mk, Function.comp_apply, hMinv]
    refine (Fintype.sum_equiv eF _ _ fun i => ?_).symm
    exact congrArg _ (Fintype.sum_equiv eF _ _ fun i' => rfl)
  have hLHSeq : (∑' v, thetaTerm A t b v)
      = ∑' x : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) * t
            * (((fun i => (x i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (x i : ℝ)) : ℝ) : ℂ)
          + 2 * π * ∑ i, (b ∘ eF) i * (x i : ℂ)) := by
    rw [← ePi.tsum_eq]
    exact tsum_congr fun v => by unfold thetaTerm; rw [hQeq v, hLeq v]
  have hRHSeq : (∑' w, dualTerm A t b w)
      = ∑' x : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) / t
            * ((fun i => (x i : ℂ) + Complex.I * (b ∘ eF) i)
              ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
                *ᵥ fun i => (x i : ℂ) + Complex.I * (b ∘ eF) i))) := by
    rw [← ePi.tsum_eq]
    exact tsum_congr fun w => by unfold dualTerm; rw [hDeq w]
  unfold PoissonLaw PoissonLawBlock
  rw [hLHSeq, hRHSeq, hdet]

theorem gapsw80_t2_rankNGaussianPoisson :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef →
      ∀ {t : ℝ}, 0 < t → ∀ b : Fin n → ℂ, PoissonLaw A t b := by
  intro n
  induction n with
  | zero =>
    intro A hA t ht b
    unfold PoissonLaw thetaTerm dualTerm rQuad cQuad
    simp only [dotProduct, Matrix.mulVec, Finset.univ_eq_empty, Finset.sum_empty,
      Complex.ofReal_zero, mul_zero, _root_.neg_zero, add_zero, Complex.exp_zero, pow_zero,
      one_mul, Matrix.det_fin_zero, Complex.ofReal_one, Complex.one_cpow]
  | succ m IH =>
    intro A hA t ht b
    rw [gapsw80_t2_poissonLaw_reindex]
    refine gapsw80_t2_poisson_step IH _ ?_ ht _
    have hAT : Aᵀ = A := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA.1
    refine (posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
    · show _ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Equiv.symm_symm,
        ← congrFun (congrFun hAT (finSumFinEquiv i)) (finSumFinEquiv j)]
    · intro x hx
      have hxe : (fun j => x (finSumFinEquiv.symm j)) ≠ 0 := fun h =>
        hx (funext fun i => by
          have := congrFun h (finSumFinEquiv i); simpa using this)
      have key := (posDef_iff_dotProduct_mulVec.mp hA).2 hxe
      refine lt_of_lt_of_eq key ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
        Matrix.submatrix_apply, star_trivial, Equiv.symm_symm]
      refine Fintype.sum_equiv finSumFinEquiv.symm _ _ fun j => ?_
      simp only [Equiv.apply_symm_apply]
      exact congrArg _ (Fintype.sum_equiv finSumFinEquiv.symm _ _ fun j' => by
        simp only [Equiv.apply_symm_apply])

theorem gapsw80_t2_rankNGaussianPoisson_real
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) {t : ℝ} (ht : 0 < t) :
    (∑' v : Fin n → ℤ,
        cexp ((-(π * t * (zcastR v ⬝ᵥ A *ᵥ zcastR v)) : ℝ) : ℂ))
      = (((t ^ n * A.det) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∑' w : Fin n → ℤ,
          cexp ((-(π * (zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w) / t) : ℝ) : ℂ) := by
  have h := gapsw80_t2_rankNGaussianPoisson n A hA ht (fun _ => 0)
  have hpos : (0 : ℝ) < t ^ n * A.det := mul_pos (pow_pos ht n) hA.det_pos
  have hpref : (((t ^ n * A.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
      = (((t ^ n * A.det) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [show (-(1 / 2) : ℂ) = (((-(1 / 2) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpos.le]
  have hθ0 : ∀ v, thetaTerm A t (fun _ => 0) v
      = cexp ((-(π * t * (zcastR v ⬝ᵥ A *ᵥ zcastR v)) : ℝ) : ℂ) := fun v => by
    unfold thetaTerm rQuad
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    push_cast; ring_nf
  have hδ0 : ∀ w, dualTerm A t (fun _ => 0) w
      = cexp ((-(π * (zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w) / t) : ℝ) : ℂ) := fun w => by
    unfold dualTerm cQuad liftC
    simp only [Pi.zero_apply, mul_zero, add_zero]
    congr 1
    have hQ : (fun i => (w i : ℂ)) ⬝ᵥ ((A⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (w i : ℂ))
        = (((zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w : ℝ)) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, zcastR,
        Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [hQ]; push_cast; ring
  unfold PoissonLaw at h
  rw [tsum_congr hθ0, tsum_congr hδ0, hpref] at h
  exact h

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

end FLT.Gapsw80T2RankNGaussianPoisson
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section

set_option maxHeartbeats 6400000

noncomputable section

namespace FLT
namespace Gapsw80T4MultiVarIdealThetaTransformation

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

def gapsw80_t4_placeOf : index K → InfinitePlace K :=
  Sum.elim (fun w => (w : InfinitePlace K)) (fun p => (p.1 : InfinitePlace K))

@[scoped simp] theorem placeOf_inl (w : {w : InfinitePlace K // IsReal w}) :
    gapsw80_t4_placeOf K (Sum.inl w) = (w : InfinitePlace K) := rfl

@[scoped simp] theorem placeOf_inr (p : {w : InfinitePlace K // IsComplex w} × Fin 2) :
    gapsw80_t4_placeOf K (Sum.inr p) = (p.1 : InfinitePlace K) := rfl

def gapsw80_t4_Dscale (y : InfinitePlace K → ℝ) : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.diagonal fun i => y (gapsw80_t4_placeOf K ((eIdx K).symm i))

theorem Dscale_posDef {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (gapsw80_t4_Dscale K y).PosDef :=
  Matrix.PosDef.diagonal fun i => hy _

theorem fiber_placeOf_isReal {w : InfinitePlace K} (hw : IsReal w) :
    (Finset.univ.filter fun j => gapsw80_t4_placeOf K j = w)
      = {Sum.inl ⟨w, hw⟩} := by
  ext j
  rcases j with ⟨v, hv⟩ | ⟨⟨v, hv⟩, k⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inl,
      Finset.mem_singleton, Sum.inl.injEq, Subtype.mk.injEq, Subtype.coe_mk]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inr,
      Finset.mem_singleton, Subtype.coe_mk]
    exact iff_of_false (fun h => (not_isReal_iff_isComplex.mpr hv) (h ▸ hw)) (by simp)

theorem fiber_placeOf_isComplex {w : InfinitePlace K} (hw : IsComplex w) :
    (Finset.univ.filter fun j => gapsw80_t4_placeOf K j = w)
      = {Sum.inr (⟨w, hw⟩, 0), Sum.inr (⟨w, hw⟩, 1)} := by
  ext j
  rcases j with ⟨v, hv⟩ | ⟨⟨v, hv⟩, k⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inl,
      Finset.mem_insert, Finset.mem_singleton, Subtype.coe_mk]
    exact iff_of_false (fun h => (not_isComplex_iff_isReal.mpr hv) (h ▸ hw)) (by simp)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, placeOf_inr,
      Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq, Prod.mk.injEq,
      Subtype.mk.injEq, Subtype.coe_mk]
    constructor
    · rintro rfl; fin_cases k <;> simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

theorem gapsw80_t4_det_Dscale (y : InfinitePlace K → ℝ) :
    (gapsw80_t4_Dscale K y).det = ∏ w : InfinitePlace K, y w ^ mult w := by
  rw [gapsw80_t4_Dscale, Matrix.det_diagonal,
    Fintype.prod_equiv (eIdx K).symm _ (fun j => y (gapsw80_t4_placeOf K j))
      (fun i => by simp),
    ← Finset.prod_fiberwise Finset.univ (fun j => gapsw80_t4_placeOf K j)
      (fun j => y (gapsw80_t4_placeOf K j))]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_eq_pow_card fun j hj => by
      rw [Finset.mem_filter] at hj; rw [hj.2]]
  congr 1
  rcases isReal_or_isComplex w with hw | hw
  · rw [mult, if_pos hw, fiber_placeOf_isReal K hw, Finset.card_singleton]
  · rw [mult, if_neg (not_isReal_iff_isComplex.mpr hw), fiber_placeOf_isComplex K hw,
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def gapsw80_t4_scaledGram (y : InfinitePlace K → ℝ) :
    Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  (coordMatrix K I)ᵀ * gapsw80_t4_Dscale K y * coordMatrix K I

theorem det_coordMatrix_ne_zero : (coordMatrix K I).det ≠ 0 := fun h =>
  (ZLattice.covolume_pos (mixedEmbedding.idealLattice K I) MeasureTheory.volume).ne'
    ((abs_det_coordMatrix K I).symm.trans (by rw [h, abs_zero]))

theorem isUnit_coordMatrix : IsUnit (coordMatrix K I) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_coordMatrix_ne_zero K I))

theorem gapsw80_t4_scaledGram_posDef {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (gapsw80_t4_scaledGram K I y).PosDef := by
  have h := (Dscale_posDef K hy).conjTranspose_mul_mul_same (B := coordMatrix K I)
    (Matrix.mulVec_injective_of_isUnit (isUnit_coordMatrix K I))
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem gapsw80_t4_det_scaledGram (y : InfinitePlace K → ℝ) :
    (gapsw80_t4_scaledGram K I y).det
      = (∏ w : InfinitePlace K, y w ^ mult w)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2 := by
  rw [gapsw80_t4_scaledGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    gapsw80_t4_det_Dscale, mul_comm (coordMatrix K I).det, mul_assoc, ← sq, ← sq_abs,
    abs_det_coordMatrix]

theorem sum_sq_repr_fiber_eq_normAtPlace_sq (x : mixedSpace K) (w : InfinitePlace K) :
    ∑ j ∈ Finset.univ.filter (fun j => gapsw80_t4_placeOf K j = w),
        ((mixedEmbedding.stdBasis K).repr x j) ^ 2
      = normAtPlace w x ^ 2 := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, fiber_placeOf_isReal K hw, Finset.sum_singleton,
      stdBasis_apply_isReal, Real.norm_eq_abs, sq_abs]
  · rw [normAtPlace_apply_of_isComplex hw, fiber_placeOf_isComplex K hw,
      Finset.sum_insert (by simp), Finset.sum_singleton,
      stdBasis_apply_isComplex_fst, stdBasis_apply_isComplex_snd,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring

theorem coordMatrix_mulVec_eq_repr (v : Fin (nK K) → ℤ) (i : Fin (nK K)) :
    ((coordMatrix K I) *ᵥ zcastR v) i
      = (mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) ((eIdx K).symm i) := by

  have hRHS : (mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) ((eIdx K).symm i)
      = ∑ j, (v j : ℝ) * (stdBasisFin K).repr
          (fractionalIdealLatticeBasis K I ((eI K I).symm j)) i := by
    rw [show (mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) ((eIdx K).symm i)
          = (stdBasisFin K).repr (zEquiv K I v : mixedSpace K) i by
        simp only [stdBasisFin, Basis.repr_reindex_apply],
      coe_zEquiv_apply, map_sum]
    simp only [map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hRHS, coordMatrix_eq_toMatrix, Matrix.mulVec]
  simp only [dotProduct, Basis.toMatrix_apply, Function.comp_apply, idealZBasis_apply, zcastR]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gapsw80_t4_quadForm_scaledGram (y : InfinitePlace K → ℝ) (v : Fin (nK K) → ℤ) :
    zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v
      = ∑ w : InfinitePlace K, y w * normAtPlace w (zEquiv K I v : mixedSpace K) ^ 2 := by

  have hstep1 : zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v
      = ((coordMatrix K I) *ᵥ zcastR v) ⬝ᵥ
          (gapsw80_t4_Dscale K y) *ᵥ ((coordMatrix K I) *ᵥ zcastR v) := by
    rw [gapsw80_t4_scaledGram, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (zcastR v) (coordMatrix K I)ᵀ,
      Matrix.vecMul_transpose]

  rw [hstep1]
  have hstep2 : ∀ u : Fin (nK K) → ℝ, u ⬝ᵥ (gapsw80_t4_Dscale K y) *ᵥ u
      = ∑ i, y (gapsw80_t4_placeOf K ((eIdx K).symm i)) * u i ^ 2 := fun u => by
    simp only [dotProduct, gapsw80_t4_Dscale, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hstep2,
    Fintype.sum_equiv (eIdx K).symm _
      (fun j => y (gapsw80_t4_placeOf K j)
        * ((mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) j) ^ 2)
      (fun i => by rw [coordMatrix_mulVec_eq_repr K I v i]),
    ← Finset.sum_fiberwise Finset.univ (fun j => gapsw80_t4_placeOf K j)
      (fun j => y (gapsw80_t4_placeOf K j)
        * ((mixedEmbedding.stdBasis K).repr (zEquiv K I v : mixedSpace K) j) ^ 2)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sum_sq_repr_fiber_eq_normAtPlace_sq K (zEquiv K I v : mixedSpace K) w,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j hj => by
    rw [Finset.mem_filter] at hj; rw [hj.2]

def gapsw80_t4_multiIdealTheta (y : InfinitePlace K → ℝ) : ℂ :=
  ∑' v : Fin (nK K) → ℤ, cexp ((-(π *
    (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ)

theorem gapsw80_t4_multiIdealTheta_eq_latticeSum (y : InfinitePlace K → ℝ) :
    gapsw80_t4_multiIdealTheta K I y
      = ∑' x : mixedEmbedding.idealLattice K I,
          cexp ((-(π *
            ∑ w : InfinitePlace K, y w * normAtPlace w (x : mixedSpace K) ^ 2) : ℝ) : ℂ) := by
  unfold gapsw80_t4_multiIdealTheta
  rw [← (zEquiv K I).toEquiv.tsum_eq]
  exact tsum_congr fun v => by rw [gapsw80_t4_quadForm_scaledGram]; rfl

theorem gapsw80_t4_scaledGram_const_eq (t : ℝ) :
    gapsw80_t4_scaledGram K I (fun _ => t) = t • gapsw80_t3_idealGram K I := by
  have hD : gapsw80_t4_Dscale K (fun _ => t) = Matrix.diagonal (fun _ => t) := rfl
  rw [gapsw80_t4_scaledGram, gapsw80_t3_idealGram_eq_transpose_mul, hD,
    show (Matrix.diagonal (fun _ : Fin (nK K) => t) : Matrix _ _ ℝ) = t • 1 by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, h],
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem gapsw80_t4_multiIdealTheta_transformation {y : InfinitePlace K → ℝ}
    (hy : ∀ w, 0 < y w) :
    gapsw80_t4_multiIdealTheta K I y
      = ((((∏ w : InfinitePlace K, y w ^ mult w)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∑' w : Fin (nK K) → ℤ,
          cexp ((-(π *
            (zcastR w ⬝ᵥ (gapsw80_t4_scaledGram K I y)⁻¹ *ᵥ zcastR w)) : ℝ) : ℂ) := by
  have h := gapsw80_t2_rankNGaussianPoisson_real (gapsw80_t4_scaledGram K I y)
    (gapsw80_t4_scaledGram_posDef K I hy) one_pos
  rw [gapsw80_t4_det_scaledGram, one_pow, one_mul] at h
  simp only [mul_one, div_one] at h
  exact h

theorem gapsw80_t4_scaledGram_inv_eq {y : InfinitePlace K → ℝ} (hy : ∀ w, 0 < y w) :
    (gapsw80_t4_scaledGram K I y)⁻¹
      = (coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K (fun w => (y w)⁻¹)
          * ((coordMatrix K I)ᵀ)⁻¹ := by
  have hD : gapsw80_t4_Dscale K (fun w => (y w)⁻¹) = (gapsw80_t4_Dscale K y)⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [show gapsw80_t4_Dscale K y
          = Matrix.diagonal fun i => y (gapsw80_t4_placeOf K ((eIdx K).symm i)) from rfl,
      show gapsw80_t4_Dscale K (fun w => (y w)⁻¹)
          = Matrix.diagonal fun i => (y (gapsw80_t4_placeOf K ((eIdx K).symm i)))⁻¹ from rfl,
      Matrix.diagonal_mul_diagonal, show (1 : Matrix (Fin (nK K)) (Fin (nK K)) ℝ)
          = Matrix.diagonal 1 from (Matrix.diagonal_one).symm]
    exact Matrix.diagonal_eq_diagonal_iff.mpr fun i => mul_inv_cancel₀ (hy _).ne'
  rw [hD, gapsw80_t4_scaledGram, Matrix.mul_assoc, Matrix.mul_inv_rev, Matrix.mul_inv_rev]

end FLT.Gapsw80T4MultiVarIdealThetaTransformation
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation"

section

set_option maxHeartbeats 6400000

noncomputable section

namespace FLT
namespace Gapsw80T5HeckeThetaKernel

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding.fundamentalCone"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"
open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T4MultiVarIdealThetaTransformation
p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

def gapsw80_t5_unitSqScale (η : (𝓞 K)ˣ) : realSpace K := fun w => (w (η : K)) ^ 2

theorem normAtPlace_unitSMul (η : (𝓞 K)ˣ) (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (η • x) = w (η : K) * normAtPlace w x := by
  rw [unitSMul_smul, map_mul, normAtPlace_apply]

theorem unitSMul_mem_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (η : (𝓞 K)ˣ)
    {x : mixedSpace K} (hx : x ∈ mixedEmbedding.idealLattice K I) :
    η • x ∈ mixedEmbedding.idealLattice K I := by
  obtain ⟨a, ha, rfl⟩ := (mem_idealLattice K I).mp hx
  refine (mem_idealLattice K I).mpr ⟨(η : 𝓞 K) • a, Submodule.smul_mem _ _ ha, ?_⟩
  rw [unitSMul_smul, Algebra.smul_def, map_mul]

def gapsw80_t5_unitSMulLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (η : (𝓞 K)ˣ) :
    mixedEmbedding.idealLattice K I ≃ mixedEmbedding.idealLattice K I where
  toFun x := ⟨η • (x : mixedSpace K), unitSMul_mem_idealLattice K I η x.2⟩
  invFun x := ⟨η⁻¹ • (x : mixedSpace K), unitSMul_mem_idealLattice K I η⁻¹ x.2⟩
  left_inv x := by
    simp only [Subtype.mk.injEq, inv_smul_smul]
  right_inv x := by
    simp only [Subtype.mk.injEq, smul_inv_smul]

theorem gapsw80_t5_multiIdealTheta_unitSq_smul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (η : (𝓞 K)ˣ) (y : InfinitePlace K → ℝ) :
    gapsw80_t4_multiIdealTheta K I (gapsw80_t5_unitSqScale K η * y)
      = gapsw80_t4_multiIdealTheta K I y := by
  rw [gapsw80_t4_multiIdealTheta_eq_latticeSum, gapsw80_t4_multiIdealTheta_eq_latticeSum]
  conv_rhs => rw [← (gapsw80_t5_unitSMulLatticeEquiv K I η).tsum_eq]
  refine tsum_congr fun x => ?_
  have hsum : ∑ w : InfinitePlace K,
        (gapsw80_t5_unitSqScale K η * y) w * normAtPlace w (x : mixedSpace K) ^ 2
      = ∑ w : InfinitePlace K,
        y w * normAtPlace w ((gapsw80_t5_unitSMulLatticeEquiv K I η x : mixedSpace K)) ^ 2 := by
    refine Finset.sum_congr rfl fun w _ => ?_
    show gapsw80_t5_unitSqScale K η w * y w * normAtPlace w (x : mixedSpace K) ^ 2
      = y w * normAtPlace w (η • (x : mixedSpace K)) ^ 2
    rw [normAtPlace_unitSMul, mul_pow, gapsw80_t5_unitSqScale]
    ring
  rw [hsum]

def gapsw80_t5_yParam (c : realSpace K) : realSpace K := fun w => (expMapBasis c w) ^ 2

theorem yParam_pos (c : realSpace K) (w : InfinitePlace K) :
    0 < gapsw80_t5_yParam K c w := pow_pos (expMapBasis_pos c w) 2

theorem gapsw80_t5_prod_yParam_mult (c : realSpace K) :
    ∏ w : InfinitePlace K, (gapsw80_t5_yParam K c w) ^ mult w
      = Real.exp (c w₀) ^ (2 * nK K) := by
  unfold gapsw80_t5_yParam
  simp_rw [← pow_mul, mul_comm 2, pow_mul]
  rw [Finset.prod_pow, prod_expMapBasis_pow, ← pow_mul, mul_comm]

theorem expMapBasis_neg (c : realSpace K) (w : InfinitePlace K) :
    expMapBasis (-c) w = (expMapBasis c w)⁻¹ := by
  rw [expMapBasis_apply, expMapBasis_apply, _root_.map_neg, expMap_apply, expMap_apply,
    Pi.neg_apply, mul_neg, Real.exp_neg]

theorem gapsw80_t5_yParam_neg (c : realSpace K) (w : InfinitePlace K) :
    gapsw80_t5_yParam K (-c) w = (gapsw80_t5_yParam K c w)⁻¹ := by
  unfold gapsw80_t5_yParam
  rw [expMapBasis_neg, inv_pow]

theorem expMapBasis_add_single {i : InfinitePlace K} (hi : i ≠ w₀) (c : realSpace K)
    (w : InfinitePlace K) :
    expMapBasis (c + Pi.single i 1) w
      = expMapBasis c w * w (fundSystem K (equivFinRank.symm ⟨i, hi⟩) : K) := by

  rw [expMapBasis_apply, expMapBasis_apply, map_add, expMap_add, Pi.mul_apply,
    show ((completeBasis K).equivFun.symm) (Pi.single i 1) = completeBasis K i by
      simp [Basis.equivFun_symm_apply, Pi.single_apply],
    completeBasis_apply_of_ne K ⟨i, hi⟩,
    show expMap (expMap.symm
        (normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))))) w
      = normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) w from
      congrFun (expMap.right_inv (by simp [expMap_target, pos_at_place])) w,
    normAtAllPlaces_apply, normAtPlace_apply]

theorem gapsw80_t5_yParam_add_single {i : InfinitePlace K} (hi : i ≠ w₀) (c : realSpace K) :
    gapsw80_t5_yParam K (c + Pi.single i 1)
      = gapsw80_t5_unitSqScale K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))
          * gapsw80_t5_yParam K c := by
  ext w
  unfold gapsw80_t5_yParam gapsw80_t5_unitSqScale
  rw [expMapBasis_add_single K hi, mul_pow, Pi.mul_apply, mul_comm]

def gapsw80_t5_mkParam (r : ℝ) (u : logSpace K) : realSpace K :=
  fun w => if h : w = w₀ then r else u ⟨w, h⟩

@[scoped simp] theorem mkParam_w₀ (r : ℝ) (u : logSpace K) : gapsw80_t5_mkParam K r u w₀ = r := by
  unfold gapsw80_t5_mkParam; rw [dif_pos rfl]

@[scoped simp] theorem mkParam_ne {w : InfinitePlace K} (hw : w ≠ w₀) (r : ℝ) (u : logSpace K) :
    gapsw80_t5_mkParam K r u w = u ⟨w, hw⟩ := by
  unfold gapsw80_t5_mkParam; rw [dif_neg hw]

theorem mkParam_neg (r : ℝ) (u : logSpace K) :
    gapsw80_t5_mkParam K (-r) (-u) = -(gapsw80_t5_mkParam K r u) := by
  ext w
  by_cases hw : w = w₀
  · simp [hw, mkParam_w₀]
  · simp [mkParam_ne K hw]

theorem gapsw80_t5_prod_yParam_mkParam (r : ℝ) (u : logSpace K) :
    ∏ w : InfinitePlace K, (gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u) w) ^ mult w
      = Real.exp r ^ (2 * nK K) := by
  rw [gapsw80_t5_prod_yParam_mult, mkParam_w₀]

theorem exp_half_log_pow_two_n {t : ℝ} (ht : 0 < t) :
    Real.exp (Real.log t / 2) ^ (2 * nK K) = t ^ (nK K) := by
  rw [pow_mul, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero,
    Real.exp_log ht]

def gapsw80_t5_heckeKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
    gapsw80_t4_multiIdealTheta K I
      (gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume

theorem gapsw80_t5_heckeKernel_transformation_raw (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          (∑' v : Fin (nK K) → ℤ,
            cexp ((-(π *
              (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I
                  (gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)))⁻¹
                *ᵥ zcastR v)) : ℝ) : ℂ)) ∂volume := by
  unfold gapsw80_t5_heckeKernel
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  rw [gapsw80_t4_multiIdealTheta_transformation K I (fun w => yParam_pos K _ w),
    gapsw80_t5_prod_yParam_mkParam, exp_half_log_pow_two_n K ht]

theorem gapsw80_t5_scaledGram_yParam_inv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) :
    (gapsw80_t4_scaledGram K I (gapsw80_t5_yParam K c))⁻¹
      = (coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K (gapsw80_t5_yParam K (-c))
          * ((coordMatrix K I)ᵀ)⁻¹ := by
  rw [gapsw80_t4_scaledGram_inv_eq K I (fun w => yParam_pos K c w),
    show (fun w => (gapsw80_t5_yParam K c w)⁻¹) = gapsw80_t5_yParam K (-c) from
      funext fun w => (gapsw80_t5_yParam_neg K c w).symm]

theorem gapsw80_t5_heckeKernel_transformation_raw' (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          (∑' v : Fin (nK K) → ℤ,
            cexp ((-(π *
              (zcastR v ⬝ᵥ ((coordMatrix K I)⁻¹
                  * gapsw80_t4_Dscale K
                      (gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t⁻¹ / 2) (-u)))
                  * ((coordMatrix K I)ᵀ)⁻¹)
                *ᵥ zcastR v)) : ℝ) : ℂ)) ∂volume := by
  rw [gapsw80_t5_heckeKernel_transformation_raw K I ht]
  congr 1
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1
  ext v
  rw [gapsw80_t5_scaledGram_yParam_inv,
    show gapsw80_t5_mkParam K (Real.log t⁻¹ / 2) (-u)
        = -(gapsw80_t5_mkParam K (Real.log t / 2) u) by
      rw [Real.log_inv, neg_div, ← mkParam_neg]]

end FLT.Gapsw80T5HeckeThetaKernel
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel"

section

set_option maxHeartbeats 6400000

noncomputable section

namespace FLT
namespace Gapsw80T6TraceDualBridge

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"
open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T4MultiVarIdealThetaTransformation FLT.Gapsw80T5HeckeThetaKernel
p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

def gapsw80_t6_multSign : index K → ℝ :=
  Sum.elim (fun _ => 1) (fun p => if p.2 = 0 then 2 else -2)

@[scoped simp] theorem multSign_inl (w : {w : InfinitePlace K // IsReal w}) :
    gapsw80_t6_multSign K (Sum.inl w) = 1 := rfl

@[scoped simp] theorem multSign_inr_fst (w : {w : InfinitePlace K // IsComplex w}) :
    gapsw80_t6_multSign K (Sum.inr (w, 0)) = 2 := rfl

@[scoped simp] theorem multSign_inr_snd (w : {w : InfinitePlace K // IsComplex w}) :
    gapsw80_t6_multSign K (Sum.inr (w, 1)) = -2 := rfl

theorem multSign_sq (c : index K) :
    (gapsw80_t6_multSign K c) ^ 2 = ((mult (gapsw80_t4_placeOf K c)) ^ 2 : ℝ) := by
  rcases c with ⟨w, hw⟩ | ⟨⟨w, hw⟩, j⟩
  · simp [mult, hw]
  · rw [placeOf_inr, mult, if_neg (not_isReal_iff_isComplex.mpr hw)]
    fin_cases j <;> simp [gapsw80_t6_multSign]

def gapsw80_t6_Phi : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  Matrix.diagonal fun i => gapsw80_t6_multSign K ((eIdx K).symm i)

theorem gapsw80_t6_Phi_Dscale_Phi (y : InfinitePlace K → ℝ) :
    (gapsw80_t6_Phi K)ᵀ * gapsw80_t4_Dscale K y * gapsw80_t6_Phi K
      = gapsw80_t4_Dscale K (fun w => (mult w : ℝ)^2 * y w) := by
  rw [gapsw80_t6_Phi, Matrix.diagonal_transpose, gapsw80_t4_Dscale, gapsw80_t4_Dscale,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  refine Matrix.diagonal_eq_diagonal_iff.mpr fun i => ?_
  rw [show gapsw80_t6_multSign K ((eIdx K).symm i) * y (gapsw80_t4_placeOf K ((eIdx K).symm i))
        * gapsw80_t6_multSign K ((eIdx K).symm i)
      = gapsw80_t6_multSign K ((eIdx K).symm i) ^ 2
        * y (gapsw80_t4_placeOf K ((eIdx K).symm i)) from by ring,
    multSign_sq]

theorem abs_multSign (c : index K) :
    |gapsw80_t6_multSign K c| = (mult (gapsw80_t4_placeOf K c) : ℝ) := by
  rcases c with ⟨w, hw⟩ | ⟨⟨w, hw⟩, j⟩
  · simp [mult, hw]
  · have hmult : mult (w : InfinitePlace K) = 2 := by
      rw [mult]; exact if_neg (not_isReal_iff_isComplex.mpr hw)
    fin_cases j <;> simp [gapsw80_t6_multSign, placeOf_inr, hmult]

theorem gapsw80_t6_abs_det_Phi :
    |(gapsw80_t6_Phi K).det| = (4 : ℝ) ^ nrComplexPlaces K := by
  rw [gapsw80_t6_Phi, Matrix.det_diagonal, Finset.abs_prod]
  calc ∏ i, |gapsw80_t6_multSign K ((eIdx K).symm i)|
      = ∏ c : index K, (mult (gapsw80_t4_placeOf K c) : ℝ) := by
        rw [Fintype.prod_equiv (eIdx K).symm _ (fun c => |gapsw80_t6_multSign K c|)
          (fun i => rfl)]
        exact Finset.prod_congr rfl fun c _ => abs_multSign K c
    _ = ∏ w : InfinitePlace K, (mult w : ℝ) ^ mult w := by
        rw [← Finset.prod_fiberwise Finset.univ (gapsw80_t4_placeOf K)
            (fun c => (mult (gapsw80_t4_placeOf K c) : ℝ))]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [Finset.prod_eq_pow_card fun c hc => by
              rw [Finset.mem_filter] at hc; rw [hc.2]]
        congr 1
        rcases isReal_or_isComplex w with hw | hw
        · rw [mult, if_pos hw, fiber_placeOf_isReal K hw, Finset.card_singleton]
        · rw [mult, if_neg (not_isReal_iff_isComplex.mpr hw), fiber_placeOf_isComplex K hw,
            Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    _ = (4 : ℝ) ^ nrComplexPlaces K := by
        rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => IsReal w)]
        simp only [mult_isReal, Nat.cast_one, one_pow, pow_one, Finset.prod_const_one, one_mul]
        have hmn : ∀ w : {w : InfinitePlace K // ¬IsReal w},
            mult (w : InfinitePlace K) = 2 :=
          fun w => by rw [mult, if_neg w.2]
        simp only [fun w => hmn w, Nat.cast_ofNat]
        rw [show ((2 : ℝ) ^ 2 : ℝ) = 4 from by norm_num, Finset.prod_const,
          Finset.card_univ]
        congr 1
        exact Fintype.card_congr
          (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex)

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def gapsw80_t6_idealBasisK (i : Fin (nK K)) : K :=
  basisOfFractionalIdeal K I ((eI K I).symm i)

theorem mixedEmbedding_idealBasisK (i : Fin (nK K)) :
    mixedEmbedding K (gapsw80_t6_idealBasisK K I i)
      = (idealZBasis K I i : mixedSpace K) := by
  rw [gapsw80_t6_idealBasisK, idealZBasis_apply, fractionalIdealLatticeBasis_apply]

theorem idealBasisK_mem (i : Fin (nK K)) :
    gapsw80_t6_idealBasisK K I i ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have h : gapsw80_t6_idealBasisK K I i ∈ ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
    rw [← mem_span_basisOfFractionalIdeal]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact h

def gapsw80_t6_biTerm (a b : K) (c : index K) : ℝ :=
  (mixedEmbedding.stdBasis K).repr (mixedEmbedding K a) c
    * gapsw80_t6_multSign K c
    * (mixedEmbedding.stdBasis K).repr (mixedEmbedding K b) c

theorem biTerm_isReal (a b : K) (w : {w : InfinitePlace K // IsReal w}) :
    gapsw80_t6_biTerm K a b (Sum.inl w)
      = embedding_of_isReal w.2 (a * b) := by
  unfold gapsw80_t6_biTerm
  rw [multSign_inl, mul_one, stdBasis_apply_isReal, stdBasis_apply_isReal,
    mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal, ← map_mul]

theorem biTerm_isComplex_sum (a b : K) (w : {w : InfinitePlace K // IsComplex w}) :
    gapsw80_t6_biTerm K a b (Sum.inr (w, 0)) + gapsw80_t6_biTerm K a b (Sum.inr (w, 1))
      = 2 * (w.1.embedding (a * b)).re := by
  unfold gapsw80_t6_biTerm
  simp only [multSign_inr_fst, multSign_inr_snd, stdBasis_apply_isComplex_fst,
    stdBasis_apply_isComplex_snd, mixedEmbedding_apply_isComplex, map_mul, Complex.mul_re]
  ring

theorem sum_biTerm_eq_sum_embeddings (a b : K) :
    ((∑ c : index K, gapsw80_t6_biTerm K a b c : ℝ) : ℂ)
      = ∑ φ : K →+* ℂ, φ (a * b) := by

  have hRHS : (∑ φ : K →+* ℂ, φ (a * b))
      = ∑ c : index K, (indexEquiv K c) (a * b) :=
    ((indexEquiv K).sum_comp (fun φ => φ (a * b))).symm
  rw [hRHS, Fintype.sum_sum_type, Fintype.sum_sum_type, Complex.ofReal_add,
    Complex.ofReal_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun w _ => ?_) ?_
  · rw [biTerm_isReal, indexEquiv_apply_isReal, ← embedding_of_isReal_apply w.2]
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Complex.ofReal_add, ← Complex.ofReal_add,
      biTerm_isComplex_sum, indexEquiv_apply_isComplex_fst, indexEquiv_apply_isComplex_snd,
      ComplexEmbedding.conjugate_coe_eq, Complex.add_conj, Complex.ofReal_mul,
      Complex.ofReal_ofNat]

theorem gapsw80_t6_stdBasis_Phi_bilinear_eq_trace (a b : K) :
    ∑ i : Fin (nK K),
      (stdBasisFin K).repr (mixedEmbedding K a) i
        * gapsw80_t6_multSign K ((eIdx K).symm i)
        * (stdBasisFin K).repr (mixedEmbedding K b) i
      = ((Algebra.trace ℚ K (a * b) : ℚ) : ℝ) := by

  have hLHS : ∑ i : Fin (nK K),
        (stdBasisFin K).repr (mixedEmbedding K a) i
          * gapsw80_t6_multSign K ((eIdx K).symm i)
          * (stdBasisFin K).repr (mixedEmbedding K b) i
      = ∑ c : index K, gapsw80_t6_biTerm K a b c := by
    rw [Fintype.sum_equiv (eIdx K).symm _ (gapsw80_t6_biTerm K a b) fun i => ?_]
    unfold gapsw80_t6_biTerm
    simp only [stdBasisFin, Basis.repr_reindex_apply]
  rw [hLHS]
  have hRHS : ((Algebra.trace ℚ K (a * b) : ℚ) : ℂ)
      = ∑ φ : K →+* ℂ, φ (a * b) := by
    rw [show ((Algebra.trace ℚ K (a * b) : ℚ) : ℂ)
          = algebraMap ℚ ℂ (Algebra.trace ℚ K (a * b)) from rfl,
      trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ),
      ← (RingHom.equivRatAlgHom (R := K) (S := ℂ)).sum_comp (fun σ => σ (a * b))]
    rfl
  have h := sum_biTerm_eq_sum_embeddings K a b
  rw [← hRHS] at h
  exact_mod_cast h

def gapsw80_t6_traceDualIdeal : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

@[scoped simp] theorem coe_traceDualIdeal :
    (gapsw80_t6_traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

def gapsw80_t6_bridgeMatrix : Matrix (Fin (nK K)) (Fin (nK K)) ℝ :=
  (coordMatrix K I)ᵀ * gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)

theorem coordMatrix_apply (i j : Fin (nK K)) :
    coordMatrix K I i j
      = (stdBasisFin K).repr (mixedEmbedding K (gapsw80_t6_idealBasisK K I j)) i := by
  rw [coordMatrix_eq_toMatrix, Basis.toMatrix_apply, mixedEmbedding_idealBasisK]

theorem gapsw80_t6_bridgeMatrix_entry_eq_trace (j k : Fin (nK K)) :
    gapsw80_t6_bridgeMatrix K I j k
      = ((Algebra.trace ℚ K
          (gapsw80_t6_idealBasisK K I j
            * gapsw80_t6_idealBasisK K (gapsw80_t6_traceDualIdeal K I) k) : ℚ) : ℝ) := by
  rw [← gapsw80_t6_stdBasis_Phi_bilinear_eq_trace, gapsw80_t6_bridgeMatrix,
    Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_apply, coordMatrix_apply,
    show (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)) i k
      = gapsw80_t6_multSign K ((eIdx K).symm i)
          * coordMatrix K (gapsw80_t6_traceDualIdeal K I) i k from by
      rw [gapsw80_t6_Phi, Matrix.diagonal_mul],
    coordMatrix_apply]
  ring

theorem gapsw80_t6_bridgeMatrix_entry_isInt (j k : Fin (nK K)) :
    ∃ m : ℤ, gapsw80_t6_bridgeMatrix K I j k = (m : ℝ) := by
  rw [gapsw80_t6_bridgeMatrix_entry_eq_trace]
  have hck : gapsw80_t6_idealBasisK K (gapsw80_t6_traceDualIdeal K I) k
      ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := idealBasisK_mem K (gapsw80_t6_traceDualIdeal K I) k
    rwa [coe_traceDualIdeal] at h
  have hint : Algebra.traceForm ℚ K
        (gapsw80_t6_idealBasisK K (gapsw80_t6_traceDualIdeal K I) k)
        (gapsw80_t6_idealBasisK K I j)
      ∈ (algebraMap ℤ ℚ).range :=
    (FractionalIdeal.mem_dual I.ne_zero).mp hck _ (idealBasisK_mem K I j)
  obtain ⟨m, hm⟩ := hint
  refine ⟨m, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm] at hm
  rw [← hm]
  simp only [eq_intCast, Rat.cast_intCast]

def gapsw80_t6_bridgeMatZ : Matrix (Fin (nK K)) (Fin (nK K)) ℤ :=
  fun j k => (gapsw80_t6_bridgeMatrix_entry_isInt K I j k).choose

theorem bridgeMatZ_cast_eq :
    (gapsw80_t6_bridgeMatZ K I).map (Int.cast : ℤ → ℝ) = gapsw80_t6_bridgeMatrix K I := by
  ext j k
  exact (gapsw80_t6_bridgeMatrix_entry_isInt K I j k).choose_spec.symm

theorem absNorm_traceDualIdeal :
    FractionalIdeal.absNorm
        (gapsw80_t6_traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
      = (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)
          * ((discr K).natAbs : ℚ))⁻¹ := by
  have hd1 : FractionalIdeal.absNorm
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
        = ((discr K).natAbs : ℚ)⁻¹ := by
    have hcoe : (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹
        = (↑(differentIdeal ℤ (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
      (coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)).symm
    rw [← inv_inv (FractionalIdeal.absNorm _), ← map_inv₀, hcoe,
      FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal (K := K)]
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv, map_mul, map_inv₀, hd1,
    mul_comm, ← mul_inv]

theorem gapsw80_t6_abs_det_bridgeMatrix :
    |(gapsw80_t6_bridgeMatrix K I).det| = 1 := by
  have hdet : |(gapsw80_t6_bridgeMatrix K I).det|
      = ZLattice.covolume (mixedEmbedding.idealLattice K I)
          * (4 : ℝ) ^ nrComplexPlaces K
          * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I)) := by
    rw [gapsw80_t6_bridgeMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, abs_mul, abs_det_coordMatrix, abs_det_coordMatrix, gapsw80_t6_abs_det_Phi]
  rw [hdet, mixedEmbedding.covolume_idealLattice, mixedEmbedding.covolume_idealLattice,
    absNorm_traceDualIdeal]
  have hD : (0 : ℝ) < |(discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hNI : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≠ 0 := by
    have hne := (FractionalIdeal.absNorm_eq_zero_iff (K := K)).not.mpr I.ne_zero
    exact_mod_cast hne
  have hsqD : (Real.sqrt |(discr K : ℝ)|) ^ 2 = |(discr K : ℝ)| :=
    Real.sq_sqrt (abs_nonneg _)
  have hnatAbs : ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h4 : (4 : ℝ) ^ nrComplexPlaces K * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K) ^ 2 = 1 := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul,
      mul_comm 2 (nrComplexPlaces K), ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]

  push_cast
  rw [hnatAbs, mul_inv]
  have hgoal : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
        * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|
        * (4 : ℝ) ^ nrComplexPlaces K
        * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)⁻¹
            * |(discr K : ℝ)|⁻¹ * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)
      = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
            * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)⁻¹)
          * ((Real.sqrt |(discr K : ℝ)|) ^ 2 * |(discr K : ℝ)|⁻¹)
          * ((4 : ℝ) ^ nrComplexPlaces K * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K) ^ 2) := by
    ring
  rw [hgoal, mul_inv_cancel₀ hNI, hsqD, mul_inv_cancel₀ hD.ne', h4, one_mul, one_mul]

theorem cast_det_bridgeMatZ :
    ((gapsw80_t6_bridgeMatZ K I).det : ℝ) = (gapsw80_t6_bridgeMatrix K I).det := by
  have h : ((gapsw80_t6_bridgeMatZ K I).map (Int.cast : ℤ → ℝ)).det
      = (gapsw80_t6_bridgeMatrix K I).det := by rw [bridgeMatZ_cast_eq]
  rw [← h]
  exact (RingHom.map_det (Int.castRingHom ℝ) (gapsw80_t6_bridgeMatZ K I)).trans
    (congrArg Matrix.det rfl)

theorem bridgeMatZ_isUnit : IsUnit (gapsw80_t6_bridgeMatZ K I) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h1 : |((gapsw80_t6_bridgeMatZ K I).det : ℝ)| = 1 := by
    rw [cast_det_bridgeMatZ, gapsw80_t6_abs_det_bridgeMatrix]
  have hn : (gapsw80_t6_bridgeMatZ K I).det.natAbs = 1 := by
    have h2 : ((gapsw80_t6_bridgeMatZ K I).det.natAbs : ℝ) = 1 := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact h1
    exact_mod_cast h2
  exact Int.isUnit_iff_natAbs_eq.mpr hn

def gapsw80_t6_bridgeMatZUnit : (Matrix (Fin (nK K)) (Fin (nK K)) ℤ)ˣ :=
  (bridgeMatZ_isUnit K I).unit

@[scoped simp] theorem coe_bridgeMatZUnit :
    ((gapsw80_t6_bridgeMatZUnit K I : Matrix (Fin (nK K)) (Fin (nK K)) ℤ))
      = gapsw80_t6_bridgeMatZ K I := rfl

def gapsw80_t6_bridgeEquiv : (Fin (nK K) → ℤ) ≃ (Fin (nK K) → ℤ) where
  toFun v := ((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val *ᵥ v
  invFun v := (gapsw80_t6_bridgeMatZUnit K I).val *ᵥ v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem zcastR_bridgeEquiv_apply (v : Fin (nK K) → ℤ) :
    zcastR (gapsw80_t6_bridgeEquiv K I v)
      = (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
          *ᵥ zcastR v := by
  ext i
  change ((((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val *ᵥ v) i : ℝ) = _
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, zcastR]
  push_cast
  rfl

theorem bridgeMatrix_mul_cast_inv :
    gapsw80_t6_bridgeMatrix K I
        * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = 1 := by
  have h : (gapsw80_t6_bridgeMatZ K I) * ((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val
      = 1 := by
    conv_lhs => rw [← coe_bridgeMatZUnit, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmap : ((gapsw80_t6_bridgeMatZ K I) * ((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val).map
        (Int.cast : ℤ → ℝ)
      = gapsw80_t6_bridgeMatrix K I
          * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ)) := by
    have := map_mul (Int.castRingHom ℝ).mapMatrix (gapsw80_t6_bridgeMatZ K I)
      ((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val
    simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at this
    rw [this, bridgeMatZ_cast_eq]
  rw [← hmap, h]
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply, apply_ite (Int.cast : ℤ → ℝ)]

theorem Phi_mul_coordMatrix_mul_cast_inv :
    gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)
        * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = ((coordMatrix K I)ᵀ)⁻¹ := by
  have hunit : IsUnit ((coordMatrix K I)ᵀ).det := by
    rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr (det_coordMatrix_ne_zero K I)
  have hcancel : ((coordMatrix K I)ᵀ)⁻¹ * (coordMatrix K I)ᵀ = 1 :=
    Matrix.nonsing_inv_mul _ hunit
  calc gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)
        * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))
      = (((coordMatrix K I)ᵀ)⁻¹ * (coordMatrix K I)ᵀ)
          * (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)
              * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))) := by
        rw [hcancel, one_mul]
    _ = ((coordMatrix K I)ᵀ)⁻¹
          * (gapsw80_t6_bridgeMatrix K I
              * (((gapsw80_t6_bridgeMatZUnit K I)⁻¹).val.map (Int.cast : ℤ → ℝ))) := by
        rw [gapsw80_t6_bridgeMatrix, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = ((coordMatrix K I)ᵀ)⁻¹ := by
        rw [bridgeMatrix_mul_cast_inv, mul_one]

theorem gapsw80_t6_dualQuadForm_eq (y' : InfinitePlace K → ℝ) (v : Fin (nK K) → ℤ) :
    zcastR v ⬝ᵥ ((coordMatrix K I)⁻¹
        * gapsw80_t4_Dscale K y' * ((coordMatrix K I)ᵀ)⁻¹) *ᵥ zcastR v
      = zcastR (gapsw80_t6_bridgeEquiv K I v) ⬝ᵥ
          gapsw80_t4_scaledGram K (gapsw80_t6_traceDualIdeal K I)
            (fun w => (mult w : ℝ)^2 * y' w)
          *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v) := by

  have hMv : ((coordMatrix K I)ᵀ)⁻¹ *ᵥ zcastR v
      = (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))
          *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v) := by
    rw [zcastR_bridgeEquiv_apply, Matrix.mulVec_mulVec, Phi_mul_coordMatrix_mul_cast_inv]

  have hLHS : zcastR v ⬝ᵥ ((coordMatrix K I)⁻¹ * gapsw80_t4_Dscale K y'
        * ((coordMatrix K I)ᵀ)⁻¹) *ᵥ zcastR v
      = (((coordMatrix K I)ᵀ)⁻¹ *ᵥ zcastR v) ⬝ᵥ
          (gapsw80_t4_Dscale K y') *ᵥ (((coordMatrix K I)ᵀ)⁻¹ *ᵥ zcastR v) := by
    rw [show (coordMatrix K I)⁻¹ = (((coordMatrix K I)ᵀ)⁻¹)ᵀ from by
          rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose],
      Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (zcastR v) (((coordMatrix K I)ᵀ)⁻¹)ᵀ, Matrix.vecMul_transpose]

  have hRHS : zcastR (gapsw80_t6_bridgeEquiv K I v) ⬝ᵥ
        (gapsw80_t4_scaledGram K (gapsw80_t6_traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w))
        *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v)
      = ((gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))
            *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v))
          ⬝ᵥ (gapsw80_t4_Dscale K y')
          *ᵥ ((gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))
            *ᵥ zcastR (gapsw80_t6_bridgeEquiv K I v)) := by
    have hG : gapsw80_t4_scaledGram K (gapsw80_t6_traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w)
        = (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))ᵀ
            * gapsw80_t4_Dscale K y'
            * (gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I)) := by
      rw [gapsw80_t4_scaledGram, ← gapsw80_t6_Phi_Dscale_Phi, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hG, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec _
        ((gapsw80_t6_Phi K * coordMatrix K (gapsw80_t6_traceDualIdeal K I))ᵀ),
      Matrix.vecMul_transpose]
  rw [hLHS, hRHS, hMv]

theorem gapsw80_t6_dualGramSum_eq_multiIdealTheta_codiff (y' : InfinitePlace K → ℝ) :
    (∑' v : Fin (nK K) → ℤ,
      cexp ((-(π * (zcastR v ⬝ᵥ ((coordMatrix K I)⁻¹
          * gapsw80_t4_Dscale K y' * ((coordMatrix K I)ᵀ)⁻¹)
        *ᵥ zcastR v)) : ℝ) : ℂ))
      = gapsw80_t4_multiIdealTheta K (gapsw80_t6_traceDualIdeal K I)
          (fun w => (mult w : ℝ)^2 * y' w) := by
  conv_rhs => rw [gapsw80_t4_multiIdealTheta, ← (gapsw80_t6_bridgeEquiv K I).tsum_eq]
  exact tsum_congr fun v => by rw [gapsw80_t6_dualQuadForm_eq]

theorem gapsw80_t6_heckeKernel_transformation_bridged
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∫ u in (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1),
          gapsw80_t4_multiIdealTheta K (gapsw80_t6_traceDualIdeal K I)
            (fun w => (mult w : ℝ)^2 * gapsw80_t5_yParam K
              (gapsw80_t5_mkParam K (Real.log t⁻¹ / 2) (-u)) w) ∂MeasureTheory.volume := by
  rw [gapsw80_t5_heckeKernel_transformation_raw' K I ht]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  rw [← gapsw80_t6_dualGramSum_eq_multiIdealTheta_codiff]

end FLT.Gapsw80T6TraceDualBridge
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

section

set_option maxHeartbeats 6400000

noncomputable section

namespace FLT
namespace Gapsw80T7ClosedFEWeakPair

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding.fundamentalCone"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"
open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T4MultiVarIdealThetaTransformation FLT.Gapsw80T5HeckeThetaKernel
open FLT.Gapsw80T6TraceDualBridge
p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Asymptotics P2MW.S_NumberField_exists_completedDedekindZeta_package.Asymptotics Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Asymptotics.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

def gapsw80_t7_multSq : realSpace K := fun w => ((mult w : ℝ)) ^ 2

theorem multSq_pos (w : InfinitePlace K) : 0 < gapsw80_t7_multSq K w :=
  pow_pos (Nat.cast_pos.mpr mult_pos) 2

theorem multSq_unitSqScale_comm (η : (𝓞 K)ˣ) (y : realSpace K) :
    gapsw80_t7_multSq K * (gapsw80_t5_unitSqScale K η * y)
      = gapsw80_t5_unitSqScale K η * (gapsw80_t7_multSq K * y) := by
  ext w; simp only [Pi.mul_apply]; ring

theorem gapsw80_t7_multiIdealTheta_multSq_yParam_periodic
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {i : InfinitePlace K} (hi : i ≠ w₀)
    (c : realSpace K) :
    gapsw80_t4_multiIdealTheta K J
        (gapsw80_t7_multSq K * gapsw80_t5_yParam K (c + Pi.single i 1))
      = gapsw80_t4_multiIdealTheta K J
          (gapsw80_t7_multSq K * gapsw80_t5_yParam K c) := by
  rw [gapsw80_t5_yParam_add_single K hi, multSq_unitSqScale_comm,
    gapsw80_t5_multiIdealTheta_unitSq_smul]

theorem mkParam_add_single (r : ℝ) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) :
    gapsw80_t5_mkParam K r (u + Pi.single i 1)
      = gapsw80_t5_mkParam K r u + Pi.single (i : InfinitePlace K) 1 := by
  ext w
  by_cases hw : w = w₀
  · subst hw
    simp only [mkParam_w₀, Pi.add_apply, Pi.single_eq_of_ne' i.2, add_zero]
  · simp only [mkParam_ne K hw, Pi.add_apply]
    by_cases hwi : w = (i : InfinitePlace K)
    · subst hwi
      simp [Pi.single_eq_same, show (⟨(i:InfinitePlace K), hw⟩ : {w // w ≠ w₀}) = i from
        Subtype.ext rfl]
    · rw [Pi.single_eq_of_ne (fun h => hwi (Subtype.ext_iff.mp h)),
        Pi.single_eq_of_ne hwi, add_zero]

abbrev gapsw80_t7_integrand (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ)
    (u : logSpace K) : ℂ :=
  gapsw80_t4_multiIdealTheta K J
    (gapsw80_t7_multSq K * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u))

theorem gapsw80_t7_integrand_single_zperiodic (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (r : ℝ) (i : {w : InfinitePlace K // w ≠ w₀}) (k : ℤ) (u : logSpace K) :
    gapsw80_t7_integrand K J r (u + k • Pi.single i 1) = gapsw80_t7_integrand K J r u := by
  have hstep : ∀ v : logSpace K,
      gapsw80_t7_integrand K J r (v + Pi.single i 1) = gapsw80_t7_integrand K J r v := fun v => by
    unfold gapsw80_t7_integrand
    rw [mkParam_add_single, gapsw80_t7_multiIdealTheta_multSq_yParam_periodic K J i.2]
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [add_smul, one_smul, ← add_assoc, hstep]; exact ih
  | pred n ih =>
    have h' := (hstep (u + (-(n : ℤ) - 1) • Pi.single i 1)).symm
    rw [add_assoc, show (-(n:ℤ)-1) • Pi.single i (1:ℝ) + (Pi.single i 1 : logSpace K)
        = (-(n:ℤ)) • Pi.single i 1 from by rw [sub_smul, one_smul, sub_add_cancel]] at h'
    exact h'.trans ih

theorem gapsw80_t7_integrand_zlattice_invariant (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (r : ℝ) (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (u : logSpace K) :
    gapsw80_t7_integrand K J r ((g : logSpace K) + u) = gapsw80_t7_integrand K J r u := by
  have hmem := g.2
  rw [Basis.mem_span_iff_repr_mem] at hmem
  simp only [Pi.basisFun_repr] at hmem
  choose k hk using hmem
  have hg : (g : logSpace K) = ∑ i, (k i) • Pi.single i (1:ℝ) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← hk, eq_intCast]
    simp [zsmul_eq_mul]
  rw [hg]

  induction (Finset.univ : Finset {w : InfinitePlace K // w ≠ w₀}) using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj,
      show (k j • Pi.single j (1:ℝ) + ∑ i ∈ s, k i • Pi.single i 1) + u
          = (∑ i ∈ s, k i • Pi.single i 1 + u) + k j • Pi.single j 1 from by abel,
      gapsw80_t7_integrand_single_zperiodic]
    exact ih

abbrev gapsw80_t7_unitBox : Set (logSpace K) :=
  Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Ico (0 : ℝ) 1

theorem unitBox_eq_fundamentalDomain :
    gapsw80_t7_unitBox K
      = ZSpan.fundamentalDomain (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}) :=
  (ZSpan.fundamentalDomain_pi_basisFun).symm

theorem gapsw80_t7_unitBox_isAddFundamentalDomain :
    IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      (gapsw80_t7_unitBox K) volume := by
  rw [unitBox_eq_fundamentalDomain]
  exact ZSpan.isAddFundamentalDomain _ volume

local instance : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (logSpace K) volume :=
  ⟨fun g s _ => measure_preimage_add _ _ _⟩

local instance : Countable
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))) := by
  refine Countable.of_equiv ({w : InfinitePlace K // w ≠ w₀} → ℤ)
    (Equiv.ofBijective
      (fun k : {w : InfinitePlace K // w ≠ w₀} → ℤ =>
        (⟨fun i => (k i : ℝ), ?_⟩ :
          Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))))
      ⟨?_, ?_⟩)
  · rw [Basis.mem_span_iff_repr_mem]; intro i; exact ⟨k i, by simp⟩
  · intro k₁ k₂ h
    exact funext fun i => Int.cast_injective (congr_fun (Subtype.ext_iff.mp h) i)
  · intro ⟨v, hv⟩
    rw [Basis.mem_span_iff_repr_mem] at hv
    simp only [Pi.basisFun_repr] at hv
    choose k hk using hv
    exact ⟨k, Subtype.ext (funext fun i => by simp [← hk i, eq_intCast])⟩

theorem gapsw80_t7_neg_unitBox_isAddFundamentalDomain :
    IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      ((Neg.neg : logSpace K → logSpace K) '' gapsw80_t7_unitBox K) volume := by
  refine (gapsw80_t7_unitBox_isAddFundamentalDomain K).image_of_equiv
    (Equiv.neg (logSpace K))
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
    (Equiv.neg _) ?_
  intro g x
  show -((-g : logSpace K) + x) = (g : logSpace K) + -x
  simp only [neg_add, neg_neg]

theorem gapsw80_t7_setIntegral_neg_box_eq (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J r (-u) ∂volume
      = ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J r u ∂volume := by

  calc ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J r (-u) ∂volume
      = ∫ v in (Neg.neg : logSpace K → logSpace K) '' gapsw80_t7_unitBox K,
          gapsw80_t7_integrand K J r v ∂volume :=
        ((Measure.measurePreserving_neg (volume : Measure (logSpace K))).setIntegral_image_emb
          (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.neg (logSpace K)))
          (gapsw80_t7_integrand K J r) (gapsw80_t7_unitBox K)).symm
    _ = ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J r u ∂volume :=
        (gapsw80_t7_neg_unitBox_isAddFundamentalDomain K).setIntegral_eq
          (gapsw80_t7_unitBox_isAddFundamentalDomain K)
          (fun g u => gapsw80_t7_integrand_zlattice_invariant K J r g u)

def gapsw80_t7_multHeckeKernel (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in gapsw80_t7_unitBox K, gapsw80_t7_integrand K J (Real.log t / 2) u ∂volume

theorem gapsw80_t7_heckeKernel_closed_FE (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t
      = ((((t : ℝ) ^ (nK K)
          * (ZLattice.covolume (mixedEmbedding.idealLattice K I)) ^ 2) ^ (-(1/2) : ℝ) : ℝ) : ℂ)
        * gapsw80_t7_multHeckeKernel K (gapsw80_t6_traceDualIdeal K I) t⁻¹ := by
  rw [gapsw80_t6_heckeKernel_transformation_bridged K I ht, gapsw80_t7_multHeckeKernel]
  congr 1

  rw [← gapsw80_t7_setIntegral_neg_box_eq K (gapsw80_t6_traceDualIdeal K I) (Real.log t⁻¹ / 2)]
  rfl

theorem gapsw80_t7_covol_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < ZLattice.covolume (mixedEmbedding.idealLattice K I) :=
  ZLattice.covolume_pos _ volume

theorem rpow_factor_h_feq {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    (x⁻¹ ^ n * c ^ 2) ^ (-(1/2) : ℝ) = x ^ ((n : ℝ)/2) * c⁻¹ := by
  have h1 : (x⁻¹ ^ n : ℝ) ^ (-(1/2) : ℝ) = x ^ ((n : ℝ)/2) := by
    rw [← Real.rpow_natCast x⁻¹, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le,
      ← Real.rpow_mul hx.le]
    ring_nf
  have h2 : (c ^ 2 : ℝ) ^ (-(1/2) : ℝ) = c⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hc.le]
    norm_num
    exact Real.rpow_neg_one c
  rw [Real.mul_rpow (by positivity) (by positivity), h1, h2]

theorem gapsw80_t7_h_feq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      gapsw80_t5_heckeKernel K I (1 / x)
        = (((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹
            * ((x ^ ((nK K : ℝ)/2) : ℝ) : ℂ))
          • gapsw80_t7_multHeckeKernel K (gapsw80_t6_traceDualIdeal K I) x := by
  intro x hx
  have hx' : (0:ℝ) < x := hx
  have h1x : (0:ℝ) < 1/x := by positivity
  rw [gapsw80_t7_heckeKernel_closed_FE K I h1x, one_div, inv_inv, smul_eq_mul]
  congr 1
  rw [rpow_factor_h_feq hx' (gapsw80_t7_covol_pos K I)]
  push_cast
  ring

def gapsw80_t7_unitPart (u : logSpace K) : realSpace K := fun w =>
  (∏ i : {w : InfinitePlace K // w ≠ w₀},
    (w (fundSystem K (equivFinRank.symm i) : K)) ^ (u i)) ^ 2

theorem unitPart_pos (u : logSpace K) (w : InfinitePlace K) :
    0 < gapsw80_t7_unitPart K u w := by
  refine pow_pos (Finset.prod_pos fun i _ => ?_) 2
  exact Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _

theorem gapsw80_t7_yParam_mkParam_factor {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (w : InfinitePlace K) :
    gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u) w
      = t * gapsw80_t7_unitPart K u w := by
  unfold gapsw80_t5_yParam gapsw80_t7_unitPart
  rw [expMapBasis_apply']
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mkParam_w₀,
    ← Real.exp_nat_mul, show (2:ℕ) * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]
  congr 2
  exact Finset.prod_congr rfl fun i _ => by rw [mkParam_ne K i.2]

theorem continuous_unitPart (w : InfinitePlace K) :
    Continuous fun u : logSpace K => gapsw80_t7_unitPart K u w := by
  unfold gapsw80_t7_unitPart
  refine (continuous_finset_prod _ fun i _ => ?_).pow 2
  exact (Real.continuous_const_rpow
    (pos_iff.mpr (by simp [fundSystem])).ne').comp (continuous_apply i)

theorem gapsw80_t7_unitPart_lower_bound :
    ∃ c > 0, ∀ u ∈ (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1),
      ∀ w, c ≤ gapsw80_t7_unitPart K u w := by
  have hcpct : IsCompact (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hne : (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1).Nonempty :=
    ⟨0, fun i _ => by simp⟩

  have hw : ∀ w : InfinitePlace K, ∃ c > 0,
      ∀ u ∈ (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1),
        c ≤ gapsw80_t7_unitPart K u w := fun w => by
    obtain ⟨u₀, hu₀, hmin⟩ := hcpct.exists_isMinOn hne (continuous_unitPart K w).continuousOn
    exact ⟨gapsw80_t7_unitPart K u₀ w, unitPart_pos K u₀ w, fun u hu => hmin hu⟩
  choose c hcpos hc using hw
  refine ⟨Finset.univ.inf' ⟨w₀, Finset.mem_univ _⟩ c, ?_, fun u hu w => ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun w _ => hcpos w
  · exact (Finset.inf'_le c (Finset.mem_univ w)).trans (hc w u hu)

theorem isCompact_sum_sq_eq_one :
    IsCompact {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} := by
  have hclosed : IsClosed {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hbdd : {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} ⊆ Metric.closedBall 0 1 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hle : w i ^ 2 ≤ 1 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)).trans_eq hw
    calc ‖w i‖ = |w i| := Real.norm_eq_abs _
      _ = √(w i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  exact (Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hclosed, Metric.isBounded_closedBall.subset hbdd⟩)

theorem gapsw80_t7_idealGram_lower_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ lam > 0, ∀ v : Fin (nK K) → ℤ,
      lam * ∑ i, (v i : ℝ)^2 ≤ zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v := by
  set F : (Fin (nK K) → ℝ) → ℝ := fun w => w ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ w with hF
  have hFcont : Continuous F := by unfold F; fun_prop
  have hFscale : ∀ (c : ℝ) (w : Fin (nK K) → ℝ), F (c • w) = c^2 * F w := fun c w => by
    simp only [hF, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, sq, mul_assoc]
  have hSne : {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1}.Nonempty := by
    refine ⟨Pi.single (⟨0, Module.finrank_pos⟩ : Fin (nK K)) 1, ?_⟩
    simp only [Set.mem_setOf_eq, Pi.single_apply, ite_pow, one_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  obtain ⟨ww, hww, hmin⟩ := (isCompact_sum_sq_eq_one K).exists_isMinOn hSne hFcont.continuousOn
  have hne : ww ≠ 0 := fun habs => by rw [habs] at hww; simp at hww
  have hlam : 0 < F ww := by
    have h := (gapsw80_t3_idealGram_posDef K I).dotProduct_mulVec_pos hne
    simpa [hF] using h
  refine ⟨F ww, hlam, fun v => ?_⟩
  by_cases hv : zcastR v = 0
  · have hsum0 : ∑ i, (v i : ℝ)^2 = 0 := Finset.sum_eq_zero fun i _ => by
      have h0 : (v i : ℝ) = 0 := congr_fun hv i; rw [h0]; ring
    simp only [hsum0, mul_zero, hv, hF, Matrix.mulVec_zero, dotProduct_zero, le_refl]
  ·
    set s : ℝ := Real.sqrt (∑ i, (v i : ℝ)^2) with hs_def
    have hsumpos : 0 < ∑ i, (v i : ℝ)^2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ?_
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact ⟨i, Finset.mem_univ i, by
        simp only [zcastR, Pi.zero_apply] at hi; positivity⟩
    have hspos : 0 < s := Real.sqrt_pos.mpr hsumpos
    have hs_sq : s^2 = ∑ i, (v i : ℝ)^2 := Real.sq_sqrt hsumpos.le
    have hmem : s⁻¹ • zcastR v ∈ {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} := by
      simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
        ← hs_sq, inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hspos.ne')
    calc F ww * ∑ i, (v i : ℝ)^2
        = s^2 * F ww := by rw [hs_sq, mul_comm]
      _ ≤ s^2 * F (s⁻¹ • zcastR v) :=
          mul_le_mul_of_nonneg_left (hmin hmem) (sq_nonneg s)
      _ = F (s • (s⁻¹ • zcastR v)) := (hFscale s _).symm
      _ = zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v := by
          rw [smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]

theorem multiIdealTheta_zero_term (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : InfinitePlace K → ℝ) :
    cexp ((-(π * (zcastR (0 : Fin (nK K) → ℤ) ⬝ᵥ (gapsw80_t4_scaledGram K I y)
      *ᵥ zcastR 0)) : ℝ) : ℂ) = 1 := by
  simp [zcastR, dotProduct]

theorem scaledGram_lower_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℝ}
    {y : InfinitePlace K → ℝ} (hy : ∀ w, c ≤ y w) (v : Fin (nK K) → ℤ) :
    c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)
      ≤ zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v := by
  have hGram1 : gapsw80_t3_idealGram K I = gapsw80_t4_scaledGram K I (fun _ => (1:ℝ)) := by
    rw [gapsw80_t4_scaledGram_const_eq, one_smul]
  rw [hGram1, gapsw80_t4_quadForm_scaledGram, gapsw80_t4_quadForm_scaledGram, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => by
    rw [one_mul]; exact mul_le_mul_of_nonneg_right (hy w) (sq_nonneg _)

theorem one_le_sum_sq_of_ne_zero {v : Fin (nK K) → ℤ} (hv : v ≠ 0) :
    (1 : ℝ) ≤ ∑ i, (v i : ℝ)^2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h1 : (1:ℝ) ≤ (v i : ℝ)^2 := by
    have : (1:ℤ) ≤ |v i| := Int.one_le_abs (by simpa using hi)
    have habs : (1:ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast this
    calc (1:ℝ) = (1:ℝ)^2 := (one_pow 2).symm
      _ ≤ |(v i:ℝ)|^2 := pow_le_pow_left₀ zero_le_one habs 2
      _ = (v i:ℝ)^2 := sq_abs _
  have h2 : (v i : ℝ)^2 ≤ ∑ j, (v j : ℝ)^2 :=
    Finset.single_le_sum (f := fun j => (v j : ℝ)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

theorem gapsw80_t7_summable_dom_gaussian {lam : ℝ} (hlam : 0 < lam) :
    Summable fun v : Fin (nK K) → ℤ => rexp (-(π * lam * ∑ i, (v i : ℝ)^2)) := by
  have h := gapsw80_t2_summable_gaussian_Zn (n := nK K) (c := π * lam) (by positivity)
  exact h.congr fun v => by ring_nf

theorem gapsw80_t7_theta_sub_one_exp_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C p, 0 < p ∧ ∀ {c : ℝ}, 1 ≤ c →
      ∀ {y : InfinitePlace K → ℝ}, (∀ w, c ≤ y w) →
        ‖gapsw80_t4_multiIdealTheta K I y - 1‖ ≤ C * Real.exp (-(p * c)) := by
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  set p := π * lam with hp_def
  have hp : 0 < p := by positivity
  have hsum : Summable fun v : Fin (nK K) → ℤ => rexp (-(p * ∑ i, (v i:ℝ)^2)) :=
    gapsw80_t7_summable_dom_gaussian K hlam
  set C := rexp p * ∑' v : Fin (nK K) → ℤ, rexp (-(p * ∑ i, (v i:ℝ)^2)) with hC_def
  refine ⟨C, p, hp, fun {c} hc {y} hy => ?_⟩

  let f : (Fin (nK K) → ℤ) → ℂ := fun v =>
    cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ)
  have hzero : f 0 = 1 := multiIdealTheta_zero_term K I y

  have hterm : ∀ v, ‖f v‖ ≤ rexp (-(p * c * ∑ i, (v i:ℝ)^2)) := fun v => by
    show ‖cexp _‖ ≤ _
    rw [Complex.norm_exp, Complex.ofReal_re]
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    calc p * c * ∑ i, (v i:ℝ)^2
        = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
      _ ≤ π * (c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hGram v) (by linarith)) Real.pi_nonneg
      _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v) :=
          mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hy v) Real.pi_nonneg

  have hdom : ∀ v : Fin (nK K) → ℤ,
      rexp (-(p * c * ∑ i, (v i:ℝ)^2)) ≤ rexp (-(p * ∑ i, (v i:ℝ)^2)) := fun v => by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have hs : (0:ℝ) ≤ ∑ i, (v i : ℝ)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hc)) hs]
  have hsplit : ∀ {v : Fin (nK K) → ℤ}, v ≠ 0 →
      rexp (-(p * c * ∑ i, (v i:ℝ)^2)) ≤ rexp (-(p*(c-1))) * rexp (-(p * ∑ i, (v i:ℝ)^2)) := by
    intro v hv
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 := one_le_sum_sq_of_ne_zero K hv
    nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hc)) (sub_nonneg.mpr h1)]

  have hfullnorm : Summable fun v => ‖f v‖ :=
    hsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => (hterm v).trans (hdom v))
  have hfullsum : Summable f := hfullnorm.of_norm
  have htail_summable : Summable fun v : Fin (nK K) → ℤ =>
      if v = 0 then (0:ℝ) else rexp (-(p * c * ∑ i, (v i:ℝ)^2)) := by
    refine hsum.of_nonneg_of_le (fun v => ?_) (fun v => ?_)
    · split_ifs <;> positivity
    · split_ifs with h
      · positivity
      · exact hdom v
  have hite_norm_summable : Summable fun v : Fin (nK K) → ℤ =>
      ‖if v = (0 : Fin (nK K) → ℤ) then (0:ℂ) else f v‖ := by
    refine hfullnorm.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    split_ifs <;> simp

  have hTheta : gapsw80_t4_multiIdealTheta K I y - 1
      = ∑' v, if v = 0 then 0 else f v := by
    have heq : gapsw80_t4_multiIdealTheta K I y = ∑' v, f v := rfl
    rw [heq, hfullsum.tsum_eq_add_tsum_ite 0, hzero, add_sub_cancel_left]
  rw [hTheta]
  calc ‖∑' v, if v = 0 then 0 else f v‖
      ≤ ∑' v, ‖if v = (0 : Fin (nK K) → ℤ) then (0:ℂ) else f v‖ :=
        norm_tsum_le_tsum_norm hite_norm_summable
    _ ≤ ∑' v, if v = (0 : Fin (nK K) → ℤ) then (0:ℝ) else rexp (-(p*c*∑ i, (v i:ℝ)^2)) := by
        refine hite_norm_summable.tsum_le_tsum (fun v => ?_) htail_summable
        split_ifs with h
        · simp
        · exact hterm v
    _ ≤ ∑' v : Fin (nK K) → ℤ, rexp (-(p*(c-1))) * rexp (-(p * ∑ i, (v i:ℝ)^2)) := by
        refine htail_summable.tsum_le_tsum (fun v => ?_) (hsum.mul_left _)
        split_ifs with h
        · positivity
        · exact hsplit h
    _ = C * rexp (-(p * c)) := by
        rw [tsum_mul_left, hC_def,
          show -(p*(c-1)) = p + (-(p*c)) from by ring, Real.exp_add]
        ring

theorem continuous_theta_term (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (v : Fin (nK K) → ℤ) :
    Continuous fun y : InfinitePlace K → ℝ =>
      cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (Continuous.neg ?_))
  refine continuous_const.mul ?_
  simp only [gapsw80_t4_quadForm_scaledGram]
  exact continuous_finset_sum _ fun w _ => (continuous_apply w).mul continuous_const

theorem gapsw80_t7_continuousOn_multiIdealTheta_ge (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {c : ℝ} (hc : 0 < c) :
    ContinuousOn (gapsw80_t4_multiIdealTheta K I) {y | ∀ w, c ≤ y w} := by
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  refine continuousOn_tsum (fun v => (continuous_theta_term K I v).continuousOn)
    (gapsw80_t7_summable_dom_gaussian K (mul_pos hc hlam)) (fun v y hy => ?_)
  rw [Complex.norm_exp, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  calc π * (c * lam) * ∑ i, (v i:ℝ)^2
      = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
    _ ≤ π * (c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGram v) hc.le) Real.pi_nonneg
    _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v) :=
        mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hy v) Real.pi_nonneg

theorem gapsw80_t7_continuousOn_multiIdealTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t4_multiIdealTheta K I) {y | ∀ w, 0 < y w} := by
  intro y hy
  set c := Finset.univ.inf' ⟨w₀, Finset.mem_univ _⟩ (fun w => y w / 2) with hc_def
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr fun w _ => half_pos (hy w)
  have hy' : y ∈ {z | ∀ w, c ≤ z w} := fun w =>
    (Finset.inf'_le _ (Finset.mem_univ w)).trans (half_le_self (hy w).le)
  have hopen : IsOpen {z : InfinitePlace K → ℝ | ∀ w, c < z w} := by
    have : {z : InfinitePlace K → ℝ | ∀ w, c < z w} = ⋂ w, {z | c < z w} := by
      ext z; simp [Set.mem_iInter]
    rw [this]; exact isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have hy'' : y ∈ {z | ∀ w, c < z w} := fun w =>
    (Finset.inf'_le _ (Finset.mem_univ w)).trans_lt (by linarith [half_lt_self (hy w)])

  refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_
    (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hy''))
  exact ((gapsw80_t7_continuousOn_multiIdealTheta_ge K I hc) y hy').mono
    (fun z hz w => (hz w).le)

theorem continuous_mkParam (r : ℝ) :
    Continuous fun u : logSpace K => gapsw80_t5_mkParam K r u := by
  refine continuous_pi fun w => ?_
  unfold gapsw80_t5_mkParam
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

theorem continuous_genericKernel_integrand (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ)
    (scale : realSpace K) (hscale : ∀ w, 0 < scale w) :
    Continuous fun u : logSpace K =>
      gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u)) := by
  have hyP : Continuous fun u : logSpace K =>
      scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u) := by
    refine continuous_pi fun w => ?_
    exact continuous_const.mul
      (((continuous_apply w).comp ((continuous_expMapBasis K).comp (continuous_mkParam K r))).pow 2)
  refine ContinuousOn.comp_continuous (gapsw80_t7_continuousOn_multiIdealTheta K I) hyP ?_
  exact fun u w => mul_pos (hscale w) (yParam_pos K _ w)

theorem volume_unitBox_eq_one : volume (gapsw80_t7_unitBox K) = 1 := by
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

theorem volume_unitBox_lt_top : volume (gapsw80_t7_unitBox K) < ⊤ := by
  rw [volume_unitBox_eq_one]; exact ENNReal.one_lt_top

theorem gapsw80_t7_continuousOn_genericKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (scale : realSpace K) (hscale : ∀ w, 1 ≤ scale w) :
    ContinuousOn (fun t : ℝ => ∫ u in gapsw80_t7_unitBox K,
      gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume)
      (Set.Ioi 0) := by
  have hscale' : ∀ w, 0 < scale w := fun w => lt_of_lt_of_le one_pos (hscale w)
  obtain ⟨cK, hcK, hLB⟩ := gapsw80_t7_unitPart_lower_bound K
  obtain ⟨C, p, hp, hbound⟩ := gapsw80_t7_theta_sub_one_exp_bound K I
  haveI hfin : IsFiniteMeasure (volume.restrict (gapsw80_t7_unitBox K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitBox_lt_top K⟩

  intro t₀ ht₀
  have ht₀' : (0:ℝ) < t₀ := ht₀
  set s := Set.Icc (t₀/2) (t₀+1) with hs_def
  have hsnhds : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hssub : s ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le (by linarith) ht.1
  set c₀ : ℝ := cK * (t₀/2)
  have hc₀ : 0 < c₀ := mul_pos hcK (by linarith)
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  set M : ℝ := ∑' v : Fin (nK K) → ℤ, rexp (-(π * (c₀ * lam) * ∑ i, (v i:ℝ)^2)) with hM_def
  have hMsum := gapsw80_t7_summable_dom_gaussian K (mul_pos hc₀ hlam)

  have hy_lb : ∀ t ∈ s, ∀ u ∈ gapsw80_t7_unitBox K, ∀ w,
      c₀ ≤ (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) w := by
    intro t ht u hu w
    have ht' : (0:ℝ) < t := hssub ht
    rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht']
    have huIcc : u ∈ (Set.univ.pi fun _ : {w // w ≠ w₀} => Icc (0:ℝ) 1) :=
      fun i hi => Ico_subset_Icc_self (hu i hi)
    have huP : 0 < gapsw80_t7_unitPart K u w := unitPart_pos K u w
    calc c₀ = cK * (t₀/2) := rfl
      _ ≤ gapsw80_t7_unitPart K u w * t :=
          mul_le_mul (hLB u huIcc w) ht.1 (by linarith) huP.le
      _ = 1 * (t * gapsw80_t7_unitPart K u w) := by ring
      _ ≤ scale w * (t * gapsw80_t7_unitPart K u w) :=
          mul_le_mul_of_nonneg_right (hscale w) (by positivity)

  have hTheta_bound : ∀ t ∈ s, ∀ u ∈ gapsw80_t7_unitBox K,
      ‖gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u))‖ ≤ M := by
    intro t ht u hu
    unfold gapsw80_t4_multiIdealTheta
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact hMsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => by
        rw [Complex.norm_exp, Complex.ofReal_re]
        exact Real.exp_le_exp.mpr (neg_le_neg (by
          calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
              = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
            _ ≤ π * (c₀ * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
            _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I _) *ᵥ zcastR v) :=
                mul_le_mul_of_nonneg_left
                  (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg)))
    · refine (Summable.tsum_le_tsum (fun v => ?_) ?_ hMsum)
      · rw [Complex.norm_exp, Complex.ofReal_re]
        exact Real.exp_le_exp.mpr (neg_le_neg (by
          calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
              = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
            _ ≤ π * (c₀ * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
            _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I _) *ᵥ zcastR v) :=
                mul_le_mul_of_nonneg_left
                  (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg))
      · exact hMsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => by
          rw [Complex.norm_exp, Complex.ofReal_re]
          exact Real.exp_le_exp.mpr (neg_le_neg (by
            calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
                = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
              _ ≤ π * (c₀ * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
              _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I _) *ᵥ zcastR v) :=
                  mul_le_mul_of_nonneg_left
                    (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg)))

  have hcontOn_s : ContinuousOn
      (fun t => ∫ u in gapsw80_t7_unitBox K,
        gapsw80_t4_multiIdealTheta K I
          (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume) s := by
    refine continuousOn_of_dominated (bound := fun _ => M)
      (μ := volume.restrict (gapsw80_t7_unitBox K)) ?_ ?_ ?_ ?_
    · intro t _
      exact (continuous_genericKernel_integrand K I _ scale hscale').aestronglyMeasurable.restrict
    · intro t ht
      exact ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
        (fun u hu => hTheta_bound t ht u hu)
    · exact integrable_const M
    · refine ae_of_all _ fun u => ?_

      have hmk : ContinuousOn (fun t : ℝ => gapsw80_t5_mkParam K (Real.log t / 2) u) s := by
        refine continuousOn_pi.mpr fun w' => ?_
        unfold gapsw80_t5_mkParam
        split_ifs
        · exact (Real.continuousOn_log.mono (hssub.trans fun x hx => ne_of_gt hx)).div_const 2
        · exact continuousOn_const
      have hyP : ContinuousOn
          (fun t : ℝ => scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) s := by
        refine ContinuousOn.mul continuousOn_const ?_
        refine continuousOn_pi.mpr fun w => ?_
        unfold gapsw80_t5_yParam
        exact (((continuous_apply w).comp (continuous_expMapBasis K)).continuousOn.comp hmk
          (Set.mapsTo_univ _ _)).pow 2
      exact (gapsw80_t7_continuousOn_multiIdealTheta K I).comp hyP
        (fun t ht w => mul_pos (hscale' w) (yParam_pos K _ w))
  exact (hcontOn_s t₀ ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds hsnhds)

theorem gapsw80_t7_continuousOn_heckeKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t5_heckeKernel K I) (Set.Ioi 0) := by
  have h := gapsw80_t7_continuousOn_genericKernel K I 1 (fun _ => le_refl 1)
  simp only [one_mul] at h
  exact h

theorem gapsw80_t7_continuousOn_multHeckeKernel (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t7_multHeckeKernel K J) (Set.Ioi 0) := by
  have h := gapsw80_t7_continuousOn_genericKernel K J (gapsw80_t7_multSq K)
    (fun w => one_le_pow₀ (Nat.one_le_cast.mpr mult_pos))
  exact h

theorem gapsw80_t7_genericKernel_sub_one_isBigO_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (scale : realSpace K) (hscale : ∀ w, 1 ≤ scale w) :
    ∃ p > 0, (fun t => (∫ u in gapsw80_t7_unitBox K,
        gapsw80_t4_multiIdealTheta K I
          (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume) - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨cK, hcK, hLB⟩ := gapsw80_t7_unitPart_lower_bound K
  obtain ⟨C, p, hp, hbound⟩ := gapsw80_t7_theta_sub_one_exp_bound K I
  have hscale' : ∀ w, 0 < scale w := fun w => lt_of_lt_of_le one_pos (hscale w)
  refine ⟨p * cK, by positivity, IsBigO.of_bound (max C 0) ?_⟩
  filter_upwards [eventually_ge_atTop cK⁻¹] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le (inv_pos.mpr hcK) ht
  have hcKt : 1 ≤ cK * t := by rw [mul_comm]; exact (inv_le_iff_one_le_mul₀ hcK).mp ht
  set G : logSpace K → ℂ := fun u => gapsw80_t4_multiIdealTheta K I
      (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) with hG_def

  have hptw : ∀ u ∈ gapsw80_t7_unitBox K, ‖G u - 1‖ ≤ C * Real.exp (-(p * (cK * t))) := by
    intro u hu
    refine hbound hcKt (fun w => ?_)
    rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht0]
    have huIcc : u ∈ (Set.univ.pi fun _ : {w // w ≠ w₀} => Icc (0:ℝ) 1) :=
      fun i hi => Ico_subset_Icc_self (hu i hi)
    have huP : 0 < gapsw80_t7_unitPart K u w := unitPart_pos K u w
    calc cK * t ≤ gapsw80_t7_unitPart K u w * t :=
          mul_le_mul_of_nonneg_right (hLB u huIcc w) ht0.le
      _ = 1 * (t * gapsw80_t7_unitPart K u w) := by ring
      _ ≤ scale w * (t * gapsw80_t7_unitPart K u w) :=
          mul_le_mul_of_nonneg_right (hscale w) (by positivity)

  have hGcont : Continuous G := continuous_genericKernel_integrand K I _ scale hscale'
  haveI hfin : IsFiniteMeasure (volume.restrict (gapsw80_t7_unitBox K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitBox_lt_top K⟩
  have hintconst : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (gapsw80_t7_unitBox K) volume := by
    simp only [IntegrableOn, integrable_const_iff]; exact Or.inr hfin
  have hint : IntegrableOn (fun u => G u - 1) (gapsw80_t7_unitBox K) volume := by
    refine ⟨(hGcont.sub continuous_const).aestronglyMeasurable.restrict, ?_⟩
    refine HasFiniteIntegral.mono' ?_
      (ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
        (fun u hu => hptw u hu))
    exact (integrable_const (C * Real.exp (-(p * (cK * t))))).hasFiniteIntegral

  have heq : (∫ u in gapsw80_t7_unitBox K, G u ∂volume) - 1
      = ∫ u in gapsw80_t7_unitBox K, (G u - 1) ∂volume := by
    have hintG : IntegrableOn G (gapsw80_t7_unitBox K) volume :=
      (hint.add hintconst).congr_fun
        (fun u _ => by simp only [Pi.add_apply]; ring)
        (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    rw [integral_sub hintG hintconst, setIntegral_const]
    simp [measureReal_def, volume_unitBox_eq_one]

  rw [Real.norm_of_nonneg (Real.exp_pos _).le,
    show -(p * cK) * t = -(p * (cK * t)) from by ring]
  calc ‖(∫ u in gapsw80_t7_unitBox K, G u ∂volume) - 1‖
      = ‖∫ u in gapsw80_t7_unitBox K, (G u - 1) ∂volume‖ := by rw [heq]
    _ ≤ (C * Real.exp (-(p * (cK * t)))) * (volume (gapsw80_t7_unitBox K)).toReal :=
        norm_setIntegral_le_of_norm_le_const (volume_unitBox_lt_top K) hptw
    _ = C * Real.exp (-(p * (cK * t))) := by
        rw [volume_unitBox_eq_one, ENNReal.toReal_one, mul_one]
    _ ≤ max C 0 * Real.exp (-(p * (cK * t))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

theorem gapsw80_t7_heckeKernel_sub_one_isBigO_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ p > 0, (fun t => gapsw80_t5_heckeKernel K I t - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_genericKernel_sub_one_isBigO_exp K I 1 (fun _ => le_refl 1)
  refine ⟨p, hp, hO.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl⟩
  simp only [one_mul, gapsw80_t5_heckeKernel]

theorem gapsw80_t7_hf_top (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun t => gapsw80_t5_heckeKernel K I t - 1) =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_heckeKernel_sub_one_isBigO_exp K I
  exact hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

theorem gapsw80_t7_multHeckeKernel_sub_one_isBigO_exp (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ p > 0, (fun t => gapsw80_t7_multHeckeKernel K J t - 1)
      =O[atTop] fun t => Real.exp (-p * t) :=
  gapsw80_t7_genericKernel_sub_one_isBigO_exp K J (gapsw80_t7_multSq K)
    (fun w => one_le_pow₀ (Nat.one_le_cast.mpr mult_pos))

theorem gapsw80_t7_hg_top (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun t => gapsw80_t7_multHeckeKernel K J t - 1) =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_multHeckeKernel_sub_one_isBigO_exp K J
  exact hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

set_option maxHeartbeats 12800000 in

def gapsw80_t7_heckeWeakFEPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : WeakFEPair ℂ where
  f := gapsw80_t5_heckeKernel K I
  g := gapsw80_t7_multHeckeKernel K (gapsw80_t6_traceDualIdeal K I)
  k := (nK K : ℝ) / 2
  ε := ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹
  f₀ := 1
  g₀ := 1
  hk := div_pos (by exact_mod_cast (Module.finrank_pos : 0 < finrank ℚ K)) two_pos
  hε := by
    refine inv_ne_zero (Complex.ofReal_ne_zero.mpr ?_)
    exact (gapsw80_t7_covol_pos K I).ne'
  hf_int := (gapsw80_t7_continuousOn_heckeKernel K I).locallyIntegrableOn measurableSet_Ioi
  hg_int := (gapsw80_t7_continuousOn_multHeckeKernel K _).locallyIntegrableOn measurableSet_Ioi
  h_feq := by
    intro x hx
    have h := gapsw80_t7_h_feq K I x hx
    simp only [smul_eq_mul] at h ⊢
    convert h using 2
  hf_top := gapsw80_t7_hf_top K I
  hg_top := gapsw80_t7_hg_top K _

end FLT.Gapsw80T7ClosedFEWeakPair
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T8MellinGammaPartialZeta

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding.fundamentalCone"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"
open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T4MultiVarIdealThetaTransformation FLT.Gapsw80T5HeckeThetaKernel
open FLT.Gapsw80T6TraceDualBridge FLT.Gapsw80T7ClosedFEWeakPair
p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Asymptotics P2MW.S_NumberField_exists_completedDedekindZeta_package.Asymptotics Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Asymptotics.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

theorem gapsw80_t8_mellin_expNeg_eq_Gamma {a : ℝ} (ha : 0 < a) {β : ℂ} (hβ : 0 < β.re) :
    ∫ τ in Set.Ioi (0:ℝ), (τ : ℂ) ^ (β - 1) * cexp (-(a * τ : ℝ))
      = ((a : ℝ) : ℂ) ^ (-β) * Complex.Gamma β := by

  have hm := mellin_comp_mul_left (E := ℂ) (fun t ↦ cexp (-(t:ℝ))) β ha
  simp only [mellin, smul_eq_mul] at hm
  calc ∫ τ in Set.Ioi (0:ℝ), (τ : ℂ) ^ (β - 1) * cexp (-(a * τ : ℝ))
      = ((a:ℝ):ℂ) ^ (-β) * ∫ τ in Set.Ioi (0:ℝ), (τ:ℂ) ^ (β-1) * cexp (-(τ:ℝ)) := hm
    _ = ((a:ℝ):ℂ) ^ (-β) * Complex.Gamma β := by
        rw [Complex.Gamma_eq_integral hβ, Complex.GammaIntegral]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        simp only [Complex.ofReal_exp, Complex.ofReal_neg, mul_comm]

theorem gapsw80_t8_gammaFactor_isReal {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((π * a : ℝ) : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2)
      = Gammaℝ s * ((a:ℝ):ℂ) ^ (-(s/2)) := by
  rw [Gammaℝ_def, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_nonneg ha.le, neg_div]
  ring

theorem gapsw80_t8_gammaℂ_norm_const (s : ℂ) :
    (2:ℂ) * ((2 * π : ℝ) : ℂ) ^ (-s) * (2:ℂ) ^ (s - 1) = ((π:ℝ):ℂ) ^ (-s) := by
  have h2ne : ((2:ℝ):ℂ) ≠ 0 := by norm_num
  rw [show ((2*π:ℝ):ℂ) = ((2:ℝ):ℂ) * ((π:ℝ):ℂ) from by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_nonneg,
    show (2:ℂ) = ((2:ℝ):ℂ) from by norm_num]
  calc ((2:ℝ):ℂ) * (((2:ℝ):ℂ)^(-s) * ((π:ℝ):ℂ)^(-s)) * ((2:ℝ):ℂ)^(s-1)
      = (((2:ℝ):ℂ)^(s-1) * ((2:ℝ):ℂ)^(-s) * ((2:ℝ):ℂ)) * ((π:ℝ):ℂ)^(-s) := by ring
    _ = ((2:ℝ):ℂ)^(s-1 + -s) * ((2:ℝ):ℂ) * ((π:ℝ):ℂ)^(-s) := by
        rw [Complex.cpow_add _ _ h2ne]
    _ = ((π:ℝ):ℂ)^(-s) := by
        rw [show s - 1 + -s = (-1:ℂ) from by ring, Complex.cpow_neg_one,
          inv_mul_cancel₀ h2ne, one_mul]

theorem gapsw80_t8_gammaFactor_isComplex {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((π * a : ℝ) : ℂ) ^ (-s) * Complex.Gamma s
      = Gammaℂ s * (2:ℂ) ^ (s - 1) * ((a:ℝ):ℂ) ^ (-s) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_nonneg ha.le,
    Gammaℂ_def]
  calc ((π:ℝ):ℂ)^(-s) * ((a:ℝ):ℂ)^(-s) * Complex.Gamma s
      = ((2:ℂ) * ((2*π:ℝ):ℂ)^(-s) * (2:ℂ)^(s-1)) * ((a:ℝ):ℂ)^(-s) * Complex.Gamma s := by
        rw [gapsw80_t8_gammaℂ_norm_const]
    _ = 2 * (2 * (π:ℂ))^(-s) * Complex.Gamma s * (2:ℂ)^(s-1) * ((a:ℝ):ℂ)^(-s) := by
        rw [show ((2*π:ℝ):ℂ) = 2 * (π:ℂ) from by push_cast; ring]; ring

theorem gapsw80_t8_ofReal_pow_cpow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (z : ℂ) :
    (((a : ℝ) : ℂ) ^ n) ^ z = ((a : ℝ) : ℂ) ^ ((n : ℂ) * z) := by
  have harg : (n : ℝ) * Complex.arg ((a:ℝ):ℂ) = 0 := by
    rw [Complex.arg_ofReal_of_nonneg ha, mul_zero]
  exact (Complex.cpow_nat_mul' (x := ((a:ℝ):ℂ)) (n := n)
    (harg ▸ neg_lt_zero.mpr Real.pi_pos) (harg ▸ Real.pi_nonneg) z).symm

theorem gapsw80_t8_ofReal_sqrt_cpow {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    ((Real.sqrt a : ℝ) : ℂ) ^ z = ((a : ℝ) : ℂ) ^ (z / 2) := by
  have key := gapsw80_t8_ofReal_pow_cpow (Real.sqrt_nonneg a) 2 (z / 2)
  rw [show (((Real.sqrt a : ℝ):ℂ))^(2:ℕ) = ((a:ℝ):ℂ) by
        rw [← Complex.ofReal_pow, Real.sq_sqrt ha],
      show ((2:ℕ):ℂ) * (z/2) = z by push_cast; ring] at key
  exact key.symm

theorem gapsw80_t8_prod_ofReal_cpow {ι : Type*} (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (z : ℂ) :
    ((∏ i ∈ s, a i : ℝ) : ℂ) ^ z = ∏ i ∈ s, ((a i : ℝ) : ℂ) ^ z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha j (Finset.mem_cons_self j s))
        (Finset.prod_nonneg fun i hi => ha i (Finset.mem_cons_of_mem hi)),
      ih (fun i hi => ha i (Finset.mem_cons_of_mem hi))]

noncomputable def gapsw80_t8_placeParam (p : ℝ × logSpace K) : realSpace K :=
  fun w ↦ p.1 * gapsw80_t7_unitPart K p.2 w

theorem gapsw80_t8_placeParam_pos {p : ℝ × logSpace K} (hp : 0 < p.1) (w : InfinitePlace K) :
    0 < gapsw80_t8_placeParam K p w :=
  mul_pos hp (unitPart_pos K p.2 w)

theorem gapsw80_t8_prod_placeParam_pow_mult {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ∏ w : InfinitePlace K, gapsw80_t8_placeParam K (t, u) w ^ w.mult = t ^ nK K := by
  have key : ∀ w, gapsw80_t8_placeParam K (t, u) w
      = gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u) w := fun w => by
    rw [gapsw80_t7_yParam_mkParam_factor K ht u w]; rfl
  simp_rw [key]
  exact (gapsw80_t5_prod_yParam_mkParam K _ u).trans (exp_half_log_pow_two_n K ht)

theorem gapsw80_t8_mkParam_measurePreserving :
    MeasurePreserving (fun p : ℝ × logSpace K => gapsw80_t5_mkParam K p.1 p.2)
      volume volume := by

  have heq : (fun p : ℝ × logSpace K => gapsw80_t5_mkParam K p.1 p.2)
      = ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w₀)).symm
        ∘ Prod.map
          ⇑(MeasurableEquiv.piUnique (fun _ : {w : InfinitePlace K // w = w₀} => ℝ)).symm
          id := by
    funext p; funext w
    unfold gapsw80_t5_mkParam
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
      MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, Equiv.piEquivPiSubtypeProd_symm_apply,
      MeasurableEquiv.piUnique_symm_apply]
    by_cases hw : w = w₀
    · subst hw; simp only [dif_pos]; rfl
    · simp only [dif_neg hw]
  rw [heq, Measure.volume_eq_prod ℝ (logSpace K)]
  refine (volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w₀)).symm.comp ?_
  have hp := (volume_preserving_piUnique (fun _ : {w : InfinitePlace K // w = w₀} => ℝ)).symm.prod
    (MeasurePreserving.id (volume : Measure (logSpace K)))
  convert hp

  · rfl
  simp only [Measure.volume_eq_prod]
  congr!

theorem gapsw80_t8_lintegral_comp_halflog {h : ℝ → ENNReal} (hh : Measurable h) :
    ∫⁻ r, h r = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * t)⁻¹ * h (Real.log t / 2) := by
  have himg : (fun t : ℝ => Real.log t / 2) '' Set.Ioi (0:ℝ) = Set.univ :=
    Set.eq_univ_of_forall fun r => ⟨Real.exp (2 * r), Real.exp_pos _, by
      show Real.log (Real.exp (2 * r)) / 2 = r; rw [Real.log_exp]; ring⟩
  have hinj : Set.InjOn (fun t : ℝ => Real.log t / 2) (Set.Ioi 0) := fun t₁ h₁ t₂ h₂ heq => by
    have hlog : Real.log t₁ = Real.log t₂ := by linarith [heq]
    exact (Real.exp_log h₁).symm.trans (hlog ▸ Real.exp_log h₂)
  have hder : ∀ t ∈ Set.Ioi (0:ℝ), HasFDerivWithinAt (fun t => Real.log t / 2)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * t)⁻¹) (Set.Ioi 0) t := fun t ht => by
    have : HasDerivAt (fun t => Real.log t / 2) (2 * t)⁻¹ t := by
      rw [mul_inv, mul_comm, ← div_eq_mul_inv]
      exact (Real.hasDerivAt_log (ne_of_gt ht)).div_const 2
    exact this.hasFDerivAt.hasFDerivWithinAt
  conv_lhs => rw [← setLIntegral_univ, ← himg]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_Ioi hder hinj h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  congr 2
  simp_rw [ContinuousLinearMap.det, LinearMap.det_ring, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul,
    abs_of_pos (inv_pos.mpr (mul_pos two_pos ht'))]

theorem gapsw80_t8_setLIntegral_mkParam_halflog {G : realSpace K → ENNReal}
    (hG : Measurable G) :
    ∫⁻ c, G c
      = ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
          ENNReal.ofReal (2 * p.1)⁻¹ * G (gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2) := by

  have hGm : Measurable (fun p : ℝ × logSpace K => G (gapsw80_t5_mkParam K p.1 p.2)) :=
    hG.comp (gapsw80_t8_mkParam_measurePreserving K).measurable
  have hGm' : Measurable (fun p : ℝ × logSpace K =>
      ENNReal.ofReal (2 * p.1)⁻¹ * G (gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_fst).inv).mul
      (hGm.comp (((Real.measurable_log.comp measurable_fst).div_const 2).prodMk measurable_snd))
  have hh : Measurable (fun r : ℝ => ∫⁻ u : logSpace K, G (gapsw80_t5_mkParam K r u)) :=
    hGm.lintegral_prod_right'
  rw [← (gapsw80_t8_mkParam_measurePreserving K).lintegral_comp hG, Measure.volume_eq_prod,
    lintegral_prod _ hGm.aemeasurable, setLIntegral_prod _ hGm'.aemeasurable]
  dsimp only
  rw [gapsw80_t8_lintegral_comp_halflog hh]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [setLIntegral_univ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem gapsw80_t8_expMapBasis_image_univ :
    expMapBasis '' (Set.univ : Set (realSpace K)) = {τ : realSpace K | ∀ w, 0 < τ w} := by
  ext τ
  refine ⟨fun ⟨c, _, hc⟩ w => hc ▸ expMapBasis_pos c w, fun hτ => ?_⟩

  exact ⟨expMapBasis.symm τ, Set.mem_univ _, expMapBasis.right_inv (Set.mem_univ_pi.mpr hτ)⟩

abbrev gapsw80_t8_fderiv_sq (σ : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  .pi fun w ↦ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * σ w)).comp (.proj w)

theorem gapsw80_t8_hasFDerivAt_sq (σ : realSpace K) :
    HasFDerivAt (fun σ' : realSpace K => fun w => σ' w ^ 2) (gapsw80_t8_fderiv_sq K σ) σ := by
  simp only [hasFDerivAt_pi', ContinuousLinearMap.proj_pi]
  intro w
  have hd : HasDerivAt (fun x : ℝ => x ^ 2) (2 * σ w) (σ w) := by
    simpa using hasDerivAt_pow 2 (σ w)
  exact hd.hasFDerivAt.comp (f := fun σ' : realSpace K => σ' w) σ (hasFDerivAt_apply w σ)

open _root_.ContinuousLinearMap _root_.P2MW.S_NumberField_exists_completedDedekindZeta_package.ContinuousLinearMap in
theorem gapsw80_t8_abs_det_fderiv_sq (σ : realSpace K) :
    |(gapsw80_t8_fderiv_sq K σ).det|
      = 2 ^ (nrRealPlaces K + nrComplexPlaces K) * ∏ w : InfinitePlace K, |σ w| := by
  simp only [gapsw80_t8_fderiv_sq, ContinuousLinearMap.det, coe_pi]
  erw [LinearMap.det_pi]
  simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul, Finset.abs_prod, abs_mul, abs_pow, abs_two,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    card_eq_nrRealPlaces_add_nrComplexPlaces]

theorem gapsw80_t8_setLIntegral_sq_pos {g : realSpace K → ENNReal} (hg : Measurable g) :
    ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w}, g τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K) *
        ∫⁻ σ in {σ : realSpace K | ∀ w, 0 < σ w},
          (∏ w : InfinitePlace K, ENNReal.ofReal (σ w)) * g (fun w => σ w ^ 2) := by
  set P : Set (realSpace K) := {σ | ∀ w, 0 < σ w}
  have hPmeas : MeasurableSet P := by
    rw [show P = Set.univ.pi fun _ => Set.Ioi (0:ℝ) from Set.ext fun σ => by
      simp [P, Set.mem_univ_pi]]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have himg : (fun σ : realSpace K => fun w => σ w ^ 2) '' P = P := by
    refine Set.ext fun τ => ⟨fun ⟨σ, hσ, hστ⟩ w => hστ ▸ pow_pos (hσ w) 2, fun hτ => ?_⟩
    exact ⟨fun w => Real.sqrt (τ w), fun w => Real.sqrt_pos.mpr (hτ w),
      funext fun w => Real.sq_sqrt (hτ w).le⟩
  have hinj : Set.InjOn (fun σ : realSpace K => fun w => σ w ^ 2) P :=
    fun σ₁ h₁ σ₂ h₂ heq => funext fun w =>
      (pow_left_inj₀ (h₁ w).le (h₂ w).le two_ne_zero).mp (congrFun heq w)
  conv_lhs => rw [show P = (fun σ : realSpace K => fun w => σ w ^ 2) '' P from himg.symm]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hPmeas
      (fun σ _ => (gapsw80_t8_hasFDerivAt_sq K σ).hasFDerivWithinAt) hinj g,
    ← lintegral_const_mul' _ _ (by finiteness)]
  refine setLIntegral_congr_fun hPmeas fun σ hσ => ?_
  rw [gapsw80_t8_abs_det_fderiv_sq, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),
    show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp,
    ENNReal.ofReal_prod_of_nonneg fun w _ => abs_nonneg _,
    show (∏ w, ENNReal.ofReal |σ w|) = ∏ w, ENNReal.ofReal (σ w) from
      Finset.prod_congr rfl fun w _ => by rw [abs_of_pos (hσ w)],
    mul_assoc]

theorem gapsw80_t8_setLIntegral_placeParam {f : realSpace K → ENNReal} (hf : Measurable f) :
    ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ *
        ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ := by

  have hmeB : Measurable (fun c : realSpace K => expMapBasis c) :=
    (continuous_expMapBasis K).measurable
  have hmsq : Measurable (fun σ : realSpace K => fun w => σ w ^ 2) :=
    measurable_pi_lambda _ fun w => (measurable_pi_apply w).pow_const 2

  set H : realSpace K → ENNReal := fun c =>
    ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2) with hHdef
  have hH : Measurable H :=
    (ENNReal.measurable_ofReal.comp
        ((Real.measurable_exp.comp (measurable_pi_apply w₀)).pow_const _)).mul (hf.comp (hmsq.comp hmeB))

  have stepL : ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)
      = (2 : ENNReal) * ∫⁻ c, H c := by
    rw [gapsw80_t8_setLIntegral_mkParam_halflog K hH,
      ← lintegral_const_mul' _ _ (by finiteness)]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
    have ht : (0:ℝ) < p.1 := hp.1
    have hcw : gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2 w₀ = Real.log p.1 / 2 := mkParam_w₀ K _ _
    have hplace : (fun w => (expMapBasis (gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2) w) ^ 2)
        = gapsw80_t8_placeParam K p := funext fun w =>
      gapsw80_t7_yParam_mkParam_factor K ht p.2 w
    have hn : 1 ≤ nK K := Module.finrank_pos
    simp only [hHdef, hcw, hplace, exp_half_log_pow_two_n K ht]
    rw [show (2:ENNReal) = ENNReal.ofReal (2:ℝ) from by simp, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity),
      show (2:ℝ) * (2 * p.1)⁻¹ * p.1 ^ nK K = p.1 ^ (nK K - 1) by
        rw [show p.1 ^ nK K = p.1 * p.1 ^ (nK K - 1) by
          conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']]
        field_simp]

  have stepR : ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2 : ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
        * ∫⁻ c, H c := by
    have hf' : Measurable (fun τ : realSpace K =>
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ) :=
      (Finset.measurable_prod _ fun w _ =>
        ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)).mul hf
    have hσ : Measurable (fun σ : realSpace K =>
        (∏ w, ENNReal.ofReal (σ w)) *
          ((∏ w : {w // IsComplex w}, ENNReal.ofReal (σ w.1 ^ 2)) * f (fun w => σ w ^ 2))) :=
      (Finset.measurable_prod _ fun w _ =>
          ENNReal.measurable_ofReal.comp (measurable_pi_apply w)).mul (hf'.comp hmsq)
    rw [gapsw80_t8_setLIntegral_sq_pos K hf', ← gapsw80_t8_expMapBasis_image_univ K,
      setLIntegral_expMapBasis_image MeasurableSet.univ hσ, setLIntegral_univ, ← mul_assoc]
    congr 1
    refine lintegral_congr fun c => ?_

    have heBpos : ∀ w, (0:ℝ) < expMapBasis c w := fun w => expMapBasis_pos c w
    have hPc0 : (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun w _ => (ENNReal.ofReal_pos.mpr (heBpos w.1)).ne'
    have hPcT : (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) ≠ ⊤ :=
      (ENNReal.prod_lt_top fun w _ => ENNReal.ofReal_lt_top).ne

    have hPaPc : (∏ w, ENNReal.ofReal (expMapBasis c w))
          * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
        = ENNReal.ofReal (Real.exp (c w₀) ^ nK K) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => (heBpos w).le),
        ← ENNReal.ofReal_prod_of_nonneg (fun w _ => (heBpos w.1).le),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (heBpos w).le),
        prod_eq_prod_mul_prod (fun w => expMapBasis c w), mul_assoc, ← sq,
        ← prod_expMapBasis_pow c, prod_eq_prod_mul_prod (fun w => expMapBasis c w ^ w.mult)]
      congr 2
      · exact Finset.prod_congr rfl fun w _ => by rw [mult_isReal w, pow_one]
      · rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun w _ => by rw [mult_isComplex w]

    simp only [hHdef, show (fun w => c w) = c from rfl]
    rw [show (c w₀) * (Module.finrank ℚ K : ℝ) = (nK K : ℝ) * c w₀ from mul_comm _ _,
      Real.exp_nat_mul,
      show (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1 ^ 2))
          = (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) from by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun w _ => by rw [sq, ENNReal.ofReal_mul (heBpos w.1).le],
      show Real.exp (c w₀) ^ (2 * nK K)
          = Real.exp (c w₀) ^ nK K * Real.exp (c w₀) ^ nK K from by rw [two_mul, pow_add],
      ENNReal.ofReal_mul (pow_nonneg (Real.exp_nonneg _) _)]

    rw [← mul_assoc _ _ (f _), ← mul_assoc (∏ w, ENNReal.ofReal (expMapBasis c w)),
      ← mul_assoc, ← mul_assoc]
    congr 1

    calc ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹
            * ((∏ w, ENNReal.ofReal (expMapBasis c w))
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)))
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
        = ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * ((∏ w, ENNReal.ofReal (expMapBasis c w))
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)))
            * ((∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))) := by ring
      _ = ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * ENNReal.ofReal (Real.exp (c w₀) ^ nK K) := by
          rw [hPaPc, ENNReal.inv_mul_cancel hPc0 hPcT, mul_one]

  rw [stepL, stepR, ← mul_assoc]
  congr 1
  have hR : (0:ℝ) < regulator K := regulator_pos K
  have hn : 0 < nK K := Module.finrank_pos
  have hX : (0:ℝ) < (2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K :=
    mul_pos (mul_pos (zpow_pos two_pos _) (Nat.cast_pos.mpr hn)) hR
  have h2X : (2:ℝ) * ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K)
      = (2:ℝ) ^ nrRealPlaces K * (nK K : ℝ) * regulator K := by
    have key : (2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * 2 = (2:ℝ) ^ nrRealPlaces K := by
      rw [← zpow_add_one₀ (two_ne_zero (α := ℝ)), sub_add_cancel, zpow_natCast]
    rw [← key]; ring
  have hB : (2:ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2:ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
      = ENNReal.ofReal ((2:ℝ) ^ nrRealPlaces K * (nK K : ℝ) * regulator K) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast,
      show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp,
      pow_add, mul_assoc ((2:ENNReal) ^ nrRealPlaces K),
      show (2:ENNReal) ^ nrComplexPlaces K * ((2:ENNReal)⁻¹ ^ nrComplexPlaces K
            * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
          = (nK K : ENNReal) * ENNReal.ofReal (regulator K)
            * ((2:ENNReal) * (2:ENNReal)⁻¹) ^ nrComplexPlaces K from by rw [mul_pow]; ring,
      ENNReal.mul_inv_cancel (by norm_num) (by simp), one_pow, mul_one, ← mul_assoc]
  rw [hB, ← h2X, ← ENNReal.ofReal_mul (inv_nonneg.mpr hX.le),
    show ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K)⁻¹
          * ((2:ℝ) * ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K))
        = (2:ℝ) from by field_simp,
    show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp]

theorem gapsw80_t8_continuous_placeParam :
    Continuous (gapsw80_t8_placeParam K) :=
  continuous_pi fun w => continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd)

theorem gapsw80_t8_placeParam_measure_eq :
    Measure.map (gapsw80_t8_placeParam K)
        ((volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)))).withDensity
          (fun p => ENNReal.ofReal (p.1 ^ (nK K - 1))))
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹
        • (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}).withDensity
            (fun τ => ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) := by
  have hφ : Measurable (gapsw80_t8_placeParam K) := (gapsw80_t8_continuous_placeParam K).measurable
  have hdL : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (p.1 ^ (nK K - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hdR : Measurable (fun τ : realSpace K =>
      ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) :=
    Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hgL : Measurable fun p => f (gapsw80_t8_placeParam K p) := hf.comp hφ
  rw [lintegral_map hf hφ, lintegral_withDensity_eq_lintegral_mul _ hdL hgL,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hdR hf, smul_eq_mul]
  simp only [Pi.mul_apply]
  exact gapsw80_t8_setLIntegral_placeParam K hf

theorem gapsw80_t8_setIntegral_placeParam {G : realSpace K → ℂ}
    (hG : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w})) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p)
      = (((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ) *
        ∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ := by
  have hC : (0:ℝ) ≤ ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg
      (mul_nonneg (zpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) (regulator_pos K).le)
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} := by
    rw [show {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) from
      Set.ext fun τ => by simp [Set.mem_univ_pi]]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hφ : Measurable (gapsw80_t8_placeParam K) := (gapsw80_t8_continuous_placeParam K).measurable
  have hdL : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (p.1 ^ (nK K - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hdR : Measurable (fun τ : realSpace K =>
      ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) :=
    Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)

  have hGmap : AEStronglyMeasurable G (Measure.map (gapsw80_t8_placeParam K)
      ((volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)))).withDensity
        (fun p => ENNReal.ofReal (p.1 ^ (nK K - 1))))) := by
    rw [gapsw80_t8_placeParam_measure_eq]
    exact .mono_ac
      (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)) hG

  have key := (integral_map hφ.aemeasurable hGmap).symm
  rw [gapsw80_t8_placeParam_measure_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hdR
      (Filter.Eventually.of_forall fun _ => ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hdL
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal hC, Complex.real_smul] at key

  have stepL : (∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p))
      = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        (ENNReal.ofReal (p.1 ^ (nK K - 1))).toReal • G (gapsw80_t8_placeParam K p) :=
    setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => by
      rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hp.1) _), Complex.real_smul]
  have stepR : (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)).toReal • G τ)
      = ∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ :=
    setIntegral_congr_fun hBmeas fun τ hτ => by
      rw [ENNReal.toReal_prod,
        show (∏ w : {w : InfinitePlace K // IsComplex w}, (ENNReal.ofReal (τ w.1)).toReal)
            = ∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 from
          Finset.prod_congr rfl fun w _ => ENNReal.toReal_ofReal (le_of_lt (hτ w.1)),
        Complex.real_smul]
  rw [stepL, key, stepR, Complex.ofReal_inv]

theorem gapsw80_t8_prod_gammaFactor_eq {s : ℂ} (hs : 1 < s.re) {x : mixedSpace K}
    (hx : ∀ w, normAtPlace w x ≠ 0) :
    ∏ w : InfinitePlace K,
        (((π * normAtPlace w x ^ 2 : ℝ) : ℂ) ^ (-(w.mult * s / 2)) * Complex.Gamma (w.mult * s / 2))
      = Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ) ^ (s - 1)) ^ nrComplexPlaces K
        * ∏ w : InfinitePlace K, ((normAtPlace w x : ℝ) : ℂ) ^ (-(w.mult * s)) := by
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    (normAtPlace_nonneg w x).lt_of_ne (Ne.symm (hx w))

  have hreal : ∀ w : {w : InfinitePlace K // IsReal w},
      ((π * normAtPlace w.1 x ^ 2 : ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s / 2))
        * Complex.Gamma ((w.1.mult:ℂ) * s / 2)
      = Gammaℝ s * ((normAtPlace w.1 x:ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s)) := fun w => by
    simp only [mult_isReal w, Nat.cast_one, one_mul]
    rw [gapsw80_t8_gammaFactor_isReal (pow_pos (hpos w.1) 2) s, Complex.ofReal_pow,
      gapsw80_t8_ofReal_pow_cpow (hpos w.1).le 2 (-(s/2)),
      show ((2:ℕ):ℂ) * -(s/2) = -s from by push_cast; ring]

  have hcplx : ∀ w : {w : InfinitePlace K // IsComplex w},
      ((π * normAtPlace w.1 x ^ 2 : ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s / 2))
        * Complex.Gamma ((w.1.mult:ℂ) * s / 2)
      = (Gammaℂ s * (2:ℂ)^(s-1)) * ((normAtPlace w.1 x:ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s)) := fun w => by
    simp only [mult_isComplex w, Nat.cast_ofNat]
    rw [show ((2:ℂ) * s / 2) = s from by ring,
      gapsw80_t8_gammaFactor_isComplex (pow_pos (hpos w.1) 2) s, Complex.ofReal_pow,
      gapsw80_t8_ofReal_pow_cpow (hpos w.1).le 2 (-s),
      show ((2:ℕ):ℂ) * -s = -((2:ℂ)*s) from by push_cast; ring, mul_assoc]
  rw [prod_eq_prod_mul_prod (K := K), prod_eq_prod_mul_prod (K := K)
      (f := fun w => ((normAtPlace w x:ℝ):ℂ) ^ (-((w.mult:ℂ) * s)))]
  simp only [hreal, hcplx, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    nrRealPlaces, nrComplexPlaces]
  ring

theorem gapsw80_t8_prod_normAtPlace_cpow {x : mixedSpace K} (hx : ∀ w, normAtPlace w x ≠ 0)
    (s : ℂ) :
    ∏ w : InfinitePlace K, ((normAtPlace w x : ℝ) : ℂ) ^ (-(w.mult * s))
      = ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (-s) := by
  rw [mixedEmbedding.norm_apply,
    gapsw80_t8_prod_ofReal_cpow Finset.univ
      (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _) (-s)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.ofReal_pow,
    gapsw80_t8_ofReal_pow_cpow (normAtPlace_nonneg w x) w.mult (-s)]
  congr 1; push_cast; ring

abbrev gapsw80_t8_nonzeroIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type :=
  {a : K // a ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ∧ a ≠ 0}

scoped instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MulAction (𝓞 K)ˣ (gapsw80_t8_nonzeroIdeal K I) where
  smul u x := ⟨(u : 𝓞 K) • (x : K),
    Submodule.smul_mem _ _ x.2.1,
    smul_ne_zero (by exact_mod_cast u.ne_zero) x.2.2⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul u v x := Subtype.ext (mul_smul _ _ _)

noncomputable def gapsw80_t8_orbitRepr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) : K :=
  (x.out : K)

noncomputable def gapsw80_t8_partialDedekindZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ∑' J : {J : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 J = C},
    ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)

theorem gapsw80_t8_spanSingleton_mul_inv_le_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * (↑I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
  calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * ↑I⁻¹
      ≤ (↑I : FractionalIdeal (𝓞 K)⁰ K) * ↑I⁻¹ :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr x.2.1) _
    _ = 1 := I.mul_inv

noncomputable def gapsw80_t8_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) : (Ideal (𝓞 K))⁰ :=
  ⟨(FractionalIdeal.le_one_iff_exists_coeIdeal.mp
      (gapsw80_t8_spanSingleton_mul_inv_le_one K I x)).choose,
    mem_nonZeroDivisors_iff_ne_zero.mpr fun h ↦
      (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.2.2) (Units.ne_zero I⁻¹))
        ((FractionalIdeal.le_one_iff_exists_coeIdeal.mp
            (gapsw80_t8_spanSingleton_mul_inv_le_one K I x)).choose_spec.symm.trans
          (by rw [show (0 : Ideal (𝓞 K)) = ⊥ from rfl] at h
              rw [h, FractionalIdeal.coeIdeal_bot]))⟩

theorem gapsw80_t8_coe_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) :
    ((gapsw80_t8_orbitToIdeal K I x : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * ↑I⁻¹ :=
  (FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    (gapsw80_t8_spanSingleton_mul_inv_le_one K I x)).choose_spec

theorem gapsw80_t8_mk0_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) :
    ClassGroup.mk0 (gapsw80_t8_orbitToIdeal K I x) = (ClassGroup.mk K I)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ClassGroup.mk_mk0 K, ← map_mul, ClassGroup.mk_eq_one_iff]
  refine ⟨⟨(x : K), ?_⟩⟩
  rw [show ((FractionalIdeal.mk0 K (gapsw80_t8_orbitToIdeal K I x) * I :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) from by
    rw [Units.val_mul, FractionalIdeal.coe_mk0, gapsw80_t8_coe_orbitToIdeal,
      mul_assoc, I.inv_mul, mul_one],
    FractionalIdeal.coe_spanSingleton]

theorem gapsw80_t8_absNorm_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) :
    (Ideal.absNorm (gapsw80_t8_orbitToIdeal K I x : Ideal (𝓞 K)) : ℚ)
      * FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)
      = |Algebra.norm ℚ (x : K)| := by
  have hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    fun h ↦ (Units.ne_zero I) (FractionalIdeal.absNorm_eq_zero_iff.mp h)
  rw [← FractionalIdeal.coeIdeal_absNorm (K := K), gapsw80_t8_coe_orbitToIdeal, map_mul,
    FractionalIdeal.absNorm_span_singleton, Units.val_inv_eq_inv_val, map_inv₀,
    inv_mul_cancel_right₀ hI]

theorem gapsw80_t8_orbitToIdeal_smul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : (𝓞 K)ˣ) (x : gapsw80_t8_nonzeroIdeal K I) :
    gapsw80_t8_orbitToIdeal K I (u • x) = gapsw80_t8_orbitToIdeal K I x := by
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u • x : gapsw80_t8_nonzeroIdeal K I) : K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) := by
    show FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : 𝓞 K) • (x : K)) = _
    rw [Algebra.smul_def, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit,
      FractionalIdeal.coeIdeal_top, one_mul]
  exact Subtype.ext <| FractionalIdeal.coeIdeal_injective (K := K) <|
    show ((gapsw80_t8_orbitToIdeal K I (u • x) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = ((gapsw80_t8_orbitToIdeal K I x : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) from by
      rw [gapsw80_t8_coe_orbitToIdeal, gapsw80_t8_coe_orbitToIdeal, hspan]

noncomputable def gapsw80_t8_orbitQuotEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)) ≃
      {J : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 J = (ClassGroup.mk K I)⁻¹} :=
  Equiv.ofBijective
    (Quotient.lift
      (fun x ↦ ⟨gapsw80_t8_orbitToIdeal K I x, gapsw80_t8_mk0_orbitToIdeal K I x⟩)
      (fun a b h ↦ Subtype.ext <| by
        obtain ⟨u, rfl⟩ := MulAction.orbitRel_apply.mp h
        exact gapsw80_t8_orbitToIdeal_smul K I u b))
    ⟨fun q₁ q₂ h ↦ by
      induction q₁ using Quotient.inductionOn with | _ a => ?_
      induction q₂ using Quotient.inductionOn with | _ b => ?_
      refine Quotient.sound (MulAction.orbitRel_apply.mpr ?_)
      have hab : gapsw80_t8_orbitToIdeal K I a = gapsw80_t8_orbitToIdeal K I b :=
        congrArg Subtype.val h
      have hc : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) := by
        have := congrArg
          (fun J : (Ideal (𝓞 K))⁰ ↦ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I) hab
        simpa only [gapsw80_t8_coe_orbitToIdeal, mul_assoc, I.inv_mul, mul_one] using this
      obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hc
      refine ⟨u⁻¹, Subtype.ext (show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • (b : K) = (a : K) from ?_)⟩
      have hu' : ((u : (𝓞 K)ˣ) : 𝓞 K) • (a : K) = (b : K) := hu
      rw [← hu', ← mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul],
    fun ⟨J, hJ⟩ ↦ by
      have hJI : ClassGroup.mk K (FractionalIdeal.mk0 K J * I) = 1 := by
        rw [map_mul, ClassGroup.mk_mk0, hJ, inv_mul_cancel]
      obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).mp
        (ClassGroup.mk_eq_one_iff.mp hJI)
      have hx0 : x ≠ 0 := fun h0 ↦ Units.ne_zero _
        (hx.trans (by rw [h0, FractionalIdeal.spanSingleton_zero]))
      replace hx : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
        rw [← hx, Units.val_mul, FractionalIdeal.coe_mk0]
      have hxI : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) :=
        FractionalIdeal.spanSingleton_le_iff_mem.mp <|
          calc FractionalIdeal.spanSingleton (𝓞 K)⁰ x
              = ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I := hx.symm
            _ ≤ 1 * ↑I := mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
            _ = ↑I := one_mul _
      refine ⟨Quotient.mk _ ⟨x, hxI, hx0⟩, Subtype.ext (Subtype.ext
        (FractionalIdeal.coeIdeal_injective (K := K)
          (show ((gapsw80_t8_orbitToIdeal K I ⟨x, hxI, hx0⟩ : Ideal (𝓞 K)) :
              FractionalIdeal (𝓞 K)⁰ K) = ↑↑J from ?_)))⟩
      rw [gapsw80_t8_coe_orbitToIdeal, ← hx, mul_assoc, I.mul_inv, mul_one]⟩

theorem gapsw80_t8_tsum_orbit_normInv_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
      ((|(Algebra.norm ℚ (gapsw80_t8_orbitRepr K I x) : ℚ)| : ℝ) : ℂ) ^ (-s))
      = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s)
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s := by
  rw [gapsw80_t8_partialDedekindZeta, ← (gapsw80_t8_orbitQuotEquiv K I).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun q ↦ ?_
  unfold gapsw80_t8_orbitRepr
  have hout : ((gapsw80_t8_orbitQuotEquiv K I q : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = gapsw80_t8_orbitToIdeal K I q.out := by
    conv_lhs => rw [← q.out_eq]
    rfl
  have hM : (0:ℝ) ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have hN : (0:ℝ) ≤ (Ideal.absNorm (gapsw80_t8_orbitToIdeal K I q.out : Ideal (𝓞 K)) : ℝ) :=
    Nat.cast_nonneg _
  rw [hout, ← Complex.ofReal_natCast (Ideal.absNorm _),
    ← Complex.mul_cpow_ofReal_nonneg hM hN]
  congr 2
  exact_mod_cast ((gapsw80_t8_absNorm_orbitToIdeal K I q.out).symm.trans (mul_comm _ _))

theorem gapsw80_t8_covol_discr_cpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
      * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
    = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s)
      * ((2:ℝ) : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) := by
  have hN : (0:ℝ) ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2i : (0:ℝ) ≤ (2:ℝ)⁻¹ := by norm_num
  have h2r : (0:ℝ) ≤ ((2:ℝ)⁻¹) ^ nrComplexPlaces K := pow_nonneg h2i _
  have hD : (0:ℝ) ≤ |(discr K : ℝ)| := abs_nonneg _
  have hDne : ((|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, abs_eq_zero, Int.cast_eq_zero]
    exact discr_ne_zero K
  have harg2 : Complex.arg ((2:ℝ):ℂ) ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.pi_ne_zero.symm

  rw [mixedEmbedding.covolume_idealLattice, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg hN h2r) (Real.sqrt_nonneg _),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hN h2r,
    Complex.ofReal_pow, gapsw80_t8_ofReal_pow_cpow h2i (nrComplexPlaces K) (-s),
    gapsw80_t8_ofReal_sqrt_cpow hD (-s),
    show (((2:ℝ)⁻¹ : ℝ) : ℂ) = (((2:ℝ):ℂ))⁻¹ from Complex.ofReal_inv 2,
    Complex.inv_cpow _ _ harg2, ← Complex.cpow_neg,
    show -((nrComplexPlaces K : ℂ) * -s) = (nrComplexPlaces K : ℂ) * s from by ring,
    mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hDne,
    show -s / 2 + s / 2 = (0:ℂ) from by ring, Complex.cpow_zero, mul_one]

noncomputable def gapsw80_t8_nonzeroIdealLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    gapsw80_t8_nonzeroIdeal K I
      ≃ {x : mixedEmbedding.idealLattice K I // (x : mixedSpace K) ≠ 0} where
  toFun a := ⟨⟨mixedEmbedding K (a : K),
      (mem_idealLattice K I).mpr ⟨(a : K), a.2.1, rfl⟩⟩,
    fun h => a.2.2 <| (mixedEmbedding_injective K) (h.trans (_root_.map_zero _).symm)⟩
  invFun x := ⟨((mem_idealLattice K I).mp x.1.2).choose,
    ((mem_idealLattice K I).mp x.1.2).choose_spec.1,
    fun ha => x.2 (by
      have := ((mem_idealLattice K I).mp x.1.2).choose_spec.2
      rw [ha, _root_.map_zero] at this; exact this.symm)⟩
  left_inv a := by
    apply Subtype.ext
    have hch := ((mem_idealLattice K I).mp
      ((mem_idealLattice K I).mpr ⟨(a : K), a.2.1, rfl⟩)).choose_spec.2
    exact (mixedEmbedding_injective K) hch
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    exact ((mem_idealLattice K I).mp x.1.2).choose_spec.2

noncomputable def gapsw80_t8_zEquivNonzero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {v : Fin (nK K) → ℤ // v ≠ 0}
      ≃ {x : mixedEmbedding.idealLattice K I // (x : mixedSpace K) ≠ 0} where
  toFun v := ⟨zEquiv K I v, fun h => v.2 (by
    have : (zEquiv K I v : mixedEmbedding.idealLattice K I) = 0 := Subtype.ext h
    simpa using (zEquiv K I).injective (this.trans (_root_.map_zero _).symm))⟩
  invFun x := ⟨(zEquiv K I).symm x,
    fun h => x.2 (by rw [← (zEquiv K I).apply_symm_apply x.1, h, _root_.map_zero]; rfl)⟩
  left_inv v := Subtype.ext ((zEquiv K I).symm_apply_apply v)
  right_inv x := Subtype.ext ((zEquiv K I).apply_symm_apply x)

theorem gapsw80_t8_summable_thetaTerm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun v : Fin (nK K) → ℤ =>
      cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ) := by
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I

  obtain ⟨w₁, -, hw₁⟩ := Finset.exists_min_image
    (Finset.univ : Finset (InfinitePlace K)) y Finset.univ_nonempty
  set c := y w₁ with hc_def
  have hc : 0 < c := hy w₁
  have hcle : ∀ w, c ≤ y w := fun w => hw₁ w (Finset.mem_univ w)
  refine Summable.of_norm ?_
  refine (gapsw80_t7_summable_dom_gaussian K (mul_pos hc hlam)).of_nonneg_of_le
    (fun v => norm_nonneg _) (fun v => ?_)
  rw [Complex.norm_exp, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  calc π * (c * lam) * ∑ i, (v i:ℝ)^2
      = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
    _ ≤ π * (c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hGram v) hc.le) Real.pi_nonneg
    _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v) :=
        mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hcle v) Real.pi_nonneg

theorem gapsw80_t8_multiIdealTheta_sub_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    gapsw80_t4_multiIdealTheta K I y - 1
      = ∑' a : gapsw80_t8_nonzeroIdeal K I,
          cexp ((-(π * ∑ w : InfinitePlace K, y w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by

  set f : (Fin (nK K) → ℤ) → ℂ := fun v =>
    cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ) with hf_def
  have hfsum : Summable f := gapsw80_t8_summable_thetaTerm K I hy
  have hzero : f 0 = 1 := multiIdealTheta_zero_term K I y

  have hTheta : gapsw80_t4_multiIdealTheta K I y - 1
      = ∑' v : {v : Fin (nK K) → ℤ // v ≠ 0}, f v := by
    have heq : gapsw80_t4_multiIdealTheta K I y = ∑' v, f v := rfl
    rw [heq, hfsum.tsum_eq_add_tsum_ite 0, hzero, add_sub_cancel_left]
    refine Eq.symm ((tsum_subtype {v : Fin (nK K) → ℤ | v ≠ 0} f).trans ?_)
    exact tsum_congr fun v => by
      simp only [Set.indicator_apply, Set.mem_setOf_eq, ne_eq, ite_not]
  rw [hTheta]

  rw [← ((gapsw80_t8_zEquivNonzero K I).trans
    (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm).tsum_eq]
  refine tsum_congr fun a => ?_

  have hcoe : ((zEquiv K I) (a : Fin (nK K) → ℤ) : mixedSpace K)
      = mixedEmbedding K
          ((((gapsw80_t8_zEquivNonzero K I).trans
              (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm) a : gapsw80_t8_nonzeroIdeal K I) : K) := by
    have hch := ((mem_idealLattice K I).mp
      ((gapsw80_t8_zEquivNonzero K I) a).1.2).choose_spec.2
    exact hch.symm
  have hsum : (zcastR (a : Fin (nK K) → ℤ) ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR (a : Fin (nK K) → ℤ))
      = ∑ w, y w * (w ((((gapsw80_t8_zEquivNonzero K I).trans
          (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm) a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 :=
    (gapsw80_t4_quadForm_scaledGram K I y a).trans
      (Finset.sum_congr rfl fun w _ => by rw [hcoe, normAtPlace_apply])
  simp only [hf_def, hsum]

theorem gapsw80_t8_summable_rexpQ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : gapsw80_t8_nonzeroIdeal K I =>
      Real.exp (-(π * ∑ w, y w * (w (a : K)) ^ 2)) := by
  have h : Summable fun a : gapsw80_t8_nonzeroIdeal K I =>
      cexp ((-(π * ∑ w, y w * (w (a : K)) ^ 2) : ℝ) : ℂ) :=
    (Equiv.summable_iff ((gapsw80_t8_zEquivNonzero K I).trans
        (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm)).mp
      (((gapsw80_t8_summable_thetaTerm K I hy).subtype {v | v ≠ 0}).congr fun a => by
        simp only [Function.comp_apply]
        have hcoe : ((zEquiv K I) (a : Fin (nK K) → ℤ) : mixedSpace K)
            = mixedEmbedding K
                ((((gapsw80_t8_zEquivNonzero K I).trans
                    (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm) a :
                  gapsw80_t8_nonzeroIdeal K I) : K) :=
          (((mem_idealLattice K I).mp
            ((gapsw80_t8_zEquivNonzero K I) a).1.2).choose_spec.2).symm
        congr 4
        exact (gapsw80_t4_quadForm_scaledGram K I y a).trans
          (Finset.sum_congr rfl fun w _ => by rw [hcoe, normAtPlace_apply]))
  exact h.norm.congr fun a => by rw [Complex.norm_exp, Complex.ofReal_re]

theorem gapsw80_t8_heckeKernel_sub_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t - 1
      = ∫ u in gapsw80_t7_unitBox K,
          (gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1) ∂volume := by
  have hvol : volume (gapsw80_t7_unitBox K) = 1 := volume_unitBox_eq_one K
  have hint2 : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (gapsw80_t7_unitBox K) volume :=
    integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top)

  have hint1 : IntegrableOn
      (fun u => gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)))
      (gapsw80_t7_unitBox K) volume := by
    have hcont : Continuous
        (fun u => gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u))) := by
      have h := continuous_genericKernel_integrand K I (Real.log t / 2) 1 (fun _ => one_pos)
      simp only [one_mul] at h
      exact h.congr fun u => by
        congr 1; funext w; exact gapsw80_t7_yParam_mkParam_factor K ht u w
    have hcompact : IsCompact
        (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    exact (hcont.locallyIntegrable.integrableOn_isCompact hcompact).mono_set
      (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)
  rw [integral_sub hint1 hint2, setIntegral_const]
  have hvol' : volume.real (gapsw80_t7_unitBox K) = 1 := by
    rw [measureReal_def, hvol, ENNReal.toReal_one]
  rw [hvol', one_smul]
  congr 1
  unfold gapsw80_t5_heckeKernel
  refine setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1; funext w; rw [gapsw80_t7_yParam_mkParam_factor K ht]; rfl

theorem gapsw80_t8_integrableOn_theta_sub_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1)
      (gapsw80_t7_unitBox K) volume := by
  have hcont : Continuous
      (fun u => gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u))) := by
    have h := continuous_genericKernel_integrand K I (Real.log t / 2) 1 (fun _ => one_pos)
    simp only [one_mul] at h
    exact h.congr fun u => by
      congr 1; funext w; exact gapsw80_t7_yParam_mkParam_factor K ht u w
  have hcompact : IsCompact
      (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (((hcont.sub continuous_const).locallyIntegrable.integrableOn_isCompact hcompact).mono_set
    (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self))

theorem gapsw80_t8_placeParam_add_single {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) (w : InfinitePlace K) :
    gapsw80_t8_placeParam K (t, u + Pi.single i 1) w
      = gapsw80_t8_placeParam K (t, u) w
        * gapsw80_t5_unitSqScale K (fundSystem K (equivFinRank.symm i)) w := by
  have key : ∀ v, gapsw80_t8_placeParam K (t, v) w
      = gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) v) w := fun v => by
    rw [gapsw80_t7_yParam_mkParam_factor K ht v w]; rfl
  rw [key, key, mkParam_add_single, gapsw80_t5_yParam_add_single K i.2, Pi.mul_apply, mul_comm]

theorem gapsw80_t8_quadForm_unit_smul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℝ × logSpace K) (η : (𝓞 K)ˣ) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K, gapsw80_t8_placeParam K p w * (w ((η • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K,
          gapsw80_t8_placeParam K p w * gapsw80_t5_unitSqScale K η w * (w (a : K)) ^ 2 := by
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcoe : ((η • a : gapsw80_t8_nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
  rw [hcoe, Algebra.smul_def, map_mul, mul_pow, gapsw80_t5_unitSqScale,
    show ((algebraMap (𝓞 K) K) (η : 𝓞 K) : K) = ((η : 𝓞 K) : K) from rfl]
  ring

theorem gapsw80_t8_quadForm_torsion_invariant (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℝ × logSpace K) (ζ : torsion K) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        gapsw80_t8_placeParam K p w * (w (((ζ : (𝓞 K)ˣ) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2 := by
  rw [gapsw80_t8_quadForm_unit_smul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [gapsw80_t5_unitSqScale, (mem_torsion K).mp ζ.2 w, one_pow, mul_one]

theorem gapsw80_t8_quadForm_shift_single (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) (u : logSpace K) (i : {w : InfinitePlace K // w ≠ w₀})
    (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        gapsw80_t8_placeParam K (t, u + Pi.single i 1) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          gapsw80_t8_placeParam K (t, u) w
            * (w (((fundSystem K (equivFinRank.symm i)) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  rw [gapsw80_t8_quadForm_unit_smul]
  exact Finset.sum_congr rfl fun w _ => by rw [gapsw80_t8_placeParam_add_single K ht]

noncomputable def gapsw80_t8_dutEquiv : torsion K × (Fin (rank K) → ℤ) ≃ (𝓞 K)ˣ :=
  Equiv.ofBijective (fun p => (p.1 : (𝓞 K)ˣ) * ∏ i, fundSystem K i ^ p.2 i)
    (Function.bijective_iff_existsUnique _ |>.mpr fun x => by
      obtain ⟨ζe, he, huniq⟩ := exist_unique_eq_mul_prod K x
      exact ⟨ζe, he.symm, fun ζe' he' => huniq ζe' he'.symm⟩)

theorem gapsw80_t8_stabilizer_eq_bot (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : gapsw80_t8_nonzeroIdeal K I) :
    MulAction.stabilizer (𝓞 K)ˣ a = ⊥ := by
  rw [eq_bot_iff]
  intro η hη
  have hstab : ((η • a : gapsw80_t8_nonzeroIdeal K I) : K) = (a : K) :=
    Subtype.ext_iff.mp (MulAction.mem_stabilizer_iff.mp hη)
  have hcoe : algebraMap (𝓞 K) K (η : 𝓞 K) * (a : K) = (a : K) := by
    have hunf : ((η • a : gapsw80_t8_nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
    rw [hunf, Algebra.smul_def] at hstab; exact hstab
  have hη1 : algebraMap (𝓞 K) K (η : 𝓞 K) = 1 := (mul_eq_right₀ a.2.2).mp hcoe
  have hη𝓞 : (η : 𝓞 K) = 1 :=
    (IsFractionRing.injective (𝓞 K) K) (hη1.trans (map_one _).symm)
  exact Subgroup.mem_bot.mpr (Units.ext (hη𝓞.trans Units.val_one.symm))

noncomputable def gapsw80_t8_orbitGroupEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) :
    (𝓞 K)ˣ ≃ MulAction.orbit (𝓞 K)ˣ ω.out :=
  ((MulAction.orbitEquivQuotientStabilizer (𝓞 K)ˣ ω.out).trans
    ((Subgroup.quotientEquivOfEq (gapsw80_t8_stabilizer_eq_bot K I ω.out)).trans
      (QuotientGroup.quotientBot.toEquiv))).symm

theorem gapsw80_t8_orbitGroupEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)))
    (η : (𝓞 K)ˣ) :
    ((gapsw80_t8_orbitGroupEquiv K I ω η : gapsw80_t8_nonzeroIdeal K I) : K)
      = ((η • ω.out : gapsw80_t8_nonzeroIdeal K I) : K) := by
  have h := MulAction.orbitEquivQuotientStabilizer_symm_apply (G := (𝓞 K)ˣ) ω.out η
  show ((((MulAction.orbitEquivQuotientStabilizer (𝓞 K)ˣ ω.out).trans
      ((Subgroup.quotientEquivOfEq (gapsw80_t8_stabilizer_eq_bot K I ω.out)).trans
        QuotientGroup.quotientBot.toEquiv)).symm η : gapsw80_t8_nonzeroIdeal K I) : K)
    = ((η • ω.out : gapsw80_t8_nonzeroIdeal K I) : K)
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    show ((QuotientGroup.quotientBot (G := (𝓞 K)ˣ)).toEquiv.symm η : (𝓞 K)ˣ ⧸ (⊥ : Subgroup (𝓞 K)ˣ))
        = QuotientGroup.mk η from rfl,
    show ((Subgroup.quotientEquivOfEq (gapsw80_t8_stabilizer_eq_bot K I ω.out)).symm
          (QuotientGroup.mk η) : (𝓞 K)ˣ ⧸ MulAction.stabilizer (𝓞 K)ˣ ω.out)
        = QuotientGroup.mk η from rfl]
  exact congrArg (fun x : gapsw80_t8_nonzeroIdeal K I => (x : K)) h

noncomputable def gapsw80_t8_orbitSigmaEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _ : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)), (𝓞 K)ˣ)
      ≃ gapsw80_t8_nonzeroIdeal K I :=
  (Equiv.sigmaCongrRight fun ω => gapsw80_t8_orbitGroupEquiv K I ω).trans
    (MulAction.selfEquivSigmaOrbits (𝓞 K)ˣ (gapsw80_t8_nonzeroIdeal K I)).symm

theorem gapsw80_t8_orbitSigmaEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)))
    (η : (𝓞 K)ˣ) :
    ((gapsw80_t8_orbitSigmaEquiv K I ⟨ω, η⟩ : gapsw80_t8_nonzeroIdeal K I) : K)
      = ((η • ω.out : gapsw80_t8_nonzeroIdeal K I) : K) :=
  gapsw80_t8_orbitGroupEquiv_apply K I ω η

noncomputable def gapsw80_t8_spanEquiv :
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      ≃ ({w : InfinitePlace K // w ≠ w₀} → ℤ) where
  toFun g := fun i =>
    ((Basis.mem_span_iff_repr_mem ℤ _ _).mp g.2 i).choose
  invFun m := ⟨fun i => (m i : ℝ), by
    rw [Basis.mem_span_iff_repr_mem]
    exact fun i => ⟨m i, by simp⟩⟩
  left_inv g := by
    apply Subtype.ext; funext i
    have := ((Basis.mem_span_iff_repr_mem ℤ _ _).mp g.2 i).choose_spec
    simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
    exact this
  right_inv m := by
    funext i
    refine Int.cast_injective (α := ℝ) ?_
    have hmem : (fun j => (m j : ℝ))
        ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) := by
      rw [Basis.mem_span_iff_repr_mem]; exact fun j => ⟨m j, by simp⟩
    have := ((Basis.mem_span_iff_repr_mem ℤ _ _).mp hmem i).choose_spec
    simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
    exact this

theorem gapsw80_t8_spanEquiv_symm_apply_coe (m : {w : InfinitePlace K // w ≠ w₀} → ℤ)
    (i : {w : InfinitePlace K // w ≠ w₀}) :
    ((gapsw80_t8_spanEquiv K).symm m : logSpace K) i = (m i : ℝ) := rfl

theorem gapsw80_t8_quadForm_shift_span (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        gapsw80_t8_placeParam K (t, u + (g : logSpace K)) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i, fundSystem K (equivFinRank.symm i) ^ (gapsw80_t8_spanEquiv K g i))
                • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  set m := gapsw80_t8_spanEquiv K g with hm_def
  have hg : (g : logSpace K) = ∑ i, (m i : ℝ) • Pi.single i (1:ℝ) := by
    have : g = (gapsw80_t8_spanEquiv K).symm m := ((gapsw80_t8_spanEquiv K).symm_apply_apply g).symm
    rw [this]
    funext j
    simp only [gapsw80_t8_spanEquiv_symm_apply_coe, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hg]

  have hstep : ∀ (v : logSpace K) (i : {w : InfinitePlace K // w ≠ w₀}) (k : ℤ),
      ∀ (b : gapsw80_t8_nonzeroIdeal K I),
      ∑ w, gapsw80_t8_placeParam K (t, v + (k : ℝ) • Pi.single i 1) w * (w (b : K)) ^ 2
        = ∑ w, gapsw80_t8_placeParam K (t, v) w
            * (w (((fundSystem K (equivFinRank.symm i) ^ k) • b : gapsw80_t8_nonzeroIdeal K I)
                : K)) ^ 2 := by
    intro v i k
    induction k using Int.induction_on with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [show (((n:ℤ)+1:ℤ):ℝ) • Pi.single i (1:ℝ)
              = ((n:ℤ):ℝ) • Pi.single i 1 + Pi.single i 1 from by
            push_cast; rw [add_smul, one_smul],
        ← add_assoc, gapsw80_t8_quadForm_shift_single K I ht,
        ih (fundSystem K (equivFinRank.symm i) • b), ← mul_smul, ← _root_.zpow_add_one,
        show ((n:ℤ)+1 : ℤ) = (((n:ℕ)+1:ℕ):ℤ) from by push_cast; ring]
    | pred n ih =>
      intro b
      have key := (gapsw80_t8_quadForm_shift_single K I ht
        (v + ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i 1) i
        ((fundSystem K (equivFinRank.symm i))⁻¹ • b)).symm
      rw [← mul_smul, mul_inv_cancel, one_smul, add_assoc,
        show ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i (1:ℝ) + Pi.single i 1
            = ((-(n:ℤ):ℤ):ℝ) • Pi.single i 1 from by
          rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul, sub_add_cancel]] at key
      rw [key, ih ((fundSystem K (equivFinRank.symm i))⁻¹ • b), ← mul_smul,
        show fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)) * (fundSystem K (equivFinRank.symm i))⁻¹
            = fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)-1) from by group]

  suffices ∀ (s : Finset {w : InfinitePlace K // w ≠ w₀}) (a' : gapsw80_t8_nonzeroIdeal K I),
      ∑ w, gapsw80_t8_placeParam K (t, u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) w
          * (w (a' : K)) ^ 2
        = ∑ w, gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i ∈ s, fundSystem K (equivFinRank.symm i) ^ (m i)) • a'
                : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 from this Finset.univ a
  intro s
  induction s using Finset.induction with
  | empty => intro a'; simp
  | insert j s hj ih =>
    intro a'
    rw [Finset.sum_insert hj, add_comm ((m j : ℝ) • Pi.single j 1), ← add_assoc,
      hstep (u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) j (m j) a',
      ih ((fundSystem K (equivFinRank.symm j) ^ (m j)) • a'),
      Finset.prod_insert hj, mul_smul, smul_comm]

scoped instance gapsw80_t8_countable_nonzeroIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Countable (gapsw80_t8_nonzeroIdeal K I) :=
  ((gapsw80_t8_nonzeroIdealLatticeEquiv K I).trans
    (gapsw80_t8_zEquivNonzero K I).symm).countable_iff.mpr Subtype.countable

local instance : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (logSpace K) volume :=
  ⟨fun g s _ => measure_preimage_add _ _ _⟩

local instance : Countable
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))) :=
  (gapsw80_t8_spanEquiv K).countable_iff.mpr inferInstance

noncomputable local instance instSpanProdAddAction : AddAction
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) where
  vadd g p := (p.1, g +ᵥ p.2)
  zero_vadd p := Prod.ext rfl (zero_vadd _ p.2)
  add_vadd g h p := Prod.ext rfl (add_vadd g h p.2)

local instance instSpanProdMeasurableConstVAdd : MeasurableConstVAdd
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) :=
  ⟨fun g => measurable_fst.prodMk ((measurable_const_vadd g).comp measurable_snd)⟩

local instance instSpanProdVAddInvariant : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume) :=
  ⟨fun g _ hs =>
    ((MeasurePreserving.id _).prod (measurePreserving_vadd g volume)).measure_preimage
      hs.nullMeasurableSet⟩

theorem gapsw80_t8_continuous_cexpQ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : gapsw80_t8_nonzeroIdeal K I) :
    Continuous fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_neg.comp ?_))
  refine continuous_const.mul (continuous_finset_sum _ fun w _ => ?_)
  exact (continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd)).mul continuous_const

theorem gapsw80_t8_lintegral_master_reindex (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σre : ℝ) :
    ∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2)) * p.1 ^ (σre - 1))
      = (torsionOrder K : ENNReal) *
        ∑' ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            ENNReal.ofReal (Real.exp
                (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2))
              * p.1 ^ (σre - 1)) := by
  set GE : gapsw80_t8_nonzeroIdeal K I → ℝ × logSpace K → ENNReal := fun a p =>
    ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
      * p.1 ^ (σre - 1)) with hGE_def
  have hGE_orbitSigma : ∀ ω η p, GE (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, η⟩) p
      = GE (η • ω.out) p := fun ω η p => by unfold GE; congr 4

  rw [← (gapsw80_t8_orbitSigmaEquiv K I).tsum_eq fun a =>
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), GE a p,
    ENNReal.tsum_sigma']
  refine (tsum_congr fun ω => ?_).trans ENNReal.tsum_mul_left

  have hstep6a : ∀ p' : torsion K × (Fin (rank K) → ℤ), ∀ p : ℝ × logSpace K,
      GE (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩) p
        = GE ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p := fun p' p => by
    rw [hGE_orbitSigma,
      show gapsw80_t8_dutEquiv K p' • ω.out
          = (p'.1 : (𝓞 K)ˣ) • ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) from by
        rw [← mul_smul]; rfl]
    unfold GE; congr 5
    exact gapsw80_t8_quadForm_torsion_invariant K I p p'.1 _
  rw [← (gapsw80_t8_dutEquiv K).tsum_eq,
    tsum_congr fun p' => lintegral_congr fun p => hstep6a p' p]

  rw [ENNReal.tsum_prod']
  simp only [Prod.snd]
  rw [ENNReal.tsum_const,
    show (ENat.card (torsion K) : ENNReal) = (torsionOrder K : ENNReal) from by
      rw [ENat.card_eq_coe_natCard]; rfl]
  congr 1

  set efr : (Fin (rank K) → ℤ) ≃
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) :=
    (Equiv.arrowCongr
        (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) (Equiv.refl ℤ)).trans
      (gapsw80_t8_spanEquiv K).symm with hefr_def
  have hefr_prod : ∀ g,
      (∏ j, fundSystem K j ^ efr.symm g j)
        = ∏ i, fundSystem K (equivFinRank.symm i) ^ gapsw80_t8_spanEquiv K g i := fun g => by
    have hefrs : ∀ j, efr.symm g j = gapsw80_t8_spanEquiv K g (equivFinRank j) := fun j => by
      simp only [hefr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_symm,
        Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
        Equiv.symm_apply_apply, id_eq]
    exact Fintype.prod_equiv (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) _ _
      fun j => by rw [hefrs j, Equiv.symm_apply_apply]
  rw [← efr.symm.tsum_eq,
    tsum_congr fun g => by rw [hefr_prod g]]

  have hrpow_meas : Measurable fun p : ℝ × logSpace K => p.1 ^ (σre - 1) :=
    (measurable_of_continuousOn_compl_singleton (0:ℝ)
      (fun x hx => (Real.continuousAt_rpow_const x (σre - 1) (Or.inl hx)).continuousWithinAt)).comp
    measurable_fst
  have hGE_meas : ∀ a, Measurable (GE a) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun w _ =>
        (measurable_fst.mul ((continuous_unitPart K w).measurable.comp measurable_snd)).mul
          measurable_const)).neg).mul hrpow_meas)
  have hGE_slice_meas : ∀ a,
      Measurable fun t : ℝ => ∫⁻ u in gapsw80_t7_unitBox K, GE a (t, u) ∂volume := fun a =>
    (hGE_meas a).lintegral_prod_right' (ν := volume.restrict (gapsw80_t7_unitBox K))
  have hGE_repr : (fun p => ENNReal.ofReal (Real.exp
          (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2))
        * p.1 ^ (σre - 1))) = GE ω.out := rfl
  simp_rw [hGE_repr, Measure.volume_eq_prod (ℝ) (logSpace K),
    ← Measure.prod_restrict, lintegral_prod _ (hGE_meas _).aemeasurable, setLIntegral_univ]
  rw [← lintegral_tsum fun g => (hGE_slice_meas _).aemeasurable.restrict]

  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [(gapsw80_t7_unitBox_isAddFundamentalDomain K).lintegral_eq_tsum''
    (fun u => GE ω.out (t, u))]
  exact tsum_congr fun g => setLIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => by
      unfold GE; congr 5
      rw [show (g +ᵥ u : logSpace K) = u + (g : logSpace K) from by
            rw [AddSubmonoid.vadd_def]; exact add_comm _ _]
      exact (gapsw80_t8_quadForm_shift_span K I ht u g ω.out).symm

theorem gapsw80_t8_enorm_integrand_eq (σ : ℂ) (x : K) {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ‖cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖ₑ
      = ENNReal.ofReal
          (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2))
            * p.1 ^ (σ.re - 1)) := by
  have hn : ‖cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖
      = Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2))
        * p.1 ^ (σ.re - 1) := by
    rw [norm_mul, Complex.norm_exp, Complex.ofReal_re,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp),
      Complex.sub_re, Complex.one_re]
  rw [← hn, ← ofReal_norm_eq_enorm]

theorem gapsw80_t8_master_finite (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re) :
    (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤ := by

  have hMC : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
        - (gapsw80_t7_heckeWeakFEPair K I).f₀)) (Set.Ioi 0) volume :=
    ((gapsw80_t7_heckeWeakFEPair K I).hasMellin hσ).1
  suffices heq : (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1)))
      = ∫⁻ t in Set.Ioi (0:ℝ),
          ‖(t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
            - (gapsw80_t7_heckeWeakFEPair K I).f₀)‖ₑ by
    rw [heq]; exact hMC.2.ne

  have hrpow_meas : Measurable fun p : ℝ × logSpace K => p.1 ^ (σ.re - 1) :=
    (measurable_of_continuousOn_compl_singleton (0:ℝ)
      (fun x hx => (Real.continuousAt_rpow_const x (σ.re - 1) (Or.inl hx)).continuousWithinAt)).comp
    measurable_fst
  have hGE_meas : ∀ a : gapsw80_t8_nonzeroIdeal K I,
      Measurable fun p : ℝ × logSpace K =>
        ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
          * p.1 ^ (σ.re - 1)) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun w _ =>
        (measurable_fst.mul ((continuous_unitPart K w).measurable.comp measurable_snd)).mul
          measurable_const)).neg).mul hrpow_meas)

  rw [← lintegral_tsum fun a => (hGE_meas a).aemeasurable.restrict,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (Measurable.ennreal_tsum hGE_meas).aemeasurable]

  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  have hrpow_nn : (0:ℝ) ≤ t ^ (σ.re - 1) := Real.rpow_nonneg ht'.le _
  have hy : ∀ u : logSpace K, ∀ w, 0 < gapsw80_t8_placeParam K (t, u) w :=
    fun u w => gapsw80_t8_placeParam_pos K ht' (p := (t, u)) w

  have hΘ_real : ∀ u : logSpace K,
      gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1
        = ((∑' a : gapsw80_t8_nonzeroIdeal K I,
            Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2)) : ℝ)
          : ℂ) := fun u => by
    rw [gapsw80_t8_multiIdealTheta_sub_one K I (hy u), Complex.ofReal_tsum]
    exact tsum_congr fun a => (Complex.ofReal_exp _).symm
  have hΘ_norm : ∀ u : logSpace K,
      ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖
        = ∑' a : gapsw80_t8_nonzeroIdeal K I,
            Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2)) := fun u => by
    rw [hΘ_real u, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le)]
  have hintΘ := gapsw80_t8_integrableOn_theta_sub_one K I ht'
  calc (∫⁻ u in gapsw80_t7_unitBox K,
          ∑' a : gapsw80_t8_nonzeroIdeal K I,
            ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w
                * (w (a : K)) ^ 2)) * t ^ (σ.re - 1)) ∂volume)

      = ENNReal.ofReal (t ^ (σ.re - 1)) * ∫⁻ u in gapsw80_t7_unitBox K,
            ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖ₑ ∂volume := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun
          (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
        rw [tsum_congr fun a => by rw [mul_comm, ENNReal.ofReal_mul hrpow_nn],
          ENNReal.tsum_mul_left,
          ← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le)
            (gapsw80_t8_summable_rexpQ K I (hy u)),
          ← ofReal_norm_eq_enorm, hΘ_norm u]

    _ = ENNReal.ofReal (t ^ (σ.re - 1) * ∫ u in gapsw80_t7_unitBox K,
            ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖ ∂volume) := by
        rw [setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            fun u _ => (ofReal_norm_eq_enorm _).symm,
          ← ofReal_integral_eq_lintegral_ofReal hintΘ.norm (ae_of_all _ fun u => norm_nonneg _),
          ENNReal.ofReal_mul hrpow_nn]

    _ = _ := by
        rw [← ofReal_norm_eq_enorm, smul_eq_mul, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re, Complex.one_re,
          show (gapsw80_t7_heckeWeakFEPair K I).f = gapsw80_t5_heckeKernel K I from rfl,
          show ((gapsw80_t7_heckeWeakFEPair K I).f₀ : ℂ) = 1 from rfl,
          gapsw80_t8_heckeKernel_sub_one K I ht',
          setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            (fun u _ => hΘ_real u),
          integral_complex_ofReal, Complex.norm_real,
          Real.norm_of_nonneg (integral_nonneg fun u => tsum_nonneg fun _ => (Real.exp_pos _).le),
          setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            (fun u _ => hΘ_norm u)]

theorem gapsw80_t8_integrableOn_orbitRepr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) :
    IntegrableOn (fun p =>
        cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w
            * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := by
  have hcont : ContinuousOn (fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w
          * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) :=
    (gapsw80_t8_continuous_cexpQ K I ω.out).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt
  refine ⟨hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ)
      fun p hp => gapsw80_t8_enorm_integrand_eq K σ (gapsw80_t8_orbitRepr K I ω) (p := p) hp.1]
  refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (gapsw80_t8_master_finite K I hσ))
  rw [gapsw80_t8_lintegral_master_reindex K I σ.re]
  exact le_trans (ENNReal.le_tsum ω)
    (le_mul_of_one_le_left' (by exact_mod_cast torsionOrder_pos K))

theorem gapsw80_t8_quadForm_unit_smul_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (p : ℝ × logSpace K) (η : (𝓞 K)ˣ) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K p w * (w ((η • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K p w * gapsw80_t5_unitSqScale K η w * (w (a : K)) ^ 2 := by
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcoe : ((η • a : gapsw80_t8_nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
  rw [hcoe, Algebra.smul_def, map_mul, mul_pow, gapsw80_t5_unitSqScale,
    show ((algebraMap (𝓞 K) K) (η : 𝓞 K) : K) = ((η : 𝓞 K) : K) from rfl]
  ring

theorem gapsw80_t8_quadForm_torsion_invariant_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (p : ℝ × logSpace K) (ζ : torsion K) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K p w
          * (w (((ζ : (𝓞 K)ˣ) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2 := by
  rw [gapsw80_t8_quadForm_unit_smul_c]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [gapsw80_t5_unitSqScale, (mem_torsion K).mp ζ.2 w, one_pow, mul_one]

theorem gapsw80_t8_quadForm_shift_single_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K (t, u + Pi.single i 1) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((fundSystem K (equivFinRank.symm i)) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  rw [gapsw80_t8_quadForm_unit_smul_c]
  exact Finset.sum_congr rfl fun w _ => by rw [gapsw80_t8_placeParam_add_single K ht]; ring

theorem gapsw80_t8_quadForm_shift_span_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K (t, u + (g : logSpace K)) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i, fundSystem K (equivFinRank.symm i) ^ (gapsw80_t8_spanEquiv K g i))
                • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  set m := gapsw80_t8_spanEquiv K g with hm_def
  have hg : (g : logSpace K) = ∑ i, (m i : ℝ) • Pi.single i (1:ℝ) := by
    have : g = (gapsw80_t8_spanEquiv K).symm m := ((gapsw80_t8_spanEquiv K).symm_apply_apply g).symm
    rw [this]
    funext j
    simp only [gapsw80_t8_spanEquiv_symm_apply_coe, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hg]
  have hstep : ∀ (v : logSpace K) (i : {w : InfinitePlace K // w ≠ w₀}) (k : ℤ),
      ∀ (b : gapsw80_t8_nonzeroIdeal K I),
      ∑ w, c w * gapsw80_t8_placeParam K (t, v + (k : ℝ) • Pi.single i 1) w * (w (b : K)) ^ 2
        = ∑ w, c w * gapsw80_t8_placeParam K (t, v) w
            * (w (((fundSystem K (equivFinRank.symm i) ^ k) • b : gapsw80_t8_nonzeroIdeal K I)
                : K)) ^ 2 := by
    intro v i k
    induction k using Int.induction_on with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [show (((n:ℤ)+1:ℤ):ℝ) • Pi.single i (1:ℝ)
              = ((n:ℤ):ℝ) • Pi.single i 1 + Pi.single i 1 from by
            push_cast; rw [add_smul, one_smul],
        ← add_assoc, gapsw80_t8_quadForm_shift_single_c K I c ht,
        ih (fundSystem K (equivFinRank.symm i) • b), ← mul_smul, ← _root_.zpow_add_one,
        show ((n:ℤ)+1 : ℤ) = (((n:ℕ)+1:ℕ):ℤ) from by push_cast; ring]
    | pred n ih =>
      intro b
      have key := (gapsw80_t8_quadForm_shift_single_c K I c ht
        (v + ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i 1) i
        ((fundSystem K (equivFinRank.symm i))⁻¹ • b)).symm
      rw [← mul_smul, mul_inv_cancel, one_smul, add_assoc,
        show ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i (1:ℝ) + Pi.single i 1
            = ((-(n:ℤ):ℤ):ℝ) • Pi.single i 1 from by
          rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul, sub_add_cancel]] at key
      rw [key, ih ((fundSystem K (equivFinRank.symm i))⁻¹ • b), ← mul_smul,
        show fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)) * (fundSystem K (equivFinRank.symm i))⁻¹
            = fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)-1) from by group]
  suffices ∀ (s : Finset {w : InfinitePlace K // w ≠ w₀}) (a' : gapsw80_t8_nonzeroIdeal K I),
      ∑ w, c w * gapsw80_t8_placeParam K (t, u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) w
          * (w (a' : K)) ^ 2
        = ∑ w, c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i ∈ s, fundSystem K (equivFinRank.symm i) ^ (m i)) • a'
                : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 from this Finset.univ a
  intro s
  induction s using Finset.induction with
  | empty => intro a'; simp
  | insert j s hj ih =>
    intro a'
    rw [Finset.sum_insert hj, add_comm ((m j : ℝ) • Pi.single j 1), ← add_assoc,
      hstep (u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) j (m j) a',
      ih ((fundSystem K (equivFinRank.symm j) ^ (m j)) • a'),
      Finset.prod_insert hj, mul_smul, smul_comm]

theorem gapsw80_t8_continuous_cexpQ_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (a : gapsw80_t8_nonzeroIdeal K I) :
    Continuous fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_neg.comp ?_))
  refine continuous_const.mul (continuous_finset_sum _ fun w _ => ?_)
  exact (continuous_const.mul
    (continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd))).mul continuous_const

theorem gapsw80_t8_enorm_integrand_eq_c (c : realSpace K) (σ : ℂ) (x : K)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ‖cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖ₑ
      = ENNReal.ofReal
          (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2))
            * p.1 ^ (σ.re - 1)) := by
  rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_exp, Complex.ofReal_re,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp),
    Complex.sub_re, Complex.one_re]

theorem gapsw80_t8_rankinSelberg_unfold_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (σ : ℂ)
    (hMaster : (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤)
    (hIntω : ∀ ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
      IntegrableOn (fun p =>
          cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
        ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume) :
    (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
        * ∫ u in gapsw80_t7_unitBox K,
            (∑' a : gapsw80_t8_nonzeroIdeal K I,
              cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
            ∂volume)
      = (torsionOrder K : ℂ) *
        ∑' ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K, c w * gapsw80_t8_placeParam K p w
                * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ (σ - 1) := by

  set F : gapsw80_t8_nonzeroIdeal K I → ℝ × logSpace K → ℂ := fun a p =>
    cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ)
      * ((p.1 : ℝ) : ℂ) ^ (σ - 1) with hF_def
  have hF_sm : ∀ a, AEStronglyMeasurable (F a)
      (volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K))) := fun a =>
    ((gapsw80_t8_continuous_cexpQ_c K I c a).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt).aestronglyMeasurable
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
  have hF_enorm : ∀ a, ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
      ‖F a p‖ₑ = ENNReal.ofReal
        (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
          * p.1 ^ (σ.re - 1)) := fun a p hp =>
    gapsw80_t8_enorm_integrand_eq_c K c σ (a : K) (p := p) hp.1
  have hMaster' : (∑' a, ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), ‖F a p‖ₑ) ≠ ⊤ := by
    refine (tsum_congr fun a => setLIntegral_congr_fun
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
      (hF_enorm a)).symm ▸ hMaster

  have hFsum_int : IntegrableOn (fun p => ∑' a, F a p)
      ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K)) volume := by
    refine ⟨AEStronglyMeasurable.tsum hF_sm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hMaster')
    rw [← lintegral_tsum fun a => (hF_sm a).enorm]
    exact lintegral_mono fun p => enorm_tsum_le_tsum_enorm
  rw [show (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume)
      = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), ∑' a, F a p from by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hFsum_int]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
      fun u _ => by rw [tsum_mul_right, mul_comm]]

  rw [integral_tsum (fun a => hF_sm a) hMaster']

  have hSsum : Summable fun a => ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F a p := by
    refine .of_norm (.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
      (ENNReal.summable_toReal hMaster'))
    rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm_eq_enorm]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top hMaster' (ENNReal.le_tsum a))
      (enorm_integral_le_lintegral_enorm _)
  have hF_Q : ∀ (a b : gapsw80_t8_nonzeroIdeal K I) (p : ℝ × logSpace K),
      (∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2)
        = ∑ w, c w * gapsw80_t8_placeParam K p w * (w (b : K)) ^ 2 →
      F a p = F b p := fun a b p hQ => by unfold F; rw [hQ]
  have hSsumSig : Summable fun p :
        Σ _ : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)), (𝓞 K)ˣ =>
      ∫ q in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F (gapsw80_t8_orbitSigmaEquiv K I p) q :=
    (gapsw80_t8_orbitSigmaEquiv K I).summable_iff.mpr hSsum
  rw [((gapsw80_t8_orbitSigmaEquiv K I).tsum_eq _).symm.trans hSsumSig.tsum_sigma,
    ← tsum_mul_left]
  refine tsum_congr fun ω => ?_
  have hstep6a : ∀ (p' : torsion K × (Fin (rank K) → ℤ)) (p : ℝ × logSpace K),
      F (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩) p
        = F ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p := fun p' p =>
    hF_Q _ _ p (by
      rw [show ((gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩ :
            gapsw80_t8_nonzeroIdeal K I) : K)
          = ((gapsw80_t8_dutEquiv K p' • ω.out : gapsw80_t8_nonzeroIdeal K I) : K) from
        gapsw80_t8_orbitSigmaEquiv_apply K I ω _,
        show gapsw80_t8_dutEquiv K p' • ω.out
            = (p'.1 : (𝓞 K)ˣ) • ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) from by
          rw [← mul_smul]; rfl]
      exact gapsw80_t8_quadForm_torsion_invariant_c K I c p p'.1 _)
  rw [← (gapsw80_t8_dutEquiv K).tsum_eq,
    tsum_congr fun p' => setIntegral_congr_fun
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
      fun p _ => hstep6a p' p]
  have hSsumPr : Summable fun p' : torsion K × (Fin (rank K) → ℤ) =>
      ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
        F ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p :=
    ((hSsumSig.sigma_factor ω).comp_injective (i := gapsw80_t8_dutEquiv K)
      (gapsw80_t8_dutEquiv K).injective).congr
      fun p' => setIntegral_congr_fun
        (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
        fun p _ => hstep6a p' p
  rw [hSsumPr.tsum_prod]
  simp only [Prod.snd]
  rw [tsum_const, nsmul_eq_mul,
    show ((torsionOrder K : ℕ) : ℂ) = (Nat.card (torsion K) : ℂ) from rfl]
  congr 1
  set efr : (Fin (rank K) → ℤ) ≃
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) :=
    (Equiv.arrowCongr
        (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) (Equiv.refl ℤ)).trans
      (gapsw80_t8_spanEquiv K).symm with hefr_def
  rw [← efr.symm.tsum_eq,
    tsum_congr fun g => by rw [show (∏ j, fundSystem K j ^ efr.symm g j)
        = (∏ i, fundSystem K (equivFinRank.symm i) ^ gapsw80_t8_spanEquiv K g i) from
      Fintype.prod_equiv (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) _ _
        fun j => by
          simp only [hefr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_symm,
            Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
            Equiv.symm_apply_apply, id_eq]]]

  have hInt_ω : IntegrableOn (F ω.out)
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := hIntω ω
  have hInt_box : ∀ b : gapsw80_t8_nonzeroIdeal K I,
      IntegrableOn (F b) ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K)) volume := fun b =>
    ⟨hF_sm b, hasFiniteIntegral_iff_enorm.mpr
      (lt_of_le_of_lt (ENNReal.le_tsum b) (lt_top_iff_ne_top.mpr hMaster'))⟩
  set ν : Measure (ℝ × logSpace K) :=
    ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume with hν_def
  have hν_eq : (volume : Measure (ℝ × logSpace K)).restrict
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) = ν := by
    rw [hν_def, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hν_box : (volume : Measure (ℝ × logSpace K)).restrict
        ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K))
      = ν.restrict (Prod.snd ⁻¹' gapsw80_t7_unitBox K) := by
    rw [hν_def, show (Prod.snd ⁻¹' gapsw80_t7_unitBox K : Set (ℝ × logSpace K))
          = Set.univ ×ˢ gapsw80_t7_unitBox K from Set.univ_prod.symm,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod,
      ← Measure.prod_restrict]
  have hInt_ω' : Integrable (F ω.out) ν := by rw [← hν_eq]; exact hInt_ω
  have hFD_prod : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      (Prod.snd ⁻¹' gapsw80_t7_unitBox K) ν :=
    (gapsw80_t7_unitBox_isAddFundamentalDomain K).preimage_of_equiv
      (f := Prod.snd) Measure.quasiMeasurePreserving_snd Function.bijective_id (fun _ _ => rfl)
  rw [show (fun p : ℝ × logSpace K =>
          cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w
                * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1)) = F ω.out from rfl,
    show (∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)), F ω.out p)
        = ∫ p, F ω.out p ∂ν from by rw [← hν_eq],
    hFD_prod.integral_eq_tsum'' (F ω.out) hInt_ω']
  refine tsum_congr fun g => ?_
  rw [show (∫ p in Prod.snd ⁻¹' gapsw80_t7_unitBox K, F ω.out (g +ᵥ p) ∂ν)
        = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F ω.out (g +ᵥ p) from by
    show (∫ p, _ ∂(ν.restrict _)) = ∫ p, _ ∂(volume.restrict _); rw [hν_box]]
  refine setIntegral_congr_fun
    (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
    fun p hp => ?_
  show F _ p = F ω.out (p.1, g +ᵥ p.2)
  unfold F
  congr 5
  rw [show (g +ᵥ p.2 : logSpace K) = p.2 + (g : logSpace K) from by
        rw [AddSubmonoid.vadd_def]; exact add_comm _ _]
  exact (gapsw80_t8_quadForm_shift_span_c K I c hp.1 p.2 g ω.out).symm

theorem gapsw80_t8_heckeLambda_unfold_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).Λ ((nK K : ℂ) * s / 2)
      = (torsionOrder K : ℂ) *
        ∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K,
                gapsw80_t8_placeParam K p w *
                (w (gapsw80_t8_orbitRepr K I x)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1) := by
  set σ : ℂ := (nK K : ℂ) * s / 2 with hσ_def

  have hnK : (0:ℝ) < (nK K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hσ_re' : σ.re = (nK K : ℝ) * s.re / 2 := by
    rw [hσ_def]
    simp only [Complex.div_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im, mul_zero, zero_add, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, add_zero, Complex.normSq_ofNat]
    ring
  have hσ_re : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re := by
    show (nK K : ℝ) / 2 < σ.re
    rw [hσ_re']; nlinarith
  have hMellin := ((gapsw80_t7_heckeWeakFEPair K I).hasMellin hσ_re).2
  rw [← hMellin]

  have hstep23 : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
          - (gapsw80_t7_heckeWeakFEPair K I).f₀)
        = (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume := fun t ht => by
    have ht' : (0:ℝ) < t := ht
    rw [show (gapsw80_t7_heckeWeakFEPair K I).f = gapsw80_t5_heckeKernel K I from rfl,
      show ((gapsw80_t7_heckeWeakFEPair K I).f₀ : ℂ) = 1 from rfl, smul_eq_mul,
      gapsw80_t8_heckeKernel_sub_one K I ht']
    congr 1
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
    exact gapsw80_t8_multiIdealTheta_sub_one K I (fun w => gapsw80_t8_placeParam_pos K ht' w)
  rw [show mellin (fun t => (gapsw80_t7_heckeWeakFEPair K I).f t
        - (gapsw80_t7_heckeWeakFEPair K I).f₀) σ
      = ∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume from
    setIntegral_congr_fun measurableSet_Ioi hstep23]

  have hMaster1 : (∑' a : gapsw80_t8_nonzeroIdeal K I,
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
        ENNReal.ofReal
          (Real.exp (-(π * ∑ w, (1:realSpace K) w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
            * p.1 ^ (σ.re - 1))) ≠ ⊤ := by
    simp only [Pi.one_apply, one_mul]; exact gapsw80_t8_master_finite K I hσ_re
  have hIntω1 : ∀ ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
      IntegrableOn (fun p =>
          cexp ((-(π * ∑ w, (1:realSpace K) w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
        ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := fun ω => by
    simp only [Pi.one_apply, one_mul]; exact gapsw80_t8_integrableOn_orbitRepr K I hσ_re ω
  have hRS := gapsw80_t8_rankinSelberg_unfold_c K I 1 σ hMaster1 hIntω1
  simp only [Pi.one_apply, one_mul] at hRS
  exact hRS

theorem gapsw80_t8_perOrbit_integral_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        cexp ((-(π * ∑ w : InfinitePlace K,
            gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = (((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ)
        * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1)) ^ nrComplexPlaces K
          * ((|(Algebra.norm ℚ (gapsw80_t8_orbitRepr K I ω) : ℚ)| : ℝ) : ℂ) ^ (-s)) := by
  set a : K := gapsw80_t8_orbitRepr K I ω with ha_def
  have ha_ne : a ≠ 0 := ω.out.2.2
  have ha_pos : ∀ w : InfinitePlace K, (0:ℝ) < w a := fun w => pos_iff.mpr ha_ne
  have hnK : 1 ≤ nK K := Module.finrank_pos
  have hBset : {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) :=
    Set.ext fun τ => by simp [Set.mem_univ_pi]
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} :=
    hBset ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioi

  set G : realSpace K → ℂ := fun τ =>
    cexp ((-(π * ∑ w, τ w * (w a) ^ 2) : ℝ) : ℂ)
      * ((∏ w : InfinitePlace K, τ w ^ w.mult : ℝ) : ℂ) ^ ((s - 2) / 2) with hG_def

  have hfactor : ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w a) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p) := fun p hp => by
    have ht : (0:ℝ) < p.1 := hp.1
    simp only [hG_def, gapsw80_t8_prod_placeParam_pow_mult K ht p.2, Complex.ofReal_pow]
    rw [gapsw80_t8_ofReal_pow_cpow ht.le (nK K) ((s-2)/2),
      ← Complex.cpow_natCast (p.1:ℂ) (nK K - 1), mul_comm ((↑p.1:ℂ)^((nK K - 1 : ℕ):ℂ)),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 2
    push_cast [Nat.cast_sub hnK]; ring

  have hG_sm : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hBmeas
    refine (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_finset_sum _ fun w _ =>
          (continuous_apply w).mul continuous_const)).neg)).continuousOn.mul ?_
    intro τ hτ
    exact (((Complex.continuous_ofReal.comp (continuous_finset_prod _ fun w _ =>
        (continuous_apply w).pow _)).continuousAt).cpow continuousAt_const
      (Or.inl (by
        simp only [Function.comp_apply, Complex.ofReal_re]
        exact Finset.prod_pos fun w _ => pow_pos (hτ w) _))).continuousWithinAt

  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) hfactor,
    gapsw80_t8_setIntegral_placeParam K hG_sm]
  congr 1

  have hreorg : ∀ τ ∈ {τ : realSpace K | ∀ w, 0 < τ w},
      ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ
        = ∏ w : InfinitePlace K,
            (((τ w : ℝ) : ℂ) ^ ((w.mult : ℂ) * s / 2 - 1)
              * cexp ((-(π * (w a)^2 * τ w) : ℝ) : ℂ)) := fun τ hτ => by
    have hτpos : ∀ w, (0:ℝ) < τ w := hτ
    have hτne : ∀ w, ((τ w : ℝ) : ℂ) ≠ 0 := fun w => Complex.ofReal_ne_zero.mpr (hτpos w).ne'
    simp only [hG_def]

    rw [show cexp ((-(π * ∑ w, τ w * (w a)^2):ℝ):ℂ)
          = ∏ w : InfinitePlace K, cexp ((-(π * (w a)^2 * τ w) : ℝ):ℂ) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.exp_sum]
        exact Finset.prod_congr rfl fun w _ => by ring_nf,

      gapsw80_t8_prod_ofReal_cpow Finset.univ (fun w _ => pow_nonneg (hτpos w).le _) ((s-2)/2),
      show (∏ w : InfinitePlace K, ((τ w ^ w.mult : ℝ):ℂ) ^ ((s-2)/2))
          = ∏ w : InfinitePlace K, ((τ w:ℝ):ℂ) ^ ((w.mult:ℂ)*(s-2)/2) from
        Finset.prod_congr rfl fun w _ => by
          rw [Complex.ofReal_pow,
            gapsw80_t8_ofReal_pow_cpow (hτpos w).le w.mult ((s-2)/2)]; ring_nf]

    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => cexp ((-(π*(w a)^2*τ w):ℝ):ℂ) * ((τ w:ℝ):ℂ)^((w.mult:ℂ)*(s-2)/2)),
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => ((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*τ w):ℝ):ℂ)),

      mul_left_comm
        (∏ w : {w : InfinitePlace K // IsComplex w}, ((τ w.1:ℝ):ℂ)),
      ← Finset.prod_mul_distrib]
    refine congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    ·
      rw [mult_isReal w, Nat.cast_one, one_mul, one_mul,
        show s/2-1 = (s-2)/2 from by ring, mul_comm]
    ·
      rw [mult_isComplex w, Nat.cast_ofNat, show (2:ℂ)*(s-2)/2 = s-2 from by ring,
        show (2:ℂ)*s/2-1 = s-1 from by ring, mul_comm ((τ w.1:ℝ):ℂ), mul_assoc,
        show ((τ w.1:ℝ):ℂ)^(s-2) * ((τ w.1:ℝ):ℂ) = ((τ w.1:ℝ):ℂ)^(s-1) from by
          rw [show (s-1:ℂ) = (s-2)+1 from by ring,
            Complex.cpow_add _ _ (hτne w.1), Complex.cpow_one],
        mul_comm]

  have hmeas_eq : (volume : Measure (realSpace K)).restrict {τ | ∀ w, 0 < τ w}
      = Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [hBset, volume_pi, Measure.restrict_pi_pi]
  set fw : InfinitePlace K → ℝ → ℂ := fun w r =>
    (r:ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*r):ℝ):ℂ) with hfw_def
  have hfub : (∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
        ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ), fw w r :=
    integral_fintype_prod_eq_prod fw
  rw [setIntegral_congr_fun hBmeas hreorg,
    show (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ∏ w : InfinitePlace K, (((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
            * cexp ((-(π*(w a)^2*τ w):ℝ):ℂ)))
        = ∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
          ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0))
      from by rw [← hmeas_eq],
    hfub]
  simp only [hfw_def]

  have hβre : ∀ w : InfinitePlace K, (0:ℝ) < ((w.mult:ℂ)*s/2).re := fun w => by
    have hre : ((w.mult:ℂ)*s/2).re = (w.mult : ℝ)*s.re/2 := by
      rw [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    rw [hre]
    exact div_pos (mul_pos (Nat.cast_pos.mpr w.mult_pos) (lt_trans one_pos hs)) two_pos
  rw [show (∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ),
            ((r:ℝ):ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*r):ℝ):ℂ))
        = ∏ w : InfinitePlace K,
            (((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by
        simp only [Complex.ofReal_neg]
        exact gapsw80_t8_mellin_expNeg_eq_Gamma
          (mul_pos Real.pi_pos (pow_pos (ha_pos w) 2)) (hβre w)]

  have hx_nz : ∀ w, normAtPlace w (mixedEmbedding K a) ≠ 0 := fun w => by
    rw [normAtPlace_apply]; exact (ha_pos w).ne'
  rw [show (∏ w : InfinitePlace K,
            (((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) * Complex.Gamma ((w.mult:ℂ)*s/2)))
        = ∏ w : InfinitePlace K,
            (((π * normAtPlace w (mixedEmbedding K a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by rw [normAtPlace_apply],
    gapsw80_t8_prod_gammaFactor_eq K hs hx_nz,
    gapsw80_t8_prod_normAtPlace_cpow K hx_nz s,
    mixedEmbedding.norm_eq_norm, Rat.cast_abs]

theorem gapsw80_t8_heckeLambda_eq_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).Λ ((nK K : ℂ) * s / 2)
      = ((torsionOrder K : ℂ)
          / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ)))
        * ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s := by

  rw [gapsw80_t8_heckeLambda_unfold_eq K I hs,
    tsum_congr (gapsw80_t8_perOrbit_integral_eq K I hs), tsum_mul_left, tsum_mul_left,
    gapsw80_t8_tsum_orbit_normInv_eq K I hs, mul_pow (Gammaℂ s), div_eq_mul_inv, mul_inv, mul_inv]

  set Ccov : ℂ := ((ZLattice.covolume (mixedEmbedding.idealLattice K I):ℝ):ℂ)^(-s) with hCcov
  set Cdisc : ℂ := ((|(discr K:ℝ)|:ℝ):ℂ)^(s/2) with hCdisc
  set CabsN : ℂ := ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K):ℝ):ℂ)^(-s) with hCabsN
  set C2rs : ℂ := ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s) with hC2rs
  have hcd : Ccov * Cdisc = CabsN * C2rs := gapsw80_t8_covol_discr_cpow K I s

  have h2ne : (2:ℂ) ≠ 0 := two_ne_zero
  have hr₁ : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    have h1 := card_add_two_mul_card_eq_rank K
    have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hconst : (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * (nK K:ℝ) * regulator K : ℝ)⁻¹ : ℂ)
        * ((2:ℂ)^(s-1))^nrComplexPlaces K
      = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * ((nK K:ℂ))⁻¹
        * ((regulator K:ℝ):ℂ)⁻¹ * C2rs := by
    have h2pow : ((2:ℂ)^((nrRealPlaces K:ℤ)-1 : ℤ))⁻¹ * ((2:ℂ)^(s-1))^nrComplexPlaces K
        = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * C2rs := by
      rw [hC2rs, Complex.ofReal_ofNat,
        ← Complex.cpow_intCast (2:ℂ) ((nrRealPlaces K:ℤ)-1),
        ← Complex.cpow_natCast (2:ℂ) (nrRealPlaces K + nrComplexPlaces K - 1),
        ← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_nat_mul (2:ℂ) (nrComplexPlaces K) (s-1),
        ← Complex.cpow_add _ _ h2ne, ← Complex.cpow_add _ _ h2ne]
      congr 1
      push_cast [Nat.cast_sub hr₁]; ring
    rw [← Complex.ofReal_inv, mul_inv, mul_inv, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zpow, Complex.ofReal_ofNat]
    linear_combination ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹ * h2pow
  linear_combination (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s * CabsN
        * (torsionOrder K : ℂ)) * hconst
    - ((torsionOrder K : ℂ) * ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s) * hcd

theorem gapsw80_t8_one_le_multSq (w : InfinitePlace K) : (1:ℝ) ≤ gapsw80_t7_multSq K w :=
  one_le_pow₀ (Nat.one_le_cast.mpr mult_pos)

theorem gapsw80_t8_multHeckeKernel_sub_one (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t7_multHeckeKernel K J t - 1
      = ∫ u in gapsw80_t7_unitBox K,
          (gapsw80_t4_multiIdealTheta K J
            (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w) - 1) ∂volume := by
  have hvol : volume (gapsw80_t7_unitBox K) = 1 := volume_unitBox_eq_one K
  have hint2 : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (gapsw80_t7_unitBox K) volume :=
    integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top)

  have hcont : Continuous
      (fun u => gapsw80_t4_multiIdealTheta K J
        (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w)) := by
    have h := continuous_genericKernel_integrand K J (Real.log t / 2)
      (gapsw80_t7_multSq K) (fun w => multSq_pos K w)
    exact h.congr fun u => by
      congr 1; funext w
      rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht]; rfl
  have hint1 : IntegrableOn
      (fun u => gapsw80_t4_multiIdealTheta K J
        (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w))
      (gapsw80_t7_unitBox K) volume := by
    have hcompact : IsCompact
        (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    exact (hcont.locallyIntegrable.integrableOn_isCompact hcompact).mono_set
      (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)
  rw [integral_sub hint1 hint2, setIntegral_const]
  have hvol' : volume.real (gapsw80_t7_unitBox K) = 1 := by
    rw [measureReal_def, hvol, ENNReal.toReal_one]
  rw [hvol', one_smul]
  congr 1
  unfold gapsw80_t7_multHeckeKernel gapsw80_t7_integrand
  refine setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1; funext w
  rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht]; rfl

theorem gapsw80_t8_rexpQ_c_le {c : realSpace K} (hc : ∀ w, 1 ≤ c w) (x : K)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2))
      ≤ Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2)) := by
  refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le))
  refine Finset.sum_le_sum fun w _ => ?_
  have hpp := (gapsw80_t8_placeParam_pos K hp w).le
  have hwx := sq_nonneg (w x)
  nlinarith [hc w, mul_nonneg hpp hwx]

theorem gapsw80_t8_master_finite_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re) :
    (∑' a : gapsw80_t8_nonzeroIdeal K J,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
                * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (gapsw80_t8_master_finite K J hσ) ?_
  refine ENNReal.tsum_le_tsum fun a => ?_
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))] with p hp
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (gapsw80_t8_rexpQ_c_le K (gapsw80_t8_one_le_multSq K) (a : K) hp.1)
    (Real.rpow_nonneg (le_of_lt hp.1) _))

theorem gapsw80_t8_integrableOn_orbitRepr_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K J))) :
    IntegrableOn (fun p =>
        cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
            * (w (gapsw80_t8_orbitRepr K J ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := by
  set a : K := gapsw80_t8_orbitRepr K J ω
  have hcont : ContinuousOn (fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
          * (w a) ^ 2) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) :=
    (gapsw80_t8_continuous_cexpQ_c K J (gapsw80_t7_multSq K) ω.out).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt
  refine ⟨hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound := (gapsw80_t8_integrableOn_orbitRepr K J hσ ω).2
  rw [hasFiniteIntegral_iff_enorm] at hbound
  refine lt_of_le_of_lt ?_ hbound
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
  rw [gapsw80_t8_enorm_integrand_eq_c K (gapsw80_t7_multSq K) σ a hp.1,
    gapsw80_t8_enorm_integrand_eq K σ a hp.1]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (gapsw80_t8_rexpQ_c_le K (gapsw80_t8_one_le_multSq K) a hp.1)
    (Real.rpow_nonneg (le_of_lt hp.1) _))

theorem gapsw80_t8_symmLambda_unfold_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = (torsionOrder K : ℂ) *
        ∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ)
            (gapsw80_t8_nonzeroIdeal K (gapsw80_t6_traceDualIdeal K I))),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K,
                gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w *
                (w (gapsw80_t8_orbitRepr K (gapsw80_t6_traceDualIdeal K I) x)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1) := by
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := gapsw80_t6_traceDualIdeal K I with hJ_def
  set σ : ℂ := (nK K : ℂ) * s / 2 with hσ_def
  have hnK : (0:ℝ) < (nK K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hσ_re' : σ.re = (nK K : ℝ) * s.re / 2 := by
    rw [hσ_def]
    simp only [Complex.div_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im, mul_zero, zero_add, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, add_zero, Complex.normSq_ofNat]
    ring
  have hσ_re : ((gapsw80_t7_heckeWeakFEPair K I).symm.k : ℝ) < σ.re := by
    show (nK K : ℝ) / 2 < σ.re
    rw [hσ_re']; nlinarith
  have hσ_reJ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re := hσ_re

  have hMellin := ((gapsw80_t7_heckeWeakFEPair K I).symm.hasMellin hσ_re).2
  rw [← hMellin]

  have hy : ∀ {t : ℝ} (_ : 0 < t) (u : logSpace K), ∀ w,
      0 < gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w := fun ht u w =>
    mul_pos (multSq_pos K w) (gapsw80_t8_placeParam_pos K ht w)
  have hstep23 : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).symm.f t
          - (gapsw80_t7_heckeWeakFEPair K I).symm.f₀)
        = (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K J,
                cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w
                    * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume := fun t ht => by
    have ht' : (0:ℝ) < t := ht
    rw [show (gapsw80_t7_heckeWeakFEPair K I).symm.f
          = gapsw80_t7_multHeckeKernel K J from rfl,
      show ((gapsw80_t7_heckeWeakFEPair K I).symm.f₀ : ℂ) = 1 from rfl, smul_eq_mul,
      gapsw80_t8_multHeckeKernel_sub_one K J ht']
    congr 1
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
    have := gapsw80_t8_multiIdealTheta_sub_one K J (y := fun w =>
        gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w) (hy ht' u)
    simpa only [mul_assoc] using this
  rw [show mellin (fun t => (gapsw80_t7_heckeWeakFEPair K I).symm.f t
        - (gapsw80_t7_heckeWeakFEPair K I).symm.f₀) σ
      = ∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K J,
                cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w
                    * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume from
    setIntegral_congr_fun measurableSet_Ioi hstep23]

  exact gapsw80_t8_rankinSelberg_unfold_c K J (gapsw80_t7_multSq K) σ
    (gapsw80_t8_master_finite_mult K J hσ_reJ)
    (gapsw80_t8_integrableOn_orbitRepr_mult K J hσ_reJ)

theorem gapsw80_t8_perOrbit_integral_eq_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K J))) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        cexp ((-(π * ∑ w : InfinitePlace K,
            gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K J ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((4:ℝ):ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * ((((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1)) ^ nrComplexPlaces K
            * ((|(Algebra.norm ℚ (gapsw80_t8_orbitRepr K J ω) : ℚ)| : ℝ) : ℂ) ^ (-s))) := by
  set a : K := gapsw80_t8_orbitRepr K J ω with ha_def
  have ha_ne : a ≠ 0 := ω.out.2.2
  have ha_pos : ∀ w : InfinitePlace K, (0:ℝ) < w a := fun w => pos_iff.mpr ha_ne
  have hnK : 1 ≤ nK K := Module.finrank_pos
  have hBset : {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) :=
    Set.ext fun τ => by simp [Set.mem_univ_pi]
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} :=
    hBset ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioi

  set G : realSpace K → ℂ := fun τ =>
    cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * τ w * (w a) ^ 2) : ℝ) : ℂ)
      * ((∏ w : InfinitePlace K, τ w ^ w.mult : ℝ) : ℂ) ^ ((s - 2) / 2) with hG_def

  have hfactor : ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
      cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w * (w a) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p) := fun p hp => by
    have ht : (0:ℝ) < p.1 := hp.1
    simp only [hG_def, gapsw80_t8_prod_placeParam_pow_mult K ht p.2, Complex.ofReal_pow]
    rw [gapsw80_t8_ofReal_pow_cpow ht.le (nK K) ((s-2)/2),
      ← Complex.cpow_natCast (p.1:ℂ) (nK K - 1), mul_comm ((↑p.1:ℂ)^((nK K - 1 : ℕ):ℂ)),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 2
    push_cast [Nat.cast_sub hnK]; ring
  have hG_sm : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hBmeas
    refine (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_finset_sum _ fun w _ =>
          (continuous_const.mul (continuous_apply w)).mul continuous_const)).neg)).continuousOn.mul ?_
    intro τ hτ
    exact (((Complex.continuous_ofReal.comp (continuous_finset_prod _ fun w _ =>
        (continuous_apply w).pow _)).continuousAt).cpow continuousAt_const
      (Or.inl (by
        simp only [Function.comp_apply, Complex.ofReal_re]
        exact Finset.prod_pos fun w _ => pow_pos (hτ w) _))).continuousWithinAt

  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) hfactor,
    gapsw80_t8_setIntegral_placeParam K hG_sm]
  rw [show ((4:ℝ):ℂ) ^ (-(nrComplexPlaces K:ℂ)*s)
        * ((((2:ℝ)^((nrRealPlaces K:ℤ)-1) * nK K * regulator K:ℝ)⁻¹:ℂ)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1))^nrComplexPlaces K
            * ((|(Algebra.norm ℚ a : ℚ)|:ℝ):ℂ)^(-s)))
      = (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * nK K * regulator K:ℝ)⁻¹:ℂ)
        * (((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1))^nrComplexPlaces K
            * ((|(Algebra.norm ℚ a : ℚ)|:ℝ):ℂ)^(-s))) from by ring]
  congr 1

  have hreorg : ∀ τ ∈ {τ : realSpace K | ∀ w, 0 < τ w},
      ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ
        = ∏ w : InfinitePlace K,
            (((τ w : ℝ) : ℂ) ^ ((w.mult : ℂ) * s / 2 - 1)
              * cexp ((-(π * gapsw80_t7_multSq K w * (w a)^2 * τ w) : ℝ) : ℂ)) := fun τ hτ => by
    have hτpos : ∀ w, (0:ℝ) < τ w := hτ
    have hτne : ∀ w, ((τ w : ℝ) : ℂ) ≠ 0 := fun w => Complex.ofReal_ne_zero.mpr (hτpos w).ne'
    simp only [hG_def]
    rw [show cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * τ w * (w a)^2):ℝ):ℂ)
          = ∏ w : InfinitePlace K,
              cexp ((-(π * gapsw80_t7_multSq K w * (w a)^2 * τ w) : ℝ):ℂ) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.exp_sum]
        exact Finset.prod_congr rfl fun w _ => by ring_nf,
      gapsw80_t8_prod_ofReal_cpow Finset.univ (fun w _ => pow_nonneg (hτpos w).le _) ((s-2)/2),
      show (∏ w : InfinitePlace K, ((τ w ^ w.mult : ℝ):ℂ) ^ ((s-2)/2))
          = ∏ w : InfinitePlace K, ((τ w:ℝ):ℂ) ^ ((w.mult:ℂ)*(s-2)/2) from
        Finset.prod_congr rfl fun w _ => by
          rw [Complex.ofReal_pow,
            gapsw80_t8_ofReal_pow_cpow (hτpos w).le w.mult ((s-2)/2)]; ring_nf]
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)
          * ((τ w:ℝ):ℂ)^((w.mult:ℂ)*(s-2)/2)),
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => ((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
          * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)),
      mul_left_comm
        (∏ w : {w : InfinitePlace K // IsComplex w}, ((τ w.1:ℝ):ℂ)),
      ← Finset.prod_mul_distrib]
    refine congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    · rw [mult_isReal w, Nat.cast_one, one_mul, one_mul,
        show s/2-1 = (s-2)/2 from by ring, mul_comm]
    · rw [mult_isComplex w, Nat.cast_ofNat, show (2:ℂ)*(s-2)/2 = s-2 from by ring,
        show (2:ℂ)*s/2-1 = s-1 from by ring, mul_comm ((τ w.1:ℝ):ℂ), mul_assoc,
        show ((τ w.1:ℝ):ℂ)^(s-2) * ((τ w.1:ℝ):ℂ) = ((τ w.1:ℝ):ℂ)^(s-1) from by
          rw [show (s-1:ℂ) = (s-2)+1 from by ring,
            Complex.cpow_add _ _ (hτne w.1), Complex.cpow_one],
        mul_comm]

  have hmeas_eq : (volume : Measure (realSpace K)).restrict {τ | ∀ w, 0 < τ w}
      = Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [hBset, volume_pi, Measure.restrict_pi_pi]
  set fw : InfinitePlace K → ℝ → ℂ := fun w r =>
    (r:ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*r):ℝ):ℂ) with hfw_def
  have hfub : (∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
        ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ), fw w r :=
    integral_fintype_prod_eq_prod fw
  rw [setIntegral_congr_fun hBmeas hreorg,
    show (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ∏ w : InfinitePlace K, (((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
            * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)))
        = ∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
          ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0))
      from by rw [← hmeas_eq],
    hfub]
  simp only [hfw_def]
  have hβre : ∀ w : InfinitePlace K, (0:ℝ) < ((w.mult:ℂ)*s/2).re := fun w => by
    have hre : ((w.mult:ℂ)*s/2).re = (w.mult : ℝ)*s.re/2 := by
      rw [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    rw [hre]
    exact div_pos (mul_pos (Nat.cast_pos.mpr w.mult_pos) (lt_trans one_pos hs)) two_pos
  rw [show (∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ),
            ((r:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
              * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*r):ℝ):ℂ))
        = ∏ w : InfinitePlace K,
            (((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by
        simp only [Complex.ofReal_neg]
        exact gapsw80_t8_mellin_expNeg_eq_Gamma
          (mul_pos (mul_pos Real.pi_pos (multSq_pos K w)) (pow_pos (ha_pos w) 2)) (hβre w)]

  have hx_nz : ∀ w, normAtPlace w (mixedEmbedding K a) ≠ 0 := fun w => by
    rw [normAtPlace_apply]; exact (ha_pos w).ne'
  have hsplit : ∀ w : InfinitePlace K,
      ((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
        = ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
          * ((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) := fun w => by
    rw [show π * gapsw80_t7_multSq K w * (w a)^2
          = gapsw80_t7_multSq K w * (π * (w a)^2) from by ring,
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (multSq_pos K w).le
        (mul_nonneg Real.pi_pos.le (sq_nonneg _))]
  rw [show (∏ w : InfinitePlace K,
            (((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)))
        = (∏ w : InfinitePlace K, ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)))
          * ∏ w : InfinitePlace K,
              (((π * normAtPlace w (mixedEmbedding K a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
                * Complex.Gamma ((w.mult:ℂ)*s/2)) from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [hsplit w, normAtPlace_apply]; ring,
    gapsw80_t8_prod_gammaFactor_eq K hs hx_nz,
    gapsw80_t8_prod_normAtPlace_cpow K hx_nz s,
    mixedEmbedding.norm_eq_norm, Rat.cast_abs]

  congr 1
  rw [prod_eq_prod_mul_prod (K := K)
      (f := fun w => ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)))]
  have hreal : (∏ w : {w : InfinitePlace K // IsReal w},
      ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2))) = 1 :=
    Finset.prod_eq_one fun w _ => by
      rw [show gapsw80_t7_multSq K w.1 = 1 from by
        simp [gapsw80_t7_multSq, mult_isReal w], Complex.ofReal_one, Complex.one_cpow]
  have hcplx : (∏ w : {w : InfinitePlace K // IsComplex w},
        ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2)))
      = ((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s) := by
    rw [show (∏ w : {w : InfinitePlace K // IsComplex w},
            ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2)))
          = ∏ _w : {w : InfinitePlace K // IsComplex w}, ((4:ℝ):ℂ)^(-s) from
        Finset.prod_congr rfl fun w _ => by
          rw [show gapsw80_t7_multSq K w.1 = 4 from by
            simp [gapsw80_t7_multSq, mult_isComplex w]; norm_num,
            mult_isComplex w]
          congr 1; push_cast; ring,
      Finset.prod_const, ← Complex.cpow_nat_mul, Finset.card_univ,
      show Fintype.card {w : InfinitePlace K // IsComplex w} = nrComplexPlaces K from rfl]
    congr 1; push_cast; ring
  rw [hreal, one_mul, hcplx]

theorem gapsw80_t8_symmLambda_eq_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = ((torsionOrder K : ℂ)
          / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ)))
        * ((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * ((ZLattice.covolume (mixedEmbedding.idealLattice K
            (gapsw80_t6_traceDualIdeal K I)) : ℝ) : ℂ) ^ (-s)
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I))⁻¹ s := by
  set J := gapsw80_t6_traceDualIdeal K I with hJ_def

  rw [gapsw80_t8_symmLambda_unfold_eq K I hs,
    tsum_congr (gapsw80_t8_perOrbit_integral_eq_mult K J hs), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, gapsw80_t8_tsum_orbit_normInv_eq K J hs, mul_pow (Gammaℂ s),
    div_eq_mul_inv, mul_inv, mul_inv]

  set Ccov : ℂ := ((ZLattice.covolume (mixedEmbedding.idealLattice K J):ℝ):ℂ)^(-s) with hCcov
  set Cdisc : ℂ := ((|(discr K:ℝ)|:ℝ):ℂ)^(s/2) with hCdisc
  set CabsN : ℂ := ((FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K):ℝ):ℂ)^(-s) with hCabsN
  set C2rs : ℂ := ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s) with hC2rs
  set C4rs : ℂ := ((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s) with hC4rs
  have hcd : Ccov * Cdisc = CabsN * C2rs := gapsw80_t8_covol_discr_cpow K J s
  have h2ne : (2:ℂ) ≠ 0 := two_ne_zero
  have hr₁ : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    have h1 := card_add_two_mul_card_eq_rank K
    have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hconst : (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * (nK K:ℝ) * regulator K : ℝ)⁻¹ : ℂ)
        * ((2:ℂ)^(s-1))^nrComplexPlaces K
      = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * ((nK K:ℂ))⁻¹
        * ((regulator K:ℝ):ℂ)⁻¹ * C2rs := by
    have h2pow : ((2:ℂ)^((nrRealPlaces K:ℤ)-1 : ℤ))⁻¹ * ((2:ℂ)^(s-1))^nrComplexPlaces K
        = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * C2rs := by
      rw [hC2rs, Complex.ofReal_ofNat,
        ← Complex.cpow_intCast (2:ℂ) ((nrRealPlaces K:ℤ)-1),
        ← Complex.cpow_natCast (2:ℂ) (nrRealPlaces K + nrComplexPlaces K - 1),
        ← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_nat_mul (2:ℂ) (nrComplexPlaces K) (s-1),
        ← Complex.cpow_add _ _ h2ne, ← Complex.cpow_add _ _ h2ne]
      congr 1
      push_cast [Nat.cast_sub hr₁]; ring
    rw [← Complex.ofReal_inv, mul_inv, mul_inv, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zpow, Complex.ofReal_ofNat]
    linear_combination ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹ * h2pow
  linear_combination C4rs * (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K J)⁻¹ s * CabsN
        * (torsionOrder K : ℂ)) * hconst
    - C4rs * ((torsionOrder K : ℂ) * ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K J)⁻¹ s) * hcd

theorem gapsw80_t8_sat_covol_prod (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (mixedEmbedding.idealLattice K I)
        * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I))
      = (4 : ℝ)⁻¹ ^ nrComplexPlaces K := by
  have h4 : ((4:ℝ) ^ nrComplexPlaces K) ≠ 0 := (pow_pos (by norm_num) _).ne'
  have hdet : |(gapsw80_t6_bridgeMatrix K I).det|
      = ZLattice.covolume (mixedEmbedding.idealLattice K I)
          * (4 : ℝ) ^ nrComplexPlaces K
          * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I)) := by
    rw [gapsw80_t6_bridgeMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, abs_mul, abs_det_coordMatrix, abs_det_coordMatrix, gapsw80_t6_abs_det_Phi]
  have h1 : ZLattice.covolume (mixedEmbedding.idealLattice K I)
        * (4 : ℝ) ^ nrComplexPlaces K
        * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I))
      = 1 := hdet ▸ gapsw80_t6_abs_det_bridgeMatrix K I
  rw [inv_pow]; field_simp
  linear_combination h1

end FLT.Gapsw80T8MellinGammaPartialZeta
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T9ClassSumA1Closure

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"
open FLT.Gapsw80T3IdealLatticeThetaTransformation FLT.Gapsw80T5HeckeThetaKernel
open FLT.Gapsw80T6TraceDualBridge FLT.Gapsw80T7ClosedFEWeakPair
open FLT.Gapsw80T8MellinGammaPartialZeta
p2m_open "Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

noncomputable def gapsw80_t9_constK : ℂ :=
  (torsionOrder K : ℂ)
    / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ))

theorem gapsw80_t9_constK_def :
    gapsw80_t9_constK K = (torsionOrder K : ℂ)
      / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1)
          * (nK K : ℂ) * (regulator K : ℂ)) := rfl

theorem gapsw80_t9_constK_ne_zero : gapsw80_t9_constK K ≠ 0 := by
  refine div_ne_zero ?_ (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · exact_mod_cast (torsionOrder_pos K).ne'
  · exact pow_ne_zero _ two_ne_zero
  · exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  · exact Complex.ofReal_ne_zero.mpr (regulator_pos K).ne'

noncomputable def gapsw80_t9_classRepr (C : ClassGroup (𝓞 K)) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (FractionalIdeal.mk0 K (ClassGroup.mk0_surjective C).choose)⁻¹

theorem gapsw80_t9_mk_classRepr (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (gapsw80_t9_classRepr K C) = C⁻¹ := by
  unfold gapsw80_t9_classRepr
  rw [map_inv, ClassGroup.mk_mk0, (ClassGroup.mk0_surjective C).choose_spec]

noncomputable abbrev gapsw80_t9_covolRepr (C : ClassGroup (𝓞 K)) : ℝ :=
  ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t9_classRepr K C))

theorem gapsw80_t9_covolRepr_pos (C : ClassGroup (𝓞 K)) :
    0 < gapsw80_t9_covolRepr K C := gapsw80_t7_covol_pos K _

noncomputable def gapsw80_t9_completedDedekindZeta (s : ℂ) : ℂ :=
  (gapsw80_t9_constK K)⁻¹
    * ∑ C : ClassGroup (𝓞 K),
        ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
          * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ ((nK K : ℂ) * s / 2)

noncomputable abbrev gapsw80_t9_gammaFactor (s : ℂ) : ℂ :=
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

theorem gapsw80_t9_sigma_one_sub (s : ℂ) :
    (nK K : ℂ) * (1 - s) / 2
      = (((nK K : ℝ) / 2 : ℝ) : ℂ) - (nK K : ℂ) * s / 2 := by
  push_cast; ring

theorem gapsw80_t9_perClass_FE_step (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (1 - s)
        * (gapsw80_t7_heckeWeakFEPair K I).Λ ((nK K : ℂ) * (1 - s) / 2)
      = ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2) := by
  have hFE := (gapsw80_t7_heckeWeakFEPair K I).functional_equation ((nK K : ℂ) * s / 2)
  have hk : (gapsw80_t7_heckeWeakFEPair K I).k = (nK K : ℝ) / 2 := rfl
  have hε : (gapsw80_t7_heckeWeakFEPair K I).ε
      = ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℂ))⁻¹ := rfl
  rw [hk, hε, smul_eq_mul] at hFE
  have hcov : ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (gapsw80_t7_covol_pos K I).ne'
  rw [gapsw80_t9_sigma_one_sub, hFE, ← mul_assoc]
  congr 1
  rw [show (1:ℂ) - s = (-s) + 1 from by ring, Complex.cpow_add _ _ hcov, Complex.cpow_one,
    mul_assoc, mul_inv_cancel₀ hcov, mul_one]

theorem gapsw80_t9_four_cpow_cancel (s : ℂ) :
    ((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * (((4:ℝ)⁻¹ ^ nrComplexPlaces K : ℝ) : ℂ) ^ (-s)
      = 1 := by
  have h4 : ((4:ℝ):ℂ) ≠ 0 := by norm_num
  have harg : Complex.arg ((4:ℝ):ℂ) = 0 :=
    Complex.arg_ofReal_of_nonneg (by norm_num)
  have harg' : Complex.arg (((4:ℝ):ℂ)^nrComplexPlaces K) ≠ Real.pi := by
    rw [show ((4:ℝ):ℂ) ^ nrComplexPlaces K = ((4 ^ nrComplexPlaces K : ℝ) : ℂ) from
      by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm

  have hinv : (((4:ℝ)⁻¹^nrComplexPlaces K : ℝ):ℂ) = (((4:ℝ):ℂ)^nrComplexPlaces K)⁻¹ := by
    rw [inv_pow]; push_cast; ring
  rw [hinv, Complex.inv_cpow _ _ harg',
    ← Complex.cpow_nat_mul' (x := ((4:ℝ):ℂ))
      (by rw [harg, mul_zero]; linarith [Real.pi_pos])
      (by rw [harg, mul_zero]; exact Real.pi_pos.le) (-s),
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ h4]
  convert Complex.cpow_zero _ using 2
  push_cast; ring

theorem gapsw80_t9_covol_cancel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
          * ((ZLattice.covolume (mixedEmbedding.idealLattice K
              (gapsw80_t6_traceDualIdeal K I)) : ℝ) : ℂ) ^ (-s))
      = 1 := by
  have hI := (gapsw80_t7_covol_pos K I).le
  have hJ := (gapsw80_t7_covol_pos K (gapsw80_t6_traceDualIdeal K I)).le
  rw [show ∀ a b c : ℂ, a*(b*c) = b*(a*c) from fun a b c => by ring,
    ← Complex.mul_cpow_ofReal_nonneg hI hJ, ← Complex.ofReal_mul,
    gapsw80_t8_sat_covol_prod]
  exact gapsw80_t9_four_cpow_cancel K s

theorem gapsw80_t9_perClass_identified (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = gapsw80_t9_constK K
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gapsw80_t9_gammaFactor K s
        * gapsw80_t8_partialDedekindZeta K
            (ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I))⁻¹ s := by
  rw [gapsw80_t8_symmLambda_eq_completedPartialZeta K I hs, ← gapsw80_t9_constK_def]
  linear_combination
    (gapsw80_t9_constK K * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
      * gapsw80_t9_gammaFactor K s
      * gapsw80_t8_partialDedekindZeta K
          (ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I))⁻¹ s)
    * gapsw80_t9_covol_cancel K I s

noncomputable def gapsw80_t9_diffIdeal : (Ideal (𝓞 K))⁰ :=
  ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_iff_ne_zero.mpr differentIdeal_ne_bot⟩

noncomputable def gapsw80_t9_diffClass : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (gapsw80_t9_diffIdeal K)

theorem gapsw80_t9_traceDualIdeal_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    gapsw80_t6_traceDualIdeal K I
      = (FractionalIdeal.mk0 K (gapsw80_t9_diffIdeal K))⁻¹ * I⁻¹ := by
  apply Units.ext
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0]
  congr 1
  have h := coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)
  rw [gapsw80_t9_diffIdeal, h, inv_inv]

theorem gapsw80_t9_mk_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I)
      = (gapsw80_t9_diffClass K)⁻¹ * (ClassGroup.mk K I)⁻¹ := by
  rw [gapsw80_t9_traceDualIdeal_eq, map_mul, map_inv, map_inv, ClassGroup.mk_mk0,
    gapsw80_t9_diffClass]

noncomputable def gapsw80_t9_classBijection : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.inv (ClassGroup (𝓞 K))).trans (Equiv.mulLeft (gapsw80_t9_diffClass K))

theorem gapsw80_t9_classBijection_apply (C : ClassGroup (𝓞 K)) :
    gapsw80_t9_classBijection K C = gapsw80_t9_diffClass K * C⁻¹ := rfl

theorem gapsw80_t9_sum_bijection_partialZeta (s : ℂ) :
    ∑ C : ClassGroup (𝓞 K),
        gapsw80_t8_partialDedekindZeta K (gapsw80_t9_diffClass K * C⁻¹) s
      = ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s :=
  Finset.sum_equiv (gapsw80_t9_classBijection K) (fun _ => by simp)
    (fun C _ => by rw [gapsw80_t9_classBijection_apply])

theorem gapsw80_t9_completedDedekindZeta_eq_sum {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K s
      = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gapsw80_t9_gammaFactor K s
        * ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s := by
  unfold gapsw80_t9_completedDedekindZeta gapsw80_t9_covolRepr gapsw80_t9_gammaFactor
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [gapsw80_t8_heckeLambda_eq_completedPartialZeta K (gapsw80_t9_classRepr K C) hs,
    gapsw80_t9_mk_classRepr, inv_inv, ← gapsw80_t9_constK_def]
  set cov : ℂ := ((ZLattice.covolume
      (mixedEmbedding.idealLattice K (gapsw80_t9_classRepr K C)) : ℝ) : ℂ) with hcov_def
  have hcov : cov ≠ 0 := Complex.ofReal_ne_zero.mpr (gapsw80_t7_covol_pos K _).ne'
  have key : (gapsw80_t9_constK K)⁻¹ * cov ^ s * (gapsw80_t9_constK K * cov ^ (-s)) = 1 := by
    rw [show ∀ a b c d : ℂ, a*b*(c*d) = (a*c)*(b*d) from fun a b c d => by ring,
      inv_mul_cancel₀ (gapsw80_t9_constK_ne_zero K),
      ← Complex.cpow_add _ _ hcov, add_neg_cancel, Complex.cpow_zero, one_mul]
  linear_combination
    (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K
      * Gammaℂ s ^ nrComplexPlaces K * gapsw80_t8_partialDedekindZeta K C s) * key

theorem gapsw80_t9_completedDedekindZeta_one_sub_eq_sum {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K (1 - s)
      = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gapsw80_t9_gammaFactor K s
        * ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s := by
  unfold gapsw80_t9_completedDedekindZeta gapsw80_t9_covolRepr
  rw [← gapsw80_t9_sum_bijection_partialZeta, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [gapsw80_t9_perClass_FE_step, gapsw80_t9_perClass_identified K _ hs,
    gapsw80_t9_mk_traceDualIdeal, gapsw80_t9_mk_classRepr, inv_inv, mul_inv, inv_inv]
  linear_combination
    (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) * gapsw80_t9_gammaFactor K s
      * gapsw80_t8_partialDedekindZeta K (gapsw80_t9_diffClass K * C⁻¹) s)
    * inv_mul_cancel₀ (gapsw80_t9_constK_ne_zero K)

theorem gapsw80_t9_FE_halfplane {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s :=
  (gapsw80_t9_completedDedekindZeta_one_sub_eq_sum K hs).trans
    (gapsw80_t9_completedDedekindZeta_eq_sum K hs).symm

theorem gapsw80_t9_isClosed_pair : IsClosed ({(0:ℂ), 1} : Set ℂ) :=
  ((Set.finite_singleton (1:ℂ)).insert 0).isClosed

theorem gapsw80_t9_isPreconnected_compl :
    IsPreconnected ({(0:ℂ), 1}ᶜ : Set ℂ) :=
  (Set.Countable.isConnected_compl_of_one_lt_rank
    (rank_real_complex ▸ Nat.one_lt_ofNat)
    (((Set.finite_singleton (1:ℂ)).insert 0).countable)).isPreconnected

theorem gapsw80_t9_nK_ne_zero : (nK K : ℂ) ≠ 0 := by
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'

theorem gapsw80_t9_differentiableOn_completedDedekindZeta :
    DifferentiableOn ℂ (gapsw80_t9_completedDedekindZeta K) {(0:ℂ), 1}ᶜ := by
  refine (differentiableOn_const _).mul (DifferentiableOn.fun_sum (fun C _ => ?_))
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  refine ((differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (gapsw80_t9_covolRepr_pos K C).ne'))).mul ?_
    ).differentiableWithinAt
  refine ((gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).differentiableAt_Λ
    ?_ ?_).comp s ((differentiableAt_const _).mul differentiableAt_id |>.div_const _)
  · left
    exact fun h => hs.1 (by
      have := mul_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right two_ne_zero)
      exact this.resolve_left (gapsw80_t9_nK_ne_zero K))
  · left
    intro h
    apply hs.2
    have hk : ((gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).k : ℂ)
        = (nK K : ℂ) / 2 := by
      show (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2; push_cast; ring
    rw [hk, div_eq_div_iff (two_ne_zero) (two_ne_zero)] at h
    have h' := mul_right_cancel₀ (two_ne_zero (α := ℂ)) h
    exact mul_left_cancel₀ (gapsw80_t9_nK_ne_zero K) (h'.trans (mul_one _).symm)

theorem gapsw80_t9_analyticOnNhd_completedDedekindZeta :
    AnalyticOnNhd ℂ (gapsw80_t9_completedDedekindZeta K) {(0:ℂ), 1}ᶜ :=
  (gapsw80_t9_differentiableOn_completedDedekindZeta K).analyticOnNhd
    gapsw80_t9_isClosed_pair.isOpen_compl

theorem gapsw80_t9_completedDedekindZeta_FE {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    gapsw80_t9_completedDedekindZeta K (1 - s) = gapsw80_t9_completedDedekindZeta K s := by
  have hU : IsOpen ({(0:ℂ), 1}ᶜ : Set ℂ) := (gapsw80_t9_isClosed_pair).isOpen_compl
  have hAf := gapsw80_t9_analyticOnNhd_completedDedekindZeta K
  have hAg : AnalyticOnNhd ℂ
      (fun z => gapsw80_t9_completedDedekindZeta K (1 - z)) {(0:ℂ), 1}ᶜ := by
    have hswap : Set.MapsTo (fun z : ℂ => 1 - z) {(0:ℂ), 1}ᶜ {(0:ℂ), 1}ᶜ := by
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or, sub_eq_zero, sub_eq_self] at hz ⊢
      exact ⟨fun h => hz.2 h.symm, hz.1⟩
    exact fun z hz => (hAf _ (hswap hz)).comp (analyticAt_const.sub analyticAt_id)
  have hsU : s ∈ ({(0:ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs0, hs1⟩
  have h2U : (2:ℂ) ∈ ({(0:ℂ), 1}ᶜ : Set ℂ) := by norm_num
  refine (hAg.eqOn_of_preconnected_of_frequently_eq hAf
    gapsw80_t9_isPreconnected_compl h2U ?_ hsU)

  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2mem : (2:ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
  exact ((Filter.eventually_of_mem (hopen.mem_nhds h2mem)
    (fun z hz => gapsw80_t9_FE_halfplane K hz)).filter_mono
      nhdsWithin_le_nhds).frequently

section Guards

end Guards
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

end FLT.Gapsw80T9ClassSumA1Closure
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T10DedekindZetaBridgeA1Discharge

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
open FLT.Gapsw80T8MellinGammaPartialZeta FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
p2m_open "Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set Ideal P2MW.S_NumberField_exists_completedDedekindZeta_package.Ideal NumberField.Ideal Asymptotics P2MW.S_NumberField_exists_completedDedekindZeta_package.Asymptotics"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

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

theorem gapsw80_t10_sum_partialDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s
      = dedekindZeta K s := by
  have hSum := gapsw80_t10_summable_idealNorm K hs

  have hHS : HasSum
      (fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (dedekindZeta K s) := by
    have hSig := (Equiv.sigmaFiberEquiv
      (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).summable_iff.mpr hSum
    refine (Equiv.sigmaFiberEquiv
      (fun J : (Ideal (𝓞 K))⁰ => absNorm (J : Ideal (𝓞 K)))).hasSum_iff.mp ?_
    exact HasSum.sigma_of_hasSum
      (gapsw80_t10_LSeriesSummable_dedekindZeta K hs).hasSum
      (gapsw80_t10_fiber_hasSum K s) hSig

  have stepC : ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s
      = ∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) := by
    have hSig : HasSum
        ((fun J : (Ideal (𝓞 K))⁰ ↦ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) ∘
          (Equiv.sigmaFiberEquiv
            (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K))))
        (∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) :=
      (Equiv.sigmaFiberEquiv
        (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K))).hasSum_iff.mpr hSum.hasSum
    have hOuter : HasSum (fun C : ClassGroup (𝓞 K) => gapsw80_t8_partialDedekindZeta K C s)
        (∑' J : (Ideal (𝓞 K))⁰, ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) :=
      hSig.sigma fun C => (hSum.subtype _).hasSum
    exact (hasSum_fintype _).unique hOuter
  rw [stepC, hHS.tsum_eq]

theorem gapsw80_t10_discrCoercion :
    (((|discr K| : ℤ) : ℂ)) = (((|(discr K : ℝ)| : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_intCast, Int.cast_abs]

theorem gapsw80_t10_completedDedekindZeta_eq_T1 {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t9_completedDedekindZeta K s
      = gapsw80_t1_completedDedekindZeta K s := by
  rw [gapsw80_t9_completedDedekindZeta_eq_sum K hs,
    gapsw80_t10_sum_partialDedekindZeta_eq K hs,
    gapsw80_t1_completedDedekindZeta, gapsw80_t10_discrCoercion,
    gapsw80_t9_gammaFactor]
  ring

noncomputable def gapsw80_t10_Lambda (s : ℂ) : ℂ :=
  if s = 0 ∨ s = 1 then gapsw80_t9_completedDedekindZeta K 2
  else gapsw80_t9_completedDedekindZeta K s

theorem gapsw80_t10_Lambda_eqOn :
    Set.EqOn (gapsw80_t10_Lambda K) (gapsw80_t9_completedDedekindZeta K)
      {(0 : ℂ), 1}ᶜ := by
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  exact if_neg (not_or.mpr hs)

theorem gapsw80_t10_Lambda_differentiableOn :
    DifferentiableOn ℂ (gapsw80_t10_Lambda K) {(0 : ℂ), 1}ᶜ :=
  (gapsw80_t9_differentiableOn_completedDedekindZeta K).congr
    (gapsw80_t10_Lambda_eqOn K)

theorem gapsw80_t10_Lambda_eq_T1 {s : ℂ} (hs : 1 < s.re) :
    gapsw80_t10_Lambda K s = gapsw80_t1_completedDedekindZeta K s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  rw [gapsw80_t10_Lambda, if_neg (not_or.mpr ⟨hs0, hs1⟩)]
  exact gapsw80_t10_completedDedekindZeta_eq_T1 K hs

theorem gapsw80_t10_Lambda_FE (s : ℂ) :
    gapsw80_t10_Lambda K (1 - s) = gapsw80_t10_Lambda K s := by
  unfold gapsw80_t10_Lambda
  by_cases h : s = 0 ∨ s = 1
  · have h' : (1 - s) = 0 ∨ (1 - s) = 1 := by
      rcases h with h0 | h1
      · exact Or.inr (by rw [h0]; ring)
      · exact Or.inl (by rw [h1]; ring)
    rw [if_pos h', if_pos h]
  · rw [not_or] at h
    have h' : ¬((1 - s) = 0 ∨ (1 - s) = 1) := by
      rw [not_or]
      exact ⟨fun hc => h.2 (sub_eq_zero.mp hc).symm, fun hc => h.1 (sub_eq_self.mp hc)⟩
    rw [if_neg h', if_neg (not_or.mpr h)]
    exact gapsw80_t9_completedDedekindZeta_FE K h.1 h.2

theorem gapsw80_t10_A1_closed :
    FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition.gapsw80_t1_DedekindCompletedFE := by
  intro K
  exact ⟨gapsw80_t10_Lambda K,
    gapsw80_t10_Lambda_differentiableOn K,
    fun s hs => gapsw80_t10_Lambda_eq_T1 K hs,
    gapsw80_t10_Lambda_FE K⟩

end FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T11ExplicitFormulaA34Decomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module"

def gapsw80_t11_XiOrderOneHadamard : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ ξ : ℂ → ℂ,
      Differentiable ℂ ξ ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
        ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) ∧
      (∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖)

end FLT.Gapsw80T11ExplicitFormulaA34Decomp
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

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
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex"

section PerK

variable (K : Type) [Field K] [NumberField K]

end PerK
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

def gapsw80_t32_XiEndpointNonvanishing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ ξ : ℂ → ℂ,
    Differentiable ℂ ξ →
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      ξ s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s) →
    ξ 0 ≠ 0 ∧ ξ 1 ≠ 0

end FLT.Gapsw80T32D1aBoundaryCaseDecomp
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

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
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

def gapsw80_t42_CompletedZetaRealSuperlinear : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∀ C : ℝ, ∃ s : ℂ,
    2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
    C * ‖s‖ < Real.log ‖s * (s - 1) * gapsw80_t9_completedDedekindZeta K s‖

end FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace KwDyf2XiEntireOrderDecomp

open FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T7ClosedFEWeakPair
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

noncomputable abbrev kwDyf2_P (C : ClassGroup (𝓞 K)) : WeakFEPair ℂ :=
  gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)

noncomputable def kwDyf2_xiSummand (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
    * (s * (s - 1) * (kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)
        - 2 * (s - 1) / (nK K : ℂ)
        + 2 * s * (kwDyf2_P K C).ε / (nK K : ℂ))

noncomputable def kwDyf2_xi (s : ℂ) : ℂ :=
  (gapsw80_t9_constK K)⁻¹ * ∑ C : ClassGroup (𝓞 K), kwDyf2_xiSummand K C s

theorem kwDyf2_differentiable_const_cpow {c : ℝ} (hc : 0 < c) :
    Differentiable ℂ (fun s : ℂ => (c : ℂ) ^ s) :=
  fun _ => differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))

theorem kwDyf2_differentiable_xiSummand (C : ClassGroup (𝓞 K)) :
    Differentiable ℂ (kwDyf2_xiSummand K C) := by
  unfold kwDyf2_xiSummand
  refine (kwDyf2_differentiable_const_cpow (gapsw80_t9_covolRepr_pos K C)).mul ?_
  refine (((differentiable_id.mul (differentiable_id.sub_const 1)).mul ?_).sub
    ((differentiable_const 2 |>.mul (differentiable_id.sub_const 1)).div_const _)).add
    (((differentiable_const 2).mul differentiable_id |>.mul (differentiable_const _)).div_const _)
  exact (kwDyf2_P K C).differentiable_Λ₀.comp
    (((differentiable_const _).mul differentiable_id).div_const _)

theorem kwDyf2_differentiable_xi : Differentiable ℂ (kwDyf2_xi K) := by
  have _em := Classical.em
  unfold kwDyf2_xi
  exact (differentiable_const _).mul
    (Differentiable.fun_sum (fun C _ => kwDyf2_differentiable_xiSummand K C))

theorem kwDyf2_Pk_coe (C : ClassGroup (𝓞 K)) :
    ((kwDyf2_P K C).k : ℂ) = (nK K : ℂ) / 2 := by
  show (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2; push_cast; ring

theorem kwDyf2_xiSummand_eq (C : ClassGroup (𝓞 K)) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    kwDyf2_xiSummand K C s =
      ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
        * (s * (s - 1)
            * (kwDyf2_P K C).Λ ((nK K : ℂ) * s / 2)) := by
  unfold kwDyf2_xiSummand
  congr 1
  have hf0 : (kwDyf2_P K C).f₀ = 1 := rfl
  have hg0 : (kwDyf2_P K C).g₀ = 1 := rfl
  simp only [WeakFEPair.Λ, hf0, hg0, smul_eq_mul, mul_one]
  rw [kwDyf2_Pk_coe K C]
  have hn : (nK K : ℂ) ≠ 0 := gapsw80_t9_nK_ne_zero K
  have hσ : (nK K : ℂ) * s / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hn hs0) two_ne_zero
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hkσ : (nK K : ℂ) / 2 - (nK K : ℂ) * s / 2 ≠ 0 := by
    rw [div_sub_div_same, ← mul_one_sub]
    exact div_ne_zero (mul_ne_zero hn h1s) two_ne_zero
  field_simp
  ring

theorem kwDyf2_xi_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    kwDyf2_xi K s = s * (s - 1) * gapsw80_t9_completedDedekindZeta K s := by
  have _em := Classical.em
  unfold kwDyf2_xi gapsw80_t9_completedDedekindZeta
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [kwDyf2_xiSummand_eq K C hs0 hs1]
  ring

def kwDyf2_XiOrderBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

set_option maxHeartbeats 3200000 in

theorem kwDyf2_B1_of_C1 (hC1 : kwDyf2_XiOrderBound) :
    gapsw80_t11_XiOrderOneHadamard := by
  have _em := Classical.em
  intro K _ _
  exact ⟨kwDyf2_xi K, kwDyf2_differentiable_xi K,
    fun s hs0 hs1 => kwDyf2_xi_eq K hs0 hs1, hC1 K⟩

set_option maxHeartbeats 3200000 in

theorem kwDyf2_sat_xi_FE {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    kwDyf2_xi K (1 - s) = kwDyf2_xi K s := by
  have _em := Classical.em
  have h1s0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have h1s1 : (1 : ℂ) - s ≠ 1 := fun h => hs0 (sub_eq_self.mp h)
  rw [kwDyf2_xi_eq K h1s0 h1s1, kwDyf2_xi_eq K hs0 hs1,
    gapsw80_t9_completedDedekindZeta_FE K hs0 hs1]
  ring

end FLT.KwDyf2XiEntireOrderDecomp
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section AxiomAudits
open FLT.KwDyf2XiEntireOrderDecomp

end AxiomAudits
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

namespace FLT
namespace Gapsw80T36D1appXiEndpointResidueProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T7ClosedFEWeakPair
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T31D1HadamardSubDecomp
open FLT.Gapsw80T32D1aBoundaryCaseDecomp
open FLT.Gapsw80T35D1apa0ThreeFourOneIneqProof
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter"
p2m_open_scoped "nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

theorem gapsw80_t36_nK_cast_ne_zero : (nK K : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne'

theorem gapsw80_t36_nK_cast_half : (((nK K : ℝ) / 2 : ℝ) : ℂ) = (nK K : ℂ) / 2 := by
  push_cast; ring

theorem gapsw80_t36_affine_tendsto (a : ℂ) :
    Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] a) (𝓝[≠] ((nK K : ℂ) * a / 2)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (((continuous_const.mul continuous_id').div_const 2).tendsto a).mono_left
      nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall (fun s hs ↦ ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
    exact fun h ↦ hs (mul_left_cancel₀ (gapsw80_t36_nK_cast_ne_zero K)
      (by linear_combination 2 * h))

set_option maxHeartbeats 3200000 in

theorem gapsw80_t36_perClass_residue_one (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
        * ((s - 1)
          * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 1) (𝓝 (2 / (nK K : ℂ))) := by
  set P := gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)
  have hn := gapsw80_t36_nK_cast_ne_zero K
  have hk : (P.k : ℂ) = (nK K : ℂ) / 2 := gapsw80_t36_nK_cast_half K

  have hmap : Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] 1) (𝓝[≠] (P.k : ℂ)) := by
    have := gapsw80_t36_affine_tendsto K 1
    rwa [mul_one, ← hk] at this
  have hres : Tendsto (fun s : ℂ ↦ ((nK K : ℂ) * s / 2 - (P.k : ℂ))
        * P.Λ ((nK K : ℂ) * s / 2)) (𝓝[≠] 1) (𝓝 P.ε) := by
    have h := P.Λ_residue_k.comp hmap
    simpa only [Function.comp_def, smul_eq_mul,
      show (P.g₀ : ℂ) = 1 from rfl, mul_one] using h

  have hres' : Tendsto (fun s : ℂ ↦ (s - 1) * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 1) (𝓝 ((2 / (nK K : ℂ)) * P.ε)) := by
    refine (hres.const_mul (2 / (nK K : ℂ))).congr' (Eventually.of_forall fun s ↦ ?_)
    rw [hk, show (2 / (nK K : ℂ)) * (((nK K : ℂ) * s / 2 - (nK K : ℂ) / 2)
          * P.Λ ((nK K : ℂ) * s / 2))
        = ((2 / (nK K : ℂ)) * ((nK K : ℂ) / 2)) * ((s - 1) * P.Λ ((nK K : ℂ) * s / 2))
        from by ring,
      show (2 / (nK K : ℂ)) * ((nK K : ℂ) / 2) = 1 from by field_simp, one_mul]

  have hcvne : ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (gapsw80_t9_covolRepr_pos K C).ne'
  have hcov : Tendsto (fun s : ℂ ↦ ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s)
      (𝓝[≠] 1) (𝓝 ((gapsw80_t9_covolRepr K C : ℝ) : ℂ)) := by
    have := (continuousAt_const_cpow hcvne (b := 1)).tendsto
    simpa only [Complex.cpow_one] using this.mono_left nhdsWithin_le_nhds
  have hcε : ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) * P.ε = 1 := by
    show ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) * ((gapsw80_t9_covolRepr K C : ℝ) : ℂ)⁻¹ = 1
    exact mul_inv_cancel₀ hcvne
  have := hcov.mul hres'
  rwa [show ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) * ((2 / (nK K : ℂ)) * P.ε)
      = (2 / (nK K : ℂ)) * (((gapsw80_t9_covolRepr K C : ℝ) : ℂ) * P.ε) from by ring,
    hcε, mul_one] at this

set_option maxHeartbeats 3200000 in

theorem gapsw80_t36_perClass_residue_zero (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℂ ↦ ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
        * (s * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
            ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 0) (𝓝 (-(2 / (nK K : ℂ)))) := by
  set P := gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)
  have hn := gapsw80_t36_nK_cast_ne_zero K
  have hmap : Tendsto (fun s : ℂ ↦ (nK K : ℂ) * s / 2) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    have := gapsw80_t36_affine_tendsto K 0
    simpa using this
  have hres : Tendsto (fun s : ℂ ↦ ((nK K : ℂ) * s / 2) * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 0) (𝓝 (-1 : ℂ)) := by
    have h := P.Λ_residue_zero.comp hmap
    simpa only [Function.comp_def, smul_eq_mul,
      show (P.f₀ : ℂ) = 1 from rfl] using h
  have hres' : Tendsto (fun s : ℂ ↦ s * P.Λ ((nK K : ℂ) * s / 2))
      (𝓝[≠] 0) (𝓝 (-(2 / (nK K : ℂ)))) := by
    have h := hres.const_mul (2 / (nK K : ℂ))
    rw [show (2 / (nK K : ℂ)) * (-1) = -(2 / (nK K : ℂ)) from by ring] at h
    refine h.congr' (Eventually.of_forall fun s ↦ ?_)
    rw [show (2 / (nK K : ℂ)) * ((nK K : ℂ) * s / 2 * P.Λ ((nK K : ℂ) * s / 2))
        = ((2 / (nK K : ℂ)) * ((nK K : ℂ) / 2)) * (s * P.Λ ((nK K : ℂ) * s / 2))
        from by ring,
      show (2 / (nK K : ℂ)) * ((nK K : ℂ) / 2) = 1 from by field_simp, one_mul]
  have hcvne : ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (gapsw80_t9_covolRepr_pos K C).ne'
  have hcov : Tendsto (fun s : ℂ ↦ ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s)
      (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    have := (continuousAt_const_cpow hcvne (b := 0)).tendsto
    simpa only [Complex.cpow_zero] using this.mono_left nhdsWithin_le_nhds
  have := hcov.mul hres'
  rwa [one_mul] at this

noncomputable def gapsw80_t36_xiResidueVal : ℂ :=
  (gapsw80_t9_constK K)⁻¹
    * (2 * (Fintype.card (ClassGroup (𝓞 K)) : ℂ) / (nK K : ℂ))

theorem gapsw80_t36_xiResidueVal_ne_zero : gapsw80_t36_xiResidueVal K ≠ 0 := by
  refine mul_ne_zero (inv_ne_zero (gapsw80_t9_constK_ne_zero K)) (div_ne_zero ?_ ?_)
  · exact mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · exact gapsw80_t36_nK_cast_ne_zero K

set_option maxHeartbeats 3200000 in

theorem gapsw80_t36_tendsto_xi_rhs_one :
    Tendsto (fun s : ℂ ↦ s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
      (𝓝[≠] 1) (𝓝 (gapsw80_t36_xiResidueVal K)) := by
  have hsum : Tendsto (fun s : ℂ ↦
        ∑ C : ClassGroup (𝓞 K), ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
          * ((s - 1) * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
              ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 1) (𝓝 (∑ _C : ClassGroup (𝓞 K), (2 / (nK K : ℂ)))) :=
    tendsto_finset_sum _ (fun C _ ↦ gapsw80_t36_perClass_residue_one K C)
  have hs : Tendsto (fun s : ℂ ↦ s) (𝓝[≠] 1) (𝓝 (1:ℂ)) :=
    continuous_id.tendsto' 1 1 rfl |>.mono_left nhdsWithin_le_nhds
  have hG := (hsum.const_mul (gapsw80_t9_constK K)⁻¹).mul hs
  have hval : (gapsw80_t9_constK K)⁻¹
        * (∑ _C : ClassGroup (𝓞 K), (2 / (nK K : ℂ))) * 1
      = gapsw80_t36_xiResidueVal K := by
    rw [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    unfold gapsw80_t36_xiResidueVal; ring
  rw [← hval]
  refine hG.congr' (Eventually.of_forall fun s ↦ ?_)
  unfold gapsw80_t9_completedDedekindZeta
  have hsum_eq : ∑ C : ClassGroup (𝓞 K),
        ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s * ((s - 1)
          * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
              ((nK K : ℂ) * s / 2))
      = (s - 1) * ∑ C : ClassGroup (𝓞 K),
          ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
            * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
                ((nK K : ℂ) * s / 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun C _ ↦ by ring)
  rw [hsum_eq]; ring

set_option maxHeartbeats 3200000 in

theorem gapsw80_t36_tendsto_xi_rhs_zero :
    Tendsto (fun s : ℂ ↦ s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
      (𝓝[≠] 0) (𝓝 (gapsw80_t36_xiResidueVal K)) := by
  have hsum : Tendsto (fun s : ℂ ↦
        ∑ C : ClassGroup (𝓞 K), ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
          * (s * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
              ((nK K : ℂ) * s / 2)))
      (𝓝[≠] 0) (𝓝 (∑ _C : ClassGroup (𝓞 K), (-(2 / (nK K : ℂ))))) :=
    tendsto_finset_sum _ (fun C _ ↦ gapsw80_t36_perClass_residue_zero K C)
  have hs1 : Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 0) (𝓝 (-1:ℂ)) := by
    have := (continuous_sub_right (1:ℂ)).tendsto (0:ℂ)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hG := (hsum.const_mul (gapsw80_t9_constK K)⁻¹).mul hs1
  have hval : (gapsw80_t9_constK K)⁻¹
        * (∑ _C : ClassGroup (𝓞 K), (-(2 / (nK K : ℂ)))) * (-1)
      = gapsw80_t36_xiResidueVal K := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    unfold gapsw80_t36_xiResidueVal; ring
  rw [← hval]
  refine hG.congr' (Eventually.of_forall fun s ↦ ?_)
  unfold gapsw80_t9_completedDedekindZeta
  have hsum_eq : ∑ C : ClassGroup (𝓞 K),
        ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s * (s
          * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
              ((nK K : ℂ) * s / 2))
      = s * ∑ C : ClassGroup (𝓞 K),
          ((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s
            * (gapsw80_t7_heckeWeakFEPair K (gapsw80_t9_classRepr K C)).Λ
                ((nK K : ℂ) * s / 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun C _ ↦ by ring)
  rw [hsum_eq]; ring

set_option maxHeartbeats 3200000 in

theorem gapsw80_t36_D1app_closed : gapsw80_t32_XiEndpointNonvanishing := by
  have _em := Classical.em
  intro K _ _ ξ hdiff hagr

  have heq1 : (fun s ↦ s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
      =ᶠ[𝓝[≠] (1:ℂ)] ξ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
        (isOpen_ne.mem_nhds (one_ne_zero (α := ℂ))),
      self_mem_nhdsWithin] with s hs0 hs1
    exact (hagr s hs0 hs1).symm
  have heq0 : (fun s ↦ s * (s - 1) * gapsw80_t9_completedDedekindZeta K s)
      =ᶠ[𝓝[≠] (0:ℂ)] ξ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (zero_ne_one (α := ℂ)))]
      with s hs0 hs1
    exact (hagr s hs0 hs1).symm
  have hξ1 : ξ 1 = gapsw80_t36_xiResidueVal K :=
    tendsto_nhds_unique
      ((hdiff.continuous.tendsto 1).mono_left nhdsWithin_le_nhds)
      ((gapsw80_t36_tendsto_xi_rhs_one K).congr' heq1)
  have hξ0 : ξ 0 = gapsw80_t36_xiResidueVal K :=
    tendsto_nhds_unique
      ((hdiff.continuous.tendsto 0).mono_left nhdsWithin_le_nhds)
      ((gapsw80_t36_tendsto_xi_rhs_zero K).congr' heq0)
  exact ⟨hξ0 ▸ gapsw80_t36_xiResidueVal_ne_zero K, hξ1 ▸ gapsw80_t36_xiResidueVal_ne_zero K⟩

end FLT.Gapsw80T36D1appXiEndpointResidueProof
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace KwDyf2XiOrderBoundDecomp

open FLT.KwDyf2XiEntireOrderDecomp
open FLT.Gapsw80T9ClassSumA1Closure
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical"

theorem kwDyf2_norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  have _em := Classical.em
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs,
    Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

theorem kwDyf2_norm_le_norm_one_sub {s : ℂ} (hs : s.re ≤ 1/2) :
    ‖s‖ ≤ ‖1 - s‖ := by
  have h : ‖s‖^2 ≤ ‖1 - s‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, zero_sub, neg_mul_neg]
    nlinarith
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg s), Real.sqrt_sq (norm_nonneg (1 - s))] at this

theorem kwDyf2_norm_mul_log_norm_nonneg {s : ℂ} (hs : 2 ≤ ‖s‖) :
    0 ≤ ‖s‖ * Real.log ‖s‖ :=
  mul_nonneg (by linarith) (Real.log_nonneg (by linarith))

theorem kwDyf2_norm_one_sub_le {s : ℂ} (hs : 2 ≤ ‖s‖) :
    ‖1 - s‖ ≤ (3/2) * ‖s‖ :=
  calc ‖1 - s‖ ≤ ‖(1:ℂ)‖ + ‖s‖ := norm_sub_le 1 s
    _ = 1 + ‖s‖ := by rw [norm_one]
    _ ≤ (3/2) * ‖s‖ := by linarith

theorem kwDyf2_refl_growth_bound {s : ℂ} (hs : 2 ≤ ‖s‖) (hle : ‖s‖ ≤ ‖1 - s‖) :
    ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 3 * ‖s‖ * Real.log ‖s‖ := by
  have hlog2 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log two_pos hs
  have hlogpos : 0 < Real.log ‖s‖ :=
    lt_of_lt_of_le (Real.log_pos one_lt_two) hlog2
  have h32 : ‖1 - s‖ ≤ (3/2) * ‖s‖ := kwDyf2_norm_one_sub_le hs
  have h1spos : (0:ℝ) < ‖1 - s‖ := lt_of_lt_of_le two_pos (hs.trans hle)
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hlog : Real.log ‖1 - s‖ ≤ 2 * Real.log ‖s‖ := by
    calc Real.log ‖1 - s‖ ≤ Real.log ((3/2) * ‖s‖) :=
          Real.log_le_log h1spos h32
      _ = Real.log (3/2) + Real.log ‖s‖ :=
          Real.log_mul (by norm_num) hspos.ne'
      _ ≤ Real.log 2 + Real.log ‖s‖ := by
          have : Real.log (3/2) ≤ Real.log 2 :=
            Real.log_le_log (by norm_num) (by norm_num)
          linarith
      _ ≤ 2 * Real.log ‖s‖ := by linarith
  calc ‖1 - s‖ * Real.log ‖1 - s‖
      ≤ (3/2) * ‖s‖ * (2 * Real.log ‖s‖) := by
        refine mul_le_mul h32 hlog ?_ (by linarith)
        exact Real.log_nonneg (le_trans one_le_two (hs.trans hle))
    _ = 3 * ‖s‖ * Real.log ‖s‖ := by ring

def kwDyf2_XiHalfplaneBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 1/2 ≤ s.re → 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

theorem kwDyf2_C1_of_halfplane (hHalf : kwDyf2_XiHalfplaneBound) :
    kwDyf2_XiOrderBound := by
  have _em := Classical.em
  intro K _ _
  obtain ⟨C, hC⟩ := hHalf K
  refine ⟨3 * max C 0, fun s hs => ?_⟩
  have hsln : 0 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_norm_mul_log_norm_nonneg hs
  rcases le_or_gt (1/2 : ℝ) s.re with hre | hre
  ·
    calc Real.log ‖kwDyf2_xi K s‖
        ≤ C * ‖s‖ * Real.log ‖s‖ := hC s hre hs
      _ ≤ max C 0 * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; gcongr; exact le_max_left C 0
      _ ≤ 3 * max C 0 * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc (3 * max C 0)]
          gcongr
          nlinarith [le_max_right C 0]
  ·
    have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
    have hs1 : s ≠ 1 := fun h => by simp [h, Complex.one_re] at hre; linarith
    rw [← kwDyf2_sat_xi_FE K hs0 hs1]
    have h1re : 1/2 ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]; linarith
    have hle : ‖s‖ ≤ ‖1 - s‖ := kwDyf2_norm_le_norm_one_sub hre.le
    have h1norm : 2 ≤ ‖1 - s‖ := le_trans hs hle
    calc Real.log ‖kwDyf2_xi K (1 - s)‖
        ≤ C * ‖1 - s‖ * Real.log ‖1 - s‖ := hC (1 - s) h1re h1norm
      _ ≤ max C 0 * (‖1 - s‖ * Real.log ‖1 - s‖) := by
          rw [mul_assoc]; gcongr
          · exact kwDyf2_norm_mul_log_norm_nonneg h1norm
          · exact le_max_left C 0
      _ ≤ max C 0 * (3 * ‖s‖ * Real.log ‖s‖) :=
          mul_le_mul_of_nonneg_left (kwDyf2_refl_growth_bound hs hle)
            (le_max_right C 0)
      _ = 3 * max C 0 * ‖s‖ * Real.log ‖s‖ := by ring

def kwDyf2_XiRightHalfBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 3/2 ≤ s.re → 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

def kwDyf2_XiStripBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ C : ℝ, ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → 2 ≤ ‖s‖ →
      Real.log ‖kwDyf2_xi K s‖ ≤ C * ‖s‖ * Real.log ‖s‖

theorem kwDyf2_halfplane_of_C1a_C1b
    (hC1a : kwDyf2_XiRightHalfBound) (hC1b : kwDyf2_XiStripBound) :
    kwDyf2_XiHalfplaneBound := by
  have _em := Classical.em
  intro K _ _
  obtain ⟨Ca, hCa⟩ := hC1a K
  obtain ⟨Cb, hCb⟩ := hC1b K
  refine ⟨max (max Ca 0) (max Cb 0), fun s hre hs => ?_⟩
  have hsln : 0 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_norm_mul_log_norm_nonneg hs
  rcases le_or_gt (3/2 : ℝ) s.re with hre2 | hre2
  · calc Real.log ‖kwDyf2_xi K s‖ ≤ Ca * ‖s‖ * Real.log ‖s‖ := hCa s hre2 hs
      _ ≤ max (max Ca 0) (max Cb 0) * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; gcongr
          exact le_trans (le_max_left Ca 0) (le_max_left _ _)
  · calc Real.log ‖kwDyf2_xi K s‖ ≤ Cb * ‖s‖ * Real.log ‖s‖ := hCb s hre hre2.le hs
      _ ≤ max (max Ca 0) (max Cb 0) * ‖s‖ * Real.log ‖s‖ := by
          rw [mul_assoc, mul_assoc]; gcongr
          exact le_trans (le_max_left Cb 0) (le_max_right _ _)

set_option maxHeartbeats 3200000 in

theorem kwDyf2_C1_of_C1a_C1b
    (hC1a : kwDyf2_XiRightHalfBound) (hC1b : kwDyf2_XiStripBound) :
    kwDyf2_XiOrderBound :=
  kwDyf2_C1_of_halfplane (kwDyf2_halfplane_of_C1a_C1b hC1a hC1b)

end FLT.KwDyf2XiOrderBoundDecomp
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section AxiomAudits
open FLT.KwDyf2XiOrderBoundDecomp

end AxiomAudits
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace KwDyf2RealGammaLogBound

open FLT.KwDyf2XiOrderBoundDecomp
p2m_open "Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical Nat P2MW.S_NumberField_exists_completedDedekindZeta_package.Nat"

theorem kwDyf2_monotoneOn_mul_log : MonotoneOn (fun t => t * Real.log t) (Set.Ici 1) := by
  have _em := Classical.em
  intro a ha b hb hab
  exact mul_le_mul hab (Real.log_le_log (lt_of_lt_of_le one_pos ha) hab)
    (Real.log_nonneg ha) (le_trans (le_of_lt one_pos) hb)

theorem kwDyf2_log_factorial_le {n : ℕ} :
    Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  have _em := Classical.em
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · simp [h0]
  · calc Real.log (n ! : ℝ)
        ≤ Real.log ((n : ℝ) ^ n) := by
          refine Real.log_le_log (by exact_mod_cast n.factorial_pos) ?_
          exact_mod_cast Nat.factorial_le_pow n
      _ = (n : ℝ) * Real.log (n : ℝ) := by
          rw [Real.log_pow]

set_option maxHeartbeats 12800000 in

theorem kwDyf2_log_Gamma_le_self_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Real.log (Real.Gamma x) ≤ x * Real.log x := by
  have _em := Classical.em
  set n := ⌊x⌋₊ with hn_def
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (le_trans zero_le_one hx)
  have hxn1 : x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1

  have ha : 0 ≤ (n:ℝ) + 1 - x := by linarith
  have hb : 0 ≤ x - (n:ℝ) := by linarith
  have hab : ((n:ℝ) + 1 - x) + (x - (n:ℝ)) = 1 := by ring
  have hcomb : ((n:ℝ) + 1 - x) • (n : ℝ) + (x - (n:ℝ)) • ((n : ℝ) + 1) = x := by
    simp only [smul_eq_mul]; ring

  have hconv := Real.convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hnpos)
    (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < (n:ℝ) + 1)) ha hb hab
  rw [hcomb, Function.comp_apply, Function.comp_apply, Function.comp_apply,
    smul_eq_mul, smul_eq_mul] at hconv

  have hGn : Real.Gamma (n : ℝ) = ((n - 1)! : ℝ) := by
    have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hn1).symm
    rw [hcast]; exact_mod_cast Real.Gamma_nat_eq_factorial (n - 1)
  have hGn1 : Real.Gamma ((n : ℝ) + 1) = (n ! : ℝ) := by
    exact_mod_cast Real.Gamma_nat_eq_factorial n
  rw [hGn, hGn1] at hconv

  have hend1 : Real.log ((n - 1)! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    calc Real.log ((n - 1)! : ℝ)
        ≤ Real.log (n ! : ℝ) := by
          refine Real.log_le_log (by exact_mod_cast (n-1).factorial_pos) ?_
          exact_mod_cast Nat.factorial_le (Nat.sub_le n 1)
      _ ≤ (n : ℝ) * Real.log (n : ℝ) := kwDyf2_log_factorial_le
  have hend2 : Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    kwDyf2_log_factorial_le

  have hstep : Real.log (Real.Gamma x) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    calc Real.log (Real.Gamma x)
        ≤ ((n:ℝ)+1-x) * Real.log ((n - 1)! : ℝ)
            + (x-(n:ℝ)) * Real.log (n ! : ℝ) := hconv
      _ ≤ ((n:ℝ)+1-x) * ((n : ℝ) * Real.log (n : ℝ))
            + (x-(n:ℝ)) * ((n : ℝ) * Real.log (n : ℝ)) := by gcongr
      _ = (n : ℝ) * Real.log (n : ℝ) := by rw [← add_mul, hab, one_mul]

  exact hstep.trans (kwDyf2_monotoneOn_mul_log
    (Set.mem_Ici.mpr (by exact_mod_cast hn1)) (Set.mem_Ici.mpr hx) hnx)

theorem kwDyf2_log_norm_Gamma_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    Real.log ‖Complex.Gamma s‖ ≤ s.re * Real.log s.re := by
  have _em := Classical.em
  have hrepos : 0 < s.re := lt_of_lt_of_le one_pos hs
  have hΓ : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re :=
    kwDyf2_norm_Gamma_le_Gamma_re hrepos
  have hΓne : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have : s.re = (-(m:ℂ)).re := by rw [hm]
    simp only [Complex.neg_re, Complex.natCast_re] at this
    linarith
  calc Real.log ‖Complex.Gamma s‖
      ≤ Real.log (Real.Gamma s.re) :=
        Real.log_le_log (norm_pos_iff.mpr hΓne) hΓ
    _ ≤ s.re * Real.log s.re := kwDyf2_log_Gamma_le_self_mul_log hs

theorem kwDyf2_log_norm_Gamma_le_norm_mul_log_norm {s : ℂ}
    (hs : 1 ≤ s.re) :
    Real.log ‖Complex.Gamma s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have _em := Classical.em
  have hre_norm : s.re ≤ ‖s‖ := Complex.re_le_norm s
  exact (kwDyf2_log_norm_Gamma_le_re hs).trans
    (kwDyf2_monotoneOn_mul_log (Set.mem_Ici.mpr hs)
      (Set.mem_Ici.mpr (le_trans hs hre_norm)) hre_norm)

end FLT.KwDyf2RealGammaLogBound
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section AxiomAudits
open FLT.KwDyf2RealGammaLogBound

end AxiomAudits
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace KwDyf2XiStripBoundAttack

open FLT.KwDyf2XiEntireOrderDecomp
open FLT.KwDyf2XiOrderBoundDecomp
open FLT.Gapsw80T15XiOrderOneB1Decomp
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T3IdealLatticeThetaTransformation
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical"

theorem kwDyf2_rpow_le_endpoints {t a b σ : ℝ} (ht : 0 < t)
    (ha : a ≤ σ) (hb : σ ≤ b) : t ^ σ ≤ t ^ a + t ^ b := by
  have _em := Classical.em
  have hta : (0:ℝ) ≤ t ^ a := Real.rpow_nonneg ht.le a
  have htb : (0:ℝ) ≤ t ^ b := Real.rpow_nonneg ht.le b
  rcases le_total t 1 with h1 | h1
  · exact le_add_of_le_of_nonneg
      (Real.rpow_le_rpow_of_exponent_ge ht h1 ha) htb
  · exact le_add_of_nonneg_of_le hta
      (Real.rpow_le_rpow_of_exponent_le h1 hb)

section Λ₀Bound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def kwDyf2_MellinNormBound (P : WeakFEPair E) (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), ‖(t : ℂ) ^ ((x:ℂ) - 1) • P.f_modif t‖

omit [CompleteSpace E] in

theorem kwDyf2_MellinNormBound_integrable (P : WeakFEPair E) (x : ℝ) :
    IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((x:ℂ) - 1) • P.f_modif t‖)
      (Set.Ioi (0:ℝ)) :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin (x:ℂ)).1.norm

omit [CompleteSpace E] in

theorem kwDyf2_MellinNormBound_nonneg (P : WeakFEPair E) (x : ℝ) :
    0 ≤ kwDyf2_MellinNormBound P x :=
  integral_nonneg (fun _ => norm_nonneg _)

omit [CompleteSpace E] in
set_option maxHeartbeats 6400000 in

theorem kwDyf2_norm_Λ₀_le (P : WeakFEPair E) {s : ℂ} {a b : ℝ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖P.Λ₀ s‖ ≤ kwDyf2_MellinNormBound P a + kwDyf2_MellinNormBound P b := by
  have _em := Classical.em

  show ‖mellin P.f_modif s‖ ≤ _
  unfold mellin

  refine (norm_integral_le_integral_norm _).trans ?_

  have hint_a := kwDyf2_MellinNormBound_integrable P a
  have hint_b := kwDyf2_MellinNormBound_integrable P b
  rw [show kwDyf2_MellinNormBound P a + kwDyf2_MellinNormBound P b
        = ∫ t in Set.Ioi (0:ℝ),
            (‖(t:ℂ)^((a:ℂ)-1) • P.f_modif t‖ + ‖(t:ℂ)^((b:ℂ)-1) • P.f_modif t‖)
      from (integral_add hint_a hint_b).symm]
  refine setIntegral_mono_on (P.isStrongFEPair_toStrongFEPair.hasMellin s).1.norm
    (hint_a.add hint_b) measurableSet_Ioi (fun t ht => ?_)

  have htpos : (0:ℝ) < t := ht
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos,
    Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right
    (kwDyf2_rpow_le_endpoints htpos (by linarith) (by linarith)) (norm_nonneg _)

end Λ₀Bound
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

variable (K : Type) [Field K] [NumberField K]

noncomputable def kwDyf2_Bconst (C : ClassGroup (𝓞 K)) : ℝ :=
  (gapsw80_t9_covolRepr K C ^ (1/2 : ℝ) + gapsw80_t9_covolRepr K C ^ (3/2 : ℝ))
    * ((3/2) * (kwDyf2_MellinNormBound (kwDyf2_P K C) ((nK K : ℝ)/4)
                  + kwDyf2_MellinNormBound (kwDyf2_P K C) ((3 * nK K : ℝ)/4))
        + 3 / (nK K : ℝ) + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ))

set_option maxHeartbeats 12800000 in

theorem kwDyf2_norm_xiSummand_le (C : ClassGroup (𝓞 K)) {s : ℂ}
    (hre1 : 1/2 ≤ s.re) (hre2 : s.re ≤ 3/2) (hs : 2 ≤ ‖s‖) :
    ‖kwDyf2_xiSummand K C s‖ ≤ kwDyf2_Bconst K C * ‖s‖^2 := by
  have _em := Classical.em
  have hnK : (0:ℝ) < (nK K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < nK K)
  have hcov := gapsw80_t9_covolRepr_pos K C
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hs1 : ‖s - 1‖ ≤ (3/2) * ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + 1 := by
          have := norm_sub_le s 1; rwa [norm_one] at this
      _ ≤ (3/2) * ‖s‖ := by linarith
  have hsle : ‖s‖ ≤ ‖s‖^2 := by nlinarith

  have hcovpow : ‖((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s‖
      ≤ gapsw80_t9_covolRepr K C ^ (1/2:ℝ) + gapsw80_t9_covolRepr K C ^ (3/2:ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcov]
    exact kwDyf2_rpow_le_endpoints hcov hre1 hre2

  have hre_ns : ((nK K : ℂ) * s / 2).re = (nK K : ℝ) * s.re / 2 := by
    simp [Complex.mul_re]
  have hL0 : ‖(kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)‖
      ≤ kwDyf2_MellinNormBound (kwDyf2_P K C) ((nK K : ℝ)/4)
        + kwDyf2_MellinNormBound (kwDyf2_P K C) ((3 * nK K : ℝ)/4) := by
    refine kwDyf2_norm_Λ₀_le (kwDyf2_P K C) ?_ ?_
    · rw [hre_ns]; nlinarith
    · rw [hre_ns]; nlinarith
  set Msum := kwDyf2_MellinNormBound (kwDyf2_P K C) ((nK K : ℝ)/4)
              + kwDyf2_MellinNormBound (kwDyf2_P K C) ((3 * nK K : ℝ)/4)
  have hMsum_nn : 0 ≤ Msum :=
    add_nonneg (kwDyf2_MellinNormBound_nonneg _ _) (kwDyf2_MellinNormBound_nonneg _ _)

  have hbracket :
      ‖s * (s - 1) * (kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)
        - 2 * (s - 1) / (nK K : ℂ) + 2 * s * (kwDyf2_P K C).ε / (nK K : ℂ)‖
      ≤ ((3/2) * Msum + 3 / (nK K : ℝ) + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ)) * ‖s‖^2 := by
    have hnorm_nK : ‖(nK K : ℂ)‖ = (nK K : ℝ) := by
      rw [show ((nK K : ℕ) : ℂ) = ((nK K : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg hnK.le]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) (le_refl _)).trans ?_
    have h1 : ‖s * (s - 1) * (kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)‖
        ≤ (3/2) * Msum * ‖s‖^2 := by
      rw [norm_mul, norm_mul]
      calc ‖s‖ * ‖s - 1‖ * ‖(kwDyf2_P K C).Λ₀ ((nK K : ℂ) * s / 2)‖
          ≤ ‖s‖ * ((3/2)*‖s‖) * Msum := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)) hL0
              (norm_nonneg _) ?_
            positivity
        _ = (3/2) * Msum * ‖s‖^2 := by ring
    have h2 : ‖2 * (s - 1) / (nK K : ℂ)‖ ≤ 3 / (nK K : ℝ) * ‖s‖^2 := by
      rw [norm_div, norm_mul, hnorm_nK, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
      calc 2 * ‖s - 1‖ / (nK K : ℝ)
          ≤ 2 * ((3/2)*‖s‖) / (nK K : ℝ) := by gcongr
        _ = 3 * ‖s‖ / (nK K : ℝ) := by ring
        _ ≤ 3 * ‖s‖^2 / (nK K : ℝ) := by gcongr
        _ = 3 / (nK K : ℝ) * ‖s‖^2 := by ring
    have h3 : ‖2 * s * (kwDyf2_P K C).ε / (nK K : ℂ)‖
        ≤ 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by
      rw [norm_div, norm_mul, norm_mul, hnorm_nK, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
      calc 2 * ‖s‖ * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ)
          ≤ 3 * ‖s‖^2 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ) := by
            gcongr; nlinarith [norm_nonneg s]
        _ = 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by ring
    calc _ ≤ (3/2) * Msum * ‖s‖^2 + 3 / (nK K : ℝ) * ‖s‖^2
              + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ) * ‖s‖^2 := by
          gcongr
      _ = ((3/2) * Msum + 3 / (nK K : ℝ) + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ)) * ‖s‖^2 := by
          ring

  unfold kwDyf2_xiSummand kwDyf2_Bconst
  rw [norm_mul]
  calc ‖((gapsw80_t9_covolRepr K C : ℝ) : ℂ) ^ s‖ * ‖_‖
      ≤ (gapsw80_t9_covolRepr K C ^ (1/2:ℝ) + gapsw80_t9_covolRepr K C ^ (3/2:ℝ))
          * (((3/2) * Msum + 3 / (nK K : ℝ)
              + 3 * ‖(kwDyf2_P K C).ε‖ / (nK K : ℝ)) * ‖s‖^2) :=
        mul_le_mul hcovpow hbracket (norm_nonneg _)
          (add_nonneg (Real.rpow_nonneg hcov.le _) (Real.rpow_nonneg hcov.le _))
    _ = _ := by ring

noncomputable def kwDyf2_Aconst : ℝ :=
  max 1 (‖(gapsw80_t9_constK K)⁻¹‖ * ∑ C : ClassGroup (𝓞 K), kwDyf2_Bconst K C)

theorem kwDyf2_one_le_Aconst : 1 ≤ kwDyf2_Aconst K := le_max_left _ _

set_option maxHeartbeats 6400000 in

theorem kwDyf2_norm_xi_le_Aconst_sq {s : ℂ}
    (hre1 : 1/2 ≤ s.re) (hre2 : s.re ≤ 3/2) (hs : 2 ≤ ‖s‖) :
    ‖kwDyf2_xi K s‖ ≤ kwDyf2_Aconst K * ‖s‖^2 := by
  have _em := Classical.em
  unfold kwDyf2_xi
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left
    ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun C _ =>
      kwDyf2_norm_xiSummand_le K C hre1 hre2 hs))) (norm_nonneg _)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

theorem kwDyf2_one_le_norm_mul_log {s : ℂ} (hs : 2 ≤ ‖s‖) :
    1 ≤ ‖s‖ * Real.log ‖s‖ := by
  have hlog2 : (1:ℝ) ≤ 2 * Real.log 2 := by
    have h : Real.log 2 ≥ 1/2 := by
      have := Real.add_one_le_exp (1/2 : ℝ)
      have hx : Real.exp (1/2) ≤ 2 := by
        have h2 : Real.exp (1/2) * Real.exp (1/2) ≤ 2 * 2 := by
          rw [← Real.exp_add]; norm_num
          exact le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))
        nlinarith [Real.exp_pos (1/2 : ℝ)]
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num),
                (Real.le_log_iff_exp_le two_pos).mpr hx]
    linarith
  calc (1:ℝ) ≤ 2 * Real.log 2 := hlog2
    _ ≤ ‖s‖ * Real.log ‖s‖ :=
        mul_le_mul hs (Real.log_le_log two_pos hs)
          (Real.log_nonneg one_le_two) (by linarith)

set_option maxHeartbeats 6400000 in

theorem kwDyf2_xiStripBound_proved : kwDyf2_XiStripBound := by
  have _em := Classical.em
  intro K _ _
  refine ⟨Real.log (kwDyf2_Aconst K) + 2, fun s hre1 hre2 hs => ?_⟩
  have hAK1 : 1 ≤ kwDyf2_Aconst K := kwDyf2_one_le_Aconst K
  have hAKpos : 0 < kwDyf2_Aconst K := lt_of_lt_of_le one_pos hAK1
  have hlogA : 0 ≤ Real.log (kwDyf2_Aconst K) := Real.log_nonneg hAK1
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hs
  have hAs2 : 1 ≤ kwDyf2_Aconst K * ‖s‖^2 := by nlinarith
  have hlogAs2 : 0 ≤ Real.log (kwDyf2_Aconst K * ‖s‖^2) := Real.log_nonneg hAs2
  have hbnd : ‖kwDyf2_xi K s‖ ≤ kwDyf2_Aconst K * ‖s‖^2 :=
    kwDyf2_norm_xi_le_Aconst_sq K hre1 hre2 hs

  have hstep1 : Real.log ‖kwDyf2_xi K s‖ ≤ Real.log (kwDyf2_Aconst K * ‖s‖^2) := by
    rcases eq_or_lt_of_le (norm_nonneg (kwDyf2_xi K s)) with h0 | h0
    · rw [← h0, Real.log_zero]; exact hlogAs2
    · exact Real.log_le_log h0 hbnd

  have hsplit : Real.log (kwDyf2_Aconst K * ‖s‖^2)
      = Real.log (kwDyf2_Aconst K) + 2 * Real.log ‖s‖ := by
    rw [Real.log_mul hAKpos.ne' (by positivity), Real.log_pow]; ring
  have hnl := kwDyf2_one_le_norm_mul_log hs
  have hlogs : Real.log ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
    nlinarith [Real.log_nonneg (le_trans one_le_two hs)]
  calc Real.log ‖kwDyf2_xi K s‖
      ≤ Real.log (kwDyf2_Aconst K) + 2 * Real.log ‖s‖ := by
        rw [← hsplit]; exact hstep1
    _ ≤ Real.log (kwDyf2_Aconst K) * (‖s‖ * Real.log ‖s‖)
          + 2 * (‖s‖ * Real.log ‖s‖) := by
        gcongr
        calc Real.log (kwDyf2_Aconst K)
            = Real.log (kwDyf2_Aconst K) * 1 := (mul_one _).symm
          _ ≤ Real.log (kwDyf2_Aconst K) * (‖s‖ * Real.log ‖s‖) :=
              mul_le_mul_of_nonneg_left hnl hlogA
    _ = (Real.log (kwDyf2_Aconst K) + 2) * ‖s‖ * Real.log ‖s‖ := by ring

set_option maxHeartbeats 3200000 in

theorem kwDyf2_B1_of_C1a (hC1a : kwDyf2_XiRightHalfBound) :
    gapsw80_t11_XiOrderOneHadamard :=
  kwDyf2_B1_of_C1 (kwDyf2_C1_of_C1a_C1b hC1a kwDyf2_xiStripBound_proved)

end FLT.KwDyf2XiStripBoundAttack
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section AxiomAudits
open FLT.KwDyf2XiStripBoundAttack

end AxiomAudits
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T16XiRightHalfBoundProof

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real"
open FLT.Gapsw80T8MellinGammaPartialZeta FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T15XiOrderOneB1Decomp FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.KwDyf2XiEntireOrderDecomp FLT.KwDyf2XiOrderBoundDecomp
open FLT.KwDyf2XiStripBoundAttack FLT.KwDyf2RealGammaLogBound
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical nonZeroDivisors"

variable (K : Type) [Field K] [NumberField K]

theorem gapsw80_t16_re_div_two (z : ℂ) : (z / 2).re = z.re / 2 := by
  rw [Complex.div_re]; simp [Complex.normSq_ofNat]; ring

theorem gapsw80_t16_one_le_abs_discr : (1:ℝ) ≤ |(discr K : ℝ)| := by
  have h : (0:ℤ) < |discr K| := abs_pos.mpr (NumberField.discr_ne_zero K)
  have h1 : (1:ℤ) ≤ |discr K| := h
  calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_cast
    _ ≤ (|discr K| : ℝ) := by exact_mod_cast h1
    _ = |(discr K : ℝ)| := by push_cast; rfl

theorem gapsw80_t16_Gammaℂ_ne_zero {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_)
    (Complex.Gamma_ne_zero (fun m hm => by
      have : s.re = (-(m:ℂ)).re := by rw [hm]
      simp at this; linarith))
  refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
  exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

noncomputable def gapsw80_t16_zetaCoeff (n : ℕ) : ℂ :=
  (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)

noncomputable def gapsw80_t16_Mzeta : ℝ :=
  ∑' n, ‖LSeries.term (gapsw80_t16_zetaCoeff K) ((3/2 : ℝ) : ℂ) n‖

theorem gapsw80_t16_Mzeta_summable :
    Summable (fun n => ‖LSeries.term (gapsw80_t16_zetaCoeff K) ((3/2 : ℝ) : ℂ) n‖) :=
  (gapsw80_t10_LSeriesSummable_dedekindZeta K
    (s := ((3/2 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; norm_num)).norm

theorem gapsw80_t16_term_norm_le {s : ℂ} (hs : 3/2 ≤ s.re) (n : ℕ) :
    ‖LSeries.term (gapsw80_t16_zetaCoeff K) s n‖
      ≤ ‖LSeries.term (gapsw80_t16_zetaCoeff K) ((3/2 : ℝ) : ℂ) n‖ := by
  have _em := Classical.em
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [LSeries.term_zero]
  · have hn1 : 1 ≤ (n:ℝ) := Nat.one_le_cast.mpr hpos
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hpos.ne', if_neg hpos.ne',
      Complex.ofReal_re]
    exact div_le_div_of_nonneg_left (norm_nonneg _)
      (Real.rpow_pos_of_pos (by exact_mod_cast hpos) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 hs)

theorem gapsw80_t16_norm_sum_partialZeta_le {s : ℂ} (hs : 3/2 ≤ s.re) :
    ‖∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s‖
      ≤ gapsw80_t16_Mzeta K := by
  have _em := Classical.em
  have h1 : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  rw [gapsw80_t10_sum_partialDedekindZeta_eq K h1]

  have hsum := (gapsw80_t16_Mzeta_summable K).of_nonneg_of_le
    (fun _ => norm_nonneg _) (gapsw80_t16_term_norm_le K hs)
  unfold NumberField.dedekindZeta
  calc ‖LSeries _ s‖
      ≤ ∑' n, ‖LSeries.term (gapsw80_t16_zetaCoeff K) s n‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ gapsw80_t16_Mzeta K :=
        hasSum_le (gapsw80_t16_term_norm_le K hs) hsum.hasSum
          (gapsw80_t16_Mzeta_summable K).hasSum

theorem gapsw80_t16_log_norm_Gamma_half_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gamma (s / 2)‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have _em := Classical.em
  have hspos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le two_pos hns
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_one_le_norm_mul_log hns
  have hshalf_norm : ‖s / 2‖ = ‖s‖ / 2 := by
    rw [norm_div]; simp
  rcases le_or_gt 2 s.re with hge2 | hlt2
  ·
    have hre : 1 ≤ (s / 2).re := by
      rw [gapsw80_t16_re_div_two]; linarith
    have hstep := kwDyf2_log_norm_Gamma_le_norm_mul_log_norm hre
    refine hstep.trans ?_
    rw [hshalf_norm]
    have hhalf : ‖s‖ / 2 ≤ ‖s‖ := by linarith
    have hh1 : 1 ≤ ‖s‖ / 2 := by linarith
    exact kwDyf2_monotoneOn_mul_log (Set.mem_Ici.mpr hh1)
      (Set.mem_Ici.mpr (by linarith)) hhalf
  ·
    have hshalf_ne : s / 2 ≠ 0 := by
      intro h; rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact (gapsw80_t15_norm_ge_two_ne_zero_one hns).1 h
      · exact two_ne_zero h
    have hshift : Complex.Gamma (s / 2) = Complex.Gamma (s / 2 + 1) / (s / 2) := by
      rw [eq_div_iff hshalf_ne, mul_comm (Complex.Gamma (s/2)) (s/2),
          Complex.Gamma_add_one (s / 2) hshalf_ne]
    have hre1 : 1 ≤ (s / 2 + 1).re := by
      rw [Complex.add_re, Complex.one_re, gapsw80_t16_re_div_two]; linarith
    have hnorm1 : ‖s / 2 + 1‖ ≤ ‖s‖ := by
      calc ‖s / 2 + 1‖ ≤ ‖s / 2‖ + 1 := by
            have := norm_add_le (s/2) 1; rwa [norm_one] at this
        _ = ‖s‖ / 2 + 1 := by rw [hshalf_norm]
        _ ≤ ‖s‖ := by linarith
    have h1le1 : 1 ≤ ‖s / 2 + 1‖ :=
      le_trans (by exact_mod_cast hre1) (Complex.re_le_norm _)
    have hlogG1 : Real.log ‖Complex.Gamma (s / 2 + 1)‖
        ≤ ‖s / 2 + 1‖ * Real.log ‖s / 2 + 1‖ :=
      kwDyf2_log_norm_Gamma_le_norm_mul_log_norm hre1
    have hlogG1' : Real.log ‖Complex.Gamma (s / 2 + 1)‖ ≤ ‖s‖ * Real.log ‖s‖ :=
      hlogG1.trans (kwDyf2_monotoneOn_mul_log (Set.mem_Ici.mpr h1le1)
        (Set.mem_Ici.mpr (by linarith)) hnorm1)

    have h1shalf : (1:ℝ) ≤ ‖s / 2‖ := by rw [hshalf_norm]; linarith
    have hlogs2 : -Real.log ‖s / 2‖ ≤ 0 :=
      neg_nonpos_of_nonneg (Real.log_nonneg h1shalf)
    rw [hshift, norm_div, Real.log_div
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (fun m hm => by
        have : (s/2+1).re = (-(m:ℂ)).re := by rw [hm]
        simp at this; linarith)))
      (by rw [hshalf_norm]; positivity)]
    linarith [hlogG1', hlogs2]

theorem gapsw80_t16_log_norm_Gammaℝ_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gammaℝ s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
  have _em := Classical.em
  have hπ : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-s.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      gapsw80_t16_re_div_two, Complex.neg_re]
  have hπle : Real.log ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ ≤ 0 := by
    rw [hπ, Real.log_rpow Real.pi_pos]
    have hlogπ : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (one_le_two.trans Real.two_le_pi)
    nlinarith
  rw [Complex.Gammaℝ_def, norm_mul,
    Real.log_mul (by rw [hπ]; positivity)
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (fun m hm => by
        have : (s/2).re = (-(m:ℂ)).re := by rw [hm]
        simp at this; linarith)))]
  linarith [gapsw80_t16_log_norm_Gamma_half_le h32 hns, hπle]

theorem gapsw80_t16_log_norm_Gammaℂ_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖Complex.Gammaℂ s‖ ≤ 2 * (‖s‖ * Real.log ‖s‖) := by
  have _em := Classical.em
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_one_le_norm_mul_log hns
  have hre1 : 1 ≤ s.re := by linarith
  have hΓ := kwDyf2_log_norm_Gamma_le_norm_mul_log_norm hre1
  have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
  have h2πpos : (0:ℝ) < 2 * Real.pi := by positivity
  have hpow : ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ (-s.re) := by
    have : ((2 * (↑Real.pi : ℂ)) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos h2πpos, Complex.neg_re]
  have hpow_le : Real.log ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ ≤ 0 := by
    rw [hpow, Real.log_rpow h2πpos]
    have hlog2π : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by linarith [Real.two_le_pi])
    nlinarith
  have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (fun m hm => by
    have : s.re = (-(m:ℂ)).re := by rw [hm]
    simp at this; linarith)
  have hpow_ne : ‖(2 * (↑Real.pi : ℂ)) ^ (-s)‖ ≠ 0 := by rw [hpow]; positivity
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (by simp) hpow_ne) (norm_ne_zero_iff.mpr hΓne),
    Real.log_mul (by simp) hpow_ne]
  have hlog2' : Real.log ‖(2:ℂ)‖ = Real.log 2 := by simp
  linarith [hΓ, hpow_le, h1nml, hlog2]

noncomputable def gapsw80_t16_CGamma : ℝ :=
  (nrRealPlaces K : ℝ) + 2 * (nrComplexPlaces K : ℝ)

theorem gapsw80_t16_log_norm_gammaFactor_le {s : ℂ} (h32 : 3/2 ≤ s.re)
    (hns : 2 ≤ ‖s‖) :
    Real.log ‖gapsw80_t9_gammaFactor K s‖
      ≤ gapsw80_t16_CGamma K * (‖s‖ * Real.log ‖s‖) := by
  have _em := Classical.em
  have hnml : 0 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_norm_mul_log_norm_nonneg hns
  have hRne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hCne : Complex.Gammaℂ s ≠ 0 := gapsw80_t16_Gammaℂ_ne_zero (by linarith)
  unfold gapsw80_t9_gammaFactor gapsw80_t16_CGamma
  rw [norm_mul, norm_pow, norm_pow,
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hRne))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hCne)),
    Real.log_pow, Real.log_pow]
  have hR := gapsw80_t16_log_norm_Gammaℝ_le h32 hns
  have hC := gapsw80_t16_log_norm_Gammaℂ_le h32 hns
  have hRn : (nrRealPlaces K : ℝ) * Real.log ‖Complex.Gammaℝ s‖
      ≤ (nrRealPlaces K : ℝ) * (‖s‖ * Real.log ‖s‖) :=
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  have hCn : (nrComplexPlaces K : ℝ) * Real.log ‖Complex.Gammaℂ s‖
      ≤ (nrComplexPlaces K : ℝ) * (2 * (‖s‖ * Real.log ‖s‖)) :=
    mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _)
  linarith

noncomputable def gapsw80_t16_CDisc : ℝ :=
  Real.log |(discr K : ℝ)| / (2 * Real.log 2)

theorem gapsw80_t16_log_norm_discrPow_le {s : ℂ} (hns : 2 ≤ ‖s‖) :
    Real.log ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖
      ≤ gapsw80_t16_CDisc K * (‖s‖ * Real.log ‖s‖) := by
  have _em := Classical.em
  have hD1 : (1:ℝ) ≤ |(discr K : ℝ)| := gapsw80_t16_one_le_abs_discr K
  have hDpos : (0:ℝ) < |(discr K : ℝ)| := lt_of_lt_of_le one_pos hD1
  have hlogD : 0 ≤ Real.log |(discr K : ℝ)| := Real.log_nonneg hD1
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlogn2 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log two_pos hns
  have hsre : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hnspos : (0:ℝ) ≤ ‖s‖ := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hDpos),
    Real.log_rpow (by exact_mod_cast hDpos), gapsw80_t16_re_div_two]
  unfold gapsw80_t16_CDisc
  have hkey : s.re * Real.log 2 * Real.log |(discr K : ℝ)|
      ≤ Real.log |(discr K : ℝ)| * (‖s‖ * Real.log ‖s‖) := by
    have := mul_le_mul hsre hlogn2 hlog2.le hnspos
    nlinarith
  calc s.re / 2 * Real.log |(discr K : ℝ)|
      = s.re * Real.log 2 * Real.log |(discr K : ℝ)| / (2 * Real.log 2) := by
        field_simp
  _ ≤ Real.log |(discr K : ℝ)| * (‖s‖ * Real.log ‖s‖) / (2 * Real.log 2) := by
        gcongr
  _ = Real.log |(discr K : ℝ)| / (2 * Real.log 2) * (‖s‖ * Real.log ‖s‖) := by ring

noncomputable def gapsw80_t16_Cassem : ℝ :=
  max (2 + gapsw80_t16_CDisc K + gapsw80_t16_CGamma K
    + max (Real.log (gapsw80_t16_Mzeta K)) 0) 0

theorem gapsw80_t16_Cassem_nonneg : 0 ≤ gapsw80_t16_Cassem K := le_max_right _ _

theorem gapsw80_t16_xiRightHalfBound_proved : kwDyf2_XiRightHalfBound := by
  have _em := Classical.em
  intro K _ _
  refine ⟨gapsw80_t16_Cassem K, fun s h32 hns => ?_⟩
  have hnml : 0 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_norm_mul_log_norm_nonneg hns
  have h1nml : 1 ≤ ‖s‖ * Real.log ‖s‖ := kwDyf2_one_le_norm_mul_log hns
  have hCnn : 0 ≤ gapsw80_t16_Cassem K := gapsw80_t16_Cassem_nonneg K

  by_cases hξ0 : kwDyf2_xi K s = 0
  · rw [hξ0, norm_zero, Real.log_zero]
    exact mul_nonneg (mul_nonneg hCnn (by linarith)) (Real.log_nonneg (by linarith))

  have h1 : 1 < s.re := lt_of_lt_of_le (by norm_num) h32
  obtain ⟨hs0, hs1⟩ := gapsw80_t15_norm_ge_two_ne_zero_one hns
  rw [kwDyf2_xi_eq K hs0 hs1, gapsw80_t9_completedDedekindZeta_eq_sum K h1]

  have hsumne : ∑ C : ClassGroup (𝓞 K), gapsw80_t8_partialDedekindZeta K C s ≠ 0 := by
    intro habs
    apply hξ0
    rw [kwDyf2_xi_eq K hs0 hs1, gapsw80_t9_completedDedekindZeta_eq_sum K h1, habs]
    ring
  have hpoly_pos : (0:ℝ) < ‖s * (s - 1)‖ := by
    rw [norm_mul]
    exact mul_pos (norm_pos_iff.mpr hs0) (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))
  have hD1 : (1:ℝ) ≤ |(discr K : ℝ)| := gapsw80_t16_one_le_abs_discr K
  have hDpow_pos : (0:ℝ) < ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast lt_of_lt_of_le one_pos hD1)]
    positivity
  have hGamma_pos : (0:ℝ) < ‖gapsw80_t9_gammaFactor K s‖ := by
    unfold gapsw80_t9_gammaFactor
    rw [norm_mul, norm_pow, norm_pow]
    refine mul_pos (pow_pos ?_ _) (pow_pos ?_ _)
    · exact norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
    · exact norm_pos_iff.mpr (gapsw80_t16_Gammaℂ_ne_zero (by linarith))
  have hsum_pos : (0:ℝ) < ‖∑ C, gapsw80_t8_partialDedekindZeta K C s‖ :=
    norm_pos_iff.mpr hsumne

  rw [show s * (s - 1) * (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * gapsw80_t9_gammaFactor K s
        * ∑ C, gapsw80_t8_partialDedekindZeta K C s)
      = (s * (s - 1)) * (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2))
        * (gapsw80_t9_gammaFactor K s)
        * (∑ C, gapsw80_t8_partialDedekindZeta K C s) from by ring,
    norm_mul, norm_mul, norm_mul,
    Real.log_mul (by positivity) hsum_pos.ne',
    Real.log_mul (by positivity) hGamma_pos.ne',
    Real.log_mul hpoly_pos.ne' hDpow_pos.ne']

  have bPoly := gapsw80_t15_sat_polynomialFactor_orderBound s hns
  have bDisc := gapsw80_t16_log_norm_discrPow_le K hns
  have bGamma := gapsw80_t16_log_norm_gammaFactor_le K h32 hns
  have bZeta : Real.log ‖∑ C, gapsw80_t8_partialDedekindZeta K C s‖
      ≤ max (Real.log (gapsw80_t16_Mzeta K)) 0 * (‖s‖ * Real.log ‖s‖) := by
    have h := gapsw80_t16_norm_sum_partialZeta_le K h32
    calc Real.log ‖∑ C, gapsw80_t8_partialDedekindZeta K C s‖
        ≤ Real.log (gapsw80_t16_Mzeta K) :=
          Real.log_le_log hsum_pos h
      _ ≤ max (Real.log (gapsw80_t16_Mzeta K)) 0 := le_max_left _ _
      _ = max (Real.log (gapsw80_t16_Mzeta K)) 0 * 1 := (mul_one _).symm
      _ ≤ max (Real.log (gapsw80_t16_Mzeta K)) 0 * (‖s‖ * Real.log ‖s‖) :=
          mul_le_mul_of_nonneg_left h1nml (le_max_right _ _)
  have hCexp : gapsw80_t16_Cassem K
      ≥ 2 + gapsw80_t16_CDisc K + gapsw80_t16_CGamma K
        + max (Real.log (gapsw80_t16_Mzeta K)) 0 := le_max_left _ _
  calc Real.log ‖s * (s - 1)‖ + Real.log ‖((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)‖
        + Real.log ‖gapsw80_t9_gammaFactor K s‖
        + Real.log ‖∑ C, gapsw80_t8_partialDedekindZeta K C s‖
      ≤ 2 * ‖s‖ * Real.log ‖s‖
        + gapsw80_t16_CDisc K * (‖s‖ * Real.log ‖s‖)
        + gapsw80_t16_CGamma K * (‖s‖ * Real.log ‖s‖)
        + max (Real.log (gapsw80_t16_Mzeta K)) 0 * (‖s‖ * Real.log ‖s‖) := by
        linarith [bPoly, bDisc, bGamma, bZeta]
    _ = (2 + gapsw80_t16_CDisc K + gapsw80_t16_CGamma K
          + max (Real.log (gapsw80_t16_Mzeta K)) 0) * (‖s‖ * Real.log ‖s‖) := by ring
    _ ≤ gapsw80_t16_Cassem K * (‖s‖ * Real.log ‖s‖) :=
        mul_le_mul_of_nonneg_right hCexp hnml
    _ = gapsw80_t16_Cassem K * ‖s‖ * Real.log ‖s‖ := by ring

theorem gapsw80_t16_B1_closed : gapsw80_t11_XiOrderOneHadamard :=
  kwDyf2_B1_of_C1a gapsw80_t16_xiRightHalfBound_proved

end FLT.Gapsw80T16XiRightHalfBoundProof
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

set_option maxHeartbeats 6400000

namespace FLT
namespace Gapsw80T43CompletedZetaRealSuperlinearProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T16XiRightHalfBoundProof
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T30D2d0cLocalEulerFactorProof
open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp
open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof
p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real Nat P2MW.S_NumberField_exists_completedDedekindZeta_package.Nat Filter.Nat Set.Nat"

noncomputable def gapsw80_t43_L₀ : ℝ := 1 + 2 * Real.log (2 * Real.pi)

theorem gapsw80_t43_one_le_norm_discrPow (K : Type) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (1:ℝ) ≤ ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ := by
  rw [gapsw80_t10_discrCoercion,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le one_pos (gapsw80_t16_one_le_abs_discr K))]
  have hre : ((σ:ℂ) / 2).re = σ / 2 := by
    simp [Complex.ofReal_div, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  exact Real.one_le_rpow (gapsw80_t16_one_le_abs_discr K) (by linarith)

theorem gapsw80_t43_norm_Gamma_nat_succ (n : ℕ) :
    ‖Complex.Gamma ((n + 1 : ℕ) : ℂ)‖ = (n ! : ℝ) := by
  rw [show (((n + 1 : ℕ) : ℂ)) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
    show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  exact abs_of_pos (by exact_mod_cast n.factorial_pos)

theorem gapsw80_t43_one_le_norm_dedekindZeta_ofReal (K : Type) [Field K]
    [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    (1:ℝ) ≤ ‖dedekindZeta K (σ:ℂ)‖ := by
  have hre : 1 < (σ:ℂ).re := by rwa [Complex.ofReal_re]
  have hsum : LSeriesSummable
      (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ:ℂ) :=
    gapsw80_t10_LSeriesSummable_dedekindZeta K hre

  have hterm_re_nonneg : ∀ n,
      0 ≤ (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) n).re := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      have hcpow : (n:ℂ)^(σ:ℂ) = (((n:ℝ)^σ : ℝ):ℂ) := by
        rw [show ((n:ℕ):ℂ) = (((n:ℕ):ℝ):ℂ) from (Complex.ofReal_natCast n).symm,
          ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [hcpow, show ((Nat.card _ : ℕ):ℂ) = (((Nat.card _ : ℕ):ℝ):ℂ) from
          (Complex.ofReal_natCast _).symm, ← Complex.ofReal_div, Complex.ofReal_re]
      positivity

  have hterm1_re :
      (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) 1).re = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    simp only [Nat.cast_one, Complex.one_cpow, div_one]
    have : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
      simp [Ideal.absNorm_eq_one_iff]
    rw [this]; simp

  have hHS_re : HasSum
      (fun n => (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) n).re)
      (dedekindZeta K (σ:ℂ)).re :=
    Complex.hasSum_re hsum.hasSum
  calc (1:ℝ)
      = (LSeries.term _ (σ:ℂ) 1).re := hterm1_re.symm
    _ ≤ (dedekindZeta K (σ:ℂ)).re :=
        le_hasSum hHS_re 1 (fun n _ => hterm_re_nonneg n)
    _ ≤ ‖dedekindZeta K (σ:ℂ)‖ := Complex.re_le_norm _

theorem gapsw80_t43_log_pi_le : Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi) := by
  have h1 : Real.log Real.pi ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_pos])
  have h2 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

theorem gapsw80_t43_stirling_core {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) := by
  have hlog_m : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have h2π : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have key := Stirling.le_log_factorial_stirling (Nat.one_le_iff_ne_zero.mp hm)
  push_cast at key ⊢
  linarith

theorem gapsw80_t43_log_norm_Gammaℝ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1)
      ≤ Real.log ‖Complex.Gammaℝ ((2 * ((m:ℝ) + 1) : ℝ):ℂ)‖ := by
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσ
  have hσ2 : σ / 2 = (m:ℝ) + 1 := by rw [hσ]; ring
  have hm1pos : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have harg : ((σ:ℂ)/2) = ((m + 1 : ℕ) : ℂ) := by
    rw [hσ]; push_cast; ring

  have heq : ‖Complex.Gammaℝ (σ:ℂ)‖
      = Real.pi ^ (-((m:ℝ)+1)) * (m ! : ℝ) := by
    rw [Complex.Gammaℝ_def, norm_mul,
      show (-(σ:ℂ)/2) = -((σ:ℂ)/2) from by ring, harg,
      gapsw80_t43_norm_Gamma_nat_succ m,
      show (-((m+1:ℕ):ℂ)) = ((-((m:ℝ)+1) : ℝ):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.ofReal_re]
  rw [heq, Real.log_mul (by positivity) (by exact_mod_cast m.factorial_pos.ne'),
    Real.log_rpow Real.pi_pos]
  have hstir : (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) :=
    gapsw80_t43_stirling_core hm
  have hπ : Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi) := gapsw80_t43_log_pi_le
  unfold gapsw80_t43_L₀
  nlinarith [hm1pos]

theorem gapsw80_t43_log_norm_Gammaℂ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1)
      ≤ Real.log ‖Complex.Gammaℂ ((2 * ((m:ℝ) + 1) : ℝ):ℂ)‖ := by
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσ
  have hσnat : σ = ((2*m+1 : ℕ):ℝ) + 1 := by push_cast; rw [hσ]; ring
  have h2πpos : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have harg : ((σ:ℝ):ℂ) = (((2*m+1) + 1 : ℕ) : ℂ) := by
    rw [hσ]; push_cast; ring

  have heq : ‖Complex.Gammaℂ (σ:ℂ)‖
      = 2 * (2*Real.pi) ^ (-σ) * ((2*m+1)! : ℝ) := by
    rw [Complex.Gammaℂ_def, norm_mul, norm_mul, harg,
      gapsw80_t43_norm_Gamma_nat_succ (2*m+1),
      show (-(((2*m+1)+1:ℕ):ℂ)) = (((-σ):ℝ):ℂ) from by rw [hσ]; push_cast; ring,
      show ((2:ℂ)*(Real.pi:ℂ)) = (((2*Real.pi:ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos h2πpos, Complex.ofReal_re]
    norm_num
  rw [heq, Real.log_mul (by positivity) (by exact_mod_cast (2*m+1).factorial_pos.ne'),
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow h2πpos]

  have hfac_le : (m ! : ℝ) ≤ ((2*m+1)! : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hlogfac : Real.log (m ! : ℝ) ≤ Real.log ((2*m+1)! : ℝ) :=
    Real.log_le_log (by exact_mod_cast m.factorial_pos) hfac_le
  have hstir : (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) :=
    gapsw80_t43_stirling_core hm
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  unfold gapsw80_t43_L₀
  nlinarith

theorem gapsw80_t43_one_le_nrPlaces_sum (K : Type) [Field K] [NumberField K] :
    1 ≤ nrRealPlaces K + nrComplexPlaces K := by
  have hk : 1 ≤ nrRealPlaces K + 2 * nrComplexPlaces K := by
    rw [card_add_two_mul_card_eq_rank]; exact Module.finrank_pos
  omega

theorem gapsw80_t43_exists_m_superlinear (D : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ D * ((m:ℝ) + 1) < (m:ℝ) * Real.log m := by
  set D' := max D 0 with hD'
  have hD'0 : 0 ≤ D' := le_max_right _ _
  have hlog : ∀ᶠ m : ℕ in atTop, 2 * D' < Real.log (m:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (2*D')
  obtain ⟨m, hmD, hm2⟩ := (hlog.and (eventually_ge_atTop 2)).exists
  refine ⟨m, hm2, ?_⟩
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  calc D * ((m:ℝ) + 1)
      ≤ D' * ((m:ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ D' * (2 * (m:ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD'0
        have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
        linarith
    _ = (2 * D') * (m:ℝ) := by ring
    _ < Real.log (m:ℝ) * (m:ℝ) := mul_lt_mul_of_pos_right hmD hm0
    _ = (m:ℝ) * Real.log m := by ring

set_option maxHeartbeats 16000000 in

theorem gapsw80_t43_SL_closed : gapsw80_t42_CompletedZetaRealSuperlinear := by
  have _em := Classical.em
  intro K _ _ C
  obtain ⟨m, hm2, hmD⟩ := gapsw80_t43_exists_m_superlinear (2 * |C| + gapsw80_t43_L₀)
  have hm1 : 1 ≤ m := by omega
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσdef
  have hσ4 : (4:ℝ) ≤ σ := by
    have : (2:ℝ) ≤ (m:ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm1
    rw [hσdef]; linarith
  have hσ1 : (1:ℝ) < σ := by linarith
  have hσ0 : (0:ℝ) < σ := by linarith
  have hnorm_s : ‖(σ:ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos hσ0

  refine ⟨(σ:ℂ), ?_, ?_, ?_, ?_⟩
  · rw [hnorm_s]; linarith
  · exact_mod_cast hσ0.ne'
  · intro h; rw [Complex.ofReal_eq_one] at h; linarith

  have hre : (1:ℝ) < (σ:ℂ).re := by rwa [Complex.ofReal_re]

  set L : ℝ := (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1) with hLdef
  have hL_pos : 0 ≤ L := by
    have h2C : 0 ≤ 2 * |C| * ((m:ℝ)+1) := by positivity
    rw [hLdef]; linarith [hmD]
  have hCL : C * σ < L := by
    rw [hσdef, hLdef]
    have habs : C * (2 * ((m:ℝ)+1)) ≤ |C| * (2 * ((m:ℝ)+1)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    linarith [hmD]

  rw [hnorm_s, gapsw80_t10_completedDedekindZeta_eq_T1 K hre,
    gapsw80_t1_completedDedekindZeta]
  refine lt_of_lt_of_le hCL ?_

  have hDge1 : (1:ℝ) ≤ ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ :=
    gapsw80_t43_one_le_norm_discrPow K hσ0.le
  have hZge1 : (1:ℝ) ≤ ‖dedekindZeta K (σ:ℂ)‖ :=
    gapsw80_t43_one_le_norm_dedekindZeta_ofReal K hσ1
  have hGRne : Complex.Gammaℝ (σ:ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; exact hσ0)
  have hGCne : Complex.Gammaℂ (σ:ℂ) ≠ 0 :=
    gapsw80_t16_Gammaℂ_ne_zero (by rw [Complex.ofReal_re]; exact hσ0)
  have hGRpos : (0:ℝ) < ‖Complex.Gammaℝ (σ:ℂ)‖ := norm_pos_iff.mpr hGRne
  have hGCpos : (0:ℝ) < ‖Complex.Gammaℂ (σ:ℂ)‖ := norm_pos_iff.mpr hGCne
  have hGRL : L ≤ Real.log ‖Complex.Gammaℝ (σ:ℂ)‖ := by
    rw [hLdef]; exact gapsw80_t43_log_norm_Gammaℝ_ge hm1
  have hGCL : L ≤ Real.log ‖Complex.Gammaℂ (σ:ℂ)‖ := by
    rw [hLdef]; exact gapsw80_t43_log_norm_Gammaℂ_ge hm1
  have hs1 : ‖(σ:ℂ) - 1‖ = σ - 1 := by
    rw [show ((σ:ℂ) - 1) = (((σ - 1 : ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)

  simp only [norm_mul, norm_pow, hnorm_s, hs1]

  have hall_pos :
      (0:ℝ) < σ * (σ - 1) *
        (‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖) := by
    have : (0:ℝ) < σ - 1 := by linarith
    positivity

  rw [show σ * (σ - 1) *
        (‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖)
      = (σ * (σ - 1)) * ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖ by ring,
    Real.log_mul (by positivity) (by linarith [hZge1]),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by linarith [hDge1]),
    Real.log_pow, Real.log_pow]

  have hlog_ss1 : 0 ≤ Real.log (σ * (σ - 1)) :=
    Real.log_nonneg (by nlinarith)
  have hlogD : 0 ≤ Real.log ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ :=
    Real.log_nonneg hDge1
  have hlogZ : 0 ≤ Real.log ‖dedekindZeta K (σ:ℂ)‖ := Real.log_nonneg hZge1

  have hr1 : (nrRealPlaces K : ℝ) * L
      ≤ (nrRealPlaces K : ℝ) * Real.log ‖Complex.Gammaℝ (σ:ℂ)‖ :=
    mul_le_mul_of_nonneg_left hGRL (Nat.cast_nonneg _)
  have hr2 : (nrComplexPlaces K : ℝ) * L
      ≤ (nrComplexPlaces K : ℝ) * Real.log ‖Complex.Gammaℂ (σ:ℂ)‖ :=
    mul_le_mul_of_nonneg_left hGCL (Nat.cast_nonneg _)
  have hrsum : (1:ℝ) ≤ (nrRealPlaces K : ℝ) + (nrComplexPlaces K : ℝ) := by
    exact_mod_cast gapsw80_t43_one_le_nrPlaces_sum K
  nlinarith [mul_nonneg (Nat.cast_nonneg (nrRealPlaces K)) hL_pos,
    mul_nonneg (Nat.cast_nonneg (nrComplexPlaces K)) hL_pos]

end FLT.Gapsw80T43CompletedZetaRealSuperlinearProof
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition FLT.Gapsw80T9ClassSumA1Closure FLT.Gapsw80T10DedekindZetaBridgeA1Discharge FLT.Gapsw80T16XiRightHalfBoundProof FLT.Gapsw80T36D1appXiEndpointResidueProof FLT.Gapsw80T43CompletedZetaRealSuperlinearProof FLT.Gapsw80T11ExplicitFormulaA34Decomp FLT.Gapsw80T32D1aBoundaryCaseDecomp FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof in

theorem solution (K : Type) [Field K] [NumberField K] :
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) ∧
      (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
      (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0) ∧
      (∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖) := by
  refine ⟨gapsw80_t9_completedDedekindZeta K, ?_, ?_, ?_, gapsw80_t16_B1_closed K,
    gapsw80_t36_D1app_closed K, gapsw80_t43_SL_closed K⟩
  · exact gapsw80_t9_differentiableOn_completedDedekindZeta K
  · exact fun s hs0 hs1 => gapsw80_t9_completedDedekindZeta_FE K hs0 hs1
  · intro s hs
    rw [gapsw80_t10_completedDedekindZeta_eq_T1 K hs]
    rfl

end
end
end
end
end
end S_NumberField_exists_completedDedekindZeta_package
end P2MW
export P2MW.S_NumberField_exists_completedDedekindZeta_package (solution)
