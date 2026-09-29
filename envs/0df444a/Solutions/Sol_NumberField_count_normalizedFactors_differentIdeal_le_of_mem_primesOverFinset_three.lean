-- Prove2me | solution 1 for NumberField.count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3ee3fb65-b4b8-5bab-971f-bee0a27b3a18

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 8000000
set_option maxHeartbeats 6400000

namespace AlgebraicCurve
end AlgebraicCurve
namespace AutomorphicFreeness
end AutomorphicFreeness
namespace CategoryTheory
p2m_export "CategoryTheory" "eq Pairwise Under inclusion Quotient Noetherian Injective over Congruence End evaluation Free exp pi types Over comp_apply sum eval_map bijection Bundled eval Quotient.mk"
p2m_open "CategoryTheory"
end CategoryTheory
namespace Classical
p2m_export "Classical" "choice choose_spec em by_cases choose not_not"
p2m_open "Classical"
end Classical
namespace CongruenceSubgroup
p2m_open "CongruenceSubgroup"
end CongruenceSubgroup
namespace CuspForm
p2m_export "CuspForm" "sub_apply mk translate coe_zero zero_apply coe_sub ext"
p2m_open "CuspForm"
end CuspForm
namespace CyclicTate
end CyclicTate
namespace Deformation
end Deformation
namespace Deformation
namespace CarayolDescent
end Deformation.CarayolDescent
namespace Deformation
namespace IteratedPowerSeries
end Deformation.IteratedPowerSeries
namespace FLT
namespace GL2FiniteAdelicMatrixIdentificationGeneralF
end FLT.GL2FiniteAdelicMatrixIdentificationGeneralF
namespace FLT
namespace Gapsw37T2TameDifferentCeiling
end FLT.Gapsw37T2TameDifferentCeiling
namespace FLT
namespace Gapsw43T4WildDifferentLowerBoundGlue
end FLT.Gapsw43T4WildDifferentLowerBoundGlue
namespace FLT
namespace Gapsw44T4WildDifferentSummationWs
end FLT.Gapsw44T4WildDifferentSummationWs
namespace FLT
namespace Gapsw45T4WildDifferentEisensteinLink1
end FLT.Gapsw45T4WildDifferentEisensteinLink1
namespace FLT
namespace Gapsw46T5WildDifferentEisensteinLink2a
end FLT.Gapsw46T5WildDifferentEisensteinLink2a
namespace FLT
namespace Gapsw47T5WildDifferentLink2bGlobalisation
end FLT.Gapsw47T5WildDifferentLink2bGlobalisation
namespace FLT
namespace Gapsw47T5WildDifferentLink2bMonogenicEngine
end FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
namespace FLT
namespace Gapsw48T5CompletionTransportCarrierSlices
end FLT.Gapsw48T5CompletionTransportCarrierSlices
namespace FLT
namespace Gapsw50T4PieceICompletedElementProduction
end FLT.Gapsw50T4PieceICompletedElementProduction
namespace FLT
namespace Gapsw53T3WildCutThresholdCurrency
end FLT.Gapsw53T3WildCutThresholdCurrency
namespace FLT
namespace Gapsw54T2KrasnerGlobalGeneratorTransport
end FLT.Gapsw54T2KrasnerGlobalGeneratorTransport
namespace FLT
namespace Gapsw54T3WildCompletionDvrWitness
end FLT.Gapsw54T3WildCompletionDvrWitness
namespace FLT
namespace Gapsw55T2KrasnerDescentGlobalPickSeam
end FLT.Gapsw55T2KrasnerDescentGlobalPickSeam
namespace FLT
namespace Gapsw57T2DvrBaseProductionMint
end FLT.Gapsw57T2DvrBaseProductionMint
namespace FLT
namespace Gapsw57T3SinglePrimeCRTPickAtom
end FLT.Gapsw57T3SinglePrimeCRTPickAtom
namespace FLT
namespace Gapsw58T1SeamSupplyDecomposition
end FLT.Gapsw58T1SeamSupplyDecomposition
namespace FLT
namespace Gapsw58T2DvrBaseResidueSurjectivityReduction
end FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
namespace FLT
namespace Gapsw58T5WittASideEngineAtoms
end FLT.Gapsw58T5WittASideEngineAtoms
namespace FLT
namespace Gapsw59T1GlobalCRTPickSupplyDischarge
end FLT.Gapsw59T1GlobalCRTPickSupplyDischarge
namespace FLT
namespace Gapsw59T2WittCohenLiftReduction
end FLT.Gapsw59T2WittCohenLiftReduction
namespace FLT
namespace Gapsw60T2TeichmuellerSectionAtoms
end FLT.Gapsw60T2TeichmuellerSectionAtoms
namespace FLT
namespace Gapsw60T5PostRd59RegistryGateAndWeld
end FLT.Gapsw60T5PostRd59RegistryGateAndWeld
namespace FLT
namespace Gapsw61T2TeichmuellerSectionFunction
end FLT.Gapsw61T2TeichmuellerSectionFunction
namespace FLT
namespace Gapsw62T2PiadicDigitExpansion
end FLT.Gapsw62T2PiadicDigitExpansion
namespace FLT
namespace Gapsw62T3TeichmuellerAdditiveCarry
end FLT.Gapsw62T3TeichmuellerAdditiveCarry
namespace FLT
namespace Gapsw62T4WittGhostAssembly
end FLT.Gapsw62T4WittGhostAssembly
namespace FLT
namespace Gapsw63T1XjPiSpanningFamily
end FLT.Gapsw63T1XjPiSpanningFamily
namespace FLT
namespace Gapsw63T4ModuleFiniteCarrier
end FLT.Gapsw63T4ModuleFiniteCarrier
namespace FLT
namespace Gapsw63T4bWittGhostRingHomUpgrade
end FLT.Gapsw63T4bWittGhostRingHomUpgrade
namespace FLT
namespace Gapsw64T2SpanningFamilyWeld
end FLT.Gapsw64T2SpanningFamilyWeld
namespace FLT
namespace Gapsw65T6HgenHresResidualAtoms
end FLT.Gapsw65T6HgenHresResidualAtoms
namespace FLT
namespace Gapsw66T3EisensteinCoeffFactorisationSupply
end FLT.Gapsw66T3EisensteinCoeffFactorisationSupply
namespace FLT
namespace Gapsw66T4HagreeDischargePackedAlgebra
end FLT.Gapsw66T4HagreeDischargePackedAlgebra
namespace FLT
namespace Gapsw67T3WittDigitCongruenceEngine
end FLT.Gapsw67T3WittDigitCongruenceEngine
namespace FLT
namespace Gapsw67T4EisensteinCoeffWittBodyWeld
end FLT.Gapsw67T4EisensteinCoeffWittBodyWeld
namespace FLT
namespace Gapsw67T5UniformizerEisensteinSupply
end FLT.Gapsw67T5UniformizerEisensteinSupply
namespace FLT
namespace Gapsw67T6WittLiftAsserterSpine
end FLT.Gapsw67T6WittLiftAsserterSpine
namespace FLT
namespace Gapsw68T2WittEnginePackBuilder
end FLT.Gapsw68T2WittEnginePackBuilder
namespace FLT
namespace Gapsw68T3WittCohenLiftAsserter
end FLT.Gapsw68T3WittCohenLiftAsserter
namespace FLT
namespace Gapsw68T4Rd67ConsumptionGate
end FLT.Gapsw68T4Rd67ConsumptionGate
namespace FLT
namespace Gapsw69T1WittCohenLimitExistence
end FLT.Gapsw69T1WittCohenLimitExistence
namespace FLT
namespace Gapsw69T2WittApproxRingLaws
end FLT.Gapsw69T2WittApproxRingLaws
namespace FLT
namespace Gapsw69T3WittCohenLiftExactAsserter
end FLT.Gapsw69T3WittCohenLiftExactAsserter
namespace FLT
namespace Gapsw70T3SpineBResidualSurfaceFire
end FLT.Gapsw70T3SpineBResidualSurfaceFire
namespace FLT
namespace Gapsw77T4PieceIResidualCountEquiv
end FLT.Gapsw77T4PieceIResidualCountEquiv
namespace FLT
namespace Gapsw78T1PieceIResidualOfLocalDifferent
end FLT.Gapsw78T1PieceIResidualOfLocalDifferent
namespace FLT
namespace Gapsw78T2LocalDiffUniformizerDischarge
end FLT.Gapsw78T2LocalDiffUniformizerDischarge
namespace FLT
namespace Gapsw78T6AbstractBaseAKLBFrame
end FLT.Gapsw78T6AbstractBaseAKLBFrame
namespace FLT
namespace Gapsw78T7AbstractBaseEngineFire
end FLT.Gapsw78T7AbstractBaseEngineFire
namespace FLT
namespace Gapsw78T8AbstractBaseDerivDifferentEq
end FLT.Gapsw78T8AbstractBaseDerivDifferentEq
namespace FLT
namespace Gapsw78T9GlobalPrimitiveDerivWire
end FLT.Gapsw78T9GlobalPrimitiveDerivWire
namespace FLT
namespace Gapsw79T1CofactorUnitOfResidueGenerator
end FLT.Gapsw79T1CofactorUnitOfResidueGenerator
namespace FLT
namespace Gapsw79T2CofactorUnitResidueReduction
end FLT.Gapsw79T2CofactorUnitResidueReduction
namespace FLT
namespace Gapsw79T3ResidueCharpolyReduction
end FLT.Gapsw79T3ResidueCharpolyReduction
namespace FLT
namespace Gapsw79T4CharpolyResidueSepReduction
end FLT.Gapsw79T4CharpolyResidueSepReduction
namespace FLT
namespace Gapsw7X1RamificationFiltrationVocab
end FLT.Gapsw7X1RamificationFiltrationVocab
namespace FLT
namespace Gapsw7X1cPerPlaceDiscDecomposition
end FLT.Gapsw7X1cPerPlaceDiscDecomposition
namespace FLT
namespace Gapsw7X1eRealizedLowerFiltration
end FLT.Gapsw7X1eRealizedLowerFiltration
namespace FLT
namespace Gapsw7X1fHilbertDifferentFormulaBridge
end FLT.Gapsw7X1fHilbertDifferentFormulaBridge
namespace FLT
namespace Gapsw7X1iPerPlaceEmbeddedInstantiation
end FLT.Gapsw7X1iPerPlaceEmbeddedInstantiation
namespace FLT
namespace Gapsw7X1jRealizedRawSumMajoration
end FLT.Gapsw7X1jRealizedRawSumMajoration
namespace FLT
namespace Gapsw7X1mCompletionCarrier
end FLT.Gapsw7X1mCompletionCarrier
namespace FLT
namespace Gapsw7X1xLocalDifferentCompletionIdentification
end FLT.Gapsw7X1xLocalDifferentCompletionIdentification
namespace FLT
namespace Gapsw7X3bDerivativeDifferentSlice
end FLT.Gapsw7X3bDerivativeDifferentSlice
namespace FLT
namespace Gapsw7X3jCarrierAlgebraWiring
end FLT.Gapsw7X3jCarrierAlgebraWiring
namespace FLT
namespace Gapsw7X3lCarrierIntegralClosure
end FLT.Gapsw7X3lCarrierIntegralClosure
namespace FLT
namespace Gapsw7X3lRd20t4HmapHfxCarrierWss
end FLT.Gapsw7X3lRd20t4HmapHfxCarrierWss
namespace FLT
namespace Gapsw7X3mCompletionFieldFiniteDimensional
end FLT.Gapsw7X3mCompletionFieldFiniteDimensional
namespace FLT
namespace Gapsw7X3pHenselCoeffIntegralClosureHeadline
end FLT.Gapsw7X3pHenselCoeffIntegralClosureHeadline
namespace FLT
namespace Gapsw7X3wExtensionCompletionCarrier
end FLT.Gapsw7X3wExtensionCompletionCarrier
namespace FLT
namespace Gapsw7X3xCrossPlaceTraceDecomposition
end FLT.Gapsw7X3xCrossPlaceTraceDecomposition
namespace FLT
namespace Gapsw7X4gCompletionInstanceRow
end FLT.Gapsw7X4gCompletionInstanceRow
namespace FLT
namespace PlaceDataSemilocalDischarge
end FLT.PlaceDataSemilocalDischarge
namespace Finset
p2m_export "Finset" "image fold mem_univ eq_univ_iff_forall image_singleton coe_image sum_sdiff coe_inv mul_mem_mul cons_induction coe_range diag exists coe_mul card smul_def filter mem_range sum_singleton ext gcd mul_sum mem_image sum_eq_single Subset.trans finite_toSet coe_sub preimage range_zero sum_congr choose sum_sub_distrib pow_mem_pow notMem_empty choose_spec mem_singleton map_map sum_range_succ pi mem_filter mem_coe val_injective mem_map sum_empty univ slice coe_pow sum_mul mem_sup isUnit_iff sum_add_distrib mem_sdiff coe_inj map singleton_subset_iff restrict range_eq_Ico sum_const_zero coe_one sum_filter_ne_zero cons sum_Ico_consecutive range Subset.antisymm sum_Ico_eq_sub smul_mem_smul mk sum_range_succ' coe_zpow map_injective one_lt_card fintype sum_cons coe_univ mem_offDiag sum_range_one mem_Ico coe_zero val card_eq_of_bijective mem_image_of_mem offDiag mem_cons mem_preimage Ico"
p2m_open "Finset"
end Finset
namespace Function
p2m_export "Function" "update update_of_ne update_self iterate_succ_apply' comp_assoc invFun Surjective Bijective algebra iterate_add_apply comp_id Injective Exact comp iterate_zero_apply iterate_fixed nontrivial onFun comp_apply eval"
p2m_open "Function"
end Function
namespace HahnSeries
p2m_export "HahnSeries" "single order coeff isUnit_iff algebraMap_apply pow_add C map mk instCommRing addVal map_C map_coeff"
p2m_open "HahnSeries"
end HahnSeries
namespace HeightOneSpectrum
end HeightOneSpectrum
namespace IntermediateField
p2m_export "IntermediateField" "toSubalgebra_injective charP toAlgebra map_le_iff_le_comap mk val finrank_top' mem_restrictScalars lift inclusion adjoin.powerBasis_dim ext equivOfEq algebraMap_apply smul_def mem_toSubalgebra adjoin.finrank FG adjoin toSubalgebra fg_top comap map_map topEquiv mem_top adjoin.powerBasis restrictScalars top_toSubalgebra algebraMap_mem mem_bot adjoin_simple_toSubalgebra_of_isAlgebraic map_injective mem_map Lifts subset_adjoin smul_mem normal restrict isAlgebraic_iff map"
p2m_open "IntermediateField"
end IntermediateField
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "mem_primesOverFinset_iff primesOverFinset HeightOneSpectrum.adicCompletion HeightOneSpectrum.adicCompletionIntegers HeightOneSpectrum.ext exists_forall_sub_mem_ideal mk HeightOneSpectrum"
p2m_open "IsDedekindDomain"
end IsDedekindDomain
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "mem_primesOverFinset_iff primesOverFinset HeightOneSpectrum.adicCompletion HeightOneSpectrum.adicCompletionIntegers HeightOneSpectrum.ext exists_forall_sub_mem_ideal mk HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "intValuation_exists_uniformizer valuation_of_algebraMap intValuation_le_pow_iff_mem valuedAdicCompletion_eq_valuation adicCompletion_valueGroup_eq isMaximal algebraMap_adicCompletion valuation_lt_one_iff_mem mk asIdeal mem_adicCompletionIntegers comap isPrime adicCompletion valuation coe_mem_adicCompletionIntegers ne_bot under intValuation_le_one adicCompletionIntegers valuedAdicCompletion_surjective irreducible intValuation_if_neg prime intValuation"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"
end IsDedekindDomain.HeightOneSpectrum
namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "quotient addVal_add mk irreducible_iff_uniformizer maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd addVal_def eq_unit_mul_pow_irreducible exists_irreducible addVal_pow remainder not_a_field' not_a_field addVal_mul"
p2m_open "IsDiscreteValuationRing"
end IsDiscreteValuationRing
namespace IsLocalRing
p2m_export "IsLocalRing" "eq_maximalIdeal ResidueField maximalIdeal_le_jacobson of_surjective maximalIdeal maximalIdeal.isMaximal mem_maximalIdeal notMem_maximalIdeal residue_surjective of_injective of_surjective' eq_of_eval_eq_zero_of_not_isUnit_sub residue"
p2m_open "IsLocalRing"
end IsLocalRing
namespace LinearMap
p2m_export "LinearMap" "mem_range comp_id range sub_apply coe_range inverse charpoly_natDegree det_baseChange rank ker_eq_bot range_zero charpoly_prodMap id codRestrict_apply charpoly_monic module isUnit_iff_ker_eq_bot mul_apply' restrict_apply restrict_coe_apply map_span codRestrict inr zero_apply baseChangeHom map_injective trace_comp_comm' charpoly mk diag pi mul proj ext comp isIntegral trace single prodMap comp_assoc baseChange restrictScalars ker inl mem_ker comp_apply subtype_comp_codRestrict trace_conj' mem_range_self restrict isUnit_iff_isUnit_det conjugate charpoly_baseChange"
p2m_open "LinearMap"
end LinearMap
namespace Matrix
p2m_export "Matrix" "J isIntegral ext row add sub_apply zero map_smul' trace_conj' diag scalar uniformity comp charpoly isUnit_iff_isUnit_det map_map rank smul exp_nsmul charP zero_apply map_injective single ext_iff mul_apply' zpow_neg charpoly_monic toLinearEquiv det inhabited diagonal comp_apply of map inv_inj one unique inv_zpow' trace module nonempty"
p2m_open "Matrix"
end Matrix
namespace Module
p2m_export "Module" "Finite.of_finite Injective Free.chooseBasis isTorsionFree_iff_algebraMap_injective equiv Finite.of_basis End.baseChangeHom finrank Free mk finite_def Free.of_basis Finite.of_injective IsTorsionFree Finite.of_restrictScalars_finite End restrictScalars End.aeval_apply_of_hasEigenvector End.hasEigenvalue_iff_isRoot_charpoly Finite.of_surjective Finite.of_isLocalization finrank_of_bijective_algebraMap Free.of_divisionRing Finite.fg_top jacobson projective_lifting_property Basis"
p2m_open "Module"
end Module
namespace MonoidWithZeroHom
p2m_export "MonoidWithZeroHom" "id ext mk ext_int coe_one comp_apply inl comp_id comp_assoc comp inr"
p2m_open "MonoidWithZeroHom"
end MonoidWithZeroHom
namespace Multiplicative
p2m_export "Multiplicative" "ofAdd toAdd ofAdd_lt ext group smul mul toAdd_le fintype"
p2m_open "Multiplicative"
end Multiplicative
namespace NumberField
p2m_export "NumberField" "FinitePlace mk place RingOfIntegers RingOfIntegers.rank"
p2m_open "NumberField"
end NumberField
namespace Pointwise
p2m_open "Pointwise"
end Pointwise
namespace Polynomial
p2m_export "Polynomial" "C monic_X_add_C map_injective X map_monic_ne_zero coeff_natDegree eval_mul natDegree_comp coeff_map coe_one derivative_C aeval_map_algebraMap derivative_map aeval_def natDegree_mul eval₂_at_zero coeff natDegree_derivative_lt unique lifts_and_natDegree_eq_and_monic divX eval₂ rootMultiplicity_le_one_of_separable aeval ext_iff map_surjective degree mapEquiv expand factor aeval_C rootMultiplicity_mul update coe_inj IsRoot.def map_map map_dvd_map nontrivial_iff coe_pow map_C isUnit_map aeval_eq_sum_range derivative_X_pow Splits map eval₂_X count_roots derivative_X comp_assoc Monic comp roots algebra eval₂_mul eval_natCast eval_pow natDegree_pow coe_mul X_dvd_iff sum infinite rootMultiplicity_pos coe_sub charP derivative_mul reverse isUnit_iff_degree_eq_zero aeval_comp rootMultiplicity_eq_zero map_div Separable natDegree eval_X eval₂_map eval_C eq_of_monic_of_dvd_of_natDegree_le X_pow_comp mem_lifts divX_mul_X_add nontrivial rootMultiplicity coe_zero rootMultiplicity_X_sub_C_pow eval_sub derivative_sub pow module natDegree_eq_zero natDegree_map Gal monic_X_sub_C derivative map_X eval_one aeval_X modByMonic_add_div coeffs constantCoeff eval₂_eq_eval_map roots_pow map_dvd map_comp algebraMap_apply IsRoot.dvd degree_map modByMonic_eq_zero_iff_dvd coeff_eq_zero_of_natDegree_lt aeval_mul mod eval_map inhabited natDegree_X_sub_C ext not_isUnit_X Monic.of_mul_monic_left coeff_X_pow IsRoot content eval₂_C monic_X_pow_sub_C hom_eval₂ funext eval_eq_sum_range' isUnit_iff ring aeval_algHom_apply lifts constantCoeff_apply natDegree_X_add_C restriction coeff_derivative Separable.map aeval_algebraMap_apply eval natDegree_le_of_dvd"
p2m_open "Polynomial"
end Polynomial
namespace PowerSeries
p2m_export "PowerSeries" "coe_mul X_dvd_iff algebraMap_apply subst mk map_comp aeval map_surjective coe_zero eval₂_X coe_sub eval₂ map_X constantCoeff coe_one eval₂_C derivative coeff_map expand order derivative_X coe_pow heval ext coeff_X_pow map_eq_zero map_C map C coeff X map_injective exp coeff_derivative derivative_C"
p2m_open "PowerSeries"
end PowerSeries
namespace ProartinianCat
end ProartinianCat
namespace TensorProduct
p2m_export "TensorProduct" "congr map_map lift mk map_comp ext tmul map_surjective map Algebra.smul_def mk_surjective"
p2m_open "TensorProduct"
end TensorProduct
namespace Topology
p2m_export "Topology" "lower upper"
p2m_open "Topology"
end Topology
namespace UniqueFactorizationMonoid
p2m_export "UniqueFactorizationMonoid" "normalizedFactors_pow emultiplicity_eq_count_normalizedFactors mk factors normalizedFactors_irreducible factors_eq_normalizedFactors normalizedFactors"
p2m_open "UniqueFactorizationMonoid"
end UniqueFactorizationMonoid
namespace Valuation
p2m_export "Valuation" "isClosed_valuationSubring map_add' valuationSubring ext mem_valuationSubring_iff map_sub map IsRankOneDiscrete ne_zero_iff map_add_eq_of_lt_right map_div congr Completion mem_integer_iff is_topological_valuation integer restrict pos_iff isClosed_integer mem_maximalIdeal_iff integer.integers comap mk map_sub_swap Uniformizer IsRankOneDiscrete.mk' isOpen_valuationSubring hasBasis_uniformity"
namespace IsRankOneDiscrete
p2m_export "Valuation.IsRankOneDiscrete" "valueGroup₀_equiv_withZeroMulInt_strictMono valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective valueGroup₀_equiv_withZeroMulInt_apply mk generator_lt_one exists_generator_lt_one' generator_zpowers_eq_valueGroup generator valueGroup₀_equiv_withZeroMulInt mk'"
p2m_open "Valuation.IsRankOneDiscrete Valuation"
end Valuation.IsRankOneDiscrete
namespace Valued
p2m_export "Valued" "is_topological_valuation isClosed_integer mk mk' v hasBasis_uniformity integer valuedCompletion_apply extension integer.finite_quotient_maximalIdeal_pow_of_finite_residueField exists_pow_lt_of_le_exp_neg_one isClosed_valuationSubring mem_nhds ResidueField maximalIdeal isOpen_valuationSubring"
p2m_open "Valued"
end Valued
namespace WithZero
p2m_export "WithZero" "coe_one zero_lt_coe exists_ne_zero_and_lt_and_lt map lt_ofAdd_iff coe_le_coe coe_mul le_ofAdd_iff coe_inj coe coe_lt_coe exp_inj exp_ne_zero coe_inv exists exp exp_zero lift coe_zpow inhabited coe_unzero pow one coe_pow le unzero zero_eq_bot exp_nsmul exp_le_exp"
p2m_open "WithZero"
end WithZero

section

scoped instance {K L : Type*} [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L] :
    Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := by simp [Algebra.commutes]
  smul_def' _ _ := by simp [← Algebra.smul_def]; rfl

end

section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000
p2m_open "Finset P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Finset P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.CyclicTate IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing CongruenceSubgroup P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.CongruenceSubgroup CuspForm P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.CuspForm"
open AutomorphicFreeness Deformation Deformation.IteratedPowerSeries ProartinianCat
p2m_open "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Deformation.CarayolDescent Matrix P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Matrix CategoryTheory P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.CategoryTheory"
namespace ModularCurve
namespace AdaptedFamily
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)
section DefReprDischarge
variable (𝓞 : Type) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]
scoped instance fact_prime_three_defReprHeckeInt : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
end DefReprDischarge
end AdaptedFamily
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily"
end ModularCurve
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
section
variable {K L : Type*} [Field K] [Field L]
variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]
p2m_open "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
variable [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
scoped instance : CharZero Kᵥ :=
  ((algebraMap K Kᵥ).charZero_iff (algebraMap K Kᵥ).injective).mp inferInstance
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw45T4WildDifferentEisensteinLink1
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "IsDiscreteValuationRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDiscreteValuationRing"
section UltrametricEngine
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
set_option maxHeartbeats 1600000 in

theorem gapsw45_t4_addVal_add_eq_left {x y : B}
    (h : addVal B x < addVal B y) :
    addVal B (x + y) = addVal B x := by
  have _em := Classical.em
  refine le_antisymm ?_ ?_
  · have hx : x = x + y + -y := (add_neg_cancel_right x y).symm
    have hneg : addVal B (-y) = addVal B y := by
      have h1 : (-y : B) = ((-1 : Bˣ) : B) * y := by
        rw [Units.val_neg, Units.val_one, neg_one_mul]
      rw [h1, addVal_mul, addVal_eq_zero_of_unit, zero_add]
    have h2 : min (addVal B (x + y)) (addVal B (-y)) ≤ addVal B x := by
      conv_rhs => rw [hx]
      exact addVal_add
    rw [hneg] at h2
    rcases min_cases (addVal B (x + y)) (addVal B y) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rwa [heq] at h2
    · rw [heq] at h2
      exact absurd (h.trans_le h2) (lt_irrefl _)
  · have h3 : min (addVal B x) (addVal B y) ≤ addVal B (x + y) := addVal_add
    rwa [min_eq_left h.le] at h3
end UltrametricEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
end FLT.Gapsw45T4WildDifferentEisensteinLink1
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw45T4WildDifferentEisensteinLink1
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "IsDiscreteValuationRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDiscreteValuationRing"
section UltrametricEngine
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
set_option maxHeartbeats 1600000 in

theorem gapsw45_t4_addVal_sum_eq_min {ι : Type*} (s : Finset ι) (t : ι → B) :
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → addVal B (t i) ≠ addVal B (t j)) →
    (s = ∅ ∨ ∃ i ∈ s, addVal B (∑ j ∈ s, t j) = addVal B (t i)
      ∧ ∀ j ∈ s, addVal B (t i) ≤ addVal B (t j)) := by
  have _em := Classical.em
  induction s using Finset.cons_induction with
  | empty => exact fun _ => Or.inl rfl
  | cons a s ha IH =>
    intro hdist
    right
    have hdist' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → addVal B (t i) ≠ addVal B (t j) :=
      fun i hi j hj hij => hdist i (Finset.mem_cons.mpr (Or.inr hi))
        j (Finset.mem_cons.mpr (Or.inr hj)) hij
    rcases IH hdist' with rfl | ⟨i, hi, hsumv, hmin⟩
    · refine ⟨a, Finset.mem_cons.mpr (Or.inl rfl), ?_, ?_⟩
      · rw [Finset.sum_cons, Finset.sum_empty, add_zero]
      · intro j hj
        rcases Finset.mem_cons.mp hj with rfl | hj0
        · exact le_refl _
        · exact absurd hj0 (Finset.notMem_empty j)
    · have hai : a ≠ i := fun h => ha (by rw [h]; exact hi)
      have hne : addVal B (t a) ≠ addVal B (t i) :=
        hdist a (Finset.mem_cons.mpr (Or.inl rfl)) i (Finset.mem_cons.mpr (Or.inr hi)) hai
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨a, Finset.mem_cons.mpr (Or.inl rfl), ?_, ?_⟩
        · rw [Finset.sum_cons]
          exact gapsw45_t4_addVal_add_eq_left (x := t a) (y := ∑ j ∈ s, t j)
            (by rw [hsumv]; exact hlt)
        · intro j hj
          rcases Finset.mem_cons.mp hj with rfl | hj'
          · exact le_refl _
          · exact hlt.le.trans (hmin j hj')
      · refine ⟨i, Finset.mem_cons.mpr (Or.inr hi), ?_, ?_⟩
        · rw [Finset.sum_cons, add_comm (t a)]
          rw [gapsw45_t4_addVal_add_eq_left (x := ∑ j ∈ s, t j) (y := t a)
            (by rw [hsumv]; exact hgt)]
          exact hsumv
        · intro j hj
          rcases Finset.mem_cons.mp hj with rfl | hj'
          · exact hgt.le
          · exact hmin j hj'
end UltrametricEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
end FLT.Gapsw45T4WildDifferentEisensteinLink1
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw45T4WildDifferentEisensteinLink1
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "IsDiscreteValuationRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDiscreteValuationRing"
section UltrametricEngine
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
set_option maxHeartbeats 1600000 in

theorem gapsw45_t4_addVal_sum_le {ι : Type*} (s : Finset ι) (t : ι → B)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → addVal B (t i) ≠ addVal B (t j))
    (j : ι) (hj : j ∈ s) :
    addVal B (∑ i ∈ s, t i) ≤ addVal B (t j) := by
  have _em := Classical.em
  rcases gapsw45_t4_addVal_sum_eq_min s t hdist with hempty | ⟨i, hi, hsumv, hmin⟩
  · rw [hempty] at hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [hsumv]
    exact hmin j hj
end UltrametricEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
end FLT.Gapsw45T4WildDifferentEisensteinLink1
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw45T4WildDifferentEisensteinLink1
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "IsDiscreteValuationRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDiscreteValuationRing"
section EisensteinCeiling
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
set_option maxHeartbeats 1600000 in

theorem gapsw45_t4_addVal_term_sum_le {π : B} (hπ : Irreducible π)
    (e : ℕ) (he0 : 0 < e) (c : ℕ → B)
    (hcv : ∀ i : ℕ, i < e → c i = 0 ∨
      ∃ (u : Bˣ) (k : ℕ), c i = (u : B) * π ^ (e * k))
    (ue : Bˣ) (ke : ℕ) (hce : c (e - 1) = (ue : B) * π ^ (e * ke)) :
    addVal B (∑ i ∈ Finset.range e, c i * π ^ i) ≤ ((e - 1 + e * ke : ℕ) : ℕ∞) := by
  classical
  have _em := Classical.em
  have htop_eq : c (e - 1) * π ^ (e - 1) = (ue : B) * π ^ (e * ke + (e - 1)) := by
    rw [hce, pow_add, mul_assoc]
  have htop_ne : c (e - 1) * π ^ (e - 1) ≠ 0 := by
    rw [htop_eq]
    exact mul_ne_zero (Units.ne_zero ue) (pow_ne_zero _ hπ.ne_zero)
  have hvtop : addVal B (c (e - 1) * π ^ (e - 1)) = ((e * ke + (e - 1) : ℕ) : ℕ∞) :=
    addVal_def _ ue hπ _ htop_eq
  have hval : ∀ i ∈ (Finset.range e).filter (fun i => c i * π ^ i ≠ 0),
      ∃ k : ℕ, addVal B (c i * π ^ i) = ((e * k + i : ℕ) : ℕ∞) := by
    intro i hi
    obtain ⟨hir, hine⟩ := Finset.mem_filter.mp hi
    have hilt : i < e := Finset.mem_range.mp hir
    rcases hcv i hilt with h0 | ⟨u, k, hk⟩
    · exact absurd (by rw [h0, zero_mul]) hine
    · refine ⟨k, addVal_def _ u hπ _ ?_⟩
      rw [hk, pow_add, mul_assoc]
  have hdist : ∀ i ∈ (Finset.range e).filter (fun i => c i * π ^ i ≠ 0),
      ∀ j ∈ (Finset.range e).filter (fun i => c i * π ^ i ≠ 0),
      i ≠ j → addVal B (c i * π ^ i) ≠ addVal B (c j * π ^ j) := by
    intro i hi j hj hij hv
    obtain ⟨k, hk⟩ := hval i hi
    obtain ⟨k', hk'⟩ := hval j hj
    rw [hk, hk'] at hv
    have hnat : e * k + i = e * k' + j := by exact_mod_cast hv
    have hilt : i < e := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hjlt : j < e := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    apply hij
    have h1 : (e * k + i) % e = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hilt]
    have h2 : (e * k' + j) % e = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjlt]
    rw [← h1, ← h2, hnat]
  have hmem : e - 1 ∈ (Finset.range e).filter (fun i => c i * π ^ i ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), htop_ne⟩
  calc addVal B (∑ i ∈ Finset.range e, c i * π ^ i)
      = addVal B (∑ i ∈ (Finset.range e).filter (fun i => c i * π ^ i ≠ 0),
          c i * π ^ i) := by rw [Finset.sum_filter_ne_zero]
    _ ≤ addVal B (c (e - 1) * π ^ (e - 1)) :=
        gapsw45_t4_addVal_sum_le _ _ hdist (e - 1) hmem
    _ = ((e * ke + (e - 1) : ℕ) : ℕ∞) := hvtop
    _ = ((e - 1 + e * ke : ℕ) : ℕ∞) := by rw [Nat.add_comm]
end EisensteinCeiling
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
end FLT.Gapsw45T4WildDifferentEisensteinLink1
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw45T4WildDifferentEisensteinLink1
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "IsDiscreteValuationRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDiscreteValuationRing"
section EisensteinCeiling
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
set_option maxHeartbeats 1600000 in

theorem gapsw45_t4_addVal_eval_derivative_le
    (π : B) (hπ : Irreducible π) (f : Polynomial B) (e : ℕ)
    (he0 : 0 < e) (hdeg : f.natDegree = e) (hmonic : f.Monic)
    (hcv : ∀ i : ℕ, i + 1 < e → f.coeff (i + 1) * ((i : B) + 1) = 0 ∨
      ∃ (u : Bˣ) (k : ℕ), f.coeff (i + 1) * ((i : B) + 1) = (u : B) * π ^ (e * k))
    (ue : Bˣ) (ke : ℕ) (heB : ((e : ℕ) : B) = (ue : B) * π ^ (e * ke)) :
    addVal B (Polynomial.eval π (Polynomial.derivative f))
      ≤ ((e - 1 + e * ke : ℕ) : ℕ∞) := by
  have _em := Classical.em
  have hfe : f.coeff e = 1 := by
    rw [← hdeg]
    exact hmonic.coeff_natDegree
  have hcoe : f.coeff (e - 1 + 1) * ((↑(e - 1) : B) + 1) = (ue : B) * π ^ (e * ke) := by
    rw [← Nat.cast_add_one, show e - 1 + 1 = e from Nat.sub_add_cancel (by omega)]
    rw [hfe, one_mul, heB]
  have hcv' : ∀ i : ℕ, i < e → f.coeff (i + 1) * ((i : B) + 1) = 0 ∨
      ∃ (u : Bˣ) (k : ℕ), f.coeff (i + 1) * ((i : B) + 1) = (u : B) * π ^ (e * k) := by
    intro i hilt
    by_cases hi1 : i + 1 < e
    · exact hcv i hi1
    · have hieq : i = e - 1 := by omega
      subst hieq
      exact Or.inr ⟨ue, ke, hcoe⟩
  have hsum : Polynomial.eval π (Polynomial.derivative f)
      = ∑ i ∈ Finset.range e, f.coeff (i + 1) * ((i : B) + 1) * π ^ i := by
    have hdlt : (Polynomial.derivative f).natDegree < e := by
      have h := Polynomial.natDegree_derivative_lt (p := f) (by rw [hdeg]; omega)
      rw [hdeg] at h
      exact h
    rw [Polynomial.eval_eq_sum_range' hdlt π]
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_derivative]
  rw [hsum]
  exact gapsw45_t4_addVal_term_sum_le hπ e he0
    (fun i => f.coeff (i + 1) * ((i : B) + 1)) hcv' ue ke hcoe
end EisensteinCeiling
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
end FLT.Gapsw45T4WildDifferentEisensteinLink1
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 1600000 in

theorem gapsw47_t5_p1_algebraMap_eq_unit_mul_pow
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Algebra A B]
    (π : B) (e : ℕ) (ϖ : A) (hϖ : Irreducible ϖ)
    (u0 : Bˣ) (hu0 : algebraMap A B ϖ = (u0 : B) * π ^ e)
    (a : A) (ha : a ≠ 0) :
    ∃ (u : Bˣ) (k : ℕ), algebraMap A B a = (u : B) * π ^ (e * k) := by
  have _em := Classical.em
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hv : IsUnit (algebraMap A B (v : A)) := v.isUnit.map (algebraMap A B)
  refine ⟨hv.unit * u0 ^ n, n, ?_⟩
  rw [map_mul, map_pow, hu0, mul_pow, ← pow_mul, Units.val_mul, IsUnit.unit_spec,
    Units.val_pow_eq_pow_val]
  ring
end FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 1600000 in

theorem gapsw47_t5_p1_mapped_coeff_mul_succ_shape
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Algebra A B]
    (π : B) (e : ℕ) (ϖ : A) (hϖ : Irreducible ϖ)
    (u0 : Bˣ) (hu0 : algebraMap A B ϖ = (u0 : B) * π ^ e)
    (p : Polynomial A) :
    ∀ i : ℕ, i + 1 < e →
      (p.map (algebraMap A B)).coeff (i + 1) * ((i : B) + 1) = 0 ∨
      ∃ (u : Bˣ) (k : ℕ),
        (p.map (algebraMap A B)).coeff (i + 1) * ((i : B) + 1)
          = (u : B) * π ^ (e * k) := by
  have _em := Classical.em
  intro i _
  have hcm : (p.map (algebraMap A B)).coeff (i + 1) * ((i : B) + 1)
      = algebraMap A B (p.coeff (i + 1) * ((i : A) + 1)) := by
    rw [Polynomial.coeff_map, map_mul, map_add, map_natCast, map_one]
  by_cases h0 : p.coeff (i + 1) * ((i : A) + 1) = 0
  · left
    rw [hcm, h0, map_zero]
  · right
    obtain ⟨u, k, hu⟩ := gapsw47_t5_p1_algebraMap_eq_unit_mul_pow π e ϖ hϖ u0 hu0 _ h0
    exact ⟨u, k, by rw [hcm, hu]⟩
end FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 3200000 in

theorem gapsw47_t5_p1_adjoin_eq_top_of_residue_lift
    {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B]
    (π : B) (e : ℕ) (ϖ : A) (hϖm : ϖ ∈ IsLocalRing.maximalIdeal A)
    (u0 : Bˣ) (hu0 : algebraMap A B ϖ = (u0 : B) * π ^ e)
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ Ideal.span {π}) :
    Algebra.adjoin A {π} = ⊤ := by
  have _em := Classical.em

  have key : ∀ (n : ℕ) (b : B), ∃ y ∈ Algebra.adjoin A {π}, ∃ c : B,
      b - y = π ^ n * c := by
    intro n
    induction n with
    | zero =>
      intro b
      exact ⟨0, Subalgebra.zero_mem _, b, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨y, hy, c, hc⟩ := ih b
      obtain ⟨a, ha⟩ := hres c
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨d, hd⟩ := ha
      refine ⟨y + algebraMap A B a * π ^ n, ?_, d, ?_⟩
      · have hπa : π ∈ Algebra.adjoin A {π} := Algebra.self_mem_adjoin_singleton A π
        have hmap : algebraMap A B a ∈ Algebra.adjoin A {π} :=
          Subalgebra.algebraMap_mem _ a
        have hpow : π ^ n ∈ Algebra.adjoin A {π} := Subalgebra.pow_mem _ hπa n
        exact Subalgebra.add_mem _ hy (Subalgebra.mul_mem _ hmap hpow)
      · calc b - (y + algebraMap A B a * π ^ n)
            = (b - y) - algebraMap A B a * π ^ n := by ring
          _ = π ^ n * c - algebraMap A B a * π ^ n := by rw [hc]
          _ = π ^ n * (c - algebraMap A B a) := by ring
          _ = π ^ n * (π * d) := by rw [hd]
          _ = π ^ (n + 1) * d := by ring

  have hfg : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have hjac : IsLocalRing.maximalIdeal A ≤ Ideal.jacobson (⊥ : Ideal A) :=
    IsLocalRing.maximalIdeal_le_jacobson ⊥
  have hNN : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule (Algebra.adjoin A {π})
      ⊔ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B) := by
    rintro b -
    obtain ⟨y, hy, c, hc⟩ := key e b
    have hπe : (π : B) ^ e = ((u0⁻¹ : Bˣ) : B) * algebraMap A B ϖ := by
      rw [hu0, ← mul_assoc, Units.inv_mul, one_mul]
    have hsm : b - y = ϖ • (((u0⁻¹ : Bˣ) : B) * c) := by
      rw [Algebra.smul_def, hc, hπe]
      ring
    have hmem : b - y ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B) := by
      rw [hsm]
      exact Submodule.smul_mem_smul hϖm Submodule.mem_top
    have hsum : y + (b - y) ∈
        Subalgebra.toSubmodule (Algebra.adjoin A {π})
          ⊔ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B) :=
      Submodule.add_mem _
        (Submodule.mem_sup_left
          (show y ∈ Subalgebra.toSubmodule (Algebra.adjoin A {π}) from hy))
        (Submodule.mem_sup_right hmem)
    have hb : y + (b - y) = b := by ring
    rwa [hb] at hsum
  rw [← Algebra.toSubmodule_eq_top, ← top_le_iff]
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hNN
end FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 1600000 in

theorem gapsw47_t5_p1_adjoin_eq_top_of_irreducible
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (π : B) (e : ℕ) (ϖ : A) (hϖ : Irreducible ϖ)
    (u0 : Bˣ) (hu0 : algebraMap A B ϖ = (u0 : B) * π ^ e)
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ Ideal.span {π}) :
    Algebra.adjoin A {π} = ⊤ := by
  have _em := Classical.em
  refine gapsw47_t5_p1_adjoin_eq_top_of_residue_lift π e ϖ ?_ u0 hu0 hres
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hϖ.not_isUnit
end FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw48T5CompletionTransportCarrierSlices
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
set_option maxHeartbeats 1600000 in
open scoped algebraMap in

theorem gapsw48_t5_completion_valued_le_exp_iff_mem
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (r : R) (n : ℕ) :
    Valued.v (r : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) ↔
      r ∈ v.asIdeal ^ n := by
  have _em := Classical.em
  rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
  exact v.intValuation_le_pow_iff_mem r n
end FLT.Gapsw48T5CompletionTransportCarrierSlices
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw48T5CompletionTransportCarrierSlices
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
set_option maxHeartbeats 1600000 in
open scoped algebraMap in

theorem gapsw48_t5_not_pow_dvd_of_mem_of_completion_valued_not_le
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)
    {I : Ideal R} {x : R} {n : ℕ} (hx : x ∈ I)
    (hv : ¬ Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ))) :
    ¬ v.asIdeal ^ n ∣ I := by
  have _em := Classical.em
  intro h
  exact hv ((gapsw48_t5_completion_valued_le_exp_iff_mem K v x n).mpr
    (Ideal.le_of_dvd h hx))
end FLT.Gapsw48T5CompletionTransportCarrierSlices
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw48T5CompletionTransportCarrierSlices
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open scoped algebraMap in

def Gapsw48T5CompletionTransportPieceIResidual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
    3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal →
    ∃ x ∈ differentIdeal ℤ (𝓞 K),
      ¬ Valued.v (x : v.adicCompletion K) ≤
        WithZero.exp (-(((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal
          + (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal
            * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) : ℕ) : ℤ))
end FLT.Gapsw48T5CompletionTransportCarrierSlices
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw48T5CompletionTransportCarrierSlices
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open scoped algebraMap in

theorem gapsw48_t5_pieceIResidual_pin :
    Gapsw48T5CompletionTransportPieceIResidual =
      (∀ (K : Type) [Field K] [NumberField K]
        (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal →
        ∃ x ∈ differentIdeal ℤ (𝓞 K),
          ¬ Valued.v (x : v.adicCompletion K) ≤
            WithZero.exp (-(((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal
              + (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal
                * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) :
                  ℕ) : ℤ))) := by
  have _em := Classical.em
  rfl
end FLT.Gapsw48T5CompletionTransportCarrierSlices
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw48T5CompletionTransportCarrierSlices
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
set_option maxHeartbeats 3200000 in

theorem gapsw48_t5_wild_notDvd_of_pieceIResidual
    (hres : Gapsw48T5CompletionTransportPieceIResidual) :
    ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K)),
      P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
      3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P →
      ¬ P ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' P
          + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
            * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P))
        ∣ differentIdeal ℤ (𝓞 K) := by
  have _em := Classical.em
  intro K _ _ P hP hw
  have h3ne : (Ideal.span {(3 : ℤ)} : Ideal ℤ) ≠ ⊥ := fun h =>
    (by norm_num : (3 : ℤ) ≠ 0) (Ideal.span_singleton_eq_bot.mp h)
  have h3prime : (Ideal.span {(3 : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three
  haveI h3max : (Ideal.span {(3 : ℤ)} : Ideal ℤ).IsMaximal := h3prime.isMaximal h3ne
  have hP' := hP
  rw [IsDedekindDomain.mem_primesOverFinset_iff h3ne] at hP'
  obtain ⟨hPprime, hPlies⟩ := hP'
  haveI := hPprime
  haveI := hPlies
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h3ne P
  obtain ⟨x, hx, hval⟩ :=
    hres K ⟨P, hPprime, hPbot⟩ hP hw
  exact gapsw48_t5_not_pow_dvd_of_mem_of_completion_valued_not_le K
    ⟨P, hPprime, hPbot⟩ hx hval
end FLT.Gapsw48T5CompletionTransportCarrierSlices
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw54T2KrasnerGlobalGeneratorTransport
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw53T3WildCutThresholdCurrency
open FLT.Gapsw50T4PieceICompletedElementProduction

theorem gapsw54_t2_span_three_ne_bot : (Ideal.span {(3 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  have _em := Classical.em
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  norm_num
end FLT.Gapsw54T2KrasnerGlobalGeneratorTransport
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw54T2KrasnerGlobalGeneratorTransport
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw53T3WildCutThresholdCurrency
open FLT.Gapsw50T4PieceICompletedElementProduction

theorem gapsw54_t2_span_three_isMaximal :
    (Ideal.span {(3 : ℤ)} : Ideal ℤ).IsMaximal := by
  have _em := Classical.em
  exact ((Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three).isMaximal
    gapsw54_t2_span_three_ne_bot
end FLT.Gapsw54T2KrasnerGlobalGeneratorTransport
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw54T2KrasnerGlobalGeneratorTransport
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw53T3WildCutThresholdCurrency
open FLT.Gapsw50T4PieceICompletedElementProduction
set_option maxHeartbeats 1600000 in

theorem gapsw54_t2_ramificationIdx_ne_zero
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal ≠ 0 := by
  have _em := Classical.em
  classical
  haveI := gapsw54_t2_span_three_isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff gapsw54_t2_span_three_ne_bot] at hv
  obtain ⟨hPprime, hPlies⟩ := hv
  haveI := hPprime
  haveI := hPlies
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver v.asIdeal
    gapsw54_t2_span_three_ne_bot
end FLT.Gapsw54T2KrasnerGlobalGeneratorTransport
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw58T2DvrBaseResidueSurjectivityReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw50T4PieceICompletedElementProduction
open FLT.Gapsw55T2KrasnerDescentGlobalPickSeam
open FLT.Gapsw57T2DvrBaseProductionMint

def Gapsw58T2UnramifiedDvrBaseResidueSurjectivityProduction : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
    3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A)
      (_ : IsDiscreteValuationRing A)
      (_ : Algebra A (v.adicCompletionIntegers K))
      (_ : Module.Finite A (v.adicCompletionIntegers K)),
      Irreducible (3 : A) ∧
      ∀ b : v.adicCompletionIntegers K, ∃ a : A,
        b - algebraMap A (v.adicCompletionIntegers K) a ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
end FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw58T2DvrBaseResidueSurjectivityReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw50T4PieceICompletedElementProduction
open FLT.Gapsw55T2KrasnerDescentGlobalPickSeam
open FLT.Gapsw57T2DvrBaseProductionMint

theorem gapsw58_t2_residueSurjectivity_pin :
    Gapsw58T2UnramifiedDvrBaseResidueSurjectivityProduction =
      (∀ (K : Type) [Field K] [NumberField K]
        (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal →
        ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A)
          (_ : IsDiscreteValuationRing A)
          (_ : Algebra A (v.adicCompletionIntegers K))
          (_ : Module.Finite A (v.adicCompletionIntegers K)),
          Irreducible (3 : A) ∧
          ∀ b : v.adicCompletionIntegers K, ∃ a : A,
            b - algebraMap A (v.adicCompletionIntegers K) a ∈
              IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  have _em := Classical.em
  rfl
end FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw64T2SpanningFamilyWeld
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw54T2KrasnerGlobalGeneratorTransport
open FLT.Gapsw63T1XjPiSpanningFamily
open FLT.Gapsw63T4ModuleFiniteCarrier
set_option maxHeartbeats 1600000 in

theorem gapsw64_t2_finProd_sum_eq_range_sum {M : Type*} [AddCommMonoid M]
    (g : ℕ → ℕ → M) (e f : ℕ) :
    ∑ q : Fin e × Fin f, g (q.1 : ℕ) (q.2 : ℕ)
      = ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f, g i j := by
  have _em := Classical.em
  rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range f, g i j) e]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun j => g (i : ℕ) j) f
end FLT.Gapsw64T2SpanningFamilyWeld
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw7X1cPerPlaceDiscDecomposition
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "Classical P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Classical"
attribute [local instance] FractionRing.liftAlgebra

theorem gapsw7_x1c_span_three_ne_bot : (Ideal.span {(3 : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  norm_num
end FLT.Gapsw7X1cPerPlaceDiscDecomposition
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw7X1cPerPlaceDiscDecomposition
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "Classical P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Classical"
attribute [local instance] FractionRing.liftAlgebra

theorem gapsw7_x1c_span_three_isPrime : (Ideal.span {(3 : ℤ)} : Ideal ℤ).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three
end FLT.Gapsw7X1cPerPlaceDiscDecomposition
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

set_option autoImplicit false
namespace FLT
namespace Gapsw7X1cPerPlaceDiscDecomposition
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "Classical P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Classical"
attribute [local instance] FractionRing.liftAlgebra

theorem gapsw7_x1c_span_three_isMaximal : (Ideal.span {(3 : ℤ)} : Ideal ℤ).IsMaximal :=
  gapsw7_x1c_span_three_isPrime.isMaximal gapsw7_x1c_span_three_ne_bot
end FLT.Gapsw7X1cPerPlaceDiscDecomposition
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
namespace FLT
namespace Gapsw7X3bDerivativeDifferentSlice
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial nonZeroDivisors"
variable (A K : Type*) {L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable (L) in

theorem gapsw7_x3b_differentIdeal_eq_span_aeval_derivative
    (x : B) (hmono : Algebra.adjoin A {x} = ⊤)
    (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have _em := Classical.em
  have h := conductor_mul_differentIdeal A K L x hx
  rwa [conductor_eq_top_of_adjoin_eq_top hmono, Ideal.top_mul] at h
end FLT.Gapsw7X3bDerivativeDifferentSlice
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

namespace FLT
namespace Gapsw7X3bDerivativeDifferentSlice
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial nonZeroDivisors"
variable (A K : Type*) {L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable (L) in

theorem gapsw7_x3b_adjoin_fractionField_eq_top_of_monogenic
    (x : B) (hmono : Algebra.adjoin A {x} = ⊤) :
    Algebra.adjoin K {algebraMap B L x} = ⊤ := by
  have _em := Classical.em
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hxL : IsIntegral K (algebraMap B L x) := Algebra.IsIntegral.isIntegral _
  have hsub : (IntermediateField.adjoin K {algebraMap B L x}).toSubalgebra
      = Algebra.adjoin K {algebraMap B L x} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxL.isAlgebraic
  have hB : ∀ b : B, algebraMap B L b ∈ IntermediateField.adjoin K {algebraMap B L x} := by
    intro b
    have hb : algebraMap B L b ∈
        (Algebra.adjoin A ({x} : Set B)).map (IsScalarTower.toAlgHom A B L) :=
      Subalgebra.mem_map.mpr ⟨b, by rw [hmono]; exact Algebra.mem_top, rfl⟩
    rw [AlgHom.map_adjoin_singleton] at hb
    have hxmem : (IsScalarTower.toAlgHom A B L) x ∈
        Subalgebra.restrictScalars A
          (IntermediateField.adjoin K {algebraMap B L x}).toSubalgebra := by
      rw [Subalgebra.mem_restrictScalars, IntermediateField.mem_toSubalgebra]
      exact IntermediateField.subset_adjoin K _ (by
        simp [IsScalarTower.coe_toAlgHom'])
    have hle : Algebra.adjoin A ({(IsScalarTower.toAlgHom A B L) x} : Set L) ≤
        Subalgebra.restrictScalars A
          (IntermediateField.adjoin K {algebraMap B L x}).toSubalgebra :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxmem)
    have hmem := hle hb
    rwa [Subalgebra.mem_restrictScalars, IntermediateField.mem_toSubalgebra] at hmem
  rw [Algebra.eq_top_iff]
  intro l
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj (M := B⁰) l
  have hs0 : algebraMap B L (s : B) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hl : l = algebraMap B L b / algebraMap B L (s : B) := by
    rw [eq_div_iff hs0]
    exact hbs
  rw [← hsub, IntermediateField.mem_toSubalgebra, hl]
  exact div_mem (hB b) (hB (s : B))
end FLT.Gapsw7X3bDerivativeDifferentSlice
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

namespace FLT
namespace Gapsw7X3bDerivativeDifferentSlice
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial nonZeroDivisors"
variable (A K : Type*) {L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable (L) in
include K L in

theorem gapsw7_x3b_differentIdeal_eq_span_aeval_derivative_of_monogenic
    (x : B) (hmono : Algebra.adjoin A {x} = ⊤) :
    differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have _em := Classical.em
  exact gapsw7_x3b_differentIdeal_eq_span_aeval_derivative A K L x hmono
    (gapsw7_x3b_adjoin_fractionField_eq_top_of_monogenic A K L x hmono)
end FLT.Gapsw7X3bDerivativeDifferentSlice
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
section
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "mem_primesOverFinset_iff primesOverFinset HeightOneSpectrum.adicCompletion HeightOneSpectrum.adicCompletionIntegers HeightOneSpectrum.ext exists_forall_sub_mem_ideal mk HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "intValuation_exists_uniformizer valuation_of_algebraMap intValuation_le_pow_iff_mem valuedAdicCompletion_eq_valuation adicCompletion_valueGroup_eq isMaximal algebraMap_adicCompletion valuation_lt_one_iff_mem mk asIdeal mem_adicCompletionIntegers comap isPrime adicCompletion valuation coe_mem_adicCompletionIntegers ne_bot under intValuation_le_one adicCompletionIntegers valuedAdicCompletion_surjective irreducible intValuation_if_neg prime intValuation"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
lemma intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]

  rw [intValuation_if_neg _ hnz, Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]
end IsDedekindDomain.HeightOneSpectrum
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
section
variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]
namespace Ideal p2m_export "Ideal" "map_le_iff_le_comap height map_map span_singleton_eq_span_singleton Quotient.eq_zero_iff_mem mem_span_singleton prime_of_isPrime mul_mem_right under_def Quotient.mkₐ Quotient.eq pow_le_pow_right top_mul matrix inertia comap_bot_of_injective IsPrime.ne_top map_span exists_forall_sub_mem_ideal Quotient.maximal_ideal_iff_isField_quotient pow_succ_lt_pow pi sum_mem quotientToQuotientRangePowQuotSucc_injective inertiaDeg_algebraMap Factors.finrank_pow_ramificationIdx quotientToQuotientRangePowQuotSucc Factors.piQuotientEquiv isUnit_iff mem_bot span Factors.ramificationIdx_ne_zero powQuotSuccInclusion_injective span_singleton_eq_bot mul_unit_mem_iff_mem eq_top_of_isUnit_mem LiesOver.over mul_le_left Quotient.algebraQuotientPowRamificationIdx span_singleton_prime quotientToQuotientRangePowQuotSucc_mk powQuotSuccInclusion mul_mem_mul count_associates_factors_eq one_eq_top span_singleton_pow map_quotient_self Factors.isPrime IsMaximal zero_eq_bot Quotient.mk Quotient.field mul_mem_left span_singleton_ne_top quotEquivPowQuotPowSuccEquiv quotEquivOfEq map IsPrime.isMaximal Quotient.isUnit_mk_pow_iff_isUnit_mk quotientMap_injective' bot_pow irreducible_pow_sup_of_ge span_singleton_le_iff_mem quotientEquivAlgOfEq mem_sup_left IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver FG quotientMap Factors.finiteDimensional_quotient_pow Factors.piQuotientLinearEquiv Factors.piQuotientEquiv_mk mul_top ext jacobson Quotient.mk_out Factors.ne_bot le_of_dvd quotientToQuotientRangePowQuotSucc_surjective mem_span_singleton' IsMaximal.eq_of_le LiesOver mem_iInf quotientMap_mk pow_mem_of_mem IsPrime Quotient.mk_eq_mk span_le ramificationIdx' mem_sup_right ResidueField span_singleton_mul_right_unit powQuotPowSuccEquivMapMkPowSuccPow Factors.liesOver span_singleton_mul_left_unit pow_le_self powQuotSuccInclusion_apply_coe ramificationIdx_ne_zero mem_comap IsTwoSided Filtration eq_prime_pow_mul_coprime IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count pow_mem_pow finiteQuotientOfFreeOfNeBot inertiaDeg'_pos under rank_prime_pow_ramificationIdx pow_right_mono inertiaDeg' quotientMulEquivQuotientProd comap Quotient.nontrivial_iff finrank_prime_pow_ramificationIdx Quotient.mk_eq_mk_iff_sub_mem fg_top bot_mul eq_top_iff_one ramificationIdx_mul_inertiaDeg_of_isLocalRing map_eq_bot_iff_of_injective iInf_pow_eq_bot_of_isLocalRing Quotient.mkₐ_eq_mk subset_span pow_right_strictAnti Quotient.algebraQuotientOfRamificationIdxNeZero isCoprime_of_isMaximal ne_bot_of_liesOver_of_ne_bot Quotient.mk_surjective isCoprime_iff_sup_eq Quotient.algebraQuotientOfLEComap map_top mem_span_singleton_self" namespace Quotient p2m_export "Ideal.Quotient" "eq_zero_iff_mem mkₐ maximal_ideal_iff_isField_quotient ring normal algebraQuotientPowRamificationIdx mk isUnit_mk_pow_iff_isUnit_mk factor mk_out lift mk_eq_mk algebra mk_eq_mk_iff_sub_mem mkₐ_eq_mk algebraQuotientOfRamificationIdxNeZero mk_surjective algebraQuotientOfLEComap one" end Ideal.Quotient
p2m_open_scoped "Ideal Ideal.Quotient" in
theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve"

section
variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
namespace IsLocalRing p2m_export "IsLocalRing" "eq_maximalIdeal ResidueField maximalIdeal_le_jacobson of_surjective maximalIdeal maximalIdeal.isMaximal mem_maximalIdeal notMem_maximalIdeal residue_surjective of_injective of_surjective' eq_of_eval_eq_zero_of_not_isUnit_sub residue" end IsLocalRing
p2m_open_scoped "IsLocalRing" in
scoped instance IsLocalRing.quot : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective

p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"

section
section
p2m_open_scoped "IsLocalRing" in
theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"

section
section
variable {F : Type*} [Field F]
namespace ValuationSubring p2m_export "ValuationSubring" "comap subtype mem_comap neg_mem algebraMap_apply ext zero_mem mem_nonunits_iff mk mem_top mul_mem algebraMap_injective add_mem eq_top_iff decompositionSubgroup algebra valuation inclusion" end ValuationSubring
p2m_open_scoped "ValuationSubring" in
theorem ValuationSubring.valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((hv.v.mem_valuationSubring_iff _).1 x.2)
  rw [← Valued.v.map_one (R := K), ← Submonoid.coe_one, ← u.mul_inv, hu,
    Submonoid.coe_mul, Valued.v.map_mul]
  nth_rw 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_right ((hv.v.mem_valuationSubring_iff _).1 (u⁻¹.val.property)) _
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"

section
variable {F : Type*} [Field F]
p2m_open_scoped "ValuationSubring" in
theorem ValuationSubring.isUnit_of_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : Valued.v x.val = 1) : IsUnit x := by
  have : IsUnit x.val := by rw [isUnit_iff_ne_zero, ne_eq, ← map_eq_zero hv.v, hx]; aesop
  obtain ⟨u, hu⟩ := this
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  rw [isUnit_iff_exists]
  exact ⟨⟨u⁻¹.val, hu_inv_le⟩,  ⟨by aesop, by aesop⟩⟩
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"

section
variable {F : Type*} [Field F]
p2m_open_scoped "ValuationSubring" in
theorem ValuationSubring.isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valued_eq_one_of_isUnit x, isUnit_of_valued_eq_one x⟩
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"

section
noncomputable section
p2m_open "PowerSeries P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.PowerSeries HahnSeries P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.HahnSeries Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
namespace ModularCurve
namespace PhiGen
variable {K : Type*} [Field K] [Algebra ℚ K]
variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

scoped instance instNeZeroPhiGenDescentEll : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
end PhiGen
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end ModularCurve
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

noncomputable section
p2m_open "PowerSeries P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.PowerSeries HahnSeries P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.HahnSeries Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
namespace ModularCurve
namespace PhiGen
variable {K : Type*} [Field K] [Algebra ℚ K]
variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
variable (conj : Fin (ℓ + 1) → LaurentSeries K)
variable (ζ : Kˣ) (J : LaurentSeries K)
section Gates

scoped instance instFactPrimeTwoPhiGenDescent : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
end Gates
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end PhiGen
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end ModularCurve
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

section
open AlgebraicCurve
namespace ModularCurve

scoped instance charZero_algebraicClosureRat_layerC : CharZero (AlgebraicClosure ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
end ModularCurve
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

section
set_option autoImplicit false
p2m_open "Module P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Module"
section TraceAdditivity
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
namespace LinearMap
p2m_export "LinearMap" "mem_range comp_id range sub_apply coe_range inverse charpoly_natDegree det_baseChange rank ker_eq_bot range_zero charpoly_prodMap id codRestrict_apply charpoly_monic module isUnit_iff_ker_eq_bot mul_apply' restrict_apply restrict_coe_apply map_span codRestrict inr zero_apply baseChangeHom map_injective trace_comp_comm' charpoly mk diag pi mul proj ext comp isIntegral trace single prodMap comp_assoc baseChange restrictScalars ker inl mem_ker comp_apply subtype_comp_codRestrict trace_conj' mem_range_self restrict isUnit_iff_isUnit_det conjugate charpoly_baseChange"
p2m_open "LinearMap"

theorem trace_eq_trace_restrict_add_trace_mapQ (f : V →ₗ[k] V) {p : Submodule k V}
    (hp : ∀ x ∈ p, f x ∈ p) :
    trace k V f
      = trace k p (f.restrict hp) + trace k (V ⧸ p) (p.mapQ p f fun x hx => hp x hx) := by
  classical

  obtain ⟨s, hs⟩ := Module.projective_lifting_property p.mkQ LinearMap.id p.mkQ_surjective

  have hsplit : trace k V f
      = trace k V ((f ∘ₗ s) ∘ₗ p.mkQ) + trace k V (f - (f ∘ₗ s) ∘ₗ p.mkQ) := by
    rw [map_sub]; ring

  have hQ : trace k V ((f ∘ₗ s) ∘ₗ p.mkQ)
      = trace k (V ⧸ p) (p.mapQ p f fun x hx => hp x hx) := by
    rw [trace_comp_comm']
    congr 1
    rw [← comp_assoc, ← Submodule.mapQ_mkQ, comp_assoc, hs, comp_id]

  have hmemp : ∀ v : V, v - s (p.mkQ v) ∈ p := by
    intro v
    have hmk : p.mkQ (s (p.mkQ v)) = p.mkQ v := by
      have := LinearMap.ext_iff.mp hs (p.mkQ v)
      simpa using this
    have : p.mkQ (v - s (p.mkQ v)) = 0 := by rw [map_sub, hmk, sub_self]
    rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at this
  have hmem : ∀ v : V, (f - (f ∘ₗ s) ∘ₗ p.mkQ) v ∈ p := by
    intro v
    have hval : (f - (f ∘ₗ s) ∘ₗ p.mkQ) v = f (v - s (p.mkQ v)) := by
      simp [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    rw [hval]
    exact hp _ (hmemp v)

  have hP : trace k V (f - (f ∘ₗ s) ∘ₗ p.mkQ) = trace k p (f.restrict hp) := by
    have hfact : f - (f ∘ₗ s) ∘ₗ p.mkQ
        = p.subtype ∘ₗ LinearMap.codRestrict p (f - (f ∘ₗ s) ∘ₗ p.mkQ) hmem :=
      (LinearMap.subtype_comp_codRestrict _ _ _).symm
    rw [hfact, trace_comp_comm']
    congr 1
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx0 : p.mkQ (x : V) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact x.2
    simp [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.sub_apply,
      LinearMap.restrict_coe_apply, hx0]
  rw [hsplit, hQ, hP, add_comm]
end LinearMap
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end TraceAdditivity
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw63T4bWittGhostRingHomUpgrade
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T3TeichmuellerAdditiveCarry
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw63T4ModuleFiniteCarrier

noncomputable def gapsw63_t4b_ringHomOfPack
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (f : WittVector 3 ((𝓞 K) ⧸ v.asIdeal) → v.adicCompletionIntegers K)
    (hone : f 1 = 1)
    (hmul : ∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f (a * b) = f a * f b)
    (hadd : ∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f (a + b) = f a + f b) :
    WittVector 3 ((𝓞 K) ⧸ v.asIdeal) →+* v.adicCompletionIntegers K where
  toFun := f
  map_one' := hone
  map_mul' := hmul
  map_zero' := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  map_add' := hadd
end FLT.Gapsw63T4bWittGhostRingHomUpgrade
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

set_option autoImplicit false
namespace FLT
namespace Gapsw63T4bWittGhostRingHomUpgrade
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T3TeichmuellerAdditiveCarry
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw63T4ModuleFiniteCarrier

noncomputable def gapsw63_t4b_algebraOfPack
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (f : WittVector 3 ((𝓞 K) ⧸ v.asIdeal) → v.adicCompletionIntegers K)
    (hone : f 1 = 1)
    (hmul : ∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f (a * b) = f a * f b)
    (hadd : ∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f (a + b) = f a + f b) :
    Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K) :=
  (gapsw63_t4b_ringHomOfPack K v f hone hmul hadd).toAlgebra
end FLT.Gapsw63T4bWittGhostRingHomUpgrade
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

set_option autoImplicit false
namespace FLT
namespace Gapsw63T4bWittGhostRingHomUpgrade
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T3TeichmuellerAdditiveCarry
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw63T4ModuleFiniteCarrier
set_option maxHeartbeats 1600000 in

theorem gapsw63_t4b_algebraOfPack_algebraMap
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (f : WittVector 3 ((𝓞 K) ⧸ v.asIdeal) → v.adicCompletionIntegers K)
    (hone : f 1 = 1)
    (hmul : ∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f (a * b) = f a * f b)
    (hadd : ∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f (a + b) = f a + f b)
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) :
    @algebraMap _ _ _ _ (gapsw63_t4b_algebraOfPack K v f hone hmul hadd) a
      = f a := by
  have _em := Classical.em
  rfl
end FLT.Gapsw63T4bWittGhostRingHomUpgrade
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T9GlobalPrimitiveDerivWire
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.FLT.Gapsw48T5CompletionTransportCarrierSlices"
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"

theorem gapsw78_t9_exists_integral_primitive_element
    (K : Type) [Field K] [NumberField K] :
    ∃ ξ : 𝓞 K, Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤ := by
  have _em := Classical.em
  classical

  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K

  have hαalg : IsAlgebraic ℚ α := Algebra.IsAlgebraic.isAlgebraic α
  have hadj : Algebra.adjoin ℚ {α} = (⊤ : Subalgebra ℚ K) := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαalg
    rw [hα, IntermediateField.top_toSubalgebra] at this
    exact this.symm

  have hαalgZ : IsAlgebraic ℤ α := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr hαalg

  obtain ⟨n, hn, hint⟩ := hαalgZ.exists_integral_multiple

  refine ⟨⟨n • α, hint⟩, ?_⟩

  show Algebra.adjoin ℚ {(n • α : K)} = ⊤
  refine top_le_iff.mp (hadj ▸ Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_))
  have heq : (n : ℚ)⁻¹ • (n • α : K) = α := by
    rw [show (n • α : K) = (n : ℚ) • α from (Int.cast_smul_eq_zsmul ℚ n α).symm,
      smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hn), one_smul]
  have hmem : (n : ℚ)⁻¹ • (n • α : K)
      ∈ Algebra.adjoin ℚ ({(n • α : K)} : Set K) :=
    SMulMemClass.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _))
  rw [heq] at hmem; exact hmem
end FLT.Gapsw78T9GlobalPrimitiveDerivWire
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T9GlobalPrimitiveDerivWire
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.FLT.Gapsw48T5CompletionTransportCarrierSlices"
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"
set_option maxHeartbeats 6400000 in

theorem gapsw78_t9_pieceIResidual_of_globalDerivVal
    (hGlobalDerivVal :
      ∀ (K : Type) [Field K] [NumberField K]
        (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        v.asIdeal ∈ IsDedekindDomain.primesOverFinset
          (Ideal.span {(3 : ℤ)}) (𝓞 K) →
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal →
        ∃ ξ : 𝓞 K, Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤ ∧
          ¬ Valued.v ((Polynomial.aeval ξ
                (Polynomial.derivative (minpoly ℤ ξ)) : 𝓞 K)
              : v.adicCompletion K) ≤
            WithZero.exp (-(((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal
              + (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal
                * padicValNat 3
                  ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) :
                    ℕ) : ℤ))) :
    Gapsw48T5CompletionTransportPieceIResidual := by
  have _em := Classical.em
  rw [gapsw48_t5_pieceIResidual_pin]
  intro K _ _ v hv hwild
  obtain ⟨ξ, hadj, hval⟩ := hGlobalDerivVal K v hv hwild
  exact ⟨Polynomial.aeval ξ (Polynomial.derivative (minpoly ℤ ξ)),
    aeval_derivative_mem_differentIdeal ℤ ℚ K ξ hadj, hval⟩
end FLT.Gapsw78T9GlobalPrimitiveDerivWire
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

section

namespace FLT
namespace Gapsw58T5WittASideEngineAtoms

p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"

theorem gapsw58_t5_three_mem_residue_prime
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    (3 : 𝓞 K) ∈ v.asIdeal := by
  have _em := Classical.em
  haveI := FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff
    FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot] at h1
  obtain ⟨-, hlies⟩ := h1
  have h3 : (3 : ℤ) ∈ Ideal.span {(3 : ℤ)} := Ideal.mem_span_singleton_self 3
  rw [hlies.over, Ideal.under_def, Ideal.mem_comap] at h3
  rwa [map_ofNat] at h3

theorem gapsw58_t5_residue_field_finite
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Finite ((𝓞 K) ⧸ v.asIdeal) := by
  have _em := Classical.em
  exact v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot

theorem gapsw58_t5_residue_isMaximal
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.IsMaximal := by
  have _em := Classical.em
  exact v.isPrime.isMaximal v.ne_bot

theorem gapsw58_t5_residue_charP_three
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    CharP ((𝓞 K) ⧸ v.asIdeal) 3 := by
  have _em := Classical.em
  have hmem : (3 : 𝓞 K) ∈ v.asIdeal := gapsw58_t5_three_mem_residue_prime K v h1
  haveI : Nontrivial ((𝓞 K) ⧸ v.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  have h30 : ((3 : ℕ) : (𝓞 K) ⧸ v.asIdeal) = 0 := by
    rw [Nat.cast_ofNat, ← map_ofNat (Ideal.Quotient.mk v.asIdeal) 3]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h30

theorem gapsw58_t5_residue_perfectRing_three
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    ∃ _ : CharP ((𝓞 K) ⧸ v.asIdeal) 3, PerfectRing ((𝓞 K) ⧸ v.asIdeal) 3 := by
  have _em := Classical.em
  haveI hch : CharP ((𝓞 K) ⧸ v.asIdeal) 3 := gapsw58_t5_residue_charP_three K v h1
  haveI : Finite ((𝓞 K) ⧸ v.asIdeal) := gapsw58_t5_residue_field_finite K v
  haveI := v.isPrime
  exact ⟨hch, inferInstance⟩

set_option maxHeartbeats 1600000 in

theorem gapsw58_t5_witt_dvr_irreducible_bundle
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (_hwild : 3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) :
    ∃ (_ : IsDomain (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)))
      (_ : IsDiscreteValuationRing (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))),
      Irreducible (3 : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) := by
  have _em := Classical.em
  haveI hmax : v.asIdeal.IsMaximal := gapsw58_t5_residue_isMaximal K v
  haveI hch : CharP ((𝓞 K) ⧸ v.asIdeal) 3 := gapsw58_t5_residue_charP_three K v h1
  haveI hfin : Finite ((𝓞 K) ⧸ v.asIdeal) := gapsw58_t5_residue_field_finite K v
  letI : Field ((𝓞 K) ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  refine ⟨inferInstance, inferInstance, ?_⟩
  have h := WittVector.irreducible 3 (k := (𝓞 K) ⧸ v.asIdeal)
  rwa [Nat.cast_ofNat] at h

end FLT.Gapsw58T5WittASideEngineAtoms
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw46T5WildDifferentEisensteinLink2a
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "IsDiscreteValuationRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDiscreteValuationRing"
open FLT.Gapsw45T4WildDifferentEisensteinLink1
open FLT.Gapsw7X3bDerivativeDifferentSlice
section EvalBridge
set_option maxHeartbeats 1600000 in

theorem gapsw46_t5_eval_map_derivative_eq_aeval {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (x : S) (p : Polynomial R) :
    Polynomial.eval x (Polynomial.derivative (p.map (algebraMap R S)))
      = Polynomial.aeval x (Polynomial.derivative p) := by
  have _em := Classical.em
  rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def]
end EvalBridge
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end FLT.Gapsw46T5WildDifferentEisensteinLink2a
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

set_option autoImplicit false
namespace FLT
namespace Gapsw46T5WildDifferentEisensteinLink2a
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "IsDiscreteValuationRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDiscreteValuationRing"
open FLT.Gapsw45T4WildDifferentEisensteinLink1
open FLT.Gapsw7X3bDerivativeDifferentSlice
variable (A K : Type*) {L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
section DVR
variable [IsDiscreteValuationRing B]
variable (L) in
set_option maxHeartbeats 1600000 in

theorem gapsw46_t5_pow_mem_differentIdeal
    (π : B) (hπ : Irreducible π)
    (hx : Algebra.adjoin K {algebraMap B L π} = ⊤)
    (e : ℕ) (he0 : 0 < e)
    (hdeg : ((minpoly A π).map (algebraMap A B)).natDegree = e)
    (hcv : ∀ i : ℕ, i + 1 < e →
      ((minpoly A π).map (algebraMap A B)).coeff (i + 1) * ((i : B) + 1) = 0 ∨
      ∃ (u : Bˣ) (k : ℕ),
        ((minpoly A π).map (algebraMap A B)).coeff (i + 1) * ((i : B) + 1)
          = (u : B) * π ^ (e * k))
    (ue : Bˣ) (ke : ℕ) (heB : ((e : ℕ) : B) = (ue : B) * π ^ (e * ke)) :
    π ^ (e - 1 + e * ke) ∈ differentIdeal A B := by
  have _em := Classical.em
  have hAx : IsIntegral A π := IsIntegralClosure.isIntegral A L π
  have hmonic : ((minpoly A π).map (algebraMap A B)).Monic :=
    (minpoly.monic hAx).map _
  have hceil := gapsw45_t4_addVal_eval_derivative_le π hπ
    ((minpoly A π).map (algebraMap A B)) e he0 hdeg hmonic hcv ue ke heB
  rw [gapsw46_t5_eval_map_derivative_eq_aeval π (minpoly A π)] at hceil
  have hdvd : aeval π (derivative (minpoly A π)) ∣ π ^ (e - 1 + e * ke) :=
    addVal_le_iff_dvd.mp (by rw [hπ.addVal_pow]; exact hceil)
  have hle : Ideal.span {aeval π (derivative (minpoly A π))} ≤ differentIdeal A B :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (aeval_derivative_mem_differentIdeal A K L π hx))
  exact hle (Ideal.mem_span_singleton.mpr hdvd)
end DVR
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end FLT.Gapsw46T5WildDifferentEisensteinLink2a
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

set_option autoImplicit false
namespace FLT
namespace Gapsw46T5WildDifferentEisensteinLink2a
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "IsDiscreteValuationRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDiscreteValuationRing"
open FLT.Gapsw45T4WildDifferentEisensteinLink1
open FLT.Gapsw7X3bDerivativeDifferentSlice
variable (A K : Type*) {L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
section DVR
variable [IsDiscreteValuationRing B]
variable (L) in
include K L in
set_option maxHeartbeats 1600000 in

theorem gapsw46_t5_pow_mem_differentIdeal_of_monogenic
    (π : B) (hπ : Irreducible π)
    (hmono : Algebra.adjoin A {π} = ⊤)
    (e : ℕ) (he0 : 0 < e)
    (hdeg : ((minpoly A π).map (algebraMap A B)).natDegree = e)
    (hcv : ∀ i : ℕ, i + 1 < e →
      ((minpoly A π).map (algebraMap A B)).coeff (i + 1) * ((i : B) + 1) = 0 ∨
      ∃ (u : Bˣ) (k : ℕ),
        ((minpoly A π).map (algebraMap A B)).coeff (i + 1) * ((i : B) + 1)
          = (u : B) * π ^ (e * k))
    (ue : Bˣ) (ke : ℕ) (heB : ((e : ℕ) : B) = (ue : B) * π ^ (e * ke)) :
    π ^ (e - 1 + e * ke) ∈ differentIdeal A B := by
  have _em := Classical.em
  exact gapsw46_t5_pow_mem_differentIdeal A K L π hπ
    (gapsw7_x3b_adjoin_fractionField_eq_top_of_monogenic A K L π hmono)
    e he0 hdeg hcv ue ke heB
end DVR
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
end FLT.Gapsw46T5WildDifferentEisensteinLink2a
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

section
/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/

section

p2m_open "Multiplicative P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Multiplicative WithZero P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.WithZero"

p2m_open_scoped "Topology P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Topology"

namespace Valued
p2m_export "Valued" "is_topological_valuation isClosed_integer mk mk' v hasBasis_uniformity integer valuedCompletion_apply extension integer.finite_quotient_maximalIdeal_pow_of_finite_residueField exists_pow_lt_of_le_exp_neg_one isClosed_valuationSubring mem_nhds ResidueField maximalIdeal isOpen_valuationSubring"
namespace WithZeroMulInt
p2m_open "Valued"

variable {K : Type*} [Field K] [hv : Valued K ℤᵐ⁰]

theorem irreducible_valuation_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : v ϖ.1 < 1 := by
  have := mt (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 h.not_isUnit
  exact lt_of_le_of_ne (Valuation.mem_integer_iff _ _ |>.1 ϖ.2) this

theorem irreducible_valuation_le_ofAdd_neg_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v ϖ.1 ≤ ofAdd (-1 : ℤ) := by
  letI := (lt_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])).1 (irreducible_valuation_lt_one h)
  rw [le_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])]
  omega

theorem mem_maximalIdeal_pow_valuation [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} {n : ℕ} (hx : x ∈ 𝓂[K] ^ n) {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v x.val ≤ v ϖ.1 ^ n := by
  by_cases hx₀ : x = 0
  · simp [hx₀]
  · simp_rw [h.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    let ⟨y, hy⟩ := hx
    simp only [hy, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ge_iff_le]
    exact le_trans (mul_le_of_le_one_right' <| (Valuation.mem_integer_iff _ _).1 y.2) le_rfl

lemma finite_quotient_maximalIdeal_pow_of_finite_residueField {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsDiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      Finite.of_ideal_quotient
        (I := Ideal.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

theorem finite_cover_of_uniformity_basis [IsDiscreteValuationRing 𝒪[K]] (γ : ℤᵐ⁰ˣ)
    (h : Finite 𝓀[K]) :
    ∃ t : Set K, Set.Finite t ∧
      (𝒪[K]).carrier ⊆ ⋃ y ∈ t, { x | (x, y) ∈ { p | v (p.2 - p.1) < γ.val } } := by
  classical
  let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let ⟨m, hm⟩ := exists_pow_lt_of_le_exp_neg_one (irreducible_valuation_le_ofAdd_neg_one hϖ) γ
  letI := finite_quotient_maximalIdeal_pow_of_finite_residueField h m
  have h := Fintype.ofFinite (𝒪[K] ⧸ 𝓂[K] ^ m)
  let T := Subtype.val '' (h.elems.image Quotient.out : Set 𝒪[K])
  refine ⟨T, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Ideal.Quotient.mk (𝓂[K] ^ m) ⟨x, hx⟩).out
  refine ⟨y, Set.mem_image_of_mem _ <| Finset.mem_image_of_mem Quotient.out (h.complete _),
    lt_of_le_of_lt (mem_maximalIdeal_pow_valuation (Ideal.Quotient.out_sub _ _) hϖ) hm⟩

variable (K)

open _root_.Valuation.IsRankOneDiscrete _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Valuation.IsRankOneDiscrete in

theorem integer_compactSpace [CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]]
    [hv.v.IsRankOneDiscrete] (h : Finite 𝓀[K]) (hsurj : Function.Surjective hv.v) :
    CompactSpace 𝒪[K] where
  isCompact_univ := by
    refine isCompact_iff_isCompact_univ.1 <| isCompact_iff_totallyBounded_isComplete.2
      ⟨(hasBasis_uniformity _ _).totallyBounded_iff.2 fun γ _ ↦ ?_, (isClosed_integer K).isComplete⟩
    obtain ⟨t, htf, ht⟩ := finite_cover_of_uniformity_basis
      (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt v).toMulEquiv γ) h
    refine ⟨t, htf, ht.trans fun x hx ↦ ?_⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hit, hi⟩ := hx
    use i, hit
    rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
      valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj]
    simpa using hi

end Valued.WithZeroMulInt
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

section
/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/

section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "mem_primesOverFinset_iff primesOverFinset HeightOneSpectrum.adicCompletion HeightOneSpectrum.adicCompletionIntegers HeightOneSpectrum.ext exists_forall_sub_mem_ideal mk HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "intValuation_exists_uniformizer valuation_of_algebraMap intValuation_le_pow_iff_mem valuedAdicCompletion_eq_valuation adicCompletion_valueGroup_eq isMaximal algebraMap_adicCompletion valuation_lt_one_iff_mem mk asIdeal mem_adicCompletionIntegers comap isPrime adicCompletion valuation coe_mem_adicCompletionIntegers ne_bot under intValuation_le_one adicCompletionIntegers valuedAdicCompletion_surjective irreducible intValuation_if_neg prime intValuation"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"

section Multiplicative

p2m_open_scoped "WithZero P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.WithZero"
lemma exists_ofAdd_natCast_of_le_one {x : ℤᵐ⁰} (hx : x ≠ 0) (hx' : x ≤ 1) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  lift x to Multiplicative ℤ using hx
  norm_cast at hx'
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos hx')
  use k
  rw [← hk, Int.neg_neg]
  rfl

end Multiplicative
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen"

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

lemma ne_zero_of_some_le_intValuation {a : A} {m : Multiplicative ℤ} (h : m ≤ v.intValuation a)
    : a ≠ 0 := by
  rintro rfl
  simp at h

lemma emultiplicity_eq_of_valuation_eq_ofAdd {a : A} {k : ℕ}
    (hv : v.intValuation a = (Multiplicative.ofAdd (-(k : ℤ)))) :
    emultiplicity v.asIdeal (Ideal.span {a}) = k := by
  classical
  have hnz : a ≠ 0 := ne_zero_of_some_le_intValuation _ (le_of_eq hv.symm)
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  simp only [intValuation_if_neg _ hnz, WithZero.exp, ofAdd_neg, WithZero.coe_inv, inv_inj,
    WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq, Nat.cast_inj] at hv
  rw [← hv, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb,
    Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot, normalize_eq]

lemma exists_adicValued_mul_sub_le {a b : A} {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    (hle : γ ≤ v.intValuation a)
    (hle' : v.intValuation b ≤ v.intValuation a) :
    ∃ y, v.intValuation (y * a - b) ≤ γ := by

  have hγ' : γ ≤ 1 := by
    apply hle.trans
    apply intValuation_le_one
  obtain ⟨n, hn⟩ := exists_ofAdd_natCast_of_le_one hγ hγ'
  rw [← hn, ← WithZero.exp] at hle ⊢
  have hnz : a ≠ 0 := ne_zero_of_some_le_intValuation _ hle
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]

  rw [intValuation_eq_coe_neg_multiplicity _ hnz, WithZero.exp_le_exp, neg_le_neg_iff,
    Int.ofNat_le] at hle
  have hm : emultiplicity v.asIdeal (Ideal.span {a}) ≤ n :=
    le_of_eq_of_le
      (emultiplicity_eq_of_valuation_eq_ofAdd v <| intValuation_eq_coe_neg_multiplicity v hnz)
      (ENat.coe_le_coe.mpr hle)
  have hb : b ∈ v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
    rwa [← intValuation_le_pow_iff_mem, ← intValuation_eq_coe_neg_multiplicity _ hnz]

  rw [← Ideal.irreducible_pow_sup_of_ge hnb (irreducible v) n hm] at hb

  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  use y

  rwa [hy, ← hxz, sub_add_cancel_right, intValuation_le_pow_iff_mem, neg_mem_iff]

open _root_.MonoidWithZeroHom _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.MonoidWithZeroHom in
lemma exists_adicValued_sub_lt_of_adicValued_le_one {x : (WithVal (v.valuation K))}
    (γ : ((WithZero (Multiplicative ℤ)))ˣ) (hx : Valued.v x ≤ 1) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by

  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A) x
  dsimp only at hnd

  have hnd' := congr_arg Valued.v hnd
  simp only [map_mul] at hnd'
  have hge : Valued.v ((algebraMap A (WithVal (v.valuation K))) d) ≥
      Valued.v ((algebraMap A (WithVal (v.valuation K))) n) :=
    calc Valued.v ((algebraMap A (WithVal (v.valuation K))) d)
          ≥ (valuation K v) x.ofVal *
            (valuation K v) ((algebraMap A (WithVal (v.valuation K))) d).ofVal :=
                mul_le_of_le_one_left' hx
        _ = Valued.v ((algebraMap A (WithVal (v.valuation K))) n) := hnd'
  simp only [ge_iff_le, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hge
  simp only [valuation_of_algebraMap] at hge
  have hdz : (algebraMap A (WithVal (v.valuation K)) d) ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ (fun _ ↦ id) hd

  have hv : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hdz
  let hu : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) * γ.val ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨hv, γ.ne_zero⟩
  obtain ⟨γ', hγ, hγu, hγv⟩ := WithZero.exists_ne_zero_and_lt_and_lt hu hv
  simp only [WithVal.algebraMap_right_apply, WithVal.valued_toVal, valuation_of_algebraMap] at hγv

  obtain ⟨a, hval⟩ := exists_adicValued_mul_sub_le v hγ hγv.le hge
  use a
  rw [← eq_div_iff_mul_eq hdz] at hnd
  rw [adicCompletion.valuedAdicCompletion_def, ← adicCompletion.equiv_apply, map_sub,
    adicCompletion.equiv_apply, adicCompletion.equiv_apply,
    adicCompletion.toCompletion_ofCompletion, adicCompletion.toCompletion_ofCompletion,
    ← UniformSpace.Completion.coe_sub, Valued.extensionValuation_apply_coe, hnd, sub_div' hdz,
    map_div₀]
  rw [← Valuation.pos_iff Valued.v, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hdz
  simp only [WithVal.algebraMap_right_apply, WithVal.equiv_symm_apply,
    ← WithVal.toVal_mul, ← WithVal.toVal_sub, WithVal.valued_toVal, ← map_mul, ← map_sub] at hγu ⊢
  rw [div_lt_iff₀' hdz, valuation_of_algebraMap]
  exact lt_of_le_of_lt hval hγu

p2m_open_scoped "WithZero P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.WithZero"

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

scoped instance : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

open _root_.Valuation.IsRankOneDiscrete _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Valuation.IsRankOneDiscrete in

theorem closureAlgebraMapIntegers_eq_integers :
    closure (algebraMap A (v.adicCompletion K)).range =
    SetLike.coe (v.adicCompletionIntegers K) := by
  apply subset_antisymm

  · apply closure_minimal _ (Valued.isClosed_valuationSubring _)
    rintro b ⟨a, rfl⟩
    exact coe_mem_adicCompletionIntegers v a

  · let f := fun (k : WithVal (v.valuation K)) => (k : v.adicCompletion K)
    suffices h : closure (f '' (f ⁻¹' (adicCompletionIntegers K v))) ⊆
        closure (algebraMap A (adicCompletion K v)).range by
      apply Set.Subset.trans _ h
      exact DenseRange.subset_closure_image_preimage_of_isOpen
        ((adicCompletion.ofCompletion_surjective K v).denseRange.comp
          UniformSpace.Completion.denseRange_coe (adicCompletion.continuous_ofCompletion K v))
        (Valued.isOpen_valuationSubring _)

    apply closure_minimal _ isClosed_closure
    rintro k ⟨x, hx, rfl⟩
    unfold f at hx
    rw [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers,
        adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply] at hx
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Valued.mem_nhds] at hU
    obtain ⟨γ, hγ⟩ := hU
    let γ' := Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt _).toMulEquiv γ
    obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicValued_le_one K v γ' hx
    use algebraMap A K a
    constructor
    · use a
      rfl
    · apply hγ
      simp only [sub_zero, WithVal.equiv_symm_apply, Set.mem_setOf_eq]
      rwa [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (valuedAdicCompletion_surjective K v)]

open _root_.Valuation.IsRankOneDiscrete _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Valuation.IsRankOneDiscrete in

theorem exists_adicValued_sub_lt_of_adicCompletionInteger
    (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  have h := closureAlgebraMapIntegers_eq_integers K v
  rw [Set.ext_iff] at h
  specialize h x
  simp_rw [RingHom.coe_range, Subtype.coe_prop, iff_true, mem_closure_iff_nhds] at h
  specialize h { y | Valued.v (y  - (x : v.adicCompletion K)) < γ.val }
  have hn : {y | Valued.v (y - (x : v.adicCompletion K)) < γ.val} ∈ nhds x.val := by
    rw [Valued.mem_nhds]
    use (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv).symm γ
    have hsurj := (valuedAdicCompletion_surjective K v)
    intro y hy
    have hy' := (valueGroup₀_equiv_withZeroMulInt_strictMono vK) hy
    rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj] at hy'
    refine lt_of_lt_of_eq hy' ?_
    exact MulEquiv.apply_symm_apply (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv _
  obtain ⟨z, ⟨hz, a, ha⟩⟩ := h hn
  use a
  rw [algebraMap_adicCompletion, Function.comp_apply] at ha
  rwa [ha]

private noncomputable abbrev _root_.IsDedekindDomain.HeightOneSpectrum.completionIdeal : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (adicCompletionIntegers K v)

p2m_export "IsDedekindDomain.HeightOneSpectrum" "completionIdeal"
lemma mem_completionIdeal_iff (x : v.adicCompletionIntegers K) :
    x ∈ completionIdeal K v ↔ Valued.v x.val < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

lemma algebraMap_completionIntegers (x : A) :
    (algebraMap A (v.adicCompletionIntegers K) x) = (algebraMap A (v.adicCompletion K) x) :=
  rfl

scoped instance : (v.completionIdeal K).LiesOver v.asIdeal where
  «over» := by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]

open _root_.IsLocalRing _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing in

noncomputable def ResidueFieldToCompletionResidueField :
    A ⧸ v.asIdeal →+* ResidueField (v.adicCompletionIntegers K) :=
  Ideal.quotientMap _ (algebraMap _ _) <| le_of_eq Ideal.LiesOver.over

open _root_.IsLocalRing _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing in
theorem s18_resField_inj :
    Function.Injective (ResidueFieldToCompletionResidueField K v) :=
  Ideal.quotientMap_injective' <| ge_of_eq Ideal.LiesOver.over

set_option maxHeartbeats 1600000 in
open _root_.IsLocalRing _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing in
theorem s18_resField_surj :
    Function.Surjective (ResidueFieldToCompletionResidueField K v) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal (v.adicCompletionIntegers K)) z
  obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicCompletionInteger K v y 1
  refine ⟨Ideal.Quotient.mk v.asIdeal a, ?_⟩
  change Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K))
      (algebraMap A (v.adicCompletionIntegers K) a) = Ideal.Quotient.mk _ y
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  show _ ∈ completionIdeal K v
  rw [mem_completionIdeal_iff]
  exact ha

open _root_.IsLocalRing _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing in

noncomputable def ResidueFieldEquivCompletionResidueField :
    A ⧸ v.asIdeal ≃+* ResidueField (v.adicCompletionIntegers K) :=
  RingEquiv.ofBijective (ResidueFieldToCompletionResidueField K v)
    ⟨s18_resField_inj K v, s18_resField_surj K v⟩

namespace adicCompletion
p2m_open "IsDedekindDomain.HeightOneSpectrum.adicCompletion"

open scoped algebraMap in
theorem exists_uniformizer (v : HeightOneSpectrum A) :
    ∃ π : v.adicCompletionIntegers K, Valued.v π.1 = Multiplicative.ofAdd (- 1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  use π
  rw [← WithZero.exp, ← hπ, ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]

variable {K} in
theorem uniformizer_ne_zero {v : HeightOneSpectrum A}
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    π ≠ 0 := by
  contrapose! hπ
  simp [hπ]

set_option backward.isDefEq.respectTransparency false in
variable {K} in
open scoped _root_.Multiplicative _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Multiplicative in
theorem uniformizer_not_isUnit {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬IsUnit (π : v.adicCompletionIntegers K) := by
  rw [ValuationSubring.isUnit_iff_valued_eq_one, ← WithZero.coe_one, ← ofAdd_zero, hπ]
  apply ne_of_lt
  rw [WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
  omega

theorem eq_pow_uniformizer_mul_unit {x : v.adicCompletionIntegers K} (hx : x ≠ 0)
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π ^ n * u := by
  have hx' : Valued.v x.1 ≠ 0 := by simp [hx]
  let m := - Multiplicative.toAdd (WithZero.unzero hx')
  have hm₀ : 0 ≤ m := by
    simp_rw [m, Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le]
    rw [← WithZero.coe_le_coe]; exact (WithZero.coe_unzero _).symm ▸ x.2
  have hpow : Valued.v (π ^ (-m) * x.val) = 1 := by
    rw [Valued.v.map_mul, map_zpow₀, hπ, ofAdd_neg, WithZero.coe_inv,
      inv_zpow', neg_neg, ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd,
      WithZero.coe_inv, WithZero.coe_unzero, inv_mul_cancel₀ hx']
  let a : v.adicCompletionIntegers K := ⟨π ^ (-m) * x.val, le_of_eq hpow⟩
  refine ⟨m.toNat, (ValuationSubring.isUnit_of_valued_eq_one a hpow).unit, Subtype.ext ?_⟩
  simp only [zpow_neg, IsUnit.unit_spec, MulMemClass.coe_mul, SubmonoidClass.coe_pow, a,
    ← zpow_natCast, m.toNat_of_nonneg hm₀, ← mul_assoc]
  rw [mul_inv_cancel₀ (zpow_ne_zero _ <| (by simp [uniformizer_ne_zero hπ])), one_mul]

open scoped algebraMap in
theorem maximalIdeal_eq_span_uniformizer {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {(π : v.adicCompletionIntegers K)} := by
  refine (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.span_singleton_ne_top (uniformizer_not_isUnit v hπ)) (fun x hx => ?_)
  by_cases hx₀ : x = 0
  · simp only [hx₀, Ideal.zero_mem]
  · obtain ⟨n, ⟨u, hu⟩⟩ := eq_pow_uniformizer_mul_unit K v hx₀ hπ
    have hn : ¬(IsUnit x) := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
    replace hn : n ≠ 0 := fun h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
    simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self π hn

scoped instance : Ring.DimensionLEOne (v.adicCompletionIntegers K) where
  maximalOfPrime {𝔭} h𝔭_ne_bot h𝔭_prime := by
    let ⟨x, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭_ne_bot
    let ⟨π, hπ⟩ := exists_uniformizer K v
    obtain ⟨n, ⟨u, rfl⟩⟩ := eq_pow_uniformizer_mul_unit K v hx.2 hπ
    simp only [Units.isUnit, Ideal.mul_unit_mem_iff_mem, ne_eq, mul_eq_zero, pow_eq_zero_iff',
      Units.ne_zero, or_false, not_and, Decidable.not_not] at hx
    by_cases hn : n = 0
    · simp only [hn, pow_zero, ← 𝔭.eq_top_iff_one, implies_true, and_true] at hx
      exact h𝔭_prime.ne_top hx |>.elim
    · rw [h𝔭_prime.pow_mem_iff_mem n (by omega), ← 𝔭.span_singleton_le_iff_mem,
        ← maximalIdeal_eq_span_uniformizer K v hπ] at hx
      exact IsLocalRing.maximalIdeal_le h𝔭_prime.ne_top hx.1

open scoped algebraMap in
scoped instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  apply IsPrincipalIdealRing.of_prime
  intro P hP
  by_cases hP_bot : P = ⊥
  · exact hP_bot ▸ bot_isPrincipal
  · let ⟨π, hπ⟩ := exists_uniformizer K v
    use π
    rw [IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_bot)]
    exact maximalIdeal_eq_span_uniformizer K v hπ

scoped instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    let ⟨π, hπ⟩ := exists_uniformizer K v
    rw [maximalIdeal_eq_span_uniformizer K v hπ]
    intro h
    simp only [Ideal.span_singleton_eq_bot] at h
    exact uniformizer_ne_zero hπ h

open scoped _root_.Valued _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Valued in
scoped instance : IsDiscreteValuationRing (𝒪[v.adicCompletion K]) :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))

lemma mem_completionIdeal_pow {n : ℕ} (x : v.adicCompletionIntegers K) :
    x ∈ (v.completionIdeal K) ^ n ↔ Valued.v x.val ≤ ↑(Multiplicative.ofAdd (-(n : ℤ))) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  unfold completionIdeal
  rw [maximalIdeal_eq_span_uniformizer K v hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hvalπ_pow : (Valued.v π.val) ^ n = (Multiplicative.ofAdd (-n : ℤ)) := by
    rw [hπ]
    norm_num
    norm_cast
    rw [← ofAdd_nsmul, Nat.smul_one_eq_cast]
  constructor
  · rintro ⟨a, rfl⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ofAdd_neg,
      WithZero.coe_inv]
    apply mul_le_of_le_one_of_le a.prop <| le_of_eq hvalπ_pow
  · intro hx
    set a := x.val / (π ^ n) with ha'
    have ha : Valued.v a ≤ 1 := by
      rwa [ha', Valuation.map_div, Valuation.map_pow, hvalπ_pow,
        div_le_one₀ (WithZero.zero_lt_coe _)]
    use ⟨a, ha⟩
    apply Subtype.val_injective
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, ha']
    rw [div_mul_eq_mul_div₀, mul_div_cancel_right₀]
    apply pow_ne_zero n
    norm_cast
    exact uniformizer_ne_zero hπ

end adicCompletion
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion"

end IsDedekindDomain.HeightOneSpectrum
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw37T1TameTraceFiltrationEngine
p2m_open "Module P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Module"
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)
local notation "e" => Ideal.ramificationIdx' p P
set_option maxHeartbeats 3200000 in

theorem gapsw37_t1_trace_quotient_pow_ramificationIdx_eq_nsmul
    [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    [NeZero e] [FiniteDimensional (R ⧸ p) (S ⧸ P ^ e)] (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk (P ^ e) x)
      = e • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
  classical

  let TI : ∀ I : Ideal (S ⧸ P ^ e), I →ₗ[R ⧸ p] I := fun I =>
    { toFun := fun w => ⟨Ideal.Quotient.mk (P ^ e) x * (w : S ⧸ P ^ e),
        I.mul_mem_left _ w.2⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp [mul_add]
      map_smul' := fun c a => by
        apply Subtype.ext
        simp }
  have TI_coe : ∀ (I : Ideal (S ⧸ P ^ e)) (w : I),
      ((TI I w : I) : S ⧸ P ^ e) = Ideal.Quotient.mk (P ^ e) x * (w : S ⧸ P ^ e) :=
    fun I w => rfl

  let coeI : ∀ I : Ideal (S ⧸ P ^ e), I →ₗ[R ⧸ p] S ⧸ P ^ e := fun I =>
    { toFun := fun w => (w : S ⧸ P ^ e)
      map_add' := fun a b => rfl
      map_smul' := fun c a => Submodule.coe_smul_of_tower c a }
  have coeTI : ∀ (I : Ideal (S ⧸ P ^ e)) (w : I),
      coeI I (TI I w) = Ideal.Quotient.mk (P ^ e) x * coeI I w := fun I w => rfl
  have lmul_appE : ∀ z w : S ⧸ P ^ e,
      Algebra.lmul (R ⧸ p) (S ⧸ P ^ e) z w = z * w := fun z w => by
    simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  have lmul_appP : ∀ z w : S ⧸ P,
      Algebra.lmul (R ⧸ p) (S ⧸ P) z w = z * w := fun z w => by
    simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']

  have hfdI : ∀ I : Ideal (S ⧸ P ^ e), FiniteDimensional (R ⧸ p) I := fun I =>
    FiniteDimensional.of_injective (coeI I) fun a b hab => Subtype.ext hab

  have hcommA : ∀ (j : ℕ) (u : Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (j + 1))),
      TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j)) (Ideal.powQuotSuccInclusion p P j u)
        = Ideal.powQuotSuccInclusion p P j
            (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (j + 1))) u) := by
    intro j u
    apply Subtype.ext
    simp only [TI_coe, Ideal.powQuotSuccInclusion_apply_coe]

  have hinv : ∀ j : ℕ, ∀ v ∈ LinearMap.range (Ideal.powQuotSuccInclusion p P j),
      TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j)) v
        ∈ LinearMap.range (Ideal.powQuotSuccInclusion p P j) := by
    intro j v hv
    obtain ⟨u, rfl⟩ := hv
    exact ⟨TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (j + 1))) u, (hcommA j u).symm⟩

  have htraceA : ∀ j : ℕ,
      LinearMap.trace (R ⧸ p) (LinearMap.range (Ideal.powQuotSuccInclusion p P j))
          ((TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j))).restrict (hinv j))
        = LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (j + 1)))
            (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (j + 1)))) := by
    intro j
    have hconj : (LinearEquiv.ofInjective (Ideal.powQuotSuccInclusion p P j)
          (Ideal.powQuotSuccInclusion_injective p P j)).conj
          (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (j + 1))))
        = (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j))).restrict (hinv j) := by
      apply LinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := (LinearEquiv.ofInjective (Ideal.powQuotSuccInclusion p P j)
        (Ideal.powQuotSuccInclusion_injective p P j)).surjective z
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      apply Subtype.ext
      simp only [LinearEquiv.ofInjective_apply, LinearMap.restrict_apply]
      exact (hcommA j w).symm
    rw [← hconj, LinearMap.trace_conj']

  have hcommB : ∀ (j : ℕ) {a : S} (a_mem : a ∈ P ^ j) (y : S ⧸ P),
      Ideal.quotientToQuotientRangePowQuotSucc p P a_mem
          (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) y)
        = (LinearMap.range (Ideal.powQuotSuccInclusion p P j)).mapQ
            (LinearMap.range (Ideal.powQuotSuccInclusion p P j))
            (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j)))
            (fun v hv => hinv j v hv)
            (Ideal.quotientToQuotientRangePowQuotSucc p P a_mem y) := by
    intro j a a_mem y
    obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [lmul_appP, ← map_mul, ← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk,
      Ideal.quotientToQuotientRangePowQuotSucc_mk, Ideal.quotientToQuotientRangePowQuotSucc_mk,
      Submodule.mapQ_apply]
    apply congrArg
    apply Subtype.ext
    show Ideal.Quotient.mk (P ^ e) (a * (x * y₀))
        = Ideal.Quotient.mk (P ^ e) x * Ideal.Quotient.mk (P ^ e) (a * y₀)
    rw [← map_mul]
    exact congrArg (Ideal.Quotient.mk (P ^ e)) (by ring)

  have htraceB : ∀ j : ℕ, j < e →
      LinearMap.trace (R ⧸ p)
          ((Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j))
            ⧸ LinearMap.range (Ideal.powQuotSuccInclusion p P j))
          ((LinearMap.range (Ideal.powQuotSuccInclusion p P j)).mapQ
            (LinearMap.range (Ideal.powQuotSuccInclusion p P j))
            (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j)))
            (fun v hv => hinv j v hv))
        = LinearMap.trace (R ⧸ p) (S ⧸ P)
            (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x)) := by
    intro j hj
    obtain ⟨a, a_mem, a_notMem⟩ := SetLike.exists_of_lt
      (Ideal.pow_right_strictAnti P hP0 (Ideal.IsPrime.ne_top inferInstance) (le_refl j.succ))
    have hbij : Function.Bijective (Ideal.quotientToQuotientRangePowQuotSucc p P a_mem) :=
      ⟨Ideal.quotientToQuotientRangePowQuotSucc_injective p P hj a_mem a_notMem,
        Ideal.quotientToQuotientRangePowQuotSucc_surjective p P hP0 hj a_mem a_notMem⟩
    have hconjB : (LinearEquiv.ofBijective
          (Ideal.quotientToQuotientRangePowQuotSucc p P a_mem) hbij).conj
          (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x))
        = (LinearMap.range (Ideal.powQuotSuccInclusion p P j)).mapQ
            (LinearMap.range (Ideal.powQuotSuccInclusion p P j))
            (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j)))
            (fun v hv => hinv j v hv) := by
      apply LinearMap.ext
      intro z
      obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective
        (Ideal.quotientToQuotientRangePowQuotSucc p P a_mem) hbij).surjective z
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply]
      exact hcommB j a_mem y
    rw [← hconjB, LinearMap.trace_conj']

  have key : LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ)))
        (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ))))
      = (e - 0) • LinearMap.trace (R ⧸ p) (S ⧸ P)
          (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x)) := by
    refine Nat.decreasingInduction'
      (P := fun j => LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j))
          (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j)))
        = (e - j) • LinearMap.trace (R ⧸ p) (S ⧸ P)
            (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x)))
      (fun j hj _hij ih => ?_) (Nat.zero_le e) ?_
    ·
      haveI := hfdI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j))
      have hadd := LinearMap.trace_eq_trace_restrict_add_trace_mapQ
        (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j))) (hinv j)
      have ih' : LinearMap.trace (R ⧸ p)
            (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (j + 1)))
            (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (j + 1))))
          = (e - (j + 1)) • LinearMap.trace (R ⧸ p) (S ⧸ P)
              (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x)) := ih
      show LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j))
            (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ j)))
          = (e - j) • LinearMap.trace (R ⧸ p) (S ⧸ P)
              (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x))
      rw [hadd, htraceA j, htraceB j hj, ih', ← succ_nsmul, Nat.sub_succ,
        ← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hj)]
    ·
      have hTzero : TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ e)) = 0 := by
        apply LinearMap.ext
        intro w
        have hw : (w : S ⧸ P ^ e) = 0 := by
          have h2 : (w : S ⧸ P ^ e) ∈ (⊥ : Ideal (S ⧸ P ^ e)) :=
            le_of_eq (Ideal.map_quotient_self (P ^ e)) w.2
          simpa using h2
        apply Subtype.ext
        rw [TI_coe, hw, mul_zero, LinearMap.zero_apply, ZeroMemClass.coe_zero]
      show LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ e))
            (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ e)))
          = (e - e) • LinearMap.trace (R ⧸ p) (S ⧸ P)
              (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x))
      rw [hTzero, map_zero, Nat.sub_self, zero_nsmul]

  have hI0 : Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ)) = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
  have hinj0 : Function.Injective (coeI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ)))) :=
    fun a b hab => Subtype.ext hab
  have hsurj0 : Function.Surjective
      (coeI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ)))) := by
    intro z
    refine ⟨⟨z, ?_⟩, rfl⟩
    rw [hI0]
    exact Submodule.mem_top
  have htop : LinearMap.trace (R ⧸ p) (S ⧸ P ^ e)
        (Algebra.lmul (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk (P ^ e) x))
      = LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ)))
          (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ)))) := by
    have hconj0 : (LinearEquiv.ofBijective
          (coeI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ)))) ⟨hinj0, hsurj0⟩).conj
          (TI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ))))
        = Algebra.lmul (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk (P ^ e) x) := by
      apply LinearMap.ext
      intro z
      have hz : coeI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ)))
          ((LinearEquiv.ofBijective
            (coeI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ))))
            ⟨hinj0, hsurj0⟩).symm z) = z := by
        conv_rhs => rw [← (LinearEquiv.ofBijective
          (coeI (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (0 : ℕ))))
          ⟨hinj0, hsurj0⟩).apply_symm_apply z]
        rw [LinearEquiv.ofBijective_apply]
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.ofBijective_apply, coeTI, hz, lmul_appE]
    rw [← hconj0, LinearMap.trace_conj']
  rw [Algebra.trace_apply, Algebra.trace_apply, htop, key, Nat.sub_zero]
end FLT.Gapsw37T1TameTraceFiltrationEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw59T2WittCohenLiftReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw50T4PieceICompletedElementProduction
open FLT.Gapsw55T2KrasnerDescentGlobalPickSeam
open FLT.Gapsw57T2DvrBaseProductionMint
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw58T5WittASideEngineAtoms

def Gapsw59T2WittCohenLiftSupply : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
    3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal →
    ∃ (_ : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K))
      (_ : Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K)),
      ∀ b : v.adicCompletionIntegers K, ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K) a ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
end FLT.Gapsw59T2WittCohenLiftReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

set_option autoImplicit false
namespace FLT
namespace Gapsw59T2WittCohenLiftReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw50T4PieceICompletedElementProduction
open FLT.Gapsw55T2KrasnerDescentGlobalPickSeam
open FLT.Gapsw57T2DvrBaseProductionMint
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw58T5WittASideEngineAtoms

theorem gapsw59_t2_wittLift_pin :
    Gapsw59T2WittCohenLiftSupply =
      (∀ (K : Type) [Field K] [NumberField K]
        (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal →
        ∃ (_ : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K))
          (_ : Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K)),
          ∀ b : v.adicCompletionIntegers K, ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
            b - algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K) a ∈
              IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  have _em := Classical.em
  rfl
end FLT.Gapsw59T2WittCohenLiftReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

set_option autoImplicit false
namespace FLT
namespace Gapsw59T2WittCohenLiftReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw50T4PieceICompletedElementProduction
open FLT.Gapsw55T2KrasnerDescentGlobalPickSeam
open FLT.Gapsw57T2DvrBaseProductionMint
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw58T5WittASideEngineAtoms
set_option maxHeartbeats 1600000 in

theorem gapsw59_t2_residueSurjectivity_of_wittLift
    (hlift : Gapsw59T2WittCohenLiftSupply) :
    Gapsw58T2UnramifiedDvrBaseResidueSurjectivityProduction := by
  have _em := Classical.em
  rw [gapsw59_t2_wittLift_pin] at hlift
  rw [gapsw58_t2_residueSurjectivity_pin]
  intro K _ _ v hv hwild
  obtain ⟨iAlg, iFin, hres⟩ := hlift K v hv hwild
  obtain ⟨hdom, hdvr, h3⟩ := gapsw58_t5_witt_dvr_irreducible_bundle K v hv hwild
  exact ⟨WittVector 3 ((𝓞 K) ⧸ v.asIdeal), inferInstance, hdom, hdvr, iAlg, iFin,
    h3, hres⟩
end FLT.Gapsw59T2WittCohenLiftReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
p2m_open "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "Matrix P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Matrix Function P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Function"
namespace FLT
namespace GL2GeneralPlaceCongruenceIndexExplicit
noncomputable section
section GeneralPlace
open FLT.GL2FiniteAdelicMatrixIdentificationGeneralF
variable (F : Type*) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

theorem natCard_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
      = Nat.card (𝓞 F ⧸ w.asIdeal) :=
  (Nat.card_congr (ResidueFieldEquivCompletionResidueField F w).toEquiv).symm
end GeneralPlace
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
end FLT.GL2GeneralPlaceCongruenceIndexExplicit
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw54T3WildCompletionDvrWitness
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

theorem gapsw54_t3_uniformizer_irreducible
    (A : Type) [CommRing A] [IsDedekindDomain A]
    (F : Type) [Field F] [Algebra A F] [IsFractionRing A F]
    (v : IsDedekindDomain.HeightOneSpectrum A)
    (π : v.adicCompletionIntegers F)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    Irreducible π := by
  have _em := Classical.em
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr
    (adicCompletion.maximalIdeal_eq_span_uniformizer F v hπ)
end FLT.Gapsw54T3WildCompletionDvrWitness
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

set_option autoImplicit false
namespace FLT
namespace Gapsw54T3WildCompletionDvrWitness
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
set_option maxHeartbeats 1600000 in

theorem gapsw54_t3_intValuation_three_eq_ramificationIdx
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    v.intValuation (3 : 𝓞 K) =
      WithZero.exp (-((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal : ℤ)) := by
  have _em := Classical.em
  have h3O : (3 : 𝓞 K) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 K) K) h
    rw [map_ofNat, map_zero] at h'
    norm_num at h'
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(3 : ℤ)})
      = Ideal.span {(3 : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton, map_ofNat]
  have hbot : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(3 : ℤ)}) ≠ ⊥ := by
    rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]
    exact h3O
  have hcount := Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    (p := Ideal.span {(3 : ℤ)}) (P := v.asIdeal) hbot v.isPrime v.ne_bot
  have hspan0 : (Ideal.span {(3 : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h3O
  rw [v.intValuation_if_neg h3O,
    Ideal.count_associates_factors_eq hspan0 v.isPrime v.ne_bot,
    hcount, hmap]
end FLT.Gapsw54T3WildCompletionDvrWitness
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

set_option autoImplicit false
namespace FLT
namespace Gapsw54T3WildCompletionDvrWitness
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
set_option maxHeartbeats 1600000 in

theorem gapsw54_t3_wild_three_unit_uniformizer_factorisation
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ∃ (π : v.adicCompletionIntegers K) (u0 : (↥(v.adicCompletionIntegers K))ˣ),
      Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) ∧
      (3 : v.adicCompletionIntegers K) =
        (u0 : v.adicCompletionIntegers K)
          * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) := by
  have _em := Classical.em
  have hval3 : Valued.v ((3 : v.adicCompletionIntegers K) : v.adicCompletion K)
      = WithZero.exp (-((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal : ℤ)) := by
    rw [← map_ofNat (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) 3,
      algebraMap_completionIntegers, v.valuedAdicCompletion_eq_valuation,
      v.valuation_of_algebraMap,
      gapsw54_t3_intValuation_three_eq_ramificationIdx K v]
  have h3ne : (3 : v.adicCompletionIntegers K) ≠ 0 := by
    intro h
    rw [h, ZeroMemClass.coe_zero, map_zero] at hval3
    exact WithZero.exp_ne_zero hval3.symm
  obtain ⟨π, hπ⟩ := adicCompletion.exists_uniformizer K v
  have hπe : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := hπ
  obtain ⟨n, u, hu⟩ := adicCompletion.eq_pow_uniformizer_mul_unit K v h3ne hπ
  have hvu : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one _).mp u.isUnit
  have hun : Valued.v ((3 : v.adicCompletionIntegers K) : v.adicCompletion K)
      = WithZero.exp (-(n : ℤ)) := by
    rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
      hπe, hvu, mul_one, ← WithZero.exp_nsmul, WithZero.exp_inj]
    simp
  have hne : n = (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal := by
    have h := hun.symm.trans hval3
    rw [WithZero.exp_inj] at h
    omega
  refine ⟨π, u, hπe, ?_⟩
  rw [hu, hne, mul_comm]
end FLT.Gapsw54T3WildCompletionDvrWitness
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

set_option autoImplicit false
namespace FLT
namespace Gapsw54T3WildCompletionDvrWitness
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

theorem gapsw54_t3_algebraMap_three_reduction
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : Type) [CommRing A] [Algebra A (v.adicCompletionIntegers K)] :
    algebraMap A (v.adicCompletionIntegers K) 3 =
      (3 : v.adicCompletionIntegers K) := by
  have _em := Classical.em
  exact map_ofNat (algebraMap A (v.adicCompletionIntegers K)) 3
end FLT.Gapsw54T3WildCompletionDvrWitness
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

set_option autoImplicit false
namespace FLT
namespace Gapsw54T3WildCompletionDvrWitness
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
set_option maxHeartbeats 1600000 in

theorem gapsw54_t3_global_residue_system
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    ∀ b : v.adicCompletionIntegers K, ∃ a : 𝓞 K,
      b - algebraMap (𝓞 K) (v.adicCompletionIntegers K) a ∈ Ideal.span {π} := by
  have _em := Classical.em
  intro b
  obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicCompletionInteger K v b 1
  refine ⟨a, ?_⟩
  rw [← adicCompletion.maximalIdeal_eq_span_uniformizer K v hπ]
  refine (mem_completionIdeal_iff K v _).mpr ?_
  have hsub : ((b - algebraMap (𝓞 K) (v.adicCompletionIntegers K) a :
        v.adicCompletionIntegers K) : v.adicCompletion K)
      = (b : v.adicCompletion K) - algebraMap (𝓞 K) (v.adicCompletion K) a := by
    rw [AddSubgroupClass.coe_sub, algebraMap_completionIntegers]
    with_unfolding_all rfl
  rw [hsub, Valuation.map_sub_swap]
  exact ha
end FLT.Gapsw54T3WildCompletionDvrWitness
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

section

namespace FLT
namespace Gapsw7X1mCompletionCarrier

p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "Classical P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Classical"
open FLT.Gapsw7X1RamificationFiltrationVocab
open FLT.Gapsw7X1eRealizedLowerFiltration
open FLT.Gapsw7X1iPerPlaceEmbeddedInstantiation
open FLT.Gapsw7X1jRealizedRawSumMajoration
open FLT.Gapsw7X1cPerPlaceDiscDecomposition
open FLT.Gapsw7X1fHilbertDifferentFormulaBridge

theorem gapsw7_x1m_isPrime_liesOver_ne_bot_of_mem
    (K : Type*) [Field K] [NumberField K] {P : Ideal (𝓞 K)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    P.IsPrime ∧ P.LiesOver (Ideal.span {(3 : ℤ)}) ∧ P ≠ ⊥ := by
  have _em := Classical.em
  haveI : Module.IsTorsionFree ℤ (𝓞 K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (RingHom.injective_int _)
  haveI := gapsw7_x1c_span_three_isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff gapsw7_x1c_span_three_ne_bot] at hP
  obtain ⟨hP1, hP2⟩ := hP
  have hmapbot : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(3 : ℤ)}) ≠ ⊥ := fun hbot =>
    gapsw7_x1c_span_three_ne_bot
      ((Ideal.map_eq_bot_iff_of_injective
        (RingHom.injective_int (algebraMap ℤ (𝓞 K)))).mp hbot)
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(3 : ℤ)}) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hP2.over.le
  exact ⟨hP1, hP2, fun hbot => hmapbot (le_bot_iff.mp (hbot ▸ hle))⟩

noncomputable def gapsw7X1mPlace (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := P
  isPrime := (gapsw7_x1m_isPrime_liesOver_ne_bot_of_mem K hP).1
  ne_bot := (gapsw7_x1m_isPrime_liesOver_ne_bot_of_mem K hP).2.2

theorem gapsw7_x1m_place_asIdeal (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    (gapsw7X1mPlace K P hP).asIdeal = P := by
  have _em := Classical.em
  rfl

noncomputable def gapsw7X1mCompletionIdeal (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    Ideal ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
  (gapsw7X1mPlace K P hP).completionIdeal K

theorem gapsw7_x1m_completionIdeal_eq_maximalIdeal (K : Type*) [Field K]
    [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    gapsw7X1mCompletionIdeal K P hP
      = IsLocalRing.maximalIdeal ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) := by
  have _em := Classical.em
  rfl

theorem gapsw7_x1m_completionIdeal_liesOver (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    (gapsw7X1mCompletionIdeal K P hP).LiesOver P := by
  have _em := Classical.em
  exact inferInstanceAs
    (Ideal.LiesOver ((gapsw7X1mPlace K P hP).completionIdeal K)
      ((gapsw7X1mPlace K P hP).asIdeal))

noncomputable def gapsw7X1mResidueEquiv (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    ((𝓞 K) ⧸ P) ≃+*
      IsLocalRing.ResidueField ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
  IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K
    (gapsw7X1mPlace K P hP)

end FLT.Gapsw7X1mCompletionCarrier
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"

section
section
variable (K : Type*) [Field K] [NumberField K]
p2m_open "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
variable (v : HeightOneSpectrum (𝓞 K))
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
namespace NumberField p2m_export "NumberField" "FinitePlace mk place RingOfIntegers RingOfIntegers.rank" end NumberField
p2m_open_scoped "NumberField" in
scoped instance NumberField.instFiniteResidueFieldAdicCompletionIntegers :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  apply (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv.finite_iff.mp
  exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
variable (K : Type*) [Field K] [NumberField K]
p2m_open "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
variable (v : HeightOneSpectrum (𝓞 K))
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open scoped _root_.Valued _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Valued in
scoped instance : Finite (𝓀[v.adicCompletion K]) :=
  inferInstanceAs (Finite (ResidueField (v.adicCompletionIntegers K)))
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
variable (K : Type*) [Field K] [NumberField K]
p2m_open "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
variable (v : HeightOneSpectrum (𝓞 K))
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
p2m_open_scoped "NumberField" in
scoped instance NumberField.instCompactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) :=
  Valued.WithZeroMulInt.integer_compactSpace (v.adicCompletion K) inferInstance
    (v.valuedAdicCompletion_surjective K)
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw37T2TameDifferentCeiling
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "Classical P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Classical"
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

theorem gapsw37t2_exists_mem_mk_eq_of_sup_eq_top {B : Type*} [CommRing B]
    {I Q : Ideal B} (hsup : I ⊔ Q = ⊤) (x : B) :
    ∃ y : B, y ∈ Q ∧ Ideal.Quotient.mk I y = Ideal.Quotient.mk I x := by
  have _em := Classical.em
  have h1 : (1 : B) ∈ I ⊔ Q := hsup ▸ Submodule.mem_top
  obtain ⟨i, hi, q, hq, hiq⟩ := Submodule.mem_sup.mp h1
  refine ⟨q * x, Ideal.mul_mem_right x Q hq, (Ideal.Quotient.eq).mpr ?_⟩
  have hq1 : q = 1 - i := by rw [← hiq]; ring
  have hqx : q * x - x = -(i * x) := by rw [hq1]; ring
  rw [hqx]
  exact I.neg_mem (Ideal.mul_mem_right x I hi)
end FLT.Gapsw37T2TameDifferentCeiling
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw37T2TameDifferentCeiling
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "Classical P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Classical"
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

theorem gapsw37t2_intTrace_notMem_of_trace_quotient_ne_zero
    (A : Type*) {B : Type*} [CommRing A] [CommRing B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    {p : Ideal A} [p.IsMaximal] {y : B}
    (htr : Algebra.trace (A ⧸ p) (B ⧸ Ideal.map (algebraMap A B) p)
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) p) y) ≠ 0) :
    Algebra.intTrace A B y ∉ p := by
  have _em := Classical.em
  intro hmem
  apply htr
  rw [Algebra.trace_quotient_eq_of_isDedekindDomain]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
end FLT.Gapsw37T2TameDifferentCeiling
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw37T2TameDifferentCeiling
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "Classical P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Classical"
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

theorem gapsw37t2_not_pow_dvd_differentIdeal_of_tame
    (A : Type*) {B : Type*} [CommRing A] [CommRing B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] [Finite (A ⧸ p)] (hp : p ≠ ⊥)
    (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (hQ : P ^ p.ramificationIdx' P * Q = Ideal.map (algebraMap A B) p)
    (hcop : IsCoprime (P ^ p.ramificationIdx' P) Q)
    (htame : ((p.ramificationIdx' P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ p.ramificationIdx' P ∣ differentIdeal A B := by
  have _em := Classical.em
  have he0' : p.ramificationIdx' P ≠ 0 := by
    intro h0; rw [h0] at htame; simp at htame
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply hp
    rw [← Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B), ← hQ,
      Ideal.bot_pow he0', Ideal.bot_mul]
  haveI : NeZero (p.ramificationIdx' P) := ⟨he0'⟩

  haveI : IsScalarTower A (A ⧸ p) (B ⧸ P ^ p.ramificationIdx' P) := .of_algebraMap_eq' rfl
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [← Ideal.map_le_iff_le_comap, ← hQ]; exact Ideal.mul_le_right)
  haveI : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (A ⧸ p) (B ⧸ P ^ p.ramificationIdx' P) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ p.ramificationIdx' P)
  haveI : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  haveI : Module.Finite (A ⧸ p) (B ⧸ P) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Algebra.trace (A ⧸ p) (B ⧸ P) x₀ ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x₀

  obtain ⟨y, hyQ, hyx⟩ := gapsw37t2_exists_mem_mk_eq_of_sup_eq_top
    (Ideal.isCoprime_iff_sup_eq.mp hcop) x

  have hyxP : Ideal.Quotient.mk P y = Ideal.Quotient.mk P x := by
    rw [Ideal.Quotient.eq] at hyx ⊢
    exact Ideal.pow_le_self he0' hyx

  have hscale :
      Algebra.trace (A ⧸ p) (B ⧸ P ^ p.ramificationIdx' P)
          (Ideal.Quotient.mk (P ^ p.ramificationIdx' P) y)
        = p.ramificationIdx' P •
            Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk P y) :=
    FLT.Gapsw37T1TameTraceFiltrationEngine.gapsw37_t1_trace_quotient_pow_ramificationIdx_eq_nsmul
      p P hPbot y
  have htrPe : Algebra.trace (A ⧸ p) (B ⧸ P ^ p.ramificationIdx' P)
      (Ideal.Quotient.mk (P ^ p.ramificationIdx' P) y) ≠ 0 := by
    rw [hscale, hyxP, nsmul_eq_mul]
    exact mul_ne_zero htame hx₀

  letI eqv : (B ⧸ Ideal.map (algebraMap A B) p)
      ≃ₐ[A ⧸ p] ((B ⧸ P ^ p.ramificationIdx' P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hQ.symm).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ p.ramificationIdx' P) Q hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }

  have htrace : Algebra.trace (A ⧸ p) (B ⧸ Ideal.map (algebraMap A B) p)
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) p) y) ≠ 0 := by
    rw [← Algebra.trace_eq_of_algEquiv eqv]
    have h2 : (eqv (Ideal.Quotient.mk (Ideal.map (algebraMap A B) p) y)).2 = 0 := by
      simpa [eqv, Ideal.Quotient.eq_zero_iff_mem] using hyQ
    have h1 : (eqv (Ideal.Quotient.mk (Ideal.map (algebraMap A B) p) y)).1
        = Ideal.Quotient.mk (P ^ p.ramificationIdx' P) y := by
      simp [eqv]
    rw [Algebra.trace_prod_apply, h1, h2, map_zero, add_zero]
    exact htrPe
  exact not_dvd_differentIdeal_of_intTrace_not_mem A (P ^ p.ramificationIdx' P) Q hQ y hyQ
    (gapsw37t2_intTrace_notMem_of_trace_quotient_ne_zero A htrace)
end FLT.Gapsw37T2TameDifferentCeiling
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw37T2TameDifferentCeiling
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "Classical P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Classical"
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

theorem gapsw37t2_count_normalizedFactors_differentIdeal_le_ramificationIdx_sub_one
    (K : Type*) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (he : ¬ (3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P)) :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P
      ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P - 1 := by
  have _em := Classical.em
  haveI := FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_isMaximal
  haveI : Algebra.IsAlgebraic (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    isAlgebraic_of_isFractionRing (R := ℤ) (S := 𝓞 K) (FractionRing ℤ) (FractionRing (𝓞 K))
  haveI : Algebra.IsIntegral (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  rw [IsDedekindDomain.mem_primesOverFinset_iff
    FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot] at hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI := hPprime
  haveI := hPlies
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot
    rw [Ideal.LiesOver.over (p := Ideal.span {(3 : ℤ)}) (P := (⊥ : Ideal (𝓞 K))),
      Ideal.under_def]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
  haveI : P.IsMaximal := hPprime.isMaximal hPbot
  haveI : Finite (ℤ ⧸ Ideal.span {(3 : ℤ)}) := by
    have e3 := (Int.quotientSpanEquivZMod 3).toEquiv
    rw [show ((3 : ℤ).natAbs) = 3 from rfl] at e3
    exact Finite.of_equiv (ZMod 3) e3.symm

  have htame3 : (((Ideal.span {(3 : ℤ)}).ramificationIdx' P : ℕ) :
      ℤ ⧸ Ideal.span {(3 : ℤ)}) ≠ 0 := by
    intro h0
    apply he
    have h1 : ((((Ideal.span {(3 : ℤ)}).ramificationIdx' P : ℕ) : ℤ))
        ∈ Ideal.span {(3 : ℤ)} := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    rw [Ideal.mem_span_singleton] at h1
    exact_mod_cast h1

  by_contra hcon
  push Not at hcon
  have he0 : (Ideal.span {(3 : ℤ)}).ramificationIdx' P ≠ 0 := by
    intro h0
    apply he
    rw [h0]
    exact dvd_zero 3
  have hge : (Ideal.span {(3 : ℤ)}).ramificationIdx' P
      ≤ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by omega
  have hD0 : differentIdeal ℤ (𝓞 K) ≠ 0 := by
    simpa using (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))
  have hPirr : Irreducible P := (Ideal.prime_of_isPrime hPbot hPprime).irreducible
  have hdvd : P ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) ∣ differentIdeal ℤ (𝓞 K) := by
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPirr hD0,
      normalize_eq]
    exact_mod_cast hge

  have hmapbot : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(3 : ℤ)}) ≠ ⊥ := fun hbot =>
    FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot
      ((Ideal.map_eq_bot_iff_of_injective
        (RingHom.injective_int (algebraMap ℤ (𝓞 K)))).mp hbot)
  have hecount : (Ideal.span {(3 : ℤ)}).ramificationIdx' P
      = (normalizedFactors (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(3 : ℤ)}))).count P :=
    Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmapbot hPprime hPbot
  obtain ⟨Q, hQtop, hQeq⟩ := Ideal.eq_prime_pow_mul_coprime hmapbot P
  rw [← hecount] at hQeq

  exact gapsw37t2_not_pow_dvd_differentIdeal_of_tame ℤ
    FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot P Q hQeq.symm
    ((Ideal.isCoprime_iff_sup_eq.mpr hQtop).pow_left) htame3 hdvd
end FLT.Gapsw37T2TameDifferentCeiling
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw57T3SinglePrimeCRTPickAtom
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open_scoped "IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw54T2KrasnerGlobalGeneratorTransport
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw55T2KrasnerDescentGlobalPickSeam
set_option maxHeartbeats 1600000 in

theorem gapsw57_t3_completed_three_valuation
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Valued.v ((3 : v.adicCompletionIntegers K) : v.adicCompletion K) =
      WithZero.exp (-((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal : ℤ)) := by
  have _em := Classical.em
  rw [← map_ofNat (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) 3,
    algebraMap_completionIntegers, v.valuedAdicCompletion_eq_valuation,
    v.valuation_of_algebraMap,
    gapsw54_t3_intValuation_three_eq_ramificationIdx K v]
end FLT.Gapsw57T3SinglePrimeCRTPickAtom
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw67T5UniformizerEisensteinSupply
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw66T4HagreeDischargePackedAlgebra
set_option maxHeartbeats 1600000 in

theorem gapsw67_t5_uniformizer_exists
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (hwild : 3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) :
    ∃ π : v.adicCompletionIntegers K,
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
        Ideal.span {π} ∧ π ≠ 0 := by
  have _em := Classical.em
  have _h1 := h1
  have _hwild := hwild
  obtain ⟨π, hπ⟩ := adicCompletion.exists_uniformizer K v
  have hπe : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := hπ
  exact ⟨π, adicCompletion.maximalIdeal_eq_span_uniformizer K v hπe,
    (gapsw54_t3_uniformizer_irreducible (𝓞 K) K v π hπe).ne_zero⟩
end FLT.Gapsw67T5UniformizerEisensteinSupply
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw67T5UniformizerEisensteinSupply
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw66T4HagreeDischargePackedAlgebra
set_option maxHeartbeats 1600000 in

theorem gapsw67_t5_eisenstein_unit_exists
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hπ : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {π}) :
    ∃ u0 : (↥(v.adicCompletionIntegers K))ˣ,
      (3 : v.adicCompletionIntegers K) =
        (u0 : v.adicCompletionIntegers K)
          * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) := by
  have _em := Classical.em
  obtain ⟨π₀, u0, hπ₀, h3fac⟩ :=
    gapsw54_t3_wild_three_unit_uniformizer_factorisation K v
  have hspan : Ideal.span {π₀} = Ideal.span {π} := by
    rw [← adicCompletion.maximalIdeal_eq_span_uniformizer K v hπ₀, hπ]
  have hassoc : Associated π₀ π :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  obtain ⟨c, hc⟩ := Associated.pow_pow
    (n := (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) hassoc.symm
  refine ⟨u0 * c, ?_⟩
  rw [h3fac, ← hc, Units.val_mul]
  ring
end FLT.Gapsw67T5UniformizerEisensteinSupply
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw67T5UniformizerEisensteinSupply
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw66T4HagreeDischargePackedAlgebra
set_option maxHeartbeats 1600000 in

theorem gapsw67_t5_eisenstein_unit_exists_algebraMap
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : Type) [CommRing A] [Algebra A (v.adicCompletionIntegers K)]
    (π : v.adicCompletionIntegers K)
    (hπ : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {π}) :
    ∃ u0 : (↥(v.adicCompletionIntegers K))ˣ,
      algebraMap A (v.adicCompletionIntegers K) 3 =
        (u0 : v.adicCompletionIntegers K)
          * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) := by
  have _em := Classical.em
  obtain ⟨u0, h3fac⟩ := gapsw67_t5_eisenstein_unit_exists K v π hπ
  refine ⟨u0, ?_⟩
  rw [gapsw54_t3_algebraMap_three_reduction K v A]
  exact h3fac
end FLT.Gapsw67T5UniformizerEisensteinSupply
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T1PieceIResidualOfLocalDifferent
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
open scoped algebraMap
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw77T4PieceIResidualCountEquiv
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X1xLocalDifferentCompletionIdentification
set_option maxHeartbeats 1600000 in

theorem gapsw78_t1_place_asIdeal_roundtrip
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hP : v.asIdeal ∈
      IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    gapsw7X1mPlace K (v.asIdeal) hP = v := by
  have _em := Classical.em
  exact IsDedekindDomain.HeightOneSpectrum.ext
    (gapsw7_x1m_place_asIdeal K (v.asIdeal) hP)
end FLT.Gapsw78T1PieceIResidualOfLocalDifferent
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T6AbstractBaseAKLBFrame
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T2LocalDiffUniformizerDischarge
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
set_option maxHeartbeats 3200000 in

theorem gapsw78_t6_algebraMap_injective
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    (h3A : Irreducible (3 : A)) :
    Function.Injective (algebraMap A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)) := by
  have _em := Classical.em
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne

  have hker_prime : (RingHom.ker (algebraMap A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))).IsPrime :=
    RingHom.ker_isPrime _

  have hker_max : RingHom.ker (algebraMap A
        ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
      = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (hker_prime.isMaximal hne)

  have h3ker : (3 : A) ∈ RingHom.ker (algebraMap A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)) := by
    rw [hker_max, IsLocalRing.mem_maximalIdeal]
    exact h3A.not_isUnit

  rw [RingHom.mem_ker, map_ofNat] at h3ker
  have h3ne : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ≠ 0 := by
    intro h
    have hcoe : ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K)
      = (3 : (gapsw7X1mPlace K P hP).adicCompletion K) := by norm_cast
    have : (3 : (gapsw7X1mPlace K P hP).adicCompletion K) = 0 := by
      rw [← hcoe, h, ZeroMemClass.coe_zero]
    exact three_ne_zero this
  exact h3ne h3ker
end FLT.Gapsw78T6AbstractBaseAKLBFrame
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T6AbstractBaseAKLBFrame
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T2LocalDiffUniformizerDischarge
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
set_option maxHeartbeats 3200000 in

theorem gapsw78_t6_isTorsionFree
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    (h3A : Irreducible (3 : A)) :
    Module.IsTorsionFree A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) := by
  have _em := Classical.em
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr
    (gapsw78_t6_algebraMap_injective K P hP A h3A)
end FLT.Gapsw78T6AbstractBaseAKLBFrame
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T6AbstractBaseAKLBFrame
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T2LocalDiffUniformizerDischarge
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
set_option maxHeartbeats 3200000 in

theorem gapsw78_t6_isIntegralClosure
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.Finite A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletion K)]
    [IsScalarTower A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ((gapsw7X1mPlace K P hP).adicCompletion K)] :
    IsIntegralClosure ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) A
      ((gapsw7X1mPlace K P hP).adicCompletion K) := by
  have _em := Classical.em
  haveI : Algebra.IsIntegral A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    Algebra.IsIntegral.of_finite _ _
  exact IsIntegralClosure.of_isIntegrallyClosed _ _ _
end FLT.Gapsw78T6AbstractBaseAKLBFrame
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T6AbstractBaseAKLBFrame
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T2LocalDiffUniformizerDischarge
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
set_option maxHeartbeats 3200000 in

theorem gapsw78_t6_module_finite_fractionRing
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.Finite A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    (h3A : Irreducible (3 : A))
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletion K)]
    [IsScalarTower A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ((gapsw7X1mPlace K P hP).adicCompletion K)]
    [Algebra (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K)]
    [IsScalarTower A (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K)] :
    Module.Finite (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) := by
  have _em := Classical.em
  haveI : FaithfulSMul A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (gapsw78_t6_algebraMap_injective K P hP A h3A)
  exact Module.Finite.of_isLocalization A
    ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) (nonZeroDivisors A)
end FLT.Gapsw78T6AbstractBaseAKLBFrame
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T6AbstractBaseAKLBFrame
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T2LocalDiffUniformizerDischarge
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
set_option maxHeartbeats 3200000 in

theorem gapsw78_t6_charZero
    (A : Type) [CommRing A] [IsDomain A]
    (h3A : Irreducible (3 : A)) : CharZero A := by
  have _em := Classical.em
  haveI := ringChar.charP A
  rcases CharP.char_is_prime_or_zero A (ringChar A) with hp | hp
  · exfalso
    by_cases hd : ringChar A ∣ 3
    · exact h3A.ne_zero
        (by simpa using (CharP.cast_eq_zero_iff A (ringChar A) 3).mpr hd)
    · haveI : Fact (ringChar A).Prime := ⟨hp⟩
      refine h3A.not_isUnit ?_
      have hcop : Nat.Coprime 3 (ringChar A) :=
        Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr hd)
      have hzu : IsUnit ((3 : ℕ) : ZMod (ringChar A)) :=
        (ZMod.isUnit_iff_coprime 3 (ringChar A)).mpr hcop
      have := (ZMod.castHom dvd_rfl A).isUnit_map hzu
      rw [map_natCast, Nat.cast_ofNat] at this
      exact this
  · haveI : CharP A 0 := hp ▸ ringChar.charP A
    exact CharP.charP_to_charZero A
end FLT.Gapsw78T6AbstractBaseAKLBFrame
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.HeightOneSpectrum IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X3jCarrierAlgebraWiring
open FLT.Gapsw7X3lCarrierIntegralClosure
open FLT.Gapsw7X3lRd20t4HmapHfxCarrierWss
open FLT.Gapsw7X3mCompletionFieldFiniteDimensional
open FLT.Gapsw7X3pHenselCoeffIntegralClosureHeadline
open FLT.Gapsw7X3wExtensionCompletionCarrier
open FLT.Gapsw7X3xCrossPlaceTraceDecomposition
open FLT.PlaceDataSemilocalDischarge
p2m_open_scoped "TensorProduct P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.TensorProduct NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField nonZeroDivisors"
namespace FLT
namespace Gapsw7X4gCompletionInstanceRow

theorem gapsw7_x4g_isDedekindDomain_carrierIntegers (K : Type*) [Field K]
    [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    IsDedekindDomain ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) := by
  have _em := Classical.em
  exact inferInstance
end FLT.Gapsw7X4gCompletionInstanceRow
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing Pointwise P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Pointwise"
noncomputable section
section CompactNoetherianLocal
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsNoetherianRing R] [IsLocalRing R]

scoped instance (priority := 80) instIsAdicCompleteMaximalIdealOfCompactSpace :
    IsAdicComplete (maximalIdeal R) R where
  prec' f hf := by

    let S : ℕ → Set R := fun n => f n +ᵥ ((maximalIdeal R ^ n : Ideal R) : Set R)

    have hSclosed : ∀ n, IsClosed (S n) := fun n =>
      (IsNoetherianRing.isClosed_ideal (maximalIdeal R ^ n)).vadd (f n)
    have hSne : ∀ n, (S n).Nonempty := fun n =>
      ⟨f n, ⟨0, Ideal.zero_mem _, by simp⟩⟩

    have hSmono : ∀ n, S (n + 1) ⊆ S n := by
      intro n x ⟨y, hy, hxy⟩
      have hcauchy : f (n + 1) - f n ∈ (maximalIdeal R) ^ n := by
        have h := hf (Nat.le_succ n)
        rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, neg_mem_iff] at h
      exact ⟨(f (n + 1) - f n) + y,
        Ideal.add_mem _ hcauchy (Ideal.pow_le_pow_right (Nat.le_succ n) hy),
        by simp only [vadd_eq_add] at hxy ⊢; linear_combination hxy⟩

    obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      hSmono hSne (hSclosed 0).isCompact hSclosed
    refine ⟨L, fun n => ?_⟩
    obtain ⟨y, hy, hLy⟩ := Set.mem_iInter.mp hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    simp only [vadd_eq_add] at hLy
    have h : f n - L = -y := by linear_combination hLy
    rw [h]; exact neg_mem hy
end CompactNoetherianLocal
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing Pointwise P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Pointwise"
noncomputable section
section CompactNoetherianLocal
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsNoetherianRing R] [IsLocalRing R]

theorem henselianLocalRing_of_henselianRing {S : Type*} [CommRing S] [IsLocalRing S]
    [HenselianRing S (maximalIdeal S)] : HenselianLocalRing S where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk (maximalIdeal S)))
end CompactNoetherianLocal
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing Pointwise P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Pointwise"
noncomputable section
section CompactNoetherianLocal
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsNoetherianRing R] [IsLocalRing R]

scoped instance (priority := 80) instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing :
    HenselianLocalRing R :=
  henselianLocalRing_of_henselianRing
end CompactNoetherianLocal
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing Pointwise P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Pointwise"
noncomputable section
section AdicCompletionIntegers
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
p2m_open_scoped "NumberField" in

scoped instance NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) :=
  instIsAdicCompleteMaximalIdealOfCompactSpace
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end AdicCompletionIntegers
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing Pointwise P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Pointwise"
noncomputable section
section AdicCompletionIntegers
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
p2m_open_scoped "NumberField" in

scoped instance NumberField.instHenselianLocalRingAdicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) :=
  instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end AdicCompletionIntegers
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw44T4WildDifferentSummationWs
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
open nonZeroDivisors
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
open FLT.Gapsw7X1cPerPlaceDiscDecomposition
open FLT.Gapsw43T4WildDifferentLowerBoundGlue
open FLT.Gapsw37T2TameDifferentCeiling

def Gapsw44T4WildDifferentUpperBoundSupply : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K)),
    P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P
      ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P
        + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
          * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) - 1
end FLT.Gapsw44T4WildDifferentSummationWs
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw44T4WildDifferentSummationWs
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
open nonZeroDivisors
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
open FLT.Gapsw7X1cPerPlaceDiscDecomposition
open FLT.Gapsw43T4WildDifferentLowerBoundGlue
open FLT.Gapsw37T2TameDifferentCeiling

theorem gapsw44_t4_wildDifferentUpperBoundSupply_pin :
    Gapsw44T4WildDifferentUpperBoundSupply =
      (∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K)),
        P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
        (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P
          ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P
            + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
              * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) - 1) := by
  have _em := Classical.em
  rfl
end FLT.Gapsw44T4WildDifferentSummationWs
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw44T4WildDifferentSummationWs
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
open nonZeroDivisors
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
open FLT.Gapsw7X1cPerPlaceDiscDecomposition
open FLT.Gapsw43T4WildDifferentLowerBoundGlue
open FLT.Gapsw37T2TameDifferentCeiling
set_option maxHeartbeats 3200000 in

theorem gapsw44_t4_upperBoundSupply_tame_slice
    (K : Type*) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (he : ¬ (3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P)) :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P
      ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P
        + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
          * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) - 1 := by
  have h0 : padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) = 0 :=
    padicValNat.eq_zero_of_not_dvd he
  rw [h0, Nat.mul_zero, Nat.add_zero]
  exact gapsw37t2_count_normalizedFactors_differentIdeal_le_ramificationIdx_sub_one K P hP he
end FLT.Gapsw44T4WildDifferentSummationWs
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section

namespace FLT
namespace Gapsw63T4ModuleFiniteCarrier

p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw54T2KrasnerGlobalGeneratorTransport
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw57T3SinglePrimeCRTPickAtom
open FLT.Gapsw58T5WittASideEngineAtoms

set_option maxHeartbeats 1600000 in

theorem gapsw63_t4_ideal_smul_top
    (A : Type) [CommRing A] (I : Ideal A) :
    (I • ⊤ : Submodule A A) = I := by
  have _em := Classical.em
  rw [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one]

set_option maxHeartbeats 3200000 in

theorem gapsw63_t4_mem_span_range_of_complete
    (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (t : A)
    (hprec : IsPrecomplete (Ideal.span {t}) A)
    (hsep : ∀ b : B, (∀ n : ℕ, b ∈ Ideal.span {algebraMap A B t} ^ n) → b = 0)
    (ι : Type) [Fintype ι] (s : ι → B)
    (hspan : ∀ b : B, ∃ a : ι → A,
      b - ∑ i, a i • s i ∈ Ideal.span {algebraMap A B t})
    (b : B) :
    b ∈ Submodule.span A (Set.range s) := by
  have _em := Classical.em
  classical

  choose F hF using hspan
  have hquot : ∀ b' : B, ∃ c : B,
      b' - ∑ i, F b' i • s i = algebraMap A B t * c := by
    intro b'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hF b')
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose G hG using hquot

  set e : ℕ → B := fun n => G^[n] b with he
  have he0 : e 0 = b := by
    simp only [he]
    exact Function.iterate_zero_apply G b
  have hes : ∀ n : ℕ, e (n + 1) = G (e n) := by
    intro n
    simp only [he]
    exact Function.iterate_succ_apply' G n b
  set P : ℕ → ι → A := fun n i => ∑ m ∈ Finset.range n, t ^ m * F (e m) i
    with hP

  have hsmul : ∀ (m : ℕ) (x : A) (y : B),
      (t ^ m * x) • y = algebraMap A B t ^ m * (x • y) := by
    intro m x y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, mul_assoc]

  have hkey : ∀ n : ℕ, b - ∑ i, P n i • s i = algebraMap A B t ^ n * e n := by
    intro n
    induction n with
    | zero =>
      simp only [hP, Finset.range_zero, Finset.sum_empty, zero_smul,
        Finset.sum_const_zero, sub_zero, pow_zero, one_mul, he0]
    | succ n ih =>
      have hPs : ∀ i : ι, P (n + 1) i = P n i + t ^ n * F (e n) i := by
        intro i
        simp only [hP]
        exact Finset.sum_range_succ (fun m => t ^ m * F (e m) i) n
      have hsum1 : ∑ i, P (n + 1) i • s i
          = (∑ i, P n i • s i) + ∑ i, (t ^ n * F (e n) i) • s i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hPs i, add_smul]
      have hsum2 : ∑ i, (t ^ n * F (e n) i) • s i
          = algebraMap A B t ^ n * ∑ i, F (e n) i • s i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => hsmul n (F (e n) i) (s i)
      calc b - ∑ i, P (n + 1) i • s i
          = (b - ∑ i, P n i • s i) - ∑ i, (t ^ n * F (e n) i) • s i := by
            rw [hsum1]; ring
        _ = algebraMap A B t ^ n * e n
              - algebraMap A B t ^ n * ∑ i, F (e n) i • s i := by
            rw [ih, hsum2]
        _ = algebraMap A B t ^ n * (e n - ∑ i, F (e n) i • s i) := by ring
        _ = algebraMap A B t ^ n * (algebraMap A B t * e (n + 1)) := by
            rw [hG (e n), ← hes n]
        _ = algebraMap A B t ^ (n + 1) * e (n + 1) := by ring

  have hcauchy : ∀ (i : ι) {m n : ℕ}, m ≤ n →
      P m i ≡ P n i [SMOD (Ideal.span {t} ^ m • ⊤ : Submodule A A)] := by
    intro i m n hmn
    rw [SModEq.sub_mem, gapsw63_t4_ideal_smul_top]
    have hsplit : P n i - P m i = ∑ k ∈ Finset.Ico m n, t ^ k * F (e k) i := by
      simp only [hP]
      rw [Finset.sum_Ico_eq_sub (fun k => t ^ k * F (e k) i) hmn]
    have hmem : P n i - P m i ∈ Ideal.span {t} ^ m := by
      rw [hsplit, Ideal.span_singleton_pow]
      refine Ideal.sum_mem _ fun k hk => ?_
      rw [Ideal.mem_span_singleton]
      exact dvd_mul_of_dvd_left
        (pow_dvd_pow t (Finset.mem_Ico.mp hk).1) (F (e k) i)
    have hneg := neg_mem hmem
    rwa [neg_sub] at hneg

  have hlim : ∀ i : ι, ∃ L : A, ∀ n : ℕ,
      P n i ≡ L [SMOD (Ideal.span {t} ^ n • ⊤ : Submodule A A)] := by
    intro i
    exact hprec.prec (fun {m n} hmn => hcauchy i hmn)
  choose L hL using hlim

  have hresidual : ∀ n : ℕ,
      b - ∑ i, L i • s i ∈ Ideal.span {algebraMap A B t} ^ n := by
    intro n
    have h1 : b - ∑ i, P n i • s i ∈ Ideal.span {algebraMap A B t} ^ n := by
      rw [hkey n, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    have h2 : ∀ i : ι,
        (P n i - L i) • s i ∈ Ideal.span {algebraMap A B t} ^ n := by
      intro i
      have hm : P n i - L i ∈ Ideal.span {t} ^ n := by
        have h := hL i n
        rwa [SModEq.sub_mem, gapsw63_t4_ideal_smul_top] at h
      rw [Ideal.span_singleton_pow] at hm
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hm
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      refine ⟨algebraMap A B d * s i, ?_⟩
      rw [← hd, Algebra.smul_def, map_mul, map_pow]
      ring
    have hsplitsum : b - ∑ i, L i • s i
        = (b - ∑ i, P n i • s i) + ∑ i, (P n i - L i) • s i := by
      rw [show (∑ i, (P n i - L i) • s i)
            = ∑ i, (P n i • s i - L i • s i) from
          Finset.sum_congr rfl fun i _ => sub_smul (P n i) (L i) (s i)]
      rw [Finset.sum_sub_distrib]
      ring
    rw [hsplitsum]
    exact Ideal.add_mem _ h1 (Ideal.sum_mem _ fun i _ => h2 i)

  have hzero : b - ∑ i, L i • s i = 0 := hsep _ hresidual
  have hb : b = ∑ i, L i • s i := sub_eq_zero.mp hzero
  rw [hb]
  exact Submodule.sum_smul_mem _ L fun i _ => Submodule.subset_span ⟨i, rfl⟩

set_option maxHeartbeats 1600000 in

theorem gapsw63_t4_span_range_eq_top_of_complete
    (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (t : A)
    (hprec : IsPrecomplete (Ideal.span {t}) A)
    (hsep : ∀ b : B, (∀ n : ℕ, b ∈ Ideal.span {algebraMap A B t} ^ n) → b = 0)
    (ι : Type) [Fintype ι] (s : ι → B)
    (hspan : ∀ b : B, ∃ a : ι → A,
      b - ∑ i, a i • s i ∈ Ideal.span {algebraMap A B t}) :
    Submodule.span A (Set.range s) = ⊤ := by
  have _em := Classical.em
  rw [Submodule.eq_top_iff']
  intro b
  exact gapsw63_t4_mem_span_range_of_complete A B t hprec hsep ι s hspan b

set_option maxHeartbeats 1600000 in

theorem gapsw63_t4_moduleFinite_of_complete
    (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (t : A)
    (hprec : IsPrecomplete (Ideal.span {t}) A)
    (hsep : ∀ b : B, (∀ n : ℕ, b ∈ Ideal.span {algebraMap A B t} ^ n) → b = 0)
    (ι : Type) [Fintype ι] (s : ι → B)
    (hspan : ∀ b : B, ∃ a : ι → A,
      b - ∑ i, a i • s i ∈ Ideal.span {algebraMap A B t}) :
    Module.Finite A B := by
  have _em := Classical.em
  classical
  rw [Module.finite_def]
  refine ⟨Finset.univ.image s, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact gapsw63_t4_span_range_eq_top_of_complete A B t hprec hsep ι s hspan

set_option maxHeartbeats 1600000 in

theorem gapsw63_t4_sub_eq_zero_of_mem_maximalIdeal_pow
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (b : v.adicCompletionIntegers K)
    (hb : ∀ n : ℕ,
      b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :
    b = 0 := by
  have _em := Classical.em
  have hbot : (⨅ n : ℕ,
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _
      ((IsLocalRing.maximalIdeal.isMaximal _).ne_top)
  have hmem : b ∈ (⊥ : Ideal (v.adicCompletionIntegers K)) := by
    rw [← hbot]
    exact (Submodule.mem_iInf _).mpr hb
  simpa using hmem

set_option maxHeartbeats 1600000 in

theorem gapsw63_t4_three_not_isUnit
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    ¬ IsUnit (3 : v.adicCompletionIntegers K) := by
  have _em := Classical.em
  intro hu
  have hval : Valued.v ((3 : v.adicCompletionIntegers K) : v.adicCompletion K)
      = 1 := (ValuationSubring.isUnit_iff_valued_eq_one _).mp hu
  rw [gapsw57_t3_completed_three_valuation K v, ← WithZero.exp_zero,
    WithZero.exp_inj] at hval
  have he : (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal ≠ 0 :=
    gapsw54_t2_ramificationIdx_ne_zero K v h1
  omega

set_option maxHeartbeats 1600000 in

theorem gapsw63_t4_eq_zero_of_mem_span_three_pow
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (b : v.adicCompletionIntegers K)
    (hb : ∀ n : ℕ,
      b ∈ Ideal.span {(3 : v.adicCompletionIntegers K)} ^ n) :
    b = 0 := by
  have _em := Classical.em
  have hle : Ideal.span {(3 : v.adicCompletionIntegers K)} ≤
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    refine Ideal.span_le.mpr ?_
    rw [Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (mem_nonunits_iff.mpr (gapsw63_t4_three_not_isUnit K v h1))
  refine gapsw63_t4_sub_eq_zero_of_mem_maximalIdeal_pow K v b fun n => ?_
  exact Ideal.pow_right_mono hle n (hb n)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw63_t4_witt_isPrecomplete
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    IsPrecomplete
      (Ideal.span {(3 : WittVector 3 ((𝓞 K) ⧸ v.asIdeal))})
      (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) := by
  have _em := Classical.em
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hmax : v.asIdeal.IsMaximal := gapsw58_t5_residue_isMaximal K v
  letI : Field ((𝓞 K) ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI hch : CharP ((𝓞 K) ⧸ v.asIdeal) 3 :=
    gapsw58_t5_residue_charP_three K v h1
  haveI hfin : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    gapsw58_t5_residue_field_finite K v
  haveI hperf : PerfectRing ((𝓞 K) ⧸ v.asIdeal) 3 := by
    obtain ⟨_, hp⟩ := gapsw58_t5_residue_perfectRing_three K v h1
    exact hp
  have h := (WittVector.isAdicCompleteIdealSpanP
    (p := 3) (k := (𝓞 K) ⧸ v.asIdeal)).toIsPrecomplete
  rwa [Nat.cast_ofNat] at h

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw63_t4_moduleFinite_carrier
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (ι : Type) [Fintype ι] (s : ι → v.adicCompletionIntegers K)
    (hspan : ∀ b : v.adicCompletionIntegers K,
      ∃ a : ι → WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - ∑ i, a i • s i ∈
          Ideal.span {(3 : v.adicCompletionIntegers K)}) :
    Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  have halg3 : algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K) (3 : WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      = (3 : v.adicCompletionIntegers K) :=
    gapsw54_t3_algebraMap_three_reduction K v
      (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
  refine gapsw63_t4_moduleFinite_of_complete
    (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K) 3
    (gapsw63_t4_witt_isPrecomplete K v h1) ?_ ι s ?_
  · intro b hb
    refine gapsw63_t4_eq_zero_of_mem_span_three_pow K v h1 b fun n => ?_
    have h := hb n
    rwa [halg3] at h
  · intro b
    obtain ⟨a, ha⟩ := hspan b
    refine ⟨a, ?_⟩
    rwa [halg3]

set_option maxHeartbeats 1600000 in

theorem gapsw63_t4_maximalIdeal_pow_ramificationIdx_le_span_three
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
        ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) ≤
      Ideal.span {(3 : v.adicCompletionIntegers K)} := by
  have _em := Classical.em
  obtain ⟨π, u0, hπ, h3⟩ :=
    gapsw54_t3_wild_three_unit_uniformizer_factorisation K v
  have hπ' : Valued.v (π.1 : v.adicCompletion K)
      = Multiplicative.ofAdd (-1 : ℤ) := hπ
  have hmax : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
      = Ideal.span {π} :=
    adicCompletion.maximalIdeal_eq_span_uniformizer K v hπ'
  have hmem : π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) ∈
      Ideal.span {(3 : v.adicCompletionIntegers K)} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨(↑u0⁻¹ : v.adicCompletionIntegers K), ?_⟩
    calc π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)
        = 1 * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) :=
          (one_mul _).symm
      _ = ((↑u0⁻¹ : v.adicCompletionIntegers K) * ↑u0)
            * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) := by
          rw [Units.inv_mul]
      _ = (↑u0⁻¹ : v.adicCompletionIntegers K)
            * (↑u0 * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal))
          := by ring
      _ = (↑u0⁻¹ : v.adicCompletionIntegers K)
            * (3 : v.adicCompletionIntegers K) := by rw [← h3]
      _ = (3 : v.adicCompletionIntegers K)
            * (↑u0⁻¹ : v.adicCompletionIntegers K) := by ring
  calc IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
      ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)
      = Ideal.span {π}
          ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) := by
        rw [hmax]
    _ = Ideal.span
          {π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)} :=
        Ideal.span_singleton_pow π _
    _ ≤ Ideal.span {(3 : v.adicCompletionIntegers K)} := by
        refine Ideal.span_le.mpr ?_
        rw [Set.singleton_subset_iff]
        exact hmem

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw63_t4_moduleFinite_carrier_of_pow_le
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (E : ℕ)
    (hE : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ E ≤
      Ideal.span {(3 : v.adicCompletionIntegers K)})
    (ι : Type) [Fintype ι] (s : ι → v.adicCompletionIntegers K)
    (hspan : ∀ b : v.adicCompletionIntegers K,
      ∃ a : ι → WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - ∑ i, a i • s i ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ E) :
    Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  refine gapsw63_t4_moduleFinite_carrier K v h1 ι s fun b => ?_
  obtain ⟨a, ha⟩ := hspan b
  exact ⟨a, hE ha⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw63_t4_moduleFinite_carrier_of_ramification
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (ι : Type) [Fintype ι] (s : ι → v.adicCompletionIntegers K)
    (hspan : ∀ b : v.adicCompletionIntegers K,
      ∃ a : ι → WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - ∑ i, a i • s i ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
            ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)) :
    Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  exact gapsw63_t4_moduleFinite_carrier_of_pow_le K v h1
    ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)
    (gapsw63_t4_maximalIdeal_pow_ramificationIdx_le_span_three K v)
    ι s hspan

end FLT.Gapsw63T4ModuleFiniteCarrier
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
namespace Deformation
namespace TeichmullerDecomp

theorem one_lt_card_residueField' : 1 < Nat.card (κ 𝒪ᵥ) := Finite.one_lt_card
end Deformation.TeichmullerDecomp
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
namespace Deformation
namespace TeichmullerDecomp

theorem card_residueField_sub_one_ne_zero' : Nat.card (κ 𝒪ᵥ) - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt (one_lt_card_residueField' v)
end Deformation.TeichmullerDecomp
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
namespace Deformation
namespace TeichmullerDecomp

theorem isUnit_card_residueField_sub_one' :
    IsUnit ((Nat.card (κ 𝒪ᵥ) - 1 : ℕ) : 𝒪ᵥ) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have h0 : (residue (𝒪ᵥ)) ((Nat.card (κ 𝒪ᵥ) - 1 : ℕ) : 𝒪ᵥ) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_natCast] at h0
  haveI : Fintype (κ 𝒪ᵥ) := Fintype.ofFinite _
  have hq0 : (Nat.card (κ 𝒪ᵥ) : κ 𝒪ᵥ) = 0 := by
    rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  rw [Nat.cast_sub (one_lt_card_residueField' v).le, hq0, Nat.cast_one, zero_sub,
    neg_eq_zero] at h0
  exact one_ne_zero h0
end Deformation.TeichmullerDecomp
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
namespace Deformation
namespace TeichmullerDecomp

theorem pow_card_sub_one_sub_one_mem_maximalIdeal {u : 𝒪ᵥ} (hu : IsUnit u) :
    u ^ (Nat.card (κ 𝒪ᵥ) - 1) - 1 ∈ 𝔪 (𝒪ᵥ) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  haveI : Fintype (κ 𝒪ᵥ) := Fintype.ofFinite _
  have hū : residue (𝒪ᵥ) u ≠ 0 := IsUnit.ne_zero (hu.map (residue (𝒪ᵥ)))
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one (residue (𝒪ᵥ) u) hū
end Deformation.TeichmullerDecomp
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
namespace Deformation
namespace TeichmullerDecomp

theorem exists_rootOfUnity_card_sub_one_congr {u : 𝒪ᵥ} (hu : IsUnit u) :
    ∃ ω : 𝒪ᵥ, ω ^ (Nat.card (κ 𝒪ᵥ) - 1) = 1 ∧ ω - u ∈ 𝔪 (𝒪ᵥ) := by
  set f : (𝒪ᵥ)[X] := X ^ (Nat.card (κ 𝒪ᵥ) - 1) - C 1 with hfdef
  have hfmonic : f.Monic :=
    monic_X_pow_sub_C (1 : 𝒪ᵥ) (card_residueField_sub_one_ne_zero' v)
  have hfeval : f.eval u ∈ 𝔪 (𝒪ᵥ) := by
    simpa [hfdef] using pow_card_sub_one_sub_one_mem_maximalIdeal v hu
  have hfderiv : IsUnit (f.derivative.eval u) := by
    simp only [hfdef, derivative_sub, derivative_X_pow, derivative_C, sub_zero,
      eval_mul, eval_natCast, eval_pow, eval_X, map_natCast]
    exact (isUnit_card_residueField_sub_one' v).mul (hu.pow _)
  obtain ⟨ω, hroot, hmem⟩ := HenselianLocalRing.is_henselian f hfmonic u hfeval hfderiv
  refine ⟨ω, ?_, hmem⟩
  have h : ω ^ (Nat.card (κ 𝒪ᵥ) - 1) - 1 = 0 := by simpa [hfdef] using hroot
  linear_combination h
end Deformation.TeichmullerDecomp
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section

namespace FLT
namespace Gapsw47T5WildDifferentLink2bGlobalisation

p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open "UniqueFactorizationMonoid P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.UniqueFactorizationMonoid"
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
open FLT.Gapsw45T4WildDifferentEisensteinLink1
open FLT.Gapsw46T5WildDifferentEisensteinLink2a
open FLT.Gapsw44T4WildDifferentSummationWs
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine

set_option maxHeartbeats 1600000 in

theorem gapsw47_t5_p2_natCast_eq_unit_mul_pow
    {B : Type*} [CommRing B] [IsLocalRing B]
    (π : B) (e : ℕ) (u3 : Bˣ) (h3 : ((3 : ℕ) : B) = (u3 : B) * π ^ e)
    (hπ : ¬ IsUnit π) (he : e ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ u : Bˣ, ((n : ℕ) : B) = (u : B) * π ^ (e * padicValNat 3 n) := by
  have _em := Classical.em
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hπm : π ∈ IsLocalRing.maximalIdeal B := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have h3mem : ((3 : ℕ) : B) ∈ IsLocalRing.maximalIdeal B := by
    rw [h3]
    refine Ideal.mul_mem_left _ _ ?_
    have he' : e - 1 + 1 = e := by omega
    rw [← he', pow_succ]
    exact Ideal.mul_mem_left _ _ hπm

  have munit : ∀ m : ℕ, ¬ (3 ∣ m) → IsUnit ((m : ℕ) : B) := by
    intro m hm
    by_contra hu
    have hmmem : ((m : ℕ) : B) ∈ IsLocalRing.maximalIdeal B := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hg : Nat.gcd 3 m = 1 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm
    have hZ : (1 : ℤ) = 3 * Nat.gcdA 3 m + m * Nat.gcdB 3 m := by
      have h := Nat.gcd_eq_gcd_ab 3 m
      rw [hg] at h
      exact_mod_cast h
    have h1B : (1 : B) = ((3 : ℕ) : B) * ((Nat.gcdA 3 m : ℤ) : B)
        + ((m : ℕ) : B) * ((Nat.gcdB 3 m : ℤ) : B) := by
      have h : ((1 : ℤ) : B)
          = ((3 * Nat.gcdA 3 m + (m : ℤ) * Nat.gcdB 3 m : ℤ) : B) := by
        rw [← hZ]
      push_cast at h
      push_cast
      linear_combination h
    have hone : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
      rw [h1B]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h3mem)
        (Ideal.mul_mem_right _ _ hmmem)
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      ((Ideal.eq_top_iff_one _).mpr hone)

  set k := padicValNat 3 n with hk
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := 3) (n := n)
  rw [← hk] at hm
  have hm3 : ¬ (3 ∣ m) := by
    rintro ⟨t, rfl⟩
    have hdvd : (3 : ℕ) ^ (k + 1) ∣ n := ⟨t, by rw [hm]; ring⟩
    have hle := (padicValNat_dvd_iff_le hn).mp hdvd
    rw [← hk] at hle
    omega
  obtain ⟨w, hw⟩ := munit m hm3
  refine ⟨u3 ^ k * w, ?_⟩
  have hcast : ((n : ℕ) : B)
      = ((3 : ℕ) : B) ^ k * ((m : ℕ) : B) := by
    rw [hm]
    push_cast
    ring
  rw [hcast, h3, ← hw, Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]
  ring

set_option maxHeartbeats 3200000 in

theorem gapsw47_t5_p2_pow_mem_differentIdeal_of_local_model
    (A K L B : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Module.Finite A B]
    (π : B) (hπ : Irreducible π)
    (e : ℕ) (he0 : 0 < e)
    (hdeg : ((minpoly A π).map (algebraMap A B)).natDegree = e)
    (h3A : Irreducible (3 : A))
    (u3 : Bˣ) (h3B : algebraMap A B (3 : A) = (u3 : B) * π ^ e)
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ Ideal.span {π}) :
    π ^ (e - 1 + e * padicValNat 3 e) ∈ differentIdeal A B := by
  have _em := Classical.em

  have hmono : Algebra.adjoin A {π} = ⊤ :=
    gapsw47_t5_p1_adjoin_eq_top_of_irreducible π e (3 : A) h3A u3 h3B hres

  have hcv := gapsw47_t5_p1_mapped_coeff_mul_succ_shape π e (3 : A) h3A u3 h3B
    (minpoly A π)

  have h3B' : ((3 : ℕ) : B) = (u3 : B) * π ^ e := by
    rw [Nat.cast_ofNat, ← h3B, map_ofNat]
  obtain ⟨ue, heB⟩ := gapsw47_t5_p2_natCast_eq_unit_mul_pow π e u3 h3B'
    hπ.not_isUnit he0.ne' e he0.ne'

  exact gapsw46_t5_pow_mem_differentIdeal_of_monogenic A K L π hπ hmono e he0 hdeg
    hcv ue (padicValNat 3 e) heB

set_option maxHeartbeats 3200000 in

theorem gapsw47_t5_p2_ramificationIdx_ne_zero
    (K : Type*) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    (Ideal.span {(3 : ℤ)}).ramificationIdx' P ≠ 0 := by
  have _em := Classical.em
  classical
  haveI := FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff
    FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot] at hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI := hPprime
  haveI := hPlies
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot
    rw [Ideal.LiesOver.over (p := Ideal.span {(3 : ℤ)}) (P := (⊥ : Ideal (𝓞 K))),
      Ideal.under_def]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
  haveI : P.IsMaximal := hPprime.isMaximal hPbot
  exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P
    FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot

set_option maxHeartbeats 3200000 in

theorem gapsw47_t5_p2_count_le_of_not_pow_succ_dvd
    (K : Type*) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (d : ℕ)
    (hnd : ¬ P ^ (d + 1) ∣ differentIdeal ℤ (𝓞 K)) :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤ d := by
  have _em := Classical.em
  classical
  haveI := FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff
    FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot] at hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI := hPprime
  haveI := hPlies
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply FLT.Gapsw7X1cPerPlaceDiscDecomposition.gapsw7_x1c_span_three_ne_bot
    rw [Ideal.LiesOver.over (p := Ideal.span {(3 : ℤ)}) (P := (⊥ : Ideal (𝓞 K))),
      Ideal.under_def]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
  have hD0 : differentIdeal ℤ (𝓞 K) ≠ 0 := by
    simpa using (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))
  have hPirr : Irreducible P := (Ideal.prime_of_isPrime hPbot hPprime).irreducible
  by_contra hcon
  push Not at hcon
  apply hnd
  rw [pow_dvd_iff_le_emultiplicity,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPirr hD0,
    normalize_eq]
  have hsucc : d + 1 ≤ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := hcon
  exact_mod_cast hsucc

def Gapsw47T5WildDifferentCompletionTransportResidual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K)),
    P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
    3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P →
    ¬ P ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' P
        + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
          * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P))
      ∣ differentIdeal ℤ (𝓞 K)

theorem gapsw47_t5_p2_completionTransportResidual_pin :
    Gapsw47T5WildDifferentCompletionTransportResidual =
      (∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K)),
        P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (𝓞 K) →
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P →
        ¬ P ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' P
            + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
              * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P))
          ∣ differentIdeal ℤ (𝓞 K)) := by
  have _em := Classical.em
  rfl

set_option maxHeartbeats 3200000 in

theorem gapsw47_t5_p2_wildDifferentUpperBoundSupply_of_completionTransport
    (hatom : Gapsw47T5WildDifferentCompletionTransportResidual) :
    Gapsw44T4WildDifferentUpperBoundSupply := by
  have _em := Classical.em
  rw [gapsw44_t4_wildDifferentUpperBoundSupply_pin]
  intro K _ _ P hP
  by_cases hw : 3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P
  ·
    have he0 := gapsw47_t5_p2_ramificationIdx_ne_zero K P hP
    have hnd := hatom K P hP hw
    have harith : (Ideal.span {(3 : ℤ)}).ramificationIdx' P
        + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
          * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P)
        = ((Ideal.span {(3 : ℤ)}).ramificationIdx' P
            + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
              * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) - 1) + 1 := by
      omega
    rw [harith] at hnd
    exact gapsw47_t5_p2_count_le_of_not_pow_succ_dvd K P hP _ hnd
  ·
    exact gapsw44_t4_upperBoundSupply_tame_slice K P hP hw

end FLT.Gapsw47T5WildDifferentLink2bGlobalisation
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw60T2TeichmuellerSectionAtoms
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"

theorem gapsw60_t2_one_lt_card_global_residue
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    1 < Nat.card ((𝓞 K) ⧸ v.asIdeal) := by
  have _em := Classical.em
  rw [← FLT.GL2GeneralPlaceCongruenceIndexExplicit.natCard_residueField_adicCompletionIntegers
    K v]
  exact Deformation.TeichmullerDecomp.one_lt_card_residueField' v
end FLT.Gapsw60T2TeichmuellerSectionAtoms
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw60T2TeichmuellerSectionAtoms
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"

theorem gapsw60_t2_teichmuller_root_exists
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (b : v.adicCompletionIntegers K) :
    ∃ t : v.adicCompletionIntegers K,
      t ^ Nat.card ((𝓞 K) ⧸ v.asIdeal) = t ∧
      b - t ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  have hq : 1 < Nat.card ((𝓞 K) ⧸ v.asIdeal) := gapsw60_t2_one_lt_card_global_residue K v
  by_cases hb : IsUnit b
  · obtain ⟨ω, hpow, hmem⟩ :=
      Deformation.TeichmullerDecomp.exists_rootOfUnity_card_sub_one_congr v hb
    rw [FLT.GL2GeneralPlaceCongruenceIndexExplicit.natCard_residueField_adicCompletionIntegers
      K v] at hpow
    refine ⟨ω, ?_, ?_⟩
    · calc ω ^ Nat.card ((𝓞 K) ⧸ v.asIdeal)
          = ω ^ ((Nat.card ((𝓞 K) ⧸ v.asIdeal) - 1) + 1) := by
            rw [Nat.sub_add_cancel hq.le]
        _ = ω ^ (Nat.card ((𝓞 K) ⧸ v.asIdeal) - 1) * ω := pow_succ ω _
        _ = 1 * ω := by rw [hpow]
        _ = ω := one_mul ω
    · have h := neg_mem hmem
      rwa [neg_sub] at h
  · refine ⟨0, ?_, ?_⟩
    · exact zero_pow (by omega)
    · rw [sub_zero]
      exact (IsLocalRing.mem_maximalIdeal b).mpr (mem_nonunits_iff.mpr hb)
end FLT.Gapsw60T2TeichmuellerSectionAtoms
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw60T2TeichmuellerSectionAtoms
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 1600000 in

theorem gapsw60_t2_teichmuller_root_unique
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {t₁ t₂ : v.adicCompletionIntegers K}
    (h₁ : t₁ ^ Nat.card ((𝓞 K) ⧸ v.asIdeal) = t₁)
    (h₂ : t₂ ^ Nat.card ((𝓞 K) ⧸ v.asIdeal) = t₂)
    (hsub : t₁ - t₂ ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    t₁ = t₂ := by
  have _em := Classical.em
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    (ResidueFieldEquivCompletionResidueField K v).toEquiv.finite_iff.mp
      (FLT.Gapsw58T5WittASideEngineAtoms.gapsw58_t5_residue_field_finite K v)
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    Fintype.ofFinite _

  have hqκ : ((Nat.card ((𝓞 K) ⧸ v.asIdeal) : ℕ) :
      IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = 0 := by
    rw [← FLT.GL2GeneralPlaceCongruenceIndexExplicit.natCard_residueField_adicCompletionIntegers
      K v, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero _

  have ha : ((X : Polynomial (v.adicCompletionIntegers K)) ^
      Nat.card ((𝓞 K) ⧸ v.asIdeal) - X).eval t₁ = 0 := by
    simp only [eval_sub, eval_pow, eval_X]
    exact sub_eq_zero_of_eq h₁
  have hb : ((X : Polynomial (v.adicCompletionIntegers K)) ^
      Nat.card ((𝓞 K) ⧸ v.asIdeal) - X).eval t₂ = 0 := by
    simp only [eval_sub, eval_pow, eval_X]
    exact sub_eq_zero_of_eq h₂

  have hever : (Polynomial.derivative ((X : Polynomial (v.adicCompletionIntegers K)) ^
      Nat.card ((𝓞 K) ⧸ v.asIdeal) - X)).eval t₁
      = (Nat.card ((𝓞 K) ⧸ v.asIdeal) : v.adicCompletionIntegers K) *
          t₁ ^ (Nat.card ((𝓞 K) ⧸ v.asIdeal) - 1) - 1 := by
    simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul,
      eval_C, eval_pow, eval_X, eval_one]

  have hresval : IsLocalRing.residue (v.adicCompletionIntegers K)
      ((Nat.card ((𝓞 K) ⧸ v.asIdeal) : v.adicCompletionIntegers K) *
        t₁ ^ (Nat.card ((𝓞 K) ⧸ v.asIdeal) - 1) - 1) = -1 := by
    rw [RingHom.map_sub (IsLocalRing.residue (v.adicCompletionIntegers K)),
      RingHom.map_mul (IsLocalRing.residue (v.adicCompletionIntegers K)),
      RingHom.map_one (IsLocalRing.residue (v.adicCompletionIntegers K)),
      map_natCast (IsLocalRing.residue (v.adicCompletionIntegers K)),
      hqκ, zero_mul, zero_sub]
  have hunit : IsUnit ((Polynomial.derivative
      ((X : Polynomial (v.adicCompletionIntegers K)) ^
        Nat.card ((𝓞 K) ⧸ v.asIdeal) - X)).eval t₁) := by
    rw [hever, ← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have h0 : IsLocalRing.residue (v.adicCompletionIntegers K)
        ((Nat.card ((𝓞 K) ⧸ v.asIdeal) : v.adicCompletionIntegers K) *
          t₁ ^ (Nat.card ((𝓞 K) ⧸ v.asIdeal) - 1) - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hresval] at h0
    exact one_ne_zero (neg_eq_zero.mp h0)
  have hnu : ¬IsUnit (t₁ - t₂) := fun h => (IsLocalRing.notMem_maximalIdeal.mpr h) hsub
  exact IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha hb hnu hunit
end FLT.Gapsw60T2TeichmuellerSectionAtoms
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw49T5CompletionTransportAtomWeld
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw44T4WildDifferentSummationWs
set_option maxHeartbeats 1600000 in

theorem gapsw49_t5_completionTransportResidual_of_pieceIResidual
    (hres : Gapsw48T5CompletionTransportPieceIResidual) :
    Gapsw47T5WildDifferentCompletionTransportResidual := by
  have _em := Classical.em
  rw [gapsw47_t5_p2_completionTransportResidual_pin]
  exact gapsw48_t5_wild_notDvd_of_pieceIResidual hres
end FLT.Gapsw49T5CompletionTransportAtomWeld
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw49T5CompletionTransportAtomWeld
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw44T4WildDifferentSummationWs
set_option maxHeartbeats 1600000 in

theorem gapsw49_t5_wildDifferentUpperBoundSupply_of_pieceIResidual
    (hres : Gapsw48T5CompletionTransportPieceIResidual) :
    Gapsw44T4WildDifferentUpperBoundSupply := by
  have _em := Classical.em
  exact gapsw47_t5_p2_wildDifferentUpperBoundSupply_of_completionTransport
    (gapsw49_t5_completionTransportResidual_of_pieceIResidual hres)
end FLT.Gapsw49T5CompletionTransportAtomWeld
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T7AbstractBaseEngineFire
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw7X3bDerivativeDifferentSlice
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw78T6AbstractBaseAKLBFrame
p2m_open "IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"
set_option maxHeartbeats 6400000 in

theorem gapsw78_t7_inertiaDeg_eq_one_of_abstractResidueSurj
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    (h3A : Irreducible (3 : A))
    (h3mem : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ∈ gapsw7X1mCompletionIdeal K P hP)
    (hresA : ∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
      ∃ a : A, b - algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
        ∈ gapsw7X1mCompletionIdeal K P hP) :
    (Ideal.span {(3 : A)}).inertiaDeg'
        (gapsw7X1mCompletionIdeal K P hP) = 1 := by
  have _em := Classical.em
  classical
  haveI h3max : (Ideal.span {(3 : A)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible h3A

  have h3map : algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) 3
      = (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    gapsw54_t3_algebraMap_three_reduction K (gapsw7X1mPlace K P hP) A
  have hcomap :
      (gapsw7X1mCompletionIdeal K P hP).comap
          (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
        = Ideal.span {(3 : A)} := by
    refine (h3max.eq_of_le ?_ ?_).symm
    · rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_comap, map_one]
      exact fun h1 => (gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP ▸
        IsLocalRing.maximalIdeal.isMaximal _).ne_top
          ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, h3map]
      exact h3mem
  haveI : (gapsw7X1mCompletionIdeal K P hP).LiesOver (Ideal.span {(3 : A)}) :=
    ⟨hcomap.symm⟩
  rw [Ideal.inertiaDeg_algebraMap]

  have hsurj : Function.Surjective
      (algebraMap (A ⧸ Ideal.span {(3 : A)})
        ((gapsw7X1mPlace K P hP).adicCompletionIntegers K
          ⧸ gapsw7X1mCompletionIdeal K P hP)) := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hresA b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩

    show Ideal.Quotient.mk _
        (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a)
      = Ideal.Quotient.mk _ b
    exact Ideal.Quotient.eq.mpr (neg_sub b _ ▸ neg_mem ha)

  haveI : (gapsw7X1mCompletionIdeal K P hP).IsMaximal :=
    gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP ▸
      IsLocalRing.maximalIdeal.isMaximal _
  have hinj : Function.Injective
      (algebraMap (A ⧸ Ideal.span {(3 : A)})
        ((gapsw7X1mPlace K P hP).adicCompletionIntegers K
          ⧸ gapsw7X1mCompletionIdeal K P hP)) := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq, ← hcomap, Ideal.mem_comap, map_sub]
    exact Ideal.Quotient.eq.mp hxy
  exact Module.finrank_of_bijective_algebraMap ⟨hinj, hsurj⟩
end FLT.Gapsw78T7AbstractBaseEngineFire
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw78T7AbstractBaseEngineFire
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw7X3bDerivativeDifferentSlice
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw78T6AbstractBaseAKLBFrame
p2m_open "IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"
set_option maxHeartbeats 16000000 in

theorem gapsw78_t7_maximalIdeal_pow_le_of_abstractBase
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (hwild : 3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.Finite A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.IsTorsionFree A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    (h3A : Irreducible (3 : A))
    (hresA : ∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
      ∃ a : A, b - algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
        ∈ gapsw7X1mCompletionIdeal K P hP) :
    gapsw7X1mCompletionIdeal K P hP
      ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' P - 1
        + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
          * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P))
      ≤ differentIdeal A
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) := by
  have _em := Classical.em
  classical

  letI : Algebra A ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    ((algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        ((gapsw7X1mPlace K P hP).adicCompletion K)).comp
      (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))).toAlgebra
  letI : IsScalarTower A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul A ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      ((IsFractionRing.injective ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ((gapsw7X1mPlace K P hP).adicCompletion K)).comp
        (gapsw78_t6_algebraMap_injective K P hP A h3A))
  letI : Algebra (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    FractionRing.liftAlgebra A ((gapsw7X1mPlace K P hP).adicCompletion K)
  letI : IsScalarTower A (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    FractionRing.isScalarTower_liftAlgebra A
      ((gapsw7X1mPlace K P hP).adicCompletion K)
  letI : IsIntegralClosure ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) A
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    gapsw78_t6_isIntegralClosure K P hP A
  letI : Module.Finite (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    gapsw78_t6_module_finite_fractionRing K P hP A h3A
  haveI : CharZero A := gapsw78_t6_charZero A h3A
  haveI : CharZero (FractionRing A) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective A (FractionRing A))
  haveI : Algebra.IsIntegral (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    Algebra.IsIntegral.of_finite (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K)

  letI : IsDedekindDomain ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    gapsw7_x4g_isDedekindDomain_carrierIntegers K P hP

  set e := (Ideal.span {(3 : ℤ)}).ramificationIdx' P
  have he0 : 0 < e :=
    Nat.pos_of_ne_zero (gapsw47_t5_p2_ramificationIdx_ne_zero K P hP)

  obtain ⟨π, hπ⟩ := adicCompletion.exists_uniformizer K (gapsw7X1mPlace K P hP)
  have hπval : Valued.v (π : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-1 : ℤ) := hπ
  have hπirr : Irreducible π :=
    gapsw54_t3_uniformizer_irreducible (𝓞 K) K (gapsw7X1mPlace K P hP) π hπval
  have hspan : Ideal.span {π} = gapsw7X1mCompletionIdeal K P hP := by
    rw [gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP,
      adicCompletion.maximalIdeal_eq_span_uniformizer K
        (gapsw7X1mPlace K P hP) hπval]

  have hval3 : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-(e : ℤ)) := by
    rw [← map_ofNat (algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)) 3,
      algebraMap_completionIntegers,
      (gapsw7X1mPlace K P hP).valuedAdicCompletion_eq_valuation,
      (gapsw7X1mPlace K P hP).valuation_of_algebraMap,
      gapsw54_t3_intValuation_three_eq_ramificationIdx K (gapsw7X1mPlace K P hP),
      gapsw7_x1m_place_asIdeal K P hP]
  have h3ne : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ≠ 0 := by
    intro h; rw [h, ZeroMemClass.coe_zero, map_zero] at hval3
    exact WithZero.exp_ne_zero hval3.symm
  obtain ⟨n, u0, hu⟩ := adicCompletion.eq_pow_uniformizer_mul_unit K
    (gapsw7X1mPlace K P hP) h3ne hπval
  have hvu : Valued.v ((u0 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K) = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one _).mp u0.isUnit
  have hne : n = e := by
    have hun : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hP).adicCompletion K)
        = WithZero.exp (-(n : ℤ)) := by
      rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
        hπval, hvu, mul_one, ← WithZero.exp_nsmul, WithZero.exp_inj]; simp
    have h := hun.symm.trans hval3; rw [WithZero.exp_inj] at h; omega
  have h3fac : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      = (u0 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) * π ^ e := by
    rw [hu, hne, mul_comm]
  have h3B : algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) 3
      = (u0 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) * π ^ e := by
    rw [gapsw54_t3_algebraMap_three_reduction K (gapsw7X1mPlace K P hP) A, h3fac]
  have hres' : ∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
      ∃ a : A, b - algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
          ∈ Ideal.span {π} := by
    intro b; obtain ⟨a, ha⟩ := hresA b; exact ⟨a, hspan ▸ ha⟩

  have hmono : Algebra.adjoin A {π} = ⊤ :=
    gapsw47_t5_p1_adjoin_eq_top_of_irreducible π e (3 :) h3A u0 h3B hres'

  have hint : IsIntegral A π := Algebra.IsIntegral.isIntegral π
  have hmonic : (minpoly A π).Monic := minpoly.monic hint
  have hdegA : ((minpoly A π).map
        (algebraMap A
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))).natDegree = e := by
    rw [hmonic.natDegree_map]

    have hfrac : minpoly (FractionRing A)
          (algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
            ((gapsw7X1mPlace K P hP).adicCompletion K) π)
        = (minpoly A π).map (algebraMap A (FractionRing A)) :=
      minpoly.isIntegrallyClosed_eq_field_fractions
        (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) hint
    have hdegeq : (minpoly A π).natDegree
        = (minpoly (FractionRing A)
            (algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
              ((gapsw7X1mPlace K P hP).adicCompletion K) π)).natDegree := by
      rw [hfrac, hmonic.natDegree_map]
    rw [hdegeq]

    have hadj : Algebra.adjoin (FractionRing A)
        {algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ((gapsw7X1mPlace K P hP).adicCompletion K) π} = ⊤ :=
      gapsw7_x3b_adjoin_fractionField_eq_top_of_monogenic A
        (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) π hmono
    set πL := algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ((gapsw7X1mPlace K P hP).adicCompletion K) π with hπL
    have hxL : IsIntegral (FractionRing A) πL := Algebra.IsIntegral.isIntegral πL
    have hIF : (FractionRing A)⟮πL⟯
        = (⊤ : IntermediateField (FractionRing A)
            ((gapsw7X1mPlace K P hP).adicCompletion K)) :=
      IntermediateField.toSubalgebra_injective <| by
        rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
            hxL.isAlgebraic, hadj, IntermediateField.top_toSubalgebra]
    rw [← IntermediateField.adjoin.finrank hxL, hIF,
      IntermediateField.finrank_top']

    haveI h3max : (Ideal.span {(3 : A)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible h3A
    have hpne : (Ideal.span {(3 : A)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact h3A.ne_zero
    have hmaxeq : gapsw7X1mCompletionIdeal K P hP
        = IsLocalRing.maximalIdeal
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
      gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP
    have hef := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) hpne
    rw [← hmaxeq] at hef

    have h3mem : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        ∈ gapsw7X1mCompletionIdeal K P hP := by
      rw [h3fac, ← hspan]
      exact Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self π) e he0)
    rw [gapsw78_t7_inertiaDeg_eq_one_of_abstractResidueSurj K P hP A h3A
        h3mem hresA, mul_one] at hef

    have hmap3 : Ideal.map
          (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
          (Ideal.span {(3 : A)})
        = gapsw7X1mCompletionIdeal K P hP ^ e := by
      rw [Ideal.map_span, Set.image_singleton, h3B,
        Ideal.span_singleton_mul_left_unit u0.isUnit,
        ← Ideal.span_singleton_pow, hspan]
    have hPne : gapsw7X1mCompletionIdeal K P hP ≠ ⊥ := by
      rw [← hspan, Ne, Ideal.span_singleton_eq_bot]; exact hπirr.ne_zero
    have hPprime : (gapsw7X1mCompletionIdeal K P hP).IsPrime :=
      (hmaxeq ▸ IsLocalRing.maximalIdeal.isMaximal _ :
        (gapsw7X1mCompletionIdeal K P hP).IsMaximal).isPrime
    have hmapne : Ideal.map
          (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
          (Ideal.span {(3 : A)}) ≠ ⊥ :=
      hmap3 ▸ pow_ne_zero e hPne
    have hPirr : Irreducible (gapsw7X1mCompletionIdeal K P hP) :=
      (Ideal.prime_of_isPrime hPne hPprime).irreducible
    have hramloc : (Ideal.span {(3 : A)}).ramificationIdx'
        (gapsw7X1mCompletionIdeal K P hP) = e := by
      rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
          hmapne hPprime hPne, hmap3,
        UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
        UniqueFactorizationMonoid.normalizedFactors_irreducible hPirr,
        normalize_eq, Multiset.count_singleton_self, mul_one]
    omega

  have hengine : π ^ (e - 1 + e * padicValNat 3 e)
      ∈ differentIdeal A
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    gapsw47_t5_p2_pow_mem_differentIdeal_of_local_model A
      (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K)
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      π hπirr e he0 hdegA h3A u0 h3B hres'

  rw [← hspan, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
  exact hengine
end FLT.Gapsw78T7AbstractBaseEngineFire
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section

namespace FLT
namespace Gapsw61T2TeichmuellerSectionFunction

p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw60T2TeichmuellerSectionAtoms

set_option maxHeartbeats 1600000 in

theorem gapsw61_t2_residue_eq_of_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {a b : v.adicCompletionIntegers K}
    (h : a - b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    IsLocalRing.residue (v.adicCompletionIntegers K) a =
      IsLocalRing.residue (v.adicCompletionIntegers K) b := by
  have _em := Classical.em
  have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (a - b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
  rw [RingHom.map_sub
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))),
    sub_eq_zero] at h0
  exact h0

set_option maxHeartbeats 1600000 in

theorem gapsw61_t2_sub_mem_of_residue_eq
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {a b : v.adicCompletionIntegers K}
    (h : IsLocalRing.residue (v.adicCompletionIntegers K) a =
      IsLocalRing.residue (v.adicCompletionIntegers K) b) :
    a - b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    RingHom.map_sub
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))),
    sub_eq_zero]
  exact h

noncomputable def gapsw61_t2_classLift
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) : v.adicCompletionIntegers K :=
  (IsLocalRing.residue_surjective
    (ResidueFieldEquivCompletionResidueField K v x)).choose

set_option maxHeartbeats 1600000 in

theorem gapsw61_t2_classLift_residue
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers K) (gapsw61_t2_classLift K v x) =
      ResidueFieldEquivCompletionResidueField K v x := by
  have _em := Classical.em
  exact (IsLocalRing.residue_surjective
    (ResidueFieldEquivCompletionResidueField K v x)).choose_spec

noncomputable def gapsw61_t2_teichmullerSection
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) : v.adicCompletionIntegers K :=
  (gapsw60_t2_teichmuller_root_exists K v (gapsw61_t2_classLift K v x)).choose

set_option maxHeartbeats 1600000 in

theorem gapsw61_t2_teichmullerSection_pow
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) :
    gapsw61_t2_teichmullerSection K v x ^ Nat.card ((𝓞 K) ⧸ v.asIdeal) =
      gapsw61_t2_teichmullerSection K v x := by
  have _em := Classical.em
  exact (gapsw60_t2_teichmuller_root_exists K v (gapsw61_t2_classLift K v x)).choose_spec.1

set_option maxHeartbeats 1600000 in

theorem gapsw61_t2_classLift_sub_teichmullerSection_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) :
    gapsw61_t2_classLift K v x - gapsw61_t2_teichmullerSection K v x ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  exact (gapsw60_t2_teichmuller_root_exists K v (gapsw61_t2_classLift K v x)).choose_spec.2

set_option maxHeartbeats 1600000 in

theorem gapsw61_t2_teichmullerSection_residue
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers K) (gapsw61_t2_teichmullerSection K v x) =
      ResidueFieldEquivCompletionResidueField K v x := by
  have _em := Classical.em
  have h := gapsw61_t2_residue_eq_of_sub_mem K v
    (gapsw61_t2_classLift_sub_teichmullerSection_mem K v x)
  rw [← h]
  exact gapsw61_t2_classLift_residue K v x

set_option maxHeartbeats 1600000 in

theorem gapsw61_t2_teichmullerSection_eq_of_pow_eq_of_residue_eq
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) {t : v.adicCompletionIntegers K}
    (hpow : t ^ Nat.card ((𝓞 K) ⧸ v.asIdeal) = t)
    (hres : IsLocalRing.residue (v.adicCompletionIntegers K) t =
      ResidueFieldEquivCompletionResidueField K v x) :
    t = gapsw61_t2_teichmullerSection K v x := by
  have _em := Classical.em
  refine gapsw60_t2_teichmuller_root_unique K v hpow
    (gapsw61_t2_teichmullerSection_pow K v x) ?_
  exact gapsw61_t2_sub_mem_of_residue_eq K v
    (hres.trans (gapsw61_t2_teichmullerSection_residue K v x).symm)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw61_t2_teichmullerSection_one
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    gapsw61_t2_teichmullerSection K v (1 : (𝓞 K) ⧸ v.asIdeal) = 1 := by
  have _em := Classical.em
  refine (gapsw61_t2_teichmullerSection_eq_of_pow_eq_of_residue_eq K v 1 ?_ ?_).symm
  · exact one_pow _
  · rw [RingHom.map_one (IsLocalRing.residue (v.adicCompletionIntegers K))]
    exact (map_one (ResidueFieldEquivCompletionResidueField K v)).symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw61_t2_teichmullerSection_zero
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    gapsw61_t2_teichmullerSection K v (0 : (𝓞 K) ⧸ v.asIdeal) = 0 := by
  have _em := Classical.em
  have hq := gapsw60_t2_one_lt_card_global_residue K v
  refine (gapsw61_t2_teichmullerSection_eq_of_pow_eq_of_residue_eq K v 0 ?_ ?_).symm
  · exact zero_pow (by omega)
  · rw [RingHom.map_zero (IsLocalRing.residue (v.adicCompletionIntegers K))]
    exact (_root_.map_zero (ResidueFieldEquivCompletionResidueField K v)).symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw61_t2_teichmullerSection_mul
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x y : (𝓞 K) ⧸ v.asIdeal) :
    gapsw61_t2_teichmullerSection K v (x * y) =
      gapsw61_t2_teichmullerSection K v x * gapsw61_t2_teichmullerSection K v y := by
  have _em := Classical.em
  refine (gapsw61_t2_teichmullerSection_eq_of_pow_eq_of_residue_eq K v (x * y) ?_ ?_).symm
  · rw [mul_pow, gapsw61_t2_teichmullerSection_pow K v x,
      gapsw61_t2_teichmullerSection_pow K v y]
  · rw [RingHom.map_mul (IsLocalRing.residue (v.adicCompletionIntegers K)),
      gapsw61_t2_teichmullerSection_residue K v x,
      gapsw61_t2_teichmullerSection_residue K v y]
    exact (RingEquiv.map_mul (ResidueFieldEquivCompletionResidueField K v) x y).symm

set_option maxHeartbeats 1600000 in

theorem gapsw61_t2_sub_teichmullerSection_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (b : v.adicCompletionIntegers K) :
    b - gapsw61_t2_teichmullerSection K v
        ((ResidueFieldEquivCompletionResidueField K v).symm
          (IsLocalRing.residue (v.adicCompletionIntegers K) b)) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  refine gapsw61_t2_sub_mem_of_residue_eq K v ?_
  rw [gapsw61_t2_teichmullerSection_residue K v
    ((ResidueFieldEquivCompletionResidueField K v).symm
      (IsLocalRing.residue (v.adicCompletionIntegers K) b)),
    RingEquiv.apply_symm_apply]

end FLT.Gapsw61T2TeichmuellerSectionFunction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section

namespace FLT
namespace Gapsw62T2PiadicDigitExpansion

p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw60T2TeichmuellerSectionAtoms
open FLT.Gapsw61T2TeichmuellerSectionFunction

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_uniformizer_exists
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ∃ π : v.adicCompletionIntegers K,
      Irreducible π ∧
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} ∧
      π ≠ 0 := by
  have _em := Classical.em
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  exact ⟨π, hπ, hπ.maximalIdeal_eq, hπ.ne_zero⟩

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_pi_mem_maximalIdeal
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π}) :
    π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  rw [hspan]
  exact Ideal.mem_span_singleton_self π

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_maximalIdeal_pow_eq_span
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (n : ℕ) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n = Ideal.span {π ^ n} := by
  have _em := Classical.em
  rw [hspan, Ideal.span_singleton_pow]

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_term_mem_pow
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (c : (𝓞 K) ⧸ v.asIdeal) {m i : ℕ} (hmi : m ≤ i) :
    gapsw61_t2_teichmullerSection K v c * π ^ i ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m := by
  have _em := Classical.em
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmi
  have hπ : π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    gapsw62_t2_pi_mem_maximalIdeal K v π hspan
  have hkey : gapsw61_t2_teichmullerSection K v c * π ^ (m + d)
      = (gapsw61_t2_teichmullerSection K v c * π ^ d) * π ^ m := by ring
  rw [hkey]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπ m)

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_digit_step
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    {n : ℕ} {r : v.adicCompletionIntegers K}
    (hr : r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :
    ∃ c : (𝓞 K) ⧸ v.asIdeal,
      r - gapsw61_t2_teichmullerSection K v c * π ^ n ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) := by
  have _em := Classical.em
  rw [gapsw62_t2_maximalIdeal_pow_eq_span K v π hspan n, Ideal.mem_span_singleton] at hr
  obtain ⟨b, hb⟩ := hr
  refine ⟨(ResidueFieldEquivCompletionResidueField K v).symm
    (IsLocalRing.residue (v.adicCompletionIntegers K) b), ?_⟩
  have hbc := gapsw61_t2_sub_teichmullerSection_mem K v b
  have hkey : r - gapsw61_t2_teichmullerSection K v
        ((ResidueFieldEquivCompletionResidueField K v).symm
          (IsLocalRing.residue (v.adicCompletionIntegers K) b)) * π ^ n
      = π ^ n * (b - gapsw61_t2_teichmullerSection K v
        ((ResidueFieldEquivCompletionResidueField K v).symm
          (IsLocalRing.residue (v.adicCompletionIntegers K) b))) := by
    rw [hb]; ring
  rw [hkey, pow_succ]
  exact Ideal.mul_mem_mul
    (Ideal.pow_mem_pow (gapsw62_t2_pi_mem_maximalIdeal K v π hspan) n) hbc

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_partialSum_exists
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (x : v.adicCompletionIntegers K) :
    ∀ n : ℕ, ∃ a : ℕ → (𝓞 K) ⧸ v.asIdeal,
      x - ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
  have _em := Classical.em
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨c, hc⟩ := gapsw62_t2_digit_step K v π hspan ha
    refine ⟨Function.update a n c, ?_⟩
    have hsum : ∑ i ∈ Finset.range (n + 1),
          gapsw61_t2_teichmullerSection K v (Function.update a n c i) * π ^ i
        = (∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i)
          + gapsw61_t2_teichmullerSection K v c * π ^ n := by
      rw [Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hi)) c a]
      · rw [Function.update_self n c a]
    rw [hsum, sub_add_eq_sub_sub]
    exact hc

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_partialSum_congr_of_le
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (x : v.adicCompletionIntegers K) (a : ℕ → (𝓞 K) ⧸ v.asIdeal) {m n : ℕ}
    (hmn : m ≤ n)
    (h : x - ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :
    x - ∑ i ∈ Finset.range m, gapsw61_t2_teichmullerSection K v (a i) * π ^ i ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m := by
  have _em := Classical.em
  have hsplit : ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i
      = (∑ i ∈ Finset.range m, gapsw61_t2_teichmullerSection K v (a i) * π ^ i)
        + ∑ i ∈ Finset.Ico m n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le m) hmn).symm
  have hkey : x - ∑ i ∈ Finset.range m, gapsw61_t2_teichmullerSection K v (a i) * π ^ i
      = (x - ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i)
        + ∑ i ∈ Finset.Ico m n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i := by
    rw [hsplit]; ring
  rw [hkey]
  refine Ideal.add_mem _ (Ideal.pow_le_pow_right hmn h) (Ideal.sum_mem _ fun i hi => ?_)
  exact gapsw62_t2_term_mem_pow K v π hspan (a i) (Finset.mem_Ico.mp hi).1

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_digit_eq_of_section_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {c d : (𝓞 K) ⧸ v.asIdeal}
    (h : gapsw61_t2_teichmullerSection K v c - gapsw61_t2_teichmullerSection K v d ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    c = d := by
  have _em := Classical.em
  have hres := gapsw61_t2_residue_eq_of_sub_mem K v h
  rw [gapsw61_t2_teichmullerSection_residue K v c,
    gapsw61_t2_teichmullerSection_residue K v d] at hres
  exact (ResidueFieldEquivCompletionResidueField K v).injective hres

set_option maxHeartbeats 3200000 in

theorem gapsw62_t2_digit_separation
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (hπ0 : π ≠ 0) :
    ∀ (n : ℕ) (a b : ℕ → (𝓞 K) ⧸ v.asIdeal),
      (∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i)
        - (∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (b i) * π ^ i) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n →
      ∀ i < n, a i = b i := by
  have _em := Classical.em
  intro n
  induction n with
  | zero => intro a b _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro a b h
    have hfac : ∀ c : ℕ → (𝓞 K) ⧸ v.asIdeal,
        ∑ j ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (c (j + 1)) * π ^ (j + 1)
          = π * ∑ j ∈ Finset.range n,
              gapsw61_t2_teichmullerSection K v (c (j + 1)) * π ^ j := by
      intro c
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hsplit :
        (∑ j ∈ Finset.range (n + 1), gapsw61_t2_teichmullerSection K v (a j) * π ^ j)
          - (∑ j ∈ Finset.range (n + 1), gapsw61_t2_teichmullerSection K v (b j) * π ^ j)
        = π * ((∑ j ∈ Finset.range n,
                gapsw61_t2_teichmullerSection K v (a (j + 1)) * π ^ j)
              - ∑ j ∈ Finset.range n,
                gapsw61_t2_teichmullerSection K v (b (j + 1)) * π ^ j)
          + (gapsw61_t2_teichmullerSection K v (a 0)
              - gapsw61_t2_teichmullerSection K v (b 0)) := by
      rw [Finset.sum_range_succ'
          (fun j => gapsw61_t2_teichmullerSection K v (a j) * π ^ j) n,
        Finset.sum_range_succ'
          (fun j => gapsw61_t2_teichmullerSection K v (b j) * π ^ j) n]
      simp only [pow_zero, mul_one]
      rw [hfac a, hfac b]
      ring
    rw [hsplit] at h
    have hpiM : π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
      gapsw62_t2_pi_mem_maximalIdeal K v π hspan
    have hd : gapsw61_t2_teichmullerSection K v (a 0)
        - gapsw61_t2_teichmullerSection K v (b 0) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
      have h1 := Ideal.pow_le_self (Nat.succ_ne_zero n) h
      have h2 : π * ((∑ j ∈ Finset.range n,
              gapsw61_t2_teichmullerSection K v (a (j + 1)) * π ^ j)
            - ∑ j ∈ Finset.range n,
              gapsw61_t2_teichmullerSection K v (b (j + 1)) * π ^ j) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
        Ideal.mul_mem_right _ _ hpiM
      have h3 := Ideal.sub_mem _ h1 h2
      rwa [add_sub_cancel_left] at h3
    have h0 : a 0 = b 0 := gapsw62_t2_digit_eq_of_section_sub_mem K v hd
    have hz : gapsw61_t2_teichmullerSection K v (a 0)
        - gapsw61_t2_teichmullerSection K v (b 0) = 0 := by
      rw [h0, sub_self]
    rw [hz, add_zero,
      gapsw62_t2_maximalIdeal_pow_eq_span K v π hspan (n + 1),
      Ideal.mem_span_singleton] at h
    obtain ⟨e, he⟩ := h
    have hAB : (∑ j ∈ Finset.range n,
            gapsw61_t2_teichmullerSection K v (a (j + 1)) * π ^ j)
          - ∑ j ∈ Finset.range n,
            gapsw61_t2_teichmullerSection K v (b (j + 1)) * π ^ j
        = π ^ n * e := by
      apply mul_left_cancel₀ hπ0
      rw [he]
      ring
    have hABmem : (∑ j ∈ Finset.range n,
            gapsw61_t2_teichmullerSection K v (a (j + 1)) * π ^ j)
          - ∑ j ∈ Finset.range n,
            gapsw61_t2_teichmullerSection K v (b (j + 1)) * π ^ j ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
      rw [gapsw62_t2_maximalIdeal_pow_eq_span K v π hspan n, Ideal.mem_span_singleton]
      exact ⟨e, hAB⟩
    have hrec := ih (fun j => a (j + 1)) (fun j => b (j + 1)) hABmem
    intro i hi
    cases i with
    | zero => exact h0
    | succ j => exact hrec j (Nat.lt_of_succ_lt_succ hi)

set_option maxHeartbeats 1600000 in

theorem gapsw62_t2_partialSum_unique
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (hπ0 : π ≠ 0)
    (x : v.adicCompletionIntegers K) (n : ℕ) (a b : ℕ → (𝓞 K) ⧸ v.asIdeal)
    (ha : x - ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
    (hb : x - ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (b i) * π ^ i ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :
    ∀ i < n, a i = b i := by
  have _em := Classical.em
  have h := Ideal.sub_mem _ hb ha
  rw [sub_sub_sub_cancel_left] at h
  exact gapsw62_t2_digit_separation K v π hspan hπ0 n a b h

set_option maxHeartbeats 3200000 in

theorem gapsw62_t2_digitExpansion_exists
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (hπ0 : π ≠ 0)
    (x : v.adicCompletionIntegers K) :
    ∃ a : ℕ → (𝓞 K) ⧸ v.asIdeal, ∀ n : ℕ,
      x - ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (a i) * π ^ i ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
  have _em := Classical.em
  choose F hF using gapsw62_t2_partialSum_exists K v π hspan x
  refine ⟨fun i => F (i + 1) i, fun n => ?_⟩
  have hagree : ∀ i ∈ Finset.range n, F (i + 1) i = F n i := by
    intro i hi
    have hi' : i + 1 ≤ n := Finset.mem_range.mp hi
    have h1 := gapsw62_t2_partialSum_congr_of_le K v π hspan x (F n) hi' (hF n)
    exact gapsw62_t2_partialSum_unique K v π hspan hπ0 x (i + 1) (F (i + 1)) (F n)
      (hF (i + 1)) h1 i (Nat.lt_succ_self i)
  have hsum : ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (F (i + 1) i) * π ^ i
      = ∑ i ∈ Finset.range n, gapsw61_t2_teichmullerSection K v (F n i) * π ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [hagree i hi]
  show x - ∑ i ∈ Finset.range n,
      gapsw61_t2_teichmullerSection K v (F (i + 1) i) * π ^ i ∈
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n
  rw [hsum]
  exact hF n

end FLT.Gapsw62T2PiadicDigitExpansion
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw62T4WittGhostAssembly
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T2PiadicDigitExpansion
open FLT.Gapsw62T3TeichmuellerAdditiveCarry
set_option maxHeartbeats 1600000 in

theorem gapsw62_t4_constantCoeff_one
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    WittVector.constantCoeff (1 : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) = 1 := by
  have _em := Classical.em
  exact map_one
    (WittVector.constantCoeff (p := 3) (R := (𝓞 K) ⧸ v.asIdeal))
end FLT.Gapsw62T4WittGhostAssembly
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw62T4WittGhostAssembly
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T2PiadicDigitExpansion
open FLT.Gapsw62T3TeichmuellerAdditiveCarry

noncomputable def gapsw62_t4_wittGhostLayerFun
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) : v.adicCompletionIntegers K :=
  gapsw61_t2_teichmullerSection K v (WittVector.constantCoeff a)
end FLT.Gapsw62T4WittGhostAssembly
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw62T4WittGhostAssembly
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T2PiadicDigitExpansion
open FLT.Gapsw62T3TeichmuellerAdditiveCarry
set_option maxHeartbeats 1600000 in

theorem gapsw62_t4_wittGhostLayerFun_apply
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) :
    gapsw62_t4_wittGhostLayerFun K v a =
      gapsw61_t2_teichmullerSection K v (WittVector.constantCoeff a) := by
  have _em := Classical.em
  rfl
end FLT.Gapsw62T4WittGhostAssembly
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw62T4WittGhostAssembly
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T2PiadicDigitExpansion
open FLT.Gapsw62T3TeichmuellerAdditiveCarry
set_option maxHeartbeats 1600000 in

theorem gapsw62_t4_wittGhostLayerFun_teichmuller
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) :
    gapsw62_t4_wittGhostLayerFun K v (WittVector.teichmuller 3 x) =
      gapsw61_t2_teichmullerSection K v x := by
  have _em := Classical.em
  rw [gapsw62_t4_wittGhostLayerFun_apply, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero 3 x]
end FLT.Gapsw62T4WittGhostAssembly
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw62T4WittGhostAssembly
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T2PiadicDigitExpansion
open FLT.Gapsw62T3TeichmuellerAdditiveCarry
set_option maxHeartbeats 1600000 in

theorem gapsw62_t4_exists_sub_wittGhostLayerFun_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (b : v.adicCompletionIntegers K) :
    ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      b - gapsw62_t4_wittGhostLayerFun K v a ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  obtain ⟨π, _hirr, hspan, hπ0⟩ := gapsw62_t2_uniformizer_exists K v
  obtain ⟨d, hd⟩ := gapsw62_t2_digitExpansion_exists K v π hspan hπ0 b
  have h1 := hd 1
  rw [Finset.sum_range_one, pow_zero, mul_one, pow_one] at h1
  refine ⟨WittVector.teichmuller 3 (d 0), ?_⟩
  rw [gapsw62_t4_wittGhostLayerFun_teichmuller]
  exact h1
end FLT.Gapsw62T4WittGhostAssembly
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw63T1XjPiSpanningFamily
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T2PiadicDigitExpansion
open FLT.Gapsw62T4WittGhostAssembly
set_option maxHeartbeats 1600000 in

theorem gapsw63_t1_xjPi_digit_step
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (A : Type) [CommRing A] (φ : A →+* v.adicCompletionIntegers K)
    (x : v.adicCompletionIntegers K) (f : ℕ)
    (hgen : ∀ b : v.adicCompletionIntegers K, ∃ c : ℕ → A,
      b - ∑ j ∈ Finset.range f, φ (c j) * x ^ j ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    {N : ℕ} {r : v.adicCompletionIntegers K}
    (hr : r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N) :
    ∃ c : ℕ → A,
      r - ∑ j ∈ Finset.range f, φ (c j) * x ^ j * π ^ N ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (N + 1) := by
  have _em := Classical.em
  rw [gapsw62_t2_maximalIdeal_pow_eq_span K v π hspan N, Ideal.mem_span_singleton] at hr
  obtain ⟨b, hb⟩ := hr
  obtain ⟨c, hc⟩ := hgen b
  refine ⟨c, ?_⟩
  have hsum : ∑ j ∈ Finset.range f, φ (c j) * x ^ j * π ^ N
      = (∑ j ∈ Finset.range f, φ (c j) * x ^ j) * π ^ N := by
    rw [Finset.sum_mul]
  have hkey : r - ∑ j ∈ Finset.range f, φ (c j) * x ^ j * π ^ N
      = π ^ N * (b - ∑ j ∈ Finset.range f, φ (c j) * x ^ j) := by
    rw [hsum, hb]; ring
  rw [hkey, pow_succ]
  exact Ideal.mul_mem_mul
    (Ideal.pow_mem_pow (gapsw62_t2_pi_mem_maximalIdeal K v π hspan) N) hc
end FLT.Gapsw63T1XjPiSpanningFamily
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw63T1XjPiSpanningFamily
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T2PiadicDigitExpansion
open FLT.Gapsw62T4WittGhostAssembly
set_option maxHeartbeats 1600000 in

theorem gapsw63_t1_xjPi_partialSum_exists
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (A : Type) [CommRing A] (φ : A →+* v.adicCompletionIntegers K)
    (x : v.adicCompletionIntegers K) (f : ℕ)
    (hgen : ∀ b : v.adicCompletionIntegers K, ∃ c : ℕ → A,
      b - ∑ j ∈ Finset.range f, φ (c j) * x ^ j ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (b : v.adicCompletionIntegers K) :
    ∀ N : ℕ, ∃ c : ℕ → ℕ → A,
      b - ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range f, φ (c i j) * x ^ j * π ^ i ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
  have _em := Classical.em
  intro N
  induction N with
  | zero =>
    refine ⟨fun _ _ => 0, ?_⟩
    rw [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := gapsw63_t1_xjPi_digit_step K v π hspan A φ x f hgen hc
    refine ⟨Function.update c N d, ?_⟩
    have hsum : ∑ i ∈ Finset.range (N + 1),
          ∑ j ∈ Finset.range f, φ (Function.update c N d i j) * x ^ j * π ^ i
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range f, φ (c i j) * x ^ j * π ^ i)
          + ∑ j ∈ Finset.range f, φ (d j) * x ^ j * π ^ N := by
      rw [Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hi)) d c]
      · rw [Function.update_self N d c]
    rw [hsum, sub_add_eq_sub_sub]
    exact hd
end FLT.Gapsw63T1XjPiSpanningFamily
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw65T6HgenHresResidualAtoms
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw64T2SpanningFamilyWeld
set_option maxHeartbeats 1600000 in

theorem gapsw65_t6_hgen_of_residue
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (x : v.adicCompletionIntegers K)
    (hres : ∀ b : v.adicCompletionIntegers K,
      ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
          (v.adicCompletionIntegers K) a ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    ∀ b : v.adicCompletionIntegers K,
      ∃ c : ℕ → WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - ∑ j ∈ Finset.range 1,
            algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
              (v.adicCompletionIntegers K) (c j) * x ^ j ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  intro b
  obtain ⟨a, ha⟩ := hres b
  refine ⟨fun _ => a, ?_⟩
  rw [Finset.sum_range_one, pow_zero, mul_one]
  exact ha
end FLT.Gapsw65T6HgenHresResidualAtoms
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw65T6HgenHresResidualAtoms
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw64T2SpanningFamilyWeld
set_option maxHeartbeats 1600000 in

theorem gapsw65_t6_hres_of_layerFun_agreement
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (hagree : ∀ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
          (v.adicCompletionIntegers K) a
        - gapsw62_t4_wittGhostLayerFun K v a ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    ∀ b : v.adicCompletionIntegers K,
      ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
          (v.adicCompletionIntegers K) a ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  intro b
  obtain ⟨a, ha⟩ := gapsw62_t4_exists_sub_wittGhostLayerFun_mem K v b
  refine ⟨a, ?_⟩
  have hmem := sub_mem ha (hagree a)
  rwa [sub_sub_sub_cancel_right] at hmem
end FLT.Gapsw65T6HgenHresResidualAtoms
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section

namespace FLT
namespace Gapsw67T3WittDigitCongruenceEngine

p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw58T5WittASideEngineAtoms
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw62T4WittGhostAssembly

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_three_mem_maximalIdeal
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    (3 : v.adicCompletionIntegers K) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  haveI hch : CharP ((𝓞 K) ⧸ v.asIdeal) 3 :=
    gapsw58_t5_residue_charP_three K v h1
  have h3k : (3 : (𝓞 K) ⧸ v.asIdeal) = 0 := by
    have h := CharP.cast_eq_zero ((𝓞 K) ⧸ v.asIdeal) 3
    rwa [Nat.cast_ofNat] at h
  have hres : IsLocalRing.residue (v.adicCompletionIntegers K)
      (3 : v.adicCompletionIntegers K) = 0 := by
    rw [map_ofNat (IsLocalRing.residue (v.adicCompletionIntegers K)) 3,
      ← map_ofNat (ResidueFieldEquivCompletionResidueField K v) 3, h3k,
      _root_.map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hres

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_pow_three_sub_mem_succ
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h3 : (3 : v.adicCompletionIntegers K) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    {a b : v.adicCompletionIntegers K} {m : ℕ} (hm : 1 ≤ m)
    (h : a - b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m) :
    a ^ 3 - b ^ 3 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (m + 1) := by
  have _em := Classical.em
  have hkey : a ^ 3 - b ^ 3 = (a - b) ^ 3 + a * b * (3 * (a - b)) := by ring
  rw [hkey]
  refine Ideal.add_mem _ ?_ ?_
  · have hcube : (a - b) ^ 3 ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m) ^ 3 :=
      Ideal.pow_mem_pow h 3
    rw [← pow_mul] at hcube
    exact Ideal.pow_le_pow_right (by omega) hcube
  · have hmul : 3 * (a - b) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) *
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m :=
      Ideal.mul_mem_mul h3 h
    rw [← pow_succ'] at hmul
    exact Ideal.mul_mem_left _ _ hmul

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_pow_pow_three_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h3 : (3 : v.adicCompletionIntegers K) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    {a b : v.adicCompletionIntegers K}
    (h : a - b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (n : ℕ) :
    a ^ 3 ^ n - b ^ 3 ^ n ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) := by
  have _em := Classical.em
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ 3 n, pow_mul a (3 ^ n) 3, pow_mul b (3 ^ n) 3]
    exact gapsw67_t3_pow_three_sub_mem_succ K v h3 (Nat.le_add_left 1 n) ih

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_residue_expChar_three
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    ExpChar ((𝓞 K) ⧸ v.asIdeal) 3 := by
  have _em := Classical.em
  haveI hch : CharP ((𝓞 K) ⧸ v.asIdeal) 3 :=
    gapsw58_t5_residue_charP_three K v h1
  exact ExpChar.prime Nat.prime_three

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_residue_perfectRing_three
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    PerfectRing ((𝓞 K) ⧸ v.asIdeal) 3 := by
  have _em := Classical.em
  obtain ⟨hch, hp⟩ := gapsw58_t5_residue_perfectRing_three K v h1
  exact hp

noncomputable def gapsw67_t3_wittDigit
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (i : ℕ) : (𝓞 K) ⧸ v.asIdeal :=
  (@frobeniusEquiv ((𝓞 K) ⧸ v.asIdeal) 3 _
    (gapsw67_t3_residue_expChar_three K v h1)
    (gapsw67_t3_residue_perfectRing_three K v h1)).symm^[i] (a.coeff i)

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_wittDigit_zero_index
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) :
    gapsw67_t3_wittDigit K v h1 a 0 = WittVector.constantCoeff a := by
  have _em := Classical.em
  simp only [gapsw67_t3_wittDigit, Function.iterate_zero_apply,
    WittVector.constantCoeff_apply]

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_wittDigit_one_zero
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    gapsw67_t3_wittDigit K v h1 1 0 = 1 := by
  have _em := Classical.em
  rw [gapsw67_t3_wittDigit_zero_index K v h1 1]
  exact gapsw62_t4_constantCoeff_one K v

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_wittDigit_one_pos
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (i : ℕ) (hi : 0 < i) :
    gapsw67_t3_wittDigit K v h1 1 i = 0 := by
  have _em := Classical.em
  simp only [gapsw67_t3_wittDigit]
  rw [WittVector.one_coeff_eq_of_pos 3 ((𝓞 K) ⧸ v.asIdeal) i hi]
  exact Function.iterate_fixed
    (_root_.map_zero (@frobeniusEquiv ((𝓞 K) ⧸ v.asIdeal) 3 _
      (gapsw67_t3_residue_expChar_three K v h1)
      (gapsw67_t3_residue_perfectRing_three K v h1)).symm) i

noncomputable def gapsw67_t3_teichmullerPartialSum
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ) :
    v.adicCompletionIntegers K :=
  ∑ i ∈ Finset.range N,
    gapsw61_t2_teichmullerSection K v (gapsw67_t3_wittDigit K v h1 a i) * 3 ^ i

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_teichmullerPartialSum_apply
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ) :
    gapsw67_t3_teichmullerPartialSum K v h1 a N =
      ∑ i ∈ Finset.range N,
        gapsw61_t2_teichmullerSection K v (gapsw67_t3_wittDigit K v h1 a i)
          * 3 ^ i := by
  have _em := Classical.em
  rfl

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_teichmullerPartialSum_succ
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ) :
    gapsw67_t3_teichmullerPartialSum K v h1 a (N + 1) =
      gapsw67_t3_teichmullerPartialSum K v h1 a N +
        gapsw61_t2_teichmullerSection K v (gapsw67_t3_wittDigit K v h1 a N)
          * 3 ^ N := by
  have _em := Classical.em
  simp only [gapsw67_t3_teichmullerPartialSum]
  exact Finset.sum_range_succ _ N

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_teichmullerPartialSum_one
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (N : ℕ) (hN : 0 < N) :
    gapsw67_t3_teichmullerPartialSum K v h1 1 N = 1 := by
  have _em := Classical.em
  simp only [gapsw67_t3_teichmullerPartialSum]
  rw [Finset.sum_eq_single 0]
  · rw [gapsw67_t3_wittDigit_one_zero K v h1,
      gapsw61_t2_teichmullerSection_one K v, pow_zero, mul_one]
  · intro b _ hb
    rw [gapsw67_t3_wittDigit_one_pos K v h1 b (Nat.pos_of_ne_zero hb),
      gapsw61_t2_teichmullerSection_zero K v, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr hN) h0

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_teichmullerPartialSum_one_eq_layerFun
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) :
    gapsw67_t3_teichmullerPartialSum K v h1 a 1 =
      gapsw62_t4_wittGhostLayerFun K v a := by
  have _em := Classical.em
  simp only [gapsw67_t3_teichmullerPartialSum]
  rw [Finset.sum_range_one, gapsw67_t3_wittDigit_zero_index K v h1 a,
    pow_zero, mul_one, gapsw62_t4_wittGhostLayerFun_apply K v a]

set_option maxHeartbeats 1600000 in

theorem gapsw67_t3_teichmullerPartialSum_succ_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ) :
    gapsw67_t3_teichmullerPartialSum K v h1 a (N + 1) -
      gapsw67_t3_teichmullerPartialSum K v h1 a N ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
  have _em := Classical.em
  rw [gapsw67_t3_teichmullerPartialSum_succ K v h1 a N, add_sub_cancel_left]
  exact Ideal.mul_mem_left _ _
    (Ideal.pow_mem_pow (gapsw67_t3_three_mem_maximalIdeal K v h1) N)

end FLT.Gapsw67T3WittDigitCongruenceEngine
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section

namespace FLT
namespace Gapsw67T4EisensteinCoeffWittBodyWeld

p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw54T2KrasnerGlobalGeneratorTransport
open FLT.Gapsw62T2PiadicDigitExpansion
open FLT.Gapsw63T1XjPiSpanningFamily
open FLT.Gapsw63T4ModuleFiniteCarrier
open FLT.Gapsw64T2SpanningFamilyWeld
open FLT.Gapsw65T6HgenHresResidualAtoms
open FLT.Gapsw66T3EisensteinCoeffFactorisationSupply

set_option maxHeartbeats 3200000 in

theorem gapsw67_t4_xjPi_blockRemainder_of_unitFactorisation
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (A : Type) [CommRing A] (φ : A →+* v.adicCompletionIntegers K)
    (x : v.adicCompletionIntegers K) (f : ℕ)
    (hgen : ∀ b : v.adicCompletionIntegers K, ∃ c : ℕ → A,
      b - ∑ j ∈ Finset.range f, φ (c j) * x ^ j ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (e : ℕ)
    (a : A) (u0 : (↥(v.adicCompletionIntegers K))ˣ)
    (hu0 : φ a = (u0 : v.adicCompletionIntegers K) * π ^ e)
    (b : v.adicCompletionIntegers K) (N : ℕ) :
    ∃ (c : ℕ → ℕ → A) (b' : v.adicCompletionIntegers K),
      b - ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f, φ (c i j) * x ^ j * π ^ i
        = φ a ^ N * b' := by
  have _em := Classical.em
  induction N with
  | zero =>
    refine ⟨fun _ _ => 0, b, ?_⟩
    simp
  | succ N ih =>
    obtain ⟨c, b', hc⟩ := ih
    obtain ⟨d, hd⟩ := gapsw63_t1_xjPi_partialSum_exists K v π hspan A φ x f
      hgen b' e
    rw [gapsw62_t2_maximalIdeal_pow_eq_span K v π hspan e,
      Ideal.mem_span_singleton] at hd
    obtain ⟨r, hr⟩ := hd
    refine ⟨fun i j => c i j + a ^ N * d i j,
      ((u0⁻¹ : (↥(v.adicCompletionIntegers K))ˣ) : v.adicCompletionIntegers K)
        * r, ?_⟩
    show b - ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
        φ (c i j + a ^ N * d i j) * x ^ j * π ^ i
      = φ a ^ (N + 1) *
        (((u0⁻¹ : (↥(v.adicCompletionIntegers K))ˣ) : v.adicCompletionIntegers K)
          * r)
    have hπe : π ^ e
        = ((u0⁻¹ : (↥(v.adicCompletionIntegers K))ˣ) : v.adicCompletionIntegers K)
          * φ a := by
      rw [hu0, ← mul_assoc, Units.inv_mul, one_mul]
    have hsum : ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
          φ (c i j + a ^ N * d i j) * x ^ j * π ^ i
        = (∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
            φ (c i j) * x ^ j * π ^ i)
          + φ a ^ N * ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
              φ (d i j) * x ^ j * π ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_add, map_mul, map_pow]
      ring
    calc b - ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
          φ (c i j + a ^ N * d i j) * x ^ j * π ^ i
        = (b - ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
            φ (c i j) * x ^ j * π ^ i)
          - φ a ^ N * ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
              φ (d i j) * x ^ j * π ^ i := by
          rw [hsum]; ring
      _ = φ a ^ N * (b' - ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
              φ (d i j) * x ^ j * π ^ i) := by
          rw [hc]; ring
      _ = φ a ^ N * (π ^ e * r) := by rw [hr]
      _ = φ a ^ (N + 1) *
            (((u0⁻¹ : (↥(v.adicCompletionIntegers K))ˣ) : v.adicCompletionIntegers K)
              * r) := by
          rw [hπe, pow_succ]; ring

set_option maxHeartbeats 3200000 in

theorem gapsw67_t4_xjPi_spanningFamily_of_unitFactorisation
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hspan : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (A : Type) [CommRing A] (φ : A →+* v.adicCompletionIntegers K)
    (x : v.adicCompletionIntegers K) (f : ℕ)
    (hgen : ∀ b : v.adicCompletionIntegers K, ∃ c : ℕ → A,
      b - ∑ j ∈ Finset.range f, φ (c j) * x ^ j ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (e : ℕ) (he : 0 < e)
    (a : A) (u0 : (↥(v.adicCompletionIntegers K))ˣ)
    (hu0 : φ a = (u0 : v.adicCompletionIntegers K) * π ^ e)
    (b : v.adicCompletionIntegers K) (N : ℕ) :
    ∃ c : ℕ → ℕ → A,
      b - ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f, φ (c i j) * x ^ j * π ^ i ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
  have _em := Classical.em
  obtain ⟨c, b', hc⟩ := gapsw67_t4_xjPi_blockRemainder_of_unitFactorisation
    K v π hspan A φ x f hgen e a u0 hu0 b N
  refine ⟨c, ?_⟩
  rw [hc]
  have hπm : π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    gapsw62_t2_pi_mem_maximalIdeal K v π hspan
  have hφa : φ a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [hu0]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) hπm e he)
  exact Ideal.mul_mem_right b' _ (Ideal.pow_mem_pow hφa N)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw67_t4_xjPi_hspan_discharge_of_unitFactorisation
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (π : v.adicCompletionIntegers K)
    (hπ : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (x : v.adicCompletionIntegers K) (f : ℕ)
    (hgen : ∀ b : v.adicCompletionIntegers K,
      ∃ c : ℕ → WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - ∑ j ∈ Finset.range f,
            algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
              (v.adicCompletionIntegers K) (c j) * x ^ j ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (e : ℕ) (he : 0 < e)
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
    (u0 : (↥(v.adicCompletionIntegers K))ˣ)
    (hu0 : algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
        (v.adicCompletionIntegers K) a
      = (u0 : v.adicCompletionIntegers K) * π ^ e)
    (b : v.adicCompletionIntegers K) (N : ℕ) :
    ∃ cf : Fin e × Fin f → WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      b - ∑ q, cf q • (x ^ (q.2 : ℕ) * π ^ (q.1 : ℕ)) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
  have _em := Classical.em
  obtain ⟨c, hc⟩ := gapsw67_t4_xjPi_spanningFamily_of_unitFactorisation K v π hπ
    (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
    (algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (v.adicCompletionIntegers K))
    x f hgen e he a u0 hu0 b N
  refine ⟨fun q => c (q.1 : ℕ) (q.2 : ℕ), ?_⟩
  show b - ∑ q : Fin e × Fin f,
      c (q.1 : ℕ) (q.2 : ℕ) • (x ^ (q.2 : ℕ) * π ^ (q.1 : ℕ)) ∈
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N
  have hsum : ∑ q : Fin e × Fin f,
        c (q.1 : ℕ) (q.2 : ℕ) • (x ^ (q.2 : ℕ) * π ^ (q.1 : ℕ))
      = ∑ i ∈ Finset.range e, ∑ j ∈ Finset.range f,
          algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
            (v.adicCompletionIntegers K) (c i j) * x ^ j * π ^ i := by
    rw [gapsw64_t2_finProd_sum_eq_range_sum
      (fun i j => c i j • (x ^ j * π ^ i)) e f]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_assoc]
  rw [hsum]
  exact hc

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw67_t4_moduleFinite_carrier_of_unitFactorisation
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (π : v.adicCompletionIntegers K)
    (hπ : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (x : v.adicCompletionIntegers K) (f : ℕ)
    (hgen : ∀ b : v.adicCompletionIntegers K,
      ∃ c : ℕ → WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - ∑ j ∈ Finset.range f,
            algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
              (v.adicCompletionIntegers K) (c j) * x ^ j ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
    (u0 : (↥(v.adicCompletionIntegers K))ˣ)
    (hu0 : algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
        (v.adicCompletionIntegers K) a
      = (u0 : v.adicCompletionIntegers K)
        * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)) :
    Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  have he : 0 < (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal :=
    Nat.pos_of_ne_zero (gapsw54_t2_ramificationIdx_ne_zero K v h1)
  refine gapsw63_t4_moduleFinite_carrier_of_ramification K v h1
    (Fin ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) × Fin f)
    (fun q => x ^ (q.2 : ℕ) * π ^ (q.1 : ℕ)) ?_
  intro b
  obtain ⟨cf, hcf⟩ := gapsw67_t4_xjPi_hspan_discharge_of_unitFactorisation
    K v π hπ x f hgen ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal) he
    a u0 hu0 b ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)
  exact ⟨cf, hcf⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw67_t4_wittLift_body_of_residue_and_eisensteinCoeff
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (_hwild : 3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (π : v.adicCompletionIntegers K)
    (hπ : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (hres : ∀ b : v.adicCompletionIntegers K,
      ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
          (v.adicCompletionIntegers K) a ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
    (u0 : (↥(v.adicCompletionIntegers K))ˣ)
    (hu0 : algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
        (v.adicCompletionIntegers K) a
      = (u0 : v.adicCompletionIntegers K)
        * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)) :
    ∃ (_ : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
        (v.adicCompletionIntegers K))
      (_ : Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
        (v.adicCompletionIntegers K)),
      ∀ b : v.adicCompletionIntegers K,
        ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
          b - algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
            (v.adicCompletionIntegers K) a ∈
            IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  have hfin : Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K) :=
    gapsw67_t4_moduleFinite_carrier_of_unitFactorisation K v h1 π hπ π 1
      (gapsw65_t6_hgen_of_residue K v π hres) a u0 hu0
  exact ⟨iAlg, hfin, hres⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw67_t4_wittLift_body_of_residue_and_h3fac
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (_hwild : 3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)
    [iAlg : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
      (v.adicCompletionIntegers K)]
    (π : v.adicCompletionIntegers K)
    (hπ : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (hres : ∀ b : v.adicCompletionIntegers K,
      ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
        b - algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
          (v.adicCompletionIntegers K) a ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (u0 : (↥(v.adicCompletionIntegers K))ˣ)
    (hu0 : algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
        (v.adicCompletionIntegers K) 3
      = (u0 : v.adicCompletionIntegers K)
        * π ^ ((Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal)) :
    ∃ (_ : Algebra (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
        (v.adicCompletionIntegers K))
      (_ : Module.Finite (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
        (v.adicCompletionIntegers K)),
      ∀ b : v.adicCompletionIntegers K,
        ∃ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
          b - algebraMap (WittVector 3 ((𝓞 K) ⧸ v.asIdeal))
            (v.adicCompletionIntegers K) a ∈
            IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  exact gapsw67_t4_wittLift_body_of_residue_and_eisensteinCoeff K v h1 _hwild
    π hπ hres 3 u0 hu0

end FLT.Gapsw67T4EisensteinCoeffWittBodyWeld
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw68T2WittEnginePackBuilder
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw67T3WittDigitCongruenceEngine
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw68_t2_fone_of_partialSum_limit
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (f : WittVector 3 ((𝓞 K) ⧸ v.asIdeal) → v.adicCompletionIntegers K)
    (hlim : ∀ (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ),
      f a - gapsw67_t3_teichmullerPartialSum K v h1 a N ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N) :
    f 1 = 1 := by
  have _em := Classical.em
  have hmem : ∀ N : ℕ, f 1 - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · have h := hlim 1 N
      rwa [gapsw67_t3_teichmullerPartialSum_one K v h1 N hN] at h
  have hbot : f 1 - 1 ∈ (⊥ : Ideal (v.adicCompletionIntegers K)) := by
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
    exact (Submodule.mem_iInf _).mpr hmem
  rw [Ideal.mem_bot] at hbot
  exact sub_eq_zero.mp hbot
end FLT.Gapsw68T2WittEnginePackBuilder
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw68T2WittEnginePackBuilder
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw67T3WittDigitCongruenceEngine
set_option maxHeartbeats 1600000 in

theorem gapsw68_t2_hfagree_of_partialSum_limit
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (f : WittVector 3 ((𝓞 K) ⧸ v.asIdeal) → v.adicCompletionIntegers K)
    (hlim : ∀ (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ),
      f a - gapsw67_t3_teichmullerPartialSum K v h1 a N ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N) :
    ∀ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f a - gapsw62_t4_wittGhostLayerFun K v a ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  intro a
  have h := hlim a 1
  rwa [gapsw67_t3_teichmullerPartialSum_one_eq_layerFun K v h1 a,
    pow_one] at h
end FLT.Gapsw68T2WittEnginePackBuilder
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw68T4Rd67ConsumptionGate
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw67T3WittDigitCongruenceEngine
set_option maxHeartbeats 1600000 in

theorem gapsw68_t4_teichmullerPartialSum_sub_mem_of_le
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) {N M : ℕ} (hNM : N ≤ M) :
    gapsw67_t3_teichmullerPartialSum K v h1 a M -
      gapsw67_t3_teichmullerPartialSum K v h1 a N ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
  have _em := Classical.em
  induction M, hNM using Nat.le_induction with
  | base =>
    rw [sub_self]
    exact Ideal.zero_mem _
  | succ M hNM ih =>
    have hsplit : gapsw67_t3_teichmullerPartialSum K v h1 a (M + 1) -
        gapsw67_t3_teichmullerPartialSum K v h1 a N =
        (gapsw67_t3_teichmullerPartialSum K v h1 a (M + 1) -
          gapsw67_t3_teichmullerPartialSum K v h1 a M) +
        (gapsw67_t3_teichmullerPartialSum K v h1 a M -
          gapsw67_t3_teichmullerPartialSum K v h1 a N) := by ring
    rw [hsplit]
    exact Ideal.add_mem _
      (Ideal.pow_le_pow_right hNM
        (gapsw67_t3_teichmullerPartialSum_succ_sub_mem K v h1 a M))
      ih
end FLT.Gapsw68T4Rd67ConsumptionGate
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section

namespace FLT
namespace Gapsw69T2WittApproxRingLaws

p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw61T2TeichmuellerSectionFunction
open FLT.Gapsw67T3WittDigitCongruenceEngine

noncomputable def gapsw69_t2_twistedDigit
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (n i : ℕ) : (𝓞 K) ⧸ v.asIdeal :=
  (@frobeniusEquiv ((𝓞 K) ⧸ v.asIdeal) 3 _
    (gapsw67_t3_residue_expChar_three K v h1)
    (gapsw67_t3_residue_perfectRing_three K v h1)).symm^[n] (a.coeff i)

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_twistedDigit_pow
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) {n i : ℕ} (hin : i ≤ n) :
    gapsw69_t2_twistedDigit K v h1 a n i ^ 3 ^ (n - i) =
      gapsw67_t3_wittDigit K v h1 a i := by
  have _em := Classical.em
  haveI hexp : ExpChar ((𝓞 K) ⧸ v.asIdeal) 3 :=
    gapsw67_t3_residue_expChar_three K v h1
  haveI hperf : PerfectRing ((𝓞 K) ⧸ v.asIdeal) 3 :=
    gapsw67_t3_residue_perfectRing_three K v h1
  simp only [gapsw69_t2_twistedDigit, gapsw67_t3_wittDigit]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + i := ⟨n - i, (Nat.sub_add_cancel hin).symm⟩
  rw [Nat.add_sub_cancel, Function.iterate_add_apply]
  exact iterate_frobeniusEquiv_symm_pow_p_pow ((𝓞 K) ⧸ v.asIdeal) 3 _ j

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_teichmullerSection_pow_nat
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (𝓞 K) ⧸ v.asIdeal) (M : ℕ) :
    gapsw61_t2_teichmullerSection K v (x ^ M) =
      gapsw61_t2_teichmullerSection K v x ^ M := by
  have _em := Classical.em
  induction M with
  | zero =>
    rw [pow_zero, pow_zero]
    exact gapsw61_t2_teichmullerSection_one K v
  | succ M ih =>
    rw [pow_succ, pow_succ, gapsw61_t2_teichmullerSection_mul K v, ih]

noncomputable def gapsw69_t2_ghostLiftVector
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (n : ℕ) :
    WittVector 3 (v.adicCompletionIntegers K) :=
  WittVector.mk 3 (fun i => gapsw61_t2_teichmullerSection K v
    (gapsw69_t2_twistedDigit K v h1 a n i))

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_ghostLiftVector_coeff
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (n i : ℕ) :
    (gapsw69_t2_ghostLiftVector K v h1 a n).coeff i =
      gapsw61_t2_teichmullerSection K v
        (gapsw69_t2_twistedDigit K v h1 a n i) := by
  have _em := Classical.em
  rfl

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_partialSum_eq_ghostComponent
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (n : ℕ) :
    gapsw67_t3_teichmullerPartialSum K v h1 a (n + 1) =
      WittVector.ghostComponent n (gapsw69_t2_ghostLiftVector K v h1 a n) := by
  have _em := Classical.em
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial,
    gapsw67_t3_teichmullerPartialSum_apply]
  simp only [Nat.cast_ofNat]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [gapsw69_t2_ghostLiftVector_coeff K v h1 a n i,
    ← gapsw69_t2_teichmullerSection_pow_nat K v _ (3 ^ (n - i)),
    gapsw69_t2_twistedDigit_pow K v h1 a hin, mul_comm]

noncomputable def gapsw69_t2_twistResidueHom
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (n : ℕ) :
    ((𝓞 K) ⧸ v.asIdeal) →+*
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) where
  toFun x := ResidueFieldEquivCompletionResidueField K v
    ((@frobeniusEquiv ((𝓞 K) ⧸ v.asIdeal) 3 _
      (gapsw67_t3_residue_expChar_three K v h1)
      (gapsw67_t3_residue_perfectRing_three K v h1)).symm^[n] x)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_twistResidueHom_apply
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (n : ℕ) (x : (𝓞 K) ⧸ v.asIdeal) :
    gapsw69_t2_twistResidueHom K v h1 n x =
      ResidueFieldEquivCompletionResidueField K v
        ((@frobeniusEquiv ((𝓞 K) ⧸ v.asIdeal) 3 _
          (gapsw67_t3_residue_expChar_three K v h1)
          (gapsw67_t3_residue_perfectRing_three K v h1)).symm^[n] x) := by
  have _em := Classical.em
  rfl

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_residue_ghostLiftVector_coeff
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (n i : ℕ) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
      ((gapsw69_t2_ghostLiftVector K v h1 a n).coeff i) =
      gapsw69_t2_twistResidueHom K v h1 n (a.coeff i) := by
  have _em := Classical.em
  rw [gapsw69_t2_ghostLiftVector_coeff K v h1 a n i,
    gapsw69_t2_twistResidueHom_apply K v h1 n (a.coeff i)]
  have h := gapsw61_t2_teichmullerSection_residue K v
    (gapsw69_t2_twistedDigit K v h1 a n i)
  simpa only [gapsw69_t2_twistedDigit] using h

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_map_residue_ghostLiftVector
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (n : ℕ) :
    WittVector.map (IsLocalRing.residue (v.adicCompletionIntegers K))
      (gapsw69_t2_ghostLiftVector K v h1 a n) =
      WittVector.map (gapsw69_t2_twistResidueHom K v h1 n) a := by
  have _em := Classical.em
  apply WittVector.ext
  intro i
  rw [WittVector.map_coeff, WittVector.map_coeff]
  exact gapsw69_t2_residue_ghostLiftVector_coeff K v h1 a n i

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_ghostLiftVector_mul_coeff_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (n : ℕ) :
    ∀ i : ℕ,
      (gapsw69_t2_ghostLiftVector K v h1 (a * b) n).coeff i -
        (gapsw69_t2_ghostLiftVector K v h1 a n *
          gapsw69_t2_ghostLiftVector K v h1 b n).coeff i ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  intro i
  apply gapsw61_t2_sub_mem_of_residue_eq K v
  rw [gapsw69_t2_residue_ghostLiftVector_coeff K v h1 (a * b) n i,
    ← WittVector.map_coeff (IsLocalRing.residue (v.adicCompletionIntegers K))
      (gapsw69_t2_ghostLiftVector K v h1 a n *
        gapsw69_t2_ghostLiftVector K v h1 b n) i,
    map_mul (WittVector.map (IsLocalRing.residue (v.adicCompletionIntegers K)))
      (gapsw69_t2_ghostLiftVector K v h1 a n)
      (gapsw69_t2_ghostLiftVector K v h1 b n),
    gapsw69_t2_map_residue_ghostLiftVector K v h1 a n,
    gapsw69_t2_map_residue_ghostLiftVector K v h1 b n,
    ← map_mul (WittVector.map (gapsw69_t2_twistResidueHom K v h1 n)) a b,
    WittVector.map_coeff (gapsw69_t2_twistResidueHom K v h1 n) (a * b) i]

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_ghostLiftVector_add_coeff_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (n : ℕ) :
    ∀ i : ℕ,
      (gapsw69_t2_ghostLiftVector K v h1 (a + b) n).coeff i -
        (gapsw69_t2_ghostLiftVector K v h1 a n +
          gapsw69_t2_ghostLiftVector K v h1 b n).coeff i ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have _em := Classical.em
  intro i
  apply gapsw61_t2_sub_mem_of_residue_eq K v
  rw [gapsw69_t2_residue_ghostLiftVector_coeff K v h1 (a + b) n i,
    ← WittVector.map_coeff (IsLocalRing.residue (v.adicCompletionIntegers K))
      (gapsw69_t2_ghostLiftVector K v h1 a n +
        gapsw69_t2_ghostLiftVector K v h1 b n) i,
    map_add (WittVector.map (IsLocalRing.residue (v.adicCompletionIntegers K)))
      (gapsw69_t2_ghostLiftVector K v h1 a n)
      (gapsw69_t2_ghostLiftVector K v h1 b n),
    gapsw69_t2_map_residue_ghostLiftVector K v h1 a n,
    gapsw69_t2_map_residue_ghostLiftVector K v h1 b n,
    ← map_add (WittVector.map (gapsw69_t2_twistResidueHom K v h1 n)) a b,
    WittVector.map_coeff (gapsw69_t2_twistResidueHom K v h1 n) (a + b) i]

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_ghostComponent_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    {X Y : WittVector 3 (v.adicCompletionIntegers K)} (n : ℕ)
    (h : ∀ i : ℕ, X.coeff i - Y.coeff i ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    WittVector.ghostComponent n X - WittVector.ghostComponent n Y ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) := by
  have _em := Classical.em
  have h3 := gapsw67_t3_three_mem_maximalIdeal K v h1
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply,
    aeval_wittPolynomial, aeval_wittPolynomial]
  simp only [Nat.cast_ofNat]
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← mul_sub]
  have hpow : (3 : v.adicCompletionIntegers K) ^ i ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ i :=
    Ideal.pow_mem_pow h3 i
  have hdiff : X.coeff i ^ 3 ^ (n - i) - Y.coeff i ^ 3 ^ (n - i) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ ((n - i) + 1) :=
    gapsw67_t3_pow_pow_three_sub_mem K v h3 (h i) (n - i)
  have hmem := Ideal.mul_mem_mul hpow hdiff
  rw [← pow_add] at hmem
  have harith : i + ((n - i) + 1) = n + 1 := by omega
  rwa [harith] at hmem

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_teichmullerPartialSum_mul_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ) :
    gapsw67_t3_teichmullerPartialSum K v h1 (a * b) N -
      gapsw67_t3_teichmullerPartialSum K v h1 a N *
        gapsw67_t3_teichmullerPartialSum K v h1 b N ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
  have _em := Classical.em
  cases N with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n =>
    rw [gapsw69_t2_partialSum_eq_ghostComponent K v h1 (a * b) n,
      gapsw69_t2_partialSum_eq_ghostComponent K v h1 a n,
      gapsw69_t2_partialSum_eq_ghostComponent K v h1 b n,
      ← map_mul (WittVector.ghostComponent n)
        (gapsw69_t2_ghostLiftVector K v h1 a n)
        (gapsw69_t2_ghostLiftVector K v h1 b n)]
    exact gapsw69_t2_ghostComponent_sub_mem K v h1 n
      (gapsw69_t2_ghostLiftVector_mul_coeff_sub_mem K v h1 a b n)

set_option maxHeartbeats 1600000 in

theorem gapsw69_t2_teichmullerPartialSum_add_sub_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ) :
    gapsw67_t3_teichmullerPartialSum K v h1 (a + b) N -
      gapsw67_t3_teichmullerPartialSum K v h1 a N -
        gapsw67_t3_teichmullerPartialSum K v h1 b N ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
  have _em := Classical.em
  cases N with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n =>
    rw [gapsw69_t2_partialSum_eq_ghostComponent K v h1 (a + b) n,
      gapsw69_t2_partialSum_eq_ghostComponent K v h1 a n,
      gapsw69_t2_partialSum_eq_ghostComponent K v h1 b n, sub_sub,
      ← map_add (WittVector.ghostComponent n)
        (gapsw69_t2_ghostLiftVector K v h1 a n)
        (gapsw69_t2_ghostLiftVector K v h1 b n)]
    exact gapsw69_t2_ghostComponent_sub_mem K v h1 n
      (gapsw69_t2_ghostLiftVector_add_coeff_sub_mem K v h1 a b n)

end FLT.Gapsw69T2WittApproxRingLaws
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw68T3WittCohenLiftAsserter
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw59T2WittCohenLiftReduction
open FLT.Gapsw62T4WittGhostAssembly
open FLT.Gapsw63T4bWittGhostRingHomUpgrade
open FLT.Gapsw65T6HgenHresResidualAtoms
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw67T4EisensteinCoeffWittBodyWeld
open FLT.Gapsw67T5UniformizerEisensteinSupply
open FLT.Gapsw67T6WittLiftAsserterSpine
open FLT.Gapsw68T2WittEnginePackBuilder
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw68_t3_wittCohenLiftSupply_of_limit_ringLaws
    (hsupply : ∀ (K : Type) [Field K] [NumberField K]
      (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
        (Ideal.span {(3 : ℤ)}) (𝓞 K)),
      3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' v.asIdeal →
      ∃ f : WittVector 3 ((𝓞 K) ⧸ v.asIdeal) → v.adicCompletionIntegers K,
        (∀ (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ),
          f a - gapsw67_t3_teichmullerPartialSum K v h1 a N ∈
            IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N) ∧
        (∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
          f (a * b) = f a * f b) ∧
        (∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
          f (a + b) = f a + f b)) :
    Gapsw59T2WittCohenLiftSupply := by
  have _em := Classical.em
  rw [gapsw59_t2_wittLift_pin]
  intro K _ _ v h1 hwild
  obtain ⟨f, hlim, hmul, hadd⟩ := hsupply K v h1 hwild
  have hone : f 1 = 1 :=
    gapsw68_t2_fone_of_partialSum_limit K v h1 f hlim
  have hfagree : ∀ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f a - gapsw62_t4_wittGhostLayerFun K v a ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    gapsw68_t2_hfagree_of_partialSum_limit K v h1 f hlim
  have hagree : ∀ a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      @algebraMap _ _ _ _ (gapsw63_t4b_algebraOfPack K v f hone hmul hadd) a
        - gapsw62_t4_wittGhostLayerFun K v a ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    intro a
    rw [gapsw63_t4b_algebraOfPack_algebraMap K v f hone hmul hadd a]
    exact hfagree a
  have hres := @gapsw65_t6_hres_of_layerFun_agreement K _ _ v
    (gapsw63_t4b_algebraOfPack K v f hone hmul hadd) hagree
  obtain ⟨π, hπ, _hπne⟩ := gapsw67_t5_uniformizer_exists K v h1 hwild
  obtain ⟨u0, hu0⟩ := @gapsw67_t5_eisenstein_unit_exists_algebraMap K _ _ v
    (WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) _
    (gapsw63_t4b_algebraOfPack K v f hone hmul hadd) π hπ
  exact @gapsw67_t4_wittLift_body_of_residue_and_h3fac K _ _ v h1 hwild
    (gapsw63_t4b_algebraOfPack K v f hone hmul hadd) π hπ hres u0 hu0
end FLT.Gapsw68T3WittCohenLiftAsserter
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw69T1WittCohenLimitExistence
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw68T4Rd67ConsumptionGate
set_option maxHeartbeats 1600000 in

theorem gapsw69_t1_partialSum_smodEq_of_le
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) {N M : ℕ} (hNM : N ≤ M) :
    gapsw67_t3_teichmullerPartialSum K v h1 a N ≡
      gapsw67_t3_teichmullerPartialSum K v h1 a M
      [SMOD (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N • ⊤ :
        Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K))] := by
  have _em := Classical.em
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
  have h := gapsw68_t4_teichmullerPartialSum_sub_mem_of_le K v h1 a hNM
  have hneg : gapsw67_t3_teichmullerPartialSum K v h1 a N -
      gapsw67_t3_teichmullerPartialSum K v h1 a M =
      -(gapsw67_t3_teichmullerPartialSum K v h1 a M -
        gapsw67_t3_teichmullerPartialSum K v h1 a N) := by ring
  rw [hneg]
  exact neg_mem h
end FLT.Gapsw69T1WittCohenLimitExistence
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw69T1WittCohenLimitExistence
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw68T4Rd67ConsumptionGate
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw69_t1_partialSum_limit_exists
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) :
    ∃ L : v.adicCompletionIntegers K, ∀ N : ℕ,
      gapsw67_t3_teichmullerPartialSum K v h1 a N ≡ L
        [SMOD (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N • ⊤ :
          Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K))] := by
  have _em := Classical.em
  have hpre : IsPrecomplete
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
    (NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers
      K v).toIsPrecomplete
  have hcau : ∀ {m n : ℕ}, m ≤ n →
      gapsw67_t3_teichmullerPartialSum K v h1 a m ≡
        gapsw67_t3_teichmullerPartialSum K v h1 a n
        [SMOD (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m • ⊤ :
          Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K))] :=
    fun {m n} hmn => gapsw69_t1_partialSum_smodEq_of_le K v h1 a hmn
  exact hpre.prec hcau
end FLT.Gapsw69T1WittCohenLimitExistence
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw69T1WittCohenLimitExistence
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw68T4Rd67ConsumptionGate

noncomputable def gapsw69_t1_teichmullerLimit
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) :
    v.adicCompletionIntegers K :=
  Classical.choose (gapsw69_t1_partialSum_limit_exists K v h1 a)
end FLT.Gapsw69T1WittCohenLimitExistence
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw69T1WittCohenLimitExistence
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
p2m_open "IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing"
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw68T4Rd67ConsumptionGate
set_option maxHeartbeats 1600000 in

theorem gapsw69_t1_teichmullerLimit_sub_partialSum_mem
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ) :
    gapsw69_t1_teichmullerLimit K v h1 a -
      gapsw67_t3_teichmullerPartialSum K v h1 a N ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
  have _em := Classical.em
  have hsm : (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N • ⊤ :
      Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N := by
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
  have h := Classical.choose_spec (gapsw69_t1_partialSum_limit_exists K v h1 a) N
  have hmem := SModEq.sub_mem.mp h
  rw [hsm] at hmem
  simp only [gapsw69_t1_teichmullerLimit]
  have hneg : Classical.choose (gapsw69_t1_partialSum_limit_exists K v h1 a) -
      gapsw67_t3_teichmullerPartialSum K v h1 a N =
      -(gapsw67_t3_teichmullerPartialSum K v h1 a N -
        Classical.choose (gapsw69_t1_partialSum_limit_exists K v h1 a)) := by
    ring
  rw [hneg]
  exact neg_mem hmem
end FLT.Gapsw69T1WittCohenLimitExistence
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw69T3WittCohenLiftExactAsserter
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw59T2WittCohenLiftReduction
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw68T3WittCohenLiftAsserter
open FLT.Gapsw69T1WittCohenLimitExistence
open FLT.Gapsw69T2WittApproxRingLaws
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw69_t3_eq_of_forall_sub_mem_pow
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x y : v.adicCompletionIntegers K)
    (h : ∀ N : ℕ, x - y ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N) :
    x = y := by
  have _em := Classical.em
  have hbot : x - y ∈ (⊥ : Ideal (v.adicCompletionIntegers K)) := by
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
    exact (Submodule.mem_iInf _).mpr h
  rw [Ideal.mem_bot] at hbot
  exact sub_eq_zero.mp hbot
end FLT.Gapsw69T3WittCohenLiftExactAsserter
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw69T3WittCohenLiftExactAsserter
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw59T2WittCohenLiftReduction
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw68T3WittCohenLiftAsserter
open FLT.Gapsw69T1WittCohenLimitExistence
open FLT.Gapsw69T2WittApproxRingLaws
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw69_t3_fmul_exact_of_limit_approx
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (f : WittVector 3 ((𝓞 K) ⧸ v.asIdeal) → v.adicCompletionIntegers K)
    (hlim : ∀ (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ),
      f a - gapsw67_t3_teichmullerPartialSum K v h1 a N ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N)
    (happrox : ∀ (a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ), 0 < N →
      gapsw67_t3_teichmullerPartialSum K v h1 (a * b) N -
        gapsw67_t3_teichmullerPartialSum K v h1 a N *
          gapsw67_t3_teichmullerPartialSum K v h1 b N ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N) :
    ∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f (a * b) = f a * f b := by
  have _em := Classical.em
  intro a b
  apply gapsw69_t3_eq_of_forall_sub_mem_pow K v
  intro N
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [hN, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hsplit : f (a * b) - f a * f b =
      (f (a * b) - gapsw67_t3_teichmullerPartialSum K v h1 (a * b) N) +
        (gapsw67_t3_teichmullerPartialSum K v h1 (a * b) N -
          gapsw67_t3_teichmullerPartialSum K v h1 a N *
            gapsw67_t3_teichmullerPartialSum K v h1 b N) +
        -(gapsw67_t3_teichmullerPartialSum K v h1 a N *
            (f b - gapsw67_t3_teichmullerPartialSum K v h1 b N) +
          (f a - gapsw67_t3_teichmullerPartialSum K v h1 a N) * f b) := by
    ring
  rw [hsplit]
  exact add_mem (add_mem (hlim (a * b) N) (happrox a b N hN))
    (neg_mem (add_mem (Ideal.mul_mem_left _ _ (hlim b N))
      (Ideal.mul_mem_right _ _ (hlim a N))))
end FLT.Gapsw69T3WittCohenLiftExactAsserter
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw69T3WittCohenLiftExactAsserter
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw59T2WittCohenLiftReduction
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw68T3WittCohenLiftAsserter
open FLT.Gapsw69T1WittCohenLimitExistence
open FLT.Gapsw69T2WittApproxRingLaws
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw69_t3_fadd_exact_of_limit_approx
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h1 : v.asIdeal ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (f : WittVector 3 ((𝓞 K) ⧸ v.asIdeal) → v.adicCompletionIntegers K)
    (hlim : ∀ (a : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ),
      f a - gapsw67_t3_teichmullerPartialSum K v h1 a N ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N)
    (happrox : ∀ (a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal)) (N : ℕ), 0 < N →
      gapsw67_t3_teichmullerPartialSum K v h1 (a + b) N -
        (gapsw67_t3_teichmullerPartialSum K v h1 a N +
          gapsw67_t3_teichmullerPartialSum K v h1 b N) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ N) :
    ∀ a b : WittVector 3 ((𝓞 K) ⧸ v.asIdeal),
      f (a + b) = f a + f b := by
  have _em := Classical.em
  intro a b
  apply gapsw69_t3_eq_of_forall_sub_mem_pow K v
  intro N
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [hN, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hsplit : f (a + b) - (f a + f b) =
      (f (a + b) - gapsw67_t3_teichmullerPartialSum K v h1 (a + b) N) +
        (gapsw67_t3_teichmullerPartialSum K v h1 (a + b) N -
          (gapsw67_t3_teichmullerPartialSum K v h1 a N +
            gapsw67_t3_teichmullerPartialSum K v h1 b N)) +
        -((f a - gapsw67_t3_teichmullerPartialSum K v h1 a N) +
          (f b - gapsw67_t3_teichmullerPartialSum K v h1 b N)) := by
    ring
  rw [hsplit]
  exact add_mem (add_mem (hlim (a + b) N) (happrox a b N hN))
    (neg_mem (add_mem (hlim a N) (hlim b N)))
end FLT.Gapsw69T3WittCohenLiftExactAsserter
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
namespace FLT
namespace Gapsw69T3WittCohenLiftExactAsserter
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw59T2WittCohenLiftReduction
open FLT.Gapsw67T3WittDigitCongruenceEngine
open FLT.Gapsw68T3WittCohenLiftAsserter
open FLT.Gapsw69T1WittCohenLimitExistence
open FLT.Gapsw69T2WittApproxRingLaws
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gapsw68_t3_wittCohenLiftSupply_asserter :
    Gapsw59T2WittCohenLiftSupply := by
  have _em := Classical.em
  apply gapsw68_t3_wittCohenLiftSupply_of_limit_ringLaws
  intro K _ _ v h1 _hwild
  refine ⟨gapsw69_t1_teichmullerLimit K v h1,
    gapsw69_t1_teichmullerLimit_sub_partialSum_mem K v h1, ?_, ?_⟩
  · exact gapsw69_t3_fmul_exact_of_limit_approx K v h1
      (gapsw69_t1_teichmullerLimit K v h1)
      (gapsw69_t1_teichmullerLimit_sub_partialSum_mem K v h1)
      (fun a b N _ =>
        gapsw69_t2_teichmullerPartialSum_mul_sub_mem K v h1 a b N)
  · exact gapsw69_t3_fadd_exact_of_limit_approx K v h1
      (gapsw69_t1_teichmullerLimit K v h1)
      (gapsw69_t1_teichmullerLimit_sub_partialSum_mem K v h1)
      (fun a b N _ => by
        have := gapsw69_t2_teichmullerPartialSum_add_sub_mem K v h1 a b N
        rwa [sub_sub] at this)
end FLT.Gapsw69T3WittCohenLiftExactAsserter
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
namespace FLT
namespace Gapsw70T3SpineBResidualSurfaceFire
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw50T4PieceICompletedElementProduction
open FLT.Gapsw57T2DvrBaseProductionMint
open FLT.Gapsw58T1SeamSupplyDecomposition
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw59T1GlobalCRTPickSupplyDischarge
open FLT.Gapsw59T2WittCohenLiftReduction
open FLT.Gapsw60T5PostRd59RegistryGateAndWeld
open FLT.Gapsw69T3WittCohenLiftExactAsserter
set_option maxHeartbeats 1600000 in

theorem gapsw70_t3_residueSurjectivity_holds :
    Gapsw58T2UnramifiedDvrBaseResidueSurjectivityProduction := by
  have _em := Classical.em
  exact gapsw59_t2_residueSurjectivity_of_wittLift
    gapsw68_t3_wittCohenLiftSupply_asserter
end FLT.Gapsw70T3SpineBResidualSurfaceFire
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T1CofactorUnitOfResidueGenerator
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T6AbstractBaseAKLBFrame
open FLT.Gapsw78T7AbstractBaseEngineFire
open FLT.Gapsw78T8AbstractBaseDerivDifferentEq
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw7X3bDerivativeDifferentSlice
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw78T1PieceIResidualOfLocalDifferent
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 12800000 in

theorem gapsw79_t1_differentIdeal_eq_span_deriv_of_monogenic
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.Finite A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.IsTorsionFree A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    (h3A : Irreducible (3 : A))
    (x : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
    (hmono : Algebra.adjoin A {x} = ⊤) :
    differentIdeal A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      = Ideal.span
          {Polynomial.aeval x (Polynomial.derivative (minpoly A x))} := by
  have _em := Classical.em
  classical

  letI : Algebra A ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    ((algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        ((gapsw7X1mPlace K P hP).adicCompletion K)).comp
      (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))).toAlgebra
  letI : IsScalarTower A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul A ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      ((IsFractionRing.injective ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ((gapsw7X1mPlace K P hP).adicCompletion K)).comp
        (gapsw78_t6_algebraMap_injective K P hP A h3A))
  letI : Algebra (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    FractionRing.liftAlgebra A ((gapsw7X1mPlace K P hP).adicCompletion K)
  letI : IsScalarTower A (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    FractionRing.isScalarTower_liftAlgebra A
      ((gapsw7X1mPlace K P hP).adicCompletion K)
  letI : IsIntegralClosure ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) A
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    gapsw78_t6_isIntegralClosure K P hP A
  letI : Module.Finite (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    gapsw78_t6_module_finite_fractionRing K P hP A h3A
  haveI : CharZero A := gapsw78_t6_charZero A h3A
  haveI : CharZero (FractionRing A) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective A (FractionRing A))
  haveI : Algebra.IsIntegral (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    Algebra.IsIntegral.of_finite (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K)
  letI : IsDedekindDomain ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    gapsw7_x4g_isDedekindDomain_carrierIntegers K P hP

  exact gapsw7_x3b_differentIdeal_eq_span_aeval_derivative_of_monogenic A
    (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) x hmono
end FLT.Gapsw79T1CofactorUnitOfResidueGenerator
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T1CofactorUnitOfResidueGenerator
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T6AbstractBaseAKLBFrame
open FLT.Gapsw78T7AbstractBaseEngineFire
open FLT.Gapsw78T8AbstractBaseDerivDifferentEq
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw7X3bDerivativeDifferentSlice
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw78T1PieceIResidualOfLocalDifferent
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 12800000 in

theorem gapsw79_t1_pieceIResidual_of_localMonogenicResidueGen
    (hLocalMonogenicResidueGen :
      ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
        (hP : P ∈ IsDedekindDomain.primesOverFinset
          (Ideal.span {(3 : ℤ)}) (𝓞 K)),
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P →
        ∃ ξ : 𝓞 K, Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤ ∧
          ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
            [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
            [Module.Finite A
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
            [Module.IsTorsionFree A
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)],
            Irreducible (3 : A) →
            (∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
              ∃ a : A, b - algebraMap A
                    ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
                ∈ gapsw7X1mCompletionIdeal K P hP) →
            Algebra.adjoin A
                {(algebraMap (𝓞 K)
                  ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)} = ⊤ ∧
            IsUnit (Polynomial.aeval
                (algebraMap (𝓞 K)
                  ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)
              (((minpoly ℤ ξ).map (Int.castRingHom A)) /ₘ
                minpoly A (algebraMap (𝓞 K)
                  ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)))) :
    Gapsw48T5CompletionTransportPieceIResidual := by
  have _em := Classical.em
  classical

  apply gapsw78_t9_pieceIResidual_of_globalDerivVal
  intro K _ _ v hv hwild

  set P := v.asIdeal with hPdef
  have hplace : gapsw7X1mPlace K P hv = v :=
    gapsw78_t1_place_asIdeal_roundtrip K v hv

  obtain ⟨ξ, hadj, hcof⟩ := hLocalMonogenicResidueGen K P hv hwild
  refine ⟨ξ, hadj, ?_⟩

  rw [show v = gapsw7X1mPlace K P hv from hplace.symm]

  obtain ⟨A, _, _, _, _, _, h3A, hresA0⟩ :=
    gapsw70_t3_residueSurjectivity_holds K (gapsw7X1mPlace K P hv)
      (hplace ▸ hv) (hplace ▸ hwild)

  have hresA : ∀ b : (gapsw7X1mPlace K P hv).adicCompletionIntegers K,
      ∃ a : A, b - algebraMap A
            ((gapsw7X1mPlace K P hv).adicCompletionIntegers K) a
        ∈ gapsw7X1mCompletionIdeal K P hv := by
    intro b; obtain ⟨a, ha⟩ := hresA0 b
    exact ⟨a, (gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hv).symm ▸ ha⟩

  letI : Module.IsTorsionFree A
      ((gapsw7X1mPlace K P hv).adicCompletionIntegers K) :=
    gapsw78_t6_isTorsionFree K P hv A h3A

  obtain ⟨hmono, hunit⟩ := hcof A h3A hresA
  set ξP := algebraMap (𝓞 K)
      ((gapsw7X1mPlace K P hv).adicCompletionIntegers K) ξ with hξP

  have hdiff := gapsw79_t1_differentIdeal_eq_span_deriv_of_monogenic
    K P hv A h3A ξP hmono

  have hengine := gapsw78_t7_maximalIdeal_pow_le_of_abstractBase
    K P hv hwild A h3A hresA
  set e := (Ideal.span {(3 : ℤ)}).ramificationIdx' P with heq
  set d := e - 1 + e * padicValNat 3 e with hdeq
  rw [hdiff] at hengine

  obtain ⟨π, hπval⟩ :=
    adicCompletion.exists_uniformizer K (gapsw7X1mPlace K P hv)
  have hspan : Ideal.span {π} = gapsw7X1mCompletionIdeal K P hv := by
    rw [gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hv,
      adicCompletion.maximalIdeal_eq_span_uniformizer K
        (gapsw7X1mPlace K P hv) hπval]
  have hπdmem : π ^ d ∈ Ideal.span
      {Polynomial.aeval ξP (Polynomial.derivative (minpoly A ξP))} := by
    refine hengine ?_
    rw [← hspan, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _

  have hdvd : Polynomial.aeval ξP (Polynomial.derivative (minpoly A ξP)) ∣ π ^ d :=
    Ideal.mem_span_singleton.mp hπdmem
  have hvalfA : WithZero.exp (-(d : ℤ)) ≤
      Valued.v ((Polynomial.aeval ξP (Polynomial.derivative (minpoly A ξP))
        : (gapsw7X1mPlace K P hv).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hv).adicCompletion K) := by
    obtain ⟨c, hc⟩ := hdvd
    have hvalπd : Valued.v
        ((π ^ d : (gapsw7X1mPlace K P hv).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hv).adicCompletion K)
        = WithZero.exp (-(d : ℤ)) := by
      rw [SubmonoidClass.coe_pow, map_pow, hπval, ← WithZero.coe_pow,
        ← ofAdd_nsmul]
      simp [WithZero.exp, nsmul_eq_mul]
    have hvalle : Valued.v
        ((π ^ d : (gapsw7X1mPlace K P hv).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hv).adicCompletion K) ≤
        Valued.v ((Polynomial.aeval ξP (Polynomial.derivative (minpoly A ξP))
          : (gapsw7X1mPlace K P hv).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hv).adicCompletion K) := by
      rw [hc, MulMemClass.coe_mul, map_mul]
      exact mul_le_of_le_one_right' c.2
    exact hvalπd ▸ hvalle

  have hfAmonic : (minpoly A ξP).Monic :=
    minpoly.monic (IsIntegral.of_finite A ξP)
  have haeval0 : Polynomial.aeval ξP ((minpoly ℤ ξ).map (Int.castRingHom A)) = 0 := by
    rw [show Int.castRingHom A = algebraMap ℤ A from rfl,
      Polynomial.aeval_map_algebraMap, hξP,
      Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hmod : (minpoly ℤ ξ).map (Int.castRingHom A) %ₘ minpoly A ξP = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hfAmonic).mpr
      (minpoly.isIntegrallyClosed_dvd (IsIntegral.of_finite A ξP) haeval0)
  have hgA : (minpoly ℤ ξ).map (Int.castRingHom A)
      = minpoly A ξP
        * ((minpoly ℤ ξ).map (Int.castRingHom A) /ₘ minpoly A ξP) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div
      ((minpoly ℤ ξ).map (Int.castRingHom A)) (minpoly A ξP), hmod, zero_add]

  have hderiv : Polynomial.aeval ξP
        (Polynomial.derivative ((minpoly ℤ ξ).map (Int.castRingHom A)))
      = Polynomial.aeval ξP (Polynomial.derivative (minpoly A ξP))
        * Polynomial.aeval ξP
            ((minpoly ℤ ξ).map (Int.castRingHom A) /ₘ minpoly A ξP) := by
    conv_lhs => rw [hgA, Polynomial.derivative_mul, map_add, map_mul, map_mul,
      minpoly.aeval, zero_mul, add_zero]

  have hlhs : (algebraMap (𝓞 K)
        ((gapsw7X1mPlace K P hv).adicCompletionIntegers K)
        (Polynomial.aeval ξ (Polynomial.derivative (minpoly ℤ ξ))))
      = Polynomial.aeval ξP
          (Polynomial.derivative ((minpoly ℤ ξ).map (Int.castRingHom A))) := by
    rw [Polynomial.derivative_map,
      show Int.castRingHom A = algebraMap ℤ A from rfl,
      Polynomial.aeval_map_algebraMap, hξP,
      Polynomial.aeval_algebraMap_apply]

  have hvalq : Valued.v ((Polynomial.aeval ξP
        ((minpoly ℤ ξ).map (Int.castRingHom A) /ₘ minpoly A ξP)
        : (gapsw7X1mPlace K P hv).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hv).adicCompletion K) = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one _).mp hunit

  intro hle

  have hcoeeq : ((Polynomial.aeval ξ (Polynomial.derivative (minpoly ℤ ξ)) : 𝓞 K)
        : (gapsw7X1mPlace K P hv).adicCompletion K)
      = ((algebraMap (𝓞 K)
            ((gapsw7X1mPlace K P hv).adicCompletionIntegers K)
            (Polynomial.aeval ξ (Polynomial.derivative (minpoly ℤ ξ)))
          : (gapsw7X1mPlace K P hv).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hv).adicCompletion K) := by
    rw [algebraMap_completionIntegers, algebraMap_adicCompletion]
    rfl
  rw [hcoeeq, hlhs, hderiv, MulMemClass.coe_mul,
    Valued.v.map_mul, hvalq, mul_one] at hle

  have habs : WithZero.exp (-(d : ℤ))
      ≤ WithZero.exp (-(((e + e * padicValNat 3 e : ℕ) : ℤ))) :=
    hvalfA.trans hle
  rw [WithZero.exp_le_exp] at habs
  have he1 : 1 ≤ e :=
    Nat.one_le_iff_ne_zero.mpr (gapsw47_t5_p2_ramificationIdx_ne_zero K P hv)
  omega
end FLT.Gapsw79T1CofactorUnitOfResidueGenerator
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T2CofactorUnitResidueReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T6AbstractBaseAKLBFrame
open FLT.Gapsw78T7AbstractBaseEngineFire
open FLT.Gapsw7X3bDerivativeDifferentSlice
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw79T1CofactorUnitOfResidueGenerator
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw54T3WildCompletionDvrWitness
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open_scoped "IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"

theorem gapsw79_t2_pow_sub_pow_mem_sq {R : Type*} [CommRing R] (I : Ideal R)
    (x y : R) (q : ℕ) (hxy : x - y ∈ I) (hq : (q : R) ∈ I) :
    x ^ q - y ^ q ∈ I ^ 2 := by
  have _em := Classical.em
  set d := x - y with hd
  have hx : x = y + d := by rw [hd]; ring
  rw [hx, add_pow]

  have hsub : (∑ m ∈ Finset.range (q + 1),
        y ^ m * d ^ (q - m) * (q.choose m : R)) - y ^ q
      = ∑ m ∈ Finset.range q,
        y ^ m * d ^ (q - m) * (q.choose m : R) := by
    rw [Finset.sum_range_succ]
    simp
  rw [hsub]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hm' := Finset.mem_range.mp hm
  have hqm1 : 1 ≤ q - m := by omega

  rcases eq_or_lt_of_le hqm1 with heq1 | hgt1
  · have hm1 : m = q - 1 := by omega
    have hch : q.choose m = q := by
      rw [hm1, Nat.choose_symm (by omega : 1 ≤ q), Nat.choose_one_right]
    rw [← heq1, pow_one, hch, sq]
    exact Ideal.mul_mem_mul (I.mul_mem_left _ hxy) hq

  · have hd2 : d ^ (q - m) ∈ I ^ 2 := by
      have heq2 : d ^ (q - m) = d ^ 2 * d ^ (q - m - 2) := by
        rw [← pow_add]; congr 1; omega
      rw [heq2]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hxy 2)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hd2)
end FLT.Gapsw79T2CofactorUnitResidueReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T2CofactorUnitResidueReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T6AbstractBaseAKLBFrame
open FLT.Gapsw78T7AbstractBaseEngineFire
open FLT.Gapsw7X3bDerivativeDifferentSlice
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw79T1CofactorUnitOfResidueGenerator
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw54T3WildCompletionDvrWitness
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open_scoped "IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"
set_option maxHeartbeats 12800000 in

theorem gapsw79_t2_adjoin_top_of_frobFix_notin_sq
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (hwild : 3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.Finite A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.IsTorsionFree A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    (h3A : Irreducible (3 : A))
    (hresA : ∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
      ∃ a : A, b - algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
        ∈ gapsw7X1mCompletionIdeal K P hP)
    (ξ : 𝓞 K)
    (hfrob : (algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)
        ^ (Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
            ⧸ gapsw7X1mCompletionIdeal K P hP))
      - algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ
      ∉ (gapsw7X1mCompletionIdeal K P hP) ^ 2) :
    Algebra.adjoin A
        {(algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)} = ⊤ := by
  have _em := Classical.em
  classical
  set ξP := algebraMap (𝓞 K)
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ with hξP
  set 𝔪 := gapsw7X1mCompletionIdeal K P hP with h𝔪
  set q := Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)
    with hqdef
  set e := (Ideal.span {(3 : ℤ)}).ramificationIdx' P with heq
  have he0 : 0 < e :=
    Nat.pos_of_ne_zero (gapsw47_t5_p2_ramificationIdx_ne_zero K P hP)
  have he2 : 2 ≤ e := le_trans (by norm_num) (Nat.le_of_dvd he0 hwild)

  obtain ⟨a, ha⟩ := hresA ξP
  set η := ξP - algebraMap A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a with hη
  have hηmem : η ∈ 𝔪 := ha

  obtain ⟨π, hπ⟩ := adicCompletion.exists_uniformizer K (gapsw7X1mPlace K P hP)
  have hπval : Valued.v (π : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-1 : ℤ) := hπ
  have hspan : Ideal.span {π} = 𝔪 := by
    rw [h𝔪, gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP,
      adicCompletion.maximalIdeal_eq_span_uniformizer K
        (gapsw7X1mPlace K P hP) hπval]
  have hval3 : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-(e : ℤ)) := by
    rw [← map_ofNat (algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)) 3,
      algebraMap_completionIntegers,
      (gapsw7X1mPlace K P hP).valuedAdicCompletion_eq_valuation,
      (gapsw7X1mPlace K P hP).valuation_of_algebraMap,
      gapsw54_t3_intValuation_three_eq_ramificationIdx K (gapsw7X1mPlace K P hP),
      gapsw7_x1m_place_asIdeal K P hP]
  have h3ne : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ≠ 0 := by
    intro h; rw [h, ZeroMemClass.coe_zero, map_zero] at hval3
    exact WithZero.exp_ne_zero hval3.symm
  obtain ⟨n, u0, hu⟩ := adicCompletion.eq_pow_uniformizer_mul_unit K
    (gapsw7X1mPlace K P hP) h3ne hπval
  have hvu : Valued.v ((u0 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K) = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one _).mp u0.isUnit
  have hne : n = e := by
    have hun : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hP).adicCompletion K)
        = WithZero.exp (-(n : ℤ)) := by
      rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
        hπval, hvu, mul_one, ← WithZero.exp_nsmul, WithZero.exp_inj]; simp
    have h := hun.symm.trans hval3; rw [WithZero.exp_inj] at h; omega
  have h3fac : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      = (u0 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) * π ^ e := by
    rw [hu, hne, mul_comm]

  have h3mem_e : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ∈ 𝔪 ^ e := by
    rw [← hspan, Ideal.span_singleton_pow, h3fac]
    exact Ideal.mem_span_singleton.mpr ⟨u0, mul_comm _ _⟩
  have h3mem_sq : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ∈ 𝔪 ^ 2 := Ideal.pow_le_pow_right he2 h3mem_e
  have h3mem : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ∈ 𝔪 :=
    Ideal.pow_le_self he0.ne' h3mem_e

  haveI : (𝔪).IsMaximal :=
    h𝔪 ▸ gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP ▸
      IsLocalRing.maximalIdeal.isMaximal _

  haveI h𝔪fin : Finite (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪) := by
    haveI : 𝔪.LiesOver P := h𝔪 ▸ gapsw7_x1m_completionIdeal_liesOver K P hP
    have hsurjP : Function.Surjective
        (algebraMap (𝓞 K ⧸ P)
          (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)) := by
      intro y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨c, hc⟩ := gapsw54_t3_global_residue_system K
        (gapsw7X1mPlace K P hP) π hπval b
      refine ⟨Ideal.Quotient.mk _ c, ?_⟩
      show Ideal.Quotient.mk _
          (algebraMap (𝓞 K)
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c)
        = Ideal.Quotient.mk _ b
      exact Ideal.Quotient.eq.mpr (neg_sub b _ ▸ neg_mem (hspan ▸ hc))
    have hPne : P ≠ ⊥ := by
      intro hP0
      exact (gapsw7X1mPlace K P hP).ne_bot
        (by rw [gapsw7_x1m_place_asIdeal K P hP]; exact hP0)
    haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
    exact Finite.of_surjective _ hsurjP
  haveI : Fintype (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪) :=
    Fintype.ofFinite _
  have hqmem : (q : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hqdef,
      Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero
      (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)

  have hstep3 : ξP ^ q
      - (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a) ^ q
      ∈ 𝔪 ^ 2 :=
    gapsw79_t2_pow_sub_pow_mem_sq 𝔪 ξP _ q hηmem hqmem

  haveI h3max : (Ideal.span {(3 : A)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible h3A
  have h3map : algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) 3
      = (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    gapsw54_t3_algebraMap_three_reduction K (gapsw7X1mPlace K P hP) A
  have hcomap : 𝔪.comap
          (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
        = Ideal.span {(3 : A)} := by
    refine (h3max.eq_of_le ?_ ?_).symm
    · rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_comap, map_one]
      exact fun h1 => (‹𝔪.IsMaximal›).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, h3map]; exact h3mem
  haveI : 𝔪.LiesOver (Ideal.span {(3 : A)}) := ⟨hcomap.symm⟩
  have hsurj : Function.Surjective
      (algebraMap (A ⧸ Ideal.span {(3 : A)})
        (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)) := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hresA b
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    show Ideal.Quotient.mk _
        (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c)
      = Ideal.Quotient.mk _ b
    exact Ideal.Quotient.eq.mpr (neg_sub b _ ▸ neg_mem hc)
  have hinj : Function.Injective
      (algebraMap (A ⧸ Ideal.span {(3 : A)})
        (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)) := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq, ← hcomap, Ideal.mem_comap, map_sub]
    exact Ideal.Quotient.eq.mp hxy
  have hbij : Function.Bijective
      (algebraMap (A ⧸ Ideal.span {(3 : A)})
        (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)) :=
    ⟨hinj, hsurj⟩
  haveI : Finite (A ⧸ Ideal.span {(3 : A)}) := Finite.of_injective _ hinj
  haveI : Fintype (A ⧸ Ideal.span {(3 : A)}) := Fintype.ofFinite _
  letI : Field (A ⧸ Ideal.span {(3 : A)}) := Ideal.Quotient.field _
  have hcard : Nat.card (A ⧸ Ideal.span {(3 : A)}) = q := by
    rw [hqdef]; exact Nat.card_eq_of_bijective _ hbij
  have hfermat : a ^ q - a ∈ Ideal.span {(3 : A)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ← hcard,
      Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]

  have hstep5 : (algebraMap A
        ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a) ^ q
      - algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
      ∈ 𝔪 ^ 2 := by
    rw [← map_pow, ← map_sub]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hfermat
    rw [hc, map_mul, h3map]
    exact Ideal.mul_mem_right _ _ h3mem_sq

  have hstep6 : ξP ^ q
      - algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
      ∈ 𝔪 ^ 2 := by
    have : ξP ^ q
        - algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
        = (ξP ^ q
            - (algebraMap A
                ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a) ^ q)
          + ((algebraMap A
                ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a) ^ q
            - algebraMap A
                ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a) := by ring
    rw [this]; exact Ideal.add_mem _ hstep3 hstep5

  have hηnotsq : η ∉ 𝔪 ^ 2 := by
    intro hη2
    have : ξP ^ q - ξP
        = (ξP ^ q
            - algebraMap A
                ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a) - η := by
      rw [hη]; ring
    exact hfrob (this ▸ Ideal.sub_mem _ hstep6 hη2)

  have hηspan : Ideal.span {η} = 𝔪 := by
    rw [← hspan] at hηmem hηnotsq ⊢
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hηmem
    have hcunit : IsUnit c := by
      by_contra hcu
      have hcmem : c ∈ Ideal.span {π} := by
        rw [hspan, h𝔪, gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP]
        exact hcu
      obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp hcmem
      refine hηnotsq ?_
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hc, hc', sq]
      exact ⟨c', by ring⟩
    rw [hc, Ideal.span_singleton_mul_right_unit hcunit]

  have hηval : Valued.v (η : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-1 : ℤ) := by
    have hassoc : Associated π η :=
      Ideal.span_singleton_eq_span_singleton.mp (hspan.trans hηspan.symm)
    obtain ⟨w, hw⟩ := hassoc
    have hwval : Valued.v ((w : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hP).adicCompletion K) = 1 :=
      (ValuationSubring.isUnit_iff_valued_eq_one _).mp w.isUnit
    rw [← hw, MulMemClass.coe_mul, map_mul, hπval, hwval, mul_one]

  obtain ⟨n', u0', hu'⟩ := adicCompletion.eq_pow_uniformizer_mul_unit K
    (gapsw7X1mPlace K P hP) h3ne hηval
  have hvu' : Valued.v ((u0' : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K) = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one _).mp u0'.isUnit
  have hne' : n' = e := by
    have hun : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hP).adicCompletion K)
        = WithZero.exp (-(n' : ℤ)) := by
      rw [hu', MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
        hηval, hvu', mul_one, ← WithZero.exp_nsmul, WithZero.exp_inj]; simp
    have h := hun.symm.trans hval3; rw [WithZero.exp_inj] at h; omega
  have h3Bη : algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) 3
      = (u0' : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) * η ^ e := by
    rw [h3map, hu', hne', mul_comm]
  have hresη : ∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
      ∃ c : A, b - algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c
          ∈ Ideal.span {η} := by
    intro b; obtain ⟨c, hc⟩ := hresA b; exact ⟨c, hηspan ▸ hc⟩
  have hmonoη : Algebra.adjoin A {η} = ⊤ :=
    gapsw47_t5_p1_adjoin_eq_top_of_irreducible η e (3 :) h3A u0' h3Bη hresη

  rw [eq_top_iff]; intro b _
  have hξPmem : ξP ∈ Algebra.adjoin A {ξP} := Algebra.self_mem_adjoin_singleton A ξP
  have hamem : algebraMap A
        ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
      ∈ Algebra.adjoin A {ξP} := Subalgebra.algebraMap_mem _ a
  have hηmem' : η ∈ Algebra.adjoin A {ξP} := by
    rw [hη]; exact Subalgebra.sub_mem _ hξPmem hamem
  have hle : Algebra.adjoin A {η} ≤ Algebra.adjoin A {ξP} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hηmem')
  exact hle (hmonoη ▸ Algebra.mem_top)
end FLT.Gapsw79T2CofactorUnitResidueReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T2CofactorUnitResidueReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T6AbstractBaseAKLBFrame
open FLT.Gapsw78T7AbstractBaseEngineFire
open FLT.Gapsw7X3bDerivativeDifferentSlice
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw79T1CofactorUnitOfResidueGenerator
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw54T3WildCompletionDvrWitness
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open_scoped "IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"
set_option maxHeartbeats 19200000 in

theorem gapsw79_t2_isUnit_cofactor_of_residuePoly_nondvd
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (hwild : 3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.Finite A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    [Module.IsTorsionFree A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)]
    (h3A : Irreducible (3 : A))
    (hresA : ∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
      ∃ a : A, b - algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a
        ∈ gapsw7X1mCompletionIdeal K P hP)
    (ξ : 𝓞 K)
    (hmono : Algebra.adjoin A
        {(algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)} = ⊤)
    (hmu : Polynomial.rootMultiplicity
        (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)
          (algebraMap (𝓞 K)
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ))
        ((minpoly ℤ ξ).map
          ((Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)).comp
            (algebraMap ℤ
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))))
      ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P) :
    IsUnit (Polynomial.aeval
        (algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)
      (((minpoly ℤ ξ).map (Int.castRingHom A)) /ₘ
        minpoly A (algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ))) := by
  have _em := Classical.em
  classical
  set ξP := algebraMap (𝓞 K)
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ with hξP
  set 𝔪 := gapsw7X1mCompletionIdeal K P hP with h𝔪
  set e := (Ideal.span {(3 : ℤ)}).ramificationIdx' P with heq
  have he0 : 0 < e :=
    Nat.pos_of_ne_zero (gapsw47_t5_p2_ramificationIdx_ne_zero K P hP)
  have he2 : 2 ≤ e := le_trans (by norm_num) (Nat.le_of_dvd he0 hwild)

  obtain ⟨π, hπ⟩ := adicCompletion.exists_uniformizer K (gapsw7X1mPlace K P hP)
  have hπval : Valued.v (π : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-1 : ℤ) := hπ
  have hspan : Ideal.span {π} = 𝔪 := by
    rw [h𝔪, gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP,
      adicCompletion.maximalIdeal_eq_span_uniformizer K
        (gapsw7X1mPlace K P hP) hπval]
  have hval3 : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-(e : ℤ)) := by
    rw [← map_ofNat (algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)) 3,
      algebraMap_completionIntegers,
      (gapsw7X1mPlace K P hP).valuedAdicCompletion_eq_valuation,
      (gapsw7X1mPlace K P hP).valuation_of_algebraMap,
      gapsw54_t3_intValuation_three_eq_ramificationIdx K (gapsw7X1mPlace K P hP),
      gapsw7_x1m_place_asIdeal K P hP]
  have h3ne : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ≠ 0 := by
    intro h; rw [h, ZeroMemClass.coe_zero, map_zero] at hval3
    exact WithZero.exp_ne_zero hval3.symm
  obtain ⟨n, u0, hu⟩ := adicCompletion.eq_pow_uniformizer_mul_unit K
    (gapsw7X1mPlace K P hP) h3ne hπval
  have hvu : Valued.v ((u0 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K) = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one _).mp u0.isUnit
  have hne : n = e := by
    have hun : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hP).adicCompletion K)
        = WithZero.exp (-(n : ℤ)) := by
      rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
        hπval, hvu, mul_one, ← WithZero.exp_nsmul, WithZero.exp_inj]; simp
    have h := hun.symm.trans hval3; rw [WithZero.exp_inj] at h; omega
  have h3fac : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      = (u0 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) * π ^ e := by
    rw [hu, hne, mul_comm]
  have h3mem_e : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ∈ 𝔪 ^ e := by
    rw [← hspan, Ideal.span_singleton_pow, h3fac]
    exact Ideal.mem_span_singleton.mpr ⟨u0, mul_comm _ _⟩
  have h3mem_sq : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ∈ 𝔪 ^ 2 := Ideal.pow_le_pow_right he2 h3mem_e
  have h3mem : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ∈ 𝔪 :=
    Ideal.pow_le_self he0.ne' h3mem_e
  haveI h3max : (Ideal.span {(3 : A)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible h3A
  have h3map : algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) 3
      = (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    gapsw54_t3_algebraMap_three_reduction K (gapsw7X1mPlace K P hP) A
  haveI : (𝔪).IsMaximal :=
    h𝔪 ▸ gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP ▸
      IsLocalRing.maximalIdeal.isMaximal _
  have hcomap : 𝔪.comap
          (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
        = Ideal.span {(3 : A)} := by
    refine (h3max.eq_of_le ?_ ?_).symm
    · rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_comap, map_one]
      exact fun h1 => (‹𝔪.IsMaximal›).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, h3map]; exact h3mem

  obtain ⟨a, ha⟩ := hresA ξP
  set η := ξP - algebraMap A
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a with hη
  have hηmem : η ∈ 𝔪 := ha
  have hmonoη : Algebra.adjoin A {η} = ⊤ := by
    rw [eq_top_iff]; intro b _
    have hξPmem : ξP ∈ Algebra.adjoin A {η} := by
      have : ξP = η + algebraMap A
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a := by
        rw [hη]; ring
      rw [this]
      exact Subalgebra.add_mem _ (Algebra.self_mem_adjoin_singleton A η)
        (Subalgebra.algebraMap_mem _ a)
    exact (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hξPmem))
      (hmono ▸ Algebra.mem_top)

  have hπirr := gapsw54_t3_uniformizer_irreducible (𝓞 K) K
    (gapsw7X1mPlace K P hP) π hπval
  have hπnotsq : π ∉ 𝔪 ^ 2 := by
    rw [← hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : π * 1 = π * (π * c) := by rw [mul_one, ← mul_assoc, ← sq, ← hc]
    exact hπirr.not_isUnit
      (isUnit_of_dvd_one ⟨c, (mul_left_cancel₀ hπirr.ne_zero h1)⟩)
  have hηnotsq : η ∉ 𝔪 ^ 2 := by
    intro hη2

    have hAsurj2 : ∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
        ∃ c : A, b - algebraMap A
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c ∈ 𝔪 ^ 2 := by
      intro b
      have hbtop : b ∈ Algebra.adjoin A {η} := hmonoη ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hbtop
      obtain ⟨p, hp⟩ := hbtop
      refine ⟨p.coeff 0, ?_⟩
      have hb' : b = (Polynomial.aeval η) p.divX * η
          + algebraMap A
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) (p.coeff 0) := by
        calc b = (Polynomial.aeval η) p := hp.symm
          _ = (Polynomial.aeval η) (p.divX * Polynomial.X + Polynomial.C (p.coeff 0)) :=
              by rw [Polynomial.divX_mul_X_add]
          _ = _ := by
              rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [hb', add_sub_cancel_right, mul_comm]
      exact Ideal.mul_mem_right _ _ hη2
    obtain ⟨c, hc⟩ := hAsurj2 π
    have hcmem : c ∈ Ideal.span {(3 : A)} := by
      rw [← hcomap, Ideal.mem_comap]
      have : algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c
          = π - (π - algebraMap A
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c) := by ring
      rw [this]
      exact Ideal.sub_mem _ (hspan ▸ Ideal.mem_span_singleton_self π)
        (Ideal.pow_le_self (by omega) hc)
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp hcmem
    have hφc : algebraMap A
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c ∈ 𝔪 ^ 2 := by
      rw [hc', map_mul, h3map]; exact Ideal.mul_mem_right _ _ h3mem_sq
    exact hπnotsq (by
      have : π = (π - algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c)
          + algebraMap A
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c := by ring
      rw [this]; exact Ideal.add_mem _ hc hφc)

  have hηspan : Ideal.span {η} = 𝔪 := by
    rw [← hspan] at hηmem hηnotsq ⊢
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hηmem
    have hcunit : IsUnit c := by
      by_contra hcu
      have hcmem : c ∈ Ideal.span {π} := by
        rw [hspan, h𝔪, gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP]
        exact hcu
      obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp hcmem
      exact hηnotsq (by
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hc, hc', sq]
        exact ⟨c', by ring⟩)
    rw [hc, Ideal.span_singleton_mul_right_unit hcunit]
  have hηval : Valued.v (η : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-1 : ℤ) := by
    have hassoc : Associated π η :=
      Ideal.span_singleton_eq_span_singleton.mp (hspan.trans hηspan.symm)
    obtain ⟨w, hw⟩ := hassoc
    have hwval : Valued.v ((w : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hP).adicCompletion K) = 1 :=
      (ValuationSubring.isUnit_iff_valued_eq_one _).mp w.isUnit
    rw [← hw, MulMemClass.coe_mul, map_mul, hπval, hwval, mul_one]

  obtain ⟨n', u0', hu'⟩ := adicCompletion.eq_pow_uniformizer_mul_unit K
    (gapsw7X1mPlace K P hP) h3ne hηval
  have hvu' : Valued.v ((u0' : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K) = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one _).mp u0'.isUnit
  have hne' : n' = e := by
    have hun : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hP).adicCompletion K)
        = WithZero.exp (-(n' : ℤ)) := by
      rw [hu', MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
        hηval, hvu', mul_one, ← WithZero.exp_nsmul, WithZero.exp_inj]; simp
    have h := hun.symm.trans hval3; rw [WithZero.exp_inj] at h; omega
  have h3Bη : algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) 3
      = (u0' : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) * η ^ e := by
    rw [h3map, hu', hne', mul_comm]
  have hresη : ∀ b : (gapsw7X1mPlace K P hP).adicCompletionIntegers K,
      ∃ c : A, b - algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c
          ∈ Ideal.span {η} := by
    intro b; obtain ⟨c, hc⟩ := hresA b; exact ⟨c, hηspan ▸ hc⟩

  letI : Algebra A ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    ((algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        ((gapsw7X1mPlace K P hP).adicCompletion K)).comp
      (algebraMap A
        ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))).toAlgebra
  letI : IsScalarTower A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul A ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      ((IsFractionRing.injective
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ((gapsw7X1mPlace K P hP).adicCompletion K)).comp
        (gapsw78_t6_algebraMap_injective K P hP A h3A))
  letI : Algebra (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    FractionRing.liftAlgebra A ((gapsw7X1mPlace K P hP).adicCompletion K)
  letI : IsScalarTower A (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    FractionRing.isScalarTower_liftAlgebra A
      ((gapsw7X1mPlace K P hP).adicCompletion K)
  letI : IsIntegralClosure
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) A
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    gapsw78_t6_isIntegralClosure K P hP A
  letI : Module.Finite (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    gapsw78_t6_module_finite_fractionRing K P hP A h3A
  haveI : CharZero A := gapsw78_t6_charZero A h3A
  haveI : CharZero (FractionRing A) :=
    charZero_of_injective_algebraMap
      (IsFractionRing.injective A (FractionRing A))
  haveI : Algebra.IsIntegral (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K) :=
    Algebra.IsIntegral.of_finite (FractionRing A)
      ((gapsw7X1mPlace K P hP).adicCompletion K)
  letI : IsDedekindDomain
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
    gapsw7_x4g_isDedekindDomain_carrierIntegers K P hP
  have hηirr := gapsw54_t3_uniformizer_irreducible (𝓞 K) K
    (gapsw7X1mPlace K P hP) η hηval
  have hint : IsIntegral A η := Algebra.IsIntegral.isIntegral η
  have hmonic : (minpoly A η).Monic := minpoly.monic hint
  have hdegη : (minpoly A η).natDegree = e := by
    have hfrac : minpoly (FractionRing A)
          (algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
            ((gapsw7X1mPlace K P hP).adicCompletion K) η)
        = (minpoly A η).map (algebraMap A (FractionRing A)) :=
      minpoly.isIntegrallyClosed_eq_field_fractions
        (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) hint
    have hdegeq : (minpoly A η).natDegree
        = (minpoly (FractionRing A)
            (algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
              ((gapsw7X1mPlace K P hP).adicCompletion K) η)).natDegree := by
      rw [hfrac, hmonic.natDegree_map]
    rw [hdegeq]
    have hadj : Algebra.adjoin (FractionRing A)
        {algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ((gapsw7X1mPlace K P hP).adicCompletion K) η} = ⊤ :=
      gapsw7_x3b_adjoin_fractionField_eq_top_of_monogenic A
        (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) η hmonoη
    set ηL := algebraMap ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ((gapsw7X1mPlace K P hP).adicCompletion K) η
    have hxL : IsIntegral (FractionRing A) ηL := Algebra.IsIntegral.isIntegral ηL
    have hIF : (FractionRing A)⟮ηL⟯
        = (⊤ : IntermediateField (FractionRing A)
            ((gapsw7X1mPlace K P hP).adicCompletion K)) :=
      IntermediateField.toSubalgebra_injective <| by
        rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
            hxL.isAlgebraic, hadj, IntermediateField.top_toSubalgebra]
    rw [← IntermediateField.adjoin.finrank hxL, hIF,
      IntermediateField.finrank_top']
    have hpne : (Ideal.span {(3 : A)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact h3A.ne_zero
    have hmaxeq : gapsw7X1mCompletionIdeal K P hP
        = IsLocalRing.maximalIdeal
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) :=
      gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP
    have hef := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
      ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      (FractionRing A) ((gapsw7X1mPlace K P hP).adicCompletion K) hpne
    rw [← hmaxeq, ← h𝔪] at hef
    rw [gapsw78_t7_inertiaDeg_eq_one_of_abstractResidueSurj K P hP A h3A
        (h𝔪 ▸ h3mem) (h𝔪 ▸ hresA), mul_one] at hef
    have hmap3 : Ideal.map
          (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
          (Ideal.span {(3 : A)}) = 𝔪 ^ e := by
      rw [Ideal.map_span, Set.image_singleton, h3Bη,
        Ideal.span_singleton_mul_left_unit u0'.isUnit,
        ← Ideal.span_singleton_pow, hηspan]
    have hPne : 𝔪 ≠ ⊥ := by
      rw [← hηspan, Ne, Ideal.span_singleton_eq_bot]; exact hηirr.ne_zero
    have hPprime : (𝔪).IsPrime := (‹𝔪.IsMaximal›).isPrime
    have hPirr : Irreducible 𝔪 :=
      (Ideal.prime_of_isPrime hPne hPprime).irreducible
    have hramloc : (Ideal.span {(3 : A)}).ramificationIdx' 𝔪 = e := by
      rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
          (hmap3 ▸ pow_ne_zero e hPne) hPprime hPne, hmap3,
        UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
        UniqueFactorizationMonoid.normalizedFactors_irreducible hPirr,
        normalize_eq, Multiset.count_singleton_self, mul_one]
    omega

  have hspan3A : Ideal.span {(3 : A)} = IsLocalRing.maximalIdeal A :=
    h3max.eq_of_le (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h3A.not_isUnit))

  have hηe_mem : η ^ e ∈ 𝔪 ^ e := by
    rw [← hηspan, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hφ3_mem : ∀ c ∈ Ideal.span {(3 : A)},
      algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) c
        ∈ 𝔪 ^ e := by
    intro c hc
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp hc
    rw [hc', map_mul, h3map]; exact Ideal.mul_mem_right _ _ h3mem_e

  have hsum0 : ∑ j ∈ Finset.range (e + 1),
        algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ((minpoly A η).coeff j) * η ^ j = 0 := by
    have := minpoly.aeval A η
    rw [Polynomial.aeval_eq_sum_range, hdegη] at this
    simpa [Algebra.smul_def] using this

  have hEis : ∀ i < e, (minpoly A η).coeff i ∈ Ideal.span {(3 : A)} := by
    intro i hi
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    by_contra hni
    have hunit_i : IsUnit ((minpoly A η).coeff i) := by
      by_contra hnu; exact hni (hspan3A ▸ hnu)

    have hsplit : algebraMap A
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ((minpoly A η).coeff i) * η ^ i
        = -(∑ j ∈ Finset.range (e + 1) \ {i},
            algebraMap A
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
              ((minpoly A η).coeff j) * η ^ j) := by
      have hmem : i ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
      have hsplit' := hsum0
      rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hmem),
        Finset.sum_singleton] at hsplit'
      exact eq_neg_of_add_eq_zero_right hsplit'
    have hrest : ∑ j ∈ Finset.range (e + 1) \ {i},
          algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
            ((minpoly A η).coeff j) * η ^ j ∈ 𝔪 ^ (i + 1) := by
      refine Ideal.sum_mem _ fun j hj => ?_
      obtain ⟨hj1, hji⟩ := Finset.mem_sdiff.mp hj
      simp only [Finset.mem_singleton] at hji
      rcases lt_or_gt_of_ne hji with hjlt | hjgt
      ·
        exact Ideal.mul_mem_right _ _
          (Ideal.pow_le_pow_right (by omega)
            (hφ3_mem _ (ih j hjlt (lt_trans hjlt hi))))
      ·
        have : η ^ j = η ^ (i + 1) * η ^ (j - (i + 1)) := by
          rw [← pow_add]; congr 1; omega
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
          (by rw [← hηspan, Ideal.span_singleton_pow]
              exact Ideal.mem_span_singleton_self _))
    have hterm : algebraMap A
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ((minpoly A η).coeff i) * η ^ i ∈ 𝔪 ^ (i + 1) := by
      rw [hsplit]; exact neg_mem hrest

    have hηi : η ^ i ∈ 𝔪 ^ (i + 1) := by
      have huφ : IsUnit (algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
            ((minpoly A η).coeff i)) := hunit_i.map _
      obtain ⟨w, hw⟩ := huφ
      have := Ideal.mul_mem_left (𝔪 ^ (i + 1))
        ((w⁻¹ : _) : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) hterm
      rwa [← mul_assoc, ← hw, Units.inv_mul, one_mul] at this
    rw [← hηspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hηi
    obtain ⟨c, hc⟩ := hηi
    have h1 : η ^ i * 1 = η ^ i * (η * c) := by
      rw [mul_one, ← mul_assoc, ← pow_succ, ← hc]
    exact hηirr.not_isUnit (isUnit_of_dvd_one
      ⟨c, mul_left_cancel₀ (pow_ne_zero i hηirr.ne_zero) h1⟩)
  have hpbar : (minpoly A η).map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))
      = Polynomial.X ^ e := by
    refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
    split_ifs with hie
    · rw [hie, ← hdegη, hmonic.coeff_natDegree, map_one]
    · rcases lt_or_ge i e with hlt | hge
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr (hEis i hlt)
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (hdegη ▸ lt_of_le_of_ne hge (Ne.symm hie)), map_zero]

  have hfAbar : (minpoly A ξP).map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))
      = (Polynomial.X
          - Polynomial.C (Ideal.Quotient.mk (Ideal.span {(3 : A)}) a)) ^ e := by

    have hcomp_monic : ((minpoly A η).comp (Polynomial.X - Polynomial.C a)).Monic :=
      hmonic.comp (Polynomial.monic_X_sub_C a) (fun h => by
        simp [Polynomial.natDegree_X_sub_C] at h)
    have hcomp_deg : ((minpoly A η).comp
        (Polynomial.X - Polynomial.C a)).natDegree = e := by
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one, hdegη]
    have hcomp_aeval : Polynomial.aeval ξP
        ((minpoly A η).comp (Polynomial.X - Polynomial.C a)) = 0 := by
      rw [Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        show ξP - algebraMap A _ a = η from (hη ▸ rfl), minpoly.aeval]
    have hdvd : minpoly A ξP
        ∣ (minpoly A η).comp (Polynomial.X - Polynomial.C a) :=
      minpoly.isIntegrallyClosed_dvd (IsIntegral.of_finite A ξP) hcomp_aeval

    have hcomp'_aeval : Polynomial.aeval η
        ((minpoly A ξP).comp (Polynomial.X + Polynomial.C a)) = 0 := by
      rw [Polynomial.aeval_comp, map_add, Polynomial.aeval_X, Polynomial.aeval_C,
        show η + algebraMap A _ a = ξP from by rw [hη]; ring, minpoly.aeval]
    have hdvd' : minpoly A η
        ∣ (minpoly A ξP).comp (Polynomial.X + Polynomial.C a) :=
      minpoly.isIntegrallyClosed_dvd hint hcomp'_aeval
    have hdegfA : (minpoly A ξP).natDegree = e := by
      have hle : (minpoly A ξP).natDegree ≤ e := by
        have := Polynomial.natDegree_le_of_dvd hdvd hcomp_monic.ne_zero
        omega
      have hge : e ≤ (minpoly A ξP).natDegree := by
        have := Polynomial.natDegree_le_of_dvd hdvd'
          ((minpoly.monic (IsIntegral.of_finite A ξP)).comp
            (Polynomial.monic_X_add_C a) (fun h => by
              simp [Polynomial.natDegree_X_add_C] at h)).ne_zero
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one,
          hdegη] at this
        omega
      omega
    have hshift : minpoly A ξP
        = (minpoly A η).comp (Polynomial.X - Polynomial.C a) :=
      (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        (minpoly.monic (IsIntegral.of_finite A ξP)) hcomp_monic hdvd
        (by rw [hcomp_deg, hdegfA])).symm
    rw [hshift, Polynomial.map_comp, hpbar, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, Polynomial.X_pow_comp]

  set ξPbar := Ideal.Quotient.mk 𝔪 ξP with hξPbar
  set fA := minpoly A ξP with hfA
  set qA := ((minpoly ℤ ξ).map (Int.castRingHom A)) /ₘ fA with hqA
  have hfAmonic : fA.Monic := minpoly.monic (IsIntegral.of_finite A ξP)
  have haeval0 : Polynomial.aeval ξP ((minpoly ℤ ξ).map (Int.castRingHom A)) = 0 := by
    rw [show Int.castRingHom A = algebraMap ℤ A from rfl,
      Polynomial.aeval_map_algebraMap, hξP,
      Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hgA : (minpoly ℤ ξ).map (Int.castRingHom A) = fA * qA := by
    have hmod : (minpoly ℤ ξ).map (Int.castRingHom A) %ₘ fA = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hfAmonic).mpr
        (minpoly.isIntegrallyClosed_dvd (IsIntegral.of_finite A ξP) haeval0)
    conv_lhs => rw [← Polynomial.modByMonic_add_div
      ((minpoly ℤ ξ).map (Int.castRingHom A)) fA, hmod, zero_add]

  haveI : 𝔪.LiesOver (Ideal.span {(3 : A)}) := ⟨hcomap.symm⟩
  have hcomm : (Ideal.Quotient.mk 𝔪).comp
        (algebraMap A ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
      = (algebraMap (A ⧸ Ideal.span {(3 : A)})
          (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)).comp
        (Ideal.Quotient.mk (Ideal.span {(3 : A)})) := by
    ext x; rfl

  have hgbarcomm : (minpoly ℤ ξ).map
        ((Ideal.Quotient.mk 𝔪).comp
          (algebraMap ℤ ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)))
      = (((minpoly ℤ ξ).map (Int.castRingHom A)).map
          (Ideal.Quotient.mk (Ideal.span {(3 : A)}))).map
        (algebraMap (A ⧸ Ideal.span {(3 : A)})
          (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)) := by
    rw [Polynomial.map_map, Polynomial.map_map, ← hcomm]
    congr 1
    ext x; simp [IsScalarTower.algebraMap_apply ℤ A]

  have haevalbar : Ideal.Quotient.mk 𝔪 (Polynomial.aeval ξP qA)
      = Polynomial.eval₂
          (algebraMap (A ⧸ Ideal.span {(3 : A)})
            (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪))
          ξPbar
          (qA.map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))) := by
    rw [Polynomial.eval₂_map, hξPbar, Polynomial.aeval_def,
      Polynomial.hom_eval₂, hcomm]

  have hξPbar_eq : ξPbar
      = algebraMap (A ⧸ Ideal.span {(3 : A)})
          (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)
        (Ideal.Quotient.mk (Ideal.span {(3 : A)}) a) := by
    rw [hξPbar, show (algebraMap (A ⧸ Ideal.span {(3 : A)})
          (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪))
        (Ideal.Quotient.mk (Ideal.span {(3 : A)}) a)
      = Ideal.Quotient.mk 𝔪
          (algebraMap A
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) a) from rfl,
      Ideal.Quotient.eq]
    exact hηmem

  have hgbar_fact : (minpoly ℤ ξ).map
        ((Ideal.Quotient.mk 𝔪).comp
          (algebraMap ℤ ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)))
      = (Polynomial.X - Polynomial.C ξPbar) ^ e
        * (qA.map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))).map
            (algebraMap (A ⧸ Ideal.span {(3 : A)})
              (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)) := by
    rw [hgbarcomm, hgA, Polynomial.map_mul, Polynomial.map_mul, hfAbar,
      Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, ← hξPbar_eq]

  haveI : Nontrivial
      (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪) :=
    Ideal.Quotient.nontrivial_iff.mpr (‹𝔪.IsMaximal›).ne_top
  have hgbar_ne : (minpoly ℤ ξ).map
        ((Ideal.Quotient.mk 𝔪).comp
          (algebraMap ℤ ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)))
      ≠ 0 := by
    refine Polynomial.map_monic_ne_zero ?_
    exact minpoly.monic (IsIntegral.of_finite ℤ ξ)
  have hrootMult : Polynomial.rootMultiplicity ξPbar
        ((minpoly ℤ ξ).map
          ((Ideal.Quotient.mk 𝔪).comp
            (algebraMap ℤ ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))))
      = e + Polynomial.rootMultiplicity ξPbar
          ((qA.map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))).map
            (algebraMap (A ⧸ Ideal.span {(3 : A)})
              (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪))) := by
    rw [hgbar_fact, Polynomial.rootMultiplicity_mul (hgbar_fact ▸ hgbar_ne),
      Polynomial.rootMultiplicity_X_sub_C_pow]

  have hrootMult_q : Polynomial.rootMultiplicity ξPbar
        ((qA.map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))).map
          (algebraMap (A ⧸ Ideal.span {(3 : A)})
            (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪))) = 0 := by
    have h := hmu; rw [hrootMult] at h; omega

  have hqbar_ne : Polynomial.eval₂
        (algebraMap (A ⧸ Ideal.span {(3 : A)})
          (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪))
        ξPbar
        (qA.map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))) ≠ 0 := by
    have hqAmap_ne : (qA.map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))).map
          (algebraMap (A ⧸ Ideal.span {(3 : A)})
            (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)) ≠ 0 := by
      intro h0
      have := hgbar_fact
      rw [h0, mul_zero] at this
      exact hgbar_ne this
    intro heval0
    have : Polynomial.IsRoot
        ((qA.map (Ideal.Quotient.mk (Ideal.span {(3 : A)}))).map
          (algebraMap (A ⧸ Ideal.span {(3 : A)})
            (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)))
        ξPbar := by
      show Polynomial.eval ξPbar _ = 0
      rw [Polynomial.eval_map]; exact heval0
    have := (Polynomial.rootMultiplicity_pos hqAmap_ne).mpr this
    omega
  have hnotmem : Polynomial.aeval ξP qA ∉ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, haevalbar]
    exact hqbar_ne
  by_contra hnu
  exact hnotmem (h𝔪 ▸ gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP ▸ hnu)
end FLT.Gapsw79T2CofactorUnitResidueReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T2CofactorUnitResidueReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw78T6AbstractBaseAKLBFrame
open FLT.Gapsw78T7AbstractBaseEngineFire
open FLT.Gapsw7X3bDerivativeDifferentSlice
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw79T1CofactorUnitOfResidueGenerator
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
open FLT.Gapsw54T3WildCompletionDvrWitness
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
p2m_open_scoped "IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"
set_option maxHeartbeats 12800000 in

theorem gapsw79_t2_pieceIResidual_of_residueGenPrimitive
    (hResidueGenPrimitive :
      ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
        (hP : P ∈ IsDedekindDomain.primesOverFinset
          (Ideal.span {(3 : ℤ)}) (𝓞 K)),
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P →
        ∃ ξ : 𝓞 K, Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤ ∧
          ((algebraMap (𝓞 K)
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)
            ^ (Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
                ⧸ gapsw7X1mCompletionIdeal K P hP))
          - algebraMap (𝓞 K)
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ
          ∉ (gapsw7X1mCompletionIdeal K P hP) ^ 2) ∧
          Polynomial.rootMultiplicity
              (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)
                (algebraMap (𝓞 K)
                  ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ))
              ((minpoly ℤ ξ).map
                ((Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)).comp
                  (algebraMap ℤ
                    ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))))
            ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P) :
    Gapsw48T5CompletionTransportPieceIResidual := by
  have _em := Classical.em
  classical
  apply gapsw79_t1_pieceIResidual_of_localMonogenicResidueGen
  intro K _ _ P hP hwild
  obtain ⟨ξ, hadj, hfrob, hmu⟩ := hResidueGenPrimitive K P hP hwild
  refine ⟨ξ, hadj, ?_⟩
  intro A _ _ _ _ _ _ h3A hresA
  have hmono := gapsw79_t2_adjoin_top_of_frobFix_notin_sq K P hP hwild A h3A
    hresA ξ hfrob
  exact ⟨hmono,
    gapsw79_t2_isUnit_cofactor_of_residuePoly_nondvd K P hP hwild A h3A hresA
      ξ hmono hmu⟩
end FLT.Gapsw79T2CofactorUnitResidueReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T3ResidueCharpolyReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw79T1CofactorUnitOfResidueGenerator
open FLT.Gapsw79T2CofactorUnitResidueReduction
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"

theorem gapsw79_t3_completionResidue_ringHom_eq
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)).comp
        (algebraMap ℤ ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
      = Int.castRingHom (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ⧸ gapsw7X1mCompletionIdeal K P hP) :=
  RingHom.ext_int _ _
end FLT.Gapsw79T3ResidueCharpolyReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T3ResidueCharpolyReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw79T1CofactorUnitOfResidueGenerator
open FLT.Gapsw79T2CofactorUnitResidueReduction
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"

theorem gapsw79_t3_charP_completionResidue_three
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    CharP (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        ⧸ gapsw7X1mCompletionIdeal K P hP) 3 := by
  have _em := Classical.em
  set 𝔪 := gapsw7X1mCompletionIdeal K P hP with h𝔪
  set e := (Ideal.span {(3 : ℤ)}).ramificationIdx' P with heq
  have he0 : 0 < e :=
    Nat.pos_of_ne_zero (gapsw47_t5_p2_ramificationIdx_ne_zero K P hP)
  haveI h𝔪max : 𝔪.IsMaximal := by
    rw [h𝔪, gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP]
    exact IsLocalRing.maximalIdeal.isMaximal _

  obtain ⟨π, hπ⟩ := adicCompletion.exists_uniformizer K (gapsw7X1mPlace K P hP)
  have hπval : Valued.v (π : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-1 : ℤ) := hπ
  have hspan : Ideal.span {π} = 𝔪 := by
    rw [h𝔪, gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP,
      adicCompletion.maximalIdeal_eq_span_uniformizer K
        (gapsw7X1mPlace K P hP) hπval]
  have hval3 : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K)
      = WithZero.exp (-(e : ℤ)) := by
    rw [← map_ofNat (algebraMap (𝓞 K)
          ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)) 3,
      algebraMap_completionIntegers,
      (gapsw7X1mPlace K P hP).valuedAdicCompletion_eq_valuation,
      (gapsw7X1mPlace K P hP).valuation_of_algebraMap,
      gapsw54_t3_intValuation_three_eq_ramificationIdx K (gapsw7X1mPlace K P hP),
      gapsw7_x1m_place_asIdeal K P hP]
  have h3ne : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ≠ 0 := by
    intro h; rw [h, ZeroMemClass.coe_zero, map_zero] at hval3
    exact WithZero.exp_ne_zero hval3.symm
  obtain ⟨n, u0, hu⟩ := adicCompletion.eq_pow_uniformizer_mul_unit K
    (gapsw7X1mPlace K P hP) h3ne hπval
  have hvu : Valued.v ((u0 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        : (gapsw7X1mPlace K P hP).adicCompletion K) = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one _).mp u0.isUnit
  have hne : n = e := by
    have hun : Valued.v ((3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          : (gapsw7X1mPlace K P hP).adicCompletion K)
        = WithZero.exp (-(n : ℤ)) := by
      rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
        hπval, hvu, mul_one, ← WithZero.exp_nsmul, WithZero.exp_inj]; simp
    have h := hun.symm.trans hval3; rw [WithZero.exp_inj] at h; omega
  have h3mem : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K) ∈ 𝔪 := by
    have h3mem_e : (3 : (gapsw7X1mPlace K P hP).adicCompletionIntegers K)
        ∈ 𝔪 ^ e := by
      rw [← hspan, Ideal.span_singleton_pow, hu, hne]
      exact Ideal.mem_span_singleton.mpr ⟨u0, rfl⟩
    exact Ideal.pow_le_self he0.ne' h3mem_e

  haveI : Field (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪) :=
    Ideal.Quotient.field 𝔪
  have h3zero : (3 : ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪)
      = 0 := by
    rw [← map_ofNat (Ideal.Quotient.mk 𝔪) 3, Ideal.Quotient.eq_zero_iff_mem]
    exact h3mem
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h3zero
end FLT.Gapsw79T3ResidueCharpolyReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T3ResidueCharpolyReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw79T1CofactorUnitOfResidueGenerator
open FLT.Gapsw79T2CofactorUnitResidueReduction
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 19200000 in

theorem gapsw79_t3_rootMultiplicity_le_of_not_dvd_pow
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (ξ : 𝓞 K)
    (μ : ℤ[X]) (hμmon : μ.Monic)
    (hμirr : Irreducible (μ.map (Int.castRingHom (ZMod 3))))
    (hμroot : Polynomial.aeval
        (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)
          (algebraMap (𝓞 K)
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)) μ = 0)
    (hdvd : ¬ (μ.map (Int.castRingHom (ZMod 3))) ^
          ((Ideal.span {(3 : ℤ)}).ramificationIdx' P + 1)
        ∣ (minpoly ℤ ξ).map (Int.castRingHom (ZMod 3))) :
    Polynomial.rootMultiplicity
        (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)
          (algebraMap (𝓞 K)
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ))
        ((minpoly ℤ ξ).map
          ((Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)).comp
            (algebraMap ℤ
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))))
      ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P := by
  have _em := Classical.em
  classical

  set kP := ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ⧸ gapsw7X1mCompletionIdeal K P hP with hkP
  set ξPbar : kP := Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)
      (algebraMap (𝓞 K)
        ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ) with hξPbar
  set e := (Ideal.span {(3 : ℤ)}).ramificationIdx' P with heq
  set μ3 := μ.map (Int.castRingHom (ZMod 3)) with hμ3
  set g3 := (minpoly ℤ ξ).map (Int.castRingHom (ZMod 3)) with hg3

  haveI h𝔪max : (gapsw7X1mCompletionIdeal K P hP).IsMaximal := by
    rw [gapsw7_x1m_completionIdeal_eq_maximalIdeal K P hP]
    exact IsLocalRing.maximalIdeal.isMaximal _
  haveI hkPfield : Field kP := Ideal.Quotient.field (gapsw7X1mCompletionIdeal K P hP)
  haveI : CharP kP 3 := gapsw79_t3_charP_completionResidue_three K P hP
  letI : Algebra (ZMod 3) kP := ZMod.algebra kP 3
  set ι : ZMod 3 →+* kP := algebraMap (ZMod 3) kP with hι

  have hcomp : (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)).comp
        (algebraMap ℤ ((gapsw7X1mPlace K P hP).adicCompletionIntegers K))
      = ι.comp (Int.castRingHom (ZMod 3)) := by
    rw [gapsw79_t3_completionResidue_ringHom_eq K P hP]; exact RingHom.ext_int _ _

  have hgoal_poly : (minpoly ℤ ξ).map
        ((Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)).comp
          (algebraMap ℤ ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)))
      = g3.map ι := by
    rw [hcomp, ← Polynomial.map_map, hg3]
  rw [hgoal_poly]

  have hμroot' : (μ3.map ι).IsRoot ξPbar := by
    have hZkP : algebraMap ℤ kP
        = (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)).comp
          (algebraMap ℤ ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)) :=
      RingHom.ext_int _ _
    rw [Polynomial.aeval_def, hZkP] at hμroot
    show Polynomial.eval ξPbar (μ3.map ι) = 0
    rw [hμ3, Polynomial.map_map, ← hcomp, ← Polynomial.eval₂_eq_eval_map]
    exact hμroot

  have hμroot_aeval : Polynomial.aeval (R := ZMod 3) ξPbar μ3 = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← hι]; exact hμroot'

  have hmin_mon : (minpoly ℤ ξ).Monic := minpoly.monic (IsIntegral.of_finite ℤ ξ)
  have hg3mon : g3.Monic := hmin_mon.map _
  have hg3_ne : g3 ≠ 0 := hg3mon.ne_zero
  have hμ3mon : μ3.Monic := hμmon.map _
  have hg3map_ne : g3.map ι ≠ 0 := (hg3mon.map ι).ne_zero

  have hex : ∃ k, ¬ μ3 ^ (k + 1) ∣ g3 := ⟨e, hdvd⟩
  set m := Nat.find hex with hm
  have hm_ndvd : ¬ μ3 ^ (m + 1) ∣ g3 := Nat.find_spec hex
  have hme : m ≤ e := Nat.find_le hdvd
  have hm_dvd : μ3 ^ m ∣ g3 := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · simp [h0]
    · by_contra hc
      exact (Nat.find_min hex (Nat.sub_one_lt hpos.ne'))
        (by rwa [Nat.sub_add_cancel hpos])
  obtain ⟨r, hr⟩ := hm_dvd
  have hμ3_ndvd_r : ¬ μ3 ∣ r := fun ⟨s, hs⟩ =>
    hm_ndvd ⟨s, by rw [hr, hs, pow_succ]; ring⟩

  have hμ3sep : μ3.Separable := PerfectField.separable_of_irreducible hμirr

  have hrm_μ : rootMultiplicity ξPbar (μ3.map ι) = 1 :=
    le_antisymm (rootMultiplicity_le_one_of_separable hμ3sep.map ξPbar)
      ((rootMultiplicity_pos (hμ3mon.map ι).ne_zero).mpr hμroot')

  have hrm_r : rootMultiplicity ξPbar (r.map ι) = 0 := by
    refine rootMultiplicity_eq_zero (fun hroot => ?_)
    have hmin_eq : μ3 = minpoly (ZMod 3) ξPbar :=
      minpoly.eq_of_irreducible_of_monic hμirr hμroot_aeval hμ3mon
    have hrroot : Polynomial.aeval (R := ZMod 3) ξPbar r = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← hι]; exact hroot
    exact hμ3_ndvd_r (hmin_eq ▸ minpoly.dvd (ZMod 3) ξPbar hrroot)

  have hg3map : g3.map ι = (μ3.map ι) ^ m * (r.map ι) := by
    rw [hr, Polynomial.map_mul, Polynomial.map_pow]
  rw [hg3map, rootMultiplicity_mul (hg3map ▸ hg3map_ne), hrm_r, add_zero,
    ← count_roots, roots_pow, Multiset.count_nsmul, count_roots, hrm_μ, mul_one]
  exact hme
end FLT.Gapsw79T3ResidueCharpolyReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T3ResidueCharpolyReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw79T1CofactorUnitOfResidueGenerator
open FLT.Gapsw79T2CofactorUnitResidueReduction
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw7X4gCompletionInstanceRow
open FLT.Gapsw70T3SpineBResidualSurfaceFire
open FLT.Gapsw58T2DvrBaseResidueSurjectivityReduction
open FLT.Gapsw54T3WildCompletionDvrWitness
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
open FLT.Gapsw47T5WildDifferentLink2bMonogenicEngine
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial"
set_option maxHeartbeats 12800000 in

theorem gapsw79_t3_pieceIResidual_of_residueDvdZMod3
    (hResidueDvdZMod3 :
      ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
        (hP : P ∈ IsDedekindDomain.primesOverFinset
          (Ideal.span {(3 : ℤ)}) (𝓞 K)),
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P →
        ∃ ξ : 𝓞 K, Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤ ∧
          ((algebraMap (𝓞 K)
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)
            ^ (Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
                ⧸ gapsw7X1mCompletionIdeal K P hP))
          - algebraMap (𝓞 K)
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ
          ∉ (gapsw7X1mCompletionIdeal K P hP) ^ 2) ∧
          ∃ μ : ℤ[X], μ.Monic ∧
            Irreducible (μ.map (Int.castRingHom (ZMod 3))) ∧
            Polynomial.aeval
              (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)
                (algebraMap (𝓞 K)
                  ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)) μ
              = 0 ∧
            ¬ (μ.map (Int.castRingHom (ZMod 3))) ^
                ((Ideal.span {(3 : ℤ)}).ramificationIdx' P + 1)
              ∣ (minpoly ℤ ξ).map (Int.castRingHom (ZMod 3))) :
    Gapsw48T5CompletionTransportPieceIResidual := by
  have _em := Classical.em
  classical
  apply gapsw79_t2_pieceIResidual_of_residueGenPrimitive
  intro K _ _ P hP hwild
  obtain ⟨ξ, hadj, hfrob, μ, hμmon, hμirr, hμroot, hdvd⟩ :=
    hResidueDvdZMod3 K P hP hwild
  exact ⟨ξ, hadj, hfrob,
    gapsw79_t3_rootMultiplicity_le_of_not_dvd_pow K P hP ξ μ hμmon
      hμirr hμroot hdvd⟩
end FLT.Gapsw79T3ResidueCharpolyReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T4CharpolyResidueSepReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw79T3ResidueCharpolyReduction
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial LinearMap P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.LinearMap"
p2m_open_scoped "TensorProduct P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.TensorProduct"

theorem gapsw79_t4_minpoly_eq_charpoly_lmul
    (K : Type) [Field K] [NumberField K] (ξ : 𝓞 K)
    (hadj : Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤) :
    minpoly ℤ ξ = LinearMap.charpoly (Algebra.lmul ℤ (𝓞 K) ξ) := by
  have _em := Classical.em
  classical
  set cp := LinearMap.charpoly (Algebra.lmul ℤ (𝓞 K) ξ) with hcp

  have hint : IsIntegral ℤ ξ := IsIntegral.of_finite ℤ ξ

  have hcp_ann : Polynomial.aeval ξ cp = 0 := Algebra.aeval_self_charpoly_lmul ξ

  have hdvd : minpoly ℤ ξ ∣ cp := minpoly.isIntegrallyClosed_dvd hint hcp_ann

  have hmin_mon : (minpoly ℤ ξ).Monic := minpoly.monic hint
  have hcp_mon : cp.Monic := LinearMap.charpoly_monic _

  have hcp_deg : cp.natDegree = Module.finrank ℚ K := by
    rw [hcp, LinearMap.charpoly_natDegree, NumberField.RingOfIntegers.rank]

  set ξK : K := algebraMap (𝓞 K) K ξ with hξK
  have hintQ : IsIntegral ℚ ξK := Algebra.IsIntegral.isIntegral ξK
  have hrank_eq : Module.finrank ℚ K = (minpoly ℚ ξK).natDegree := by
    let pb : PowerBasis ℚ K :=
      (Algebra.adjoin.powerBasis hintQ).map
        ((Subalgebra.equivOfEq _ _ hadj).trans Subalgebra.topEquiv)
    have hdim : pb.dim = (minpoly ℚ ξK).natDegree := by
      simp only [pb, PowerBasis.map_dim, Algebra.adjoin.powerBasis_dim]
    rw [← hdim, pb.finrank]

  have hmin_annQ : Polynomial.aeval ξK ((minpoly ℤ ξ).map (algebraMap ℤ ℚ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, hξK,
      show algebraMap (𝓞 K) K ξ = IsScalarTower.toAlgHom ℤ (𝓞 K) K ξ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdeg_le : (minpoly ℚ ξK).natDegree ≤ (minpoly ℤ ξ).natDegree := by
    have hmap_mon : ((minpoly ℤ ξ).map (algebraMap ℤ ℚ)).Monic := hmin_mon.map _
    calc (minpoly ℚ ξK).natDegree
        ≤ ((minpoly ℤ ξ).map (algebraMap ℤ ℚ)).natDegree :=
          Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ ξK hmin_annQ) hmap_mon.ne_zero
      _ = (minpoly ℤ ξ).natDegree := hmin_mon.natDegree_map (algebraMap ℤ ℚ)

  have hge : cp.natDegree ≤ (minpoly ℤ ξ).natDegree :=
    hcp_deg ▸ hrank_eq ▸ hdeg_le

  obtain ⟨r, hr⟩ := hdvd
  have hr_mon : r.Monic := (Polynomial.Monic.of_mul_monic_left hmin_mon (hr ▸ hcp_mon))
  have hr_deg : r.natDegree = 0 := by
    have h1 : ((minpoly ℤ ξ) * r).natDegree ≤ (minpoly ℤ ξ).natDegree := hr ▸ hge
    rw [hmin_mon.natDegree_mul hr_mon] at h1; omega
  rw [hr, hr_mon.natDegree_eq_zero.mp hr_deg, mul_one]
end FLT.Gapsw79T4CharpolyResidueSepReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T4CharpolyResidueSepReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw79T3ResidueCharpolyReduction
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial LinearMap P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.LinearMap"
p2m_open_scoped "TensorProduct P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.TensorProduct"

theorem gapsw79_t4_isUnit_aeval_of_not_dvd_charpoly
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Module.Free k V]
    (T : V →ₗ[k] V) (p : k[X]) (hp_nu : ¬ IsUnit p)
    (hU : IsUnit (Polynomial.aeval T p)) :
    ¬ p ∣ LinearMap.charpoly T := by
  have _em := Classical.em
  classical
  intro hdvd

  have hp0 : p ≠ 0 := by
    rintro rfl; exact (LinearMap.charpoly_monic T).ne_zero (zero_dvd_iff.mp hdvd)

  let L := AlgebraicClosure k
  let TL : Module.End L (L ⊗[k] V) := T.baseChange L

  have hcpL : TL.charpoly = (LinearMap.charpoly T).map (algebraMap k L) :=
    LinearMap.charpoly_baseChange T L

  have hdegpos : (p.map (algebraMap k L)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro h
    exact hp_nu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (p.map (algebraMap k L)) hdegpos

  have hζcp : (TL.charpoly).IsRoot ζ := by
    rw [hcpL]
    exact Polynomial.IsRoot.dvd hζ (Polynomial.map_dvd _ hdvd)

  have hev : TL.HasEigenvalue ζ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly TL ζ).mpr hζcp
  obtain ⟨v, hvmem, hvne⟩ := hev.exists_hasEigenvector

  have heval : (Polynomial.aeval TL (p.map (algebraMap k L))) v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector ⟨hvmem, hvne⟩,
      Polynomial.IsRoot.def.mp hζ, zero_smul]

  have haeval_eq : Polynomial.aeval TL (p.map (algebraMap k L))
      = (Polynomial.aeval T p).baseChange L := by
    rw [Polynomial.aeval_map_algebraMap]
    exact Polynomial.aeval_algHom_apply (Module.End.baseChangeHom k L V) T p

  have hinj : Function.Injective ((Polynomial.aeval T p).baseChange L) := by
    have hdet : IsUnit (LinearMap.det ((Polynomial.aeval T p).baseChange L)) := by
      rw [LinearMap.det_baseChange]
      exact ((LinearMap.isUnit_iff_isUnit_det _).mp hU).map (algebraMap k L)
    exact LinearMap.ker_eq_bot.mp
      ((LinearMap.isUnit_iff_ker_eq_bot _).mp
        ((LinearMap.isUnit_iff_isUnit_det _).mpr hdet))

  exact hvne (hinj (by rw [← haeval_eq, heval, map_zero]))
end FLT.Gapsw79T4CharpolyResidueSepReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T4CharpolyResidueSepReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw79T3ResidueCharpolyReduction
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial LinearMap P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.LinearMap"
p2m_open_scoped "TensorProduct P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.TensorProduct"
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
set_option maxHeartbeats 19200000 in

theorem gapsw79_t4_not_dvd_minpoly_map_of_residueSep
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (ξ : 𝓞 K)
    (hadj : Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤)
    (μ : ℤ[X]) (hμmon : μ.Monic)
    (hμirr : Irreducible (μ.map (Int.castRingHom (ZMod 3))))
    (ha' : (μ.map (Int.castRingHom (ZMod 3))).natDegree
      = (Ideal.span {(3 : ℤ)}).inertiaDeg' P)
    (hd : ∀ Q ∈ IsDedekindDomain.primesOverFinset
        (Ideal.span {(3 : ℤ)}) (𝓞 K), Q ≠ P →
      Polynomial.aeval (Ideal.Quotient.mk Q ξ) μ ≠ 0) :
    ¬ (μ.map (Int.castRingHom (ZMod 3))) ^
          ((Ideal.span {(3 : ℤ)}).ramificationIdx' P + 1)
        ∣ (minpoly ℤ ξ).map (Int.castRingHom (ZMod 3)) := by
  have _em := Classical.em
  classical

  set p3 := Ideal.span {(3 : ℤ)} with hp3
  set e := p3.ramificationIdx' P with heeq
  set fP := p3.inertiaDeg' P with hfPeq
  haveI hp3ne : p3 ≠ ⊥ := by
    rw [hp3, Ne, Ideal.span_singleton_eq_bot]; norm_num
  haveI hp3max : p3.IsMaximal := by
    rw [hp3]; exact PrincipalIdealRing.isMaximal_of_irreducible Int.prime_three.irreducible
  set F := ℤ ⧸ p3 with hF
  letI : Field F := Ideal.Quotient.field p3
  let πF : ℤ →+* F := algebraMap ℤ F

  have hspan3 : p3 = Ideal.span {((3 : ℕ) : ℤ)} := by rw [hp3]; norm_num
  let σ : F ≃+* ZMod 3 :=
    (Ideal.quotEquivOfEq hspan3).trans (Int.quotientSpanNatEquivZMod 3)
  have hσcomp : (σ : F →+* ZMod 3).comp πF = Int.castRingHom (ZMod 3) :=
    RingHom.ext_int _ _

  set μF : F[X] := μ.map πF with hμF
  set gF : F[X] := (minpoly ℤ ξ).map πF with hgF
  intro hcontra
  have hcontraF : μF ^ (e + 1) ∣ gF := by
    have hmap : (μF ^ (e + 1)).map (σ : F →+* ZMod 3) ∣ gF.map (σ : F →+* ZMod 3) := by
      have h1 : gF.map (σ : F →+* ZMod 3)
          = (minpoly ℤ ξ).map (Int.castRingHom (ZMod 3)) := by
        rw [hgF, Polynomial.map_map, hσcomp]
      have h2 : (μF ^ (e + 1)).map (σ : F →+* ZMod 3)
          = (μ.map (Int.castRingHom (ZMod 3))) ^ (e + 1) := by
        rw [Polynomial.map_pow, hμF, Polynomial.map_map, hσcomp]
      rw [h1, h2]; exact hcontra
    exact (Polynomial.map_dvd_map _ σ.injective
      ((hμmon.map πF).pow (n := e + 1))).mp hmap

  have hμFmon : μF.Monic := hμmon.map πF
  have hμFmap : μF.map (σ : F →+* ZMod 3) = μ.map (Int.castRingHom (ZMod 3)) := by
    rw [hμF, Polynomial.map_map, hσcomp]
  have hμFirr : Irreducible μF := by
    have hirr' : Irreducible (Polynomial.mapEquiv σ μF) := by
      show Irreducible (μF.map (σ : F →+* ZMod 3)); rw [hμFmap]; exact hμirr
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv σ)).mp hirr'
  have hμFdeg : μF.natDegree = fP := by
    rw [hμF, hμmon.natDegree_map, ← ha', hμmon.natDegree_map]

  let V := F ⊗[ℤ] (𝓞 K)
  let bV : Module.Basis _ F V := (Module.Free.chooseBasis ℤ (𝓞 K)).baseChange F
  haveI : Module.Finite F V := Module.Finite.of_basis bV
  haveI : Module.Free F V := Module.Free.of_basis bV
  letI : CommRing V := Algebra.TensorProduct.instCommRing
  letI : Algebra F V := Algebra.TensorProduct.leftAlgebra
  let T : Module.End F V := (Algebra.lmul ℤ (𝓞 K) ξ).baseChange F
  have hgFcp : gF = LinearMap.charpoly T := by
    rw [hgF, gapsw79_t4_minpoly_eq_charpoly_lmul K ξ hadj]
    exact (LinearMap.charpoly_baseChange (Algebra.lmul ℤ (𝓞 K) ξ) F).symm

  set I3 := p3.map (algebraMap ℤ (𝓞 K)) with hI3
  have hI3ne : I3 ≠ ⊥ := by
    rw [hI3, Ne, Ideal.map_eq_bot_iff_of_injective (algebraMap ℤ (𝓞 K)).injective_int]
    exact hp3ne
  let 𝒮 := (UniqueFactorizationMonoid.factors I3).toFinset

  have h𝒮iff : ∀ Q : Ideal (𝓞 K),
      Q ∈ 𝒮 ↔ Q ∈ IsDedekindDomain.primesOverFinset p3 (𝓞 K) := fun Q => by
    rw [Multiset.mem_toFinset, UniqueFactorizationMonoid.factors_eq_normalizedFactors]
  have hPmem : P ∈ 𝒮 := (h𝒮iff P).mpr hP
  let Pf : 𝒮 := ⟨P, hPmem⟩
  haveI hPliesOver : P.LiesOver p3 := Ideal.Factors.liesOver p3 Pf
  have hQprimesOver : ∀ Q : 𝒮, (Q : Ideal (𝓞 K))
      ∈ IsDedekindDomain.primesOverFinset p3 (𝓞 K) := fun Q => (h𝒮iff Q).mp Q.2

  let ε1 : (𝓞 K ⧸ I3) ≃ₐ[F] V :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor (𝓞 K) p3

  let εR : V ≃+*
      (∀ Q : 𝒮, (𝓞 K) ⧸ (Q : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1) :=
    ε1.symm.toRingEquiv.trans (Ideal.Factors.piQuotientEquiv p3 hI3ne)
  let εL : V ≃ₗ[F]
      (∀ Q : 𝒮, (𝓞 K) ⧸ (Q : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1) :=
    { εR with
      map_smul' := fun c v => by
        exact (ε1.symm.toLinearEquiv.trans
          (Ideal.Factors.piQuotientLinearEquiv (𝓞 K) p3 hI3ne)).map_smul c v }

  have hεξ : εR (1 ⊗ₜ ξ) = fun Q => Ideal.Quotient.mk _ ξ := by
    have h1 : ε1.symm (1 ⊗ₜ[ℤ] ξ) = Ideal.Quotient.mk I3 ξ :=
      ε1.symm_apply_eq.mpr
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk (𝓞 K) p3 ξ).symm
    show (Ideal.Factors.piQuotientEquiv p3 hI3ne) (ε1.symm (1 ⊗ₜ[ℤ] ξ)) = _
    rw [h1]; exact Ideal.Factors.piQuotientEquiv_mk p3 hI3ne ξ

  have hTlmul : T = Algebra.lmul F V (1 ⊗ₜ[ℤ] ξ) := by
    refine LinearMap.ext (fun v => ?_)
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
        show a ⊗ₜ[ℤ] (ξ * m) = (1 ⊗ₜ[ℤ] ξ) * (a ⊗ₜ[ℤ] m)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add x y hx hy => simp [map_add, hx, hy]

  let Tpi : Module.End F
      (∀ Q : 𝒮, (𝓞 K) ⧸ (Q : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1) :=
    LinearMap.pi (fun Q => (Algebra.lmul F _ (Ideal.Quotient.mk _ ξ)).comp
      (LinearMap.proj Q))
  have hTconj : εL.conj T = Tpi := by
    refine LinearMap.ext (fun v => funext (fun Q => ?_))
    have h1 : (εL.conj T) v = εR ((1 ⊗ₜ[ℤ] ξ) * (εR.symm v)) := by
      show εR (T (εR.symm v)) = _
      rw [hTlmul]; rfl
    rw [h1, map_mul, RingEquiv.apply_symm_apply, hεξ]
    rfl

  haveI hWfin : ∀ Q : 𝒮, Module.Finite F
      ((𝓞 K) ⧸ (Q : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1) :=
    fun Q => Ideal.Factors.finiteDimensional_quotient_pow p3 Q
  haveI hWfree : ∀ Q : 𝒮, Module.Free F
      ((𝓞 K) ⧸ (Q : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1) :=
    fun Q => Module.Free.of_divisionRing F _

  let W_P := (𝓞 K) ⧸ P ^ e
  haveI hWPfin : Module.Finite F W_P := hWfin Pf
  haveI hWPfree : Module.Free F W_P := hWfree Pf
  let T_P : Module.End F W_P := Algebra.lmul F W_P (Ideal.Quotient.mk _ ξ)
  let W_J := ∀ Q : {Q : 𝒮 // Q ≠ Pf},
    (𝓞 K) ⧸ (Q.1 : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1.1
  haveI hWJfin : Module.Finite F W_J := inferInstance
  haveI hWJfree : Module.Free F W_J := inferInstance
  let T_J : Module.End F W_J :=
    LinearMap.pi (fun Q => (Algebra.lmul F _ (Ideal.Quotient.mk _ ξ)).comp
      (LinearMap.proj Q))

  let ε3 : (∀ Q : 𝒮, (𝓞 K) ⧸ (Q : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1)
      ≃ₗ[F] W_P × W_J :=
    { toFun := fun w => (w Pf, fun Q => w Q.1)
      invFun := fun ⟨a, b⟩ Q => if h : Q = Pf then h ▸ a else b ⟨Q, h⟩
      left_inv := fun w => funext (fun Q => by
        by_cases h : Q = Pf
        · subst h; simp
        · simp [h])
      right_inv := fun ⟨a, b⟩ => by
        refine Prod.ext (by simp) ?_
        refine funext (fun Q => ?_); simp [Q.2]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hε3conj : ε3.conj Tpi = T_P.prodMap T_J := by
    refine LinearMap.ext (fun ⟨a, b⟩ => Prod.ext ?_ (funext (fun Q => ?_)))
    · show Algebra.lmul F _ (Ideal.Quotient.mk _ ξ) (ε3.symm (a, b) Pf) = T_P a
      have : ε3.symm (a, b) Pf = a := dif_pos rfl
      rw [this]
    · show Algebra.lmul F _ (Ideal.Quotient.mk _ ξ) (ε3.symm (a, b) Q.1)
        = Algebra.lmul F _ (Ideal.Quotient.mk _ ξ) (b Q)
      have : ε3.symm (a, b) Q.1 = b Q := dif_neg Q.2
      rw [this]
  have hcp_split : gF = (LinearMap.charpoly T_P) * (LinearMap.charpoly T_J) := by
    rw [hgFcp, ← εL.charpoly_conj T, hTconj, ← ε3.charpoly_conj Tpi, hε3conj,
      LinearMap.charpoly_prodMap]

  have h2a : ¬ μF ∣ LinearMap.charpoly T_J := by
    refine gapsw79_t4_isUnit_aeval_of_not_dvd_charpoly T_J μF hμFirr.not_isUnit ?_

    have hunit_Q : ∀ Q : {Q : 𝒮 // Q ≠ Pf},
        IsUnit (Polynomial.aeval
          (Ideal.Quotient.mk ((Q.1 : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1.1) ξ) μ) := by
      intro Q
      haveI hQmax : (Q.1 : Ideal (𝓞 K)).IsMaximal :=
        Ideal.IsPrime.isMaximal (Ideal.Factors.isPrime p3 Q.1)
          (Ideal.Factors.ne_bot p3 Q.1)
      have hQneP : (Q.1 : Ideal (𝓞 K)) ≠ P := fun h =>
        Q.2 (Subtype.ext h)

      have hnotin : Polynomial.aeval ξ μ ∉ (Q.1 : Ideal (𝓞 K)) := by
        intro hin
        refine hd Q.1 (hQprimesOver Q.1) hQneP ?_
        rw [show Ideal.Quotient.mk (Q.1 : Ideal (𝓞 K)) ξ
            = Ideal.Quotient.mkₐ ℤ (Q.1 : Ideal (𝓞 K)) ξ from rfl,
          Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem]
        exact hin

      have heQ : p3.ramificationIdx' Q.1.1 ≠ 0 :=
        Ideal.Factors.ramificationIdx_ne_zero p3 Q.1
      letI : Field ((𝓞 K) ⧸ (Q.1 : Ideal (𝓞 K))) := Ideal.Quotient.field _
      have hne0 : Ideal.Quotient.mk (Q.1 : Ideal (𝓞 K)) (Polynomial.aeval ξ μ) ≠ 0 :=
        fun h => hnotin (Ideal.Quotient.eq_zero_iff_mem.mp h)
      rw [show Ideal.Quotient.mk _ ξ = Ideal.Quotient.mkₐ ℤ
            ((Q.1 : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1.1) ξ from rfl,
        Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk _ heQ]
      exact IsUnit.mk0 _ hne0

    let cJ : W_J := fun Q => Ideal.Quotient.mk _ ξ
    have hTJ_lmul : T_J = Algebra.lmul F W_J cJ := by
      refine LinearMap.ext (fun w => funext (fun Q => ?_))
      show Algebra.lmul F _ (Ideal.Quotient.mk _ ξ) (w Q) = (cJ * w) Q
      rfl
    have hunit_cJ : IsUnit (Polynomial.aeval cJ μF) := by
      refine Pi.isUnit_iff.mpr (fun Q => ?_)
      have h1 : Polynomial.aeval cJ μF Q = Polynomial.aeval (cJ Q) μF := by
        have key := Polynomial.aeval_algHom_apply (Pi.evalAlgHom F _ Q) cJ μF
        exact key.symm

      have hcomp : (algebraMap F ((𝓞 K) ⧸
            (Q.1 : Ideal (𝓞 K)) ^ p3.ramificationIdx' Q.1.1)).comp πF
          = algebraMap ℤ _ := rfl
      rw [h1, hμF, Polynomial.aeval_def, Polynomial.eval₂_map, hcomp,
        ← Polynomial.aeval_def]
      exact hunit_Q Q
    rw [hTJ_lmul, Polynomial.aeval_algHom_apply (Algebra.lmul F W_J) cJ μF]
    exact hunit_cJ.map (Algebra.lmul F W_J)

  have hdegP : (LinearMap.charpoly T_P).natDegree = e * fP := by

    rw [LinearMap.charpoly_natDegree]
    exact Ideal.Factors.finrank_pow_ramificationIdx p3 Pf
  have hfP0 : 0 < fP := Ideal.inertiaDeg'_pos p3 P
  have h2b : ¬ μF ^ (e + 1) ∣ LinearMap.charpoly T_P := by
    intro hdvd
    have hdeg : (μF ^ (e + 1)).natDegree ≤ (LinearMap.charpoly T_P).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd (LinearMap.charpoly_monic T_P).ne_zero
    have hle : e * fP + fP ≤ e * fP := by
      calc e * fP + fP = (e + 1) * fP := by ring
        _ = (μF ^ (e + 1)).natDegree := by rw [Polynomial.natDegree_pow, hμFdeg]
        _ ≤ (LinearMap.charpoly T_P).natDegree := hdeg
        _ = e * fP := hdegP
    omega

  have hcoprime : IsCoprime μF (LinearMap.charpoly T_J) :=
    (hμFirr.coprime_iff_not_dvd).mpr h2a
  have hcoprime' : IsCoprime (μF ^ (e + 1)) (LinearMap.charpoly T_J) :=
    hcoprime.pow_left
  have hdvdP : μF ^ (e + 1) ∣ LinearMap.charpoly T_P :=
    hcoprime'.dvd_of_dvd_mul_right (hcp_split ▸ hcontraF)
  exact h2b hdvdP
end FLT.Gapsw79T4CharpolyResidueSepReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace FLT
namespace Gapsw79T4CharpolyResidueSepReduction
p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw79T3ResidueCharpolyReduction
open FLT.Gapsw7X1mCompletionCarrier
open FLT.Gapsw47T5WildDifferentLink2bGlobalisation
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial LinearMap P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.LinearMap"
p2m_open_scoped "TensorProduct P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.TensorProduct"
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
set_option maxHeartbeats 12800000 in

theorem gapsw79_t4_pieceIResidual_of_residueSepGen
    (hResidueSepGen :
      ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
        (hP : P ∈ IsDedekindDomain.primesOverFinset
          (Ideal.span {(3 : ℤ)}) (𝓞 K)),
        3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P →
        ∃ ξ : 𝓞 K, Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤ ∧
          ((algebraMap (𝓞 K)
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)
            ^ (Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
                ⧸ gapsw7X1mCompletionIdeal K P hP))
          - algebraMap (𝓞 K)
              ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ
          ∉ (gapsw7X1mCompletionIdeal K P hP) ^ 2) ∧
          ∃ μ : ℤ[X], μ.Monic ∧
            Irreducible (μ.map (Int.castRingHom (ZMod 3))) ∧
            Polynomial.aeval
              (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)
                (algebraMap (𝓞 K)
                  ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)) μ
              = 0 ∧
            (μ.map (Int.castRingHom (ZMod 3))).natDegree
              = (Ideal.span {(3 : ℤ)}).inertiaDeg' P ∧
            ∀ Q ∈ IsDedekindDomain.primesOverFinset
                (Ideal.span {(3 : ℤ)}) (𝓞 K), Q ≠ P →
              Polynomial.aeval (Ideal.Quotient.mk Q ξ) μ ≠ 0) :
    Gapsw48T5CompletionTransportPieceIResidual := by
  have _em := Classical.em
  classical
  apply gapsw79_t3_pieceIResidual_of_residueDvdZMod3
  intro K _ _ P hP hwild
  obtain ⟨ξ, hadj, hfrob, μ, hμmon, hμirr, hμroot, ha', hd⟩ :=
    hResidueSepGen K P hP hwild
  exact ⟨ξ, hadj, hfrob, μ, hμmon, hμirr, hμroot,
    gapsw79_t4_not_dvd_minpoly_map_of_residueSep K P hP ξ hadj μ hμmon hμirr ha' hd⟩
end FLT.Gapsw79T4CharpolyResidueSepReduction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

section

set_option maxHeartbeats 3200000

namespace FLT
namespace Gapsw79T5ResidueSepGenConstruction

p2m_open_scoped "NumberField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_open "IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum"
open FLT.Gapsw48T5CompletionTransportCarrierSlices
open FLT.Gapsw79T4CharpolyResidueSepReduction
open FLT.Gapsw79T2CofactorUnitResidueReduction
open FLT.Gapsw78T9GlobalPrimitiveDerivWire
open FLT.Gapsw7X1mCompletionCarrier
p2m_open "Polynomial P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.Polynomial IntermediateField P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IntermediateField"

theorem gapsw79_t5_mem_completionIdeal_pow_iff_mem_pow
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) (x : 𝓞 K) (n : ℕ) :
    algebraMap (𝓞 K) ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) x
      ∈ (gapsw7X1mCompletionIdeal K P hP) ^ n
    ↔ x ∈ P ^ n := by
  have _em := Classical.em
  set v := gapsw7X1mPlace K P hP with hv
  show algebraMap (𝓞 K) (v.adicCompletionIntegers K) x ∈ (v.completionIdeal K) ^ n
    ↔ x ∈ P ^ n
  rw [adicCompletion.mem_completionIdeal_pow K v,
    algebraMap_completionIntegers, v.valuedAdicCompletion_eq_valuation,
    v.valuation_of_algebraMap]
  show v.intValuation x ≤ WithZero.exp (-(n : ℤ)) ↔ x ∈ P ^ n
  rw [v.intValuation_le_pow_iff_mem,
    show v.asIdeal = P from gapsw7_x1m_place_asIdeal K P hP]

theorem gapsw79_t5_exists_nonroot_of_irreducible_mod_three
    (L : Type*) [CommRing L] [Nontrivial L] [CharP L 3]
    (μ : ℤ[X]) (hμirr : Irreducible (μ.map (Int.castRingHom (ZMod 3)))) :
    ∃ c : L, Polynomial.aeval c μ ≠ 0 := by
  have _em := Classical.em
  classical
  set μ3 := μ.map (Int.castRingHom (ZMod 3)) with hμ3
  let ι : ZMod 3 →+* L := ZMod.castHom dvd_rfl L
  have hι_inj : Function.Injective ι := ι.injective
  have hfac : (Int.castRingHom L) = ι.comp (Int.castRingHom (ZMod 3)) :=
    RingHom.ext_int _ _
  have haeval : ∀ c : L, Polynomial.aeval c μ = eval₂ ι c μ3 := by
    intro c
    rw [Polynomial.aeval_def, algebraMap_int_eq, hfac, hμ3, ← eval₂_map]
  rcases eq_or_ne (μ3.coeff 0) 0 with h0 | h0
  ·
    have hXdvd : X ∣ μ3 := Polynomial.X_dvd_iff.mpr h0
    obtain ⟨r, hr⟩ := hXdvd
    have hru : IsUnit r := (hμirr.isUnit_or_isUnit hr).resolve_left
      Polynomial.not_isUnit_X
    obtain ⟨u, hu, hr'⟩ := Polynomial.isUnit_iff.mp hru
    refine ⟨1, ?_⟩
    rw [haeval, hr, ← hr', eval₂_mul, eval₂_X, eval₂_C, one_mul]
    exact fun h => hu.ne_zero (hι_inj (h.trans (_root_.map_zero ι).symm))
  ·
    refine ⟨0, ?_⟩
    rw [haeval, eval₂_at_zero]
    exact fun h => h0 (hι_inj (h.trans (_root_.map_zero ι).symm))

theorem gapsw79_t5_exists_monic_int_lift (p : (ZMod 3)[X]) (hp : p.Monic) :
    ∃ μ : ℤ[X], μ.Monic ∧ μ.map (Int.castRingHom (ZMod 3)) = p := by
  have _em := Classical.em
  have hsurj : Function.Surjective (Int.castRingHom (ZMod 3)) :=
    ZMod.ringHom_surjective _
  have hl : p ∈ Polynomial.lifts (Int.castRingHom (ZMod 3)) := by
    rw [Polynomial.mem_lifts]
    exact ⟨(Polynomial.map_surjective _ hsurj p).choose,
      (Polynomial.map_surjective _ hsurj p).choose_spec⟩
  obtain ⟨μ, hμmap, _, hμmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hp
  exact ⟨μ, hμmon, hμmap⟩

set_option maxHeartbeats 6400000 in

theorem gapsw79_t5_exists_primitive_in_nine_coset
    (K : Type) [Field K] [NumberField K] (α γ : K)
    (hγ : Algebra.adjoin ℚ {γ} = ⊤) :
    ∃ N : ℤ, Algebra.adjoin ℚ {α + (9 * N : ℤ) • γ} = ⊤ := by
  have _em := Classical.em
  classical
  set A := AlgebraicClosure ℚ with hA
  have hsplits : ∀ x : K, ((minpoly ℚ x).map (algebraMap ℚ A)).Splits :=
    fun x => IsAlgClosed.splits _

  have hconv : ∀ x : K, Algebra.adjoin ℚ {x} = ⊤ ↔ ℚ⟮x⟯ = ⊤ := by
    intro x
    have hxalg : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxalg]
    exact ⟨fun h => IntermediateField.toSubalgebra_injective
        (by rw [h, IntermediateField.top_toSubalgebra]),
      fun h => by rw [h, IntermediateField.top_toSubalgebra]⟩

  have hγ' : ℚ⟮γ⟯ = (⊤ : IntermediateField ℚ K) := (hconv γ).mp hγ
  have hγ_inj : Function.Injective (fun φ : K →ₐ[ℚ] A => φ γ) :=
    (Field.primitive_element_iff_algHom_eq_of_eval' ℚ A hsplits γ).mp hγ'
  haveI : Fintype (K →ₐ[ℚ] A) := minpoly.AlgHom.fintype ℚ K A

  let bad : Finset A :=
    (Finset.univ.offDiag : Finset ((K →ₐ[ℚ] A) × (K →ₐ[ℚ] A))).image
      (fun p => (p.1 α - p.2 α) / (p.2 γ - p.1 γ))

  have h9inj : Function.Injective (fun N : ℤ => ((9 * N : ℤ) : A)) := by
    intro m n hmn
    have h1 : ((9 * m : ℤ) : A) = ((9 * n : ℤ) : A) := hmn
    rw [Int.cast_inj] at h1; omega
  have hbadfin : (bad : Set A).Finite := bad.finite_toSet
  have h9inf : Set.Infinite (Set.range (fun N : ℤ => ((9 * N : ℤ) : A))) :=
    Set.infinite_range_of_injective h9inj
  obtain ⟨a, ha_rng, ha_bad⟩ := Set.Infinite.exists_notMem_finset h9inf bad
  obtain ⟨N, hN⟩ := ha_rng

  refine ⟨N, (hconv _).mpr ?_⟩
  rw [Field.primitive_element_iff_algHom_eq_of_eval' ℚ A hsplits]

  intro φ ψ hθeq
  by_contra hφψ

  have hγne : φ γ ≠ ψ γ := fun h => hφψ (hγ_inj h)

  have hsmul : ∀ χ : K →ₐ[ℚ] A, χ ((9 * N : ℤ) • γ) = ((9 * N : ℤ) : A) * χ γ := by
    intro χ
    rw [zsmul_eq_mul, map_mul, map_intCast]
  have hθeq' : φ α + ((9 * N : ℤ) : A) * φ γ = ψ α + ((9 * N : ℤ) : A) * ψ γ := by
    have h1 : φ (α + (9 * N : ℤ) • γ) = ψ (α + (9 * N : ℤ) • γ) := hθeq
    rwa [map_add, map_add, hsmul, hsmul] at h1
  have hkey : ((9 * N : ℤ) : A) = (φ α - ψ α) / (ψ γ - φ γ) := by
    have hdenom : ψ γ - φ γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγne)
    rw [eq_div_iff hdenom, mul_sub]; linear_combination -hθeq'
  have : ((9 * N : ℤ) : A) ∈ bad := by
    rw [hkey]
    exact Finset.mem_image.mpr ⟨(φ, ψ), Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, hφψ⟩, rfl⟩
  exact ha_bad (hN ▸ this)

set_option maxHeartbeats 6400000 in

theorem gapsw79_t5_exists_residue_minpoly
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K)) :
    ∃ (β : 𝓞 K) (μ : ℤ[X]), μ.Monic ∧
      Irreducible (μ.map (Int.castRingHom (ZMod 3))) ∧
      Polynomial.aeval (Ideal.Quotient.mk P β) μ = 0 ∧
      (μ.map (Int.castRingHom (ZMod 3))).natDegree
        = (Ideal.span {(3 : ℤ)}).inertiaDeg' P := by
  have _em := Classical.em
  classical

  set p3 := Ideal.span {(3 : ℤ)} with hp3
  haveI hp3max : p3.IsMaximal := by
    rw [hp3]; exact PrincipalIdealRing.isMaximal_of_irreducible
      Int.prime_three.irreducible
  set F := ℤ ⧸ p3 with hF
  letI : Field F := Ideal.Quotient.field p3
  let πF : ℤ →+* F := algebraMap ℤ F
  have hspan3 : p3 = Ideal.span {((3 : ℕ) : ℤ)} := by rw [hp3]; norm_num
  let σ : F ≃+* ZMod 3 :=
    (Ideal.quotEquivOfEq hspan3).trans (Int.quotientSpanNatEquivZMod 3)
  have hσcomp : (σ : F →+* ZMod 3).comp πF = Int.castRingHom (ZMod 3) :=
    RingHom.ext_int _ _

  obtain ⟨hPpr, hPlo, hPne⟩ := gapsw7_x1m_isPrime_liesOver_ne_bot_of_mem K hP
  haveI := hPpr; haveI := hPlo
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPne hPpr
  haveI : Finite ((𝓞 K) ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
  letI : Field ((𝓞 K) ⧸ P) := Ideal.Quotient.field P

  have halgcomp : (algebraMap F ((𝓞 K) ⧸ P)).comp πF
      = algebraMap ℤ ((𝓞 K) ⧸ P) := RingHom.ext_int _ _

  haveI : CharP F 3 := by
    refine ⟨fun n => ?_⟩
    rw [← map_natCast πF, show πF = Ideal.Quotient.mk p3 from rfl,
      Ideal.Quotient.eq_zero_iff_mem, hp3, Ideal.mem_span_singleton]
    exact Int.natCast_dvd_natCast (m := 3)
  haveI : Finite F := Finite.of_injective σ σ.injective
  haveI : FiniteDimensional F ((𝓞 K) ⧸ P) := Module.Finite.of_finite

  obtain ⟨ζ, hζ⟩ := Field.exists_primitive_element F ((𝓞 K) ⧸ P)
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective ζ
  set μF := minpoly F ζ with hμF
  have hζint : _root_.IsIntegral F ζ := Algebra.IsIntegral.isIntegral ζ
  have hμFmon : μF.Monic := minpoly.monic hζint
  have hμFirr : Irreducible μF := minpoly.irreducible hζint

  have hμFdeg : μF.natDegree = p3.inertiaDeg' P := by
    have hζadj : Algebra.adjoin F {ζ} = (⊤ : Subalgebra F ((𝓞 K) ⧸ P)) := by
      have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic (R := F) ζ)
      rw [hζ, IntermediateField.top_toSubalgebra] at this; exact this.symm
    let pb : PowerBasis F ((𝓞 K) ⧸ P) :=
      (Algebra.adjoin.powerBasis hζint).map
        ((Subalgebra.equivOfEq _ _ hζadj).trans Subalgebra.topEquiv)
    have hpb : pb.dim = μF.natDegree := by
      simp only [pb, PowerBasis.map_dim, Algebra.adjoin.powerBasis_dim, hμF]
    rw [Ideal.inertiaDeg_algebraMap]; exact (pb.finrank.trans hpb).symm

  set μ3 := μF.map (σ : F →+* ZMod 3) with hμ3
  have hμ3mon : μ3.Monic := hμFmon.map _
  have hμ3irr : Irreducible μ3 := by
    have hirr' : Irreducible (Polynomial.mapEquiv σ μF) := by
      rwa [MulEquiv.irreducible_iff]
    exact hirr'
  obtain ⟨μ, hμmon, hμmap⟩ := gapsw79_t5_exists_monic_int_lift μ3 hμ3mon

  have hμmapF : μ.map πF = μF := by
    have h1 : (μ.map πF).map (σ : F →+* ZMod 3) = μF.map (σ : F →+* ZMod 3) := by
      rw [Polynomial.map_map, hσcomp, hμmap, hμ3]
    exact Polynomial.map_injective _ σ.injective h1

  refine ⟨β, μ, hμmon, hμmap ▸ hμ3irr, ?_, ?_⟩
  ·
    show eval₂ (algebraMap ℤ ((𝓞 K) ⧸ P)) (Ideal.Quotient.mk P β) μ = 0
    rw [← halgcomp, ← Polynomial.eval₂_map, hμmapF, hβ]
    exact minpoly.aeval F ζ
  ·
    rw [hμmap, hμ3, hμFmon.natDegree_map, hμFdeg]

set_option maxHeartbeats 12800000 in

theorem gapsw79_t5_exists_crt_approximant
    (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K))
    (β : 𝓞 K) (μ : ℤ[X])
    (hμirr : Irreducible (μ.map (Int.castRingHom (ZMod 3)))) :
    ∃ ξ₁ : 𝓞 K, ξ₁ - β ∈ P ∧
      (ξ₁ ^ (Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
          ⧸ gapsw7X1mCompletionIdeal K P hP)) - ξ₁ ∉ P ^ 2) ∧
      ∀ Q ∈ IsDedekindDomain.primesOverFinset
          (Ideal.span {(3 : ℤ)}) (𝓞 K), Q ≠ P →
        Polynomial.aeval (Ideal.Quotient.mk Q ξ₁) μ ≠ 0 := by
  have _em := Classical.em
  classical
  set p3 := Ideal.span {(3 : ℤ)} with hp3
  set 𝒮 := IsDedekindDomain.primesOverFinset p3 (𝓞 K) with h𝒮
  set q := Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ⧸ gapsw7X1mCompletionIdeal K P hP) with hqdef
  obtain ⟨hPpr, hPlo, hPne⟩ := gapsw7_x1m_isPrime_liesOver_ne_bot_of_mem K hP
  haveI := hPpr; haveI := hPlo
  haveI hPmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPne hPpr
  haveI : Finite ((𝓞 K) ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  letI : Field ((𝓞 K) ⧸ P) := Ideal.Quotient.field P

  have hqeq : q = Fintype.card ((𝓞 K) ⧸ P) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (gapsw7X1mResidueEquiv K P hP).toEquiv.symm
  have hqmemP : (q : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hqeq]
    exact Nat.cast_card_eq_zero ((𝓞 K) ⧸ P)

  have hβfermat : β ^ q - β ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hqeq,
      FiniteField.pow_card, sub_self]

  obtain ⟨πP, hπP1, hπP2⟩ := SetLike.exists_of_lt
    (show (P : Ideal (𝓞 K)) ^ 2 < P ^ 1 from Ideal.pow_succ_lt_pow hPne 1)
  rw [pow_one] at hπP1
  obtain ⟨β'', hβ''P, hβ''b⟩ :
      ∃ β'' : 𝓞 K, β'' - β ∈ P ∧ β'' ^ q - β'' ∉ P ^ 2 := by
    by_cases hβb : β ^ q - β ∈ P ^ 2
    · refine ⟨β + πP, by simpa using hπP1, ?_⟩

      have hkey : (β + πP) ^ q - β ^ q ∈ P ^ 2 :=
        gapsw79_t2_pow_sub_pow_mem_sq P (β + πP) β q
          (by simpa using hπP1) hqmemP
      intro hcontra
      have hcalc : πP
          = ((β + πP) ^ q - β ^ q) + (β ^ q - β) - ((β + πP) ^ q - (β + πP)) := by
        ring
      exact hπP2 (hcalc ▸ sub_mem (add_mem hkey hβb) hcontra)
    · exact ⟨β, sub_self β ▸ P.zero_mem, hβb⟩

  have hQsetup : ∀ Q ∈ 𝒮, Q.IsMaximal ∧ (3 : 𝓞 K) ∈ Q := by
    intro Q hQ
    obtain ⟨hQpr, hQlo, hQne⟩ := gapsw7_x1m_isPrime_liesOver_ne_bot_of_mem K hQ
    refine ⟨Ring.DimensionLEOne.maximalOfPrime hQne hQpr, ?_⟩
    have h3u : (3 : ℤ) ∈ Ideal.under ℤ Q :=
      hQlo.over ▸ Ideal.mem_span_singleton_self (3 : ℤ)
    simpa only [Ideal.under_def, Ideal.mem_comap, map_ofNat] using h3u
  have h3P : (3 : 𝓞 K) ∈ P := (hQsetup P hP).2

  have hc : ∀ Q ∈ 𝒮, Q ≠ P → ∃ c : 𝓞 K,
      Polynomial.aeval (Ideal.Quotient.mk Q c) μ ≠ 0 := by
    intro Q hQ _hQP
    haveI := (hQsetup Q hQ).1
    letI : Field ((𝓞 K) ⧸ Q) := Ideal.Quotient.field Q
    haveI : CharP ((𝓞 K) ⧸ Q) 3 := by
      have h30 : ((3 : ℕ) : (𝓞 K) ⧸ Q) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
        exact_mod_cast (hQsetup Q hQ).2
      exact (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h30
    obtain ⟨cb, hcb⟩ :=
      gapsw79_t5_exists_nonroot_of_irreducible_mod_three ((𝓞 K) ⧸ Q) μ hμirr
    obtain ⟨c, hcc⟩ := Ideal.Quotient.mk_surjective cb
    exact ⟨c, hcc ▸ hcb⟩

  let Pf : 𝒮 := ⟨P, hP⟩
  let I : 𝒮 → Ideal (𝓞 K) := fun Q => (Q : Ideal (𝓞 K)) ^ (if Q = Pf then 2 else 1)
  let tgt : 𝒮 → 𝓞 K := fun Q =>
    if h : Q = Pf then β''
    else (hc Q Q.2 (fun heq => h (Subtype.ext heq))).choose
  have hIcoprime : Pairwise (Function.onFun IsCoprime I) := by
    intro Q Q' hQQ'
    haveI := (hQsetup Q.1 Q.2).1; haveI := (hQsetup Q'.1 Q'.2).1
    have hbase : IsCoprime (Q : Ideal (𝓞 K)) (Q' : Ideal (𝓞 K)) :=
      Ideal.isCoprime_of_isMaximal (fun h => hQQ' (Subtype.ext h))
    exact hbase.pow
  haveI : Fintype (𝒮 : Type _) := FinsetCoe.fintype 𝒮
  obtain ⟨ξ₁, hξ₁⟩ := Ideal.exists_forall_sub_mem_ideal hIcoprime tgt

  have hξ₁P : ξ₁ - β'' ∈ P ^ 2 := by
    have := hξ₁ Pf; simp only [I, tgt, if_pos rfl, dif_pos rfl] at this; exact this
  have hξ₁Q : ∀ (Q : 𝒮), Q ≠ Pf → ξ₁ - tgt Q ∈ (Q : Ideal (𝓞 K)) := by
    intro Q hQf
    have := hξ₁ Q
    simp only [I, if_neg hQf, pow_one] at this; exact this

  refine ⟨ξ₁, ?_, ?_, ?_⟩
  ·
    have h1 : ξ₁ - β'' ∈ P := Ideal.pow_le_self two_ne_zero hξ₁P
    have heq : ξ₁ - β = (ξ₁ - β'') + (β'' - β) := by ring
    rw [heq]; exact P.add_mem h1 hβ''P
  ·
    intro hcontra
    have hdiff : ξ₁ - β'' ∈ P := Ideal.pow_le_self two_ne_zero hξ₁P
    have hkey : ξ₁ ^ q - β'' ^ q ∈ P ^ 2 :=
      gapsw79_t2_pow_sub_pow_mem_sq P ξ₁ β'' q hdiff hqmemP
    have hcalc : β'' ^ q - β''
        = (ξ₁ ^ q - ξ₁) - (ξ₁ ^ q - β'' ^ q) + (ξ₁ - β'') := by ring
    exact hβ''b (hcalc ▸ add_mem (sub_mem hcontra hkey) hξ₁P)
  ·
    intro Q hQ hQP
    have hQf : (⟨Q, hQ⟩ : 𝒮) ≠ Pf := fun h => hQP (congrArg Subtype.val h)
    have hcong : Ideal.Quotient.mk Q ξ₁
        = Ideal.Quotient.mk Q (tgt ⟨Q, hQ⟩) :=
      Ideal.Quotient.eq.mpr (hξ₁Q ⟨Q, hQ⟩ hQf)
    rw [hcong]; simp only [tgt, dif_neg hQf]
    exact (hc Q hQ (fun h => hQf (Subtype.ext h))).choose_spec

set_option maxHeartbeats 12800000 in

theorem gapsw79_t5_residueSepGen_holds :
    ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (𝓞 K))
      (hP : P ∈ IsDedekindDomain.primesOverFinset
        (Ideal.span {(3 : ℤ)}) (𝓞 K)),
      3 ∣ (Ideal.span {(3 : ℤ)}).ramificationIdx' P →
      ∃ ξ : 𝓞 K, Algebra.adjoin ℚ {(algebraMap (𝓞 K) K ξ)} = ⊤ ∧
        ((algebraMap (𝓞 K)
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)
          ^ (Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
              ⧸ gapsw7X1mCompletionIdeal K P hP))
        - algebraMap (𝓞 K)
            ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ
        ∉ (gapsw7X1mCompletionIdeal K P hP) ^ 2) ∧
        ∃ μ : ℤ[X], μ.Monic ∧
          Irreducible (μ.map (Int.castRingHom (ZMod 3))) ∧
          Polynomial.aeval
            (Ideal.Quotient.mk (gapsw7X1mCompletionIdeal K P hP)
              (algebraMap (𝓞 K)
                ((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ξ)) μ
            = 0 ∧
          (μ.map (Int.castRingHom (ZMod 3))).natDegree
            = (Ideal.span {(3 : ℤ)}).inertiaDeg' P ∧
          ∀ Q ∈ IsDedekindDomain.primesOverFinset
              (Ideal.span {(3 : ℤ)}) (𝓞 K), Q ≠ P →
            Polynomial.aeval (Ideal.Quotient.mk Q ξ) μ ≠ 0 := by
  have _em := Classical.em
  classical
  intro K _ _ P hP _hwild
  set q := Nat.card (((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
      ⧸ gapsw7X1mCompletionIdeal K P hP) with hqdef

  obtain ⟨β, μ, hμmon, hμirr, hβroot, ha'⟩ :=
    gapsw79_t5_exists_residue_minpoly K P hP
  obtain ⟨ξ₁, hξ₁P, hξ₁b, hξ₁d⟩ :=
    gapsw79_t5_exists_crt_approximant K P hP β μ hμirr
  obtain ⟨γ, hγ⟩ := gapsw78_t9_exists_integral_primitive_element K

  obtain ⟨N, hNadj⟩ := gapsw79_t5_exists_primitive_in_nine_coset K
    (algebraMap (𝓞 K) K ξ₁) (algebraMap (𝓞 K) K γ) hγ
  set ξ := ξ₁ + (9 * N : ℤ) • γ with hξdef

  have hξK : algebraMap (𝓞 K) K ξ
      = algebraMap (𝓞 K) K ξ₁ + (9 * N : ℤ) • algebraMap (𝓞 K) K γ := by
    rw [hξdef, map_add, map_zsmul]

  have h3mem : ∀ Q ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K), (3 : 𝓞 K) ∈ Q := by
    intro Q hQ
    obtain ⟨_, hQlo, _⟩ := gapsw7_x1m_isPrime_liesOver_ne_bot_of_mem K hQ
    have h3u : (3 : ℤ) ∈ Ideal.under ℤ Q :=
      hQlo.over ▸ Ideal.mem_span_singleton_self (3 : ℤ)
    simpa only [Ideal.under_def, Ideal.mem_comap, map_ofNat] using h3u

  have h9Nγ_eq : ∀ R : Ideal (𝓞 K), (9 * N : ℤ) • γ ∈ R
      ↔ (3 : 𝓞 K) * ((3 : 𝓞 K) * ((N : 𝓞 K) * γ)) ∈ R := by
    intro R
    rw [zsmul_eq_mul, show ((9 * N : ℤ) : 𝓞 K) * γ
      = (3 : 𝓞 K) * ((3 : 𝓞 K) * ((N : 𝓞 K) * γ)) from by push_cast; ring]
  have h9Psq : (9 * N : ℤ) • γ ∈ P ^ 2 := by
    rw [h9Nγ_eq, sq]
    exact Ideal.mul_mem_mul (h3mem P hP)
      (Ideal.mul_mem_right _ _ (h3mem P hP))
  have h9Q : ∀ Q ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(3 : ℤ)}) (𝓞 K), (9 * N : ℤ) • γ ∈ Q := by
    intro Q hQ
    rw [h9Nγ_eq]; exact Ideal.mul_mem_right _ _ (h3mem Q hQ)
  have h9P : (9 * N : ℤ) • γ ∈ P := Ideal.pow_le_self two_ne_zero h9Psq

  obtain ⟨hPpr, _, hPne⟩ := gapsw7_x1m_isPrime_liesOver_ne_bot_of_mem K hP
  haveI := hPpr
  haveI : Finite ((𝓞 K) ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hqmemP : (q : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
      show q = Fintype.card ((𝓞 K) ⧸ P) from
        (Nat.card_congr (gapsw7X1mResidueEquiv K P hP).toEquiv.symm).trans
          Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero ((𝓞 K) ⧸ P)

  have hξξ₁P : ξ - ξ₁ ∈ P := by rw [hξdef, add_sub_cancel_left]; exact h9P
  have hξξ₁Psq : ξ - ξ₁ ∈ P ^ 2 := by
    rw [hξdef, add_sub_cancel_left]; exact h9Psq

  have hξb : ξ ^ q - ξ ∉ P ^ 2 := by
    intro hcontra
    have hkey : ξ ^ q - ξ₁ ^ q ∈ P ^ 2 :=
      gapsw79_t2_pow_sub_pow_mem_sq P ξ ξ₁ q hξξ₁P hqmemP
    have hcalc : ξ₁ ^ q - ξ₁
        = (ξ ^ q - ξ) - (ξ ^ q - ξ₁ ^ q) + (ξ - ξ₁) := by ring
    exact hξ₁b (hcalc ▸ add_mem (sub_mem hcontra hkey) hξξ₁Psq)

  have hξβP : Ideal.Quotient.mk P ξ = Ideal.Quotient.mk P β := by
    refine Ideal.Quotient.eq.mpr ?_
    have : ξ - β = (ξ - ξ₁) + (ξ₁ - β) := by ring
    rw [this]; exact P.add_mem hξξ₁P hξ₁P

  refine ⟨ξ, ?_, ?_, μ, hμmon, hμirr, ?_, ha', ?_⟩
  ·
    rw [hξK]; exact hNadj
  ·
    rw [← map_pow, ← map_sub, gapsw79_t5_mem_completionIdeal_pow_iff_mem_pow]
    exact hξb
  ·

    set 𝔪 := gapsw7X1mCompletionIdeal K P hP with h𝔪
    set φ := algebraMap (𝓞 K) ((gapsw7X1mPlace K P hP).adicCompletionIntegers K)
    have hcomap : P ≤ Ideal.comap φ 𝔪 := by
      rw [show 𝔪.comap φ = P from
        (gapsw7_x1m_completionIdeal_liesOver K P hP).over.symm]
    let ψ := Ideal.quotientMap 𝔪 φ hcomap
    have hψmk : ψ (Ideal.Quotient.mk P ξ) = Ideal.Quotient.mk 𝔪 (φ ξ) :=
      Ideal.quotientMap_mk
    have hψcomp : ψ.comp (algebraMap ℤ ((𝓞 K) ⧸ P))
        = algebraMap ℤ (((gapsw7X1mPlace K P hP).adicCompletionIntegers K) ⧸ 𝔪) :=
      RingHom.ext_int _ _
    have haevalP : Polynomial.aeval (Ideal.Quotient.mk P ξ) μ = 0 :=
      hξβP ▸ hβroot
    show Polynomial.aeval (Ideal.Quotient.mk 𝔪 (φ ξ)) μ = 0
    rw [← hψmk, Polynomial.aeval_def, ← hψcomp, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, haevalP, _root_.map_zero]
  ·
    intro Q hQ hQP
    have hcong : Ideal.Quotient.mk Q ξ = Ideal.Quotient.mk Q ξ₁ :=
      Ideal.Quotient.eq.mpr (by
        rw [hξdef, add_sub_cancel_left]; exact h9Q Q hQ)
    rw [hcong]; exact hξ₁d Q hQ hQP

theorem gapsw79_t5_pieceIResidual :
    Gapsw48T5CompletionTransportPieceIResidual :=
  gapsw79_t4_pieceIResidual_of_residueSepGen gapsw79_t5_residueSepGen_holds

end FLT.Gapsw79T5ResidueSepGenConstruction
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.AdaptedFamily P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.ModularCurve.PhiGen P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.adicCompletion P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.NumberField"

open FLT.Gapsw49T5CompletionTransportAtomWeld FLT.Gapsw79T5ResidueSepGenConstruction FLT.Gapsw44T4WildDifferentSummationWs in

theorem solution
    (K : Type) [Field K] [NumberField K] (P : Ideal (NumberField.RingOfIntegers K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (NumberField.RingOfIntegers K)) :
    (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (NumberField.RingOfIntegers K))).count P
      ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P
        + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
          * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) - 1 :=
  gapsw49_t5_wildDifferentUpperBoundSupply_of_pieceIResidual gapsw79_t5_pieceIResidual K P hP

end S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three
end P2MW
export P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three (solution)
