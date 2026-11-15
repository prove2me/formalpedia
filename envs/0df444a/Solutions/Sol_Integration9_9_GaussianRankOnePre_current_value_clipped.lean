-- Prove2me | solution 1 for Integration9_9.GaussianRankOnePre.current_value_clipped
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T00:41:13.05921+00:00
-- url     : https://prove2.me/submissions/6197bc67-1181-4bc8-a130-ab0a50f37c74

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_09
import Mathlib
import Theorems.Thm_AFT_FiniteDist_l1_independent_fin_le
import Theorems.Thm_AFT_FiniteDist_totalVariation_eq_half_l1
import Theorems.Thm_InfoLossLAR_WorstCase_lemma_5_2
import Theorems.Thm_Integration9_9_TM2NativeProducer_current_value
namespace P2Mba49f952
end P2Mba49f952
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → AFT.BinaryArithmetic.RationalBits.exists_code
open _root_.InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic renaming bits_value → AFT.BinaryArithmetic.bits_value
open _root_.InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT.CanonicalMoments renaming independent_embedding_expectation_general → AFT.CanonicalMoments.independent_embedding_expectation_general
open _root_.InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT.CanonicalMoments renaming independent_equiv_expectation_general → AFT.CanonicalMoments.independent_equiv_expectation_general
open _root_.InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics.HeightBound renaming div → AFT.RationalNumerics.HeightBound.div
open _root_.InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics.HeightBound renaming inv → AFT.RationalNumerics.HeightBound.inv
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → AFT.RationalNumerics.HeightBound.mono
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → AFT.RationalNumerics.HeightBound.mul
open _root_.InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics.HeightBound renaming of_int → AFT.RationalNumerics.HeightBound.of_int
open _root_.InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics.HeightBound renaming of_nat → AFT.RationalNumerics.HeightBound.of_nat
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → AFT.RationalNumerics.HeightBound.one
open _root_.InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics.HeightBound renaming pow → AFT.RationalNumerics.HeightBound.pow
open _root_.InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics renaming arctanSum_error → AFT.RationalNumerics.arctanSum_error
open _root_.InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics renaming arctan_term_bound → AFT.RationalNumerics.arctan_term_bound
open _root_.InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics renaming boundedRootList_nodup → AFT.RationalNumerics.boundedRootList_nodup
open _root_.InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics renaming commonDenominator_le → AFT.RationalNumerics.commonDenominator_le
open _root_.InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics renaming commonDenominator_pos → AFT.RationalNumerics.commonDenominator_pos
open _root_.InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics renaming commonNumerator_abs_le → AFT.RationalNumerics.commonNumerator_abs_le
open _root_.InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics renaming commonNumerator_cast → AFT.RationalNumerics.commonNumerator_cast
open _root_.InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics renaming commonNumerator_div → AFT.RationalNumerics.commonNumerator_div
open _root_.InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics renaming denominator_dvd_common → AFT.RationalNumerics.denominator_dvd_common
open _root_.InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics renaming integerLinearIteration_abs_le → AFT.RationalNumerics.integerLinearIteration_abs_le
open _root_.InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics renaming integerLinearIteration_exact → AFT.RationalNumerics.integerLinearIteration_exact
open _root_.InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics renaming integerLinearIteration_height → AFT.RationalNumerics.integerLinearIteration_height
open _root_.InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics renaming linearIteration_height → AFT.RationalNumerics.linearIteration_height
open _root_.InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics renaming mem_boundedRootList → AFT.RationalNumerics.mem_boundedRootList
open _root_.InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics renaming piApprox_error → AFT.RationalNumerics.piApprox_error
open _root_.InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics renaming piApprox_le_five → AFT.RationalNumerics.piApprox_le_five
open _root_.InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT.V7Calibration renaming actualPublicBodyChoice_nonempty → AFT.V7Calibration.actualPublicBodyChoice_nonempty
open _root_.InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT.V7Calibration renaming actualPublicPrimaryChoice_nonempty → AFT.V7Calibration.actualPublicPrimaryChoice_nonempty
open _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct renaming current_value → CurrentAFT.BinaryFiniteProduct.current_value
open _root_.InfoLossLARNativeSupplements.hf109288ce2bff41a.CurrentAFT.BinaryFullResponseCounts renaming current_sizes → CurrentAFT.BinaryFullResponseCounts.current_sizes
open _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum renaming current_value → CurrentAFT.BinaryListSum.current_value
open _root_.InfoLossLARNativeSupplements.hb7b15c9a79e648be.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_ordinary → CurrentAFT.BinaryRootMetadataSerializer.actualChoice_ordinary
open _root_.InfoLossLARNativeSupplements.h9bd8eaff2c880c78.CurrentAFT.BinaryRootMetadataSerializer renaming actualChoice_primary → CurrentAFT.BinaryRootMetadataSerializer.actualChoice_primary
open _root_.InfoLossLARNativeSupplements.ha802267fba3ae37a.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_input → CurrentAFT.BinaryRootMetadataSerializer.candidate_input
open _root_.InfoLossLARNativeSupplements.h1ccc0b12a2e9b2e7.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_kept → CurrentAFT.BinaryRootMetadataSerializer.candidate_kept
open _root_.InfoLossLARNativeSupplements.hf63ab620f3c57a9b.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_ordinary → CurrentAFT.BinaryRootMetadataSerializer.candidate_ordinary
open _root_.InfoLossLARNativeSupplements.h8b1af35cb5128d1e.CurrentAFT.BinaryRootMetadataSerializer renaming candidate_primary → CurrentAFT.BinaryRootMetadataSerializer.candidate_primary
open _root_.InfoLossLARNativeSupplements.hc002c1f58373bc9e.CurrentAFT.BinaryRootMetadataSerializer renaming classify_numbering → CurrentAFT.BinaryRootMetadataSerializer.classify_numbering
open _root_.InfoLossLARNativeSupplements.h0654708b8f7abd41.CurrentAFT.BinaryRootMetadataSerializer renaming current_castMetadata → CurrentAFT.BinaryRootMetadataSerializer.current_castMetadata
open _root_.InfoLossLARNativeSupplements.h62365cd168bf9746.CurrentAFT.BinaryRootMetadataSerializer renaming current_cast_tags → CurrentAFT.BinaryRootMetadataSerializer.current_cast_tags
open _root_.InfoLossLARNativeSupplements.hd04a074a03468451.CurrentAFT.BinaryRootMetadataSerializer renaming current_congr_counts → CurrentAFT.BinaryRootMetadataSerializer.current_congr_counts
open _root_.InfoLossLARNativeSupplements.h92779a9b15e1ad74.CurrentAFT.BinaryRootMetadataSerializer renaming current_kept_le → CurrentAFT.BinaryRootMetadataSerializer.current_kept_le
open _root_.InfoLossLARNativeSupplements.h5d3e6518d488d268.CurrentAFT.BinaryRootMetadataSerializer renaming current_metadata_actual → CurrentAFT.BinaryRootMetadataSerializer.current_metadata_actual
open _root_.InfoLossLARNativeSupplements.h6da04ab1cb4f0ae9.CurrentAFT.BinaryRootMetadataSerializer renaming current_native_counts → CurrentAFT.BinaryRootMetadataSerializer.current_native_counts
open _root_.InfoLossLARNativeSupplements.h0034013fd46e34b6.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_actual → CurrentAFT.BinaryRootMetadataSerializer.current_rational_actual
open _root_.InfoLossLARNativeSupplements.he41810aeef644de7.CurrentAFT.BinaryRootMetadataSerializer renaming current_rational_native → CurrentAFT.BinaryRootMetadataSerializer.current_rational_native
open _root_.InfoLossLARNativeSupplements.hdf21f91932116c35.CurrentAFT.BinaryRootMetadataSerializer renaming current_role → CurrentAFT.BinaryRootMetadataSerializer.current_role
open _root_.InfoLossLARNativeSupplements.h2f02b0da80d0da15.CurrentAFT.BinaryRootMetadataSerializer renaming current_role_actual → CurrentAFT.BinaryRootMetadataSerializer.current_role_actual
open _root_.InfoLossLARNativeSupplements.hf05bd272bb1b56e1.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot → CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot
open _root_.InfoLossLARNativeSupplements.h99dea6e0b2cb92cd.CurrentAFT.BinaryRootMetadataSerializer renaming current_tagSlot_actual → CurrentAFT.BinaryRootMetadataSerializer.current_tagSlot_actual
open _root_.InfoLossLARNativeSupplements.h5aa51497de94248a.CurrentAFT.BinaryRootMetadataSerializer renaming find_value → CurrentAFT.BinaryRootMetadataSerializer.find_value
open _root_.InfoLossLARNativeSupplements.he1ba053a04ebe416.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_kept → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_kept
open _root_.InfoLossLARNativeSupplements.hb19b481a4ab916e9.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_ordinary → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_ordinary
open _root_.InfoLossLARNativeSupplements.h925bf1f311c5581d.CurrentAFT.BinaryRootMetadataSerializer renaming inputOrdering_symm_primary → CurrentAFT.BinaryRootMetadataSerializer.inputOrdering_symm_primary
open _root_.InfoLossLARNativeSupplements.h28bdeb915df6f31b.CurrentAFT.BinaryRootMetadataSerializer renaming keptOrdering_number → CurrentAFT.BinaryRootMetadataSerializer.keptOrdering_number
open _root_.InfoLossLARNativeSupplements.hd98ece77ce245c62.CurrentAFT.BinaryRootMetadataSerializer renaming kept_length_le → CurrentAFT.BinaryRootMetadataSerializer.kept_length_le
open _root_.InfoLossLARNativeSupplements.h0c3b1f75a36dc0a1.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_input → CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_input
open _root_.InfoLossLARNativeSupplements.h3614eab28d16c434.CurrentAFT.BinaryRootMetadataSerializer renaming matchesBlock_value → CurrentAFT.BinaryRootMetadataSerializer.matchesBlock_value
open _root_.InfoLossLARNativeSupplements.h7211ad64e277ecd6.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_get → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_get
open _root_.InfoLossLARNativeSupplements.h5bfd14958fa45ca1.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_increasing → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_increasing
open _root_.InfoLossLARNativeSupplements.h830e34787bfcc36e.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_membership → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_membership
open _root_.InfoLossLARNativeSupplements.hdf4e90e4faeda9bb.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput
open _root_.InfoLossLARNativeSupplements.h0eb6479555712d22.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_tagsInput_vector → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_tagsInput_vector
open _root_.InfoLossLARNativeSupplements.he3484ce79e618bef.CurrentAFT.BinaryRootMetadataSerializer renaming nativeTag_value → CurrentAFT.BinaryRootMetadataSerializer.nativeTag_value
open _root_.InfoLossLARNativeSupplements.hb10c61056b84e123.CurrentAFT.BinaryRootMetadataSerializer renaming position_input → CurrentAFT.BinaryRootMetadataSerializer.position_input
open _root_.InfoLossLARNativeSupplements.h717398dca61c08fb.CurrentAFT.BinaryRootMetadataSerializer renaming rational_current_cast_tags → CurrentAFT.BinaryRootMetadataSerializer.rational_current_cast_tags
open _root_.InfoLossLARNativeSupplements.h5c1679d60747a3c8.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_at_group → CurrentAFT.BinaryRootMetadataSerializer.retainedInput_at_group
open _root_.InfoLossLARNativeSupplements.hd10b40ce4e5fb3ce.CurrentAFT.BinaryRootMetadataSerializer renaming retainedInput_get → CurrentAFT.BinaryRootMetadataSerializer.retainedInput_get
open _root_.InfoLossLARNativeSupplements.h790debae9bc7d744.CurrentAFT.BinaryRootMetadataSerializer renaming role_input → CurrentAFT.BinaryRootMetadataSerializer.role_input
open _root_.InfoLossLARNativeSupplements.h36433fb6e771176d.CurrentAFT.BinaryRootMetadataSerializer renaming role_kept → CurrentAFT.BinaryRootMetadataSerializer.role_kept
open _root_.InfoLossLARNativeSupplements.h1c0aacbfbcab259c.CurrentAFT.BinaryRootMetadataSerializer renaming role_ordinary → CurrentAFT.BinaryRootMetadataSerializer.role_ordinary
open _root_.InfoLossLARNativeSupplements.had28d56c66c172c2.CurrentAFT.BinaryRootMetadataSerializer renaming role_primary → CurrentAFT.BinaryRootMetadataSerializer.role_primary
open _root_.InfoLossLARNativeSupplements.hf7b606d7b6c71037.CurrentAFT.BinaryRootMetadataSerializer renaming splitIndex_value → CurrentAFT.BinaryRootMetadataSerializer.splitIndex_value
open _root_.InfoLossLARNativeSupplements.hc171b658125977dd.CurrentAFT.BinaryRootMetadataSerializer renaming tagBlocks_card → CurrentAFT.BinaryRootMetadataSerializer.tagBlocks_card
open _root_.InfoLossLARNativeSupplements.h864990220cd05a68.CurrentAFT.BinaryRootMetadataSerializer renaming tagSlot_input → CurrentAFT.BinaryRootMetadataSerializer.tagSlot_input
open _root_.InfoLossLARNativeSupplements.he99bee3d04267632.CurrentAFT.BinaryRootMetadataSerializer renaming tagsInput_get → CurrentAFT.BinaryRootMetadataSerializer.tagsInput_get
open _root_.InfoLossLARNativeSupplements.h15d8c2848429780a.CurrentAFT.BinaryRootMetadataSerializer renaming vector_count_cast_get → CurrentAFT.BinaryRootMetadataSerializer.vector_count_cast_get
open _root_.InfoLossLARNativeSupplements.h6033ffbe1c08cc96.CurrentAFT.BinaryRootMetadataSerializer renaming vector_length_cast_get → CurrentAFT.BinaryRootMetadataSerializer.vector_length_cast_get
open _root_.InfoLossLARNativeSupplements.he438d921f6936ff8.CurrentAFT.BinaryRootMetadataSerializer renaming vector_mem_toList → CurrentAFT.BinaryRootMetadataSerializer.vector_mem_toList
open _root_.InfoLossLARNativeSupplements.he37fcb2fedaaad11.CurrentAFT.BinarySparseCycleEvaluation renaming current_tuple_value → CurrentAFT.BinarySparseCycleEvaluation.current_tuple_value
open _root_.InfoLossLARNativeSupplements.h42f327202f6ffc34.CurrentAFT.BinarySparseCycleEvaluation renaming rootEntry_value → CurrentAFT.BinarySparseCycleEvaluation.rootEntry_value
open _root_.InfoLossLARNativeSupplements.h046841627a1cee9b.CurrentAFT.BinarySparseCycleEvaluation renaming roots_value → CurrentAFT.BinarySparseCycleEvaluation.roots_value
open _root_.InfoLossLARNativeSupplements.hd0df78f75d4d893f.CurrentAFT.BinarySparseCycleEvaluation renaming term_value → CurrentAFT.BinarySparseCycleEvaluation.term_value
open _root_.InfoLossLARNativeSupplements.hf4f5fd4dcb0d678c.CurrentAFT.BinarySparseCycleEvaluation renaming weightEntry_value → CurrentAFT.BinarySparseCycleEvaluation.weightEntry_value
open _root_.InfoLossLARNativeSupplements.haf9b5363dbfc3f4c.CurrentAFT.BinarySparseCycleSemantic renaming coordinates_apply → CurrentAFT.BinarySparseCycleSemantic.coordinates_apply
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → CurrentAFT.BinarySparseCycleSemantic.current_value
open _root_.InfoLossLARNativeSupplements.h0cda298b0874d5b6.CurrentAFT.BinarySparseCycleSemantic renaming product_coordinates → CurrentAFT.BinarySparseCycleSemantic.product_coordinates
open _root_.InfoLossLARNativeSupplements.h10d530ee15bdc77f.CurrentAFT.BinarySparseCycleSemantic renaming roots_coordinates → CurrentAFT.BinarySparseCycleSemantic.roots_coordinates
open _root_.InfoLossLARNativeSupplements.h5cfbe96a887c7fbe.CurrentAFT.BinaryTouchedCycle renaming candidates_length → CurrentAFT.BinaryTouchedCycle.candidates_length
open _root_.InfoLossLARNativeSupplements.hbcb1352f59b47e7a.CurrentAFT.BinaryTouchedCycle renaming prepare_length → CurrentAFT.BinaryTouchedCycle.prepare_length
open _root_.InfoLossLARNativeSupplements.h7b66ba8c3614b749.CurrentAFT.BinaryTouchedCycle renaming unique_length → CurrentAFT.BinaryTouchedCycle.unique_length
open _root_.InfoLossLARNativeSupplements.h8bc15ae79e4624be.CurrentAFT.BinaryTouchedCycleBuffer renaming lookup_value → CurrentAFT.BinaryTouchedCycleBuffer.lookup_value
open _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks renaming positions_value → CurrentAFT.BinaryTouchedCycleRanks.positions_value
open _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum renaming current_value → CurrentAFT.BinaryTupleSum.current_value
open _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum renaming get_ofFn_fun → CurrentAFT.BinaryTupleSum.get_ofFn_fun
open _root_.InfoLossLARNativeSupplements.ha84cbfc4268e8d40.CurrentAFT.BinaryTupleSum renaming prepend_get → CurrentAFT.BinaryTupleSum.prepend_get
open _root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum renaming prepend_value → CurrentAFT.BinaryTupleSum.prepend_value
open _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag renaming card → CurrentAFT.CountedBoundedRootTags.Tag.card
open _root_.InfoLossLARNativeSupplements.h9568a61082f27bb9.CurrentAFT.CountedBoundedRootTags.Tag renaming nodup → CurrentAFT.CountedBoundedRootTags.Tag.nodup
open _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag renaming read_value → CurrentAFT.CountedBoundedRootTags.Tag.read_value
open _root_.InfoLossLARNativeSupplements.hd05ef333dfb7baf7.CurrentAFT.CountedBoundedRootTags.Tag renaming store_value → CurrentAFT.CountedBoundedRootTags.Tag.store_value
open _root_.InfoLossLARNativeSupplements.h8bf8720ebb55498f.CurrentAFT.CountedBoundedRootTags.Tag renaming vector_increasing → CurrentAFT.CountedBoundedRootTags.Tag.vector_increasing
open _root_.InfoLossLARNativeSupplements.h5fde173c8469afa6.CurrentAFT.CountedBoundedRootTags renaming current_sets → CurrentAFT.CountedBoundedRootTags.current_sets
open _root_.InfoLossLARNativeSupplements.he8f344a3055fc54a.CurrentAFT.CountedBoundedRootTags renaming entry_sets → CurrentAFT.CountedBoundedRootTags.entry_sets
open _root_.InfoLossLARNativeSupplements.h2c50018e32584610.CurrentAFT.CountedBoundedRootTags renaming guarded_value → CurrentAFT.CountedBoundedRootTags.guarded_value
open _root_.InfoLossLARNativeSupplements.h4aa23a1b871c5bc6.CurrentAFT.CountedBoundedRootTags renaming sum_value → CurrentAFT.CountedBoundedRootTags.sum_value
open _root_.InfoLossLARNativeSupplements.h5a83c4211de0d052.CurrentAFT.CountedBoundedRootTags renaming sum_value_equiv → CurrentAFT.CountedBoundedRootTags.sum_value_equiv
open _root_.InfoLossLARNativeSupplements.h857ff8dbe55756b8.CurrentAFT.CurrentCycleEntryProgram renaming bodyCount_eq → CurrentAFT.CurrentCycleEntryProgram.bodyCount_eq
open _root_.InfoLossLARNativeSupplements.h4b24203afd73c049.CurrentAFT.CurrentCycleEntryProgram renaming roots_mod_iff → CurrentAFT.CurrentCycleEntryProgram.roots_mod_iff
open _root_.InfoLossLARNativeSupplements.h187f69822989eb63.CurrentAFT.CurrentCycleEntryProgram renaming selectedEntry_cast → CurrentAFT.CurrentCycleEntryProgram.selectedEntry_cast
open _root_.InfoLossLARNativeSupplements.h9180bab9fc132623.CurrentAFT.CurrentCycleEntryProgram renaming selected_probability_source → CurrentAFT.CurrentCycleEntryProgram.selected_probability_source
open _root_.InfoLossLARNativeSupplements.hf7c0550335227b9c.CurrentAFT.CurrentGaussianBits renaming ratio_bounds → CurrentAFT.CurrentGaussianBits.ratio_bounds
open _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram renaming encode_value → CurrentAFT.CurrentPublicShiftProgram.encode_value
open _root_.InfoLossLARNativeSupplements.h4ae04e3f1cb5b359.CurrentAFT.CurrentRootSlotIndex renaming tagPosition_eq → CurrentAFT.CurrentRootSlotIndex.tagPosition_eq
open _root_.InfoLossLARNativeSupplements.h20ee486b3d1dffd8.CurrentAFT.CyclePatternProgram renaming averagedEvaluate_cast → CurrentAFT.CyclePatternProgram.averagedEvaluate_cast
open _root_.InfoLossLARNativeSupplements.hb37dd6f3dcea3b7d.CurrentAFT.CyclePatternProgram renaming evaluate_local → CurrentAFT.CyclePatternProgram.evaluate_local
open _root_.InfoLossLARNativeSupplements.h689ba464633d8cff.CurrentAFT.CyclePatternProgram renaming evaluate_semantics → CurrentAFT.CyclePatternProgram.evaluate_semantics
open _root_.InfoLossLARNativeSupplements.hd02155c30f7ca58d.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_eq_windowEvaluate → CurrentAFT.CyclePatternProgram.gaussianEvaluate_eq_windowEvaluate
open _root_.InfoLossLARNativeSupplements.hc532f8ed89f571a1.CurrentAFT.CyclePatternProgram renaming gaussianEvaluate_semantics → CurrentAFT.CyclePatternProgram.gaussianEvaluate_semantics
open _root_.InfoLossLARNativeSupplements.h3e1ece29cbe1b4d4.CurrentAFT.CyclePatternProgram renaming restricted_expectation → CurrentAFT.CyclePatternProgram.restricted_expectation
open _root_.InfoLossLARNativeSupplements.h33993643e1712ab8.CurrentAFT.CycleRootExpansion renaming current_body_two_le → CurrentAFT.CycleRootExpansion.current_body_two_le
open _root_.InfoLossLARNativeSupplements.hd99e5f9e75bbb7e1.CurrentAFT.CycleSelections renaming averagedSelectedLaw_coordinate → CurrentAFT.CycleSelections.averagedSelectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.h788b7dba49e3cc6b.CurrentAFT.CycleSelections renaming selectedLaw_coordinate → CurrentAFT.CycleSelections.selectedLaw_coordinate
open _root_.InfoLossLARNativeSupplements.h8eafa7c1234de921.CurrentAFT.FullResponseEnumeration renaming mem_boundedSubsets → CurrentAFT.FullResponseEnumeration.mem_boundedSubsets
open _root_.InfoLossLARNativeSupplements.h4d94229af05aca84.CurrentAFT.Parameters renaming modulus_eq_find → CurrentAFT.Parameters.modulus_eq_find
open _root_.InfoLossLARNativeSupplements.h7c8d9f04458b8eff.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal → CurrentAFT.ProtectedCycle.cycleLaw_marginal
open _root_.InfoLossLARNativeSupplements.ha0baf4dfdfb7707f.CurrentAFT.ProtectedCycle renaming cycleLaw_marginal_of_two_le → CurrentAFT.ProtectedCycle.cycleLaw_marginal_of_two_le
open _root_.InfoLossLARNativeSupplements.h94f62847a0770621.CurrentAFT.ProtectedCycle renaming independent_pair_law → CurrentAFT.ProtectedCycle.independent_pair_law
open _root_.InfoLossLARNativeSupplements.h2021c53cebcb97f7.CurrentAFT.RationalScalarFamilyAverage renaming current_eq_window_sum → CurrentAFT.RationalScalarFamilyAverage.current_eq_window_sum
open _root_.InfoLossLARNativeSupplements.h6473fbae786c301e.CurrentAFT.RootSignedMassProgram renaming referenceEntry_cast → CurrentAFT.RootSignedMassProgram.referenceEntry_cast
open _root_.InfoLossLARNativeSupplements.h4c23fa31c2a53a0c.CurrentAFT.RootSignedMassProgram renaming singleton_probability → CurrentAFT.RootSignedMassProgram.singleton_probability
open _root_.InfoLossLARNativeSupplements.hb738544899c1bf50.CurrentAFT.TensorPublicProjection renaming independent_decision_expectation → CurrentAFT.TensorPublicProjection.independent_decision_expectation
open _root_.InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics renaming natAbs_finset_sum_le → AFT.RationalNumerics.natAbs_finset_sum_le
open _root_.InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics.HeightBound renaming reduced_le → AFT.RationalNumerics.HeightBound.reduced_le
open _root_.InfoLossLARNativeSupplements.hd70d55bab6f2346d.CurrentAFT.CountedBoundedRootTags renaming bounded_sum → CurrentAFT.CountedBoundedRootTags.bounded_sum
open _root_.InfoLossLARNativeSupplements.hb84db39a2a2ae627.CurrentAFT.CountedBoundedRootTags renaming flatMap_attach → CurrentAFT.CountedBoundedRootTags.flatMap_attach
open _root_.InfoLossLARNativeSupplements.he91e90e23380c2d0.CurrentAFT.JointTaggedPhysicalFock renaming law_nonempty → CurrentAFT.JointTaggedPhysicalFock.law_nonempty
section
set_option backward.isDefEq.respectTransparency false
namespace AFT
open scoped BigOperators
end AFT
namespace AFT
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h41 (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] _root_.AFT.zeroSumLattice n)
    (B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (c w : Fin (n + 1) → ℤ) (a : Fin n → ℤ)
    (ha : _root_.AFT.pathLoad n a = w - c) (x : (Fin n → ℤ) × ℤ) :
    _root_.AFT.roundingLoad n c (_root_.AFT.blockTransport n (_root_.AFT.edgeBasisChange n treeBasis) B a x) =
      (treeBasis (B x.1) : Fin (n + 1) → ℤ) + x.2 • w := by
  simp only [_root_.AFT.roundingLoad, _root_.AFT.blockTransport, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.AFT.pathLoad_add, _root_.AFT.pathLoad_smul, _root_.AFT.pathLoad_edgeBasisChange, ha, smul_sub]
  abel
open _root_.P2Mba49f952 renaming h41 → _p2mH41
end AFT
open _root_.P2Mba49f952 renaming h41 → _p2mH41
namespace AFT
end AFT
namespace AFT
end AFT
end
open _root_.P2Mba49f952 renaming h41 → _p2mH41
namespace AFT
end AFT
namespace AFT.RationalRejectionProgram
end AFT.RationalRejectionProgram
section
namespace AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h38 {State : Type*} (test : State → _root_.AFT.RationalRejectionProgram.CountedValue Bool)
    (input : List State) :
    (_root_.AFT.RationalRejectionProgram.countedListAll test input).value=true ↔ ∀ entry∈input,(test entry).value=true := by
  induction input with
  | nil => simp [_root_.AFT.RationalRejectionProgram.countedListAll]
  | cons first rest ih => simp [_root_.AFT.RationalRejectionProgram.countedListAll,ih]
open _root_.P2Mba49f952 renaming h38 → _p2mH38
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h37 (count : ℕ) (test : Fin count → _root_.AFT.RationalRejectionProgram.CountedValue Bool) :
    (_root_.AFT.RationalRejectionProgram.countedFinAll count test).value=true ↔ ∀ index,(test index).value=true := by
  simp [_root_.AFT.RationalRejectionProgram.countedFinAll,_p2mH38]
open _root_.P2Mba49f952 renaming h37 → _p2mH37
end AFT.RationalRejectionProgram
open _root_.P2Mba49f952 renaming h37 → _p2mH37
open _root_.P2Mba49f952 renaming h38 → _p2mH38
end
open _root_.P2Mba49f952 renaming h37 → _p2mH37
open _root_.P2Mba49f952 renaming h38 → _p2mH38
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits
namespace AFT.BinaryArithmetic.RationalBits.ArrayResult
end AFT.BinaryArithmetic.RationalBits.ArrayResult
namespace AFT.BinaryArithmetic.RationalBits.ArrayResult.mk
end AFT.BinaryArithmetic.RationalBits.ArrayResult.mk
namespace AFT.BinaryArithmetic.RationalBits.buildArray
end AFT.BinaryArithmetic.RationalBits.buildArray
namespace AFT.BinaryArithmetic.RationalBits.sumFin
end AFT.BinaryArithmetic.RationalBits.sumFin
namespace AFT.BinaryArithmetic.RationalBits.sumFin.match_1
end AFT.BinaryArithmetic.RationalBits.sumFin.match_1
namespace AFT.BinaryArithmetic.ReadResult
end AFT.BinaryArithmetic.ReadResult
namespace AFT.BinaryArithmetic.ReadResult.mk
end AFT.BinaryArithmetic.ReadResult.mk
namespace AFT.BinaryArithmetic.UnaryCounterResult
end AFT.BinaryArithmetic.UnaryCounterResult
namespace AFT.BinaryArithmetic.UnaryCounterResult.mk
end AFT.BinaryArithmetic.UnaryCounterResult.mk
namespace AFT.BinaryArithmetic.addCounter
end AFT.BinaryArithmetic.addCounter
namespace AFT.BinaryArithmetic.addCounter.match_1
end AFT.BinaryArithmetic.addCounter.match_1
namespace AFT.BinaryArithmetic.doubleCounter
end AFT.BinaryArithmetic.doubleCounter
namespace AFT.BinaryArithmetic.doubleCounter.match_1
end AFT.BinaryArithmetic.doubleCounter.match_1
namespace AFT.BinaryArithmetic.multiplyCounter
end AFT.BinaryArithmetic.multiplyCounter
namespace AFT.BinaryArithmetic.readCounter
end AFT.BinaryArithmetic.readCounter
namespace AFT.BinaryArithmetic.readCounter.match_1
end AFT.BinaryArithmetic.readCounter.match_1
namespace AFT.BinaryArithmetic.readList
end AFT.BinaryArithmetic.readList
namespace AFT.BinaryArithmetic.readList.match_1
end AFT.BinaryArithmetic.readList.match_1
namespace AFT.BinaryArithmetic.readVector
end AFT.BinaryArithmetic.readVector
section
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h29 (count : ℕ) (test : Fin count → _root_.AFT.RationalRejectionProgram.CountedValue Bool) :
    (_root_.AFT.BinaryArithmetic.countFin count test).count=∑ index,if (test index).value then 1 else 0 := by
  induction count with
  | zero => simp [_root_.AFT.BinaryArithmetic.countFin]
  | succ count ih =>
    simp only [_root_.AFT.BinaryArithmetic.countFin,ih,Fin.sum_univ_castSucc]
    split <;> simp_all
open _root_.P2Mba49f952 renaming h29 → _p2mH29
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h30 {count : ℕ} (mask : Vector Bool count) :
    (_root_.AFT.BinaryArithmetic.maskCount mask).count=(_root_.AFT.BinaryArithmetic.maskSet mask).card := by
  simp only [_root_.AFT.BinaryArithmetic.maskCount,_p2mH29,_root_.AFT.BinaryArithmetic.readVector_value,_root_.AFT.BinaryArithmetic.maskSet,Finset.card_filter]
open _root_.P2Mba49f952 renaming h30 → _p2mH30
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h29 → _p2mH29
open _root_.P2Mba49f952 renaming h30 → _p2mH30
end
open _root_.P2Mba49f952 renaming h29 → _p2mH29
open _root_.P2Mba49f952 renaming h30 → _p2mH30
namespace AFT.BinaryArithmetic.signedLe
end AFT.BinaryArithmetic.signedLe
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.finiteChartEquiv
end AFT.BoundaryCalibration.finiteChartEquiv
namespace AFT.BoundaryCalibration.finiteInputEquiv
end AFT.BoundaryCalibration.finiteInputEquiv
section
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h33 (cutoff modulus : ℕ) (boundarySign baselineSign : Bool)
     (boundary baseline : List Bool) (input color : ℕ) :
     (_root_.AFT.BinaryArithmetic.protectedPalette cutoff modulus boundarySign baselineSign boundary baseline input color).value=true ↔
       _root_.AFT.BinaryArithmetic.signedValue boundarySign boundary+max (_root_.AFT.BinaryArithmetic.signedValue baselineSign baseline-
         ((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ))) 0≤(color : ℤ) ∧
       (color : ℤ)<(modulus : ℤ)-_root_.AFT.BinaryArithmetic.signedValue boundarySign boundary+
         min (_root_.AFT.BinaryArithmetic.signedValue baselineSign baseline-((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ))) 0 := by
   let source := _root_.AFT.BinaryArithmetic.divideCounter input (_root_.AFT.BinaryArithmetic.doubleCounter cutoff).count.succ
   let address := _root_.AFT.BinaryArithmetic.canonicalCounter source.remainder
   let shiftRadius := _root_.AFT.BinaryArithmetic.canonicalCounter cutoff
   let modulusBits := _root_.AFT.BinaryArithmetic.canonicalCounter modulus
   let colorBits := _root_.AFT.BinaryArithmetic.canonicalCounter color
   let shiftStart := _root_.AFT.BinaryArithmetic.signedAdd baselineSign false baseline shiftRadius.digits
   let shift := _root_.AFT.BinaryArithmetic.signedAdd shiftStart.negative true shiftStart.digits address.digits
   let lower := _root_.AFT.BinaryArithmetic.signedAdd boundarySign shift.negative boundary shift.digits
   let upperStart := _root_.AFT.BinaryArithmetic.signedAdd false (!boundarySign) modulusBits.digits boundary
   let upper := _root_.AFT.BinaryArithmetic.signedAdd upperStart.negative shift.negative upperStart.digits shift.digits
   have hsource : source.remainder=input%(2*cutoff+1) := by
     dsimp only [source];simpa only [_root_.AFT.BinaryArithmetic.doubleCounter_value] using (_root_.AFT.BinaryArithmetic.divideCounter_value input (_root_.AFT.BinaryArithmetic.doubleCounter cutoff).count.succ (Nat.succ_pos _)).2
   have hstart : _root_.AFT.BinaryArithmetic.signedValue shiftStart.negative shiftStart.digits=_root_.AFT.BinaryArithmetic.signedValue baselineSign baseline+(cutoff : ℤ) := by
     dsimp only [shiftStart];rw [_root_.AFT.BinaryArithmetic.signedAdd_value]
     simp only [shiftRadius,_root_.AFT.BinaryArithmetic.signedValue,Bool.false_eq_true,ite_false,_root_.AFT.BinaryArithmetic.canonicalCounter_value]
   have hshift : _root_.AFT.BinaryArithmetic.signedValue shift.negative shift.digits=_root_.AFT.BinaryArithmetic.signedValue baselineSign baseline-
       ((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ)) := by
     dsimp only [shift];rw [_root_.AFT.BinaryArithmetic.signedAdd_value,hstart]
     simp only [address,_root_.AFT.BinaryArithmetic.signedValue,ite_true,_root_.AFT.BinaryArithmetic.canonicalCounter_value,hsource]
     ring
   have hlower := _root_.AFT.BinaryArithmetic.signedAdd_value boundarySign shift.negative boundary shift.digits
   change _root_.AFT.BinaryArithmetic.signedValue lower.negative lower.digits=_ at hlower
   rw [hshift] at hlower
   have hupperStart : _root_.AFT.BinaryArithmetic.signedValue upperStart.negative upperStart.digits=(modulus : ℤ)-_root_.AFT.BinaryArithmetic.signedValue boundarySign boundary := by
     dsimp only [upperStart];rw [_root_.AFT.BinaryArithmetic.signedAdd_value,_root_.AFT.BinaryArithmetic.signedValue_not]
     simp only [modulusBits,_root_.AFT.BinaryArithmetic.signedValue,Bool.false_eq_true,ite_false,_root_.AFT.BinaryArithmetic.canonicalCounter_value,sub_eq_add_neg]
   have hupper := _root_.AFT.BinaryArithmetic.signedAdd_value upperStart.negative shift.negative upperStart.digits shift.digits
   change _root_.AFT.BinaryArithmetic.signedValue upper.negative upper.digits=_ at hupper
   rw [hupperStart,hshift] at hupper
   have hcolor : _root_.AFT.BinaryArithmetic.signedValue false colorBits.digits=(color : ℤ) := by simp [colorBits,_root_.AFT.BinaryArithmetic.signedValue,_root_.AFT.BinaryArithmetic.canonicalCounter_value]
   change ((_root_.AFT.BinaryArithmetic.signedLe boundarySign false boundary colorBits.digits).value &&
     (_root_.AFT.BinaryArithmetic.signedLe lower.negative false lower.digits colorBits.digits).value &&
     !(_root_.AFT.BinaryArithmetic.signedLe upperStart.negative false upperStart.digits colorBits.digits).value &&
     !(_root_.AFT.BinaryArithmetic.signedLe upper.negative false upper.digits colorBits.digits).value)=true ↔ _
   simp only [Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,_root_.AFT.BinaryArithmetic.signedLe_value,hcolor,hlower,hupperStart,hupper]
   omega
open _root_.P2Mba49f952 renaming h33 → _p2mH33
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h33 → _p2mH33
end
open _root_.P2Mba49f952 renaming h33 → _p2mH33
namespace AFT.BinaryArithmetic.SignedResult
end AFT.BinaryArithmetic.SignedResult
namespace AFT.BinaryArithmetic.SignedResult.mk
end AFT.BinaryArithmetic.SignedResult.mk
namespace AFT.BinaryArithmetic.signedAdd
end AFT.BinaryArithmetic.signedAdd
namespace AFT.BinaryArithmetic.storeData
end AFT.BinaryArithmetic.storeData
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
namespace IntegerBits
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h1 (count : ℕ) (term : Fin count → _root_.AFT.RationalRejectionProgram.CountedValue _root_.AFT.BinaryArithmetic.IntegerBits) :
    (_root_.AFT.BinaryArithmetic.IntegerBits.sumFin count term).value.decode=∑ index,(term index).value.decode := by
  induction count with
  | zero => simp [_root_.AFT.BinaryArithmetic.IntegerBits.sumFin]
  | succ count ih => simp only [_root_.AFT.BinaryArithmetic.IntegerBits.sumFin,_root_.AFT.BinaryArithmetic.IntegerBits.add_value,ih,Fin.sum_univ_castSucc]
open _root_.P2Mba49f952 renaming h1 → AFT.BinaryArithmetic.IntegerBits.sumFin_value
open _root_.P2Mba49f952 renaming h1 → _p2mH1
end IntegerBits
open _root_.P2Mba49f952 renaming h1 → AFT.BinaryArithmetic.IntegerBits.sumFin_value
open _root_.P2Mba49f952 renaming h1 → _p2mH1
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h1 → AFT.BinaryArithmetic.IntegerBits.sumFin_value
open _root_.P2Mba49f952 renaming h1 → _p2mH1
end
open _root_.P2Mba49f952 renaming h1 → AFT.BinaryArithmetic.IntegerBits.sumFin_value
open _root_.P2Mba49f952 renaming h1 → _p2mH1
namespace AFT.BinaryArithmetic.IntegerBits
end AFT.BinaryArithmetic.IntegerBits
namespace AFT.BinaryArithmetic.IntegerBits.decode
end AFT.BinaryArithmetic.IntegerBits.decode
namespace AFT.BinaryArithmetic.IntegerBits.mk
end AFT.BinaryArithmetic.IntegerBits.mk
namespace AFT.BinaryArithmetic.IntegerBits.multiply
end AFT.BinaryArithmetic.IntegerBits.multiply
namespace AFT.BinaryArithmetic.IntegerBits.subtract
end AFT.BinaryArithmetic.IntegerBits.subtract
namespace AFT.BinaryArithmetic.IntegerBits.sumFin
end AFT.BinaryArithmetic.IntegerBits.sumFin
namespace AFT.BinaryArithmetic.IntegerBits.sumFin.match_1
end AFT.BinaryArithmetic.IntegerBits.sumFin.match_1
namespace AFT.BinaryArithmetic.IntegerBits.zero
end AFT.BinaryArithmetic.IntegerBits.zero
section
namespace AFT.BinaryArithmetic.IntegerBits
open AFT.RationalRejectionProgram
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h0 (input : _root_.AFT.BinaryArithmetic.IntegerBits) (modulus : List Bool) (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus)
    (hdiv : (_root_.AFT.BinaryArithmetic.value modulus : ℤ) ∣ input.decode) :
    (_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient input modulus).value.decode=input.decode/(_root_.AFT.BinaryArithmetic.value modulus : ℤ) := by
  have hv := (_root_.AFT.BinaryArithmetic.divide_value input.digits modulus hq).1
  cases hs : input.negative with
  | false => simp only [_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient,_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,Bool.false_eq_true,ite_false,hv,Int.natCast_ediv]
  | true =>
      have hd : (_root_.AFT.BinaryArithmetic.value modulus : ℤ) ∣ (_root_.AFT.BinaryArithmetic.value input.digits : ℤ) := by
        simpa only [_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,ite_true,dvd_neg] using hdiv
      simp only [_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient,_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,ite_true,hv,Int.natCast_ediv,Int.neg_ediv_of_dvd hd]
open _root_.P2Mba49f952 renaming h0 → _p2mH0
end AFT.BinaryArithmetic.IntegerBits
open _root_.P2Mba49f952 renaming h0 → _p2mH0
end
open _root_.P2Mba49f952 renaming h0 → _p2mH0
namespace AFT.blockTransport
end AFT.blockTransport
namespace AFT.injectionColumn
end AFT.injectionColumn
namespace AFT.pathLoad
end AFT.pathLoad
namespace AFT.pathLoad.match_1
end AFT.pathLoad.match_1
namespace AFT.roundingLoad
end AFT.roundingLoad
namespace AFT.totalCharge
end AFT.totalCharge
namespace AFT.transportBlockMatrix
end AFT.transportBlockMatrix
section
namespace AFT
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h42 {α : Type*} {count : ℕ} (f : Fin count → α) :
    (Vector.ofFn f).get=f := by
  funext index
  exact Vector.get_ofFn f index
open _root_.P2Mba49f952 renaming h42 → _p2mH42
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h39 (count : ℕ) (load : Vector ℤ (count+1))
    (hload : _root_.AFT.totalCharge load.get=0) : _root_.AFT.pathLoad count (_root_.AFT.pathInverseProgram count load).value.get=load.get := by
  induction count with
  | zero =>
    funext index
    have hi : index=0 := Fin.ext (by omega)
    subst index
    simpa [_root_.AFT.totalCharge,_root_.AFT.pathLoad] using hload.symm
  | succ count ih =>
    let tail := Vector.ofFn (fun index : Fin (count+1) => load.get index.succ+if index=0 then load.get 0 else 0)
    have ht : _root_.AFT.totalCharge tail.get=0 := by
      have hsum : load.get 0+(∑ index : Fin (count+1),load.get index.succ)=0 := by
        simpa only [_root_.AFT.totalCharge,Fin.sum_univ_succ] using hload
      simpa [tail,_root_.AFT.totalCharge,Finset.sum_add_distrib,add_comm] using hsum
    have hh := ih tail ht
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simp only [_root_.AFT.pathInverseProgram,Vector.get_ofFn,_root_.AFT.pathLoad,Fin.cons_zero]
    · simp only [_root_.AFT.pathInverseProgram,_p2mH42,_root_.AFT.pathLoad,Fin.cons_succ,Fin.tail_cons]
      change _root_.AFT.pathLoad count (_root_.AFT.pathInverseProgram count tail).value.get rest -
        (if rest=0 then load.get 0 else 0)=load.get rest.succ
      rw [hh]
      simp [tail]
open _root_.P2Mba49f952 renaming h39 → _p2mH39
noncomputable section
end
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h40 (count : ℕ) (modulus : ℤ) (injection load : Vector ℤ (count+1))
    (hinjection : _root_.AFT.totalCharge injection.get=modulus) (hload : modulus ∣ _root_.AFT.totalCharge load.get) :
    _root_.AFT.roundingLoad count injection.get
      ((_root_.AFT.roundingInverseProgram count modulus injection load).value.1.get,
        (_root_.AFT.roundingInverseProgram count modulus injection load).value.2)=load.get := by
  let charge := _root_.AFT.totalCharge load.get/modulus
  have hcharge : charge*modulus=_root_.AFT.totalCharge load.get := Int.ediv_mul_cancel hload
  let shifted := Vector.ofFn (fun index => load.get index-charge*injection.get index)
  have hshift : _root_.AFT.totalCharge shifted.get=0 := by
    rw [_p2mH42]
    change _root_.AFT.totalCharge (load.get-charge • injection.get)=0
    rw [_root_.AFT.totalCharge_sub,_root_.AFT.totalCharge_smul,hinjection,hcharge,sub_self]
  have hh := _p2mH39 count shifted hshift
  change _root_.AFT.pathLoad count (_root_.AFT.pathInverseProgram count shifted).value.get+charge • injection.get=load.get
  rw [hh]
  funext index
  simp only [shifted,Vector.get_ofFn,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring
open _root_.P2Mba49f952 renaming h40 → _p2mH40
noncomputable section
end
end AFT
open _root_.P2Mba49f952 renaming h39 → _p2mH39
open _root_.P2Mba49f952 renaming h40 → _p2mH40
open _root_.P2Mba49f952 renaming h42 → _p2mH42
end
open _root_.P2Mba49f952 renaming h39 → _p2mH39
open _root_.P2Mba49f952 renaming h40 → _p2mH40
open _root_.P2Mba49f952 renaming h42 → _p2mH42
namespace AFT.BinaryArithmetic.IntegerBits.exactQuotient
end AFT.BinaryArithmetic.IntegerBits.exactQuotient
namespace AFT.BinaryArithmetic.IntegerBits.residue
end AFT.BinaryArithmetic.IntegerBits.residue
namespace AFT.IntegerCoordinateRun
end AFT.IntegerCoordinateRun
namespace AFT.IntegerCoordinateRun.mk
end AFT.IntegerCoordinateRun.mk
namespace AFT.IntegerLoadRun
end AFT.IntegerLoadRun
namespace AFT.IntegerLoadRun.mk
end AFT.IntegerLoadRun.mk
namespace AFT.IntegerVectorRun
end AFT.IntegerVectorRun
namespace AFT.IntegerVectorRun.mk
end AFT.IntegerVectorRun.mk
namespace AFT.pathForwardProgram
end AFT.pathForwardProgram
namespace AFT.pathForwardProgram.match_1
end AFT.pathForwardProgram.match_1
namespace AFT.pathInverseProgram
end AFT.pathInverseProgram
namespace AFT.pathInverseProgram.match_1
end AFT.pathInverseProgram.match_1
namespace AFT.roundingInverseProgram
end AFT.roundingInverseProgram
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h20 {count : ℕ} (load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+2)) (first : _root_.AFT.BinaryArithmetic.IntegerBits)
    (index : Fin (count+1)) :
    ((_root_.AFT.BinaryArithmetic.binaryPathTail load first).value.get index).decode=(load.get index.succ).decode+
      if index=0 then first.decode else 0 := by
  simp only [_root_.AFT.BinaryArithmetic.binaryPathTail,_root_.AFT.BinaryArithmetic.storeData_get,_root_.AFT.BinaryArithmetic.pathTailEntry,_root_.AFT.BinaryArithmetic.readVector_value]
  by_cases hi : index=0
  · subst index;simp [_root_.AFT.BinaryArithmetic.IntegerBits.add_value]
  · have hi' : index.val ≠ 0 := fun hh => hi (Fin.ext hh)
    simp [hi,hi']
open _root_.P2Mba49f952 renaming h20 → _p2mH20
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h19 (count : ℕ) (load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (index : Fin count) :
    ((_root_.AFT.BinaryArithmetic.binaryPathInverse count load).value.get index).decode=
      (_root_.AFT.pathInverseProgram count (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode)).value.get index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      have ht : (_root_.AFT.BinaryArithmetic.binaryPathTail load (load.get 0)).value.map _root_.AFT.BinaryArithmetic.IntegerBits.decode=
          Vector.ofFn (fun slot : Fin (count+1) => (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get slot.succ+
            if slot=0 then (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get 0 else 0) := by
        apply Vector.ext
        intro slot hs
        change ((_root_.AFT.BinaryArithmetic.binaryPathTail load (load.get 0)).value.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get ⟨slot,hs⟩=
          (Vector.ofFn (fun slot : Fin (count+1) => (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get slot.succ+
            if slot=0 then (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get 0 else 0)).get ⟨slot,hs⟩
        simp only [Vector.get_map,Vector.get_ofFn,_p2mH20]
      refine Fin.cases ?_ (fun rest => ?_) index
      · simp only [_root_.AFT.BinaryArithmetic.binaryPathInverse,_root_.AFT.BinaryArithmetic.storeData_get,Fin.cases_zero,_root_.AFT.BinaryArithmetic.readVector_value,
          _root_.AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_zero,Vector.get_map]
      · simp only [_root_.AFT.BinaryArithmetic.binaryPathInverse,_root_.AFT.BinaryArithmetic.storeData_get,Fin.cases_succ,_root_.AFT.BinaryArithmetic.readVector_value,
          _root_.AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_succ]
        rw [ih,ht]
open _root_.P2Mba49f952 renaming h19 → _p2mH19
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h19 → _p2mH19
open _root_.P2Mba49f952 renaming h20 → _p2mH20
end
open _root_.P2Mba49f952 renaming h19 → _p2mH19
open _root_.P2Mba49f952 renaming h20 → _p2mH20
namespace AFT.BinaryArithmetic.binaryPathInverse
end AFT.BinaryArithmetic.binaryPathInverse
namespace AFT.BinaryArithmetic.binaryPathInverse.match_1
end AFT.BinaryArithmetic.binaryPathInverse.match_1
namespace AFT.BinaryArithmetic.binaryPathInverseWork
end AFT.BinaryArithmetic.binaryPathInverseWork
namespace AFT.BinaryArithmetic.binaryPathTail
end AFT.BinaryArithmetic.binaryPathTail
namespace AFT.BinaryArithmetic.pathTailEntry
end AFT.BinaryArithmetic.pathTailEntry
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h26 {size : ℕ} (charge : _root_.AFT.BinaryArithmetic.IntegerBits) (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits size)
    (index : Fin size) :
    ((_root_.AFT.BinaryArithmetic.binaryShiftedLoad charge injection load).value.get index).decode=
      (load.get index).decode-charge.decode*(injection.get index).decode := by
  simp only [_root_.AFT.BinaryArithmetic.binaryShiftedLoad,_root_.AFT.BinaryArithmetic.storeData_get,_root_.AFT.BinaryArithmetic.shiftedLoadEntry,_root_.AFT.BinaryArithmetic.IntegerBits.subtract_value,
    _root_.AFT.BinaryArithmetic.IntegerBits.multiply_value,_root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h26 → _p2mH26
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h25 (count : ℕ) (modulus : List Bool)
    (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus)
    (hdiv : (_root_.AFT.BinaryArithmetic.value modulus : ℤ) ∣ ∑ index,(load.get index).decode) :
    (_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).charge.decode=
      (_root_.AFT.roundingInverseProgram count (_root_.AFT.BinaryArithmetic.value modulus) (injection.map _root_.AFT.BinaryArithmetic.IntegerBits.decode) (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode)).value.2 ∧
    ∀ index,((_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).edges.get index).decode=
      ((_root_.AFT.roundingInverseProgram count (_root_.AFT.BinaryArithmetic.value modulus) (injection.map _root_.AFT.BinaryArithmetic.IntegerBits.decode) (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode)).value.1.get index) := by
  have htotal : (_root_.AFT.BinaryArithmetic.IntegerBits.sumFin (count+1) (_root_.AFT.BinaryArithmetic.readVector _root_.AFT.BinaryArithmetic.IntegerBits.zero load)).value.decode=
      ∑ index,(load.get index).decode := by rw [_p2mH1];simp only [_root_.AFT.BinaryArithmetic.readVector_value]
  have hc := _p2mH0 (_root_.AFT.BinaryArithmetic.IntegerBits.sumFin (count+1) (_root_.AFT.BinaryArithmetic.readVector _root_.AFT.BinaryArithmetic.IntegerBits.zero load)).value
    modulus hq (by rw [htotal];exact hdiv)
  rw [htotal] at hc
  refine ⟨?_,?_⟩
  · simpa only [_root_.AFT.BinaryArithmetic.binaryRoundingInverse,_root_.AFT.roundingInverseProgram,Vector.get_map] using hc
  · intro index
    simp only [_root_.AFT.BinaryArithmetic.binaryRoundingInverse,_p2mH19,_root_.AFT.roundingInverseProgram,Vector.get_map]
    congr 3
    apply Vector.ext
    intro slot hs
    change ((_root_.AFT.BinaryArithmetic.binaryShiftedLoad _ injection load).value.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get ⟨slot,hs⟩=
      (Vector.ofFn (fun index : Fin (count+1) => (load.get index).decode-
        ((∑ point : Fin (count+1),(load.get point).decode)/(_root_.AFT.BinaryArithmetic.value modulus : ℤ))*(injection.get index).decode)).get ⟨slot,hs⟩
    simp only [Vector.get_map,Vector.get_ofFn,_p2mH26,hc]
open _root_.P2Mba49f952 renaming h25 → _p2mH25
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h25 → _p2mH25
open _root_.P2Mba49f952 renaming h26 → _p2mH26
end
open _root_.P2Mba49f952 renaming h25 → _p2mH25
open _root_.P2Mba49f952 renaming h26 → _p2mH26
namespace AFT.BinaryArithmetic.BinaryCoordinateResult
end AFT.BinaryArithmetic.BinaryCoordinateResult
namespace AFT.BinaryArithmetic.BinaryCoordinateResult.mk
end AFT.BinaryArithmetic.BinaryCoordinateResult.mk
namespace AFT.BinaryArithmetic.binaryRoundingInverse
end AFT.BinaryArithmetic.binaryRoundingInverse
namespace AFT.BinaryArithmetic.binaryShiftedLoad
end AFT.BinaryArithmetic.binaryShiftedLoad
namespace AFT.BinaryArithmetic.shiftedLoadEntry
end AFT.BinaryArithmetic.shiftedLoadEntry
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h35 {size : ℕ} (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.IntegerBits size) size)
     (column row : Fin size) : (_root_.AFT.BinaryArithmetic.readIntegerMatrix matrix column row).value=(matrix.get column).get row := by
   simp only [_root_.AFT.BinaryArithmetic.readIntegerMatrix,_root_.AFT.BinaryArithmetic.readList_value]
   rw [List.getElem?_eq_getElem (by simp only [Vector.length_toList];exact column.isLt)]
   simp only [Vector.getElem_toList,_root_.AFT.BinaryArithmetic.readVector_value]
   rfl
open _root_.P2Mba49f952 renaming h35 → _p2mH35
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h21 (count : ℕ) (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column vertex : Fin (count+1)) :
     (_root_.AFT.BinaryArithmetic.binaryPermutedColumn count matrix permutation column).value.get vertex=
       (matrix.get column).get (permutation.get vertex) := by
   simp only [_root_.AFT.BinaryArithmetic.binaryPermutedColumn,_root_.AFT.BinaryArithmetic.storeData_get,_p2mH35,_root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h21 → _p2mH21
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h21 → _p2mH21
open _root_.P2Mba49f952 renaming h35 → _p2mH35
end
open _root_.P2Mba49f952 renaming h21 → _p2mH21
open _root_.P2Mba49f952 renaming h35 → _p2mH35
namespace AFT.BinaryArithmetic.normalize
end AFT.BinaryArithmetic.normalize
namespace AFT.BinaryArithmetic.normalize.match_1
end AFT.BinaryArithmetic.normalize.match_1
namespace AFT.PermutationProgram
end AFT.PermutationProgram
namespace AFT.PermutationProgram.CountedPermutation
end AFT.PermutationProgram.CountedPermutation
namespace AFT.PermutationProgram.CountedPermutation.mk
end AFT.PermutationProgram.CountedPermutation.mk
namespace AFT.PermutationProgram.bitValue
end AFT.PermutationProgram.bitValue
namespace AFT.PermutationProgram.bitValue.match_1
end AFT.PermutationProgram.bitValue.match_1
namespace AFT.PermutationProgram.countedBucket
end AFT.PermutationProgram.countedBucket
namespace AFT.PermutationProgram.countedBucket.match_1
end AFT.PermutationProgram.countedBucket.match_1
namespace AFT.PermutationProgram.countedChoice
end AFT.PermutationProgram.countedChoice
namespace AFT.PermutationProgram.countedRows
end AFT.PermutationProgram.countedRows
namespace AFT.PermutationProgram.countedRows.match_1
end AFT.PermutationProgram.countedRows.match_1
namespace AFT.PermutationProgram.powerTwo
end AFT.PermutationProgram.powerTwo
namespace AFT.PermutationProgram.powerTwo.match_1
end AFT.PermutationProgram.powerTwo.match_1
namespace AFT.PermutationProgram.uniformCounts
end AFT.PermutationProgram.uniformCounts
section
namespace AFT.BinaryArithmetic
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h34 (bits : ℕ) (word : Fin bits → Fin 2) :
    (_root_.AFT.BinaryArithmetic.readBitTape bits word).digits.length=bits := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [_root_.AFT.BinaryArithmetic.readBitTape,List.length_cons,ih]
open _root_.P2Mba49f952 renaming h34 → _p2mH34
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h34 → _p2mH34
end
open _root_.P2Mba49f952 renaming h34 → _p2mH34
namespace AFT.BinaryArithmetic.RationalBits.ceilNatural
end AFT.BinaryArithmetic.RationalBits.ceilNatural
namespace AFT.BinaryArithmetic.RationalBits.ceil_fraction
end AFT.BinaryArithmetic.RationalBits.ceil_fraction
namespace AFT.BinaryArithmetic.RationalBits.factorial
end AFT.BinaryArithmetic.RationalBits.factorial
namespace AFT.BinaryArithmetic.RationalBits.factorialWorkStep
end AFT.BinaryArithmetic.RationalBits.factorialWorkStep
namespace AFT.BinaryArithmetic.RationalBits.half
end AFT.BinaryArithmetic.RationalBits.half
namespace AFT.BinaryArithmetic.RationalBits.maxZero
end AFT.BinaryArithmetic.RationalBits.maxZero
namespace AFT.BinaryArithmetic.RationalBits.ofCounter
end AFT.BinaryArithmetic.RationalBits.ofCounter
namespace AFT.BinaryArithmetic.RationalBits.power
end AFT.BinaryArithmetic.RationalBits.power
namespace AFT.BinaryArithmetic.RationalBits.power.match_1
end AFT.BinaryArithmetic.RationalBits.power.match_1
namespace AFT.BinaryArithmetic.RationalBits.quotient
end AFT.BinaryArithmetic.RationalBits.quotient
namespace AFT.BinaryArithmetic.RationalBits.sumRange
end AFT.BinaryArithmetic.RationalBits.sumRange
namespace AFT.BinaryArithmetic.RationalBits.third
end AFT.BinaryArithmetic.RationalBits.third
namespace AFT.RationalAcceptanceCoin
end AFT.RationalAcceptanceCoin
namespace AFT.RationalAcceptanceCoin.clipped
end AFT.RationalAcceptanceCoin.clipped
namespace AFT.RationalAcceptanceCoin.count
end AFT.RationalAcceptanceCoin.count
namespace AFT.RationalAcceptanceCoin.counts
end AFT.RationalAcceptanceCoin.counts
section
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h12 (input : _root_.AFT.BinaryArithmetic.RationalBits) :
    (_root_.AFT.BinaryArithmetic.RationalBits.clipUnit input).data.decode=_root_.AFT.RationalAcceptanceCoin.clipped input.decode := by
  have hd : (0 : ℚ)<_root_.AFT.BinaryArithmetic.value input.denominator := by exact_mod_cast input.denominator_positive
  cases hs : input.negative with
  | true =>
      have hn : input.decode≤ 0 := by
        rw [_root_.AFT.BinaryArithmetic.RationalBits.decode_fraction]
        simp only [_root_.AFT.BinaryArithmetic.signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hd.le
      simp only [_root_.AFT.BinaryArithmetic.RationalBits.clipUnit,hs,ite_true,_root_.AFT.BinaryArithmetic.RationalBits.zero_value,_root_.AFT.RationalAcceptanceCoin.clipped,max_eq_right hn,
        min_eq_right (by norm_num : (0 : ℚ)≤ 1)]
  | false =>
      have he : input.decode=(_root_.AFT.BinaryArithmetic.value input.numerator : ℚ)/(_root_.AFT.BinaryArithmetic.value input.denominator : ℚ) := by
        rw [_root_.AFT.BinaryArithmetic.RationalBits.decode_fraction]
        simp only [_root_.AFT.BinaryArithmetic.signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast]
      have hn : 0≤ input.decode := by rw [he];positivity
      simp only [_root_.AFT.BinaryArithmetic.RationalBits.clipUnit,hs,ite_false,Bool.false_eq_true,_root_.AFT.RationalAcceptanceCoin.clipped,max_eq_left hn]
      split <;> rename_i hb
      · have hc := (_root_.AFT.BinaryArithmetic.subtract_borrow input.numerator input.denominator).mp hb
        have hh : input.decode<1 := by rw [he,div_lt_one hd];exact_mod_cast hc
        exact (min_eq_right hh.le).symm
      · have hc : _root_.AFT.BinaryArithmetic.value input.denominator≤ _root_.AFT.BinaryArithmetic.value input.numerator := by
          exact Nat.le_of_not_gt (fun hh => hb ((_root_.AFT.BinaryArithmetic.subtract_borrow input.numerator input.denominator).mpr hh))
        have hh : 1≤ input.decode := by rw [he,le_div_iff₀ hd];simpa only [one_mul] using (show (_root_.AFT.BinaryArithmetic.value input.denominator : ℚ)≤_root_.AFT.BinaryArithmetic.value input.numerator by exact_mod_cast hc)
        rw [_root_.AFT.BinaryArithmetic.RationalBits.one_value,min_eq_left hh]
open _root_.P2Mba49f952 renaming h12 → _p2mH12
end AFT.BinaryArithmetic.RationalBits
open _root_.P2Mba49f952 renaming h12 → _p2mH12
end
open _root_.P2Mba49f952 renaming h12 → _p2mH12
namespace AFT.BinaryArithmetic.CounterDivisionResult
end AFT.BinaryArithmetic.CounterDivisionResult
namespace AFT.BinaryArithmetic.CounterDivisionResult.mk
end AFT.BinaryArithmetic.CounterDivisionResult.mk
namespace AFT.BinaryArithmetic.binaryPoolScan
end AFT.BinaryArithmetic.binaryPoolScan
namespace AFT.BinaryArithmetic.binaryPoolScan.match_1
end AFT.BinaryArithmetic.binaryPoolScan.match_1
namespace AFT.BinaryArithmetic.binaryRunPoolScan
end AFT.BinaryArithmetic.binaryRunPoolScan
namespace AFT.BinaryArithmetic.differenceCounter
end AFT.BinaryArithmetic.differenceCounter
namespace AFT.BinaryArithmetic.differenceCounter.match_1
end AFT.BinaryArithmetic.differenceCounter.match_1
namespace AFT.BinaryArithmetic.divideCounter
end AFT.BinaryArithmetic.divideCounter
namespace AFT.blockVertexSplit
end AFT.blockVertexSplit
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h27 (legs rest : ℕ) (index : Fin (legs*3+rest)) :
     (_root_.AFT.BinaryArithmetic.binaryVertexCode legs rest index).value=(_root_.AFT.blockVertexNumbering legs rest).symm index := by
   apply (_root_.AFT.blockVertexNumbering legs rest).injective
   rw [Equiv.apply_symm_apply]
   unfold _root_.AFT.BinaryArithmetic.binaryVertexCode
   try dsimp only
   split
   · rename_i h
     apply Fin.ext
     change (_root_.AFT.BinaryArithmetic.divideCounter index.val 3).remainder+3*(_root_.AFT.BinaryArithmetic.divideCounter index.val 3).quotient=index.val
     rw [(_root_.AFT.BinaryArithmetic.divideCounter_value index.val 3 (by omega)).1,(_root_.AFT.BinaryArithmetic.divideCounter_value index.val 3 (by omega)).2]
     exact Nat.mod_add_div _ _
   · rename_i h
     apply Fin.ext
     change legs*3+(0+1*(_root_.AFT.BinaryArithmetic.differenceCounter index.val (_root_.AFT.BinaryArithmetic.multiplyCounter legs 3).count).count)=index.val
     simp only [Nat.zero_add,Nat.one_mul]
     rw [_root_.AFT.BinaryArithmetic.differenceCounter_value,_root_.AFT.BinaryArithmetic.multiplyCounter_value]
     have hi : legs*3 ≤ index.val := by
       have hh : ¬ index.val<(_root_.AFT.BinaryArithmetic.multiplyCounter legs 3).count := fun hi => h ((_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mpr hi)
       rw [_root_.AFT.BinaryArithmetic.multiplyCounter_value] at hh
       omega
     omega
open _root_.P2Mba49f952 renaming h27 → _p2mH27
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h24 (legs rest : ℕ) (index : Fin legs⊕Fin rest) :
     (_root_.AFT.BinaryArithmetic.binaryRootAddress legs rest index).value=_root_.AFT.blockNumbering legs rest index := by
   cases index <;> apply Fin.ext <;> simp [_root_.AFT.BinaryArithmetic.binaryRootAddress,_root_.AFT.blockNumbering,_root_.AFT.BinaryArithmetic.addCounter_value]
open _root_.P2Mba49f952 renaming h24 → _p2mH24
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h24 → _p2mH24
open _root_.P2Mba49f952 renaming h27 → _p2mH27
end
open _root_.P2Mba49f952 renaming h24 → _p2mH24
open _root_.P2Mba49f952 renaming h27 → _p2mH27
namespace AFT.BinaryArithmetic.countFin
end AFT.BinaryArithmetic.countFin
namespace AFT.BinaryArithmetic.countFin.match_1
end AFT.BinaryArithmetic.countFin.match_1
namespace AFT.BinaryArithmetic.equalCounter
end AFT.BinaryArithmetic.equalCounter
namespace AFT.BinaryArithmetic.equalCounter.match_1
end AFT.BinaryArithmetic.equalCounter.match_1
namespace AFT.BinaryArithmetic.maskCount
end AFT.BinaryArithmetic.maskCount
namespace AFT.BinaryArithmetic.maskSet
end AFT.BinaryArithmetic.maskSet
namespace AFT.BoundaryCalibration.chartExpectationHeight
end AFT.BoundaryCalibration.chartExpectationHeight
namespace AFT.BoundaryCalibration.chartProjectionHeight
end AFT.BoundaryCalibration.chartProjectionHeight
section
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram AFT.BoundaryCalibration
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h13 (first second : _root_.AFT.BinaryArithmetic.RationalBits) :
    (_root_.AFT.BinaryArithmetic.RationalBits.difference first second).data.decode=first.decode-second.decode := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.difference,_root_.AFT.BinaryArithmetic.RationalBits.add_value,_root_.AFT.BinaryArithmetic.RationalBits.negate_value,sub_eq_add_neg]
open _root_.P2Mba49f952 renaming h13 → _p2mH13
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h8 (charts : ℕ) (term : Fin charts → _root_.AFT.BinaryArithmetic.RationalResult) :
    (_root_.AFT.BinaryArithmetic.RationalBits.chartExpectation charts term).data.decode=_root_.AFT.BoundaryCalibration.chartExpectationProgram charts (fun index => (term index).data.decode) := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartExpectation,_root_.AFT.BinaryArithmetic.RationalBits.quotient_value,_root_.AFT.BinaryArithmetic.RationalBits.sumFin_value,_root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value,_root_.AFT.BoundaryCalibration.chartExpectationProgram]
open _root_.P2Mba49f952 renaming h8 → _p2mH8
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h3 {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits charts)
    (color : Fin colors) (point : Fin charts) :
    (_root_.AFT.BinaryArithmetic.RationalBits.chartConditionalTerm feature profile color point).data.decode=
      if feature.get point=color then (profile.get point).decode else 0 := by
  have he : (_root_.AFT.BinaryArithmetic.equalCounter (_root_.AFT.BinaryArithmetic.readVector 0 feature point).value.val color.val).value=true ↔ feature.get point=color := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value,_root_.AFT.BinaryArithmetic.readVector_value]
    exact Fin.val_injective.eq_iff
  by_cases hh : feature.get point=color
  · have hb := he.mpr hh
    simp only [_root_.AFT.BinaryArithmetic.readVector_value] at hb
    simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartConditionalTerm,_root_.AFT.BinaryArithmetic.readVector_value,hb,ite_true,if_pos hh]
  · have hb : (_root_.AFT.BinaryArithmetic.equalCounter (_root_.AFT.BinaryArithmetic.readVector 0 feature point).value.val color.val).value=false := by
      cases hv : (_root_.AFT.BinaryArithmetic.equalCounter (_root_.AFT.BinaryArithmetic.readVector 0 feature point).value.val color.val).value
      · rfl
      · exact False.elim (hh (he.mp hv))
    simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartConditionalTerm,hb,Bool.false_eq_true,ite_false,if_neg hh,_root_.AFT.BinaryArithmetic.RationalBits.zero_value]
open _root_.P2Mba49f952 renaming h3 → _p2mH3
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h4 {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) (color : Fin colors) :
    (_root_.AFT.BinaryArithmetic.RationalBits.chartConditional feature profile color).data.decode=
      _root_.AFT.BoundaryCalibration.chartConditionalProgram charts colors feature.get (fun index => (profile.get index).decode) color := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartConditional,_root_.AFT.BinaryArithmetic.RationalBits.multiply_value,_root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value,_p2mH8,_p2mH3,_root_.AFT.BoundaryCalibration.chartConditionalProgram]
open _root_.P2Mba49f952 renaming h4 → _p2mH4
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h2 {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) (color : Fin colors) :
    (_root_.AFT.BinaryArithmetic.RationalBits.chartAllowedTerm feature allowed profile color).data.decode=
      if color∈_root_.AFT.BinaryArithmetic.maskSet allowed then _root_.AFT.BoundaryCalibration.chartConditionalProgram charts colors feature.get
        (fun index => (profile.get index).decode) color else 0 := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartAllowedTerm,_root_.AFT.BinaryArithmetic.readVector_value,_root_.AFT.BinaryArithmetic.maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
  split <;> simp_all only [_p2mH4,_root_.AFT.BinaryArithmetic.RationalBits.zero_value]
open _root_.P2Mba49f952 renaming h2 → _p2mH2
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h9 {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) (point : Fin charts) :
    (_root_.AFT.BinaryArithmetic.RationalBits.chartFeature feature allowed profile point).data.decode=
      _root_.AFT.BoundaryCalibration.chartFeatureProgram charts colors feature.get (_root_.AFT.BinaryArithmetic.maskSet allowed) (fun index => (profile.get index).decode) point := by
  have htotal : (_root_.AFT.BinaryArithmetic.RationalBits.sumFin colors (_root_.AFT.BinaryArithmetic.RationalBits.chartAllowedTerm feature allowed profile)).data.decode=
      ∑ color∈_root_.AFT.BinaryArithmetic.maskSet allowed,_root_.AFT.BoundaryCalibration.chartConditionalProgram charts colors feature.get
        (fun index => (profile.get index).decode) color := by
    rw [_root_.AFT.BinaryArithmetic.RationalBits.sumFin_value]
    simp only [_p2mH2,_root_.AFT.BinaryArithmetic.maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [Finset.sum_filter]
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartFeature,_root_.AFT.BinaryArithmetic.readVector_value,_root_.AFT.BoundaryCalibration.chartFeatureProgram]
  split <;> rename_i hactive
  · simp only [_p2mH13,_p2mH4,_root_.AFT.BinaryArithmetic.RationalBits.quotient_value,htotal,_root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value,_p2mH30]
    rw [if_pos (by simpa only [_root_.AFT.BinaryArithmetic.maskSet,Finset.mem_filter,Finset.mem_univ,true_and] using hactive)]
  · simp only [_root_.AFT.BinaryArithmetic.RationalBits.zero_value]
    rw [if_neg (by simpa only [_root_.AFT.BinaryArithmetic.maskSet,Finset.mem_filter,Finset.mem_univ,true_and] using hactive)]
open _root_.P2Mba49f952 renaming h9 → _p2mH9
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h10 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) (point : Fin charts) :
    (_root_.AFT.BinaryArithmetic.RationalBits.chartProjection feature allowed profile point).data.decode=
      _root_.AFT.BoundaryCalibration.chartProjectionProgram charts colors features (fun index => (feature.get index).get)
        (fun index => _root_.AFT.BinaryArithmetic.maskSet (allowed.get index)) (fun index => (profile.get index).decode) point := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartProjection,_root_.AFT.BinaryArithmetic.RationalBits.add_value,_p2mH8,_root_.AFT.BinaryArithmetic.RationalBits.sumFin_value,_root_.AFT.BinaryArithmetic.RationalBits.chartProjectionTerm,
    _root_.AFT.BinaryArithmetic.readVector_value,_p2mH9,_root_.AFT.BoundaryCalibration.chartProjectionProgram]
open _root_.P2Mba49f952 renaming h10 → _p2mH10
end AFT.BinaryArithmetic.RationalBits
open _root_.P2Mba49f952 renaming h2 → _p2mH2
open _root_.P2Mba49f952 renaming h3 → _p2mH3
open _root_.P2Mba49f952 renaming h4 → _p2mH4
open _root_.P2Mba49f952 renaming h8 → _p2mH8
open _root_.P2Mba49f952 renaming h9 → _p2mH9
open _root_.P2Mba49f952 renaming h10 → _p2mH10
open _root_.P2Mba49f952 renaming h13 → _p2mH13
end
open _root_.P2Mba49f952 renaming h2 → _p2mH2
open _root_.P2Mba49f952 renaming h3 → _p2mH3
open _root_.P2Mba49f952 renaming h4 → _p2mH4
open _root_.P2Mba49f952 renaming h8 → _p2mH8
open _root_.P2Mba49f952 renaming h9 → _p2mH9
open _root_.P2Mba49f952 renaming h10 → _p2mH10
open _root_.P2Mba49f952 renaming h13 → _p2mH13
namespace AFT.RationalNumerics
end AFT.RationalNumerics
section
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h17 {count : ℕ} (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.RationalBits count) count)
    (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits count) (output input : Fin count) :
    (_root_.AFT.BinaryArithmetic.RationalBits.matrixProductTerm matrix profile output input).data.decode=
      ((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.matrixProductTerm,_root_.AFT.BinaryArithmetic.RationalBits.multiply_value,_root_.AFT.BinaryArithmetic.RationalBits.matrixEntry_value,_root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h17 → _p2mH17
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h18 {count : ℕ} (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.RationalBits count) count)
    (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits count) (output : Fin count) :
    (_root_.AFT.BinaryArithmetic.RationalBits.matrixRow matrix profile output).data.decode=
      ∑ input,((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.matrixRow,_root_.AFT.BinaryArithmetic.RationalBits.sumFin_value,_p2mH17]
open _root_.P2Mba49f952 renaming h18 → _p2mH18
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h16 {count : ℕ} (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.RationalBits count) count)
    (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits count) (output : Fin count) :
    ((_root_.AFT.BinaryArithmetic.RationalBits.matrixApply matrix profile).data.get output).decode=
      ∑ input,((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.matrixApply,_root_.AFT.BinaryArithmetic.RationalBits.buildArray_get,_p2mH18]
open _root_.P2Mba49f952 renaming h16 → _p2mH16
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h14 {count : ℕ} (rhs applied : Vector _root_.AFT.BinaryArithmetic.RationalBits count) (output : Fin count) :
    (_root_.AFT.BinaryArithmetic.RationalBits.iterationEntry rhs applied output).data.decode=(rhs.get output).decode-(applied.get output).decode := by
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.iterationEntry,_root_.AFT.BinaryArithmetic.RationalBits.add_value,_root_.AFT.BinaryArithmetic.RationalBits.negate_value,_root_.AFT.BinaryArithmetic.readVector_value,sub_eq_add_neg]
open _root_.P2Mba49f952 renaming h14 → _p2mH14
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h15 {count : ℕ} (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.RationalBits count) count)
    (rhs : Vector _root_.AFT.BinaryArithmetic.RationalBits count) (steps : ℕ) (output : Fin count) :
    ((_root_.AFT.BinaryArithmetic.RationalBits.iteration matrix rhs steps).data.get output).decode=
      _root_.AFT.RationalNumerics.linearIteration (fun out inp => ((matrix.get out).get inp).decode) (fun out => (rhs.get out).decode) steps output := by
  induction steps generalizing output with
  | zero => simp [_root_.AFT.BinaryArithmetic.RationalBits.iteration,_root_.AFT.RationalNumerics.linearIteration]
  | succ steps ih =>
    simp only [_root_.AFT.BinaryArithmetic.RationalBits.iteration,_root_.AFT.BinaryArithmetic.RationalBits.buildArray_get,_p2mH14,_p2mH16,_root_.AFT.RationalNumerics.linearIteration,Pi.sub_apply,_root_.AFT.RationalNumerics.matrixApply]
    congr 1
    apply Finset.sum_congr rfl
    intro input _
    rw [ih]
open _root_.P2Mba49f952 renaming h15 → _p2mH15
end AFT.BinaryArithmetic.RationalBits
open _root_.P2Mba49f952 renaming h14 → _p2mH14
open _root_.P2Mba49f952 renaming h15 → _p2mH15
open _root_.P2Mba49f952 renaming h16 → _p2mH16
open _root_.P2Mba49f952 renaming h17 → _p2mH17
open _root_.P2Mba49f952 renaming h18 → _p2mH18
end
open _root_.P2Mba49f952 renaming h14 → _p2mH14
open _root_.P2Mba49f952 renaming h15 → _p2mH15
open _root_.P2Mba49f952 renaming h16 → _p2mH16
open _root_.P2Mba49f952 renaming h17 → _p2mH17
open _root_.P2Mba49f952 renaming h18 → _p2mH18
namespace AFT.BinaryArithmetic.RationalBits.conditionalWork
end AFT.BinaryArithmetic.RationalBits.conditionalWork
namespace AFT.BinaryArithmetic.RationalBits.expectationWork
end AFT.BinaryArithmetic.RationalBits.expectationWork
namespace AFT.BinaryArithmetic.RationalBits.featureWork
end AFT.BinaryArithmetic.RationalBits.featureWork
namespace AFT.BinaryArithmetic.RationalBits.finiteSumWork
end AFT.BinaryArithmetic.RationalBits.finiteSumWork
namespace AFT.BinaryArithmetic.RationalBits.iteration
end AFT.BinaryArithmetic.RationalBits.iteration
namespace AFT.BinaryArithmetic.RationalBits.iteration.match_1
end AFT.BinaryArithmetic.RationalBits.iteration.match_1
namespace AFT.BinaryArithmetic.RationalBits.iterationEntry
end AFT.BinaryArithmetic.RationalBits.iterationEntry
namespace AFT.BinaryArithmetic.RationalBits.iterationWorkStep
end AFT.BinaryArithmetic.RationalBits.iterationWorkStep
namespace AFT.BinaryArithmetic.RationalBits.matrixApply
end AFT.BinaryArithmetic.RationalBits.matrixApply
namespace AFT.BinaryArithmetic.RationalBits.matrixEntry
end AFT.BinaryArithmetic.RationalBits.matrixEntry
namespace AFT.BinaryArithmetic.RationalBits.matrixProductTerm
end AFT.BinaryArithmetic.RationalBits.matrixProductTerm
namespace AFT.BinaryArithmetic.RationalBits.matrixRow
end AFT.BinaryArithmetic.RationalBits.matrixRow
namespace AFT.BinaryArithmetic.RationalBits.projectionWork
end AFT.BinaryArithmetic.RationalBits.projectionWork
section
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h11 {charts : ℕ} (fiber : Vector Bool charts) (point : Fin charts) :
     (_root_.AFT.BinaryArithmetic.RationalBits.chartSpike fiber point).data.decode=_root_.AFT.BoundaryCalibration.chartSpikeProgram charts (_root_.AFT.BinaryArithmetic.maskSet fiber) point := by
   simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartSpike,_root_.AFT.BinaryArithmetic.readVector_value,_root_.AFT.BoundaryCalibration.chartSpikeProgram,_root_.AFT.BinaryArithmetic.maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
   split <;> simp_all [_root_.AFT.BinaryArithmetic.RationalBits.quotient_value,_root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value,_p2mH30,_root_.AFT.BinaryArithmetic.maskSet]
open _root_.P2Mba49f952 renaming h11 → _p2mH11
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h5 {charts : ℕ} (safe : Vector Bool charts) (input point : Fin charts) :
     (_root_.AFT.BinaryArithmetic.RationalBits.chartDeletedBasis safe input point).data.decode=
       if point∈_root_.AFT.BinaryArithmetic.maskSet safe then 0 else if point=input then 1 else 0 := by
   have he : (_root_.AFT.BinaryArithmetic.equalCounter point.val input.val).value=true ↔ point=input := by
     rw [_root_.AFT.BinaryArithmetic.equalCounter_value,Fin.val_inj]
   simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartDeletedBasis,_root_.AFT.BinaryArithmetic.readVector_value,_root_.AFT.BinaryArithmetic.maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
   by_cases hs : safe.get point=true
   · simp [hs]
   · simp only [hs,Bool.false_eq_true,ite_false]
     by_cases hi : point=input
     · simp only [he.mpr hi,ite_true,if_pos hi,_root_.AFT.BinaryArithmetic.RationalBits.one_value]
     · have hn : (_root_.AFT.BinaryArithmetic.equalCounter point.val input.val).value=false := Bool.eq_false_iff.mpr (fun h => hi (he.mp h))
       simp [hn,hi]
open _root_.P2Mba49f952 renaming h5 → _p2mH5
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h6 {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) :
     (_root_.AFT.BinaryArithmetic.RationalBits.chartDeletionEntry feature allowed safe output input).data.decode=
       _root_.AFT.BoundaryCalibration.chartDeletionMatrixProgram charts colors features (fun i => (feature.get i).get)
         (fun i => _root_.AFT.BinaryArithmetic.maskSet (allowed.get i)) (_root_.AFT.BinaryArithmetic.maskSet safe) output input := by
   simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartDeletionEntry,_root_.AFT.BinaryArithmetic.RationalBits.negate_value,_p2mH10,_root_.AFT.BinaryArithmetic.RationalBits.buildArray_get,_p2mH5,
     _root_.AFT.BoundaryCalibration.chartDeletionMatrixProgram,_root_.AFT.BoundaryCalibration.chartDeletionProgram]
open _root_.P2Mba49f952 renaming h6 → _p2mH6
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h7 {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) :
     (((_root_.AFT.BinaryArithmetic.RationalBits.chartDeletionMatrix feature allowed safe).data.get output).get input).decode=
       _root_.AFT.BoundaryCalibration.chartDeletionMatrixProgram charts colors features (fun i => (feature.get i).get)
         (fun i => _root_.AFT.BinaryArithmetic.maskSet (allowed.get i)) (_root_.AFT.BinaryArithmetic.maskSet safe) output input := by
   simp only [_root_.AFT.BinaryArithmetic.RationalBits.chartDeletionMatrix,Vector.get_map,Vector.get_ofFn,_root_.AFT.BinaryArithmetic.RationalBits.buildArray_get,_p2mH6]
open _root_.P2Mba49f952 renaming h7 → _p2mH7
end AFT.BinaryArithmetic.RationalBits
open _root_.P2Mba49f952 renaming h5 → _p2mH5
open _root_.P2Mba49f952 renaming h6 → _p2mH6
open _root_.P2Mba49f952 renaming h7 → _p2mH7
open _root_.P2Mba49f952 renaming h11 → _p2mH11
end
open _root_.P2Mba49f952 renaming h5 → _p2mH5
open _root_.P2Mba49f952 renaming h6 → _p2mH6
open _root_.P2Mba49f952 renaming h7 → _p2mH7
open _root_.P2Mba49f952 renaming h11 → _p2mH11
namespace AFT.BoundaryCalibration.StoredChartSupports
end AFT.BoundaryCalibration.StoredChartSupports
namespace AFT.BoundaryCalibration.StoredChartSupports.mk
end AFT.BoundaryCalibration.StoredChartSupports.mk
namespace AFT.BoundaryCalibration.countedChartSupports
end AFT.BoundaryCalibration.countedChartSupports
namespace AFT.BoundaryCalibration.countedFiberChartTest
end AFT.BoundaryCalibration.countedFiberChartTest
namespace AFT.BoundaryCalibration.countedSafeChartTest
end AFT.BoundaryCalibration.countedSafeChartTest
section
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h28 {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (point : Fin charts) (index : Fin features) :
     (_root_.AFT.BinaryArithmetic.chartAllowedAt feature allowed point index).value=(allowed.get index).get ((feature.get index).get point) := by
   simp only [_root_.AFT.BinaryArithmetic.chartAllowedAt,_root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h28 → _p2mH28
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h36 {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (point : Fin charts) :
     (_root_.AFT.BinaryArithmetic.safeChart feature allowed scale point).value=true ↔
       scale.get point≠0 ∧ ∀ index,(allowed.get index).get ((feature.get index).get point)=true := by
   simp only [_root_.AFT.BinaryArithmetic.safeChart,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,_root_.AFT.BinaryArithmetic.equalCounter_value,
     _root_.AFT.BinaryArithmetic.readVector_value,_p2mH37,_p2mH28]
   have hzero : (scale.get point).val=0 ↔ scale.get point=0 := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
   rw [hzero]
open _root_.P2Mba49f952 renaming h36 → _p2mH36
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h28 → _p2mH28
open _root_.P2Mba49f952 renaming h36 → _p2mH36
end
open _root_.P2Mba49f952 renaming h28 → _p2mH28
open _root_.P2Mba49f952 renaming h36 → _p2mH36
namespace AFT.BinaryArithmetic.binaryEdgeAddress
end AFT.BinaryArithmetic.binaryEdgeAddress
namespace AFT.BinaryArithmetic.binaryEdgeAddress.match_1
end AFT.BinaryArithmetic.binaryEdgeAddress.match_1
namespace AFT.BinaryArithmetic.binaryRootAddress
end AFT.BinaryArithmetic.binaryRootAddress
namespace AFT.BinaryArithmetic.binaryRootAddress.match_1
end AFT.BinaryArithmetic.binaryRootAddress.match_1
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualBodyRootBasis
end AFT.V7Calibration.actualBodyRootBasis
namespace AFT.V7Calibration.actualRootIndex
end AFT.V7Calibration.actualRootIndex
namespace AFT.V7Calibration.blockIndexNumbering
end AFT.V7Calibration.blockIndexNumbering
namespace AFT.V7Calibration.coordinateZeroSumCongr
end AFT.V7Calibration.coordinateZeroSumCongr
namespace AFT.V7Calibration.physicalEdgeIndexEquiv
end AFT.V7Calibration.physicalEdgeIndexEquiv
namespace AFT.blockEdgeNumbering
end AFT.blockEdgeNumbering
namespace AFT.blockNumbering
end AFT.blockNumbering
namespace AFT.physicalEdgeLoadProgram
end AFT.physicalEdgeLoadProgram
namespace AFT.physicalEdgeLoadProgram.match_1
end AFT.physicalEdgeLoadProgram.match_1
namespace AFT.physicalEdgeNumberingProgram
end AFT.physicalEdgeNumberingProgram
namespace AFT.physicalInitialLoadProgram
end AFT.physicalInitialLoadProgram
namespace AFT.physicalQueueLoadProgram
end AFT.physicalQueueLoadProgram
namespace AFT.physicalVertexNumberingProgram
end AFT.physicalVertexNumberingProgram
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h22 (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (vertex : Fin (count+1)) :
     (_root_.AFT.BinaryArithmetic.binaryPhysicalVertex legs rest count hvertex vertex).value=
       (_root_.AFT.physicalVertexNumberingProgram legs rest count hvertex).symm vertex :=
   _p2mH27 legs rest _
open _root_.P2Mba49f952 renaming h22 → _p2mH22
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h22 → _p2mH22
end
open _root_.P2Mba49f952 renaming h22 → _p2mH22
namespace AFT.BinaryArithmetic.ProtectedDimensions
end AFT.BinaryArithmetic.ProtectedDimensions
namespace AFT.BinaryArithmetic.ProtectedDimensions.mk
end AFT.BinaryArithmetic.ProtectedDimensions.mk
namespace AFT.BinaryArithmetic.chartAllowedAt
end AFT.BinaryArithmetic.chartAllowedAt
namespace AFT.BinaryArithmetic.chartAllowedExceptAt
end AFT.BinaryArithmetic.chartAllowedExceptAt
namespace AFT.BinaryArithmetic.fiberChart
end AFT.BinaryArithmetic.fiberChart
namespace AFT.BinaryArithmetic.protectedAtom
end AFT.BinaryArithmetic.protectedAtom
namespace AFT.BinaryArithmetic.protectedDimensions
end AFT.BinaryArithmetic.protectedDimensions
namespace AFT.BinaryArithmetic.protectedDimensionsWork
end AFT.BinaryArithmetic.protectedDimensionsWork
namespace AFT.BinaryArithmetic.protectedMark
end AFT.BinaryArithmetic.protectedMark
namespace AFT.BinaryArithmetic.protectedMarkAddress
end AFT.BinaryArithmetic.protectedMarkAddress
namespace AFT.BinaryArithmetic.safeChart
end AFT.BinaryArithmetic.safeChart
namespace AFT.BinaryArithmetic.supportWork
end AFT.BinaryArithmetic.supportWork
section
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h31 (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (h : _root_.AFT.BinaryArithmetic.BinaryPublicChartMetadata charts modulus features=
       _root_.AFT.BinaryArithmetic.BinaryPublicChartMetadata (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1))) :
     cast h (_root_.AFT.BinaryArithmetic.protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value=
       (_root_.AFT.BinaryArithmetic.protectedMetadataCore cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) rfl rfl
         boundarySign baselineSign boundary baseline mark).value := by
   subst charts
   subst features
   rfl
open _root_.P2Mba49f952 renaming h31 → _p2mH31
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h32 (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     (_root_.AFT.BinaryArithmetic.protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value=
       (_root_.AFT.BinaryArithmetic.protectedMetadataCore cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) rfl rfl
         boundarySign baselineSign boundary baseline mark).value := by
   dsimp only [_root_.AFT.BinaryArithmetic.protectedMetadata]
   exact _p2mH31 cutoff modulus _ _ _ _ boundarySign baselineSign boundary baseline mark _
open _root_.P2Mba49f952 renaming h32 → _p2mH32
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h31 → _p2mH31
open _root_.P2Mba49f952 renaming h32 → _p2mH32
end
open _root_.P2Mba49f952 renaming h31 → _p2mH31
open _root_.P2Mba49f952 renaming h32 → _p2mH32
namespace AFT.BinaryArithmetic.binaryAcceptance
end AFT.BinaryArithmetic.binaryAcceptance
namespace AFT.BinaryArithmetic.binaryAcceptanceWork
end AFT.BinaryArithmetic.binaryAcceptanceWork
namespace AFT.BinaryArithmetic.rationalAcceptance_threshold
end AFT.BinaryArithmetic.rationalAcceptance_threshold
namespace AFT.RationalAcceptanceCoin.draw
end AFT.RationalAcceptanceCoin.draw
namespace AFT.RationalRejectionProgram.CountedValue
end AFT.RationalRejectionProgram.CountedValue
namespace AFT.RationalRejectionProgram.CountedValue.mk
end AFT.RationalRejectionProgram.CountedValue.mk
namespace AFT.RationalRejectionProgram.countedAcceptance
end AFT.RationalRejectionProgram.countedAcceptance
namespace AFT.RationalRejectionProgram.countedDraw
end AFT.RationalRejectionProgram.countedDraw
namespace AFT.RationalRejectionProgram.countedDraw.match_1
end AFT.RationalRejectionProgram.countedDraw.match_1
namespace AFT.RationalRejectionProgram.draw
end AFT.RationalRejectionProgram.draw
namespace AFT.RationalRejectionProgram.proposal
end AFT.RationalRejectionProgram.proposal
section
namespace AFT.BinaryArithmetic
open RationalNumerics RationalRejectionProgram
variable {State Tape : Type*}
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h23 (raw envelope : _root_.AFT.BinaryArithmetic.RationalBits) :
    (_root_.AFT.BinaryArithmetic.binaryPositiveRatio raw envelope).data.decode=max raw.decode 0/envelope.decode := by
  simp only [_root_.AFT.BinaryArithmetic.binaryPositiveRatio,_root_.AFT.BinaryArithmetic.RationalBits.quotient_value,_root_.AFT.BinaryArithmetic.RationalBits.maxZero_value]
open _root_.P2Mba49f952 renaming h23 → _p2mH23
end AFT.BinaryArithmetic
open _root_.P2Mba49f952 renaming h23 → _p2mH23
end
open _root_.P2Mba49f952 renaming h23 → _p2mH23
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ActualBlockFock
end CurrentAFT.ActualBlockFock
namespace CurrentAFT.ActualBlockFock.Slots
end CurrentAFT.ActualBlockFock.Slots
namespace CurrentAFT.ActualBlockFock.Slots.match_1
end CurrentAFT.ActualBlockFock.Slots.match_1
namespace CurrentAFT.ActualBlockFock.blockLawAt
end CurrentAFT.ActualBlockFock.blockLawAt
namespace CurrentAFT.ActualBlockFock.productFockEnergy
end CurrentAFT.ActualBlockFock.productFockEnergy
namespace CurrentAFT.ActualBlockFock.singletonLaw
end CurrentAFT.ActualBlockFock.singletonLaw
section
namespace CurrentAFT.CurrentPhysicalNumbering
open AFT ActualBlockFock
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.bodySize Parameters.legCount Parameters.dimension
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h177 (security : ℕ) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) (slot : Fin 3) :
    (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security ⟨.inl leg, slot⟩).val = slot.val + 3 * leg.val := by
  rfl
open _root_.P2Mba49f952 renaming h177 → _p2mH177
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h176 (security : ℕ) (center : Fin (_root_.CurrentAFT.ActualBlockFock.centerCount security)) :
    (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security ⟨.inr (.inl center), (0 : Fin 1)⟩).val = _root_.CurrentAFT.Parameters.legCount security * 3 + center.val := by
  rfl
open _root_.P2Mba49f952 renaming h176 → _p2mH176
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h178 (security : ℕ) (queue : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security ⟨.inr (.inr queue), (0 : Fin 1)⟩).val =
      _root_.CurrentAFT.Parameters.legCount security * 3 + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val) := by
  rfl
open _root_.P2Mba49f952 renaming h178 → _p2mH178
end CurrentAFT.CurrentPhysicalNumbering
open _root_.P2Mba49f952 renaming h176 → _p2mH176
open _root_.P2Mba49f952 renaming h177 → _p2mH177
open _root_.P2Mba49f952 renaming h178 → _p2mH178
end
open _root_.P2Mba49f952 renaming h176 → _p2mH176
open _root_.P2Mba49f952 renaming h177 → _p2mH177
open _root_.P2Mba49f952 renaming h178 → _p2mH178
namespace CurrentAFT.BinaryAnchorTable
end CurrentAFT.BinaryAnchorTable
namespace CurrentAFT.BinaryAnchorTable.anchor_height
end CurrentAFT.BinaryAnchorTable.anchor_height
namespace CurrentAFT.BinaryAnchorTable.current
end CurrentAFT.BinaryAnchorTable.current
namespace CurrentAFT.BinaryAnchorTable.currentHeightPolynomial
end CurrentAFT.BinaryAnchorTable.currentHeightPolynomial
namespace CurrentAFT.BinaryAnchorTable.currentWorkPolynomial
end CurrentAFT.BinaryAnchorTable.currentWorkPolynomial
namespace CurrentAFT.BinaryAnchorTable.point
end CurrentAFT.BinaryAnchorTable.point
namespace CurrentAFT.BinaryAnchorTable.pointHeightPolynomial
end CurrentAFT.BinaryAnchorTable.pointHeightPolynomial
namespace CurrentAFT.BinaryCenterKernel
end CurrentAFT.BinaryCenterKernel
namespace CurrentAFT.BinaryCenterKernel.anchorAverage
end CurrentAFT.BinaryCenterKernel.anchorAverage
namespace CurrentAFT.BinaryCenterKernel.anchorEntry
end CurrentAFT.BinaryCenterKernel.anchorEntry
namespace CurrentAFT.BinaryCenterKernel.formulaBound
end CurrentAFT.BinaryCenterKernel.formulaBound
namespace CurrentAFT.BinaryCenterKernel.formulaPolynomial
end CurrentAFT.BinaryCenterKernel.formulaPolynomial
namespace CurrentAFT.BinaryCenterKernel.heightPolynomial
end CurrentAFT.BinaryCenterKernel.heightPolynomial
namespace CurrentAFT.BinaryCenterKernel.integerBound
end CurrentAFT.BinaryCenterKernel.integerBound
namespace CurrentAFT.BinaryCenterKernel.point
end CurrentAFT.BinaryCenterKernel.point
namespace CurrentAFT.BinaryCenterKernel.safe
end CurrentAFT.BinaryCenterKernel.safe
namespace CurrentAFT.BinaryCenterKernel.sliceWorkPolynomial
end CurrentAFT.BinaryCenterKernel.sliceWorkPolynomial
namespace CurrentAFT.BinaryCenterKernel.work
end CurrentAFT.BinaryCenterKernel.work
namespace CurrentAFT.BinaryCenterKernel.workPolynomial
end CurrentAFT.BinaryCenterKernel.workPolynomial
namespace CurrentAFT.BinaryPrimaryTable
end CurrentAFT.BinaryPrimaryTable
namespace CurrentAFT.BinaryPrimaryTable.countPolynomial
end CurrentAFT.BinaryPrimaryTable.countPolynomial
namespace CurrentAFT.BinaryPrimaryTable.currentHeightPolynomial
end CurrentAFT.BinaryPrimaryTable.currentHeightPolynomial
namespace CurrentAFT.BinaryPrimaryTable.currentWorkPolynomial
end CurrentAFT.BinaryPrimaryTable.currentWorkPolynomial
namespace CurrentAFT.BinaryPrimaryTable.guardWorkPolynomial
end CurrentAFT.BinaryPrimaryTable.guardWorkPolynomial
namespace CurrentAFT.BinaryPrimaryTable.point
end CurrentAFT.BinaryPrimaryTable.point
namespace CurrentAFT.BinaryPrimaryTable.raw
end CurrentAFT.BinaryPrimaryTable.raw
namespace CurrentAFT.BinaryPrimaryTable.rawWorkPolynomial
end CurrentAFT.BinaryPrimaryTable.rawWorkPolynomial
namespace CurrentAFT.BinaryProposalGuard
end CurrentAFT.BinaryProposalGuard
namespace CurrentAFT.BinaryProposalGuard.lowerCheckWork
end CurrentAFT.BinaryProposalGuard.lowerCheckWork
namespace CurrentAFT.BinaryProposalGuard.uniformWork
end CurrentAFT.BinaryProposalGuard.uniformWork
namespace CurrentAFT.BinaryWindowAverage
end CurrentAFT.BinaryWindowAverage
namespace CurrentAFT.BinaryWindowAverage.sumHeight
end CurrentAFT.BinaryWindowAverage.sumHeight
section
namespace CurrentAFT.BinaryReferenceTables
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter multiplyCounter PublicParameterProgram.modulus BinaryActivationProgram.cutoff
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h72 (security bits : ℕ) (primary output : Fin (_root_.CurrentAFT.PublicParameterProgram.modulus security).count) :
    (((_root_.CurrentAFT.BinaryReferenceTables.current security bits).anchor.get primary).get output).decode =
      _root_.CurrentAFT.RationalProposalProgram.anchor security bits primary.val output.val :=
  _root_.CurrentAFT.BinaryAnchorTable.current_value security bits primary output
open _root_.P2Mba49f952 renaming h72 → CurrentAFT.BinaryReferenceTables.anchor_value
open _root_.P2Mba49f952 renaming h72 → _p2mH72
noncomputable section
end
end CurrentAFT.BinaryReferenceTables
open _root_.P2Mba49f952 renaming h72 → CurrentAFT.BinaryReferenceTables.anchor_value
open _root_.P2Mba49f952 renaming h72 → _p2mH72
end
open _root_.P2Mba49f952 renaming h72 → CurrentAFT.BinaryReferenceTables.anchor_value
open _root_.P2Mba49f952 renaming h72 → _p2mH72
section
namespace CurrentAFT.BinaryPairedScore
open AFT AFT.RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h65 {count : ℕ} (primary score : Vector _root_.AFT.BinaryArithmetic.RationalBits count)
    (anchor : Vector (Vector _root_.AFT.BinaryArithmetic.RationalBits count) count) (center color : Fin count) :
    (_root_.CurrentAFT.BinaryPairedScore.term primary score anchor center color).data.decode =
      (primary.get color).decode * (score.get color).decode * ((anchor.get color).get center).decode := by
  simp only [_root_.CurrentAFT.BinaryPairedScore.term, _root_.AFT.BinaryArithmetic.RationalBits.multiply_value, _root_.AFT.BinaryArithmetic.readVector_value, _root_.AFT.BinaryArithmetic.RationalBits.matrixEntry_value]
open _root_.P2Mba49f952 renaming h65 → CurrentAFT.BinaryPairedScore.term_value
open _root_.P2Mba49f952 renaming h65 → _p2mH65
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h64 {count : ℕ} (primary centerLaw score : Vector _root_.AFT.BinaryArithmetic.RationalBits count)
    (anchor : Vector (Vector _root_.AFT.BinaryArithmetic.RationalBits count) count) (rate : _root_.AFT.BinaryArithmetic.RationalBits) (input center : Fin count) :
    (_root_.CurrentAFT.BinaryPairedScore.current primary centerLaw score anchor rate input center).data.decode =
      (score.get input).decode - rate.decode *
        (∑ color, (primary.get color).decode * (score.get color).decode * ((anchor.get color).get center).decode) /
          (centerLaw.get center).decode := by
  simp only [_root_.CurrentAFT.BinaryPairedScore.current, _root_.AFT.BinaryArithmetic.RationalBits.add_value, _root_.AFT.BinaryArithmetic.RationalBits.negate_value, _root_.AFT.BinaryArithmetic.RationalBits.multiply_value, _root_.AFT.BinaryArithmetic.RationalBits.inverse_value, _root_.AFT.BinaryArithmetic.readVector_value,
    _root_.AFT.BinaryArithmetic.RationalBits.sumFin_value, _p2mH65, div_eq_mul_inv, sub_eq_add_neg]
open _root_.P2Mba49f952 renaming h64 → CurrentAFT.BinaryPairedScore.current_value
open _root_.P2Mba49f952 renaming h64 → _p2mH64
end CurrentAFT.BinaryPairedScore
open _root_.P2Mba49f952 renaming h64 → CurrentAFT.BinaryPairedScore.current_value
open _root_.P2Mba49f952 renaming h64 → _p2mH64
open _root_.P2Mba49f952 renaming h65 → CurrentAFT.BinaryPairedScore.term_value
open _root_.P2Mba49f952 renaming h65 → _p2mH65
end
open _root_.P2Mba49f952 renaming h64 → CurrentAFT.BinaryPairedScore.current_value
open _root_.P2Mba49f952 renaming h64 → _p2mH64
open _root_.P2Mba49f952 renaming h65 → CurrentAFT.BinaryPairedScore.term_value
open _root_.P2Mba49f952 renaming h65 → _p2mH65
namespace CurrentAFT.BinaryCurrentPaired
end CurrentAFT.BinaryCurrentPaired
namespace CurrentAFT.BinaryCurrentPaired.boundPolynomial
end CurrentAFT.BinaryCurrentPaired.boundPolynomial
namespace CurrentAFT.BinaryCurrentPaired.currentHeightPolynomial
end CurrentAFT.BinaryCurrentPaired.currentHeightPolynomial
namespace CurrentAFT.BinaryCurrentPaired.currentWorkPolynomial
end CurrentAFT.BinaryCurrentPaired.currentWorkPolynomial
namespace CurrentAFT.BinaryCurrentPaired.evaluationWorkPolynomial
end CurrentAFT.BinaryCurrentPaired.evaluationWorkPolynomial
namespace CurrentAFT.BinaryCurrentPaired.heightPolynomial
end CurrentAFT.BinaryCurrentPaired.heightPolynomial
namespace CurrentAFT.BinaryCurrentPaired.scoreAt
end CurrentAFT.BinaryCurrentPaired.scoreAt
namespace CurrentAFT.BinaryPairedScore
end CurrentAFT.BinaryPairedScore
namespace CurrentAFT.BinaryPairedScore.height
end CurrentAFT.BinaryPairedScore.height
namespace CurrentAFT.BinaryPairedScore.work
end CurrentAFT.BinaryPairedScore.work
namespace CurrentAFT.BinaryTupleSum
end CurrentAFT.BinaryTupleSum
namespace CurrentAFT.BinaryTupleSum.current
end CurrentAFT.BinaryTupleSum.current
namespace CurrentAFT.BinaryTupleSum.current.match_1
end CurrentAFT.BinaryTupleSum.current.match_1
namespace CurrentAFT.BinaryTupleSum.height
end CurrentAFT.BinaryTupleSum.height
namespace CurrentAFT.BinaryTupleSum.height.match_1
end CurrentAFT.BinaryTupleSum.height.match_1
namespace CurrentAFT.BinaryTupleSum.heightPolynomial
end CurrentAFT.BinaryTupleSum.heightPolynomial
namespace CurrentAFT.BinaryTupleSum.heightPolynomial.match_1
end CurrentAFT.BinaryTupleSum.heightPolynomial.match_1
namespace CurrentAFT.BinaryTupleSum.prepend
end CurrentAFT.BinaryTupleSum.prepend
namespace CurrentAFT.BinaryTupleSum.prependWork
end CurrentAFT.BinaryTupleSum.prependWork
namespace CurrentAFT.BinaryTupleSum.work
end CurrentAFT.BinaryTupleSum.work
namespace CurrentAFT.BinaryTupleSum.work.match_1
end CurrentAFT.BinaryTupleSum.work.match_1
namespace CurrentAFT.BinaryTupleSum.workPolynomial
end CurrentAFT.BinaryTupleSum.workPolynomial
namespace CurrentAFT.BinaryTupleSum.workPolynomial.match_1
end CurrentAFT.BinaryTupleSum.workPolynomial.match_1
section
namespace CurrentAFT.BinaryPairedTensor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h67 {Value : Type*} {count : ℕ} (fallback : Value) (word : Vector Value (count+1)) (index : Fin count) :
    (_root_.CurrentAFT.BinaryPairedTensor.dropFirst fallback word).value.get index = word.get index.succ := by simp [_root_.CurrentAFT.BinaryPairedTensor.dropFirst, _root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h67 → _p2mH67
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h66 {colors : ℕ} (primary center : Vector _root_.AFT.BinaryArithmetic.RationalBits colors)
    (anchor : Vector (Vector _root_.AFT.BinaryArithmetic.RationalBits colors) colors) (rate : _root_.AFT.BinaryArithmetic.RationalBits) (fallback : Fin colors × Fin colors)
    (count : ℕ) (kernel : Vector (Fin colors) count → _root_.AFT.BinaryArithmetic.RationalResult) (groups : Vector (Fin colors × Fin colors) count) :
    (_root_.CurrentAFT.BinaryPairedTensor.current primary center anchor rate fallback count kernel groups).data.decode =
      _root_.CurrentAFT.BinaryPairedTensor.value primary center anchor rate count (fun word => (kernel (Vector.ofFn word)).data.decode) groups.get := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [_root_.CurrentAFT.BinaryPairedTensor.current, _p2mH64, _root_.AFT.BinaryArithmetic.RationalBits.buildArray_get, _root_.AFT.BinaryArithmetic.readVector_value]
    simp_rw [ih]
    simp only [_root_.CurrentAFT.BinaryPairedTensor.value, _root_.CurrentAFT.BinaryPairedTensor.lift]
    have htail : (_root_.CurrentAFT.BinaryPairedTensor.dropFirst fallback groups).value.get = fun index => groups.get index.succ := by
      funext index; exact _p2mH67 fallback groups index
    rw [htail]
    simp only [_root_.InfoLossLARNativeSupplements.hcca3d782e3229b7c.CurrentAFT.BinaryTupleSum.prepend_value, _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum.get_ofFn_fun]
open _root_.P2Mba49f952 renaming h66 → CurrentAFT.BinaryPairedTensor.current_value
open _root_.P2Mba49f952 renaming h66 → _p2mH66
end CurrentAFT.BinaryPairedTensor
open _root_.P2Mba49f952 renaming h66 → CurrentAFT.BinaryPairedTensor.current_value
open _root_.P2Mba49f952 renaming h66 → _p2mH66
open _root_.P2Mba49f952 renaming h67 → _p2mH67
end
open _root_.P2Mba49f952 renaming h66 → CurrentAFT.BinaryPairedTensor.current_value
open _root_.P2Mba49f952 renaming h66 → _p2mH66
open _root_.P2Mba49f952 renaming h67 → _p2mH67
namespace AFT.BinaryArithmetic.RationalBits.piHeightPolynomial
end AFT.BinaryArithmetic.RationalBits.piHeightPolynomial
namespace AFT.BinaryArithmetic.RationalBits.piWorkPolynomial
end AFT.BinaryArithmetic.RationalBits.piWorkPolynomial
namespace AFT.BinaryArithmetic.RationalBits.primitiveWorkPolynomial
end AFT.BinaryArithmetic.RationalBits.primitiveWorkPolynomial
namespace AFT.BinaryArithmetic.RationalBits.seriesStepWorkPolynomial
end AFT.BinaryArithmetic.RationalBits.seriesStepWorkPolynomial
namespace AFT.BinaryArithmetic.RationalBits.seriesTermBits
end AFT.BinaryArithmetic.RationalBits.seriesTermBits
namespace AFT.BinaryArithmetic.RationalBits.seriesTermBitsPolynomial
end AFT.BinaryArithmetic.RationalBits.seriesTermBitsPolynomial
namespace AFT.BinaryArithmetic.RationalBits.seriesTermWorkPolynomial
end AFT.BinaryArithmetic.RationalBits.seriesTermWorkPolynomial
namespace AFT.BinaryArithmetic.RationalBits.seriesWork
end AFT.BinaryArithmetic.RationalBits.seriesWork
namespace AFT.BinaryArithmetic.RationalBits.seriesWorkPolynomial
end AFT.BinaryArithmetic.RationalBits.seriesWorkPolynomial
namespace AFT.BinaryArithmetic.lessCounter
end AFT.BinaryArithmetic.lessCounter
namespace AFT.BinaryArithmetic.lessCounter.match_1
end AFT.BinaryArithmetic.lessCounter.match_1
namespace AFT.BinaryArithmetic.powerCounter
end AFT.BinaryArithmetic.powerCounter
namespace AFT.BinaryArithmetic.powerCounter.match_1
end AFT.BinaryArithmetic.powerCounter.match_1
namespace AFT.BinaryArithmetic.powerCounterWork
end AFT.BinaryArithmetic.powerCounterWork
namespace AFT.BinaryArithmetic.subtractCounter
end AFT.BinaryArithmetic.subtractCounter
namespace AFT.RationalNumerics.piHeight
end AFT.RationalNumerics.piHeight
namespace CurrentAFT.WeightCoordinates
end CurrentAFT.WeightCoordinates
namespace CurrentAFT.WeightCoordinates.tupleCode
end CurrentAFT.WeightCoordinates.tupleCode
namespace CurrentAFT.WeightCoordinates.tupleCode.match_1
end CurrentAFT.WeightCoordinates.tupleCode.match_1
section
namespace CurrentAFT.BinaryWeightCoordinates
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] multiplyCounter addCounter powerCounter
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h76 {First Second : Type*} {count : ℕ} (word : Vector First count) (f : First → Second) :
    (word.map f).get = fun index => f (word.get index) := by
  funext index
  simp only [Vector.get_map]
open _root_.P2Mba49f952 renaming h76 → _p2mH76
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h77 (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table base order) (primary : Vector (Fin base) r) (body : Vector (Fin base) s) :
    (_root_.CurrentAFT.BinaryWeightCoordinates.read base order r s hb hdegree table primary body).data.decode =
      ((table.get (_root_.CurrentAFT.WeightCoordinates.arityIndex order ⟨r, by omega⟩ ⟨s, by omega⟩)).get
        (_root_.CurrentAFT.WeightCoordinates.wordIndex base order r s hb hdegree primary.get body.get)).decode := by
  simp only [_root_.CurrentAFT.BinaryWeightCoordinates.read, _root_.AFT.BinaryArithmetic.readVector_value]
  congr 3
  · apply Fin.ext
    exact _root_.CurrentAFT.BinaryWeightCoordinates.arity_value order r s
  · simpa only [_root_.CurrentAFT.WeightCoordinates.wordIndex, _p2mH76, Function.comp_def] using _root_.CurrentAFT.BinaryWeightCoordinates.joint_value base r s (primary.map Fin.val) (body.map Fin.val)
open _root_.P2Mba49f952 renaming h77 → CurrentAFT.BinaryWeightCoordinates.read_value
open _root_.P2Mba49f952 renaming h77 → _p2mH77
end CurrentAFT.BinaryWeightCoordinates
open _root_.P2Mba49f952 renaming h76 → _p2mH76
open _root_.P2Mba49f952 renaming h77 → CurrentAFT.BinaryWeightCoordinates.read_value
open _root_.P2Mba49f952 renaming h77 → _p2mH77
end
open _root_.P2Mba49f952 renaming h76 → _p2mH76
open _root_.P2Mba49f952 renaming h77 → CurrentAFT.BinaryWeightCoordinates.read_value
open _root_.P2Mba49f952 renaming h77 → _p2mH77
namespace CurrentAFT.BinaryPairedTensor
end CurrentAFT.BinaryPairedTensor
namespace CurrentAFT.BinaryPairedTensor.current
end CurrentAFT.BinaryPairedTensor.current
namespace CurrentAFT.BinaryPairedTensor.current.match_1
end CurrentAFT.BinaryPairedTensor.current.match_1
namespace CurrentAFT.BinaryPairedTensor.dropFirst
end CurrentAFT.BinaryPairedTensor.dropFirst
namespace CurrentAFT.BinaryPairedTensor.dropWork
end CurrentAFT.BinaryPairedTensor.dropWork
namespace CurrentAFT.BinaryPairedTensor.height
end CurrentAFT.BinaryPairedTensor.height
namespace CurrentAFT.BinaryPairedTensor.height.match_1
end CurrentAFT.BinaryPairedTensor.height.match_1
namespace CurrentAFT.BinaryPairedTensor.heightPolynomial
end CurrentAFT.BinaryPairedTensor.heightPolynomial
namespace CurrentAFT.BinaryPairedTensor.heightPolynomial.match_1
end CurrentAFT.BinaryPairedTensor.heightPolynomial.match_1
namespace CurrentAFT.BinaryPairedTensor.lift
end CurrentAFT.BinaryPairedTensor.lift
namespace CurrentAFT.BinaryPairedTensor.value
end CurrentAFT.BinaryPairedTensor.value
namespace CurrentAFT.BinaryPairedTensor.value.match_1
end CurrentAFT.BinaryPairedTensor.value.match_1
namespace CurrentAFT.BinaryPairedTensor.work
end CurrentAFT.BinaryPairedTensor.work
namespace CurrentAFT.BinaryPairedTensor.work.match_1
end CurrentAFT.BinaryPairedTensor.work.match_1
namespace CurrentAFT.BinaryPairedTensor.workPolynomial
end CurrentAFT.BinaryPairedTensor.workPolynomial
namespace CurrentAFT.BinaryPairedTensor.workPolynomial.match_1
end CurrentAFT.BinaryPairedTensor.workPolynomial.match_1
namespace CurrentAFT.BinaryWeightCoordinates
end CurrentAFT.BinaryWeightCoordinates
namespace CurrentAFT.BinaryWeightCoordinates.arity
end CurrentAFT.BinaryWeightCoordinates.arity
namespace CurrentAFT.BinaryWeightCoordinates.checkedPower
end CurrentAFT.BinaryWeightCoordinates.checkedPower
namespace CurrentAFT.BinaryWeightCoordinates.encode
end CurrentAFT.BinaryWeightCoordinates.encode
namespace CurrentAFT.BinaryWeightCoordinates.encode.match_1
end CurrentAFT.BinaryWeightCoordinates.encode.match_1
namespace CurrentAFT.BinaryWeightCoordinates.encodeWork
end CurrentAFT.BinaryWeightCoordinates.encodeWork
namespace CurrentAFT.BinaryWeightCoordinates.encodeWork.match_1
end CurrentAFT.BinaryWeightCoordinates.encodeWork.match_1
namespace CurrentAFT.BinaryWeightCoordinates.encodeWorkPolynomial
end CurrentAFT.BinaryWeightCoordinates.encodeWorkPolynomial
namespace CurrentAFT.BinaryWeightCoordinates.joint
end CurrentAFT.BinaryWeightCoordinates.joint
namespace CurrentAFT.BinaryWeightCoordinates.jointWork
end CurrentAFT.BinaryWeightCoordinates.jointWork
namespace CurrentAFT.BinaryWeightCoordinates.jointWorkPolynomial
end CurrentAFT.BinaryWeightCoordinates.jointWorkPolynomial
namespace CurrentAFT.BinaryWeightCoordinates.leading
end CurrentAFT.BinaryWeightCoordinates.leading
namespace CurrentAFT.BinaryWeightCoordinates.leadingWork
end CurrentAFT.BinaryWeightCoordinates.leadingWork
namespace CurrentAFT.BinaryWeightCoordinates.read
end CurrentAFT.BinaryWeightCoordinates.read
namespace CurrentAFT.BinaryWeightCoordinates.readWork
end CurrentAFT.BinaryWeightCoordinates.readWork
namespace CurrentAFT.BinaryWeightCoordinates.readWorkPolynomial
end CurrentAFT.BinaryWeightCoordinates.readWorkPolynomial
namespace CurrentAFT.RationalWeightProgram
end CurrentAFT.RationalWeightProgram
namespace CurrentAFT.RationalWeightProgram.groupValues
end CurrentAFT.RationalWeightProgram.groupValues
namespace CurrentAFT.RationalWeightProgram.pairedTensor
end CurrentAFT.RationalWeightProgram.pairedTensor
namespace CurrentAFT.RationalWeightProgram.pairedTensor.match_1
end CurrentAFT.RationalWeightProgram.pairedTensor.match_1
namespace CurrentAFT.WeightCoordinates.arityCode
end CurrentAFT.WeightCoordinates.arityCode
namespace CurrentAFT.WeightCoordinates.jointCode
end CurrentAFT.WeightCoordinates.jointCode
namespace CurrentAFT.WeightCoordinates.wordIndex
end CurrentAFT.WeightCoordinates.wordIndex
section
namespace CurrentAFT.BinaryWeightLocal
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h79 {Value : Type*} {pool count : ℕ} (fallback : Value) (hp : 0 < pool)
    (values : Vector Value pool) (sites : Vector (Fin pool) count) (slot : Fin count) :
    (_root_.CurrentAFT.BinaryWeightLocal.gather fallback hp values sites).value.get slot = values.get (sites.get slot) := by
  simp [_root_.CurrentAFT.BinaryWeightLocal.gather, _root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h79 → _p2mH79
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h80 (security order : ℕ) (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors security) order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (primary : Fin arity.val.1.val → Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security))
    (body : Fin arity.val.2.val → Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) :
    _root_.CurrentAFT.BinaryWeightLocal.rawTable security order table arity (fun index => (primary index).val) (fun index => (body index).val) =
      ((table.get (_root_.CurrentAFT.WeightCoordinates.arityIndex order arity.val.1 arity.val.2)).get
        (_root_.CurrentAFT.WeightCoordinates.wordIndex (_root_.CurrentAFT.BinaryWeightLocal.colors security) order arity.val.1.val arity.val.2.val
          (_root_.CurrentAFT.BinaryWeightLocal.colors_pos security)
          arity.property primary body)).decode := by
  unfold _root_.CurrentAFT.BinaryWeightLocal.rawTable
  rw [dif_pos ⟨fun index => (primary index).isLt, fun index => (body index).isLt⟩]
  rfl
open _root_.P2Mba49f952 renaming h80 → _p2mH80
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h425 {count colors : ℕ} (color : Fin colors) (rest : Fin count → Fin colors) :
    (fun index : Fin (count+1) => (Fin.cons (α := fun _ => Fin colors) color rest index).val) =
      Fin.cons color.val (fun index => (rest index).val) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index
open _root_.P2Mba49f952 renaming h425 → _p2mH425
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h81 (security bits count : ℕ) (kernel : (Fin count → Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) → ℚ)
    (ideal : (Fin count → ℕ) → ℚ)
    (hk : ∀ word, kernel word = ideal (fun index => (word index).val))
    (groups : Fin count → Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security) × Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) :
    _root_.CurrentAFT.BinaryPairedTensor.value (_root_.CurrentAFT.BinaryReferenceTables.current security bits).primary (_root_.CurrentAFT.BinaryReferenceTables.current security bits).center
      (_root_.CurrentAFT.BinaryReferenceTables.current security bits).anchor (_root_.CurrentAFT.BinaryReferenceTables.current security bits).activation count kernel groups =
      _root_.CurrentAFT.RationalWeightProgram.pairedTensor security bits count ideal
        (fun index => ((groups index).1.val, (groups index).2.val)) := by
  induction count with
  | zero =>
    simp only [_root_.CurrentAFT.BinaryPairedTensor.value, _root_.CurrentAFT.RationalWeightProgram.pairedTensor]
    exact (hk Fin.elim0).trans (congrArg ideal (Subsingleton.elim _ _))
  | succ count ih =>
    simp only [_root_.CurrentAFT.BinaryPairedTensor.value, _root_.CurrentAFT.BinaryPairedTensor.lift, _root_.CurrentAFT.RationalWeightProgram.pairedTensor,
      _root_.CurrentAFT.RationalPairedLiftProgram.current, _root_.CurrentAFT.RationalPairedLiftProgram.anchorProfile]
    simp_rw [_root_.CurrentAFT.BinaryReferenceTables.primary_value, _p2mH72]
    rw [_root_.CurrentAFT.BinaryReferenceTables.center_value, _root_.CurrentAFT.BinaryReferenceTables.activation_value]
    have hchild (color : Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) := ih
      (fun rest => kernel (Fin.cons color rest)) (fun rest => ideal (Fin.cons color.val rest))
      (fun rest => (hk (Fin.cons color rest)).trans (congrArg ideal (_p2mH425 color rest)))
      (fun index => groups index.succ)
    simp_rw [hchild]
open _root_.P2Mba49f952 renaming h81 → _p2mH81
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h78 (security bits order : ℕ) (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors security) order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (groups : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security) × Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) arity.val.1.val)
    (centers : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) arity.val.2.val) :
    (_root_.CurrentAFT.BinaryWeightLocal.current security bits order (_root_.CurrentAFT.BinaryReferenceTables.current security bits) table arity groups centers).data.decode =
      _root_.CurrentAFT.RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => _root_.CurrentAFT.BinaryWeightLocal.rawTable security order table arity primary (fun index => (centers.get index).val))
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) := by
  rw [_root_.CurrentAFT.BinaryWeightLocal.current, _p2mH66]
  apply _p2mH81
  intro primary
  rw [_p2mH77, _p2mH80]
  simp only [_root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum.get_ofFn_fun]
open _root_.P2Mba49f952 renaming h78 → CurrentAFT.BinaryWeightLocal.current_value
open _root_.P2Mba49f952 renaming h78 → _p2mH78
end CurrentAFT.BinaryWeightLocal
open _root_.P2Mba49f952 renaming h78 → CurrentAFT.BinaryWeightLocal.current_value
open _root_.P2Mba49f952 renaming h78 → _p2mH78
open _root_.P2Mba49f952 renaming h79 → _p2mH79
open _root_.P2Mba49f952 renaming h80 → _p2mH80
open _root_.P2Mba49f952 renaming h81 → _p2mH81
open _root_.P2Mba49f952 renaming h425 → _p2mH425
end
open _root_.P2Mba49f952 renaming h78 → CurrentAFT.BinaryWeightLocal.current_value
open _root_.P2Mba49f952 renaming h78 → _p2mH78
open _root_.P2Mba49f952 renaming h79 → _p2mH79
open _root_.P2Mba49f952 renaming h80 → _p2mH80
open _root_.P2Mba49f952 renaming h81 → _p2mH81
namespace AFT.BinaryArithmetic.RationalBits.defectWork
end AFT.BinaryArithmetic.RationalBits.defectWork
namespace AFT.BinaryArithmetic.RationalBits.deletionEntryWork
end AFT.BinaryArithmetic.RationalBits.deletionEntryWork
namespace AFT.BinaryArithmetic.RationalBits.deletionMatrixWork
end AFT.BinaryArithmetic.RationalBits.deletionMatrixWork
namespace CurrentAFT.CurrentFlagArray
end CurrentAFT.CurrentFlagArray
namespace CurrentAFT.CurrentFlagArray.component
end CurrentAFT.CurrentFlagArray.component
namespace CurrentAFT.CurrentFlagArray.conditional
end CurrentAFT.CurrentFlagArray.conditional
namespace CurrentAFT.CurrentFlagArray.defect
end CurrentAFT.CurrentFlagArray.defect
namespace CurrentAFT.CurrentFlagArray.deletion
end CurrentAFT.CurrentFlagArray.deletion
namespace CurrentAFT.CurrentFlagArray.iterate
end CurrentAFT.CurrentFlagArray.iterate
namespace CurrentAFT.CurrentFlagArray.iterate.match_1
end CurrentAFT.CurrentFlagArray.iterate.match_1
namespace CurrentAFT.CurrentFlagArray.mean
end CurrentAFT.CurrentFlagArray.mean
namespace CurrentAFT.CurrentFlagArray.projection
end CurrentAFT.CurrentFlagArray.projection
namespace CurrentAFT.CurrentFlagArray.regular
end CurrentAFT.CurrentFlagArray.regular
namespace CurrentAFT.CurrentFlagArray.target
end CurrentAFT.CurrentFlagArray.target
namespace CurrentAFT.CurrentRationalFlagLaw
end CurrentAFT.CurrentRationalFlagLaw
namespace CurrentAFT.CurrentRationalFlagLaw.featureProjectionQ
end CurrentAFT.CurrentRationalFlagLaw.featureProjectionQ
namespace CurrentAFT.CurrentRationalFlagLaw.responseQ
end CurrentAFT.CurrentRationalFlagLaw.responseQ
section
namespace CurrentAFT.CurrentFlagBinary
open AFT AFT.RationalNumerics AFT.BoundaryCalibration AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h153 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector _root_.AFT.BinaryArithmetic.RationalBits charts)
    (point : Fin charts) (index : Fin features) :
    (_root_.CurrentAFT.CurrentFlagBinary.defectTerm feature allowed line spike point index).data.decode =
      if line.get index then 0 else _root_.AFT.BoundaryCalibration.chartFeatureProgram charts colors (feature.get index).get
        (_root_.AFT.BinaryArithmetic.maskSet (allowed.get index)) (fun input => (spike.get input).decode) point := by
  simp only [_root_.CurrentAFT.CurrentFlagBinary.defectTerm, _root_.AFT.BinaryArithmetic.readVector_value]
  split <;> simp_all only [_root_.AFT.BinaryArithmetic.RationalBits.zero_value, _root_.AFT.BinaryArithmetic.RationalBits.chartProjectionTerm, _root_.AFT.BinaryArithmetic.readVector_value, _p2mH9]
open _root_.P2Mba49f952 renaming h153 → _p2mH153
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h152 (charts colors : ℕ) (feature : Fin charts → Fin colors) (allowed : Finset (Fin colors))
    (profile : Fin charts → ℚ) (point : Fin charts) :
    _root_.AFT.BoundaryCalibration.chartFeatureProgram charts colors feature allowed profile point =
      _root_.CurrentAFT.CurrentFlagArray.component charts feature allowed profile point := by
  simp only [_root_.AFT.BoundaryCalibration.chartFeatureProgram, _root_.CurrentAFT.CurrentFlagArray.component, _root_.CurrentAFT.CurrentFlagArray.conditional,
    _root_.CurrentAFT.CurrentFlagArray.mean, _root_.AFT.BoundaryCalibration.chartConditionalProgram, _root_.AFT.BoundaryCalibration.chartExpectationProgram, Fintype.card_fin]
open _root_.P2Mba49f952 renaming h152 → _p2mH152
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h154 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) (point : Fin charts) :
    (_root_.CurrentAFT.CurrentFlagBinary.defect feature allowed line spike point).data.decode =
      _root_.CurrentAFT.CurrentFlagArray.defect charts (fun index => (feature.get index).get)
        (fun index => _root_.AFT.BinaryArithmetic.maskSet (allowed.get index)) line.get (fun input => (spike.get input).decode) point := by
  simp only [_root_.CurrentAFT.CurrentFlagBinary.defect, _root_.AFT.BinaryArithmetic.RationalBits.sumFin_value, _p2mH153, _p2mH152, _root_.CurrentAFT.CurrentFlagArray.defect]
open _root_.P2Mba49f952 renaming h154 → _p2mH154
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h157 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (atom : _root_.AFT.BinaryArithmetic.RationalBits) (spike : Vector _root_.AFT.BinaryArithmetic.RationalBits charts)
    (point : Fin charts) :
    (_root_.CurrentAFT.CurrentFlagBinary.targetEntry feature allowed line atom spike point).data.decode =
      _root_.CurrentAFT.CurrentFlagArray.target charts (fun index => (feature.get index).get)
        (fun index => _root_.AFT.BinaryArithmetic.maskSet (allowed.get index)) line.get atom.decode
        (fun input => (spike.get input).decode) point := by
  simp only [_root_.CurrentAFT.CurrentFlagBinary.targetEntry, _p2mH13, _root_.AFT.BinaryArithmetic.RationalBits.quotient_value, _root_.AFT.BinaryArithmetic.RationalBits.multiply_value, _root_.AFT.BinaryArithmetic.RationalBits.one_value,
    _p2mH154, _root_.CurrentAFT.CurrentFlagArray.target]
open _root_.P2Mba49f952 renaming h157 → _p2mH157
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h155 {charts : ℕ} (safe : Vector Bool charts) (profile : Vector _root_.AFT.BinaryArithmetic.RationalBits charts)
    (point : Fin charts) :
    (_root_.CurrentAFT.CurrentFlagBinary.maskedEntry safe profile point).data.decode = if safe.get point then (profile.get point).decode else 0 := by
  simp only [_root_.CurrentAFT.CurrentFlagBinary.maskedEntry, _root_.AFT.BinaryArithmetic.readVector_value]
  split <;> simp_all only [_root_.AFT.BinaryArithmetic.RationalBits.zero_value]
open _root_.P2Mba49f952 renaming h155 → _p2mH155
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h156 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : _root_.AFT.BinaryArithmetic.RationalBits)
    (steps : ℕ) (point : Fin charts) :
    ((_root_.CurrentAFT.CurrentFlagBinary.regular feature allowed line safe fiber atom steps).data.get point).decode =
      if safe.get point then
        _root_.AFT.RationalNumerics.linearIteration
          (_root_.AFT.BoundaryCalibration.chartDeletionMatrixProgram charts colors features (fun index => (feature.get index).get)
            (fun index => _root_.AFT.BinaryArithmetic.maskSet (allowed.get index)) (_root_.AFT.BinaryArithmetic.maskSet safe))
          (_root_.CurrentAFT.CurrentFlagArray.target charts (fun index => (feature.get index).get)
            (fun index => _root_.AFT.BinaryArithmetic.maskSet (allowed.get index)) line.get atom.decode
            (_root_.AFT.BoundaryCalibration.chartSpikeProgram charts (_root_.AFT.BinaryArithmetic.maskSet fiber))) steps point else 0 := by
  simp only [_root_.CurrentAFT.CurrentFlagBinary.regular, _root_.AFT.BinaryArithmetic.RationalBits.buildArray_get, _p2mH155, _p2mH15, _p2mH7,
    _p2mH157, _p2mH11]
open _root_.P2Mba49f952 renaming h156 → _p2mH156
end CurrentAFT.CurrentFlagBinary
open _root_.P2Mba49f952 renaming h152 → _p2mH152
open _root_.P2Mba49f952 renaming h153 → _p2mH153
open _root_.P2Mba49f952 renaming h154 → _p2mH154
open _root_.P2Mba49f952 renaming h155 → _p2mH155
open _root_.P2Mba49f952 renaming h156 → _p2mH156
open _root_.P2Mba49f952 renaming h157 → _p2mH157
end
open _root_.P2Mba49f952 renaming h152 → _p2mH152
open _root_.P2Mba49f952 renaming h153 → _p2mH153
open _root_.P2Mba49f952 renaming h154 → _p2mH154
open _root_.P2Mba49f952 renaming h155 → _p2mH155
open _root_.P2Mba49f952 renaming h156 → _p2mH156
open _root_.P2Mba49f952 renaming h157 → _p2mH157
namespace AFT.BinaryArithmetic.ChartCounterResult
end AFT.BinaryArithmetic.ChartCounterResult
namespace AFT.BinaryArithmetic.ChartCounterResult.mk
end AFT.BinaryArithmetic.ChartCounterResult.mk
namespace AFT.BinaryArithmetic.binaryChartCoordinates
end AFT.BinaryArithmetic.binaryChartCoordinates
namespace CurrentAFT.CurrentFlagBinary
end CurrentAFT.CurrentFlagBinary
namespace CurrentAFT.CurrentFlagBinary.defectHeight
end CurrentAFT.CurrentFlagBinary.defectHeight
namespace CurrentAFT.CurrentFlagBinary.iterateHeight
end CurrentAFT.CurrentFlagBinary.iterateHeight
namespace CurrentAFT.CurrentFlagBinary.targetWork
end CurrentAFT.CurrentFlagBinary.targetWork
section
namespace CurrentAFT.CurrentFlagBinaryMasks
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h159 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (point : Fin charts) (index : Fin features) :
    (_root_.CurrentAFT.CurrentFlagBinaryMasks.offLineAllowed feature allowed line point index).value = true ↔
      line.get index ≠ true → (allowed.get index).get ((feature.get index).get point) = true := by
  simp only [_root_.CurrentAFT.CurrentFlagBinaryMasks.offLineAllowed, _root_.AFT.BinaryArithmetic.readVector_value, _p2mH28, Bool.or_eq_true, or_iff_not_imp_left]
open _root_.P2Mba49f952 renaming h159 → _p2mH159
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h158 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (base scale shear : Vector (Fin colors) charts)
    (mark : Fin colors) (point : Fin charts) :
    (_root_.CurrentAFT.CurrentFlagBinaryMasks.fiberAt feature allowed line base scale shear mark point).value = true ↔
      base.get point = mark ∧ scale.get point ≠ 0 ∧ shear.get point = 0 ∧
        ∀ index, line.get index ≠ true → (allowed.get index).get ((feature.get index).get point) = true := by
  simp only [_root_.CurrentAFT.CurrentFlagBinaryMasks.fiberAt, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, _root_.AFT.BinaryArithmetic.readVector_value,
    _root_.AFT.BinaryArithmetic.equalCounter_value, _p2mH37, _p2mH159, and_assoc]
  have hscale : (scale.get point).val = 0 ↔ scale.get point = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hshear : (shear.get point).val = 0 ↔ shear.get point = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hn : (_root_.AFT.BinaryArithmetic.equalCounter (scale.get point).val 0).value ≠ true ↔ scale.get point ≠ 0 :=
    not_congr ((_root_.AFT.BinaryArithmetic.equalCounter_value _ _).trans hscale)
  simp only [Fin.val_inj, hn, hshear]
open _root_.P2Mba49f952 renaming h158 → _p2mH158
end CurrentAFT.CurrentFlagBinaryMasks
open _root_.P2Mba49f952 renaming h158 → _p2mH158
open _root_.P2Mba49f952 renaming h159 → _p2mH159
end
open _root_.P2Mba49f952 renaming h158 → _p2mH158
open _root_.P2Mba49f952 renaming h159 → _p2mH159
namespace AFT.BinaryArithmetic.modularDifferenceWork
end AFT.BinaryArithmetic.modularDifferenceWork
namespace AFT.BinaryArithmetic.protectedFeatureWork
end AFT.BinaryArithmetic.protectedFeatureWork
namespace AFT.BinaryArithmetic.protectedMetadata
end AFT.BinaryArithmetic.protectedMetadata
namespace AFT.BinaryArithmetic.protectedMetadataCore
end AFT.BinaryArithmetic.protectedMetadataCore
namespace AFT.BinaryArithmetic.protectedMetadataWork
end AFT.BinaryArithmetic.protectedMetadataWork
namespace CurrentAFT.CurrentFlagBinaryMasks
end CurrentAFT.CurrentFlagBinaryMasks
namespace CurrentAFT.CurrentFlagBinaryMasks.fiberAt
end CurrentAFT.CurrentFlagBinaryMasks.fiberAt
namespace CurrentAFT.CurrentFlagBinaryMasks.fiberWork
end CurrentAFT.CurrentFlagBinaryMasks.fiberWork
namespace CurrentAFT.CurrentFlagBinaryMasks.offLineAllowed
end CurrentAFT.CurrentFlagBinaryMasks.offLineAllowed
namespace CurrentAFT.CurrentFlagBinaryMasks.onLine
end CurrentAFT.CurrentFlagBinaryMasks.onLine
namespace CurrentAFT.CurrentFlagBinaryMasks.onLineWork
end CurrentAFT.CurrentFlagBinaryMasks.onLineWork
section
namespace CurrentAFT.CurrentFlagBinaryMetadata
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits CurrentFlagBinaryMasks
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h160 (modulus : ℕ) [NeZero modulus] (value : Fin modulus) :
    (ZMod.finEquiv modulus) value = (value.val : ZMod modulus) := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => apply Fin.ext; exact (Nat.mod_eq_of_lt value.isLt).symm
open _root_.P2Mba49f952 renaming h160 → _p2mH160
end CurrentAFT.CurrentFlagBinaryMetadata
open _root_.P2Mba49f952 renaming h160 → _p2mH160
end
open _root_.P2Mba49f952 renaming h160 → _p2mH160
namespace CurrentAFT.CurrentFlagBinaryMetadata
end CurrentAFT.CurrentFlagBinaryMetadata
namespace CurrentAFT.CurrentFlagBinaryMetadata.build
end CurrentAFT.CurrentFlagBinaryMetadata.build
namespace CurrentAFT.CurrentFlagIteration
end CurrentAFT.CurrentFlagIteration
namespace CurrentAFT.CurrentFlagIteration.iterationMatrix
end CurrentAFT.CurrentFlagIteration.iterationMatrix
namespace CurrentAFT.CurrentFlagMetadataSemantics
end CurrentAFT.CurrentFlagMetadataSemantics
namespace CurrentAFT.CurrentFlagTargetNorm
end CurrentAFT.CurrentFlagTargetNorm
section
namespace CurrentAFT.CurrentFlagPublicProgram
open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagFiniteCoordinates CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h164 : _root_.CurrentAFT.CurrentFlagPublicProgram.half.data.decode = (1 / 2 : ℚ) := by
  norm_num [_root_.CurrentAFT.CurrentFlagPublicProgram.half, _root_.AFT.BinaryArithmetic.RationalBits.quotient_value, _root_.AFT.BinaryArithmetic.RationalBits.one_value, _root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value]
open _root_.P2Mba49f952 renaming h164 → _p2mH164
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentFlagPublicProgram.publicProgramPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagPublicProgram.publicProgramNeZero
end
end CurrentAFT.CurrentFlagPublicProgram
open _root_.P2Mba49f952 renaming h164 → _p2mH164
end
open _root_.P2Mba49f952 renaming h164 → _p2mH164
namespace CurrentAFT.CurrentFlagIdealArrays
end CurrentAFT.CurrentFlagIdealArrays
namespace CurrentAFT.CurrentFlagIdealArrays.markedLaw
end CurrentAFT.CurrentFlagIdealArrays.markedLaw
namespace CurrentAFT.CurrentFlagIdealArrays.model
end CurrentAFT.CurrentFlagIdealArrays.model
namespace CurrentAFT.CurrentFlagIdealArrays.regularLaw
end CurrentAFT.CurrentFlagIdealArrays.regularLaw
namespace CurrentAFT.CurrentFlagProgram
end CurrentAFT.CurrentFlagProgram
namespace CurrentAFT.CurrentFlagProgram.table
end CurrentAFT.CurrentFlagProgram.table
section
namespace CurrentAFT.CurrentFlagWeightArray
open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagPublicProgram CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h165 {charts : ℕ} (raw : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) (point : Fin charts) :
    (_root_.CurrentAFT.CurrentFlagWeightArray.entry raw point).data.decode = (raw.get point).decode / charts := by
  simp only [_root_.CurrentAFT.CurrentFlagWeightArray.entry, _root_.AFT.BinaryArithmetic.RationalBits.quotient_value, _root_.AFT.BinaryArithmetic.readVector_value, _root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value]
open _root_.P2Mba49f952 renaming h165 → _p2mH165
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h166 {charts : ℕ} (raw : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) (point : Fin charts) :
    ((_root_.CurrentAFT.CurrentFlagWeightArray.scale raw).data.get point).decode = (raw.get point).decode / charts := by
  simp only [_root_.CurrentAFT.CurrentFlagWeightArray.scale, _root_.AFT.BinaryArithmetic.RationalBits.buildArray_get, _p2mH165]
open _root_.P2Mba49f952 renaming h166 → _p2mH166
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentFlagWeightArray.flagWeightPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagWeightArray.flagWeightNeZero
end
end CurrentAFT.CurrentFlagWeightArray
open _root_.P2Mba49f952 renaming h165 → _p2mH165
open _root_.P2Mba49f952 renaming h166 → _p2mH166
end
open _root_.P2Mba49f952 renaming h165 → _p2mH165
open _root_.P2Mba49f952 renaming h166 → _p2mH166
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint
namespace CurrentAFT.CurrentFlagBranchDraw
end CurrentAFT.CurrentFlagBranchDraw
namespace CurrentAFT.CurrentFlagBranchDraw.marked
end CurrentAFT.CurrentFlagBranchDraw.marked
namespace CurrentAFT.CurrentFlagWeightArray
end CurrentAFT.CurrentFlagWeightArray
namespace CurrentAFT.CurrentFlagWeightArray.markedWeights
end CurrentAFT.CurrentFlagWeightArray.markedWeights
section
namespace CurrentAFT.CurrentFlagJointDraw
open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentFlagBranchDraw
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h163 (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : _root_.CurrentAFT.CurrentFlagJointDraw.Tape modulus drawBits) :
    (_root_.CurrentAFT.CurrentFlagJointDraw.draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value =
      (word.1, if word.1 then (_root_.CurrentAFT.CurrentFlagBranchDraw.marked cutoff modulus baselineSign baseline mark drawBits word.2).value
        else (_root_.CurrentAFT.CurrentFlagBranchDraw.regular cutoff modulus baselineSign baseline mark precisionBits drawBits word.2).value) := by
  cases h : word.1 <;> simp only [_root_.CurrentAFT.CurrentFlagJointDraw.draw, h, Bool.false_eq_true, if_false, if_true]
open _root_.P2Mba49f952 renaming h163 → _p2mH163
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentFlagJointDraw.jointDrawPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagJointDraw.jointDrawNeZero
end
end CurrentAFT.CurrentFlagJointDraw
open _root_.P2Mba49f952 renaming h163 → _p2mH163
end
open _root_.P2Mba49f952 renaming h163 → _p2mH163
namespace CurrentAFT.CurrentFlagChartDraw
end CurrentAFT.CurrentFlagChartDraw
namespace CurrentAFT.CurrentFlagChartDraw.draw
end CurrentAFT.CurrentFlagChartDraw.draw
namespace CurrentAFT.PublicParameterProgram
end CurrentAFT.PublicParameterProgram
namespace CurrentAFT.PublicParameterProgram.checkedPower
end CurrentAFT.PublicParameterProgram.checkedPower
namespace CurrentAFT.PublicParameterProgram.checkedProduct
end CurrentAFT.PublicParameterProgram.checkedProduct
namespace CurrentAFT.PublicParameterProgram.checkedScan
end CurrentAFT.PublicParameterProgram.checkedScan
namespace CurrentAFT.PublicParameterProgram.primeTest
end CurrentAFT.PublicParameterProgram.primeTest
namespace CurrentAFT.PublicParameterProgram.testWork
end CurrentAFT.PublicParameterProgram.testWork
namespace CurrentAFT.PublicParameterProgram.workBound
end CurrentAFT.PublicParameterProgram.workBound
namespace CurrentAFT.PublicParameterProgram.workPolynomial
end CurrentAFT.PublicParameterProgram.workPolynomial
section
namespace CurrentAFT.CurrentPublicShiftProgram
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h181 (modulus primary : ℕ) (coin : Bool) :
    (_root_.CurrentAFT.CurrentPublicShiftProgram.direction modulus primary coin).value =
      if 2 * primary < modulus - 1 then false else if modulus - 1 < 2 * primary then true else coin := by
  simp only [_root_.CurrentAFT.CurrentPublicShiftProgram.direction, _root_.AFT.BinaryArithmetic.doubleCounter_value, _root_.AFT.BinaryArithmetic.differenceCounter_value, _root_.AFT.BinaryArithmetic.lessCounter_value]
open _root_.P2Mba49f952 renaming h181 → _p2mH181
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h182 (modulus width primary index : ℕ) (coin : Bool) (blurFirst blurSecond : ℤ) :
    (_root_.CurrentAFT.CurrentPublicShiftProgram.program modulus width primary index coin blurFirst blurSecond).value.decode =
      (if (_root_.CurrentAFT.CurrentPublicShiftProgram.direction modulus primary coin).value then ((width + index : ℕ) : ℤ) else -((width + index : ℕ) : ℤ)) +
        blurFirst - blurSecond := by
  simp only [_root_.CurrentAFT.CurrentPublicShiftProgram.program]
  rw [_root_.AFT.BinaryArithmetic.IntegerBits.add_value, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value]
  simp only [_root_.AFT.BinaryArithmetic.IntegerBits.decode, _root_.AFT.BinaryArithmetic.signedValue, _root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
  cases (_root_.CurrentAFT.CurrentPublicShiftProgram.direction modulus primary coin).value <;> simp <;> ring
open _root_.P2Mba49f952 renaming h182 → _p2mH182
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h180 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) :
    (_root_.CurrentAFT.CurrentPublicShiftProgram.current security primary seed).value.decode = _root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed := by
  simp only [_root_.CurrentAFT.CurrentPublicShiftProgram.current, _p2mH182, _root_.CurrentAFT.PublicParameterProgram.modulus_value, _root_.AFT.BinaryArithmetic.addCounter_value,
    _root_.AFT.BinaryArithmetic.powerCounter_value, _p2mH181, _root_.CurrentAFT.ActualPublicLegCharge.publicShift, _root_.CurrentAFT.ActualPublicLegCharge.signedOffset,
    _root_.CurrentAFT.InwardAnchor.positiveDirection, _root_.CurrentAFT.InwardAnchor.offset, _root_.CurrentAFT.Parameters.anchorWidth, _root_.CurrentAFT.Parameters.scale, _root_.CurrentAFT.Parameters.base,
    ← pow_mul, Nat.cast_add]
open _root_.P2Mba49f952 renaming h180 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2Mba49f952 renaming h180 → _p2mH180
end CurrentAFT.CurrentPublicShiftProgram
open _root_.P2Mba49f952 renaming h180 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2Mba49f952 renaming h180 → _p2mH180
open _root_.P2Mba49f952 renaming h181 → _p2mH181
open _root_.P2Mba49f952 renaming h182 → _p2mH182
end
open _root_.P2Mba49f952 renaming h180 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2Mba49f952 renaming h180 → _p2mH180
open _root_.P2Mba49f952 renaming h181 → _p2mH181
open _root_.P2Mba49f952 renaming h182 → _p2mH182
namespace CurrentAFT.BinaryReferenceTables
end CurrentAFT.BinaryReferenceTables
namespace CurrentAFT.BinaryReferenceTables.Result
end CurrentAFT.BinaryReferenceTables.Result
namespace CurrentAFT.BinaryReferenceTables.Result.mk
end CurrentAFT.BinaryReferenceTables.Result.mk
namespace CurrentAFT.BinaryReferenceTables.centerHeightPolynomial
end CurrentAFT.BinaryReferenceTables.centerHeightPolynomial
namespace CurrentAFT.BinaryReferenceTables.current
end CurrentAFT.BinaryReferenceTables.current
namespace CurrentAFT.BinaryReferenceTables.currentWorkPolynomial
end CurrentAFT.BinaryReferenceTables.currentWorkPolynomial
namespace CurrentAFT.BinaryReferenceTables.heightPolynomial
end CurrentAFT.BinaryReferenceTables.heightPolynomial
namespace CurrentAFT.BinaryReferenceTables.marginPolynomial
end CurrentAFT.BinaryReferenceTables.marginPolynomial
namespace CurrentAFT.BinaryReferenceTables.referenceHeightPolynomial
end CurrentAFT.BinaryReferenceTables.referenceHeightPolynomial
namespace CurrentAFT.CurrentProbabilityArrayDraw
end CurrentAFT.CurrentProbabilityArrayDraw
namespace CurrentAFT.CurrentProbabilityArrayDraw.ProbabilityArray
end CurrentAFT.CurrentProbabilityArrayDraw.ProbabilityArray
namespace CurrentAFT.CurrentProbabilityArrayDraw.ProbabilityArray.mk
end CurrentAFT.CurrentProbabilityArrayDraw.ProbabilityArray.mk
namespace CurrentAFT.CurrentProbabilityArrayDraw.draw
end CurrentAFT.CurrentProbabilityArrayDraw.draw
namespace CurrentAFT.CurrentProbabilityArrayDraw.positiveDraw
end CurrentAFT.CurrentProbabilityArrayDraw.positiveDraw
namespace CurrentAFT.CurrentProbabilityArrayDraw.workBound
end CurrentAFT.CurrentProbabilityArrayDraw.workBound
namespace CurrentAFT.CurrentSafePaletteIndex
end CurrentAFT.CurrentSafePaletteIndex
namespace CurrentAFT.CurrentSafePaletteIndex.count
end CurrentAFT.CurrentSafePaletteIndex.count
namespace CurrentAFT.CurrentSafePaletteIndex.embed
end CurrentAFT.CurrentSafePaletteIndex.embed
namespace CurrentAFT.CurrentSafePaletteIndex.equiv
end CurrentAFT.CurrentSafePaletteIndex.equiv
namespace CurrentAFT.CurrentSafePaletteIndex.uniformLaw
end CurrentAFT.CurrentSafePaletteIndex.uniformLaw
section
namespace CurrentAFT.CurrentReferenceDraw
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentProbabilityArrayDraw
open scoped BigOperators
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
attribute [local instance] _root_.CurrentAFT.CurrentReferenceDraw.safeFintype
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h183 (security tableBits drawBits : ℕ) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache security tableBits)
    (word : Fin (drawBits + (_root_.CurrentAFT.CurrentReferenceDraw.counts security).safe + 1) → Fin 2) :
    (_root_.CurrentAFT.CurrentReferenceDraw.bodyDraw security tableBits drawBits cache word).value =
      _root_.CurrentAFT.CurrentReferenceDraw.bodyEquiv security (_root_.CurrentAFT.CurrentProbabilityArrayDraw.positiveDraw _ (_root_.CurrentAFT.CurrentReferenceDraw.safe_positive security) cache.body drawBits word).value := by
  apply Subtype.ext
  apply Fin.ext
  change (_root_.AFT.BinaryArithmetic.addCounter (_root_.CurrentAFT.CurrentReferenceDraw.counts security).margin _).count = _
  rw [_root_.AFT.BinaryArithmetic.addCounter_value, _root_.CurrentAFT.CurrentReferenceDraw.bodyEquiv_value]
open _root_.P2Mba49f952 renaming h183 → _p2mH183
noncomputable section
open scoped Classical
end
end CurrentAFT.CurrentReferenceDraw
open _root_.P2Mba49f952 renaming h183 → _p2mH183
end
open _root_.P2Mba49f952 renaming h183 → _p2mH183
namespace CurrentAFT.BinaryProposalGuard.allFin
end CurrentAFT.BinaryProposalGuard.allFin
namespace CurrentAFT.BinaryProposalGuard.allFin.match_1
end CurrentAFT.BinaryProposalGuard.allFin.match_1
namespace CurrentAFT.BinaryProposalGuard.lowerCheck
end CurrentAFT.BinaryProposalGuard.lowerCheck
namespace CurrentAFT.BinaryProposalGuard.primary
end CurrentAFT.BinaryProposalGuard.primary
namespace CurrentAFT.BinaryProposalGuard.threshold
end CurrentAFT.BinaryProposalGuard.threshold
namespace CurrentAFT.BinaryProposalGuard.thresholdWork
end CurrentAFT.BinaryProposalGuard.thresholdWork
namespace CurrentAFT.BinaryProposalGuard.uniformTable
end CurrentAFT.BinaryProposalGuard.uniformTable
namespace CurrentAFT.CyclePatternProgram
end CurrentAFT.CyclePatternProgram
namespace CurrentAFT.CyclePatternProgram.evaluate
end CurrentAFT.CyclePatternProgram.evaluate
namespace CurrentAFT.CycleSelections
end CurrentAFT.CycleSelections
namespace CurrentAFT.CycleSelections.selectionLaw
end CurrentAFT.CycleSelections.selectionLaw
section
namespace CurrentAFT.BinaryDistinctTuples
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h62 (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) (first second : Fin count) :
    (_root_.CurrentAFT.BinaryDistinctTuples.pairCheck pool count hp word first second).value = true ↔
      (first.val < second.val → word.get first ≠ word.get second) := by
  simp only [_root_.CurrentAFT.BinaryDistinctTuples.pairCheck, _root_.AFT.BinaryArithmetic.readVector_value]
  by_cases hpos : (_root_.AFT.BinaryArithmetic.lessCounter first.val second.val).value = true
  · rw [if_pos hpos, Bool.or_eq_true, _root_.AFT.BinaryArithmetic.lessCounter_value, _root_.AFT.BinaryArithmetic.lessCounter_value]
    have hlt := (_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mp hpos
    constructor
    · intro h _ he
      have he' := congrArg Fin.val he
      omega
    · intro h
      have hn := h hlt
      have hn' : (word.get first).val ≠ (word.get second).val := fun he => hn (Fin.ext he)
      omega
  · rw [if_neg hpos]
    have hnot : ¬ first.val < second.val := fun h => hpos ((_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mpr h)
    simp only [hnot, false_implies]
open _root_.P2Mba49f952 renaming h62 → _p2mH62
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h59 (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) :
    (_root_.CurrentAFT.BinaryDistinctTuples.current pool count hp word).value = true ↔ Function.Injective word.get := by
  simp only [_root_.CurrentAFT.BinaryDistinctTuples.current, _root_.CurrentAFT.BinaryProposalGuard.allFin_value, _p2mH62]
  constructor
  · intro h first second he
    by_contra hn
    have hv : first.val ≠ second.val := fun hv => hn (Fin.ext hv)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · exact h first second hlt he
    · exact h second first hgt he.symm
  · intro h first second hlt he
    have hi := h he
    have hv := congrArg Fin.val hi
    omega
open _root_.P2Mba49f952 renaming h59 → CurrentAFT.BinaryDistinctTuples.current_value
open _root_.P2Mba49f952 renaming h59 → _p2mH59
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h60 (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → _root_.AFT.BinaryArithmetic.RationalResult)
    (word : Vector (Fin pool) count) :
    (_root_.CurrentAFT.BinaryDistinctTuples.guarded pool count hp kernel word).data.decode =
      if Function.Injective word.get then (kernel word).data.decode else 0 := by
  unfold _root_.CurrentAFT.BinaryDistinctTuples.guarded
  try dsimp only
  by_cases h : (_root_.CurrentAFT.BinaryDistinctTuples.current pool count hp word).value = true
  · simp only [if_pos h, if_pos ((_p2mH59 _ _ _ _).mp h)]
  · simp only [if_neg h, if_neg (fun h' => h ((_p2mH59 _ _ _ _).mpr h')), _root_.AFT.BinaryArithmetic.RationalBits.zero_value]
open _root_.P2Mba49f952 renaming h60 → CurrentAFT.BinaryDistinctTuples.guarded_value
open _root_.P2Mba49f952 renaming h60 → _p2mH60
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h63 (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → _root_.AFT.BinaryArithmetic.RationalResult) :
    (_root_.CurrentAFT.BinaryDistinctTuples.sum pool count hp kernel).data.decode =
      ∑ selection : Fin count ↪ Fin pool, (kernel (Vector.ofFn selection)).data.decode := by
  letI : Fintype {word : Fin count → Fin pool // Function.Injective word} := Fintype.ofFinite _
  rw [_root_.CurrentAFT.BinaryDistinctTuples.sum, _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum.current_value]
  simp only [_p2mH60, _root_.InfoLossLARNativeSupplements.ha8fcea89e723dc23.CurrentAFT.BinaryTupleSum.get_ofFn_fun]
  have hs := (Finset.sum_subtype (p := fun word : Fin count → Fin pool => Function.Injective word) (F := inferInstance)
    (Finset.univ.filter Function.Injective) (by simp) (fun word => (kernel (Vector.ofFn word)).data.decode))
  rw [Finset.sum_filter] at hs
  rw [hs]
  exact (Equiv.sum_comp (_root_.CurrentAFT.CyclePatternProgram.selectionEquiv pool count)
    (fun word => (kernel (Vector.ofFn word.val)).data.decode)).symm
open _root_.P2Mba49f952 renaming h63 → CurrentAFT.BinaryDistinctTuples.sum_value
open _root_.P2Mba49f952 renaming h63 → _p2mH63
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h61 (pool count : ℕ) (hp : 0 < pool) :
    (_root_.CurrentAFT.BinaryDistinctTuples.normalizer pool count hp).data.decode = (pool.descFactorial count:ℚ) := by
  rw [_root_.CurrentAFT.BinaryDistinctTuples.normalizer, _p2mH63]
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.one_value, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_embedding_eq, Fintype.card_fin]
open _root_.P2Mba49f952 renaming h61 → _p2mH61
end
open _root_.P2Mba49f952 renaming h61 → _p2mH61
open _root_.P2Mba49f952 renaming h63 → CurrentAFT.BinaryDistinctTuples.sum_value
open _root_.P2Mba49f952 renaming h63 → _p2mH63
end CurrentAFT.BinaryDistinctTuples
open _root_.P2Mba49f952 renaming h59 → CurrentAFT.BinaryDistinctTuples.current_value
open _root_.P2Mba49f952 renaming h59 → _p2mH59
open _root_.P2Mba49f952 renaming h60 → CurrentAFT.BinaryDistinctTuples.guarded_value
open _root_.P2Mba49f952 renaming h60 → _p2mH60
open _root_.P2Mba49f952 renaming h61 → _p2mH61
open _root_.P2Mba49f952 renaming h62 → _p2mH62
open _root_.P2Mba49f952 renaming h63 → CurrentAFT.BinaryDistinctTuples.sum_value
open _root_.P2Mba49f952 renaming h63 → _p2mH63
end
open _root_.P2Mba49f952 renaming h59 → CurrentAFT.BinaryDistinctTuples.current_value
open _root_.P2Mba49f952 renaming h59 → _p2mH59
open _root_.P2Mba49f952 renaming h60 → CurrentAFT.BinaryDistinctTuples.guarded_value
open _root_.P2Mba49f952 renaming h60 → _p2mH60
open _root_.P2Mba49f952 renaming h61 → _p2mH61
open _root_.P2Mba49f952 renaming h62 → _p2mH62
open _root_.P2Mba49f952 renaming h63 → CurrentAFT.BinaryDistinctTuples.sum_value
open _root_.P2Mba49f952 renaming h63 → _p2mH63
namespace AFT.BinaryArithmetic.binaryRationalDraw
end AFT.BinaryArithmetic.binaryRationalDraw
namespace AFT.BinaryArithmetic.binaryRationalDrawWork
end AFT.BinaryArithmetic.binaryRationalDrawWork
namespace AFT.BinaryArithmetic.supplementFirst_ofFn
end AFT.BinaryArithmetic.supplementFirst_ofFn
namespace CurrentAFT.CurrentGaussianBits
end CurrentAFT.CurrentGaussianBits
namespace CurrentAFT.CurrentGaussianBits.budget
end CurrentAFT.CurrentGaussianBits.budget
namespace CurrentAFT.CurrentGaussianBits.table
end CurrentAFT.CurrentGaussianBits.table
namespace CurrentAFT.CurrentGaussianBits.tableWork
end CurrentAFT.CurrentGaussianBits.tableWork
namespace CurrentAFT.CurrentGaussianBits.widthCode
end CurrentAFT.CurrentGaussianBits.widthCode
namespace CurrentAFT.CurrentGaussianBits.widthWork
end CurrentAFT.CurrentGaussianBits.widthWork
namespace CurrentAFT.CurrentGaussianBits.workPolynomial
end CurrentAFT.CurrentGaussianBits.workPolynomial
namespace CurrentAFT.WindowGaussianSampler
end CurrentAFT.WindowGaussianSampler
namespace CurrentAFT.WindowGaussianSampler.squaredWidth
end CurrentAFT.WindowGaussianSampler.squaredWidth
section
namespace CurrentAFT.CurrentWindowDraw
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open AFT.RationalRejectionProgram AFT.FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h430 {count : ℕ} (first second : Fin (count + 1) → ℚ) (heq : first = second)
    (hn : ∀ index, 0 ≤ first index) (hs : ∑ index, first index = 1)
    (hn' : ∀ index, 0 ≤ second index) (hs' : ∑ index, second index = 1)
    (bits : ℕ) (word : Fin bits → Fin 2) :
    _root_.AFT.RationalFiniteQuantization.draw first hn hs bits word = _root_.AFT.RationalFiniteQuantization.draw second hn' hs' bits word := by
  subst second
  rfl
open _root_.P2Mba49f952 renaming h430 → _p2mH430
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h185 (security cutoff bits : ℕ) (word : Fin (_root_.AFT.RationalNumerics.windowTicketBits cutoff bits) → Fin 2) :
    (_root_.CurrentAFT.CurrentWindowDraw.draw security cutoff bits word).value = _root_.CurrentAFT.WindowGaussianSampler.draw security cutoff bits word := by
  let weights := _root_.CurrentAFT.CurrentGaussianBits.table security cutoff (bits + 1)
  let selected := _root_.AFT.BinaryArithmetic.binaryRationalDraw weights.data (_root_.AFT.RationalNumerics.windowTicketBits cutoff bits) word
  have hw : (fun index => (weights.data.get index).decode) =
      _root_.AFT.RationalNumerics.windowGaussianWeights (_root_.CurrentAFT.WindowGaussianSampler.squaredWidth security) cutoff (bits + 1) :=
    funext (_root_.CurrentAFT.CurrentGaussianBits.table_value security cutoff (bits + 1))
  have hs := _root_.AFT.BinaryArithmetic.binaryRationalDraw_value weights.data (_root_.CurrentAFT.CurrentWindowDraw.table_nonneg security cutoff (bits + 1))
    (_root_.CurrentAFT.CurrentWindowDraw.table_sum security cutoff (bits + 1)) (_root_.AFT.RationalNumerics.windowTicketBits cutoff bits) word
  rw [_p2mH430 _ _ hw (_root_.CurrentAFT.CurrentWindowDraw.table_nonneg security cutoff (bits + 1)) (_root_.CurrentAFT.CurrentWindowDraw.table_sum security cutoff (bits + 1))
    (_root_.AFT.RationalNumerics.windowGaussianWeights_nonneg _ _ _) (_root_.AFT.RationalNumerics.windowGaussianWeights_sum _ _ _) _ _] at hs
  have hi : selected.value = ((_root_.AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff).symm (_root_.CurrentAFT.WindowGaussianSampler.draw security cutoff bits word)).val := by
    simpa only [_root_.CurrentAFT.WindowGaussianSampler.draw, _root_.AFT.RationalNumerics.windowGaussianDraw, Equiv.symm_apply_apply] using hs
  apply Subtype.ext
  change (_root_.AFT.BinaryArithmetic.integerDifference selected.value cutoff).value = (_root_.CurrentAFT.WindowGaussianSampler.draw security cutoff bits word).val
  rw [_root_.AFT.BinaryArithmetic.integerDifference_value, hi]
  exact congrArg Subtype.val ((_root_.AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff).apply_symm_apply (_root_.CurrentAFT.WindowGaussianSampler.draw security cutoff bits word))
open _root_.P2Mba49f952 renaming h185 → _p2mH185
noncomputable section
open scoped Classical
end
end CurrentAFT.CurrentWindowDraw
open _root_.P2Mba49f952 renaming h185 → _p2mH185
open _root_.P2Mba49f952 renaming h430 → _p2mH430
end
open _root_.P2Mba49f952 renaming h185 → _p2mH185
namespace AFT.RationalNumerics.windowGaussianDraw
end AFT.RationalNumerics.windowGaussianDraw
namespace CurrentAFT.CurrentWindowDraw
end CurrentAFT.CurrentWindowDraw
namespace CurrentAFT.WindowGaussianSampler.draw
end CurrentAFT.WindowGaussianSampler.draw
section
namespace CurrentAFT.CurrentEdgeDrawProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h145 (security first second bits : ℕ) (h : first = second)
    (word : Fin (_root_.AFT.RationalNumerics.windowTicketBits second bits) → Fin 2) :
    _root_.CurrentAFT.CurrentEdgeDrawProgram.castWindow h (_root_.CurrentAFT.CurrentWindowDraw.draw security first bits
      (cast (congrArg (fun cutoff => Fin (_root_.AFT.RationalNumerics.windowTicketBits cutoff bits) → Fin 2) h.symm) word)) =
      _root_.CurrentAFT.CurrentWindowDraw.draw security second bits word := by
  subst second
  rfl
open _root_.P2Mba49f952 renaming h145 → _p2mH145
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h146 (security bits : ℕ) (word : Fin (_root_.AFT.RationalNumerics.windowTicketBits (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) bits) → Fin 2) :
    (_root_.CurrentAFT.CurrentEdgeDrawProgram.draw security bits word).value = _root_.CurrentAFT.WindowGaussianSampler.draw security (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) bits word := by
  change (_root_.CurrentAFT.CurrentEdgeDrawProgram.castWindow (_root_.CurrentAFT.CurrentEdgeDrawProgram.cutoff_value security) (_root_.CurrentAFT.CurrentWindowDraw.draw security (_root_.CurrentAFT.CurrentEdgeDrawProgram.cutoffProgram security).quotient bits
    (cast (congrArg (fun cutoff => Fin (_root_.AFT.RationalNumerics.windowTicketBits cutoff bits) → Fin 2) (_root_.CurrentAFT.CurrentEdgeDrawProgram.cutoff_value security).symm) word))).value = _
  rw [_p2mH145, _p2mH185]
open _root_.P2Mba49f952 renaming h146 → _p2mH146
noncomputable section
open scoped Classical
end
end CurrentAFT.CurrentEdgeDrawProgram
open _root_.P2Mba49f952 renaming h145 → _p2mH145
open _root_.P2Mba49f952 renaming h146 → _p2mH146
end
open _root_.P2Mba49f952 renaming h145 → _p2mH145
open _root_.P2Mba49f952 renaming h146 → _p2mH146
namespace CurrentAFT.ActualPublicLegCharge
end CurrentAFT.ActualPublicLegCharge
namespace CurrentAFT.ActualPublicLegCharge.PublicSeed
end CurrentAFT.ActualPublicLegCharge.PublicSeed
namespace CurrentAFT.ActualPublicLegCharge.PublicSeed.mk
end CurrentAFT.ActualPublicLegCharge.PublicSeed.mk
namespace CurrentAFT.ActualPublicLegCharge.seedLaw
end CurrentAFT.ActualPublicLegCharge.seedLaw
namespace CurrentAFT.CurrentReferenceDraw
end CurrentAFT.CurrentReferenceDraw
namespace CurrentAFT.CurrentReferenceDraw.Cache
end CurrentAFT.CurrentReferenceDraw.Cache
namespace CurrentAFT.CurrentReferenceDraw.Cache.mk
end CurrentAFT.CurrentReferenceDraw.Cache.mk
namespace CurrentAFT.CurrentReferenceDraw.Counts
end CurrentAFT.CurrentReferenceDraw.Counts
namespace CurrentAFT.CurrentReferenceDraw.Counts.mk
end CurrentAFT.CurrentReferenceDraw.Counts.mk
namespace CurrentAFT.CurrentReferenceDraw.bodyDraw
end CurrentAFT.CurrentReferenceDraw.bodyDraw
namespace CurrentAFT.CurrentReferenceDraw.bodyDrawLaw
end CurrentAFT.CurrentReferenceDraw.bodyDrawLaw
namespace CurrentAFT.CurrentReferenceDraw.centerData
end CurrentAFT.CurrentReferenceDraw.centerData
namespace CurrentAFT.CurrentReferenceDraw.counts
end CurrentAFT.CurrentReferenceDraw.counts
section
namespace CurrentAFT.CurrentActivationDraw
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentProbabilityArrayDraw CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h85 (security tableBits : ℕ) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache security tableBits) (index : Fin 2) :
    ((_root_.CurrentAFT.CurrentActivationDraw.table security tableBits cache).value.data.get index).decode =
      if index = 0 then 1 - cache.activation.decode else cache.activation.decode := by
  simp only [_root_.CurrentAFT.CurrentActivationDraw.table, Vector.get_ofFn]
  split_ifs <;> simp only [_root_.AFT.BinaryArithmetic.RationalBits.add_value, _root_.AFT.BinaryArithmetic.RationalBits.one_value, _root_.AFT.BinaryArithmetic.RationalBits.negate_value, sub_eq_add_neg]
open _root_.P2Mba49f952 renaming h85 → _p2mH85
noncomputable section
open scoped Classical
end
end CurrentAFT.CurrentActivationDraw
open _root_.P2Mba49f952 renaming h85 → _p2mH85
end
open _root_.P2Mba49f952 renaming h85 → _p2mH85
namespace AFT.BinaryArithmetic.binaryUniformDraw
end AFT.BinaryArithmetic.binaryUniformDraw
namespace CurrentAFT.CurrentUniformDraw
end CurrentAFT.CurrentUniformDraw
namespace CurrentAFT.CurrentUniformDraw.law
end CurrentAFT.CurrentUniformDraw.law
section
namespace CurrentAFT.CurrentSafeDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h184 (security bits : ℕ) (word : _root_.CurrentAFT.CurrentSafeDraw.Tape security bits) :
    (_root_.CurrentAFT.CurrentSafeDraw.draw security bits word).value = (_root_.CurrentAFT.CurrentReferenceDraw.bodyEquiv security
      (_root_.AFT.BinaryArithmetic.binaryUniformDraw (_root_.CurrentAFT.CurrentReferenceDraw.counts security).safe (_root_.CurrentAFT.CurrentReferenceDraw.safe_positive security) bits word).value).val := by
  apply Fin.ext
  change (_root_.AFT.BinaryArithmetic.addCounter (_root_.CurrentAFT.CurrentReferenceDraw.counts security).margin _).count = _
  rw [_root_.AFT.BinaryArithmetic.addCounter_value, _root_.CurrentAFT.CurrentReferenceDraw.bodyEquiv_value]
open _root_.P2Mba49f952 renaming h184 → _p2mH184
noncomputable section
open scoped Classical
end
end CurrentAFT.CurrentSafeDraw
open _root_.P2Mba49f952 renaming h184 → _p2mH184
end
open _root_.P2Mba49f952 renaming h184 → _p2mH184
namespace CurrentAFT.BackgroundRates
end CurrentAFT.BackgroundRates
namespace CurrentAFT.BackgroundRates.ordinaryPool
end CurrentAFT.BackgroundRates.ordinaryPool
namespace CurrentAFT.CurrentProposalDimensions
end CurrentAFT.CurrentProposalDimensions
namespace CurrentAFT.CurrentProposalDimensions.Result
end CurrentAFT.CurrentProposalDimensions.Result
namespace CurrentAFT.CurrentProposalDimensions.Result.mk
end CurrentAFT.CurrentProposalDimensions.Result.mk
namespace CurrentAFT.CurrentProposalDimensions.current
end CurrentAFT.CurrentProposalDimensions.current
section
namespace CurrentAFT.CurrentPublicIndexProgram
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram CurrentProposalDimensions
set_option maxHeartbeats 500000
attribute [local irreducible] CurrentProposalDimensions.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h179 (security : ℕ) (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).controls) :
    (_root_.CurrentAFT.CurrentPublicIndexProgram.decode security index).value = _root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv security index := by
  apply finSumFinEquiv.injective
  have he : finSumFinEquiv (_root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv security index) =
      (finCongr (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.2.2.2.2) index := by
    simp only [_root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [he]
  apply Fin.ext
  dsimp only [_root_.CurrentAFT.CurrentPublicIndexProgram.decode]
  split_ifs with h
  · rfl
  · have hh : ¬index.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := by simpa only [← _root_.AFT.BinaryArithmetic.lessCounter_value] using h
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1] at hh
    simp only [_root_.AFT.BinaryArithmetic.subtractCounter_value, (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1, finSumFinEquiv, Equiv.coe_fn_mk,
      Sum.elim_inr, Fin.natAdd_mk, Fin.val_mk, finCongr_apply, Fin.val_cast]
    change _root_.CurrentAFT.Parameters.legCount security + (index.val - _root_.CurrentAFT.Parameters.legCount security) = index.val
    omega
open _root_.P2Mba49f952 renaming h179 → _p2mH179
end CurrentAFT.CurrentPublicIndexProgram
open _root_.P2Mba49f952 renaming h179 → _p2mH179
end
open _root_.P2Mba49f952 renaming h179 → _p2mH179
namespace AFT.BinaryArithmetic.binaryGroupTape
end AFT.BinaryArithmetic.binaryGroupTape
namespace AFT.BinaryArithmetic.binaryGroupTapeWork
end AFT.BinaryArithmetic.binaryGroupTapeWork
namespace AFT.BinaryArithmetic.binaryPermutationFromTape
end AFT.BinaryArithmetic.binaryPermutationFromTape
namespace AFT.BinaryArithmetic.binaryPermutationFromTapePolynomial
end AFT.BinaryArithmetic.binaryPermutationFromTapePolynomial
namespace AFT.BinaryArithmetic.binaryPermutationFromTapeWork
end AFT.BinaryArithmetic.binaryPermutationFromTapeWork
namespace AFT.BinaryArithmetic.binaryTapeCell
end AFT.BinaryArithmetic.binaryTapeCell
namespace AFT.BinaryArithmetic.binaryTapeCellWork
end AFT.BinaryArithmetic.binaryTapeCellWork
namespace AFT.FiniteConditionProgram
end AFT.FiniteConditionProgram
namespace AFT.FiniteConditionProgram.groupBits
end AFT.FiniteConditionProgram.groupBits
section
namespace CurrentAFT.CurrentPermutationDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h174 (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) (index : Fin count) :
    (_root_.CurrentAFT.CurrentPermutationDraw.draw count bits tape).value.forward.get index = _root_.AFT.PermutationProgram.draw count bits tape.get index :=
  _root_.AFT.BinaryArithmetic.binaryPermutationFromTape_value count bits tape index
open _root_.P2Mba49f952 renaming h174 → _p2mH174
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h173 (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) :
    (_root_.CurrentAFT.CurrentPermutationDraw.draw count bits tape).value.toEquiv = _root_.AFT.PermutationProgram.draw count bits tape.get := by
  apply Equiv.ext
  exact _p2mH174 count bits tape
open _root_.P2Mba49f952 renaming h173 → _p2mH173
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h175 (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) (index : Fin count) :
    (_root_.CurrentAFT.CurrentPermutationDraw.draw count bits tape).value.inverse.get index = (_root_.AFT.PermutationProgram.draw count bits tape.get).symm index := by
  change (_root_.CurrentAFT.CurrentPermutationDraw.draw count bits tape).value.toEquiv.symm index = _
  rw [_p2mH173]
open _root_.P2Mba49f952 renaming h175 → _p2mH175
noncomputable section
open scoped Classical
end
end CurrentAFT.CurrentPermutationDraw
open _root_.P2Mba49f952 renaming h173 → _p2mH173
open _root_.P2Mba49f952 renaming h174 → _p2mH174
open _root_.P2Mba49f952 renaming h175 → _p2mH175
end
open _root_.P2Mba49f952 renaming h173 → _p2mH173
open _root_.P2Mba49f952 renaming h174 → _p2mH174
open _root_.P2Mba49f952 renaming h175 → _p2mH175
namespace CurrentAFT.ActualPublicLegCharge.publicShift
end CurrentAFT.ActualPublicLegCharge.publicShift
namespace CurrentAFT.ActualPublicLegCharge.signedOffset
end CurrentAFT.ActualPublicLegCharge.signedOffset
namespace CurrentAFT.CurrentPublicShiftProgram
end CurrentAFT.CurrentPublicShiftProgram
namespace CurrentAFT.CurrentPublicShiftProgram.current
end CurrentAFT.CurrentPublicShiftProgram.current
namespace CurrentAFT.CurrentPublicShiftProgram.direction
end CurrentAFT.CurrentPublicShiftProgram.direction
namespace CurrentAFT.CurrentPublicShiftProgram.encode
end CurrentAFT.CurrentPublicShiftProgram.encode
namespace CurrentAFT.CurrentPublicShiftProgram.encode.match_1
end CurrentAFT.CurrentPublicShiftProgram.encode.match_1
namespace CurrentAFT.CurrentPublicShiftProgram.program
end CurrentAFT.CurrentPublicShiftProgram.program
namespace CurrentAFT.CurrentPublicShiftProgram.programWork
end CurrentAFT.CurrentPublicShiftProgram.programWork
namespace CurrentAFT.InwardAnchor
end CurrentAFT.InwardAnchor
namespace CurrentAFT.InwardAnchor.offset
end CurrentAFT.InwardAnchor.offset
section
namespace CurrentAFT.CurrentFlagCompletionProgram
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentFlagJointDraw
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h161 (cutoff first second : ℕ) [NeZero first] [NeZero second] (h : first = second)
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin second) (precisionBits drawBits : ℕ)
    (word : _root_.CurrentAFT.CurrentFlagJointDraw.Tape second drawBits) :
    _root_.CurrentAFT.CurrentFlagCompletionProgram.castChart h (_root_.CurrentAFT.CurrentFlagChartDraw.draw cutoff first baselineSign baseline (mark.cast h.symm)
      precisionBits drawBits (cast (congrArg (fun modulus => _root_.CurrentAFT.CurrentFlagJointDraw.Tape modulus drawBits) h.symm) word)) =
      _root_.CurrentAFT.CurrentFlagChartDraw.draw cutoff second baselineSign baseline mark precisionBits drawBits word := by
  subst second
  rfl
open _root_.P2Mba49f952 renaming h161 → _p2mH161
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentFlagCompletionProgram.completionProgramPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagCompletionProgram.completionProgramNeZero
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h162 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) (precisionBits drawBits : ℕ)
    (word : _root_.CurrentAFT.CurrentFlagJointDraw.Tape (_root_.CurrentAFT.Parameters.modulus security) drawBits) :
    (_root_.CurrentAFT.CurrentFlagCompletionProgram.draw security primary seed precisionBits drawBits word).value =
      (_root_.CurrentAFT.CurrentFlagChartDraw.draw (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security)
        (_root_.CurrentAFT.CurrentPublicShiftProgram.current security primary seed).value.negative
        (_root_.CurrentAFT.CurrentPublicShiftProgram.current security primary seed).value.digits primary precisionBits drawBits word).value := by
  let modulus := _root_.CurrentAFT.PublicParameterProgram.modulus security
  let base := _root_.AFT.BinaryArithmetic.addCounter security 2
  let width := _root_.AFT.BinaryArithmetic.powerCounter base.count 2
  let cutoff := _root_.AFT.BinaryArithmetic.differenceCounter width.count 1
  let shift := _root_.CurrentAFT.CurrentPublicShiftProgram.current security primary seed
  have hm : modulus.count = _root_.CurrentAFT.Parameters.modulus security := _root_.CurrentAFT.PublicParameterProgram.modulus_value security
  have hc : cutoff.count = _root_.CurrentAFT.Parameters.sourceCutoff security - 1 := by
    simp only [cutoff, width, base, _root_.AFT.BinaryArithmetic.differenceCounter_value, _root_.AFT.BinaryArithmetic.powerCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value,
      _root_.CurrentAFT.Parameters.sourceCutoff, _root_.CurrentAFT.Parameters.base]
  change (_root_.CurrentAFT.CurrentFlagCompletionProgram.castChart hm (_root_.CurrentAFT.CurrentFlagChartDraw.draw cutoff.count modulus.count shift.value.negative shift.value.digits
    (primary.cast hm.symm) precisionBits drawBits
      (cast (congrArg (fun modulus => _root_.CurrentAFT.CurrentFlagJointDraw.Tape modulus drawBits) hm.symm) word))).value = _
  rw [_p2mH161, hc]
open _root_.P2Mba49f952 renaming h162 → _p2mH162
end
open _root_.P2Mba49f952 renaming h162 → _p2mH162
end CurrentAFT.CurrentFlagCompletionProgram
open _root_.P2Mba49f952 renaming h161 → _p2mH161
open _root_.P2Mba49f952 renaming h162 → _p2mH162
end
open _root_.P2Mba49f952 renaming h161 → _p2mH161
open _root_.P2Mba49f952 renaming h162 → _p2mH162
namespace CurrentAFT.LobsterIncidence
end CurrentAFT.LobsterIncidence
namespace CurrentAFT.LobsterIncidence.bodyResidual
end CurrentAFT.LobsterIncidence.bodyResidual
namespace CurrentAFT.LobsterIncidence.firstEdge
end CurrentAFT.LobsterIncidence.firstEdge
namespace CurrentAFT.LobsterIncidence.load
end CurrentAFT.LobsterIncidence.load
namespace CurrentAFT.LobsterIncidence.load.match_1
end CurrentAFT.LobsterIncidence.load.match_1
namespace CurrentAFT.LobsterIncidence.secondEdge
end CurrentAFT.LobsterIncidence.secondEdge
namespace CurrentAFT.Parameters
end CurrentAFT.Parameters
namespace CurrentAFT.Parameters.base
end CurrentAFT.Parameters.base
namespace CurrentAFT.Parameters.bodySize
end CurrentAFT.Parameters.bodySize
namespace CurrentAFT.Parameters.calibrationOrder
end CurrentAFT.Parameters.calibrationOrder
namespace CurrentAFT.Parameters.dimension
end CurrentAFT.Parameters.dimension
namespace CurrentAFT.Parameters.leastPrimeWitness
end CurrentAFT.Parameters.leastPrimeWitness
namespace CurrentAFT.Parameters.legCount
end CurrentAFT.Parameters.legCount
namespace CurrentAFT.Parameters.primeThreshold
end CurrentAFT.Parameters.primeThreshold
namespace CurrentAFT.Parameters.scale
end CurrentAFT.Parameters.scale
namespace CurrentAFT.PublicCharge
end CurrentAFT.PublicCharge
namespace CurrentAFT.PublicCharge.attachmentIncrement
end CurrentAFT.PublicCharge.attachmentIncrement
section
namespace CurrentAFT.LobsterCoordinates
open AFT PublicCharge LobsterIncidence
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h189 (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) (index : Fin (bodyEdges + (legs + legs) + 1)) :
    (_root_.CurrentAFT.LobsterCoordinates.relabeledBasis bodyEdges legs placement attachment relabeling input).val index =
      _root_.CurrentAFT.LobsterIncidence.load placement attachment (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input)
        ((_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).symm (relabeling.symm index)) := rfl
open _root_.P2Mba49f952 renaming h189 → _p2mH189
end
open _root_.P2Mba49f952 renaming h189 → _p2mH189
end CurrentAFT.LobsterCoordinates
open _root_.P2Mba49f952 renaming h189 → _p2mH189
end
open _root_.P2Mba49f952 renaming h189 → _p2mH189
namespace CurrentAFT.LegMixer
end CurrentAFT.LegMixer
namespace CurrentAFT.LegMixer.blockCoordinateMixer
end CurrentAFT.LegMixer.blockCoordinateMixer
namespace CurrentAFT.LegMixer.coordinateMixer
end CurrentAFT.LegMixer.coordinateMixer
namespace CurrentAFT.LegMixer.inverseMixer
end CurrentAFT.LegMixer.inverseMixer
namespace CurrentAFT.LegMixer.legIncidence
end CurrentAFT.LegMixer.legIncidence
namespace CurrentAFT.LobsterCoordinates
end CurrentAFT.LobsterCoordinates
section
namespace CurrentAFT.LobsterMixerMatrix
open AFT LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Scalar : Type*} [CommRing Scalar]
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h191 (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : Fin (bodyEdges + (legs + legs)) → Scalar)
    (index : Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) :
    (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs index) =
      (_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix bodyEdges legs scale shear).mulVec (input ∘ _root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs) index := by
  simp only [_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs)]
  simp only [Equiv.symm_apply_apply, Function.comp_apply]
open _root_.P2Mba49f952 renaming h191 → _p2mH191
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h190 (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) → Scalar) :
    (_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix bodyEdges legs scale shear).mulVec input =
      Sum.elim (fun vertex => input (.inl vertex))
        (Sum.elim (fun leg => scale leg * input (.inr (.inl leg)) + shear leg * input (.inr (.inr leg)))
          (fun leg => input (.inr (.inr leg)))) := by
  ext index
  rcases index with vertex | (leg | leg) <;>
    simp [_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.diagonal_apply]
open _root_.P2Mba49f952 renaming h190 → _p2mH190
end
open _root_.P2Mba49f952 renaming h190 → _p2mH190
open _root_.P2Mba49f952 renaming h191 → _p2mH191
end CurrentAFT.LobsterMixerMatrix
open _root_.P2Mba49f952 renaming h190 → _p2mH190
open _root_.P2Mba49f952 renaming h191 → _p2mH191
end
open _root_.P2Mba49f952 renaming h190 → _p2mH190
open _root_.P2Mba49f952 renaming h191 → _p2mH191
namespace CurrentAFT.AffineBaseline
end CurrentAFT.AffineBaseline
namespace CurrentAFT.AffineBaseline.baseline
end CurrentAFT.AffineBaseline.baseline
namespace CurrentAFT.AffineBaseline.baseline.match_1
end CurrentAFT.AffineBaseline.baseline.match_1
namespace CurrentAFT.AffineBaseline.closure
end CurrentAFT.AffineBaseline.closure
namespace CurrentAFT.AffineBaseline.offset
end CurrentAFT.AffineBaseline.offset
section
namespace CurrentAFT.AffineRealization
open AFT LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h48 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    _root_.AFT.pathLoad _ (_root_.CurrentAFT.AffineRealization.extensionCorrection bodyEdges legs modulus queues relabeling) =
      _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling - _root_.AFT.injectionColumn _ modulus :=
  (Classical.choose_spec (_root_.AFT.exists_extension_correction _
    (_root_.AFT.injectionColumn _ modulus) (_root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling)
    ((_root_.CurrentAFT.AffineRealization.queueColumn_charge bodyEdges legs modulus queues relabeling).trans
      (_root_.AFT.totalCharge_injectionColumn _ modulus (_root_.CurrentAFT.AffineRealization.queue_modulus_le bodyEdges legs modulus queues)).symm))).1
open _root_.P2Mba49f952 renaming h48 → _p2mH48
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h49 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    _root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ modulus)
      (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input) =
      (_root_.CurrentAFT.LobsterCoordinates.relabeledBasis bodyEdges legs placement attachment relabeling
        ((_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
          input.2 • _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling :=
  _p2mH41 _ _ _ _ _ _
    (_p2mH48 bodyEdges legs modulus queues relabeling) input
open _root_.P2Mba49f952 renaming h49 → _p2mH49
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h51 (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : _root_.CurrentAFT.PublicCharge.PublicChargeTest modulus centers shift) :
    _root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ modulus)
      (_root_.CurrentAFT.AffineRealization.offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge) =
        _root_.CurrentAFT.AffineBaseline.numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling :=
  (Classical.choose_spec (_root_.CurrentAFT.AffineBaseline.offset_integral_preimage bodyEdges legs modulus (NeZero.ne modulus)
    (_root_.AFT.injectionColumn _ modulus) (_root_.AFT.totalCharge_injectionColumn _ modulus (_root_.CurrentAFT.AffineRealization.queue_modulus_le bodyEdges legs modulus queues))
    centers shift intercept placement closureScalar relabeling hcharge)).1
open _root_.P2Mba49f952 renaming h51 → _p2mH51
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h46 (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (closureScalar : ℤ) (hcharge : _root_.CurrentAFT.PublicCharge.PublicChargeTest modulus centers shift)
    (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    _root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ modulus)
      (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input +
        _root_.CurrentAFT.AffineRealization.offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge) =
      (_root_.CurrentAFT.LobsterCoordinates.relabeledBasis bodyEdges legs placement attachment relabeling
        ((_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
        input.2 • _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling +
        _root_.CurrentAFT.AffineBaseline.numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling := by
  have hadd (n : ℕ) (column : Fin (n + 1) → ℤ) (first second : (Fin n → ℤ) × ℤ) :
      _root_.AFT.roundingLoad n column (first + second) = _root_.AFT.roundingLoad n column first + _root_.AFT.roundingLoad n column second := by
    simp only [_root_.AFT.roundingLoad, Prod.fst_add, Prod.snd_add, _root_.AFT.pathLoad_add, add_smul]
    abel
  rw [hadd, _p2mH49, _p2mH51]
open _root_.P2Mba49f952 renaming h46 → _p2mH46
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h47 (count : ℕ) (basis : (Fin count → ℤ) ≃ₗ[ℤ] _root_.AFT.zeroSumLattice count)
    (input : Fin count → ℤ) :
    (_root_.AFT.edgeBasisChangeMatrix count basis).mulVec input = _root_.AFT.edgeBasisChange count basis input := by
  have hrepr (v : Fin count → ℤ) : ⇑((Pi.basisFun ℤ (Fin count)).repr v) = v := by
    funext i
    exact Pi.basisFun_repr ℤ (Fin count) v i
  simpa only [_root_.AFT.edgeBasisChangeMatrix, hrepr, LinearEquiv.coe_coe] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℤ (Fin count)) (Pi.basisFun ℤ (Fin count))
      (_root_.AFT.edgeBasisChange count basis).toLinearMap input
open _root_.P2Mba49f952 renaming h47 → _p2mH47
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h50 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    (_root_.CurrentAFT.AffineRealization.matrix bodyEdges legs modulus queues placement attachment relabeling scale shear).mulVec
      (Sum.elim input.1 (fun _ : Unit => input.2)) =
      Sum.elim (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).1
        (fun _ : Unit => (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).2) := by
  rw [_root_.CurrentAFT.AffineRealization.matrix, _root_.AFT.transportBlockMatrix, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add, ← Matrix.mulVec_mulVec, _p2mH47,
    _root_.CurrentAFT.AffineRealization.linearPart, _root_.AFT.blockTransport, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply]
  congr 1
  ext index
  simp [Matrix.mulVec, dotProduct, mul_comm]
open _root_.P2Mba49f952 renaming h50 → _p2mH50
end
open _root_.P2Mba49f952 renaming h46 → _p2mH46
open _root_.P2Mba49f952 renaming h47 → _p2mH47
open _root_.P2Mba49f952 renaming h48 → _p2mH48
open _root_.P2Mba49f952 renaming h49 → _p2mH49
open _root_.P2Mba49f952 renaming h50 → _p2mH50
open _root_.P2Mba49f952 renaming h51 → _p2mH51
end CurrentAFT.AffineRealization
open _root_.P2Mba49f952 renaming h46 → _p2mH46
open _root_.P2Mba49f952 renaming h47 → _p2mH47
open _root_.P2Mba49f952 renaming h48 → _p2mH48
open _root_.P2Mba49f952 renaming h49 → _p2mH49
open _root_.P2Mba49f952 renaming h50 → _p2mH50
open _root_.P2Mba49f952 renaming h51 → _p2mH51
end
open _root_.P2Mba49f952 renaming h46 → _p2mH46
open _root_.P2Mba49f952 renaming h47 → _p2mH47
open _root_.P2Mba49f952 renaming h48 → _p2mH48
open _root_.P2Mba49f952 renaming h49 → _p2mH49
open _root_.P2Mba49f952 renaming h50 → _p2mH50
open _root_.P2Mba49f952 renaming h51 → _p2mH51
namespace AFT.edgeBasisChangeMatrix
end AFT.edgeBasisChangeMatrix
namespace CurrentAFT.ActualPublicCharge
end CurrentAFT.ActualPublicCharge
namespace CurrentAFT.ActualPublicCharge.Core
end CurrentAFT.ActualPublicCharge.Core
namespace CurrentAFT.ActualPublicCharge.Core.mk
end CurrentAFT.ActualPublicCharge.Core.mk
namespace CurrentAFT.ActualPublicCharge.centerAt
end CurrentAFT.ActualPublicCharge.centerAt
namespace CurrentAFT.ActualPublicCharge.centerAt.match_1
end CurrentAFT.ActualPublicCharge.centerAt.match_1
namespace CurrentAFT.ActualPublicCharge.queueSet
end CurrentAFT.ActualPublicCharge.queueSet
namespace CurrentAFT.AffineRealization
end CurrentAFT.AffineRealization
namespace CurrentAFT.AffineRealization.linearPart
end CurrentAFT.AffineRealization.linearPart
namespace CurrentAFT.AffineRealization.matrix
end CurrentAFT.AffineRealization.matrix
namespace CurrentAFT.AffineRealization.queueColumn
end CurrentAFT.AffineRealization.queueColumn
namespace CurrentAFT.CyclePathClosure
end CurrentAFT.CyclePathClosure
namespace CurrentAFT.PublicEndpointPlacement
end CurrentAFT.PublicEndpointPlacement
namespace CurrentAFT.PublicEndpointPlacement.toAssembly
end CurrentAFT.PublicEndpointPlacement.toAssembly
namespace CurrentAFT.PublicEndpointPlacement.toAssembly.match_1
end CurrentAFT.PublicEndpointPlacement.toAssembly.match_1
namespace CurrentAFT.PublicEndpointPlacement.toPhysical
end CurrentAFT.PublicEndpointPlacement.toPhysical
namespace CurrentAFT.PublicEndpointPlacement.toPhysical.match_3
end CurrentAFT.PublicEndpointPlacement.toPhysical.match_3
section
namespace CurrentAFT.CurrentAffineGeometry
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  LobsterCoordinates AffineRealization PublicEndpointPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h91 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    _root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex)) =
      core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex) := by
  simp [_root_.CurrentAFT.CurrentAffineGeometry.relabeling]
open _root_.P2Mba49f952 renaming h91 → _p2mH91
end
open _root_.P2Mba49f952 renaming h91 → _p2mH91
end CurrentAFT.CurrentAffineGeometry
open _root_.P2Mba49f952 renaming h91 → _p2mH91
end
open _root_.P2Mba49f952 renaming h91 → _p2mH91
namespace AFT.FiniteConditionProgram.checks
end AFT.FiniteConditionProgram.checks
namespace AFT.FiniteConditionProgram.firstAccepted
end AFT.FiniteConditionProgram.firstAccepted
namespace AFT.FiniteConditionProgram.firstAccepted.match_1
end AFT.FiniteConditionProgram.firstAccepted.match_1
namespace CurrentAFT.CurrentFlagCompletionProgram
end CurrentAFT.CurrentFlagCompletionProgram
namespace CurrentAFT.CurrentPublicAffineSample
end CurrentAFT.CurrentPublicAffineSample
section
namespace CurrentAFT.CurrentChartsDraw
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentAffineData ActualPublicCharge CurrentFlagJointDraw
open scoped BigOperators
set_option maxHeartbeats 500000
attribute [local irreducible] Parameters.legCount CurrentFlagCompletionProgram.draw
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h144 (security : ℕ) (inputs : _root_.CurrentAFT.CurrentChartsDraw.InputVector security) (precisionBits drawBits : ℕ)
    (word : _root_.CurrentAFT.CurrentChartsDraw.Tapes security drawBits) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    (_root_.CurrentAFT.CurrentChartsDraw.draw security inputs precisionBits drawBits word).value leg =
      (_root_.CurrentAFT.CurrentFlagCompletionProgram.draw security (inputs.get leg).1 (inputs.get leg).2
        precisionBits drawBits (word leg)).value := by
  simp only [_root_.CurrentAFT.CurrentChartsDraw.draw, _root_.CurrentAFT.CurrentChartsDraw.drawStored, Vector.get_cast, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.BinaryArithmetic.readVector_value, Fin.cast_cast, Fin.cast_eq_self]
open _root_.P2Mba49f952 renaming h144 → _p2mH144
attribute [local irreducible] draw
noncomputable section
open scoped Classical
end
end CurrentAFT.CurrentChartsDraw
open _root_.P2Mba49f952 renaming h144 → _p2mH144
end
open _root_.P2Mba49f952 renaming h144 → _p2mH144
namespace CurrentAFT.BinaryDistinctTuples
end CurrentAFT.BinaryDistinctTuples
namespace CurrentAFT.BinaryDistinctTuples.current
end CurrentAFT.BinaryDistinctTuples.current
namespace CurrentAFT.BinaryDistinctTuples.guarded
end CurrentAFT.BinaryDistinctTuples.guarded
namespace CurrentAFT.BinaryDistinctTuples.normalizer
end CurrentAFT.BinaryDistinctTuples.normalizer
namespace CurrentAFT.BinaryDistinctTuples.pairCheck
end CurrentAFT.BinaryDistinctTuples.pairCheck
namespace CurrentAFT.BinaryDistinctTuples.sum
end CurrentAFT.BinaryDistinctTuples.sum
section
namespace CurrentAFT.BinaryTwoPoolAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h73 (primaryPool bodyPool r s : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (kernel : Vector (Fin primaryPool) r → Vector (Fin bodyPool) s → _root_.AFT.BinaryArithmetic.RationalResult) :
    (_root_.CurrentAFT.BinaryTwoPoolAverage.current primaryPool bodyPool r s hp hb kernel).data.decode =
      (∑ primary : Fin r ↪ Fin primaryPool, ∑ body : Fin s ↪ Fin bodyPool,
        (kernel (Vector.ofFn primary) (Vector.ofFn body)).data.decode)/
        ((primaryPool.descFactorial r:ℚ)*(bodyPool.descFactorial s:ℚ)) := by
  simp only [_root_.CurrentAFT.BinaryTwoPoolAverage.current, _root_.AFT.BinaryArithmetic.RationalBits.quotient_value, _root_.AFT.BinaryArithmetic.RationalBits.multiply_value, _p2mH61,
    _p2mH63]
open _root_.P2Mba49f952 renaming h73 → CurrentAFT.BinaryTwoPoolAverage.current_value
open _root_.P2Mba49f952 renaming h73 → _p2mH73
end
open _root_.P2Mba49f952 renaming h73 → CurrentAFT.BinaryTwoPoolAverage.current_value
open _root_.P2Mba49f952 renaming h73 → _p2mH73
end CurrentAFT.BinaryTwoPoolAverage
open _root_.P2Mba49f952 renaming h73 → CurrentAFT.BinaryTwoPoolAverage.current_value
open _root_.P2Mba49f952 renaming h73 → _p2mH73
end
open _root_.P2Mba49f952 renaming h73 → CurrentAFT.BinaryTwoPoolAverage.current_value
open _root_.P2Mba49f952 renaming h73 → _p2mH73
namespace CurrentAFT.BinaryTwoPoolAverage
end CurrentAFT.BinaryTwoPoolAverage
namespace CurrentAFT.BinaryTwoPoolAverage.current
end CurrentAFT.BinaryTwoPoolAverage.current
namespace CurrentAFT.BinaryTwoPoolAverage.normalizerWork
end CurrentAFT.BinaryTwoPoolAverage.normalizerWork
namespace CurrentAFT.BinaryWeightLocal
end CurrentAFT.BinaryWeightLocal
namespace CurrentAFT.BinaryWeightLocal.current
end CurrentAFT.BinaryWeightLocal.current
namespace CurrentAFT.BinaryWeightLocal.gather
end CurrentAFT.BinaryWeightLocal.gather
namespace CurrentAFT.BinaryWeightLocal.gatherWork
end CurrentAFT.BinaryWeightLocal.gatherWork
section
namespace CurrentAFT.BinaryWeightBlock
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryWeightLocal.current BinaryTwoPoolAverage.current BinaryReferenceTables.current
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h75 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors security) order) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (groups : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security) × Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) primaryPool)
    (centers : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) bodyPool)
    (first : Vector (Fin primaryPool) arity.val.1.val) (second : Vector (Fin bodyPool) arity.val.2.val) :
    (_root_.CurrentAFT.BinaryWeightBlock.selected security bits order primaryPool bodyPool hp hb (_root_.CurrentAFT.BinaryReferenceTables.current security bits) table arity groups centers first second).data.decode =
      _root_.CurrentAFT.RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => _root_.CurrentAFT.BinaryWeightLocal.rawTable security order table arity primary (fun index => (centers.get (second.get index)).val))
        (fun index => ((groups.get (first.get index)).1.val, (groups.get (first.get index)).2.val)) := by
  unfold _root_.CurrentAFT.BinaryWeightBlock.selected
  rw [_p2mH78]
  simp only [_p2mH79]
open _root_.P2Mba49f952 renaming h75 → _p2mH75
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h74 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors security) order) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (groups : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security) × Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) primaryPool)
    (centers : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) bodyPool) :
    (_root_.CurrentAFT.BinaryWeightBlock.current security bits order primaryPool bodyPool hp hb (_root_.CurrentAFT.BinaryReferenceTables.current security bits) table arity groups centers).data.decode =
      _root_.CurrentAFT.RationalWeightProgram.average arity.val.1.val arity.val.2.val primaryPool bodyPool
        (fun selected selectedCenters => _root_.CurrentAFT.RationalWeightProgram.pairedTensor security bits arity.val.1.val
          (fun primary => _root_.CurrentAFT.BinaryWeightLocal.rawTable security order table arity primary selectedCenters) selected)
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) (fun index => (centers.get index).val) := by
  rw [_root_.CurrentAFT.BinaryWeightBlock.current, _p2mH73]
  simp_rw [_p2mH75]
  simp only [Vector.get_ofFn]
  unfold _root_.CurrentAFT.RationalWeightProgram.average
  apply congrArg (fun numerator : ℚ => numerator /
    ((primaryPool.descFactorial arity.val.1.val:ℚ)*(bodyPool.descFactorial arity.val.2.val:ℚ)))
  letI := _root_.CurrentAFT.CyclePatternProgram.selectionFintype primaryPool arity.val.1.val
  letI := _root_.CurrentAFT.CyclePatternProgram.selectionFintype bodyPool arity.val.2.val
  have hprod : (∑ pair : (Fin arity.val.1.val ↪ Fin primaryPool) × (Fin arity.val.2.val ↪ Fin bodyPool),
      _root_.CurrentAFT.RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => _root_.CurrentAFT.BinaryWeightLocal.rawTable security order table arity primary (fun index => (centers.get (pair.2 index)).val))
        (fun index => ((groups.get (pair.1 index)).1.val, (groups.get (pair.1 index)).2.val))) =
      ∑ first : Fin arity.val.1.val ↪ Fin primaryPool, ∑ second : Fin arity.val.2.val ↪ Fin bodyPool,
        _root_.CurrentAFT.RationalWeightProgram.pairedTensor security bits arity.val.1.val
          (fun primary => _root_.CurrentAFT.BinaryWeightLocal.rawTable security order table arity primary (fun index => (centers.get (second index)).val))
          (fun index => ((groups.get (first index)).1.val, (groups.get (first index)).2.val)) := by
    rw [Fintype.sum_prod_type]
  apply Eq.trans ?_ hprod.symm
  apply Finset.sum_congr (by ext; simp)
  intro first _
  apply Finset.sum_congr (by ext; simp)
  intro second _
  rfl
open _root_.P2Mba49f952 renaming h74 → CurrentAFT.BinaryWeightBlock.current_value
open _root_.P2Mba49f952 renaming h74 → _p2mH74
end
open _root_.P2Mba49f952 renaming h74 → CurrentAFT.BinaryWeightBlock.current_value
open _root_.P2Mba49f952 renaming h74 → _p2mH74
open _root_.P2Mba49f952 renaming h75 → _p2mH75
end CurrentAFT.BinaryWeightBlock
open _root_.P2Mba49f952 renaming h74 → CurrentAFT.BinaryWeightBlock.current_value
open _root_.P2Mba49f952 renaming h74 → _p2mH74
open _root_.P2Mba49f952 renaming h75 → _p2mH75
end
open _root_.P2Mba49f952 renaming h74 → CurrentAFT.BinaryWeightBlock.current_value
open _root_.P2Mba49f952 renaming h74 → _p2mH74
open _root_.P2Mba49f952 renaming h75 → _p2mH75
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.LocalTensors.atomLinear
end AFT.LocalTensors.atomLinear
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace CurrentAFT.ActualWeightedFourier
end CurrentAFT.ActualWeightedFourier
namespace CurrentAFT.ActualWeightedFourier.signedOutputMass
end CurrentAFT.ActualWeightedFourier.signedOutputMass
namespace CurrentAFT.CoefficientOutputFock
end CurrentAFT.CoefficientOutputFock
namespace CurrentAFT.CoefficientOutputFock.familyMass
end CurrentAFT.CoefficientOutputFock.familyMass
namespace CurrentAFT.ControlProduct
end CurrentAFT.ControlProduct
namespace CurrentAFT.ControlProduct.homogeneousProduct
end CurrentAFT.ControlProduct.homogeneousProduct
namespace CurrentAFT.CycleRootExpansion
end CurrentAFT.CycleRootExpansion
namespace CurrentAFT.CycleRootExpansion.componentResponse
end CurrentAFT.CycleRootExpansion.componentResponse
namespace CurrentAFT.CycleRootExpansion.expectationLinear
end CurrentAFT.CycleRootExpansion.expectationLinear
namespace CurrentAFT.CycleRootExpansion.rootLaw
end CurrentAFT.CycleRootExpansion.rootLaw
namespace CurrentAFT.GradedControlAlgebra
end CurrentAFT.GradedControlAlgebra
namespace CurrentAFT.GradedControlAlgebra.coefficientsToFamily
end CurrentAFT.GradedControlAlgebra.coefficientsToFamily
namespace CurrentAFT.GradedControlAlgebra.familyProduct
end CurrentAFT.GradedControlAlgebra.familyProduct
namespace CurrentAFT.GradedControlAlgebra.positiveArity
end CurrentAFT.GradedControlAlgebra.positiveArity
namespace CurrentAFT.GradedControlAlgebra.scalarAt
end CurrentAFT.GradedControlAlgebra.scalarAt
namespace CurrentAFT.GradedControlAlgebra.scalarKernel
end CurrentAFT.GradedControlAlgebra.scalarKernel
namespace CurrentAFT.GradedControlAlgebra.transportKernel
end CurrentAFT.GradedControlAlgebra.transportKernel
namespace CurrentAFT.GradedControlAlgebra.zeroArity
end CurrentAFT.GradedControlAlgebra.zeroArity
section
namespace CurrentAFT.PhysicalPolynomialAverages
open AFT AFT.RepresentedPolynomial HistogramNormalization GradedControlAlgebra
  ControlCoordinates CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h192 (order : ℕ) : Function.Bijective (_root_.CurrentAFT.PhysicalPolynomialAverages.arityOptionMap order) := by
  constructor
  · intro left right hequal
    cases left with
    | none =>
      cases right with
      | none => rfl
      | some arity =>
        have h := congrArg (fun a : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => a.val.1.val + a.val.2.val) hequal
        have hp := arity.property.1
        change 0 + 0 = arity.val.1.val + arity.val.2.val at h
        omega
    | some arity =>
      cases right with
      | none =>
        have h := congrArg (fun a : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => a.val.1.val + a.val.2.val) hequal
        have hp := arity.property.1
        change arity.val.1.val + arity.val.2.val = 0 + 0 at h
        omega
      | some other =>
        apply congrArg some
        apply Subtype.ext
        exact congrArg (fun a : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => a.val) hequal
  · intro arity
    by_cases hzero : arity.val.1.val + arity.val.2.val = 0
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · change 0 = arity.val.1.val
        omega
      · change 0 = arity.val.2.val
        omega
    · exact ⟨some ⟨arity.val, ⟨by omega, arity.property⟩⟩, rfl⟩
open _root_.P2Mba49f952 renaming h192 → _p2mH192
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h193 {Value : Type*} [AddCommMonoid Value] (order : ℕ)
    (test : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order → Value) :
    (∑ arity, test arity) = test (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) +
      ∑ arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order, test (_root_.CurrentAFT.GradedControlAlgebra.positiveArity order arity) := by
  rw [← (Equiv.ofBijective (_root_.CurrentAFT.PhysicalPolynomialAverages.arityOptionMap order) (_p2mH192 order)).sum_comp]
  exact Fintype.sum_option _
open _root_.P2Mba49f952 renaming h193 → _p2mH193
end
open _root_.P2Mba49f952 renaming h192 → _p2mH192
open _root_.P2Mba49f952 renaming h193 → _p2mH193
end CurrentAFT.PhysicalPolynomialAverages
open _root_.P2Mba49f952 renaming h192 → _p2mH192
open _root_.P2Mba49f952 renaming h193 → _p2mH193
end
open _root_.P2Mba49f952 renaming h192 → _p2mH192
open _root_.P2Mba49f952 renaming h193 → _p2mH193
namespace CurrentAFT.BinaryWeightBlock
end CurrentAFT.BinaryWeightBlock
namespace CurrentAFT.BinaryWeightBlock.current
end CurrentAFT.BinaryWeightBlock.current
namespace CurrentAFT.BinaryWeightBlock.selected
end CurrentAFT.BinaryWeightBlock.selected
namespace CurrentAFT.PhysicalPolynomialAverages
end CurrentAFT.PhysicalPolynomialAverages
namespace CurrentAFT.PhysicalPolynomialAverages.arityOptionMap
end CurrentAFT.PhysicalPolynomialAverages.arityOptionMap
section
namespace CurrentAFT.BinaryWeightProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra ControlCoordinates
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter lessCounter PublicParameterProgram.modulus BinaryWeightBlock.current BinaryReferenceTables.current BinaryWeightBlock.height BinaryWeightBlock.work
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h84 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors security) order)
    (groups : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security) × Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) primaryPool)
    (centers : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) bodyPool) (r s : Fin (order+1)) :
    (_root_.CurrentAFT.BinaryWeightProgram.term security bits order primaryPool bodyPool hp hb (_root_.CurrentAFT.BinaryReferenceTables.current security bits) table groups centers r s).data.decode =
      if h : r.val+s.val ≤ order then _root_.CurrentAFT.BinaryWeightProgram.idealBlock security bits order primaryPool bodyPool table groups centers ⟨(r, s), h⟩ else 0 := by
  have ha : (_root_.AFT.BinaryArithmetic.lessCounter (_root_.AFT.BinaryArithmetic.addCounter r.val s.val).count (order+1)).value = true ↔ r.val+s.val ≤ order := by
    rw [_root_.AFT.BinaryArithmetic.lessCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
    omega
  unfold _root_.CurrentAFT.BinaryWeightProgram.term
  try dsimp only
  by_cases hd : r.val+s.val ≤ order
  · simp only [dif_pos (ha.mpr hd), dif_pos hd]
    exact _p2mH74 security bits order primaryPool bodyPool hp hb table ⟨(r, s), hd⟩ groups centers
  · simp only [dif_neg (fun h => hd (ha.mp h)), dif_neg hd, _root_.AFT.BinaryArithmetic.RationalBits.zero_value]
open _root_.P2Mba49f952 renaming h84 → CurrentAFT.BinaryWeightProgram.term_value
open _root_.P2Mba49f952 renaming h84 → _p2mH84
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h83 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors security) order)
    (groups : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security) × Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) primaryPool)
    (centers : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) bodyPool) :
    (_root_.CurrentAFT.BinaryWeightProgram.current security bits order primaryPool bodyPool hp hb table groups centers).data.decode =
      ∑ arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, _root_.CurrentAFT.BinaryWeightProgram.idealBlock security bits order primaryPool bodyPool table groups centers arity := by
  rw [_root_.CurrentAFT.BinaryWeightProgram.current, _root_.AFT.BinaryArithmetic.RationalBits.sumFin_value]
  simp_rw [_root_.AFT.BinaryArithmetic.RationalBits.sumFin_value, _p2mH84]
  have hsum := Finset.sum_subtype (p := fun pair : Fin (order+1) × Fin (order+1) => pair.1.val+pair.2.val ≤ order)
    (F := inferInstance) (Finset.univ.filter (fun pair => pair.1.val+pair.2.val ≤ order)) (by simp)
    (fun pair => if h : pair.1.val+pair.2.val ≤ order then
      _root_.CurrentAFT.BinaryWeightProgram.idealBlock security bits order primaryPool bodyPool table groups centers ⟨pair, h⟩ else 0)
  rw [Finset.sum_filter] at hsum
  have hh : (∑ pair : Fin (order+1) × Fin (order+1),
      if h : pair.1.val+pair.2.val ≤ order then _root_.CurrentAFT.BinaryWeightProgram.idealBlock security bits order primaryPool bodyPool table groups centers ⟨pair, h⟩ else 0) =
      ∑ arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order, _root_.CurrentAFT.BinaryWeightProgram.idealBlock security bits order primaryPool bodyPool table groups centers arity := by
    convert hsum using 1
    · apply Finset.sum_congr rfl
      intro pair _
      by_cases hd : pair.1.val+pair.2.val ≤ order <;> simp [hd]
    · apply Finset.sum_congr rfl
      intro arity _
      rw [dif_pos arity.property]
  exact (Fintype.sum_prod_type _).symm.trans hh
open _root_.P2Mba49f952 renaming h83 → _p2mH83
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h426 (primaryPool bodyPool : ℕ) (kernel : (Fin 0 → ℕ × ℕ) → (Fin 0 → ℕ) → ℚ)
    (groups : Fin primaryPool → ℕ × ℕ) (centers : Fin bodyPool → ℕ) :
    _root_.CurrentAFT.RationalWeightProgram.average 0 0 primaryPool bodyPool kernel groups centers = kernel Fin.elim0 Fin.elim0 := by
  letI := _root_.CurrentAFT.CyclePatternProgram.selectionFintype primaryPool 0
  letI := _root_.CurrentAFT.CyclePatternProgram.selectionFintype bodyPool 0
  let first : Fin 0 ↪ Fin primaryPool := ⟨Fin.elim0, fun index => Fin.elim0 index⟩
  let second : Fin 0 ↪ Fin bodyPool := ⟨Fin.elim0, fun index => Fin.elim0 index⟩
  unfold _root_.CurrentAFT.RationalWeightProgram.average
  simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, div_one]
  rw [Fintype.sum_subsingleton _ (first, second)]
  exact congrArg₂ kernel (Subsingleton.elim _ _) (Subsingleton.elim _ _)
open _root_.P2Mba49f952 renaming h426 → _p2mH426
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h82 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors security) order)
    (groups : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security) × Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) primaryPool)
    (centers : Vector (Fin (_root_.CurrentAFT.BinaryWeightLocal.colors security)) bodyPool) :
    (_root_.CurrentAFT.BinaryWeightProgram.current security bits order primaryPool bodyPool hp hb table groups centers).data.decode =
      _root_.CurrentAFT.RationalWeightProgram.current security bits order primaryPool bodyPool (_root_.CurrentAFT.BinaryWeightLocal.rawTable security order table)
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) (fun index => (centers.get index).val) := by
  rw [_p2mH83, _p2mH193]
  unfold _root_.CurrentAFT.RationalWeightProgram.current
  apply congrArg₂ (·+·)
  · unfold _root_.CurrentAFT.BinaryWeightProgram.idealBlock
    simp only [_root_.CurrentAFT.GradedControlAlgebra.zeroArity, Fin.val_zero]
    rw [_p2mH426, _root_.CurrentAFT.RationalWeightProgram.pairedTensor]
  · rfl
open _root_.P2Mba49f952 renaming h82 → CurrentAFT.BinaryWeightProgram.current_value
open _root_.P2Mba49f952 renaming h82 → _p2mH82
end
open _root_.P2Mba49f952 renaming h82 → CurrentAFT.BinaryWeightProgram.current_value
open _root_.P2Mba49f952 renaming h82 → _p2mH82
open _root_.P2Mba49f952 renaming h83 → _p2mH83
open _root_.P2Mba49f952 renaming h84 → CurrentAFT.BinaryWeightProgram.term_value
open _root_.P2Mba49f952 renaming h84 → _p2mH84
open _root_.P2Mba49f952 renaming h426 → _p2mH426
end CurrentAFT.BinaryWeightProgram
open _root_.P2Mba49f952 renaming h82 → CurrentAFT.BinaryWeightProgram.current_value
open _root_.P2Mba49f952 renaming h82 → _p2mH82
open _root_.P2Mba49f952 renaming h83 → _p2mH83
open _root_.P2Mba49f952 renaming h84 → CurrentAFT.BinaryWeightProgram.term_value
open _root_.P2Mba49f952 renaming h84 → _p2mH84
open _root_.P2Mba49f952 renaming h426 → _p2mH426
end
open _root_.P2Mba49f952 renaming h82 → CurrentAFT.BinaryWeightProgram.current_value
open _root_.P2Mba49f952 renaming h82 → _p2mH82
open _root_.P2Mba49f952 renaming h83 → _p2mH83
open _root_.P2Mba49f952 renaming h84 → CurrentAFT.BinaryWeightProgram.term_value
open _root_.P2Mba49f952 renaming h84 → _p2mH84
namespace CurrentAFT.CurrentCoreProposal
end CurrentAFT.CurrentCoreProposal
namespace CurrentAFT.CurrentCoreProposal.materializedLaw
end CurrentAFT.CurrentCoreProposal.materializedLaw
namespace CurrentAFT.CurrentLayoutDraw
end CurrentAFT.CurrentLayoutDraw
namespace CurrentAFT.CurrentLayoutDraw.Cache
end CurrentAFT.CurrentLayoutDraw.Cache
namespace CurrentAFT.CurrentLayoutDraw.workPolynomial
end CurrentAFT.CurrentLayoutDraw.workPolynomial
section
namespace CurrentAFT.CurrentEmissionRootOrder
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentProposalDimensions CurrentProposalResources CurrentCoreProposal
open ActualCycleMeanMGF ConditionalHistogramMean ActualBlockFock
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount
  CurrentCoreProposal.draw addCounter subtractCounter lessCounter
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h151 (count front : ℕ) (hprefix : front ≤ count) (index : Fin count) :
    (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate count front hprefix index).value.val = if index.val < front then count - front + index.val else index.val - front := by
  by_cases hi : index.val < front
  · have hs : (_root_.AFT.BinaryArithmetic.lessCounter index.val front).value = true := (_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mpr hi
    simp only [_root_.CurrentAFT.CurrentEmissionRootOrder.rotate, dif_pos hs, Fin.val_mk, _root_.AFT.BinaryArithmetic.addCounter_value, _root_.AFT.BinaryArithmetic.subtractCounter_value, if_pos hi]
  · have hs : ¬(_root_.AFT.BinaryArithmetic.lessCounter index.val front).value = true := by simpa only [_root_.AFT.BinaryArithmetic.lessCounter_value] using hi
    simp only [_root_.CurrentAFT.CurrentEmissionRootOrder.rotate, dif_neg hs, Fin.val_mk, _root_.AFT.BinaryArithmetic.subtractCounter_value, if_neg hi]
open _root_.P2Mba49f952 renaming h151 → _p2mH151
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h150 (security : ℕ) (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).body) :
    _root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security
      (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate (_root_.CurrentAFT.CurrentProposalDimensions.current security).body (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs (_root_.CurrentAFT.CurrentEmissionRootOrder.legs_le_body security) index).value =
    _root_.CurrentAFT.CurrentLayoutDraw.canonicalLayout security (_root_.CurrentAFT.CurrentEmissionRootOrder.rootToRole security ((_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security).symm index)) := by
  obtain ⟨leg | (center | queue), rfl⟩ := (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security).surjective index
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals apply Fin.ext
  · have hi : leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := by simpa only [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1] using leg.isLt
    have hcount := _root_.CurrentAFT.CurrentEmissionRootOrder.root_count security
    change (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate _ _ _ (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inl leg))).value.val = _
    rw [_p2mH151]
    have hv : (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inl leg)).val = leg.val := rfl
    rw [hv, if_pos hi]
    change (_root_.CurrentAFT.CurrentProposalDimensions.current security).body - (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs + leg.val =
      _root_.CurrentAFT.BackgroundPopulationBounds.freeCount security + (_root_.CurrentAFT.Parameters.modulus security + leg.val)
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
    unfold _root_.CurrentAFT.BackgroundPopulationBounds.freeCount _root_.CurrentAFT.ActualBlockFock.centerCount at *
    omega
  · change (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate _ _ _ (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inr (.inl center)))).value.val = _
    rw [_p2mH151]
    have hv : (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inr (.inl center))).val = _root_.CurrentAFT.Parameters.legCount security + center.val := rfl
    rw [hv]
    have hn : ¬_root_.CurrentAFT.Parameters.legCount security + center.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := by
      rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]; omega
    rw [if_neg hn]
    change _root_.CurrentAFT.Parameters.legCount security + center.val - (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs = center.val
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
    omega
  · change (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate _ _ _ (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inr (.inr queue)))).value.val = _
    rw [_p2mH151]
    have hv : (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inr (.inr queue))).val = _root_.CurrentAFT.Parameters.legCount security + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val) := rfl
    rw [hv]
    have hn : ¬_root_.CurrentAFT.Parameters.legCount security + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val) < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := by
      rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]; omega
    rw [if_neg hn]
    change _root_.CurrentAFT.Parameters.legCount security + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val) - (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs =
      _root_.CurrentAFT.BackgroundPopulationBounds.freeCount security + queue.val
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
    unfold _root_.CurrentAFT.BackgroundPopulationBounds.freeCount _root_.CurrentAFT.ActualBlockFock.centerCount
    omega
open _root_.P2Mba49f952 renaming h150 → _p2mH150
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h149 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).body) :
    (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout data).value.get index =
      data.body.inverse.get (layout.forward.get (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate (_root_.CurrentAFT.CurrentProposalDimensions.current security).body (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs (_root_.CurrentAFT.CurrentEmissionRootOrder.legs_le_body security) index).value) := by
  simp only [_root_.CurrentAFT.CurrentEmissionRootOrder.positions, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h149 → CurrentAFT.CurrentEmissionRootOrder.positions_value
open _root_.P2Mba49f952 renaming h149 → _p2mH149
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h429 {State Target : Type*} (equiv : State ≃ Target) (permutation : Equiv.Perm State) (state : State) :
    (equiv.permCongr permutation).symm (equiv state) = equiv (permutation.symm state) := by
  apply (equiv.permCongr permutation).injective
  simp only [Equiv.apply_symm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
open _root_.P2Mba49f952 renaming h429 → _p2mH429
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h148 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).body) :
    _root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security ((_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout data).value.get index) =
      data.core.bodyPermutation.symm (layout.layout (_root_.CurrentAFT.CurrentEmissionRootOrder.rootToRole security ((_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security).symm index))) := by
  rw [_p2mH149]
  change _root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security
      (data.body.toEquiv.symm (layout.toEquiv (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate _ _ _ index).value)) =
    ((_root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security).permCongr data.body.toEquiv).symm
      (((_root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security).permCongr layout.toEquiv)
        (_root_.CurrentAFT.CurrentLayoutDraw.canonicalLayout security (_root_.CurrentAFT.CurrentEmissionRootOrder.rootToRole security ((_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security).symm index))))
  rw [← _p2mH150 security index, Equiv.permCongr_apply, Equiv.symm_apply_apply, _p2mH429]
open _root_.P2Mba49f952 renaming h148 → _p2mH148
end CurrentAFT.CurrentEmissionRootOrder
open _root_.P2Mba49f952 renaming h148 → _p2mH148
open _root_.P2Mba49f952 renaming h149 → CurrentAFT.CurrentEmissionRootOrder.positions_value
open _root_.P2Mba49f952 renaming h149 → _p2mH149
open _root_.P2Mba49f952 renaming h150 → _p2mH150
open _root_.P2Mba49f952 renaming h151 → _p2mH151
open _root_.P2Mba49f952 renaming h429 → _p2mH429
end
open _root_.P2Mba49f952 renaming h148 → _p2mH148
open _root_.P2Mba49f952 renaming h149 → CurrentAFT.CurrentEmissionRootOrder.positions_value
open _root_.P2Mba49f952 renaming h149 → _p2mH149
open _root_.P2Mba49f952 renaming h150 → _p2mH150
open _root_.P2Mba49f952 renaming h151 → _p2mH151
namespace AFT.BinaryArithmetic.binaryPhysicalInitialLoad
end AFT.BinaryArithmetic.binaryPhysicalInitialLoad
namespace AFT.BinaryArithmetic.binaryPhysicalQueueLoad
end AFT.BinaryArithmetic.binaryPhysicalQueueLoad
namespace AFT.BinaryArithmetic.binaryPhysicalVertex
end AFT.BinaryArithmetic.binaryPhysicalVertex
namespace AFT.BinaryArithmetic.binaryRootRead
end AFT.BinaryArithmetic.binaryRootRead
namespace AFT.BinaryArithmetic.initialBlockEntry
end AFT.BinaryArithmetic.initialBlockEntry
namespace AFT.BinaryArithmetic.initialBlockEntry.match_1
end AFT.BinaryArithmetic.initialBlockEntry.match_1
namespace AFT.BinaryArithmetic.initialBlockEntry_length
end AFT.BinaryArithmetic.initialBlockEntry_length
namespace AFT.BinaryArithmetic.initialBlockEntry_work
end AFT.BinaryArithmetic.initialBlockEntry_work
namespace AFT.BinaryArithmetic.queueBlockEntry
end AFT.BinaryArithmetic.queueBlockEntry
namespace AFT.BinaryArithmetic.queueBlockEntry_length
end AFT.BinaryArithmetic.queueBlockEntry_length
namespace AFT.BinaryArithmetic.queueBlockEntry_work
end AFT.BinaryArithmetic.queueBlockEntry_work
namespace AFT.blockVertexNumbering
end AFT.blockVertexNumbering
namespace AFT.blockVertexSplit.match_1
end AFT.blockVertexSplit.match_1
namespace AFT.blockVertexSplit.match_3
end AFT.blockVertexSplit.match_3
namespace CurrentAFT.CurrentEmissionRootOrder
end CurrentAFT.CurrentEmissionRootOrder
namespace CurrentAFT.CurrentEmissionRootOrder.positions
end CurrentAFT.CurrentEmissionRootOrder.positions
namespace CurrentAFT.CurrentEmissionRootOrder.rootToRole
end CurrentAFT.CurrentEmissionRootOrder.rootToRole
namespace CurrentAFT.CurrentEmissionRootOrder.rotate
end CurrentAFT.CurrentEmissionRootOrder.rotate
namespace CurrentAFT.CurrentPhysicalNumbering
end CurrentAFT.CurrentPhysicalNumbering
namespace CurrentAFT.CurrentPhysicalNumbering.blocks
end CurrentAFT.CurrentPhysicalNumbering.blocks
namespace CurrentAFT.CurrentPhysicalNumbering.blocks.match_1
end CurrentAFT.CurrentPhysicalNumbering.blocks.match_1
namespace CurrentAFT.CurrentPhysicalNumbering.blocks.match_3
end CurrentAFT.CurrentPhysicalNumbering.blocks.match_3
namespace CurrentAFT.CurrentPhysicalNumbering.split
end CurrentAFT.CurrentPhysicalNumbering.split
namespace CurrentAFT.CurrentPhysicalNumbering.split.match_1
end CurrentAFT.CurrentPhysicalNumbering.split.match_1
section
namespace CurrentAFT.CurrentEmissionMetadata
open AFT AFT.BinaryArithmetic CurrentProposalDimensions CurrentProposalResources
open ActualBlockFock
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount Parameters.dimension
  subtractCounter
attribute [local irreducible] CurrentEmissionMetadata.current
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h147 (security : ℕ)
    (point : Sigma (_root_.AFT.blockSlotsProgram (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest)) :
    _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security (_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1 point) =
      _root_.CurrentAFT.CurrentPhysicalNumbering.numbering security (_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv security point) := by
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    apply Fin.ext
    change _ = (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security ⟨.inl (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg), slot⟩).val
    rw [_p2mH177]
    change slot.val + 3 * leg.val = slot.val + 3 * leg.val
    rfl
  · change Fin 1 at slot
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    · apply Fin.ext
      change _ = (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security
        (match finSumFinEquiv.symm (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body) with
          | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
          | .inr queue => ⟨.inr (.inr queue), (0 : Fin 1)⟩)).val
      rw [← he, Equiv.symm_apply_apply, _p2mH176]
      have hv := congrArg Fin.val he
      change center.val = body.val at hv
      change (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs * 3 + (0 + 1 * body.val) = _root_.CurrentAFT.Parameters.legCount security * 3 + center.val
      rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
      omega
    · apply Fin.ext
      change _ = (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security
        (match finSumFinEquiv.symm (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body) with
          | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
          | .inr queue => ⟨.inr (.inr queue), (0 : Fin 1)⟩)).val
      rw [← he, Equiv.symm_apply_apply, _p2mH178]
      have hv := congrArg Fin.val he
      change _root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val = body.val at hv
      change (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs * 3 + (0 + 1 * body.val) =
        _root_.CurrentAFT.Parameters.legCount security * 3 + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val)
      rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
      omega
open _root_.P2Mba49f952 renaming h147 → _p2mH147
end CurrentAFT.CurrentEmissionMetadata
open _root_.P2Mba49f952 renaming h147 → _p2mH147
end
open _root_.P2Mba49f952 renaming h147 → _p2mH147
section
namespace CurrentAFT.CurrentBinaryIncidence
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h428 (condition : Prop) [Decidable condition] (first second : _root_.AFT.BinaryArithmetic.IntegerBits) :
    (if condition then first else second).decode = if condition then first.decode else second.decode := by
  split_ifs <;> rfl
open _root_.P2Mba49f952 renaming h428 → _p2mH428
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h118 (bodyEdges column root : ℕ) :
    (_root_.CurrentAFT.CurrentBinaryIncidence.pathEntry bodyEdges column root).value.decode = if column < bodyEdges then
      (if root = column then 1 else 0) - (if root = column + 1 then 1 else 0) else 0 := by
  have hi : (_root_.AFT.BinaryArithmetic.lessCounter column bodyEdges).value = true ↔ column < bodyEdges := _root_.AFT.BinaryArithmetic.lessCounter_value _ _
  have hp : (_root_.AFT.BinaryArithmetic.equalCounter root column).value = true ↔ root = column := _root_.AFT.BinaryArithmetic.equalCounter_value _ _
  have hn : (_root_.AFT.BinaryArithmetic.equalCounter root (_root_.AFT.BinaryArithmetic.addCounter column 1).count).value = true ↔ root = column + 1 := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
  simp only [_root_.CurrentAFT.CurrentBinaryIncidence.pathEntry, _p2mH428, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.AFT.BinaryArithmetic.IntegerBits.one_value, _root_.AFT.BinaryArithmetic.IntegerBits.zero_value, hi, hp, hn]
open _root_.P2Mba49f952 renaming h118 → _p2mH118
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h117 {legs : ℕ} (bodyEdges column : ℕ) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits legs) (leg : Fin legs) :
    let first := (if column = bodyEdges + leg.val then (scale.get leg).decode else 0) +
      (if column = bodyEdges + leg.val + legs then (shear.get leg).decode else 0)
    let second := if column = bodyEdges + leg.val + legs then (1 : ℤ) else 0
    ((_root_.CurrentAFT.CurrentBinaryIncidence.legEntries bodyEdges column scale shear leg).value.1.decode,
      ((_root_.CurrentAFT.CurrentBinaryIncidence.legEntries bodyEdges column scale shear leg).value.2.1.decode,
        (_root_.CurrentAFT.CurrentBinaryIncidence.legEntries bodyEdges column scale shear leg).value.2.2.decode)) = (first, (-first - second, second)) := by
  have hf : (_root_.AFT.BinaryArithmetic.equalCounter column (_root_.AFT.BinaryArithmetic.addCounter bodyEdges leg.val).count).value = true ↔ column = bodyEdges + leg.val := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
  have hs : (_root_.AFT.BinaryArithmetic.equalCounter column (_root_.AFT.BinaryArithmetic.addCounter (_root_.AFT.BinaryArithmetic.addCounter bodyEdges leg.val).count legs).count).value = true ↔
      column = bodyEdges + leg.val + legs := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
  simp only [_root_.CurrentAFT.CurrentBinaryIncidence.legEntries, _p2mH428, _root_.AFT.BinaryArithmetic.IntegerBits.add_value, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.AFT.BinaryArithmetic.IntegerBits.negate_value, _root_.AFT.BinaryArithmetic.readVector_value, hf, hs, _root_.AFT.BinaryArithmetic.IntegerBits.zero_value, _root_.AFT.BinaryArithmetic.IntegerBits.one_value]
open _root_.P2Mba49f952 renaming h117 → _p2mH117
end CurrentAFT.CurrentBinaryIncidence
open _root_.P2Mba49f952 renaming h117 → _p2mH117
open _root_.P2Mba49f952 renaming h118 → _p2mH118
open _root_.P2Mba49f952 renaming h428 → _p2mH428
end
open _root_.P2Mba49f952 renaming h117 → _p2mH117
open _root_.P2Mba49f952 renaming h118 → _p2mH118
namespace CurrentAFT.CurrentBinaryIncidence
end CurrentAFT.CurrentBinaryIncidence
namespace CurrentAFT.CurrentBinaryIncidence.legEntries
end CurrentAFT.CurrentBinaryIncidence.legEntries
namespace CurrentAFT.CurrentBinaryIncidence.pathEntry
end CurrentAFT.CurrentBinaryIncidence.pathEntry
namespace CurrentAFT.CurrentBinaryIncidence.pathEntryWork
end CurrentAFT.CurrentBinaryIncidence.pathEntryWork
section
namespace CurrentAFT.CurrentPathImpulse
open AFT
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h172 (count column : ℕ) (vertex : Fin (count + 1)) :
    _root_.AFT.pathLoad count (fun edge => if edge.val = column then (1 : ℤ) else 0) vertex =
      if column < count then (if vertex.val = column then 1 else 0) -
        (if vertex.val = column + 1 then 1 else 0) else 0 := by
  induction count generalizing column with
  | zero => simp only [_root_.AFT.pathLoad, Pi.zero_apply, Nat.not_lt_zero, if_false]
  | succ count ih =>
    cases column with
    | zero =>
      refine Fin.cases ?_ (fun rest => ?_) vertex
      · simp [_root_.AFT.pathLoad]
      · have ht : Fin.tail (fun edge : Fin (count + 1) => if edge.val = 0 then (1 : ℤ) else 0) = 0 := by
          funext edge
          simp [Fin.tail]
        rw [_root_.AFT.pathLoad, Fin.cons_succ, ht, _root_.AFT.pathLoad_zero]
        have he : rest.val + 1 = 1 ↔ rest = 0 := by
          constructor
          · intro h; apply Fin.ext; change rest.val = 0; omega
          · rintro rfl; rfl
        change (0 - if rest = 0 then (1 : ℤ) else 0) =
          if 0 < count + 1 then (if rest.val + 1 = 0 then 1 else 0) -
            (if rest.val + 1 = 1 then 1 else 0) else 0
        simp only [Nat.zero_lt_succ, if_true, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, he]
    | succ column =>
      refine Fin.cases ?_ (fun rest => ?_) vertex
      · simp [_root_.AFT.pathLoad]
      · have ht : Fin.tail (fun edge : Fin (count + 1) => if edge.val = column + 1 then (1 : ℤ) else 0) =
            (fun edge : Fin count => if edge.val = column then 1 else 0) := by
          funext edge
          simp [Fin.tail]
        rw [_root_.AFT.pathLoad, Fin.cons_succ, ht, ih]
        have hf : ((0 : Fin (count + 1)).val = column + 1) = False := by simp
        have hp : rest.succ.val = column + 1 ↔ rest.val = column := by simp
        have hn : rest.succ.val = column + 1 + 1 ↔ rest.val = column + 1 := by simp
        simp only [hf, if_false, ite_self, Nat.add_lt_add_iff_right, hp, hn]
        exact sub_zero _
open _root_.P2Mba49f952 renaming h172 → _p2mH172
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h171 (count column : ℕ) (vertex : Fin (count + 1)) :
    (_root_.CurrentAFT.CurrentBinaryIncidence.pathEntry count column vertex.val).value.decode =
      _root_.AFT.pathLoad count (fun edge => if edge.val = column then (1 : ℤ) else 0) vertex := by
  rw [_p2mH118, _p2mH172]
open _root_.P2Mba49f952 renaming h171 → _p2mH171
end CurrentAFT.CurrentPathImpulse
open _root_.P2Mba49f952 renaming h171 → _p2mH171
open _root_.P2Mba49f952 renaming h172 → _p2mH172
end
open _root_.P2Mba49f952 renaming h171 → _p2mH171
open _root_.P2Mba49f952 renaming h172 → _p2mH172
namespace CurrentAFT.CurrentEmissionMetadata
end CurrentAFT.CurrentEmissionMetadata
namespace CurrentAFT.CurrentEmissionMetadata.Result
end CurrentAFT.CurrentEmissionMetadata.Result
namespace CurrentAFT.CurrentEmissionMetadata.Result.mk
end CurrentAFT.CurrentEmissionMetadata.Result.mk
namespace CurrentAFT.CurrentEmissionMetadata.current
end CurrentAFT.CurrentEmissionMetadata.current
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv
end CurrentAFT.CurrentEmissionMetadata.pointEquiv
namespace CurrentAFT.CurrentPathImpulse
end CurrentAFT.CurrentPathImpulse
section
namespace CurrentAFT.CurrentBinaryLoadColumns
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentEmissionMetadata
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h121 (security : ℕ) (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    (_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots point).value = roots.get
      ((_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1) := by
  simp only [_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead, _root_.AFT.BinaryArithmetic.readVector_value, _p2mH24]
open _root_.P2Mba49f952 renaming h121 → _p2mH121
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h119 (security column : ℕ) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security)
    (point : _root_.CurrentAFT.CurrentBinaryLoadColumns.Point security) :
    (_root_.CurrentAFT.CurrentBinaryLoadColumns.entry security column scale shear roots point).value.decode =
      _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry security column (fun leg => (scale.get leg).decode) (fun leg => (shear.get leg).decode) roots point := by
  rcases point with ⟨leg | body, slot⟩
  · have hv := _p2mH117 (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column scale shear leg
    have hfirst := congrArg Prod.fst hv
    have hcompanion := congrArg (fun value => value.2.1) hv
    have hsecond := congrArg (fun value => value.2.2) hv
    try dsimp only at hfirst hcompanion hsecond
    have hp := _p2mH171 (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column
      ((_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots (.inl leg)).value.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    change Fin 3 at slot
    fin_cases slot <;> simp only [_root_.CurrentAFT.CurrentBinaryLoadColumns.entry, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, Matrix.cons_val_zero', Matrix.cons_val_succ', _root_.AFT.BinaryArithmetic.IntegerBits.add_value,
      hfirst, hcompanion, hsecond, _root_.CurrentAFT.CurrentBinaryLoadColumns.primaryEntry, _root_.CurrentAFT.CurrentBinaryLoadColumns.secondEntry]
    change (_root_.CurrentAFT.CurrentBinaryIncidence.pathEntry (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column (_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots (.inl leg)).value.val).value.decode + _ = _
    rw [hp]
    simp only [_p2mH121, _root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue]
  · have hp := _p2mH171 (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column
      ((_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots (.inr body)).value.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    have hf : (_root_.AFT.BinaryArithmetic.lessCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).value = false ↔ (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers ≤ body.val := by
      rw [Bool.eq_false_iff]
      exact (not_congr (_root_.AFT.BinaryArithmetic.lessCounter_value _ _)).trans not_lt
    have hc : ((! (_root_.AFT.BinaryArithmetic.lessCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).value) &&
        (_root_.AFT.BinaryArithmetic.equalCounter column (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges).value) = true ↔
        (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers ≤ body.val ∧ column = (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', hf, _root_.AFT.BinaryArithmetic.equalCounter_value]
    simp only [_root_.CurrentAFT.CurrentBinaryLoadColumns.entry, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, _root_.AFT.BinaryArithmetic.IntegerBits.add_value]
    rw [hp]
    simp only [_p2mH121, _root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue]
    congr 1
    by_cases h : ((! (_root_.AFT.BinaryArithmetic.lessCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).value) &&
      (_root_.AFT.BinaryArithmetic.equalCounter column (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges).value) = true
    · rw [if_pos h, if_pos (hc.mp h), _root_.AFT.BinaryArithmetic.IntegerBits.one_value]
    · rw [if_neg h, if_neg (fun hh => h (hc.mpr hh)), _root_.AFT.BinaryArithmetic.IntegerBits.zero_value]
open _root_.P2Mba49f952 renaming h119 → _p2mH119
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h120 (security : ℕ) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security)
    (column row : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges + 1)) :
    (((_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix security scale shear roots).value.get column).get row).decode =
      _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry security column.val (fun leg => (scale.get leg).decode) (fun leg => (shear.get leg).decode) roots
        ((_root_.AFT.physicalVertexNumberingProgram (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges
          (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1).symm row) := by
  simp only [_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix, _root_.AFT.BinaryArithmetic.storeData_get, _p2mH119, _p2mH22]
open _root_.P2Mba49f952 renaming h120 → _p2mH120
end CurrentAFT.CurrentBinaryLoadColumns
open _root_.P2Mba49f952 renaming h119 → _p2mH119
open _root_.P2Mba49f952 renaming h120 → _p2mH120
open _root_.P2Mba49f952 renaming h121 → _p2mH121
end
open _root_.P2Mba49f952 renaming h119 → _p2mH119
open _root_.P2Mba49f952 renaming h120 → _p2mH120
open _root_.P2Mba49f952 renaming h121 → _p2mH121
namespace CurrentAFT.CurrentAffineData
end CurrentAFT.CurrentAffineData
namespace CurrentAFT.CurrentAffineData.Data
end CurrentAFT.CurrentAffineData.Data
namespace CurrentAFT.CurrentAffineData.Data.eval
end CurrentAFT.CurrentAffineData.Data.eval
namespace CurrentAFT.CurrentAffineData.Data.mk
end CurrentAFT.CurrentAffineData.Data.mk
namespace CurrentAFT.CurrentAffineData.assemble
end CurrentAFT.CurrentAffineData.assemble
namespace CurrentAFT.CurrentAffineData.assembled
end CurrentAFT.CurrentAffineData.assembled
namespace CurrentAFT.CurrentAffineData.fallback
end CurrentAFT.CurrentAffineData.fallback
namespace CurrentAFT.CurrentAffineData.scales
end CurrentAFT.CurrentAffineData.scales
namespace CurrentAFT.CurrentCoreProposal.MaterializedCore
end CurrentAFT.CurrentCoreProposal.MaterializedCore
namespace CurrentAFT.CurrentCoreProposal.MaterializedCore.core
end CurrentAFT.CurrentCoreProposal.MaterializedCore.core
namespace CurrentAFT.CurrentCoreProposal.MaterializedCore.mk
end CurrentAFT.CurrentCoreProposal.MaterializedCore.mk
namespace CurrentAFT.CurrentCoreProposal.decode
end CurrentAFT.CurrentCoreProposal.decode
namespace CurrentAFT.CurrentCoreProposal.draw
end CurrentAFT.CurrentCoreProposal.draw
namespace CurrentAFT.CurrentCoreProposal.gatherInputs
end CurrentAFT.CurrentCoreProposal.gatherInputs
section
namespace CurrentAFT.CurrentBinaryChartData
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h108 (security : ℕ) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security)
    (field : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security → ZMod (_root_.CurrentAFT.Parameters.modulus security))
    (leg : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs) :
    ((_root_.CurrentAFT.CurrentBinaryChartData.fieldArray security charts field).value.get leg).decode = (field (charts.get (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg))).val := by
  simp only [_root_.CurrentAFT.CurrentBinaryChartData.fieldArray, _root_.AFT.BinaryArithmetic.storeData_get, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h108 → _p2mH108
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h109 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (leg : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs) :
    ((_root_.CurrentAFT.CurrentBinaryChartData.shiftArray security core).value.get leg).decode = _root_.CurrentAFT.ActualPublicCharge.legShift security core.core (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg) := by
  simp only [_root_.CurrentAFT.CurrentBinaryChartData.shiftArray, _root_.AFT.BinaryArithmetic.storeData_get, _p2mH180, _root_.AFT.BinaryArithmetic.readVector_value,
    core.inputs_correct, _root_.CurrentAFT.ActualPublicCharge.legShift, _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode]
open _root_.P2Mba49f952 renaming h109 → _p2mH109
end CurrentAFT.CurrentBinaryChartData
open _root_.P2Mba49f952 renaming h108 → _p2mH108
open _root_.P2Mba49f952 renaming h109 → _p2mH109
end
open _root_.P2Mba49f952 renaming h108 → _p2mH108
open _root_.P2Mba49f952 renaming h109 → _p2mH109
namespace CurrentAFT.CurrentBinaryChartData
end CurrentAFT.CurrentBinaryChartData
namespace CurrentAFT.CurrentBinaryChartData.fieldArray
end CurrentAFT.CurrentBinaryChartData.fieldArray
namespace CurrentAFT.CurrentBinaryChartData.shiftArray
end CurrentAFT.CurrentBinaryChartData.shiftArray
namespace CurrentAFT.CurrentBinaryLoadColumns
end CurrentAFT.CurrentBinaryLoadColumns
namespace CurrentAFT.CurrentBinaryLoadColumns.entry
end CurrentAFT.CurrentBinaryLoadColumns.entry
namespace CurrentAFT.CurrentBinaryLoadColumns.entry.match_1
end CurrentAFT.CurrentBinaryLoadColumns.entry.match_1
namespace CurrentAFT.CurrentBinaryLoadColumns.loadEntry
end CurrentAFT.CurrentBinaryLoadColumns.loadEntry
namespace CurrentAFT.CurrentBinaryLoadColumns.matrix
end CurrentAFT.CurrentBinaryLoadColumns.matrix
namespace CurrentAFT.CurrentBinaryLoadColumns.pathValue
end CurrentAFT.CurrentBinaryLoadColumns.pathValue
namespace CurrentAFT.CurrentBinaryLoadColumns.primaryEntry
end CurrentAFT.CurrentBinaryLoadColumns.primaryEntry
namespace CurrentAFT.CurrentBinaryLoadColumns.rootRead
end CurrentAFT.CurrentBinaryLoadColumns.rootRead
namespace CurrentAFT.CurrentBinaryLoadColumns.secondEntry
end CurrentAFT.CurrentBinaryLoadColumns.secondEntry
section
namespace CurrentAFT.CurrentBinaryBaselines
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentEmissionMetadata
open CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h106 (security : ℕ) (body : Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) (center : Fin (_root_.CurrentAFT.ActualBlockFock.centerCount security))
    (he : finSumFinEquiv (.inl center) = _root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).controls) (hi : index.val = body.val) :
    _root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv security index = (_root_.CurrentAFT.UniformTaggedOutput.centerSplit security).symm center := by
  apply (_root_.CurrentAFT.UniformTaggedOutput.centerSplit security).injective
  apply Fin.ext
  have hv := congrArg Fin.val he
  change center.val = body.val at hv
  have hc : (_root_.CurrentAFT.UniformTaggedOutput.centerSplit security (_root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv security index)).val = index.val := by
    simp only [_root_.CurrentAFT.UniformTaggedOutput.centerSplit, _root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv, Equiv.trans_apply,
      finCongr_apply, Equiv.apply_symm_apply, Fin.val_cast]
  simpa only [Equiv.apply_symm_apply, hc, hi] using hv.symm
open _root_.P2Mba49f952 renaming h106 → _p2mH106
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h107 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    (_root_.CurrentAFT.CurrentBinaryBaselines.read security core point).value.decode = _root_.CurrentAFT.ActualPublicCharge.centerAt security layout core.core (layout (_root_.CurrentAFT.CurrentBinaryBaselines.role security point)) := by
  rcases point with leg | body
  · simp only [_root_.CurrentAFT.CurrentBinaryBaselines.read, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value, _root_.CurrentAFT.CurrentBinaryBaselines.role,
      _root_.CurrentAFT.ActualPublicCharge.centerAt, Equiv.symm_apply_apply, _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode, _root_.CurrentAFT.CurrentEmissionMetadata.legEquiv]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    · have hv := congrArg Fin.val he
      change center.val = body.val at hv
      have hb : body.val < (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers := by
        rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.2.2, ← hv]
        exact center.isLt
      have hs := (_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mpr hb
      simp only [_root_.CurrentAFT.CurrentBinaryBaselines.read, dif_pos hs, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value,
        _root_.CurrentAFT.CurrentBinaryBaselines.role, ← he, Equiv.symm_apply_apply, _root_.CurrentAFT.ActualPublicCharge.centerAt]
      have ha := _p2mH106 security body center he ⟨body.val, by rw [_root_.CurrentAFT.CurrentBinaryBaselines.controls_count]; exact hb⟩ rfl
      simp only [_root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode]
      rw [← ha, Equiv.symm_apply_apply]
    · have hv := congrArg Fin.val he
      change _root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val = body.val at hv
      have hb : ¬body.val < (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers := by
        rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.2.2]; omega
      have hs : ¬(_root_.AFT.BinaryArithmetic.lessCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).value = true := fun hs => hb ((_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mp hs)
      simp only [_root_.CurrentAFT.CurrentBinaryBaselines.read, dif_neg hs, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value,
        _root_.CurrentAFT.CurrentBinaryBaselines.role, ← he, Equiv.symm_apply_apply, _root_.CurrentAFT.ActualPublicCharge.centerAt, _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode]
      have ha : (_root_.AFT.BinaryArithmetic.subtractCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).count =
          ((_root_.CurrentAFT.CurrentProposalDimensions.queueEquiv security).symm queue).val := by
        change (_root_.AFT.BinaryArithmetic.subtractCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).count = queue.val
        rw [_root_.AFT.BinaryArithmetic.subtractCounter_value, (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.2.2]
        omega
      have hi (h : (_root_.AFT.BinaryArithmetic.subtractCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).count < (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors) :
          (⟨(_root_.AFT.BinaryArithmetic.subtractCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).count, h⟩ : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors) =
            (_root_.CurrentAFT.CurrentProposalDimensions.queueEquiv security).symm queue := Fin.ext ha
      rw [hi]
open _root_.P2Mba49f952 renaming h107 → CurrentAFT.CurrentBinaryBaselines.read_value
open _root_.P2Mba49f952 renaming h107 → _p2mH107
end CurrentAFT.CurrentBinaryBaselines
open _root_.P2Mba49f952 renaming h106 → _p2mH106
open _root_.P2Mba49f952 renaming h107 → CurrentAFT.CurrentBinaryBaselines.read_value
open _root_.P2Mba49f952 renaming h107 → _p2mH107
end
open _root_.P2Mba49f952 renaming h106 → _p2mH106
open _root_.P2Mba49f952 renaming h107 → CurrentAFT.CurrentBinaryBaselines.read_value
open _root_.P2Mba49f952 renaming h107 → _p2mH107
namespace CurrentAFT.CurrentBinaryBaselines
end CurrentAFT.CurrentBinaryBaselines
namespace CurrentAFT.CurrentBinaryBaselines.read
end CurrentAFT.CurrentBinaryBaselines.read
namespace CurrentAFT.CurrentBinaryBaselines.read.match_1
end CurrentAFT.CurrentBinaryBaselines.read.match_1
namespace CurrentAFT.CurrentBinaryBaselines.role
end CurrentAFT.CurrentBinaryBaselines.role
namespace CurrentAFT.CurrentEmissionMetadata.legEquiv
end CurrentAFT.CurrentEmissionMetadata.legEquiv
namespace CurrentAFT.UniformTaggedOutput
end CurrentAFT.UniformTaggedOutput
namespace CurrentAFT.UniformTaggedOutput.centerSplit
end CurrentAFT.UniformTaggedOutput.centerSplit
section
namespace CurrentAFT.CurrentBinaryOffsetLoad
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h139 (bodyEdges : ℕ) (root : Fin (bodyEdges + 1)) (scalar : _root_.AFT.BinaryArithmetic.IntegerBits) :
    (_root_.CurrentAFT.CurrentBinaryOffsetLoad.closure bodyEdges root.val scalar).value.decode = _root_.CurrentAFT.AffineBaseline.closure bodyEdges scalar.decode root := by
  have hl : (_root_.AFT.BinaryArithmetic.equalCounter root.val bodyEdges).value = true ↔ root = Fin.last bodyEdges := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, Fin.ext_iff]
    rfl
  have hf : (_root_.AFT.BinaryArithmetic.equalCounter root.val 0).value = true ↔ root = 0 := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, Fin.ext_iff]
    rfl
  unfold _root_.CurrentAFT.CurrentBinaryOffsetLoad.closure _root_.CurrentAFT.AffineBaseline.closure
  try dsimp only
  rw [_root_.AFT.BinaryArithmetic.IntegerBits.subtract_value]
  have he (test : Bool) : (if test then scalar else _root_.AFT.BinaryArithmetic.IntegerBits.zero).decode = if test then scalar.decode else 0 := by
    cases test <;> rfl
  rw [he, he]
  simp only [hl, hf]
open _root_.P2Mba49f952 renaming h139 → _p2mH139
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h140 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (modulus : _root_.AFT.BinaryArithmetic.IntegerBits) (shift intercept : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) (scalar : _root_.AFT.BinaryArithmetic.IntegerBits)
    (point : _root_.CurrentAFT.CurrentBinaryLoadColumns.Point security) :
    (_root_.CurrentAFT.CurrentBinaryOffsetLoad.entry security core modulus shift intercept roots scalar point).value.decode =
      _root_.CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad security core layout modulus.decode (fun leg => (shift.get leg).decode)
        (fun leg => (intercept.get leg).decode) roots scalar.decode point := by
  rcases point with ⟨leg | body, slot⟩
  · have hc := _p2mH139 (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges
      ((_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots (.inl leg)).value.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm) scalar
    simp only [Fin.val_cast, _p2mH121] at hc
    change Fin 3 at slot
    fin_cases slot <;> simp only [_root_.CurrentAFT.CurrentBinaryOffsetLoad.entry, _root_.CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad, Matrix.cons_val_zero', Matrix.cons_val_succ',
      _root_.AFT.BinaryArithmetic.IntegerBits.add_value, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.AFT.BinaryArithmetic.IntegerBits.one_value, _root_.AFT.BinaryArithmetic.readVector_value,
      _p2mH107 security core layout, hc, _p2mH121]
  · have hc := _p2mH139 (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges
      ((_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots (.inr body)).value.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm) scalar
    simp only [Fin.val_cast, _p2mH121] at hc
    simp only [_root_.CurrentAFT.CurrentBinaryOffsetLoad.entry, _root_.CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad, _root_.AFT.BinaryArithmetic.IntegerBits.add_value,
      _p2mH107 security core layout, hc, _p2mH121]
open _root_.P2Mba49f952 renaming h140 → _p2mH140
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h141 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (modulus : _root_.AFT.BinaryArithmetic.IntegerBits) (shift intercept : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) (scalar : _root_.AFT.BinaryArithmetic.IntegerBits)
    (row : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges + 1)) :
    ((_root_.CurrentAFT.CurrentBinaryOffsetLoad.load security core modulus shift intercept roots scalar).value.get row).decode =
      _root_.CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad security core layout modulus.decode (fun leg => (shift.get leg).decode)
        (fun leg => (intercept.get leg).decode) roots scalar.decode
        ((_root_.AFT.physicalVertexNumberingProgram (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges
          (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1).symm row) := by
  simp only [_root_.CurrentAFT.CurrentBinaryOffsetLoad.load, _root_.AFT.BinaryArithmetic.storeData_get, _p2mH140 security core layout, _p2mH22]
open _root_.P2Mba49f952 renaming h141 → _p2mH141
end CurrentAFT.CurrentBinaryOffsetLoad
open _root_.P2Mba49f952 renaming h139 → _p2mH139
open _root_.P2Mba49f952 renaming h140 → _p2mH140
open _root_.P2Mba49f952 renaming h141 → _p2mH141
end
open _root_.P2Mba49f952 renaming h139 → _p2mH139
open _root_.P2Mba49f952 renaming h140 → _p2mH140
open _root_.P2Mba49f952 renaming h141 → _p2mH141
section
namespace CurrentAFT.BinaryCoreCharge
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions ActualPublicCharge
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h56 (security : ℕ) (core : _root_.CurrentAFT.ActualPublicCharge.Core security) :
    (_root_.CurrentAFT.BinaryCoreCharge.numerator security core : ZMod (_root_.CurrentAFT.Parameters.modulus security)) = _root_.CurrentAFT.ActualPublicCharge.chargeValue security core := by
  unfold _root_.CurrentAFT.BinaryCoreCharge.numerator _root_.CurrentAFT.ActualPublicCharge.chargeValue
  simp only [Fintype.sum_sum_type, Int.cast_sum, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Finset.sum_add_distrib]
  push_cast
  ring
open _root_.P2Mba49f952 renaming h56 → _p2mH56
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h53 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).controls) :
    (_root_.CurrentAFT.BinaryCoreCharge.controlTerm security data index).value.decode =
      ((data.core.controls (_root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv security index)).2.val.val : ℤ) := by
  simp only [_root_.CurrentAFT.BinaryCoreCharge.controlTerm, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value,
    _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode, Equiv.symm_apply_apply]
open _root_.P2Mba49f952 renaming h53 → _p2mH53
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h55 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs) :
    (_root_.CurrentAFT.BinaryCoreCharge.legTerm security data index).value.decode =
      ((data.core.legs (_root_.CurrentAFT.CurrentProposalDimensions.legEquiv security index)).2.val : ℤ) + _root_.CurrentAFT.ActualPublicCharge.legShift security data.core (_root_.CurrentAFT.CurrentProposalDimensions.legEquiv security index) := by
  simp only [_root_.CurrentAFT.BinaryCoreCharge.legTerm, _root_.AFT.BinaryArithmetic.IntegerBits.add_value, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value,
    _p2mH180, _root_.AFT.BinaryArithmetic.readVector_value, data.inputs_correct,
    _root_.CurrentAFT.ActualPublicCharge.legShift, _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode, Equiv.symm_apply_apply]
open _root_.P2Mba49f952 renaming h55 → _p2mH55
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h57 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors) :
    (_root_.CurrentAFT.BinaryCoreCharge.queueTerm security data index).value.decode =
      ((data.core.queueBaselines (_root_.CurrentAFT.CurrentProposalDimensions.queueEquiv security index)).val : ℤ) := by
  simp only [_root_.CurrentAFT.BinaryCoreCharge.queueTerm, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value,
    _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode, Equiv.symm_apply_apply]
open _root_.P2Mba49f952 renaming h57 → _p2mH57
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h58 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) :
    (_root_.CurrentAFT.BinaryCoreCharge.total security data).value.decode = _root_.CurrentAFT.BinaryCoreCharge.numerator security data.core := by
  simp only [_root_.CurrentAFT.BinaryCoreCharge.total, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.AFT.BinaryArithmetic.IntegerBits.add_value, _p2mH1,
    _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _p2mH53, _p2mH55, _p2mH57]
  rw [Equiv.sum_comp (_root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv security) (fun index => ((data.core.controls index).2.val.val : ℤ)),
    Equiv.sum_comp (_root_.CurrentAFT.CurrentProposalDimensions.legEquiv security) (fun leg => ((data.core.legs leg).2.val : ℤ) + _root_.CurrentAFT.ActualPublicCharge.legShift security data.core leg),
    Equiv.sum_comp (_root_.CurrentAFT.CurrentProposalDimensions.queueEquiv security) (fun index => ((data.core.queueBaselines index).val : ℤ)),
    (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
  unfold _root_.CurrentAFT.BinaryCoreCharge.numerator
  norm_cast
open _root_.P2Mba49f952 renaming h58 → _p2mH58
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h54 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) :
    (_root_.CurrentAFT.BinaryCoreCharge.current security data).value = true ↔ _root_.CurrentAFT.ActualPublicCharge.publicCharge security data.core := by
  have hq : 0 < _root_.AFT.BinaryArithmetic.value (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits := by
    rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.CurrentAFT.PublicParameterProgram.modulus_value]
    exact (_root_.CurrentAFT.Parameters.modulus_spec security).2.pos
  have hr := _root_.AFT.BinaryArithmetic.IntegerBits.residue_value (_root_.CurrentAFT.BinaryCoreCharge.total security data).value
    (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits hq
  rw [_p2mH58, _root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.CurrentAFT.PublicParameterProgram.modulus_value] at hr
  change (_root_.AFT.BinaryArithmetic.normalize (_root_.AFT.BinaryArithmetic.IntegerBits.residue (_root_.CurrentAFT.BinaryCoreCharge.total security data).value
    (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits).digits).digits.isEmpty = true ↔ _
  rw [List.isEmpty_iff, _root_.AFT.BinaryArithmetic.normalize_nil_iff]
  have he : _root_.AFT.BinaryArithmetic.value (_root_.AFT.BinaryArithmetic.IntegerBits.residue (_root_.CurrentAFT.BinaryCoreCharge.total security data).value
      (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits).digits = 0 ↔
      _root_.CurrentAFT.BinaryCoreCharge.numerator security data.core % (_root_.CurrentAFT.Parameters.modulus security : ℤ) = 0 := by
    rw [_root_.CurrentAFT.PublicParameterProgram.modulus_value]
    omega
  rw [he, ← Int.dvd_iff_emod_eq_zero]
  unfold _root_.CurrentAFT.ActualPublicCharge.publicCharge
  rw [← _p2mH56]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
open _root_.P2Mba49f952 renaming h54 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2Mba49f952 renaming h54 → _p2mH54
end
open _root_.P2Mba49f952 renaming h53 → _p2mH53
open _root_.P2Mba49f952 renaming h54 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2Mba49f952 renaming h54 → _p2mH54
open _root_.P2Mba49f952 renaming h55 → _p2mH55
open _root_.P2Mba49f952 renaming h56 → _p2mH56
open _root_.P2Mba49f952 renaming h57 → _p2mH57
open _root_.P2Mba49f952 renaming h58 → _p2mH58
end CurrentAFT.BinaryCoreCharge
open _root_.P2Mba49f952 renaming h53 → _p2mH53
open _root_.P2Mba49f952 renaming h54 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2Mba49f952 renaming h54 → _p2mH54
open _root_.P2Mba49f952 renaming h55 → _p2mH55
open _root_.P2Mba49f952 renaming h56 → _p2mH56
open _root_.P2Mba49f952 renaming h57 → _p2mH57
open _root_.P2Mba49f952 renaming h58 → _p2mH58
end
open _root_.P2Mba49f952 renaming h53 → _p2mH53
open _root_.P2Mba49f952 renaming h54 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2Mba49f952 renaming h54 → _p2mH54
open _root_.P2Mba49f952 renaming h55 → _p2mH55
open _root_.P2Mba49f952 renaming h56 → _p2mH56
open _root_.P2Mba49f952 renaming h57 → _p2mH57
open _root_.P2Mba49f952 renaming h58 → _p2mH58
namespace AFT.BinaryArithmetic.BinaryAffineData
end AFT.BinaryArithmetic.BinaryAffineData
namespace AFT.BinaryArithmetic.BinaryAffineData.mk
end AFT.BinaryArithmetic.BinaryAffineData.mk
namespace AFT.BinaryArithmetic.BinaryCoordinateResult.decode
end AFT.BinaryArithmetic.BinaryCoordinateResult.decode
namespace AFT.BinaryArithmetic.binaryAffineAssembly
end AFT.BinaryArithmetic.binaryAffineAssembly
namespace AFT.BinaryArithmetic.binaryAffineAssemblyWork
end AFT.BinaryArithmetic.binaryAffineAssemblyWork
namespace CurrentAFT.ActualPublicCharge.legShift
end CurrentAFT.ActualPublicCharge.legShift
namespace CurrentAFT.BinaryCoreCharge
end CurrentAFT.BinaryCoreCharge
namespace CurrentAFT.BinaryCoreCharge.controlTerm
end CurrentAFT.BinaryCoreCharge.controlTerm
namespace CurrentAFT.BinaryCoreCharge.legTerm
end CurrentAFT.BinaryCoreCharge.legTerm
namespace CurrentAFT.BinaryCoreCharge.queueTerm
end CurrentAFT.BinaryCoreCharge.queueTerm
namespace CurrentAFT.BinaryCoreCharge.total
end CurrentAFT.BinaryCoreCharge.total
namespace CurrentAFT.CurrentBinaryOffsetLoad
end CurrentAFT.CurrentBinaryOffsetLoad
namespace CurrentAFT.CurrentBinaryOffsetLoad.entry
end CurrentAFT.CurrentBinaryOffsetLoad.entry
namespace CurrentAFT.CurrentBinaryOffsetLoad.entry.match_1
end CurrentAFT.CurrentBinaryOffsetLoad.entry.match_1
namespace CurrentAFT.CurrentBinaryOffsetLoad.load
end CurrentAFT.CurrentBinaryOffsetLoad.load
namespace CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad
end CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad
section
namespace CurrentAFT.CurrentBinaryAffinePrimitives
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h104 (security : ℕ) (row : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    ((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.injection security).value.get row).decode = _root_.AFT.injectionColumn (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges (_root_.CurrentAFT.Parameters.modulus security) row := by
  have h : (_root_.AFT.BinaryArithmetic.lessCounter row.val (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors).value = true ↔ row.val < _root_.CurrentAFT.Parameters.modulus security := by
    rw [_root_.AFT.BinaryArithmetic.lessCounter_value, (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).1]
  simp only [_root_.CurrentAFT.CurrentBinaryAffinePrimitives.injection, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.injectionColumn]
  by_cases ht : (_root_.AFT.BinaryArithmetic.lessCounter row.val (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors).value = true
  · rw [if_pos ht, if_pos (h.mp ht), _root_.AFT.BinaryArithmetic.IntegerBits.one_value]
  · rw [if_neg ht, if_neg (fun hh => ht (h.mpr hh)), _root_.AFT.BinaryArithmetic.IntegerBits.zero_value]
open _root_.P2Mba49f952 renaming h104 → _p2mH104
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h103 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (row : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security ((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value.get row) =
      core.core.endpointPermutation (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row) := by
  simp only [_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.BinaryArithmetic.readVector_value, _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode,
    Equiv.permCongr_apply]
  apply Fin.ext
  change (core.endpoints.forward.get (row.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.1)).val =
    (core.endpoints.forward.get ((_root_.CurrentAFT.CurrentProposalDimensions.endpointEquiv security).symm (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row))).val
  have hi : row.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.1 =
      (_root_.CurrentAFT.CurrentProposalDimensions.endpointEquiv security).symm (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row) := by
    apply Fin.ext
    rfl
  rw [hi]
open _root_.P2Mba49f952 renaming h103 → _p2mH103
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h105 (security : ℕ) (data : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security))
    (permutation : Vector (Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) (row : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad security data permutation).value.get row = data.get (permutation.get row) := by
  simp only [_root_.CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mba49f952 renaming h105 → _p2mH105
end CurrentAFT.CurrentBinaryAffinePrimitives
open _root_.P2Mba49f952 renaming h103 → _p2mH103
open _root_.P2Mba49f952 renaming h104 → _p2mH104
open _root_.P2Mba49f952 renaming h105 → _p2mH105
end
open _root_.P2Mba49f952 renaming h103 → _p2mH103
open _root_.P2Mba49f952 renaming h104 → _p2mH104
open _root_.P2Mba49f952 renaming h105 → _p2mH105
namespace CurrentAFT.CurrentBinaryAffinePrimitives
end CurrentAFT.CurrentBinaryAffinePrimitives
namespace CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation
end CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation
namespace CurrentAFT.CurrentBinaryAffinePrimitives.injection
end CurrentAFT.CurrentBinaryAffinePrimitives.injection
namespace CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad
end CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad
section
namespace CurrentAFT.CurrentBinaryAffineGuard
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentBinaryChartData
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h102 (security : ℕ) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    (_root_.CurrentAFT.CurrentBinaryAffineGuard.scale security charts leg).value = true ↔ (charts.get leg).2.2.1 ≠ 0 := by
  have he : (_root_.AFT.BinaryArithmetic.equalCounter (charts.get leg).2.2.1.val 0).value = true ↔ (charts.get leg).2.2.1 = 0 := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, ZMod.val_eq_zero]
  simp only [_root_.CurrentAFT.CurrentBinaryAffineGuard.scale, _root_.AFT.BinaryArithmetic.readVector_value, Bool.not_eq_true', Bool.eq_false_iff]
  exact not_congr he
open _root_.P2Mba49f952 renaming h102 → _p2mH102
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h101 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security) :
    (_root_.CurrentAFT.CurrentBinaryAffineGuard.current security core charts).value = true ↔ _root_.CurrentAFT.CurrentAffineData.Valid security core.core charts.get := by
  simp only [_root_.CurrentAFT.CurrentBinaryAffineGuard.current, Bool.and_eq_true, _p2mH54,
    _root_.CurrentAFT.BinaryProposalGuard.allFin_value, _p2mH102, _root_.CurrentAFT.CurrentAffineData.Valid]
open _root_.P2Mba49f952 renaming h101 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2Mba49f952 renaming h101 → _p2mH101
end CurrentAFT.CurrentBinaryAffineGuard
open _root_.P2Mba49f952 renaming h101 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2Mba49f952 renaming h101 → _p2mH101
open _root_.P2Mba49f952 renaming h102 → _p2mH102
end
open _root_.P2Mba49f952 renaming h101 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2Mba49f952 renaming h101 → _p2mH101
open _root_.P2Mba49f952 renaming h102 → _p2mH102
namespace AFT.BinaryArithmetic.binaryPositiveRatio
end AFT.BinaryArithmetic.binaryPositiveRatio
namespace AFT.BinaryArithmetic.binaryRejectionDraw
end AFT.BinaryArithmetic.binaryRejectionDraw
namespace AFT.BinaryArithmetic.binaryRejectionDraw.match_1
end AFT.BinaryArithmetic.binaryRejectionDraw.match_1
namespace AFT.BinaryArithmetic.binaryRejectionStepWork
end AFT.BinaryArithmetic.binaryRejectionStepWork
section
namespace CurrentAFT.BinaryArrayRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State Tape : Type*} [Inhabited Tape]
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h52 (sample : Tape → _root_.AFT.RationalRejectionProgram.CountedValue State) (score : State → _root_.AFT.RationalRejectionProgram.CountedValue _root_.AFT.BinaryArithmetic.RationalBits)
    (envelope : _root_.AFT.BinaryArithmetic.RationalBits) (bits : ℕ) (fallback : _root_.AFT.RationalRejectionProgram.CountedValue State)
    (attempts : ℕ) (words : Vector (Tape × (Fin bits → Fin 2)) attempts) :
    (_root_.CurrentAFT.BinaryArrayRejection.run sample score envelope bits fallback attempts words).value =
      (_root_.AFT.BinaryArithmetic.binaryRejectionDraw sample score envelope bits fallback attempts words.get).value := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [_root_.CurrentAFT.BinaryArrayRejection.run, _root_.AFT.BinaryArithmetic.binaryRejectionDraw, _root_.AFT.BinaryArithmetic.readVector_value]
    split_ifs
    · rfl
    · rw [ih]
      have htail : (_root_.AFT.BinaryArithmetic.storeData attempts (fun index => _root_.AFT.BinaryArithmetic.readVector (default : Tape × (Fin bits → Fin 2)) words index.succ)).value.get =
          Fin.tail words.get := by
        funext index
        exact _root_.AFT.BinaryArithmetic.storeData_get _ _ index |>.trans (_root_.AFT.BinaryArithmetic.readVector_value _ _ _)
      rw [htail]
open _root_.P2Mba49f952 renaming h52 → _p2mH52
end CurrentAFT.BinaryArrayRejection
open _root_.P2Mba49f952 renaming h52 → _p2mH52
end
open _root_.P2Mba49f952 renaming h52 → _p2mH52
namespace CurrentAFT.CurrentAffineGeometry
end CurrentAFT.CurrentAffineGeometry
namespace CurrentAFT.CurrentAffineGeometry.relabeling
end CurrentAFT.CurrentAffineGeometry.relabeling
section
namespace CurrentAFT.CurrentAffineLoad
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h98 (security : ℕ) (input : (Fin (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) → ℤ) × ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security (_root_.CurrentAFT.CurrentAffineLoad.packSource security input) = input := by
  simp [_root_.CurrentAFT.CurrentAffineLoad.splitSource, _root_.CurrentAFT.CurrentAffineLoad.packSource]
open _root_.P2Mba49f952 renaming h98 → _p2mH98
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h96 (security : ℕ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.packSource security (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input) = input := by
  funext index
  obtain ⟨edge | point, rfl⟩ := (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).surjective index
  · simp [_root_.CurrentAFT.CurrentAffineLoad.packSource, _root_.CurrentAFT.CurrentAffineLoad.splitSource]
  · cases point
    simp [_root_.CurrentAFT.CurrentAffineLoad.packSource, _root_.CurrentAFT.CurrentAffineLoad.splitSource]
open _root_.P2Mba49f952 renaming h96 → _p2mH96
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h97 (security : ℕ) (first second : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security (first + second) = _root_.CurrentAFT.CurrentAffineLoad.splitSource security first + _root_.CurrentAFT.CurrentAffineLoad.splitSource security second := rfl
open _root_.P2Mba49f952 renaming h97 → _p2mH97
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h93 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    (_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input =
      _root_.CurrentAFT.CurrentAffineLoad.packSource security
        (_root_.CurrentAFT.AffineRealization.linearPart (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.Parameters.modulus security)
          (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
          (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input)) := by
  change (Matrix.reindex _ _ _).mulVecLin input = _
  rw [Matrix.mulVecLin_reindex]
  change (fun index => (_root_.CurrentAFT.AffineRealization.matrix (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
    (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
      (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear).mulVec (input ∘ _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security)
        ((_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).symm index)) = _
  have hinput : input ∘ _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security =
      Sum.elim (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input).1 (fun _ : Unit => (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input).2) := by
    funext index
    rcases index with edge | point
    · rfl
    · cases point; rfl
  rw [hinput, _p2mH50]
  rfl
open _root_.P2Mba49f952 renaming h93 → _p2mH93
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h94 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      _root_.CurrentAFT.AffineRealization.linearPart (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.Parameters.modulus security)
        (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
        (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input) := by
  rw [_p2mH93, _p2mH98]
open _root_.P2Mba49f952 renaming h94 → _p2mH94
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h95 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (intercept : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security (_root_.CurrentAFT.CurrentAffineGeometry.offset security layout core intercept closureScalar hcharge) =
      _root_.CurrentAFT.AffineRealization.offsetCoordinates (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
        (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.centers security layout core)
        (_root_.CurrentAFT.ActualPublicCharge.legShift security core) intercept (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) closureScalar (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core)
        (_root_.CurrentAFT.CurrentAffineGeometry.centers_charge security layout core hcharge) := by
  exact _p2mH98 security _
open _root_.P2Mba49f952 renaming h95 → _p2mH95
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h92 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear intercept : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input +
      _root_.CurrentAFT.CurrentAffineGeometry.offset security layout core intercept closureScalar hcharge) =
        _root_.CurrentAFT.CurrentAffineLoad.load security layout core scale shear intercept closureScalar input := by
  unfold _root_.CurrentAFT.CurrentAffineLoad.rounding
  rw [_p2mH97, _p2mH94, _p2mH95, _p2mH46]
  rfl
open _root_.P2Mba49f952 renaming h92 → _p2mH92
end
open _root_.P2Mba49f952 renaming h92 → _p2mH92
open _root_.P2Mba49f952 renaming h93 → _p2mH93
open _root_.P2Mba49f952 renaming h94 → _p2mH94
open _root_.P2Mba49f952 renaming h95 → _p2mH95
open _root_.P2Mba49f952 renaming h96 → _p2mH96
open _root_.P2Mba49f952 renaming h97 → _p2mH97
open _root_.P2Mba49f952 renaming h98 → _p2mH98
end CurrentAFT.CurrentAffineLoad
open _root_.P2Mba49f952 renaming h92 → _p2mH92
open _root_.P2Mba49f952 renaming h93 → _p2mH93
open _root_.P2Mba49f952 renaming h94 → _p2mH94
open _root_.P2Mba49f952 renaming h95 → _p2mH95
open _root_.P2Mba49f952 renaming h96 → _p2mH96
open _root_.P2Mba49f952 renaming h97 → _p2mH97
open _root_.P2Mba49f952 renaming h98 → _p2mH98
end
open _root_.P2Mba49f952 renaming h92 → _p2mH92
open _root_.P2Mba49f952 renaming h93 → _p2mH93
open _root_.P2Mba49f952 renaming h94 → _p2mH94
open _root_.P2Mba49f952 renaming h95 → _p2mH95
open _root_.P2Mba49f952 renaming h96 → _p2mH96
open _root_.P2Mba49f952 renaming h97 → _p2mH97
open _root_.P2Mba49f952 renaming h98 → _p2mH98
section
namespace CurrentAFT.LobsterAffineLoad
open AFT PublicCharge LobsterCoordinates LobsterMixerMatrix AffineBaseline AffineRealization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h186 (bodyEdges legs : ℕ) (scale shear : Fin legs → ℤ)
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) :
    _root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs ((_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input) =
      ((_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).1,
        (fun leg => scale leg * (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.1 leg +
          shear leg * (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.2 leg,
         (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.2)) := by
  apply Prod.ext
  · funext vertex
    change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inl vertex)) = _
    rw [_p2mH191, _p2mH190]
    rfl
  · apply Prod.ext
    · funext leg
      change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inr (.inl leg))) = _
      rw [_p2mH191, _p2mH190]
      rfl
    · funext leg
      change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inr (.inr leg))) = _
      rw [_p2mH191, _p2mH190]
      rfl
open _root_.P2Mba49f952 renaming h186 → _p2mH186
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h187 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin (bodyEdges + 1)) :
    _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling (relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex))) =
      if vertex ∈ Finset.univ.map queues then 1 else 0 := by
  have hequal : relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex)) ∈
      Finset.univ.map (_root_.CurrentAFT.AffineRealization.queueEmbedding bodyEdges legs modulus queues relabeling) ↔
      vertex ∈ Finset.univ.map queues := by
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨point, heq⟩
      exact ⟨point, Sum.inl.inj ((_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).injective (relabeling.injective heq))⟩
    · rintro ⟨point, heq⟩
      exact ⟨point, congrArg (fun vertex => relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex))) heq⟩
  simp only [_root_.CurrentAFT.AffineRealization.queueColumn, hequal]
open _root_.P2Mba49f952 renaming h187 → _p2mH187
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h188 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin legs ⊕ Fin legs) :
    _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling (relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inr vertex))) = 0 := by
  have hnot : relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inr vertex)) ∉
      Finset.univ.map (_root_.CurrentAFT.AffineRealization.queueEmbedding bodyEdges legs modulus queues relabeling) := by
    intro hmem
    obtain ⟨point, _, heq⟩ := Finset.mem_map.mp hmem
    have h := (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).injective (relabeling.injective heq)
    cases h
  exact if_neg hnot
open _root_.P2Mba49f952 renaming h188 → _p2mH188
end
open _root_.P2Mba49f952 renaming h186 → _p2mH186
open _root_.P2Mba49f952 renaming h187 → _p2mH187
open _root_.P2Mba49f952 renaming h188 → _p2mH188
end CurrentAFT.LobsterAffineLoad
open _root_.P2Mba49f952 renaming h186 → _p2mH186
open _root_.P2Mba49f952 renaming h187 → _p2mH187
open _root_.P2Mba49f952 renaming h188 → _p2mH188
end
open _root_.P2Mba49f952 renaming h186 → _p2mH186
open _root_.P2Mba49f952 renaming h187 → _p2mH187
open _root_.P2Mba49f952 renaming h188 → _p2mH188
namespace CurrentAFT.CurrentProposalPrecision
end CurrentAFT.CurrentProposalPrecision
namespace CurrentAFT.CurrentProposalPrecision.paddingPolynomial
end CurrentAFT.CurrentProposalPrecision.paddingPolynomial
namespace CurrentAFT.CurrentProposalPrecision.padding_le_pow
end CurrentAFT.CurrentProposalPrecision.padding_le_pow
section
namespace CurrentAFT.BinaryProposalPrecision
open AFT BinaryArithmetic Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
attribute [local irreducible] addCounter powerCounter multiplyCounter
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h68 (security bits : ℕ) :
    (_root_.CurrentAFT.BinaryProposalPrecision.current security bits).count = _root_.CurrentAFT.CurrentProposalPrecision.tableBits security bits := by
  simp only [_root_.CurrentAFT.BinaryProposalPrecision.current, _root_.AFT.BinaryArithmetic.addCounter_value, _root_.AFT.BinaryArithmetic.powerCounter_value, _root_.AFT.BinaryArithmetic.multiplyCounter_value]
open _root_.P2Mba49f952 renaming h68 → CurrentAFT.BinaryProposalPrecision.current_value
open _root_.P2Mba49f952 renaming h68 → _p2mH68
end CurrentAFT.BinaryProposalPrecision
open _root_.P2Mba49f952 renaming h68 → CurrentAFT.BinaryProposalPrecision.current_value
open _root_.P2Mba49f952 renaming h68 → _p2mH68
end
open _root_.P2Mba49f952 renaming h68 → CurrentAFT.BinaryProposalPrecision.current_value
open _root_.P2Mba49f952 renaming h68 → _p2mH68
namespace CurrentAFT.CurrentAffineLoad
end CurrentAFT.CurrentAffineLoad
namespace CurrentAFT.CurrentAffineLoad.packSource
end CurrentAFT.CurrentAffineLoad.packSource
namespace CurrentAFT.CurrentAffineLoad.splitSource
end CurrentAFT.CurrentAffineLoad.splitSource
section
namespace CurrentAFT.CurrentAffineEmissionBridge
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean CurrentAffineGeometry CurrentAffineLoad
  LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h88 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout core scale shear input := by
  unfold _root_.CurrentAFT.CurrentAffineLoad.rounding
  rw [_p2mH94, _p2mH49]
  rfl
open _root_.P2Mba49f952 renaming h88 → _p2mH88
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h90 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear intercept : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (closure : ℤ)
    (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security (_root_.CurrentAFT.CurrentAffineGeometry.offset security layout core intercept closure hcharge) =
      _root_.CurrentAFT.CurrentAffineLoad.load security layout core scale shear intercept closure 0 := by
  simpa only [Matrix.mulVec_zero, zero_add] using _p2mH92 security layout core scale shear intercept closure hcharge 0
open _root_.P2Mba49f952 renaming h90 → _p2mH90
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h89 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (column : Fin (_root_.CurrentAFT.Parameters.dimension security)) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security (fun row => _root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear row column) =
      _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout core scale shear (Pi.single column 1) := by
  have h := _p2mH88 security layout core scale shear (Pi.single column 1)
  have he : (_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec (Pi.single column 1) =
      fun row => _root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear row column := by
    funext row
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rwa [he] at h
open _root_.P2Mba49f952 renaming h89 → _p2mH89
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h87 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) :
    _root_.AFT.totalCharge (_root_.AFT.injectionColumn (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)) = (_root_.CurrentAFT.Parameters.modulus security : ℤ) := by
  exact _root_.AFT.totalCharge_injectionColumn _ _ (_root_.CurrentAFT.AffineRealization.queue_modulus_le
    (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout))
open _root_.P2Mba49f952 renaming h87 → _p2mH87
set_option maxRecDepth 8192
 theorem _root_.P2Mba49f952.h86 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (modulus : List Bool) (hmodulus : _root_.AFT.BinaryArithmetic.value modulus = _root_.CurrentAFT.Parameters.modulus security)
    (injection bitLoad : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security + 1))
    (hinjection : ∀ vertex, (injection.get vertex).decode = _root_.AFT.injectionColumn _ (_root_.CurrentAFT.Parameters.modulus security) vertex)
    (target : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (hload : ∀ vertex, (bitLoad.get vertex).decode = _root_.CurrentAFT.CurrentAffineLoad.rounding security target (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security vertex)) :
    _root_.CurrentAFT.CurrentAffineLoad.packSource security
      ((fun edge => ((_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad).edges.get edge).decode),
        (_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad).charge.decode) = target := by
  let decodedInjection := injection.map _root_.AFT.BinaryArithmetic.IntegerBits.decode
  let decodedLoad := bitLoad.map _root_.AFT.BinaryArithmetic.IntegerBits.decode
  have hi : decodedInjection.get = _root_.AFT.injectionColumn (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) := by
    funext vertex
    simpa only [decodedInjection, Vector.get_map] using hinjection vertex
  have hm : _root_.AFT.totalCharge decodedInjection.get = (_root_.CurrentAFT.Parameters.modulus security : ℤ) := by
    rw [hi]
    exact _p2mH87 security layout
  have hl : decodedLoad.get = _root_.AFT.roundingLoad (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) decodedInjection.get (_root_.CurrentAFT.CurrentAffineLoad.splitSource security target) := by
    funext vertex
    rw [hi]
    simpa only [decodedLoad, Vector.get_map, _root_.CurrentAFT.CurrentAffineLoad.rounding, Equiv.symm_apply_apply] using hload vertex
  have hd : (_root_.CurrentAFT.Parameters.modulus security : ℤ) ∣ _root_.AFT.totalCharge decodedLoad.get := by
    exact (_root_.AFT.rounding_image_lattice _ _ _ hm _).mp ⟨_root_.CurrentAFT.CurrentAffineLoad.splitSource security target, hl.symm⟩
  have hbitdiv : (_root_.AFT.BinaryArithmetic.value modulus : ℤ) ∣ ∑ vertex, (bitLoad.get vertex).decode := by
    simpa only [hmodulus, decodedLoad, _root_.AFT.totalCharge, Vector.get_map] using hd
  have hb := _p2mH25 (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad
    (by rw [hmodulus]; exact (_root_.CurrentAFT.Parameters.modulus_spec security).2.pos) hbitdiv
  have hq : (_root_.CurrentAFT.Parameters.modulus security : ℤ) ≠ 0 := by exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.ne_zero
  have he : ((_root_.AFT.roundingInverseProgram (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) decodedInjection decodedLoad).value.1.get,
      (_root_.AFT.roundingInverseProgram (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) decodedInjection decodedLoad).value.2) =
        _root_.CurrentAFT.CurrentAffineLoad.splitSource security target := by
    apply _root_.AFT.roundingLoad_injective (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) hq decodedInjection.get hm
    rw [_p2mH40 _ _ _ _ hm hd, hl]
  rw [hmodulus] at hb
  have hresult : ((fun edge => ((_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad).edges.get edge).decode),
      (_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad).charge.decode) = _root_.CurrentAFT.CurrentAffineLoad.splitSource security target := by
    apply (Prod.ext (funext hb.2) hb.1).trans he
  rw [hresult, _p2mH96]
open _root_.P2Mba49f952 renaming h86 → _p2mH86
end
open _root_.P2Mba49f952 renaming h86 → _p2mH86
open _root_.P2Mba49f952 renaming h87 → _p2mH87
open _root_.P2Mba49f952 renaming h88 → _p2mH88
open _root_.P2Mba49f952 renaming h89 → _p2mH89
open _root_.P2Mba49f952 renaming h90 → _p2mH90
end CurrentAFT.CurrentAffineEmissionBridge
open _root_.P2Mba49f952 renaming h86 → _p2mH86
open _root_.P2Mba49f952 renaming h87 → _p2mH87
open _root_.P2Mba49f952 renaming h88 → _p2mH88
open _root_.P2Mba49f952 renaming h89 → _p2mH89
open _root_.P2Mba49f952 renaming h90 → _p2mH90
end
open _root_.P2Mba49f952 renaming h86 → _p2mH86
open _root_.P2Mba49f952 renaming h87 → _p2mH87
open _root_.P2Mba49f952 renaming h88 → _p2mH88
open _root_.P2Mba49f952 renaming h89 → _p2mH89
open _root_.P2Mba49f952 renaming h90 → _p2mH90
namespace CurrentAFT.CurrentAffineData.Valid
end CurrentAFT.CurrentAffineData.Valid
namespace CurrentAFT.CurrentAffineEmissionBridge
end CurrentAFT.CurrentAffineEmissionBridge
namespace CurrentAFT.CurrentAffineLoad.rounding
end CurrentAFT.CurrentAffineLoad.rounding
namespace CurrentAFT.CurrentBinaryAffineGuard
end CurrentAFT.CurrentBinaryAffineGuard
namespace CurrentAFT.CurrentBinaryAffineGuard.current
end CurrentAFT.CurrentBinaryAffineGuard.current
namespace CurrentAFT.CurrentBinaryAffineGuard.scale
end CurrentAFT.CurrentBinaryAffineGuard.scale
namespace CurrentAFT.CurrentMaterializedCompletion
end CurrentAFT.CurrentMaterializedCompletion
namespace CurrentAFT.CurrentMaterializedCompletion.Result
end CurrentAFT.CurrentMaterializedCompletion.Result
namespace CurrentAFT.CurrentMaterializedCompletion.Result.mk
end CurrentAFT.CurrentMaterializedCompletion.Result.mk
namespace CurrentAFT.CurrentMaterializedCompletion.complete
end CurrentAFT.CurrentMaterializedCompletion.complete
namespace CurrentAFT.CurrentMaterializedCompletion.workPolynomial
end CurrentAFT.CurrentMaterializedCompletion.workPolynomial
section
namespace CurrentAFT.CurrentBinaryAffineEmitter
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryAffinePrimitives CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h99 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result security)
    (h : ¬_root_.CurrentAFT.CurrentAffineData.Valid security sample.core.core sample.charts.get) :
    (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).columns = (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback security).columns ∧
      (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback security).offset := by
  have ht : ¬(_root_.CurrentAFT.CurrentBinaryAffineGuard.current security sample.core sample.charts).value = true :=
    fun ht => h ((_p2mH101 security sample.core sample.charts).mp ht)
  simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit, if_neg ht, and_self]
open _root_.P2Mba49f952 renaming h99 → _p2mH99
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h100 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result security)
    (h : _root_.CurrentAFT.CurrentAffineData.Valid security sample.core.core sample.charts.get) :
    (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).columns = (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled security layout sample).columns ∧
      (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled security layout sample).offset := by
  have ht := (_p2mH101 security sample.core sample.charts).mpr h
  simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit, if_pos ht, and_self]
open _root_.P2Mba49f952 renaming h100 → _p2mH100
end
open _root_.P2Mba49f952 renaming h99 → _p2mH99
open _root_.P2Mba49f952 renaming h100 → _p2mH100
end CurrentAFT.CurrentBinaryAffineEmitter
open _root_.P2Mba49f952 renaming h99 → _p2mH99
open _root_.P2Mba49f952 renaming h100 → _p2mH100
end
open _root_.P2Mba49f952 renaming h99 → _p2mH99
open _root_.P2Mba49f952 renaming h100 → _p2mH100
namespace CurrentAFT.CurrentBinaryAffineEmitter
end CurrentAFT.CurrentBinaryAffineEmitter
namespace CurrentAFT.CurrentBinaryAffineEmitter.emit
end CurrentAFT.CurrentBinaryAffineEmitter.emit
namespace CurrentAFT.CurrentBinaryAffineEmitter.emit.match_1
end CurrentAFT.CurrentBinaryAffineEmitter.emit.match_1
section
namespace CurrentAFT.CurrentBinaryFallbackSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentBinaryAffineEmitter
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h427 (test : Prop) [Decidable test] : (if test then _root_.AFT.BinaryArithmetic.IntegerBits.one else _root_.AFT.BinaryArithmetic.IntegerBits.zero).decode = if test then 1 else 0 := by
  split_ifs <;> rfl
open _root_.P2Mba49f952 renaming h427 → _p2mH427
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h114 (security : ℕ) (column : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn security column).value = Pi.single (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column) 1 := by
  funext row
  obtain ⟨edge | point, rfl⟩ := (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).surjective row
  · have he : (_root_.AFT.BinaryArithmetic.equalCounter edge.val column.val).value = true ↔
        _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inl edge) = _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column := by
      rw [_root_.AFT.BinaryArithmetic.equalCounter_value, Fin.ext_iff]
      change edge.val = column.val ↔ edge.val = column.val
      rfl
    simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate, _root_.CurrentAFT.CurrentAffineLoad.packSource, Equiv.symm_apply_apply, Sum.elim_inl,
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn, _root_.AFT.BinaryArithmetic.storeData_get, Fin.val_cast, _p2mH427, Pi.single_apply, he]
  · cases point
    have he : (_root_.AFT.BinaryArithmetic.equalCounter column.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges).value = true ↔
        _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inr ()) = _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column := by
      rw [_root_.AFT.BinaryArithmetic.equalCounter_value, Fin.ext_iff]
      change column.val = (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges ↔ _root_.CurrentAFT.CurrentAffineGeometry.edgeCount security = column.val
      rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1]
      exact eq_comm
    simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate, _root_.CurrentAFT.CurrentAffineLoad.packSource, Equiv.symm_apply_apply, Sum.elim_inr,
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn, _p2mH427, Pi.single_apply, he]
open _root_.P2Mba49f952 renaming h114 → _p2mH114
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h115 (security : ℕ) : _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback security) = 1 := by
  funext row column
  change _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security ((_root_.AFT.BinaryArithmetic.storeData _ (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn security)).value.get ((_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security).symm column)) row = _
  rw [_root_.AFT.BinaryArithmetic.storeData_get, _p2mH114, Equiv.apply_symm_apply]
  simp [Pi.single_apply, Matrix.one_apply]
open _root_.P2Mba49f952 renaming h115 → _p2mH115
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h116 (security : ℕ) : _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback security) = 0 := by
  funext row
  obtain ⟨edge | point, rfl⟩ := (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).surjective row
  · simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset, _root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback, _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate, _root_.CurrentAFT.CurrentAffineLoad.packSource, Equiv.symm_apply_apply,
      Sum.elim_inl, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.BinaryArithmetic.IntegerBits.zero_value, Pi.zero_apply]
  · cases point
    simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset, _root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback, _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate, _root_.CurrentAFT.CurrentAffineLoad.packSource, Equiv.symm_apply_apply,
      Sum.elim_inr, _root_.AFT.BinaryArithmetic.IntegerBits.zero_value, Pi.zero_apply]
open _root_.P2Mba49f952 renaming h116 → _p2mH116
end CurrentAFT.CurrentBinaryFallbackSemantic
open _root_.P2Mba49f952 renaming h114 → _p2mH114
open _root_.P2Mba49f952 renaming h115 → _p2mH115
open _root_.P2Mba49f952 renaming h116 → _p2mH116
open _root_.P2Mba49f952 renaming h427 → _p2mH427
end
open _root_.P2Mba49f952 renaming h114 → _p2mH114
open _root_.P2Mba49f952 renaming h115 → _p2mH115
open _root_.P2Mba49f952 renaming h116 → _p2mH116
namespace CurrentAFT.AffineBaseline.numberedOffset
end CurrentAFT.AffineBaseline.numberedOffset
namespace CurrentAFT.LobsterAffineLoad
end CurrentAFT.LobsterAffineLoad
namespace CurrentAFT.LobsterAffineLoad.primary
end CurrentAFT.LobsterAffineLoad.primary
section
namespace CurrentAFT.CurrentLinearPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates LobsterMixerMatrix PublicCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h167 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout core scale shear input
        (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
      _root_.CurrentAFT.LobsterIncidence.load (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
        ((_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security input).1, (_root_.CurrentAFT.CurrentLinearPhysicalLoad.primary security scale shear input, (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security input).2.2))
        (Sum.map (_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security) id vertex) +
      (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input).2 * _root_.CurrentAFT.AffineRealization.queueColumn (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
        (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core)
        (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex)) := by
  have hi : (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).symm
      (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
      _root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex) := by
    apply (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply, _p2mH91]
  unfold _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad
  rw [hi]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, _p2mH189,
    Equiv.symm_apply_apply]
  rw [_p2mH186]
  simp only [_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply]
  rfl
open _root_.P2Mba49f952 renaming h167 → _p2mH167
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h168 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (point : Sigma (_root_.CurrentAFT.ActualBlockFock.Slots security)) :
    _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout core scale shear input
      (core.endpointPermutation.symm (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security point)) =
      _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical security layout core scale shear input point := by
  have hp : _root_.CurrentAFT.CurrentPhysicalNumbering.numbering security point =
      _root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout (_root_.CurrentAFT.PublicEndpointPlacement.toAssembly security layout point) := by
    change _root_.CurrentAFT.PublicCoefficientOutput.flatten security point =
      _root_.CurrentAFT.PublicCoefficientOutput.flatten security (_root_.CurrentAFT.PublicEndpointPlacement.toPhysical security layout (_root_.CurrentAFT.PublicEndpointPlacement.toAssembly security layout point))
    rw [_root_.CurrentAFT.PublicEndpointPlacement.toPhysical_toAssembly]
  rw [hp, _p2mH167]
  rcases point with ⟨leg | (center | queue), slot⟩
  · change Fin 3 at slot
    fin_cases slot <;>
      simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, Fin.cases, Fin.induction, Fin.induction.go, _root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering, _p2mH188,
        _p2mH187, _root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.PublicCharge.attachmentIncrement,
        _root_.CurrentAFT.CurrentAffineGeometry.attachments, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition, _root_.CurrentAFT.CurrentAffineGeometry.queues, _root_.CurrentAFT.ActualPublicCharge.queuePosition, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, _root_.CurrentAFT.CurrentLinearPhysicalLoad.path, _root_.CurrentAFT.CurrentAffineGeometry.placement]
  · simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, _root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering, _p2mH187,
      _root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.PublicCharge.attachmentIncrement, _root_.CurrentAFT.CurrentAffineGeometry.attachments, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition,
      _root_.CurrentAFT.CurrentAffineGeometry.queues, _root_.CurrentAFT.ActualPublicCharge.queuePosition, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, _root_.CurrentAFT.CurrentLinearPhysicalLoad.path, _root_.CurrentAFT.CurrentAffineGeometry.placement]
  · simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, _root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering, _p2mH187,
      _root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.PublicCharge.attachmentIncrement, _root_.CurrentAFT.CurrentAffineGeometry.attachments, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition,
      _root_.CurrentAFT.CurrentAffineGeometry.queues, _root_.CurrentAFT.ActualPublicCharge.queuePosition, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, _root_.CurrentAFT.CurrentLinearPhysicalLoad.path, _root_.CurrentAFT.CurrentAffineGeometry.placement]
open _root_.P2Mba49f952 renaming h168 → _p2mH168
end
open _root_.P2Mba49f952 renaming h167 → _p2mH167
open _root_.P2Mba49f952 renaming h168 → _p2mH168
end CurrentAFT.CurrentLinearPhysicalLoad
open _root_.P2Mba49f952 renaming h167 → _p2mH167
open _root_.P2Mba49f952 renaming h168 → _p2mH168
end
open _root_.P2Mba49f952 renaming h167 → _p2mH167
open _root_.P2Mba49f952 renaming h168 → _p2mH168
namespace CurrentAFT.CurrentAffineGeometry.attachments
end CurrentAFT.CurrentAffineGeometry.attachments
namespace CurrentAFT.CurrentAffineGeometry.naturalNumbering
end CurrentAFT.CurrentAffineGeometry.naturalNumbering
namespace CurrentAFT.CurrentAffineGeometry.placement
end CurrentAFT.CurrentAffineGeometry.placement
namespace CurrentAFT.CurrentAffineGeometry.queues
end CurrentAFT.CurrentAffineGeometry.queues
namespace CurrentAFT.CurrentLinearPhysicalLoad
end CurrentAFT.CurrentLinearPhysicalLoad
namespace CurrentAFT.CurrentLinearPhysicalLoad.path
end CurrentAFT.CurrentLinearPhysicalLoad.path
namespace CurrentAFT.CurrentLinearPhysicalLoad.physical
end CurrentAFT.CurrentLinearPhysicalLoad.physical
namespace CurrentAFT.CurrentLinearPhysicalLoad.physical.match_1
end CurrentAFT.CurrentLinearPhysicalLoad.physical.match_1
section
namespace CurrentAFT.CurrentBinaryLoadSemantic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentBinaryLoadColumns CurrentEmissionMetadata
open CurrentCoreProposal (MaterializedCore)
open
  CurrentLinearPhysicalLoad CurrentAffineGeometry CurrentAffineLoad
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentEmissionMetadata.current CurrentProposalDimensions.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h130 (security : ℕ) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    (_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1 =
      _root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv security point) := by
  rcases point with leg | body
  · apply Fin.ext
    rfl
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    all_goals
      apply Fin.ext
      simp only [_root_.CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv, Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply,
        ← he, Equiv.symm_apply_apply]
    · change (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)+body.val=_root_.CurrentAFT.Parameters.legCount security+center.val
      have hv := congrArg Fin.val he
      change center.val=body.val at hv
      rw [show _root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security=_root_.CurrentAFT.Parameters.legCount security from (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1, hv]
    · change (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)+body.val=_root_.CurrentAFT.Parameters.legCount security+(_root_.CurrentAFT.ActualBlockFock.centerCount security+queue.val)
      have hv := congrArg Fin.val he
      change _root_.CurrentAFT.ActualBlockFock.centerCount security+queue.val=body.val at hv
      rw [show _root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security=_root_.CurrentAFT.Parameters.legCount security from (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1, hv]
open _root_.P2Mba49f952 renaming h130 → _p2mH130
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h123 (security : ℕ) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    _root_.CurrentAFT.CurrentEmissionRootOrder.rootToRole security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv security point) = _root_.CurrentAFT.CurrentBinaryBaselines.role security point := by
  rcases point with leg | body
  · rfl
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    all_goals simp only [_root_.CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv, _root_.CurrentAFT.CurrentBinaryBaselines.role, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.trans_apply, ← he, Equiv.symm_apply_apply]; rfl
open _root_.P2Mba49f952 renaming h123 → _p2mH123
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h131 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    ((_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value.get
      ((_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1)).val =
      (core.core.bodyPermutation.symm (layout.layout (_root_.CurrentAFT.CurrentBinaryBaselines.role security point))).val := by
  have h := _p2mH148 security layout core
    ((_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1)
  rw [_p2mH130, Equiv.symm_apply_apply, _p2mH123] at h
  have hv := congrArg (fun vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security => vertex.val) h
  simpa only [_root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv, finCongr_apply, Fin.val_cast, _p2mH130] using hv
open _root_.P2Mba49f952 renaming h131 → _p2mH131
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h122 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (index : Fin (_root_.CurrentAFT.Parameters.dimension security)) :
    (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column) index = if index.val=column.val then 1 else 0 := by
  simp only [_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput, Pi.single_apply, Fin.ext_iff]
  rfl
open _root_.P2Mba49f952 renaming h122 → _p2mH122
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h124 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) :
    (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).1 =
      fun edge => if edge.val=column.val then 1 else 0 := by
  funext edge
  change (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
    (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inl edge)))) = _
  rw [_p2mH122]
  rfl
open _root_.P2Mba49f952 renaming h124 → _p2mH124
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h125 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).2.1 leg =
      if _root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security+leg.val=column.val then 1 else 0 := by
  change (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
    (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inr (.inl leg))))) = _
  rw [_p2mH122]
  rfl
open _root_.P2Mba49f952 renaming h125 → _p2mH125
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h132 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).2.2 leg =
      if _root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security+(_root_.CurrentAFT.Parameters.legCount security+leg.val)=column.val then 1 else 0 := by
  change (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
    (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inr (.inr leg))))) = _
  rw [_p2mH122]
  rfl
open _root_.P2Mba49f952 renaming h132 → _p2mH132
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h129 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) :
    (_root_.CurrentAFT.CurrentAffineLoad.splitSource security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).2 =
      if column.val=(_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges then 1 else 0 := by
  change (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column) (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inr ())) = _
  rw [_p2mH122]
  change (if _root_.CurrentAFT.CurrentAffineGeometry.edgeCount security=column.val then (1 : ℤ) else 0)=_
  simp only [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1, eq_comm]
open _root_.P2Mba49f952 renaming h129 → _p2mH129
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h128 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1))
    (scale shear : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) → ℤ) (leg : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) :
    _root_.CurrentAFT.CurrentLinearPhysicalLoad.primary security (fun i => scale ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm i))
      (fun i => shear ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm i))
      (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column) (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg) =
      _root_.CurrentAFT.CurrentBinaryLoadColumns.primaryEntry security column.val scale shear leg := by
  rw [_root_.CurrentAFT.CurrentLinearPhysicalLoad.primary, _p2mH125, _p2mH132]
  simp only [Equiv.symm_apply_apply]
  have hleg : (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg).val=leg.val := rfl
  rw [hleg]
  unfold _root_.CurrentAFT.CurrentBinaryLoadColumns.primaryEntry
  simp only [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).1, show _root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security=_root_.CurrentAFT.Parameters.legCount security from
    (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
  simp only [_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges, add_comm (_root_.CurrentAFT.Parameters.legCount security) leg.val, ← add_assoc,
    eq_comm, mul_ite, mul_one, mul_zero]
open _root_.P2Mba49f952 renaming h128 → _p2mH128
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h133 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (leg : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) :
    (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).2.2 (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg) =
      _root_.CurrentAFT.CurrentBinaryLoadColumns.secondEntry security column.val leg := by
  rw [_p2mH132]
  unfold _root_.CurrentAFT.CurrentBinaryLoadColumns.secondEntry
  simp only [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).1, show _root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security=_root_.CurrentAFT.Parameters.legCount security from
    (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
  have hleg : (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg).val=leg.val := rfl
  rw [hleg]
  simp only [_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges, add_comm (_root_.CurrentAFT.Parameters.legCount security) leg.val, ← add_assoc, eq_comm]
open _root_.P2Mba49f952 renaming h133 → _p2mH133
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h127 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    _root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue security column.val (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value point =
      _root_.CurrentAFT.CurrentLinearPhysicalLoad.path security core.core (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
        (layout.layout (_root_.CurrentAFT.CurrentBinaryBaselines.role security point)) := by
  unfold _root_.CurrentAFT.CurrentLinearPhysicalLoad.path _root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue
  rw [_p2mH124, _p2mH172, _p2mH172]
  simp only [Fin.val_cast]
  simp only [_p2mH131, (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).1]
  rfl
open _root_.P2Mba49f952 renaming h127 → _p2mH127
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h126 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (scale shear : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) → ℤ) (point : _root_.CurrentAFT.CurrentBinaryLoadColumns.Point security) :
    _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry security column.val scale shear (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value point =
      _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout.layout core.core
        (fun leg => scale ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg))
        (fun leg => shear ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg))
        (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
        (core.core.endpointPermutation.symm (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security (_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv security point))) := by
  rw [_p2mH168]
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    fin_cases slot <;> simp only [_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv, Equiv.coe_fn_mk, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, Matrix.cons_val_zero', Matrix.cons_val_succ',
      _p2mH128, _p2mH133, _p2mH127, _root_.CurrentAFT.CurrentBinaryBaselines.role]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    · have hv := congrArg Fin.val he
      change center.val=body.val at hv
      have hn : ¬(_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers ≤ body.val := by
        rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.2.2, ← hv]
        exact Nat.not_le.mpr center.isLt
      simp only [_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv, Equiv.coe_fn_mk, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, ← he, Equiv.symm_apply_apply, _p2mH127,
        _root_.CurrentAFT.CurrentBinaryBaselines.role, hn, false_and, if_false, add_zero]
    · have hv := congrArg Fin.val he
      change _root_.CurrentAFT.ActualBlockFock.centerCount security+queue.val=body.val at hv
      have hy : (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers ≤ body.val := by
        rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.2.2, ← hv]
        omega
      simp only [_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv, Equiv.coe_fn_mk, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, ← he, Equiv.symm_apply_apply, _p2mH127,
        _root_.CurrentAFT.CurrentBinaryBaselines.role, hy, true_and, _p2mH129]
open _root_.P2Mba49f952 renaming h126 → _p2mH126
end
open _root_.P2Mba49f952 renaming h122 → _p2mH122
open _root_.P2Mba49f952 renaming h123 → _p2mH123
open _root_.P2Mba49f952 renaming h124 → _p2mH124
open _root_.P2Mba49f952 renaming h125 → _p2mH125
open _root_.P2Mba49f952 renaming h126 → _p2mH126
open _root_.P2Mba49f952 renaming h127 → _p2mH127
open _root_.P2Mba49f952 renaming h128 → _p2mH128
open _root_.P2Mba49f952 renaming h129 → _p2mH129
open _root_.P2Mba49f952 renaming h130 → _p2mH130
open _root_.P2Mba49f952 renaming h131 → _p2mH131
open _root_.P2Mba49f952 renaming h132 → _p2mH132
open _root_.P2Mba49f952 renaming h133 → _p2mH133
end CurrentAFT.CurrentBinaryLoadSemantic
open _root_.P2Mba49f952 renaming h122 → _p2mH122
open _root_.P2Mba49f952 renaming h123 → _p2mH123
open _root_.P2Mba49f952 renaming h124 → _p2mH124
open _root_.P2Mba49f952 renaming h125 → _p2mH125
open _root_.P2Mba49f952 renaming h126 → _p2mH126
open _root_.P2Mba49f952 renaming h127 → _p2mH127
open _root_.P2Mba49f952 renaming h128 → _p2mH128
open _root_.P2Mba49f952 renaming h129 → _p2mH129
open _root_.P2Mba49f952 renaming h130 → _p2mH130
open _root_.P2Mba49f952 renaming h131 → _p2mH131
open _root_.P2Mba49f952 renaming h132 → _p2mH132
open _root_.P2Mba49f952 renaming h133 → _p2mH133
end
open _root_.P2Mba49f952 renaming h122 → _p2mH122
open _root_.P2Mba49f952 renaming h123 → _p2mH123
open _root_.P2Mba49f952 renaming h124 → _p2mH124
open _root_.P2Mba49f952 renaming h125 → _p2mH125
open _root_.P2Mba49f952 renaming h126 → _p2mH126
open _root_.P2Mba49f952 renaming h127 → _p2mH127
open _root_.P2Mba49f952 renaming h128 → _p2mH128
open _root_.P2Mba49f952 renaming h129 → _p2mH129
open _root_.P2Mba49f952 renaming h130 → _p2mH130
open _root_.P2Mba49f952 renaming h131 → _p2mH131
open _root_.P2Mba49f952 renaming h132 → _p2mH132
open _root_.P2Mba49f952 renaming h133 → _p2mH133
namespace CurrentAFT.CurrentBinaryFallbackSemantic
end CurrentAFT.CurrentBinaryFallbackSemantic
namespace CurrentAFT.CurrentBinaryLoadSemantic
end CurrentAFT.CurrentBinaryLoadSemantic
namespace CurrentAFT.CurrentBinaryLoadSemantic.basisInput
end CurrentAFT.CurrentBinaryLoadSemantic.basisInput
namespace CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv
end CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
namespace CurrentAFT.CurrentLinearPhysicalLoad.primary
end CurrentAFT.CurrentLinearPhysicalLoad.primary
namespace CurrentAFT.CurrentProposalDimensions.bodyEquiv
end CurrentAFT.CurrentProposalDimensions.bodyEquiv
section
namespace CurrentAFT.CurrentBinaryMatrixSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h136 (security : ℕ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (count : ℕ) (hc : count = _root_.CurrentAFT.CurrentAffineGeometry.edgeCount security)
    (modulus : List Bool) (hm : _root_.AFT.BinaryArithmetic.value modulus = _root_.CurrentAFT.Parameters.modulus security)
    (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count + 1))
    (hi : ∀ vertex, (injection.get vertex).decode = if vertex.val < _root_.CurrentAFT.Parameters.modulus security then 1 else 0)
    (target : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (hl : ∀ vertex, (load.get vertex).decode = _root_.CurrentAFT.CurrentAffineLoad.rounding security target
      (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security (vertex.cast (congrArg (fun n => n + 1) hc)))) :
    _root_.CurrentAFT.CurrentAffineLoad.packSource security
      ((fun edge => ((_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).edges.get (edge.cast hc.symm)).decode),
        (_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).charge.decode) = target := by
  subst count
  apply _p2mH86 security layout modulus hm injection load
    (fun vertex => hi vertex) target
  intro vertex
  simpa only [id_eq,Fin.cast_refl] using hl vertex
open _root_.P2Mba49f952 renaming h136 → _p2mH136
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h138 (security : ℕ) (vertex : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    _root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security
      (vertex.cast (congrArg (fun n => n + 1) (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1)) = _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security vertex := by
  apply Fin.ext
  rfl
open _root_.P2Mba49f952 renaming h138 → _p2mH138
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h137 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security))
    (column row : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    ((_root_.AFT.BinaryArithmetic.binaryPermutedColumn (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges
      (_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix security scale shear (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value).value
      (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value column).value.get row).decode =
    _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout.layout core.core
      (fun leg => (scale.get ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)).decode)
      (fun leg => (shear.get ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)).decode)
      (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column) (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row) := by
  rw [_p2mH21, _p2mH120, _p2mH126]
  have hp := _p2mH147 security ((_root_.AFT.physicalVertexNumberingProgram (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest
    (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1).symm ((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value.get row))
  rw [Equiv.apply_symm_apply] at hp
  rw [← hp, _p2mH103, Equiv.symm_apply_apply]
open _root_.P2Mba49f952 renaming h137 → _p2mH137
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h135 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security))
    (column : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security
      (_root_.AFT.BinaryArithmetic.binaryAffineColumn (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges
        (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits
        (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.injection security).value
        (_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix security scale shear (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value).value
        (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value column).value =
    fun row => _root_.CurrentAFT.CurrentAffineGeometry.matrix security layout.layout core.core
      (fun leg => (scale.get ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)).decode)
      (fun leg => (shear.get ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)).decode) row (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column) := by
  unfold _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate _root_.AFT.BinaryArithmetic.binaryAffineColumn
  apply _p2mH136 security layout.layout (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1
  · rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.CurrentAFT.PublicParameterProgram.modulus_value]
  · intro vertex
    exact _p2mH104 security vertex
  · intro vertex
    rw [_p2mH137, _p2mH138]
    exact congrFun (_p2mH89 security layout.layout core.core _ _
      (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column)).symm (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security vertex)
open _root_.P2Mba49f952 renaming h135 → _p2mH135
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h134 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled security layout sample) =
      _root_.CurrentAFT.CurrentAffineGeometry.matrix security layout.layout sample.core.core
        (_root_.CurrentAFT.CurrentAffineData.scales security sample.charts.get) (_root_.CurrentAFT.CurrentAffineData.shears security sample.charts.get) := by
  funext row column
  simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix, _root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled, _root_.AFT.BinaryArithmetic.storeData_get, _p2mH135,
    Equiv.apply_symm_apply]
  congr 1 <;> funext leg <;>
    simp only [_p2mH108, Equiv.apply_symm_apply,
      _root_.CurrentAFT.CurrentAffineData.scales, _root_.CurrentAFT.CurrentAffineData.shears]
open _root_.P2Mba49f952 renaming h134 → _p2mH134
end
open _root_.P2Mba49f952 renaming h134 → _p2mH134
open _root_.P2Mba49f952 renaming h135 → _p2mH135
open _root_.P2Mba49f952 renaming h136 → _p2mH136
open _root_.P2Mba49f952 renaming h137 → _p2mH137
open _root_.P2Mba49f952 renaming h138 → _p2mH138
end CurrentAFT.CurrentBinaryMatrixSemantic
open _root_.P2Mba49f952 renaming h134 → _p2mH134
open _root_.P2Mba49f952 renaming h135 → _p2mH135
open _root_.P2Mba49f952 renaming h136 → _p2mH136
open _root_.P2Mba49f952 renaming h137 → _p2mH137
open _root_.P2Mba49f952 renaming h138 → _p2mH138
end
open _root_.P2Mba49f952 renaming h134 → _p2mH134
open _root_.P2Mba49f952 renaming h135 → _p2mH135
open _root_.P2Mba49f952 renaming h136 → _p2mH136
open _root_.P2Mba49f952 renaming h137 → _p2mH137
open _root_.P2Mba49f952 renaming h138 → _p2mH138
section
namespace CurrentAFT.CurrentOffsetPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h169 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (intercept : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (scalar : ℤ) (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core)
    (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security (_root_.CurrentAFT.CurrentAffineGeometry.offset security layout core intercept scalar hcharge)
      (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
      _root_.CurrentAFT.AffineBaseline.offset (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.centers security layout core)
        (_root_.CurrentAFT.ActualPublicCharge.legShift security core) intercept (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) scalar
        (Sum.map (_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security) id vertex) := by
  have hi : (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).symm
      (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
      _root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex) := by
    apply (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply, _p2mH91]
  rw [_p2mH90 security layout core 0 0 intercept scalar hcharge]
  unfold _root_.CurrentAFT.CurrentAffineLoad.load
  rw [show _root_.CurrentAFT.CurrentAffineLoad.splitSource security (0 : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) = 0 from rfl]
  simp only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, map_zero, ZeroMemClass.coe_zero,
    zero_smul, zero_add, _root_.CurrentAFT.AffineBaseline.numberedOffset, hi, Equiv.symm_apply_apply, _root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering,
    Equiv.trans_apply, Equiv.sumCongr_apply]
  rfl
open _root_.P2Mba49f952 renaming h169 → _p2mH169
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h170 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (intercept : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (scalar : ℤ) (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core)
    (point : Sigma (_root_.CurrentAFT.ActualBlockFock.Slots security)) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security (_root_.CurrentAFT.CurrentAffineGeometry.offset security layout core intercept scalar hcharge)
      (core.endpointPermutation.symm (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security point)) =
      _root_.CurrentAFT.CurrentOffsetPhysicalLoad.physical security layout core intercept scalar point := by
  have hp : _root_.CurrentAFT.CurrentPhysicalNumbering.numbering security point =
      _root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout (_root_.CurrentAFT.PublicEndpointPlacement.toAssembly security layout point) := by
    change _root_.CurrentAFT.PublicCoefficientOutput.flatten security point =
      _root_.CurrentAFT.PublicCoefficientOutput.flatten security (_root_.CurrentAFT.PublicEndpointPlacement.toPhysical security layout (_root_.CurrentAFT.PublicEndpointPlacement.toAssembly security layout point))
    rw [_root_.CurrentAFT.PublicEndpointPlacement.toPhysical_toAssembly]
  rw [hp, _p2mH169]
  rcases point with ⟨leg | (center | queue), slot⟩
  · change Fin 3 at slot
    fin_cases slot <;>
      simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, Fin.cases, Fin.induction, Fin.induction.go, _root_.CurrentAFT.AffineBaseline.offset,
        _root_.CurrentAFT.AffineBaseline.baseline, _root_.CurrentAFT.CurrentAffineGeometry.centers, _root_.CurrentAFT.CurrentAffineGeometry.placement, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.physical, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.rootLoad]
  · simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, _root_.CurrentAFT.AffineBaseline.offset, _root_.CurrentAFT.AffineBaseline.baseline, _root_.CurrentAFT.CurrentAffineGeometry.centers, _root_.CurrentAFT.CurrentAffineGeometry.placement, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.physical, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.rootLoad]
  · simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, _root_.CurrentAFT.AffineBaseline.offset, _root_.CurrentAFT.AffineBaseline.baseline, _root_.CurrentAFT.CurrentAffineGeometry.centers, _root_.CurrentAFT.CurrentAffineGeometry.placement, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.physical, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.rootLoad]
open _root_.P2Mba49f952 renaming h170 → _p2mH170
end
open _root_.P2Mba49f952 renaming h169 → _p2mH169
open _root_.P2Mba49f952 renaming h170 → _p2mH170
end CurrentAFT.CurrentOffsetPhysicalLoad
open _root_.P2Mba49f952 renaming h169 → _p2mH169
open _root_.P2Mba49f952 renaming h170 → _p2mH170
end
open _root_.P2Mba49f952 renaming h169 → _p2mH169
open _root_.P2Mba49f952 renaming h170 → _p2mH170
namespace CurrentAFT.CurrentAffineGeometry.centers
end CurrentAFT.CurrentAffineGeometry.centers
namespace CurrentAFT.CurrentOffsetPhysicalLoad
end CurrentAFT.CurrentOffsetPhysicalLoad
namespace CurrentAFT.CurrentOffsetPhysicalLoad.physical
end CurrentAFT.CurrentOffsetPhysicalLoad.physical
namespace CurrentAFT.CurrentOffsetPhysicalLoad.physical.match_1
end CurrentAFT.CurrentOffsetPhysicalLoad.physical.match_1
namespace CurrentAFT.CurrentOffsetPhysicalLoad.rootLoad
end CurrentAFT.CurrentOffsetPhysicalLoad.rootLoad
section
namespace CurrentAFT.CurrentBinaryOffsetSemantic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentBinaryLoadColumns CurrentEmissionMetadata CurrentBinaryLoadSemantic
  CurrentAffineGeometry CurrentAffineLoad
open CurrentCoreProposal (MaterializedCore)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentEmissionMetadata.current CurrentProposalDimensions.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h142 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (scalar : ℤ) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    _root_.CurrentAFT.AffineBaseline.closure (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges scalar
      (((_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value.get
        ((_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1)).cast
          (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm) =
    _root_.CurrentAFT.AffineBaseline.closure (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) scalar
      (_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security
        (core.core.bodyPermutation.symm (layout.layout (_root_.CurrentAFT.CurrentBinaryBaselines.role security point)))) := by
  simp only [_root_.CurrentAFT.AffineBaseline.closure, Fin.ext_iff, Fin.val_cast, Fin.val_last, Fin.val_zero,
    _p2mH131, (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).1]
  rfl
open _root_.P2Mba49f952 renaming h142 → _p2mH142
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h143 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (intercept : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) → ℤ) (scalar : ℤ) (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core.core)
    (point : _root_.CurrentAFT.CurrentBinaryLoadColumns.Point security) :
    _root_.CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad security core layout.layout (_root_.CurrentAFT.Parameters.modulus security)
      (fun leg => _root_.CurrentAFT.ActualPublicCharge.legShift security core.core (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg)) intercept
      (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value scalar point =
      _root_.CurrentAFT.CurrentAffineLoad.rounding security
        (_root_.CurrentAFT.CurrentAffineGeometry.offset security layout.layout core.core
          (fun leg => intercept ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)) scalar hcharge)
        (core.core.endpointPermutation.symm (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security (_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv security point))) := by
  rw [_p2mH170]
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    fin_cases slot <;> simp only [_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv, Equiv.coe_fn_mk, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.physical,
      _root_.CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Equiv.symm_apply_apply, _p2mH142, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.rootLoad, _root_.CurrentAFT.CurrentBinaryBaselines.role]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    all_goals simp only [_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv, Equiv.coe_fn_mk, _root_.CurrentAFT.CurrentOffsetPhysicalLoad.physical,
      _root_.CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad, ← he, Equiv.symm_apply_apply, _p2mH142,
      _root_.CurrentAFT.CurrentOffsetPhysicalLoad.rootLoad, _root_.CurrentAFT.CurrentBinaryBaselines.role]
open _root_.P2Mba49f952 renaming h143 → _p2mH143
end
open _root_.P2Mba49f952 renaming h142 → _p2mH142
open _root_.P2Mba49f952 renaming h143 → _p2mH143
end CurrentAFT.CurrentBinaryOffsetSemantic
open _root_.P2Mba49f952 renaming h142 → _p2mH142
open _root_.P2Mba49f952 renaming h143 → _p2mH143
end
open _root_.P2Mba49f952 renaming h142 → _p2mH142
open _root_.P2Mba49f952 renaming h143 → _p2mH143
namespace CurrentAFT.CurrentAffineData.shears
end CurrentAFT.CurrentAffineData.shears
namespace CurrentAFT.CurrentBinaryMatrixSemantic
end CurrentAFT.CurrentBinaryMatrixSemantic
namespace CurrentAFT.CurrentBinaryOffsetSemantic
end CurrentAFT.CurrentBinaryOffsetSemantic
section
namespace CurrentAFT.CurrentBinaryEmitterSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h113 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result security) (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security sample.core.core)
    (row : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    ((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad security
      (_root_.CurrentAFT.CurrentBinaryOffsetLoad.load security sample.core
        ⟨false, (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits⟩
        (_root_.CurrentAFT.CurrentBinaryChartData.shiftArray security sample.core).value
        (_root_.CurrentAFT.CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.1)).value
        (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout sample.core).value
        (_root_.CurrentAFT.CurrentPublicShiftProgram.encode sample.edge.val).value).value
      (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security sample.core).value).value.get row).decode =
    _root_.CurrentAFT.CurrentAffineLoad.rounding security
      (_root_.CurrentAFT.CurrentAffineGeometry.offset security layout.layout sample.core.core
        (_root_.CurrentAFT.CurrentAffineData.intercepts security sample.charts.get) sample.edge.val hcharge) (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row) := by
  rw [_p2mH105, _p2mH141 security sample.core layout.layout]
  have hmod : (⟨false, (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits⟩ : _root_.AFT.BinaryArithmetic.IntegerBits).decode = _root_.CurrentAFT.Parameters.modulus security := by
    simp only [_root_.AFT.BinaryArithmetic.IntegerBits.decode, _root_.AFT.BinaryArithmetic.signedValue, _root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.CurrentAFT.PublicParameterProgram.modulus_value, Bool.false_eq_true, if_false]
  rw [hmod, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value]
  simp only [_p2mH109]
  rw [_p2mH143 security layout sample.core _ _ hcharge]
  have hp := _p2mH147 security ((_root_.AFT.physicalVertexNumberingProgram (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest
    (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1).symm ((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security sample.core).value.get row))
  rw [Equiv.apply_symm_apply] at hp
  rw [← hp, _p2mH103, Equiv.symm_apply_apply]
  congr 2
  funext leg
  simp only [_p2mH108, Equiv.apply_symm_apply, _root_.CurrentAFT.CurrentAffineData.intercepts]
open _root_.P2Mba49f952 renaming h113 → _p2mH113
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h110 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result security) (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security sample.core.core) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled security layout sample) =
      _root_.CurrentAFT.CurrentAffineGeometry.offset security layout.layout sample.core.core
        (_root_.CurrentAFT.CurrentAffineData.intercepts security sample.charts.get) sample.edge.val hcharge := by
  unfold _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset _root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate
  apply _p2mH136 security layout.layout (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1
  · rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.CurrentAFT.PublicParameterProgram.modulus_value]
  · intro vertex
    exact _p2mH104 security vertex
  · intro vertex
    rw [_p2mH113 security layout sample hcharge, _p2mH138]
open _root_.P2Mba49f952 renaming h110 → _p2mH110
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h111 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (input : Option (_root_.CurrentAFT.CurrentMaterializedCompletion.Result security)) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout input) =
      (_root_.CurrentAFT.NumericalAffineTransport.realizeResult security layout.layout (input.map _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample)).matrix := by
  cases input with
  | none => exact _p2mH115 security
  | some sample =>
    by_cases h : _root_.CurrentAFT.CurrentAffineData.Valid security sample.core.core sample.charts.get
    · have he := (_p2mH100 security layout sample h).1
      change (fun row column => _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security
        ((_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).columns.get ((_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security).symm column)) row) = _
      rw [he]
      exact (_p2mH134 security layout sample).trans (by
        simp only [_root_.CurrentAFT.NumericalAffineTransport.realizeResult, Option.map_some, _root_.CurrentAFT.CurrentPublicAffineSample.realize,
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample, _root_.CurrentAFT.CurrentAffineData.assemble, dif_pos h, _root_.CurrentAFT.CurrentAffineData.assembled])
    · have he := (_p2mH99 security layout sample h).1
      change (fun row column => _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security
        ((_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).columns.get ((_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security).symm column)) row) = _
      rw [he]
      exact (_p2mH115 security).trans (by
        simp only [_root_.CurrentAFT.NumericalAffineTransport.realizeResult, Option.map_some, _root_.CurrentAFT.CurrentPublicAffineSample.realize,
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample, _root_.CurrentAFT.CurrentAffineData.assemble, dif_neg h, _root_.CurrentAFT.CurrentAffineData.fallback])
open _root_.P2Mba49f952 renaming h111 → _p2mH111
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h112 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (input : Option (_root_.CurrentAFT.CurrentMaterializedCompletion.Result security)) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout input) =
      (_root_.CurrentAFT.NumericalAffineTransport.realizeResult security layout.layout (input.map _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample)).offset := by
  cases input with
  | none => exact _p2mH116 security
  | some sample =>
    by_cases h : _root_.CurrentAFT.CurrentAffineData.Valid security sample.core.core sample.charts.get
    · have he := (_p2mH100 security layout sample h).2
      change _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = _
      rw [he]
      exact (_p2mH110 security layout sample h.1).trans (by
        simp only [_root_.CurrentAFT.NumericalAffineTransport.realizeResult, Option.map_some, _root_.CurrentAFT.CurrentPublicAffineSample.realize,
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample, _root_.CurrentAFT.CurrentAffineData.assemble, dif_pos h, _root_.CurrentAFT.CurrentAffineData.assembled])
    · have he := (_p2mH99 security layout sample h).2
      change _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = _
      rw [he]
      exact (_p2mH116 security).trans (by
        simp only [_root_.CurrentAFT.NumericalAffineTransport.realizeResult, Option.map_some, _root_.CurrentAFT.CurrentPublicAffineSample.realize,
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample, _root_.CurrentAFT.CurrentAffineData.assemble, dif_neg h, _root_.CurrentAFT.CurrentAffineData.fallback])
open _root_.P2Mba49f952 renaming h112 → _p2mH112
end
open _root_.P2Mba49f952 renaming h110 → _p2mH110
open _root_.P2Mba49f952 renaming h111 → _p2mH111
open _root_.P2Mba49f952 renaming h112 → _p2mH112
open _root_.P2Mba49f952 renaming h113 → _p2mH113
end CurrentAFT.CurrentBinaryEmitterSemantic
open _root_.P2Mba49f952 renaming h110 → _p2mH110
open _root_.P2Mba49f952 renaming h111 → _p2mH111
open _root_.P2Mba49f952 renaming h112 → _p2mH112
open _root_.P2Mba49f952 renaming h113 → _p2mH113
end
open _root_.P2Mba49f952 renaming h110 → _p2mH110
open _root_.P2Mba49f952 renaming h111 → _p2mH111
open _root_.P2Mba49f952 renaming h112 → _p2mH112
open _root_.P2Mba49f952 renaming h113 → _p2mH113
namespace CurrentAFT.CurrentAffineData.intercepts
end CurrentAFT.CurrentAffineData.intercepts
namespace CurrentAFT.CurrentBinaryEmitterSemantic
end CurrentAFT.CurrentBinaryEmitterSemantic
namespace CurrentAFT.CurrentMaterializedCompletion.Result.sample
end CurrentAFT.CurrentMaterializedCompletion.Result.sample
namespace CurrentAFT.CurrentPublicAffineSample.realize
end CurrentAFT.CurrentPublicAffineSample.realize
namespace CurrentAFT.NumericalAffineTransport
end CurrentAFT.NumericalAffineTransport
namespace CurrentAFT.NumericalAffineTransport.realizeResult
end CurrentAFT.NumericalAffineTransport.realizeResult
namespace CurrentAFT.NumericalAffineTransport.realizeResult.match_1
end CurrentAFT.NumericalAffineTransport.realizeResult.match_1
namespace CurrentAFT.PublicBitResources
end CurrentAFT.PublicBitResources
section
namespace CurrentAFT.PublicAffinePipeline
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h194 (security extra : ℕ) (data : _root_.CurrentAFT.CurrentBinaryAffineEmitter.Data security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.PublicAffinePipeline.addWork security extra data) =
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security data := rfl
open _root_.P2Mba49f952 renaming h194 → _p2mH194
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h195 (security extra : ℕ) (data : _root_.CurrentAFT.CurrentBinaryAffineEmitter.Data security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.PublicAffinePipeline.addWork security extra data) =
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security data := rfl
open _root_.P2Mba49f952 renaming h195 → _p2mH195
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h196 (security order : ℕ) (producer : _root_.CurrentAFT.PublicAffinePipeline.Producer security order)
    (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (word : _root_.CurrentAFT.CurrentMaterializedCompletion.Tapes security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.PublicAffinePipeline.forLayout security order producer layout word) =
      (_root_.CurrentAFT.NumericalAffineTransport.realizeResult security layout.layout
        ((_root_.CurrentAFT.CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample)).matrix :=
  _p2mH111 security layout _
open _root_.P2Mba49f952 renaming h196 → _p2mH196
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h197 (security order : ℕ) (producer : _root_.CurrentAFT.PublicAffinePipeline.Producer security order)
    (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (word : _root_.CurrentAFT.CurrentMaterializedCompletion.Tapes security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.PublicAffinePipeline.forLayout security order producer layout word) =
      (_root_.CurrentAFT.NumericalAffineTransport.realizeResult security layout.layout
        ((_root_.CurrentAFT.CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample)).offset :=
  _p2mH112 security layout _
open _root_.P2Mba49f952 renaming h197 → _p2mH197
end
open _root_.P2Mba49f952 renaming h194 → _p2mH194
open _root_.P2Mba49f952 renaming h195 → _p2mH195
open _root_.P2Mba49f952 renaming h196 → _p2mH196
open _root_.P2Mba49f952 renaming h197 → _p2mH197
end CurrentAFT.PublicAffinePipeline
open _root_.P2Mba49f952 renaming h194 → _p2mH194
open _root_.P2Mba49f952 renaming h195 → _p2mH195
open _root_.P2Mba49f952 renaming h196 → _p2mH196
open _root_.P2Mba49f952 renaming h197 → _p2mH197
end
open _root_.P2Mba49f952 renaming h194 → _p2mH194
open _root_.P2Mba49f952 renaming h195 → _p2mH195
open _root_.P2Mba49f952 renaming h196 → _p2mH196
open _root_.P2Mba49f952 renaming h197 → _p2mH197
namespace CurrentAFT.PublicBitTapes
end CurrentAFT.PublicBitTapes
namespace CurrentAFT.PublicBitTapes.Encoding
end CurrentAFT.PublicBitTapes.Encoding
namespace CurrentAFT.PublicBitTapes.Encoding.mk
end CurrentAFT.PublicBitTapes.Encoding.mk
section
namespace CurrentAFT.BinaryPublicBitCodec
open AFT BinaryArithmetic RationalRejectionProgram PublicBitTapes
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h70 {State : Type*} (codec : _root_.CurrentAFT.BinaryPublicBitCodec.Codec State)
    (word : Fin codec.encoding.bits → Fin 2) :
    (_root_.CurrentAFT.BinaryPublicBitCodec.decode codec word).value = codec.encoding.equiv word := by
  simp only [_root_.CurrentAFT.BinaryPublicBitCodec.decode,codec.read_value,Vector.get_cast,_root_.AFT.BinaryArithmetic.storeData_get,Nat.zero_add]
  apply congrArg
  funext index
  congr 1
open _root_.P2Mba49f952 renaming h70 → _p2mH70
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h69 {State : Type*} (codec : _root_.CurrentAFT.BinaryPublicBitCodec.Codec State) (target : _root_.CurrentAFT.PublicBitTapes.Encoding State)
    (same : codec.encoding=target) (word : Fin target.bits → Fin 2) :
    (_root_.CurrentAFT.BinaryPublicBitCodec.decodeAs codec target same word).value = target.equiv word := by
  subst target
  exact _p2mH70 codec word
open _root_.P2Mba49f952 renaming h69 → _p2mH69
end CurrentAFT.BinaryPublicBitCodec
open _root_.P2Mba49f952 renaming h69 → _p2mH69
open _root_.P2Mba49f952 renaming h70 → _p2mH70
end
open _root_.P2Mba49f952 renaming h69 → _p2mH69
open _root_.P2Mba49f952 renaming h70 → _p2mH70
namespace AFT.RationalNumerics.windowTicketBits
end AFT.RationalNumerics.windowTicketBits
namespace CurrentAFT.BinaryPublicBitCodec
end CurrentAFT.BinaryPublicBitCodec
namespace CurrentAFT.BinaryPublicBitCodec.Codec
end CurrentAFT.BinaryPublicBitCodec.Codec
namespace CurrentAFT.BinaryPublicBitCodec.Codec.mk
end CurrentAFT.BinaryPublicBitCodec.Codec.mk
namespace CurrentAFT.BinaryPublicBitCodec.Codec.read
end CurrentAFT.BinaryPublicBitCodec.Codec.read
namespace CurrentAFT.BinaryPublicBitCodec.copy
end CurrentAFT.BinaryPublicBitCodec.copy
namespace CurrentAFT.BinaryPublicBitCodec.decode
end CurrentAFT.BinaryPublicBitCodec.decode
namespace CurrentAFT.BinaryPublicBitSizes
end CurrentAFT.BinaryPublicBitSizes
namespace CurrentAFT.BinaryPublicBitSizes.Data
end CurrentAFT.BinaryPublicBitSizes.Data
namespace CurrentAFT.BinaryPublicBitSizes.Data.mk
end CurrentAFT.BinaryPublicBitSizes.Data.mk
namespace CurrentAFT.BinaryPublicBitSizes.Lengths
end CurrentAFT.BinaryPublicBitSizes.Lengths
namespace CurrentAFT.BinaryPublicBitSizes.Lengths.mk
end CurrentAFT.BinaryPublicBitSizes.Lengths.mk
namespace CurrentAFT.BinaryPublicBitSizes.assemble
end CurrentAFT.BinaryPublicBitSizes.assemble
namespace CurrentAFT.BinaryPublicBitSizes.current
end CurrentAFT.BinaryPublicBitSizes.current
namespace CurrentAFT.BinaryPublicBitSizes.formula
end CurrentAFT.BinaryPublicBitSizes.formula
namespace CurrentAFT.BinaryPublicBitSizes.workPolynomial
end CurrentAFT.BinaryPublicBitSizes.workPolynomial
namespace CurrentAFT.PublicBitTapes.split
end CurrentAFT.PublicBitTapes.split
section
namespace CurrentAFT.BinaryPublicBitDecode
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
open BinaryPublicBitCodec
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus BinaryPublicBitSizes.current PublicBitTapes.current
variable (security : ℕ) (sizes : BinaryPublicBitSizes.Data) (correct : sizes=BinaryPublicBitSizes.current security)
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h71 (security : ℕ) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2) :
    (_root_.CurrentAFT.BinaryPublicBitDecode.current security word).value=(_root_.CurrentAFT.PublicBitTapes.current security).equiv word :=
  _p2mH69 (_root_.CurrentAFT.BinaryPublicBitDecode.codec security (_root_.CurrentAFT.BinaryPublicBitSizes.current security) rfl) (_root_.CurrentAFT.PublicBitTapes.current security)
    (_root_.CurrentAFT.BinaryPublicBitDecode.codec_encoding security (_root_.CurrentAFT.BinaryPublicBitSizes.current security) rfl) word
open _root_.P2Mba49f952 renaming h71 → CurrentAFT.BinaryPublicBitDecode.current_value
open _root_.P2Mba49f952 renaming h71 → _p2mH71
noncomputable section
attribute [local irreducible] UniformPolynomialBound
end
end CurrentAFT.BinaryPublicBitDecode
open _root_.P2Mba49f952 renaming h71 → CurrentAFT.BinaryPublicBitDecode.current_value
open _root_.P2Mba49f952 renaming h71 → _p2mH71
end
open _root_.P2Mba49f952 renaming h71 → CurrentAFT.BinaryPublicBitDecode.current_value
open _root_.P2Mba49f952 renaming h71 → _p2mH71
namespace CurrentAFT.ActualAffineEvaluator
end CurrentAFT.ActualAffineEvaluator
namespace CurrentAFT.ActualAffineEvaluator.budgetPolynomial
end CurrentAFT.ActualAffineEvaluator.budgetPolynomial
namespace CurrentAFT.ActualAffineEvaluator.coordinateEntry
end CurrentAFT.ActualAffineEvaluator.coordinateEntry
namespace CurrentAFT.ActualAffineEvaluator.decodeInput
end CurrentAFT.ActualAffineEvaluator.decodeInput
namespace CurrentAFT.ActualAffineEvaluator.dotWork
end CurrentAFT.ActualAffineEvaluator.dotWork
namespace CurrentAFT.ActualAffineEvaluator.evaluate
end CurrentAFT.ActualAffineEvaluator.evaluate
namespace CurrentAFT.ActualAffineEvaluator.nativeCoordinate
end CurrentAFT.ActualAffineEvaluator.nativeCoordinate
namespace CurrentAFT.ActualAffineEvaluator.productEntry
end CurrentAFT.ActualAffineEvaluator.productEntry
namespace CurrentAFT.ActualAffineEvaluator.productWork
end CurrentAFT.ActualAffineEvaluator.productWork
namespace CurrentAFT.ActualAffineEvaluator.row
end CurrentAFT.ActualAffineEvaluator.row
namespace CurrentAFT.ActualAffineEvaluator.rowWork
end CurrentAFT.ActualAffineEvaluator.rowWork
namespace CurrentAFT.ActualAffineEvaluator.workBound
end CurrentAFT.ActualAffineEvaluator.workBound
namespace CurrentAFT.BinaryFullResponseMatrixEntry
end CurrentAFT.BinaryFullResponseMatrixEntry
namespace CurrentAFT.BinaryFullResponseMatrixEntry.validWorkPolynomial
end CurrentAFT.BinaryFullResponseMatrixEntry.validWorkPolynomial
namespace CurrentAFT.BinaryNaturalCoordinates
end CurrentAFT.BinaryNaturalCoordinates
namespace CurrentAFT.BinaryNaturalCoordinates.current
end CurrentAFT.BinaryNaturalCoordinates.current
namespace CurrentAFT.BinaryPublicBitDecode
end CurrentAFT.BinaryPublicBitDecode
namespace CurrentAFT.PublicAffinePipeline
end CurrentAFT.PublicAffinePipeline
namespace CurrentAFT.PublicAffinePipeline.workPolynomial
end CurrentAFT.PublicAffinePipeline.workPolynomial
section
namespace CurrentAFT.ActualConstructiveSampler
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open ActualCalibrationRates BinaryFullResponseData
open Filter
open scoped Classical Topology
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus
  BinaryPublicBitDecode.current PublicAffinePipeline.run
  CurrentBinaryAffineEmitter.matrix CurrentBinaryAffineEmitter.offset
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h43 (security order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2) :
    _root_.CurrentAFT.ActualConstructiveSampler.run security order data word=
      _root_.CurrentAFT.PublicAffinePipeline.addWork security (_root_.CurrentAFT.BinaryPublicBitDecode.current security word).work
        (_root_.CurrentAFT.PublicAffinePipeline.fairBitRun security order (_root_.CurrentAFT.ActualConstructiveSampler.producer security order data) word) := by
  exact congrArg (fun decoded => _root_.CurrentAFT.PublicAffinePipeline.addWork security (_root_.CurrentAFT.BinaryPublicBitDecode.current security word).work
    (_root_.CurrentAFT.PublicAffinePipeline.run security order (_root_.CurrentAFT.ActualConstructiveSampler.producer security order data) decoded))
      (_p2mH71 security word)
open _root_.P2Mba49f952 renaming h43 → _p2mH43
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h44 (security order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.ActualConstructiveSampler.run security order data word)=
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security
        (_root_.CurrentAFT.PublicAffinePipeline.fairBitRun security order (_root_.CurrentAFT.ActualConstructiveSampler.producer security order data) word) := by
  exact (congrArg (_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security) (_p2mH43 security order data word)).trans
    (_p2mH194 security _ _)
open _root_.P2Mba49f952 renaming h44 → _p2mH44
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h45 (security order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.ActualConstructiveSampler.run security order data word)=
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security
        (_root_.CurrentAFT.PublicAffinePipeline.fairBitRun security order (_root_.CurrentAFT.ActualConstructiveSampler.producer security order data) word) := by
  exact (congrArg (_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security) (_p2mH43 security order data word)).trans
    (_p2mH195 security _ _)
open _root_.P2Mba49f952 renaming h45 → _p2mH45
attribute [local instance] _root_.CurrentAFT.ActualConstructiveSampler.uniformFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualConstructiveSampler.modulusNeZero
end
open _root_.P2Mba49f952 renaming h43 → _p2mH43
open _root_.P2Mba49f952 renaming h44 → _p2mH44
open _root_.P2Mba49f952 renaming h45 → _p2mH45
end CurrentAFT.ActualConstructiveSampler
open _root_.P2Mba49f952 renaming h43 → _p2mH43
open _root_.P2Mba49f952 renaming h44 → _p2mH44
open _root_.P2Mba49f952 renaming h45 → _p2mH45
end
open _root_.P2Mba49f952 renaming h43 → _p2mH43
open _root_.P2Mba49f952 renaming h44 → _p2mH44
open _root_.P2Mba49f952 renaming h45 → _p2mH45
namespace CurrentAFT.PublicAffinePipeline.run
end CurrentAFT.PublicAffinePipeline.run
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.NativePipelineSemantic
open CurrentAFT
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  CurrentAFT.Parameters.base CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension
  CurrentAFT.Parameters.legCount CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current
  CurrentLayoutDraw.draw PublicAffinePipeline.forLayout PublicAffinePipeline.addWork
  CurrentBinaryAffineEmitter.matrix CurrentBinaryAffineEmitter.offset
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h211 (security order : ℕ) (producer : _root_.CurrentAFT.PublicAffinePipeline.Producer security order)
    (word : _root_.CurrentAFT.PublicBitTapes.Tapes security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.PublicAffinePipeline.run security order producer word)=
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security
        (_root_.CurrentAFT.CurrentLayoutDraw.draw security security word.1).value
        (_root_.CurrentAFT.CurrentMaterializedCompletion.current security order
          (producer (_root_.CurrentAFT.CurrentLayoutDraw.draw security security word.1).value).value word.2).value) := by
  unfold _root_.CurrentAFT.PublicAffinePipeline.run
  rw [_p2mH194,_p2mH196,
    _p2mH111]
open _root_.P2Mba49f952 renaming h211 → _p2mH211
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h212 (security order : ℕ) (producer : _root_.CurrentAFT.PublicAffinePipeline.Producer security order)
    (word : _root_.CurrentAFT.PublicBitTapes.Tapes security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.PublicAffinePipeline.run security order producer word)=
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security
        (_root_.CurrentAFT.CurrentLayoutDraw.draw security security word.1).value
        (_root_.CurrentAFT.CurrentMaterializedCompletion.current security order
          (producer (_root_.CurrentAFT.CurrentLayoutDraw.draw security security word.1).value).value word.2).value) := by
  unfold _root_.CurrentAFT.PublicAffinePipeline.run
  rw [_p2mH195,_p2mH197,
    _p2mH112]
open _root_.P2Mba49f952 renaming h212 → _p2mH212
end Integration9_9.NativePipelineSemantic
open _root_.P2Mba49f952 renaming h211 → _p2mH211
open _root_.P2Mba49f952 renaming h212 → _p2mH212
end
open _root_.P2Mba49f952 renaming h211 → _p2mH211
open _root_.P2Mba49f952 renaming h212 → _p2mH212
namespace AFT.BinaryArithmetic.Difference
end AFT.BinaryArithmetic.Difference
namespace AFT.BinaryArithmetic.Difference.mk
end AFT.BinaryArithmetic.Difference.mk
namespace AFT.BinaryArithmetic.IntegerBits.negate
end AFT.BinaryArithmetic.IntegerBits.negate
namespace AFT.BinaryArithmetic.RationalBits.arctan
end AFT.BinaryArithmetic.RationalBits.arctan
namespace AFT.BinaryArithmetic.RationalBits.arctanTerm
end AFT.BinaryArithmetic.RationalBits.arctanTerm
namespace AFT.BinaryArithmetic.RationalBits.chartAllowedTerm
end AFT.BinaryArithmetic.RationalBits.chartAllowedTerm
namespace AFT.BinaryArithmetic.RationalBits.chartConditional
end AFT.BinaryArithmetic.RationalBits.chartConditional
namespace AFT.BinaryArithmetic.RationalBits.chartConditionalTerm
end AFT.BinaryArithmetic.RationalBits.chartConditionalTerm
namespace AFT.BinaryArithmetic.RationalBits.chartExpectation
end AFT.BinaryArithmetic.RationalBits.chartExpectation
namespace AFT.BinaryArithmetic.RationalBits.chartFeature
end AFT.BinaryArithmetic.RationalBits.chartFeature
namespace AFT.BinaryArithmetic.RationalBits.chartProjection
end AFT.BinaryArithmetic.RationalBits.chartProjection
namespace AFT.BinaryArithmetic.RationalBits.chartProjectionTerm
end AFT.BinaryArithmetic.RationalBits.chartProjectionTerm
namespace AFT.BinaryArithmetic.RationalBits.decode
end AFT.BinaryArithmetic.RationalBits.decode
namespace AFT.BinaryArithmetic.RationalBits.difference
end AFT.BinaryArithmetic.RationalBits.difference
namespace AFT.BinaryArithmetic.RationalBits.gaussian
end AFT.BinaryArithmetic.RationalBits.gaussian
namespace AFT.BinaryArithmetic.RationalBits.gaussianFromRatio
end AFT.BinaryArithmetic.RationalBits.gaussianFromRatio
namespace AFT.BinaryArithmetic.RationalBits.gaussianRatioWork
end AFT.BinaryArithmetic.RationalBits.gaussianRatioWork
namespace AFT.BinaryArithmetic.RationalBits.gaussianWork
end AFT.BinaryArithmetic.RationalBits.gaussianWork
namespace AFT.BinaryArithmetic.RationalBits.mk
end AFT.BinaryArithmetic.RationalBits.mk
namespace AFT.BinaryArithmetic.RationalBits.pi
end AFT.BinaryArithmetic.RationalBits.pi
namespace AFT.BinaryArithmetic.RationalBits.piWork
end AFT.BinaryArithmetic.RationalBits.piWork
namespace AFT.BinaryArithmetic.RationalBits.seriesStepWork
end AFT.BinaryArithmetic.RationalBits.seriesStepWork
namespace AFT.BinaryArithmetic.RationalBits.seriesTermWork
end AFT.BinaryArithmetic.RationalBits.seriesTermWork
namespace AFT.BinaryArithmetic.RationalBits.taylor
end AFT.BinaryArithmetic.RationalBits.taylor
namespace AFT.BinaryArithmetic.RationalBits.taylorTerm
end AFT.BinaryArithmetic.RationalBits.taylorTerm
namespace AFT.BinaryArithmetic.RationalBits.termBits_bounds
end AFT.BinaryArithmetic.RationalBits.termBits_bounds
namespace AFT.BinaryArithmetic.RationalResult
end AFT.BinaryArithmetic.RationalResult
namespace AFT.BinaryArithmetic.RationalResult.mk
end AFT.BinaryArithmetic.RationalResult.mk
namespace AFT.BinaryArithmetic.Result
end AFT.BinaryArithmetic.Result
namespace AFT.BinaryArithmetic.Result.mk
end AFT.BinaryArithmetic.Result.mk
namespace AFT.BinaryArithmetic.add
end AFT.BinaryArithmetic.add
namespace AFT.BinaryArithmetic.add.match_1
end AFT.BinaryArithmetic.add.match_1
namespace AFT.BinaryArithmetic.binaryAnchorSliceTerm
end AFT.BinaryArithmetic.binaryAnchorSliceTerm
namespace AFT.BinaryArithmetic.binaryAnchorSliceTermWork
end AFT.BinaryArithmetic.binaryAnchorSliceTermWork
namespace AFT.BinaryArithmetic.binaryAveragedSlice
end AFT.BinaryArithmetic.binaryAveragedSlice
namespace AFT.BinaryArithmetic.binaryAveragedSliceWork
end AFT.BinaryArithmetic.binaryAveragedSliceWork
namespace AFT.BinaryArithmetic.multiply
end AFT.BinaryArithmetic.multiply
namespace AFT.BinaryArithmetic.multiply.match_1
end AFT.BinaryArithmetic.multiply.match_1
namespace AFT.BinaryArithmetic.reduce
end AFT.BinaryArithmetic.reduce
namespace AFT.BinaryArithmetic.signedValue
end AFT.BinaryArithmetic.signedValue
namespace AFT.BinaryArithmetic.subtract
end AFT.BinaryArithmetic.subtract
namespace AFT.BinaryArithmetic.subtract.match_1
end AFT.BinaryArithmetic.subtract.match_1
namespace AFT.BinaryArithmetic.value
end AFT.BinaryArithmetic.value
namespace AFT.BinaryArithmetic.value.match_1
end AFT.BinaryArithmetic.value.match_1
namespace AFT.RationalNumerics.windowApproxPrecision
end AFT.RationalNumerics.windowApproxPrecision
namespace CurrentAFT.BinaryActivationProgram
end CurrentAFT.BinaryActivationProgram
namespace CurrentAFT.BinaryActivationProgram.current
end CurrentAFT.BinaryActivationProgram.current
namespace CurrentAFT.BinaryActivationProgram.currentHeight
end CurrentAFT.BinaryActivationProgram.currentHeight
namespace CurrentAFT.BinaryActivationProgram.currentHeightPolynomial
end CurrentAFT.BinaryActivationProgram.currentHeightPolynomial
namespace CurrentAFT.BinaryActivationProgram.currentWork
end CurrentAFT.BinaryActivationProgram.currentWork
namespace CurrentAFT.BinaryActivationProgram.currentWorkPolynomial
end CurrentAFT.BinaryActivationProgram.currentWorkPolynomial
namespace CurrentAFT.BinaryActivationProgram.cutoff
end CurrentAFT.BinaryActivationProgram.cutoff
namespace CurrentAFT.BinaryActivationProgram.cutoffWork
end CurrentAFT.BinaryActivationProgram.cutoffWork
namespace CurrentAFT.BinaryActivationProgram.cutoffWorkPolynomial
end CurrentAFT.BinaryActivationProgram.cutoffWorkPolynomial
namespace CurrentAFT.BinaryBodyKernel
end CurrentAFT.BinaryBodyKernel
namespace CurrentAFT.BinaryBodyKernel.baselineWork
end CurrentAFT.BinaryBodyKernel.baselineWork
namespace CurrentAFT.BinaryBodyKernel.baselineWorkPolynomial
end CurrentAFT.BinaryBodyKernel.baselineWorkPolynomial
namespace CurrentAFT.BinaryBodyKernel.sliceWorkPolynomial
end CurrentAFT.BinaryBodyKernel.sliceWorkPolynomial
namespace CurrentAFT.BinaryBodyKernel.translated
end CurrentAFT.BinaryBodyKernel.translated
namespace CurrentAFT.BinaryBodyKernel.translatedWork
end CurrentAFT.BinaryBodyKernel.translatedWork
namespace CurrentAFT.BinaryBodyKernel.translatedWorkPolynomial
end CurrentAFT.BinaryBodyKernel.translatedWorkPolynomial
namespace CurrentAFT.BinaryBodyProgram
end CurrentAFT.BinaryBodyProgram
namespace CurrentAFT.BinaryBodyProgram.currentHeightPolynomial
end CurrentAFT.BinaryBodyProgram.currentHeightPolynomial
namespace CurrentAFT.BinaryBodyProgram.currentWorkPolynomial
end CurrentAFT.BinaryBodyProgram.currentWorkPolynomial
namespace CurrentAFT.BinaryBodyProgram.evaluate
end CurrentAFT.BinaryBodyProgram.evaluate
namespace CurrentAFT.BinaryBodyProgram.integerBound
end CurrentAFT.BinaryBodyProgram.integerBound
namespace CurrentAFT.BinaryBodyProgram.integerPolynomial
end CurrentAFT.BinaryBodyProgram.integerPolynomial
namespace CurrentAFT.BinaryBodyProgram.kernelHeight
end CurrentAFT.BinaryBodyProgram.kernelHeight
namespace CurrentAFT.BinaryBodyProgram.kernelHeightPolynomial
end CurrentAFT.BinaryBodyProgram.kernelHeightPolynomial
namespace CurrentAFT.BinaryBodyProgram.kernelWork
end CurrentAFT.BinaryBodyProgram.kernelWork
namespace CurrentAFT.BinaryBodyProgram.kernelWorkPolynomial
end CurrentAFT.BinaryBodyProgram.kernelWorkPolynomial
namespace CurrentAFT.BinaryBodyProgram.parameterPolynomial
end CurrentAFT.BinaryBodyProgram.parameterPolynomial
namespace CurrentAFT.BinaryBodyProgram.shiftWork
end CurrentAFT.BinaryBodyProgram.shiftWork
namespace CurrentAFT.BinaryBodyProgram.shiftWorkPolynomial
end CurrentAFT.BinaryBodyProgram.shiftWorkPolynomial
namespace CurrentAFT.BinaryDensityInverseColumn
end CurrentAFT.BinaryDensityInverseColumn
namespace CurrentAFT.BinaryDensityInverseColumn.workPolynomial
end CurrentAFT.BinaryDensityInverseColumn.workPolynomial
namespace CurrentAFT.BinaryFirstInverseProgram
end CurrentAFT.BinaryFirstInverseProgram
namespace CurrentAFT.BinaryFirstInverseProgram.Cache
end CurrentAFT.BinaryFirstInverseProgram.Cache
namespace CurrentAFT.BinaryFirstInverseProgram.Cache.mk
end CurrentAFT.BinaryFirstInverseProgram.Cache.mk
namespace CurrentAFT.BinaryFirstInverseProgram.colors
end CurrentAFT.BinaryFirstInverseProgram.colors
namespace CurrentAFT.BinaryFirstInverseProgram.colorsPolynomial
end CurrentAFT.BinaryFirstInverseProgram.colorsPolynomial
namespace CurrentAFT.BinaryFirstInverseProgram.inputAt
end CurrentAFT.BinaryFirstInverseProgram.inputAt
namespace CurrentAFT.BinaryFirstInverseProgram.prepare
end CurrentAFT.BinaryFirstInverseProgram.prepare
namespace CurrentAFT.BinaryFirstInverseProgram.signPoint
end CurrentAFT.BinaryFirstInverseProgram.signPoint
namespace CurrentAFT.BinaryFirstInverseProgram.signWorkPolynomial
end CurrentAFT.BinaryFirstInverseProgram.signWorkPolynomial
namespace CurrentAFT.BinaryMarkedKernel
end CurrentAFT.BinaryMarkedKernel
namespace CurrentAFT.BinaryMarkedKernel.average
end CurrentAFT.BinaryMarkedKernel.average
namespace CurrentAFT.BinaryMarkedKernel.coin
end CurrentAFT.BinaryMarkedKernel.coin
namespace CurrentAFT.BinaryMarkedKernel.point
end CurrentAFT.BinaryMarkedKernel.point
namespace CurrentAFT.BinaryPackedRootSum
end CurrentAFT.BinaryPackedRootSum
namespace CurrentAFT.BinaryPackedRootSum.heightPolynomial
end CurrentAFT.BinaryPackedRootSum.heightPolynomial
namespace CurrentAFT.BinaryPackedRootSum.workPolynomial
end CurrentAFT.BinaryPackedRootSum.workPolynomial
namespace CurrentAFT.BinaryProfileKernel
end CurrentAFT.BinaryProfileKernel
namespace CurrentAFT.BinaryProfileKernel.anchorWorkPolynomial
end CurrentAFT.BinaryProfileKernel.anchorWorkPolynomial
namespace CurrentAFT.BinaryProfileKernel.averagedWorkPolynomial
end CurrentAFT.BinaryProfileKernel.averagedWorkPolynomial
namespace CurrentAFT.BinaryProfileKernel.currentHeight
end CurrentAFT.BinaryProfileKernel.currentHeight
namespace CurrentAFT.BinaryProfileKernel.currentWork
end CurrentAFT.BinaryProfileKernel.currentWork
namespace CurrentAFT.BinaryProfileKernel.heightPolynomial
end CurrentAFT.BinaryProfileKernel.heightPolynomial
namespace CurrentAFT.BinaryProfileKernel.integerBound
end CurrentAFT.BinaryProfileKernel.integerBound
namespace CurrentAFT.BinaryProfileKernel.integerPolynomial
end CurrentAFT.BinaryProfileKernel.integerPolynomial
namespace CurrentAFT.BinaryProfileKernel.sliceWorkPolynomial
end CurrentAFT.BinaryProfileKernel.sliceWorkPolynomial
namespace CurrentAFT.BinaryProfileKernel.start
end CurrentAFT.BinaryProfileKernel.start
namespace CurrentAFT.BinaryProfileKernel.startWork
end CurrentAFT.BinaryProfileKernel.startWork
namespace CurrentAFT.BinaryProfileKernel.startWorkPolynomial
end CurrentAFT.BinaryProfileKernel.startWorkPolynomial
namespace CurrentAFT.BinaryProfileKernel.workPolynomial
end CurrentAFT.BinaryProfileKernel.workPolynomial
namespace CurrentAFT.BinaryProfileProgram
end CurrentAFT.BinaryProfileProgram
namespace CurrentAFT.BinaryProfileProgram.currentHeightPolynomial
end CurrentAFT.BinaryProfileProgram.currentHeightPolynomial
namespace CurrentAFT.BinaryProfileProgram.currentWorkPolynomial
end CurrentAFT.BinaryProfileProgram.currentWorkPolynomial
namespace CurrentAFT.BinaryProfileProgram.evaluate
end CurrentAFT.BinaryProfileProgram.evaluate
namespace CurrentAFT.BinaryProfileTables
end CurrentAFT.BinaryProfileTables
namespace CurrentAFT.BinaryProfileTables.diffuse
end CurrentAFT.BinaryProfileTables.diffuse
namespace CurrentAFT.BinaryProfileTables.diffuseHeightPolynomial
end CurrentAFT.BinaryProfileTables.diffuseHeightPolynomial
namespace CurrentAFT.BinaryProfileTables.diffuseWorkPolynomial
end CurrentAFT.BinaryProfileTables.diffuseWorkPolynomial
namespace CurrentAFT.BinaryProfileTables.sign
end CurrentAFT.BinaryProfileTables.sign
namespace CurrentAFT.BinaryProfileTables.signHeightPolynomial
end CurrentAFT.BinaryProfileTables.signHeightPolynomial
namespace CurrentAFT.BinaryProfileTables.signWorkPolynomial
end CurrentAFT.BinaryProfileTables.signWorkPolynomial
namespace CurrentAFT.BinaryTrimmedPair
end CurrentAFT.BinaryTrimmedPair
namespace CurrentAFT.BinaryTrimmedPair.pairShift
end CurrentAFT.BinaryTrimmedPair.pairShift
namespace CurrentAFT.BinaryTrimmedPair.pairWork
end CurrentAFT.BinaryTrimmedPair.pairWork
namespace CurrentAFT.BinaryTrimmedPair.pairWorkPolynomial
end CurrentAFT.BinaryTrimmedPair.pairWorkPolynomial
namespace CurrentAFT.CoefficientHilbert
end CurrentAFT.CoefficientHilbert
namespace CurrentAFT.CoefficientHilbert.centerLinear
end CurrentAFT.CoefficientHilbert.centerLinear
namespace CurrentAFT.RationalActualFamilyApproximation
end CurrentAFT.RationalActualFamilyApproximation
namespace CurrentAFT.RationalActualFamilyApproximation.data
end CurrentAFT.RationalActualFamilyApproximation.data
namespace CurrentAFT.RationalActualFamilyApproximation.interpret
end CurrentAFT.RationalActualFamilyApproximation.interpret
namespace CurrentAFT.RationalBackgroundDensities
end CurrentAFT.RationalBackgroundDensities
namespace CurrentAFT.RationalBackgroundDensities.bodyErrorConstant
end CurrentAFT.RationalBackgroundDensities.bodyErrorConstant
namespace CurrentAFT.RationalBackgroundDensities.primaryErrorConstant
end CurrentAFT.RationalBackgroundDensities.primaryErrorConstant
namespace CurrentAFT.RationalBackgroundDensities.residualErrorConstant
end CurrentAFT.RationalBackgroundDensities.residualErrorConstant
namespace CurrentAFT.RationalBackgroundProfiles
end CurrentAFT.RationalBackgroundProfiles
namespace CurrentAFT.RationalBackgroundProfiles.Safe
end CurrentAFT.RationalBackgroundProfiles.Safe
namespace CurrentAFT.RationalBackgroundProfiles.safe
end CurrentAFT.RationalBackgroundProfiles.safe
namespace CurrentAFT.RationalBackgroundProfiles.shifted
end CurrentAFT.RationalBackgroundProfiles.shifted
namespace CurrentAFT.RationalBackgroundProfiles.unsafeProfile
end CurrentAFT.RationalBackgroundProfiles.unsafeProfile
namespace CurrentAFT.RationalBackgroundProgram
end CurrentAFT.RationalBackgroundProgram
namespace CurrentAFT.RationalBackgroundTable
end CurrentAFT.RationalBackgroundTable
namespace CurrentAFT.RationalBackgroundTable.firstTable
end CurrentAFT.RationalBackgroundTable.firstTable
namespace CurrentAFT.RationalDensityInverseProgram
end CurrentAFT.RationalDensityInverseProgram
namespace CurrentAFT.RationalDensityInverseProgram.inverseBound
end CurrentAFT.RationalDensityInverseProgram.inverseBound
namespace CurrentAFT.RationalFamilyProductProgram
end CurrentAFT.RationalFamilyProductProgram
namespace CurrentAFT.RationalFamilyProductProgram.binomial
end CurrentAFT.RationalFamilyProductProgram.binomial
namespace CurrentAFT.RationalFamilyProductProgram.power
end CurrentAFT.RationalFamilyProductProgram.power
namespace CurrentAFT.RationalFamilyProductProgram.power.match_1
end CurrentAFT.RationalFamilyProductProgram.power.match_1
namespace CurrentAFT.RationalFamilyProductProgram.pullback
end CurrentAFT.RationalFamilyProductProgram.pullback
namespace CurrentAFT.RationalFamilyProductProgram.reciprocal
end CurrentAFT.RationalFamilyProductProgram.reciprocal
namespace CurrentAFT.RationalFamilyProductProgram.unit
end CurrentAFT.RationalFamilyProductProgram.unit
namespace CurrentAFT.RationalFirstResponseProgram
end CurrentAFT.RationalFirstResponseProgram
namespace CurrentAFT.RationalFirstResponseProgram.anchorSign
end CurrentAFT.RationalFirstResponseProgram.anchorSign
namespace CurrentAFT.RationalFirstResponseProgram.denominator
end CurrentAFT.RationalFirstResponseProgram.denominator
namespace CurrentAFT.RationalFirstResponseProgram.guardedDenominator
end CurrentAFT.RationalFirstResponseProgram.guardedDenominator
namespace CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant
end CurrentAFT.RationalFirstResponseProgram.inverseErrorConstant
namespace CurrentAFT.RationalFirstResponseProgram.profile
end CurrentAFT.RationalFirstResponseProgram.profile
namespace CurrentAFT.RationalFirstResponseProgram.signProfile
end CurrentAFT.RationalFirstResponseProgram.signProfile
namespace CurrentAFT.RationalMassLiftProgram
end CurrentAFT.RationalMassLiftProgram
namespace CurrentAFT.RationalMassLiftProgram.actual
end CurrentAFT.RationalMassLiftProgram.actual
namespace CurrentAFT.RationalMassLiftProgram.errorConstant
end CurrentAFT.RationalMassLiftProgram.errorConstant
namespace CurrentAFT.RationalOrdinaryFamilyProgram
end CurrentAFT.RationalOrdinaryFamilyProgram
namespace CurrentAFT.RationalOrdinaryFamilyProgram.bodyFirst
end CurrentAFT.RationalOrdinaryFamilyProgram.bodyFirst
namespace CurrentAFT.RationalOrdinaryFamilyProgram.first
end CurrentAFT.RationalOrdinaryFamilyProgram.first
namespace CurrentAFT.RationalOrdinaryFamilyProgram.firstActual
end CurrentAFT.RationalOrdinaryFamilyProgram.firstActual
namespace CurrentAFT.RationalOrdinaryProfileProgram
end CurrentAFT.RationalOrdinaryProfileProgram
namespace CurrentAFT.RationalOrdinaryProfileProgram.preRoot
end CurrentAFT.RationalOrdinaryProfileProgram.preRoot
namespace CurrentAFT.RationalOrdinaryProfileProgram.shifted
end CurrentAFT.RationalOrdinaryProfileProgram.shifted
namespace CurrentAFT.RationalProposalProgram
end CurrentAFT.RationalProposalProgram
namespace CurrentAFT.RationalProposalProgram.compensationApprox
end CurrentAFT.RationalProposalProgram.compensationApprox
namespace CurrentAFT.RationalProposalProgram.diffuse
end CurrentAFT.RationalProposalProgram.diffuse
namespace CurrentAFT.RationalProposalProgram.primaryRaw
end CurrentAFT.RationalProposalProgram.primaryRaw
namespace CurrentAFT.RationalRootProfileProgram
end CurrentAFT.RationalRootProfileProgram
namespace CurrentAFT.RationalRootProfileProgram.approximatePreRoot
end CurrentAFT.RationalRootProfileProgram.approximatePreRoot
namespace CurrentAFT.RationalRootProfileProgram.deviation
end CurrentAFT.RationalRootProfileProgram.deviation
namespace CurrentAFT.RationalRootProfileProgram.mean
end CurrentAFT.RationalRootProfileProgram.mean
namespace CurrentAFT.RationalRootProfileProgram.meanDeviation
end CurrentAFT.RationalRootProfileProgram.meanDeviation
namespace CurrentAFT.RationalRootProfileProgram.preRoot
end CurrentAFT.RationalRootProfileProgram.preRoot
namespace CurrentAFT.RationalRootProfileProgram.preRoot.match_1
end CurrentAFT.RationalRootProfileProgram.preRoot.match_1
namespace CurrentAFT.RationalRootProfileProgram.shifted
end CurrentAFT.RationalRootProfileProgram.shifted
namespace CurrentAFT.RationalScalarFamilyAverage
end CurrentAFT.RationalScalarFamilyAverage
namespace CurrentAFT.RationalScalarFamilyAverage.actual
end CurrentAFT.RationalScalarFamilyAverage.actual
namespace CurrentAFT.RationalSingletonProgram
end CurrentAFT.RationalSingletonProgram
namespace CurrentAFT.RationalSingletonProgram.first
end CurrentAFT.RationalSingletonProgram.first
namespace CurrentAFT.RationalSingletonProgram.positive
end CurrentAFT.RationalSingletonProgram.positive
namespace CurrentAFT.RationalTensorInverseProgram
end CurrentAFT.RationalTensorInverseProgram
namespace CurrentAFT.RationalTensorInverseProgram.actualBound
end CurrentAFT.RationalTensorInverseProgram.actualBound
namespace CurrentAFT.RootMeanPrimary
end CurrentAFT.RootMeanPrimary
namespace CurrentAFT.RootMeanPrimary.positiveAtom
end CurrentAFT.RootMeanPrimary.positiveAtom
namespace CurrentAFT.RootMeanPrimary.positiveFamily
end CurrentAFT.RootMeanPrimary.positiveFamily
namespace CurrentAFT.RootReferenceColumns
end CurrentAFT.RootReferenceColumns
namespace CurrentAFT.RootReferenceColumns.singletonFirstAt
end CurrentAFT.RootReferenceColumns.singletonFirstAt
namespace InfoLossLAR
end InfoLossLAR
namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase
namespace InfoLossLAR.WorstCase.encI
end InfoLossLAR.WorstCase.encI
namespace InfoLossLAR.WorstCase.encPair
end InfoLossLAR.WorstCase.encPair
namespace InfoLossLAR.WorstCase.encS
end InfoLossLAR.WorstCase.encS
namespace Integration9_9
end Integration9_9
namespace Integration9_9.TM2AdditionFrontend
end Integration9_9.TM2AdditionFrontend
namespace Integration9_9.TM2AdditionFrontend.Alphabet
end Integration9_9.TM2AdditionFrontend.Alphabet
namespace Integration9_9.TM2AdditionFrontend.Data
end Integration9_9.TM2AdditionFrontend.Data
namespace Integration9_9.TM2AdditionFrontend.Data.mk
end Integration9_9.TM2AdditionFrontend.Data.mk
namespace Integration9_9.TM2AdditionFrontend.Data.store
end Integration9_9.TM2AdditionFrontend.Data.store
namespace Integration9_9.TM2AdditionFrontend.Label
end Integration9_9.TM2AdditionFrontend.Label
namespace Integration9_9.TM2AdditionFrontend.Label.drain
end Integration9_9.TM2AdditionFrontend.Label.drain
namespace Integration9_9.TM2AdditionFrontend.Label.read
end Integration9_9.TM2AdditionFrontend.Label.read
namespace Integration9_9.TM2AdditionFrontend.Label.revLeft
end Integration9_9.TM2AdditionFrontend.Label.revLeft
namespace Integration9_9.TM2AdditionFrontend.Label.revOut
end Integration9_9.TM2AdditionFrontend.Label.revOut
namespace Integration9_9.TM2AdditionFrontend.Label.revRight
end Integration9_9.TM2AdditionFrontend.Label.revRight
namespace Integration9_9.TM2AdditionFrontend.Label.zip
end Integration9_9.TM2AdditionFrontend.Label.zip
namespace Integration9_9.TM2AdditionFrontend.Stack
end Integration9_9.TM2AdditionFrontend.Stack
namespace Integration9_9.TM2AdditionFrontend.Stack.input
end Integration9_9.TM2AdditionFrontend.Stack.input
namespace Integration9_9.TM2AdditionFrontend.Stack.left
end Integration9_9.TM2AdditionFrontend.Stack.left
namespace Integration9_9.TM2AdditionFrontend.Stack.leftRev
end Integration9_9.TM2AdditionFrontend.Stack.leftRev
namespace Integration9_9.TM2AdditionFrontend.Stack.output
end Integration9_9.TM2AdditionFrontend.Stack.output
namespace Integration9_9.TM2AdditionFrontend.Stack.pairRev
end Integration9_9.TM2AdditionFrontend.Stack.pairRev
namespace Integration9_9.TM2AdditionFrontend.Stack.right
end Integration9_9.TM2AdditionFrontend.Stack.right
namespace Integration9_9.TM2AdditionFrontend.Stack.rightRev
end Integration9_9.TM2AdditionFrontend.Stack.rightRev
namespace Integration9_9.TM2AdditionFrontend.addString
end Integration9_9.TM2AdditionFrontend.addString
namespace Integration9_9.TM2AdditionFrontend.decode
end Integration9_9.TM2AdditionFrontend.decode
namespace Integration9_9.TM2AdditionFrontend.frontend
end Integration9_9.TM2AdditionFrontend.frontend
namespace Integration9_9.TM2AdditionFrontend.getRev
end Integration9_9.TM2AdditionFrontend.getRev
namespace Integration9_9.TM2AdditionFrontend.instDecidableEqLabel
end Integration9_9.TM2AdditionFrontend.instDecidableEqLabel
namespace Integration9_9.TM2AdditionFrontend.instDecidableEqLabel.decEq
end Integration9_9.TM2AdditionFrontend.instDecidableEqLabel.decEq
namespace Integration9_9.TM2AdditionFrontend.instFintypeLabel
end Integration9_9.TM2AdditionFrontend.instFintypeLabel
namespace Integration9_9.TM2AdditionFrontend.marked
end Integration9_9.TM2AdditionFrontend.marked
namespace Integration9_9.TM2AdditionFrontend.nextRead
end Integration9_9.TM2AdditionFrontend.nextRead
namespace Integration9_9.TM2AdditionFrontend.operandCode
end Integration9_9.TM2AdditionFrontend.operandCode
namespace Integration9_9.TM2AdditionFrontend.program
end Integration9_9.TM2AdditionFrontend.program
namespace Integration9_9.TM2AdditionFrontend.readDigits
end Integration9_9.TM2AdditionFrontend.readDigits
namespace Integration9_9.TM2AdditionFrontend.readDigits.match_1
end Integration9_9.TM2AdditionFrontend.readDigits.match_1
namespace Integration9_9.TM2AdditionFrontend.rippleComputer
end Integration9_9.TM2AdditionFrontend.rippleComputer
namespace Integration9_9.TM2AdditionFrontend.setRev
end Integration9_9.TM2AdditionFrontend.setRev
namespace Integration9_9.TM2BinaryAddition
end Integration9_9.TM2BinaryAddition
namespace Integration9_9.TM2BinaryAddition.Alphabet
end Integration9_9.TM2BinaryAddition.Alphabet
namespace Integration9_9.TM2BinaryAddition.Stack
end Integration9_9.TM2BinaryAddition.Stack
namespace Integration9_9.TM2BinaryAddition.Stack.buffer
end Integration9_9.TM2BinaryAddition.Stack.buffer
namespace Integration9_9.TM2BinaryAddition.Stack.input
end Integration9_9.TM2BinaryAddition.Stack.input
namespace Integration9_9.TM2BinaryAddition.Stack.output
end Integration9_9.TM2BinaryAddition.Stack.output
namespace Integration9_9.TM2BinaryAddition.padPairs
end Integration9_9.TM2BinaryAddition.padPairs
namespace Integration9_9.TM2BinaryAddition.padPairs.match_1
end Integration9_9.TM2BinaryAddition.padPairs.match_1
namespace Integration9_9.TM2BinaryAddition.ripple
end Integration9_9.TM2BinaryAddition.ripple
namespace Integration9_9.TM2BinaryAddition.ripple.match_1
end Integration9_9.TM2BinaryAddition.ripple.match_1
namespace Integration9_9.TM2BinaryComparison
end Integration9_9.TM2BinaryComparison
namespace Integration9_9.TM2BinaryComparison.Alphabet
end Integration9_9.TM2BinaryComparison.Alphabet
namespace Integration9_9.TM2BinaryComparison.Flags
end Integration9_9.TM2BinaryComparison.Flags
namespace Integration9_9.TM2BinaryComparison.Flags.mk
end Integration9_9.TM2BinaryComparison.Flags.mk
namespace Integration9_9.TM2BinaryComparison.Stack
end Integration9_9.TM2BinaryComparison.Stack
namespace Integration9_9.TM2BinaryComparison.Stack.input
end Integration9_9.TM2BinaryComparison.Stack.input
namespace Integration9_9.TM2BinaryComparison.Stack.output
end Integration9_9.TM2BinaryComparison.Stack.output
namespace Integration9_9.TM2BinaryComparison.anyBit
end Integration9_9.TM2BinaryComparison.anyBit
namespace Integration9_9.TM2BinaryComparison.equalPair
end Integration9_9.TM2BinaryComparison.equalPair
namespace Integration9_9.TM2BinaryComparison.equalReadout
end Integration9_9.TM2BinaryComparison.equalReadout
namespace Integration9_9.TM2BinaryComparison.instDecidableEqFlags
end Integration9_9.TM2BinaryComparison.instDecidableEqFlags
namespace Integration9_9.TM2BinaryComparison.instDecidableEqFlags.decEq
end Integration9_9.TM2BinaryComparison.instDecidableEqFlags.decEq
namespace Integration9_9.TM2BinaryComparison.instFintypeFlags
end Integration9_9.TM2BinaryComparison.instFintypeFlags
namespace Integration9_9.TM2BinaryComparison.lePair
end Integration9_9.TM2BinaryComparison.lePair
namespace Integration9_9.TM2BinaryComparison.leReadout
end Integration9_9.TM2BinaryComparison.leReadout
namespace Integration9_9.TM2BinaryComparison.lessPair
end Integration9_9.TM2BinaryComparison.lessPair
namespace Integration9_9.TM2BinaryComparison.pairString
end Integration9_9.TM2BinaryComparison.pairString
namespace Integration9_9.TM2BinaryComparison.rawString
end Integration9_9.TM2BinaryComparison.rawString
namespace Integration9_9.TM2BinaryComparison.scan
end Integration9_9.TM2BinaryComparison.scan
namespace Integration9_9.TM2BinaryComparison.scan.match_1
end Integration9_9.TM2BinaryComparison.scan.match_1
namespace Integration9_9.TM2BinaryComparison.update
end Integration9_9.TM2BinaryComparison.update
namespace Integration9_9.TM2Canonical
end Integration9_9.TM2Canonical
namespace Integration9_9.TM2Canonical.Label
end Integration9_9.TM2Canonical.Label
namespace Integration9_9.TM2Canonical.Label.copy
end Integration9_9.TM2Canonical.Label.copy
namespace Integration9_9.TM2Canonical.Label.reverse
end Integration9_9.TM2Canonical.Label.reverse
namespace Integration9_9.TM2Canonical.Label.trim
end Integration9_9.TM2Canonical.Label.trim
namespace Integration9_9.TM2Canonical.Stack
end Integration9_9.TM2Canonical.Stack
namespace Integration9_9.TM2Canonical.Stack.buffer
end Integration9_9.TM2Canonical.Stack.buffer
namespace Integration9_9.TM2Canonical.Stack.input
end Integration9_9.TM2Canonical.Stack.input
namespace Integration9_9.TM2Canonical.Stack.output
end Integration9_9.TM2Canonical.Stack.output
namespace Integration9_9.TM2Canonical.canonical
end Integration9_9.TM2Canonical.canonical
namespace Integration9_9.TM2Canonical.program
end Integration9_9.TM2Canonical.program
namespace Integration9_9.TM2Canonical.store
end Integration9_9.TM2Canonical.store
namespace Integration9_9.TM2Composition
end Integration9_9.TM2Composition
namespace Integration9_9.TM2Composition.Alphabet
end Integration9_9.TM2Composition.Alphabet
namespace Integration9_9.TM2Composition.Alphabet.match_1
end Integration9_9.TM2Composition.Alphabet.match_1
namespace Integration9_9.TM2Composition.canonical
end Integration9_9.TM2Composition.canonical
namespace Integration9_9.TM2Composition.leftStack
end Integration9_9.TM2Composition.leftStack
namespace Integration9_9.TM2Composition.leftSymbol
end Integration9_9.TM2Composition.leftSymbol
namespace Integration9_9.TM2Composition.machine
end Integration9_9.TM2Composition.machine
namespace Integration9_9.TM2Composition.middle
end Integration9_9.TM2Composition.middle
namespace Integration9_9.TM2Composition.program
end Integration9_9.TM2Composition.program
namespace Integration9_9.TM2Composition.rightStack
end Integration9_9.TM2Composition.rightStack
namespace Integration9_9.TM2Composition.rightSymbol
end Integration9_9.TM2Composition.rightSymbol
namespace Integration9_9.TM2DynamicIntegerEncoding
end Integration9_9.TM2DynamicIntegerEncoding
namespace Integration9_9.TM2DynamicIntegerEncoding.Label
end Integration9_9.TM2DynamicIntegerEncoding.Label
namespace Integration9_9.TM2DynamicIntegerEncoding.Label.copy
end Integration9_9.TM2DynamicIntegerEncoding.Label.copy
namespace Integration9_9.TM2DynamicIntegerEncoding.Label.header
end Integration9_9.TM2DynamicIntegerEncoding.Label.header
namespace Integration9_9.TM2DynamicIntegerEncoding.Label.reverse
end Integration9_9.TM2DynamicIntegerEncoding.Label.reverse
namespace Integration9_9.TM2DynamicIntegerEncoding.Label.trim
end Integration9_9.TM2DynamicIntegerEncoding.Label.trim
namespace Integration9_9.TM2DynamicIntegerEncoding.Stack
end Integration9_9.TM2DynamicIntegerEncoding.Stack
namespace Integration9_9.TM2DynamicIntegerEncoding.Stack.buffer
end Integration9_9.TM2DynamicIntegerEncoding.Stack.buffer
namespace Integration9_9.TM2DynamicIntegerEncoding.Stack.input
end Integration9_9.TM2DynamicIntegerEncoding.Stack.input
namespace Integration9_9.TM2DynamicIntegerEncoding.Stack.output
end Integration9_9.TM2DynamicIntegerEncoding.Stack.output
namespace Integration9_9.TM2DynamicIntegerEncoding.encode
end Integration9_9.TM2DynamicIntegerEncoding.encode
namespace Integration9_9.TM2DynamicIntegerEncoding.pack
end Integration9_9.TM2DynamicIntegerEncoding.pack
namespace Integration9_9.TM2DynamicIntegerEncoding.program
end Integration9_9.TM2DynamicIntegerEncoding.program
namespace Integration9_9.TM2DynamicIntegerEncoding.rawCode
end Integration9_9.TM2DynamicIntegerEncoding.rawCode
namespace Integration9_9.TM2DynamicIntegerEncoding.store
end Integration9_9.TM2DynamicIntegerEncoding.store
namespace Integration9_9.TM2NativeActivation
end Integration9_9.TM2NativeActivation
namespace Integration9_9.TM2NativeActivation.windowRequest
end Integration9_9.TM2NativeActivation.windowRequest
namespace Integration9_9.TM2NativeAnchor
end Integration9_9.TM2NativeAnchor
namespace Integration9_9.TM2NativeAnchor.context
end Integration9_9.TM2NativeAnchor.context
namespace Integration9_9.TM2NativeAnchor.current
end Integration9_9.TM2NativeAnchor.current
namespace Integration9_9.TM2NativeAnchor.evaluate_gaussian
end Integration9_9.TM2NativeAnchor.evaluate_gaussian
namespace Integration9_9.TM2NativeAnchor.gaussianRequest
end Integration9_9.TM2NativeAnchor.gaussianRequest
namespace Integration9_9.TM2NativeAnchor.indices
end Integration9_9.TM2NativeAnchor.indices
namespace Integration9_9.TM2NativeAnchor.kernelRequest
end Integration9_9.TM2NativeAnchor.kernelRequest
namespace Integration9_9.TM2NativeAnchor.table
end Integration9_9.TM2NativeAnchor.table
namespace Integration9_9.TM2NativeAnchor.term
end Integration9_9.TM2NativeAnchor.term
namespace Integration9_9.TM2NativeArithmetic
end Integration9_9.TM2NativeArithmetic
namespace Integration9_9.TM2NativeArithmetic.ratFields
end Integration9_9.TM2NativeArithmetic.ratFields
namespace Integration9_9.TM2NativeArithmetic.ratFieldsCode
end Integration9_9.TM2NativeArithmetic.ratFieldsCode
namespace Integration9_9.TM2NativeArithmetic.rawRatCode
end Integration9_9.TM2NativeArithmetic.rawRatCode
namespace Integration9_9.TM2NativeAveragedSlice
end Integration9_9.TM2NativeAveragedSlice
namespace Integration9_9.TM2NativeAveragedSlice.current
end Integration9_9.TM2NativeAveragedSlice.current
namespace Integration9_9.TM2NativeAveragedSlice.profileValue
end Integration9_9.TM2NativeAveragedSlice.profileValue
namespace Integration9_9.TM2NativeAveragedSlice.rawValue
end Integration9_9.TM2NativeAveragedSlice.rawValue
namespace Integration9_9.TM2NativeBackgroundAlgebra
end Integration9_9.TM2NativeBackgroundAlgebra
namespace Integration9_9.TM2NativeBackgroundProfiles
end Integration9_9.TM2NativeBackgroundProfiles
namespace Integration9_9.TM2NativeBackgroundProfiles.colors
end Integration9_9.TM2NativeBackgroundProfiles.colors
namespace Integration9_9.TM2NativeBackgroundProfiles.safeTest
end Integration9_9.TM2NativeBackgroundProfiles.safeTest
namespace Integration9_9.TM2NativeBackgroundProfiles.unsafeProfile
end Integration9_9.TM2NativeBackgroundProfiles.unsafeProfile
namespace Integration9_9.TM2NativeBody
end Integration9_9.TM2NativeBody
namespace Integration9_9.TM2NativeBody.context
end Integration9_9.TM2NativeBody.context
namespace Integration9_9.TM2NativeBody.current
end Integration9_9.TM2NativeBody.current
namespace Integration9_9.TM2NativeBody.evaluate_gaussian
end Integration9_9.TM2NativeBody.evaluate_gaussian
namespace Integration9_9.TM2NativeBody.kernelRequest
end Integration9_9.TM2NativeBody.kernelRequest
namespace Integration9_9.TM2NativeBody.term
end Integration9_9.TM2NativeBody.term
namespace Integration9_9.TM2NativeBodyKernel
end Integration9_9.TM2NativeBodyKernel
namespace Integration9_9.TM2NativeBodyKernel.current
end Integration9_9.TM2NativeBodyKernel.current
namespace Integration9_9.TM2NativeBodyKernel.emodNatural
end Integration9_9.TM2NativeBodyKernel.emodNatural
namespace Integration9_9.TM2NativeBodyKernel.paletteTicks
end Integration9_9.TM2NativeBodyKernel.paletteTicks
namespace Integration9_9.TM2NativeBodyKernel.term
end Integration9_9.TM2NativeBodyKernel.term
namespace Integration9_9.TM2NativeDensityInverseColumn
end Integration9_9.TM2NativeDensityInverseColumn
namespace Integration9_9.TM2NativeDensityInverseColumn.Context
end Integration9_9.TM2NativeDensityInverseColumn.Context
namespace Integration9_9.TM2NativeDensityInverseColumn.Context.mk
end Integration9_9.TM2NativeDensityInverseColumn.Context.mk
namespace Integration9_9.TM2NativeDensityInverseColumn.current
end Integration9_9.TM2NativeDensityInverseColumn.current
namespace Integration9_9.TM2NativeDensityInverseColumn.functionalDelta
end Integration9_9.TM2NativeDensityInverseColumn.functionalDelta
namespace Integration9_9.TM2NativeDensityInverseColumn.functionalDelta_value
end Integration9_9.TM2NativeDensityInverseColumn.functionalDelta_value
namespace Integration9_9.TM2NativeDensityInverseColumn.primaryPoint
end Integration9_9.TM2NativeDensityInverseColumn.primaryPoint
namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries
namespace Integration9_9.TM2NativeFiniteSeries.cappedArctan
end Integration9_9.TM2NativeFiniteSeries.cappedArctan
namespace Integration9_9.TM2NativeFiniteSeries.cappedTaylor
end Integration9_9.TM2NativeFiniteSeries.cappedTaylor
namespace Integration9_9.TM2NativeFiniteSeries.degree
end Integration9_9.TM2NativeFiniteSeries.degree
namespace Integration9_9.TM2NativeFiniteSeries.factorialValue
end Integration9_9.TM2NativeFiniteSeries.factorialValue
namespace Integration9_9.TM2NativeFiniteSeries.powerValue
end Integration9_9.TM2NativeFiniteSeries.powerValue
namespace Integration9_9.TM2NativeFiniteSeries.takeTicks
end Integration9_9.TM2NativeFiniteSeries.takeTicks
namespace Integration9_9.TM2NativeFiniteSeries.takeTicksProgram
end Integration9_9.TM2NativeFiniteSeries.takeTicksProgram
namespace Integration9_9.TM2NativeFirstInverse
end Integration9_9.TM2NativeFirstInverse
namespace Integration9_9.TM2NativeFirstInverse.Context
end Integration9_9.TM2NativeFirstInverse.Context
namespace Integration9_9.TM2NativeFirstInverse.Context.mk
end Integration9_9.TM2NativeFirstInverse.Context.mk
namespace Integration9_9.TM2NativeFirstInverse.anchorSign
end Integration9_9.TM2NativeFirstInverse.anchorSign
namespace Integration9_9.TM2NativeFirstInverse.current
end Integration9_9.TM2NativeFirstInverse.current
namespace Integration9_9.TM2NativeFirstInverse.denominator
end Integration9_9.TM2NativeFirstInverse.denominator
namespace Integration9_9.TM2NativeFirstInverse.functionalTerm
end Integration9_9.TM2NativeFirstInverse.functionalTerm
namespace Integration9_9.TM2NativeFirstInverse.maximum
end Integration9_9.TM2NativeFirstInverse.maximum
namespace Integration9_9.TM2NativeFirstInverse.rawInput
end Integration9_9.TM2NativeFirstInverse.rawInput
namespace Integration9_9.TM2NativeFirstInverse.sign
end Integration9_9.TM2NativeFirstInverse.sign
namespace Integration9_9.TM2NativeFirstInverse.signTable
end Integration9_9.TM2NativeFirstInverse.signTable
namespace Integration9_9.TM2NativeGaussian
end Integration9_9.TM2NativeGaussian
namespace Integration9_9.TM2NativeGaussian.ceil_fraction
end Integration9_9.TM2NativeGaussian.ceil_fraction
namespace Integration9_9.TM2NativeGaussian.ceilingValue
end Integration9_9.TM2NativeGaussian.ceilingValue
namespace Integration9_9.TM2NativeGaussian.clipped
end Integration9_9.TM2NativeGaussian.clipped
namespace Integration9_9.TM2NativeGaussian.exponentialCapped
end Integration9_9.TM2NativeGaussian.exponentialCapped
namespace Integration9_9.TM2NativeGaussian.gaussianArgument
end Integration9_9.TM2NativeGaussian.gaussianArgument
namespace Integration9_9.TM2NativeGaussian.gaussianCapped
end Integration9_9.TM2NativeGaussian.gaussianCapped
namespace Integration9_9.TM2NativeGaussian.guardTicks
end Integration9_9.TM2NativeGaussian.guardTicks
namespace Integration9_9.TM2NativeGaussian.guardTicksProgram
end Integration9_9.TM2NativeGaussian.guardTicksProgram
namespace Integration9_9.TM2NativeGaussian.piTicks
end Integration9_9.TM2NativeGaussian.piTicks
namespace Integration9_9.TM2NativeGaussian.scaleBudget
end Integration9_9.TM2NativeGaussian.scaleBudget
namespace Integration9_9.TM2NativeGaussian.scaleTicks
end Integration9_9.TM2NativeGaussian.scaleTicks
namespace Integration9_9.TM2NativeGaussian.scaleTicksProgram
end Integration9_9.TM2NativeGaussian.scaleTicksProgram
namespace Integration9_9.TM2NativeGaussianWindow
end Integration9_9.TM2NativeGaussianWindow
namespace Integration9_9.TM2NativeGaussianWindow.baseTicks
end Integration9_9.TM2NativeGaussianWindow.baseTicks
namespace Integration9_9.TM2NativeGaussianWindow.current
end Integration9_9.TM2NativeGaussianWindow.current
namespace Integration9_9.TM2NativeGaussianWindow.cutoff
end Integration9_9.TM2NativeGaussianWindow.cutoff
namespace Integration9_9.TM2NativeGaussianWindow.cutoffTicks
end Integration9_9.TM2NativeGaussianWindow.cutoffTicks
namespace Integration9_9.TM2NativeGaussianWindow.indexTicks
end Integration9_9.TM2NativeGaussianWindow.indexTicks
namespace Integration9_9.TM2NativeGaussianWindow.normalize
end Integration9_9.TM2NativeGaussianWindow.normalize
namespace Integration9_9.TM2NativeGaussianWindow.precisionTicks
end Integration9_9.TM2NativeGaussianWindow.precisionTicks
namespace Integration9_9.TM2NativeGaussianWindow.ratio
end Integration9_9.TM2NativeGaussianWindow.ratio
namespace Integration9_9.TM2NativeGaussianWindow.raw
end Integration9_9.TM2NativeGaussianWindow.raw
namespace Integration9_9.TM2NativeGaussianWindow.squareTicks
end Integration9_9.TM2NativeGaussianWindow.squareTicks
namespace Integration9_9.TM2NativeGaussianWindow.width
end Integration9_9.TM2NativeGaussianWindow.width
namespace Integration9_9.TM2NativeMarkedKernel
end Integration9_9.TM2NativeMarkedKernel
namespace Integration9_9.TM2NativeMarkedKernel.coin
end Integration9_9.TM2NativeMarkedKernel.coin
namespace Integration9_9.TM2NativeMarkedKernel.current
end Integration9_9.TM2NativeMarkedKernel.current
namespace Integration9_9.TM2NativeMarkedKernel.total
end Integration9_9.TM2NativeMarkedKernel.total
namespace Integration9_9.TM2NativePrimary
end Integration9_9.TM2NativePrimary
namespace Integration9_9.TM2NativePrimary.body
end Integration9_9.TM2NativePrimary.body
namespace Integration9_9.TM2NativePrimary.colors
end Integration9_9.TM2NativePrimary.colors
namespace Integration9_9.TM2NativePrimary.current
end Integration9_9.TM2NativePrimary.current
namespace Integration9_9.TM2NativePrimary.diffuse
end Integration9_9.TM2NativePrimary.diffuse
namespace Integration9_9.TM2NativePrimary.good
end Integration9_9.TM2NativePrimary.good
namespace Integration9_9.TM2NativePrimary.guard
end Integration9_9.TM2NativePrimary.guard
namespace Integration9_9.TM2NativePrimary.legs
end Integration9_9.TM2NativePrimary.legs
namespace Integration9_9.TM2NativePrimary.population
end Integration9_9.TM2NativePrimary.population
namespace Integration9_9.TM2NativePrimary.rate
end Integration9_9.TM2NativePrimary.rate
namespace Integration9_9.TM2NativePrimary.raw
end Integration9_9.TM2NativePrimary.raw
namespace Integration9_9.TM2NativePrimary.rawTable
end Integration9_9.TM2NativePrimary.rawTable
namespace Integration9_9.TM2NativePrime
end Integration9_9.TM2NativePrime
namespace Integration9_9.TM2NativePrime.candidateTest
end Integration9_9.TM2NativePrime.candidateTest
namespace Integration9_9.TM2NativePrime.doubleSlots
end Integration9_9.TM2NativePrime.doubleSlots
namespace Integration9_9.TM2NativePrime.powerSlots
end Integration9_9.TM2NativePrime.powerSlots
namespace Integration9_9.TM2NativePrime.powerSlots.match_1
end Integration9_9.TM2NativePrime.powerSlots.match_1
namespace Integration9_9.TM2NativePrime.primeTrial
end Integration9_9.TM2NativePrime.primeTrial
namespace Integration9_9.TM2NativePrime.thresholdSlots
end Integration9_9.TM2NativePrime.thresholdSlots
namespace Integration9_9.TM2NativePrime.upperSlots
end Integration9_9.TM2NativePrime.upperSlots
namespace Integration9_9.TM2NativeProfile
end Integration9_9.TM2NativeProfile
namespace Integration9_9.TM2NativeProfile.context
end Integration9_9.TM2NativeProfile.context
namespace Integration9_9.TM2NativeProfile.current
end Integration9_9.TM2NativeProfile.current
namespace Integration9_9.TM2NativeProfile.edgeIndices
end Integration9_9.TM2NativeProfile.edgeIndices
namespace Integration9_9.TM2NativeProfile.edgeRequest
end Integration9_9.TM2NativeProfile.edgeRequest
namespace Integration9_9.TM2NativeProfile.edgeTicks
end Integration9_9.TM2NativeProfile.edgeTicks
namespace Integration9_9.TM2NativeProfile.evaluate
end Integration9_9.TM2NativeProfile.evaluate
namespace Integration9_9.TM2NativeProfile.evaluate_gaussian
end Integration9_9.TM2NativeProfile.evaluate_gaussian
namespace Integration9_9.TM2NativeProfile.gaussianList
end Integration9_9.TM2NativeProfile.gaussianList
namespace Integration9_9.TM2NativeProfile.kernelRequest
end Integration9_9.TM2NativeProfile.kernelRequest
namespace Integration9_9.TM2NativeProfile.scalarIndices
end Integration9_9.TM2NativeProfile.scalarIndices
namespace Integration9_9.TM2NativeProfile.scalarRequest
end Integration9_9.TM2NativeProfile.scalarRequest
namespace Integration9_9.TM2NativeProfile.scalarTicks
end Integration9_9.TM2NativeProfile.scalarTicks
namespace Integration9_9.TM2NativeProfile.seeds
end Integration9_9.TM2NativeProfile.seeds
namespace Integration9_9.TM2NativeProfile.term
end Integration9_9.TM2NativeProfile.term
namespace Integration9_9.TM2NativeProfile.widthTicks
end Integration9_9.TM2NativeProfile.widthTicks
namespace Integration9_9.TM2NativeReferenceTables
end Integration9_9.TM2NativeReferenceTables
namespace Integration9_9.TM2NativeReferenceTables.averageTerm
end Integration9_9.TM2NativeReferenceTables.averageTerm
namespace Integration9_9.TM2NativeReferenceTables.centerTable
end Integration9_9.TM2NativeReferenceTables.centerTable
namespace Integration9_9.TM2NativeReferenceTables.compensation
end Integration9_9.TM2NativeReferenceTables.compensation
namespace Integration9_9.TM2NativeRootGroupAlgebra
end Integration9_9.TM2NativeRootGroupAlgebra
namespace Integration9_9.TM2NativeRootGroupAlgebra.IsPoly
end Integration9_9.TM2NativeRootGroupAlgebra.IsPoly
namespace Integration9_9.TM2NativeRootGroupAlgebra.evaluate
end Integration9_9.TM2NativeRootGroupAlgebra.evaluate
namespace Integration9_9.TM2NativeRootGroupGaussian
end Integration9_9.TM2NativeRootGroupGaussian
namespace Integration9_9.TM2NativeRootGroupGaussian.cutoff
end Integration9_9.TM2NativeRootGroupGaussian.cutoff
namespace Integration9_9.TM2NativeRootGroupGaussian.gaussian
end Integration9_9.TM2NativeRootGroupGaussian.gaussian
namespace Integration9_9.TM2NativeRootGroupGaussian.leftLeaf
end Integration9_9.TM2NativeRootGroupGaussian.leftLeaf
namespace Integration9_9.TM2NativeRootGroupGaussian.rightLeaf
end Integration9_9.TM2NativeRootGroupGaussian.rightLeaf
namespace Integration9_9.TM2NativeRootGroupGaussian.scalarLeaf
end Integration9_9.TM2NativeRootGroupGaussian.scalarLeaf
namespace Integration9_9.TM2NativeRootGroupGaussian.seedAverage
end Integration9_9.TM2NativeRootGroupGaussian.seedAverage
namespace Integration9_9.TM2NativeRootGroupGaussian.windowAverage
end Integration9_9.TM2NativeRootGroupGaussian.windowAverage
namespace Integration9_9.TM2NativeRootGroupProfiles
end Integration9_9.TM2NativeRootGroupProfiles
namespace Integration9_9.TM2NativeRootGroupProfiles.compensation
end Integration9_9.TM2NativeRootGroupProfiles.compensation
namespace Integration9_9.TM2NativeRootGroupProfiles.inverseShift
end Integration9_9.TM2NativeRootGroupProfiles.inverseShift
namespace Integration9_9.TM2NativeRootGroupProfiles.paletteSum
end Integration9_9.TM2NativeRootGroupProfiles.paletteSum
namespace Integration9_9.TM2NativeRootGroupProfiles.safe
end Integration9_9.TM2NativeRootGroupProfiles.safe
namespace Integration9_9.TM2NativeRootGroupProfiles.shifted
end Integration9_9.TM2NativeRootGroupProfiles.shifted
namespace Integration9_9.TM2NativeRootGroupRoles
end Integration9_9.TM2NativeRootGroupRoles
namespace Integration9_9.TM2NativeRootGroupRoles.mean
end Integration9_9.TM2NativeRootGroupRoles.mean
namespace Integration9_9.TM2NativeRootGroupRoles.meanDeviation
end Integration9_9.TM2NativeRootGroupRoles.meanDeviation
namespace Integration9_9.TM2NativeSliceProbability
end Integration9_9.TM2NativeSliceProbability
namespace Integration9_9.TM2NativeSliceProbability.pair
end Integration9_9.TM2NativeSliceProbability.pair
namespace Integration9_9.TM2NativeSliceProbability.rawValue
end Integration9_9.TM2NativeSliceProbability.rawValue
namespace Integration9_9.TM2NativeSliceProbability.slice
end Integration9_9.TM2NativeSliceProbability.slice
namespace Integration9_9.TM2NativeTupleEnumeration
end Integration9_9.TM2NativeTupleEnumeration
namespace Integration9_9.TM2NativeTupleEnumeration.tuples
end Integration9_9.TM2NativeTupleEnumeration.tuples
namespace Integration9_9.TM2NativeTupleEnumeration.tuples.match_1
end Integration9_9.TM2NativeTupleEnumeration.tuples.match_1
namespace Integration9_9.TM2OutputEncoding
end Integration9_9.TM2OutputEncoding
namespace Integration9_9.TM2OutputEncoding.Stack
end Integration9_9.TM2OutputEncoding.Stack
namespace Integration9_9.TM2OutputEncoding.Stack.buffer
end Integration9_9.TM2OutputEncoding.Stack.buffer
namespace Integration9_9.TM2OutputEncoding.Stack.input
end Integration9_9.TM2OutputEncoding.Stack.input
namespace Integration9_9.TM2OutputEncoding.Stack.output
end Integration9_9.TM2OutputEncoding.Stack.output
namespace Integration9_9.TM2OutputEncoding.addSign
end Integration9_9.TM2OutputEncoding.addSign
namespace Integration9_9.TM2OutputEncoding.encodeInteger
end Integration9_9.TM2OutputEncoding.encodeInteger
namespace Integration9_9.TM2OutputEncoding.encodeNatural
end Integration9_9.TM2OutputEncoding.encodeNatural
namespace Integration9_9.TM2OutputEncoding.render
end Integration9_9.TM2OutputEncoding.render
namespace Integration9_9.TM2OutputEncoding.store
end Integration9_9.TM2OutputEncoding.store
namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength
namespace Integration9_9.TM2OutputLength.pushBound
end Integration9_9.TM2OutputLength.pushBound
namespace Integration9_9.TM2OutputLength.pushBound.match_1
end Integration9_9.TM2OutputLength.pushBound.match_1
namespace Integration9_9.TM2PairUnframe
end Integration9_9.TM2PairUnframe
namespace Integration9_9.TM2PairUnframe.Data
end Integration9_9.TM2PairUnframe.Data
namespace Integration9_9.TM2PairUnframe.Data.mk
end Integration9_9.TM2PairUnframe.Data.mk
namespace Integration9_9.TM2PairUnframe.Data.store
end Integration9_9.TM2PairUnframe.Data.store
namespace Integration9_9.TM2PairUnframe.Label
end Integration9_9.TM2PairUnframe.Label
namespace Integration9_9.TM2PairUnframe.Label.check
end Integration9_9.TM2PairUnframe.Label.check
namespace Integration9_9.TM2PairUnframe.Label.clearCounter
end Integration9_9.TM2PairUnframe.Label.clearCounter
namespace Integration9_9.TM2PairUnframe.Label.clearRev
end Integration9_9.TM2PairUnframe.Label.clearRev
namespace Integration9_9.TM2PairUnframe.Label.consume
end Integration9_9.TM2PairUnframe.Label.consume
namespace Integration9_9.TM2PairUnframe.Label.dec
end Integration9_9.TM2PairUnframe.Label.dec
namespace Integration9_9.TM2PairUnframe.Label.drain
end Integration9_9.TM2PairUnframe.Label.drain
namespace Integration9_9.TM2PairUnframe.Label.finish
end Integration9_9.TM2PairUnframe.Label.finish
namespace Integration9_9.TM2PairUnframe.Label.read
end Integration9_9.TM2PairUnframe.Label.read
namespace Integration9_9.TM2PairUnframe.Label.revDec
end Integration9_9.TM2PairUnframe.Label.revDec
namespace Integration9_9.TM2PairUnframe.Label.revOut
end Integration9_9.TM2PairUnframe.Label.revOut
namespace Integration9_9.TM2PairUnframe.Label.revPrefix
end Integration9_9.TM2PairUnframe.Label.revPrefix
namespace Integration9_9.TM2PairUnframe.Stack
end Integration9_9.TM2PairUnframe.Stack
namespace Integration9_9.TM2PairUnframe.Stack.counter
end Integration9_9.TM2PairUnframe.Stack.counter
namespace Integration9_9.TM2PairUnframe.Stack.input
end Integration9_9.TM2PairUnframe.Stack.input
namespace Integration9_9.TM2PairUnframe.Stack.outRev
end Integration9_9.TM2PairUnframe.Stack.outRev
namespace Integration9_9.TM2PairUnframe.Stack.output
end Integration9_9.TM2PairUnframe.Stack.output
namespace Integration9_9.TM2PairUnframe.Stack.rev
end Integration9_9.TM2PairUnframe.Stack.rev
namespace Integration9_9.TM2PairUnframe.addPair
end Integration9_9.TM2PairUnframe.addPair
namespace Integration9_9.TM2PairUnframe.frameTime
end Integration9_9.TM2PairUnframe.frameTime
namespace Integration9_9.TM2PairUnframe.instDecidableEqLabel
end Integration9_9.TM2PairUnframe.instDecidableEqLabel
namespace Integration9_9.TM2PairUnframe.instDecidableEqLabel.decEq
end Integration9_9.TM2PairUnframe.instDecidableEqLabel.decEq
namespace Integration9_9.TM2PairUnframe.instFintypeLabel
end Integration9_9.TM2PairUnframe.instFintypeLabel
namespace Integration9_9.TM2PairUnframe.next
end Integration9_9.TM2PairUnframe.next
namespace Integration9_9.TM2PairUnframe.readFrame
end Integration9_9.TM2PairUnframe.readFrame
namespace Integration9_9.TM2PairUnframe.relax
end Integration9_9.TM2PairUnframe.relax
namespace Integration9_9.TM2PairUnframe.revLabel
end Integration9_9.TM2PairUnframe.revLabel
namespace Integration9_9.TM2PairUnframe.revNext
end Integration9_9.TM2PairUnframe.revNext
namespace Integration9_9.TM2PairUnframe.singleStep
end Integration9_9.TM2PairUnframe.singleStep
namespace Integration9_9.TM2PairUnframe.unpack
end Integration9_9.TM2PairUnframe.unpack
namespace Integration9_9.TM2Simulation
end Integration9_9.TM2Simulation
namespace Integration9_9.TM2Simulation.ControlLens
end Integration9_9.TM2Simulation.ControlLens
namespace Integration9_9.TM2Simulation.ControlLens.mk
end Integration9_9.TM2Simulation.ControlLens.mk
namespace Integration9_9.TM2Simulation.singleStack
end Integration9_9.TM2Simulation.singleStack
namespace Integration9_9.TM2Simulation.statement
end Integration9_9.TM2Simulation.statement
namespace Integration9_9.TM2Simulation.statement.match_1
end Integration9_9.TM2Simulation.statement.match_1
namespace Integration9_9.TM2Simulation.statement.match_3
end Integration9_9.TM2Simulation.statement.match_3
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeFiniteDraw
open AFT AFT.RationalNumerics AFT.BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeFiniteSeries TM2NativeRootGroupProfiles
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h312 (q : ℚ) : _root_.Integration9_9.TM2NativeFiniteDraw.clipped q=_root_.AFT.RationalAcceptanceCoin.clipped q := by
  unfold _root_.Integration9_9.TM2NativeFiniteDraw.clipped _root_.AFT.RationalAcceptanceCoin.clipped
  split_ifs with h0 h1
  · rw [max_eq_right h0.le,min_eq_right (by norm_num)]
  · rw [max_eq_left (le_of_not_gt h0),min_eq_right h1.le]
  · rw [max_eq_left (le_of_not_gt h0),min_eq_left (le_of_not_gt h1)]
open _root_.P2Mba49f952 renaming h312 → _p2mH312
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h313 (bits : ℕ) (word : Fin bits → Fin 2) :
    List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i))=(_root_.AFT.BinaryArithmetic.readBitTape bits word).digits := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
    simp only [List.ofFn_succ,_root_.AFT.BinaryArithmetic.readBitTape,ih]
    rfl
open _root_.P2Mba49f952 renaming h313 → _p2mH313
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h310 (input : _root_.AFT.BinaryArithmetic.RationalBits) (bits : ℕ) (word : Fin bits → Fin 2) :
    _root_.Integration9_9.TM2NativeFiniteDraw.acceptance (input.decode,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=(_root_.AFT.BinaryArithmetic.binaryAcceptance input bits word).value := by
  have hb := _root_.AFT.BinaryArithmetic.subtract_borrow (_root_.AFT.BinaryArithmetic.readBitTape bits word).digits (input.clipUnit.data.dyadicFloor bits).digits
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.dyadicFloor_value,_p2mH12] at hb
  simp only [_root_.Integration9_9.TM2NativeFiniteDraw.acceptance,_root_.Integration9_9.TM2NativeFiniteDraw.tapeValue,_root_.Integration9_9.TM2NativeFiniteDraw.dyadicFloor,_root_.Integration9_9.TM2NativeFiniteDraw.ticks,List.length_map,_p2mH312,_p2mH313,
    _p2mH34,_root_.AFT.BinaryArithmetic.binaryAcceptance,hb]
open _root_.P2Mba49f952 renaming h310 → _p2mH310
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h311 (counts : List ℕ) (ticket : ℕ) : _root_.Integration9_9.TM2NativeFiniteDraw.bucket (counts,ticket)=_root_.AFT.FiniteTicketSampler.bucket counts ticket := by
  induction counts generalizing ticket with
  | nil => rfl
  | cons head tail ih =>
    simp only [_root_.Integration9_9.TM2NativeFiniteDraw.bucket,List.length_cons,List.range_succ_eq_map,List.findIdx_cons,List.take_succ_cons,List.take_zero,List.sum_cons,List.sum_nil,Nat.add_zero]
    by_cases h : ticket<head
    · simp only [h,decide_true,Bool.cond_true,_root_.AFT.FiniteTicketSampler.bucket,ite_true]
    · simp only [h,decide_false,Bool.cond_false,List.findIdx_map,Function.comp_def,_root_.AFT.FiniteTicketSampler.bucket,ite_false]
      have he : (fun i => decide (ticket<head+(tail.take (i+1)).sum))=
          (fun i => decide (ticket-head<(tail.take (i+1)).sum)) := by
        funext i
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
      simp only [he]
      change _root_.Integration9_9.TM2NativeFiniteDraw.bucket (tail,ticket-head)+1=1+_root_.AFT.FiniteTicketSampler.bucket tail (ticket-head)
      rw [ih,Nat.add_comm]
open _root_.P2Mba49f952 renaming h311 → _p2mH311
end Integration9_9.TM2NativeFiniteDraw
open _root_.P2Mba49f952 renaming h310 → _p2mH310
open _root_.P2Mba49f952 renaming h311 → _p2mH311
open _root_.P2Mba49f952 renaming h312 → _p2mH312
open _root_.P2Mba49f952 renaming h313 → _p2mH313
end
open _root_.P2Mba49f952 renaming h310 → _p2mH310
open _root_.P2Mba49f952 renaming h311 → _p2mH311
open _root_.P2Mba49f952 renaming h312 → _p2mH312
open _root_.P2Mba49f952 renaming h313 → _p2mH313
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeTicketDraw
open AFT AFT.RationalNumerics AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeFiniteDraw TM2NativeFiniteSeries
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h419 (extra : ℕ) (xs : List ℕ) : _root_.Integration9_9.TM2NativeTicketDraw.supplement (extra,xs)=_root_.AFT.BinaryArithmetic.supplementFirst extra xs := by cases xs <;> rfl
open _root_.P2Mba49f952 renaming h419 → _p2mH419
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h420 (weights : List _root_.AFT.BinaryArithmetic.RationalBits) (ticks : List Unit)
    (hb : (weights.map (fun q => ⌊(2 : ℚ)^ticks.length*q.decode⌋₊)).sum≤2^ticks.length) :
    _root_.Integration9_9.TM2NativeTicketDraw.ticketTable (weights.map _root_.AFT.BinaryArithmetic.RationalBits.decode,ticks)=(_root_.AFT.BinaryArithmetic.ticketTable weights ticks.length).data.map _root_.AFT.BinaryArithmetic.value := by
  rw [_root_.AFT.BinaryArithmetic.ticketTable_value weights ticks.length hb]
  simp only [_root_.Integration9_9.TM2NativeTicketDraw.ticketTable,_p2mH419,_root_.Integration9_9.TM2NativeTicketDraw.floorTable,_root_.Integration9_9.TM2NativeFiniteDraw.dyadicFloor,_root_.Integration9_9.TM2NativeFiniteDraw.dyadicPower,_root_.Integration9_9.TM2NativeFiniteDraw.natSum,List.map_map,Function.comp_def]
open _root_.P2Mba49f952 renaming h420 → _p2mH420
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h418 {count : ℕ} (weights : Vector _root_.AFT.BinaryArithmetic.RationalBits (count+1))
    (hn : ∀ i,0≤(weights.get i).decode) (hm : ∑i,(weights.get i).decode=1)
    (bits : ℕ) (word : Fin bits → Fin 2) :
    _root_.Integration9_9.TM2NativeTicketDraw.current (List.ofFn (fun i => (weights.get i).decode),List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.AFT.BinaryArithmetic.binaryRationalDraw weights bits word).value := by
  have hb := _root_.AFT.RationalFiniteQuantization.floorTotal_le (fun i => (weights.get i).decode) hn hm (2^bits)
  simp only [_root_.AFT.RationalFiniteQuantization.floorTotal,_root_.AFT.RationalFiniteQuantization.floorCount,Nat.cast_pow,Nat.cast_ofNat] at hb
  have ht : _root_.Integration9_9.TM2NativeTicketDraw.ticketTable (List.ofFn (fun i => (weights.get i).decode),_root_.Integration9_9.TM2NativeFiniteDraw.ticks (List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i))))=
      (_root_.AFT.BinaryArithmetic.ticketTable (List.ofFn weights.get) bits).data.map _root_.AFT.BinaryArithmetic.value := by
    have hl : (_root_.Integration9_9.TM2NativeFiniteDraw.ticks (List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))).length=bits := by simp [_root_.Integration9_9.TM2NativeFiniteDraw.ticks]
    have hh := _p2mH420 (List.ofFn weights.get) (_root_.Integration9_9.TM2NativeFiniteDraw.ticks (List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i))))
      (by simpa only [hl,List.map_ofFn,List.sum_ofFn,Function.comp_def] using hb)
    simpa only [hl,List.map_ofFn,Function.comp_def] using hh
  rw [_root_.Integration9_9.TM2NativeTicketDraw.current,ht,_p2mH311]
  simp only [_root_.AFT.BinaryArithmetic.binaryRationalDraw,_root_.AFT.BinaryArithmetic.binaryBucket_value,_root_.Integration9_9.TM2NativeFiniteDraw.tapeValue,_p2mH313]
open _root_.P2Mba49f952 renaming h418 → _p2mH418
end Integration9_9.TM2NativeTicketDraw
open _root_.P2Mba49f952 renaming h418 → _p2mH418
open _root_.P2Mba49f952 renaming h419 → _p2mH419
open _root_.P2Mba49f952 renaming h420 → _p2mH420
end
open _root_.P2Mba49f952 renaming h418 → _p2mH418
open _root_.P2Mba49f952 renaming h419 → _p2mH419
open _root_.P2Mba49f952 renaming h420 → _p2mH420
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativePositiveDraw
open AFT AFT.RationalNumerics AFT.BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeRootGroupProfiles
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h335 (q : ℚ) : _root_.Integration9_9.TM2NativePositiveDraw.positive q=max 0 q := by
  by_cases h : q<0
  · simp only [_root_.Integration9_9.TM2NativePositiveDraw.positive,h,ite_true,max_eq_left h.le]
  · simp only [_root_.Integration9_9.TM2NativePositiveDraw.positive,h,ite_false,max_eq_right (le_of_not_gt h)]
open _root_.P2Mba49f952 renaming h335 → _p2mH335
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h334 {count : ℕ} (raw : Fin (count+1) → ℚ) :
    _root_.Integration9_9.TM2NativePositiveDraw.normalize (List.ofFn raw)=List.ofFn (_root_.AFT.RationalNumerics.positiveWeightProgram raw) := by
  have ht : _root_.Integration9_9.TM2NativePositiveDraw.total (List.ofFn raw)=_root_.AFT.RationalNumerics.positiveNormalizerProgram raw := by
    simp only [_root_.Integration9_9.TM2NativePositiveDraw.total,_root_.Integration9_9.TM2NativePositiveDraw.clipped,List.map_ofFn,List.sum_ofFn,_p2mH335,_root_.AFT.RationalNumerics.positiveNormalizerProgram,_root_.AFT.RationalNumerics.positivePartProgram,Function.comp_def]
  simp only [_root_.Integration9_9.TM2NativePositiveDraw.normalize,ht]
  by_cases h : _root_.AFT.RationalNumerics.positiveNormalizerProgram raw=0
  · simp only [h,ite_true,List.length_ofFn]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      change (if i=0 then (1 : ℚ) else 0)=_root_.AFT.RationalNumerics.positiveWeightProgram raw ⟨i,by simpa using hj⟩
      simp only [_root_.AFT.RationalNumerics.positiveWeightProgram,h,ite_true,Fin.ext_iff,Fin.val_zero]
  · simp only [h,ite_false,_root_.Integration9_9.TM2NativePositiveDraw.clipped,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [_root_.AFT.RationalNumerics.positiveWeightProgram,h,ite_false,_root_.AFT.RationalNumerics.positivePartProgram,_p2mH335,Function.comp_def]
open _root_.P2Mba49f952 renaming h334 → _p2mH334
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h333 {count : ℕ} (raw : Vector _root_.AFT.BinaryArithmetic.RationalBits (count+1)) :
    _root_.Integration9_9.TM2NativePositiveDraw.normalize (List.ofFn (fun i => (raw.get i).decode))=
      List.ofFn (fun i => ((_root_.AFT.BinaryArithmetic.RationalBits.binaryPositiveNormalize raw).data.get i).decode) := by
  rw [_p2mH334]
  simp only [_root_.AFT.BinaryArithmetic.RationalBits.binaryPositiveNormalize_value]
open _root_.P2Mba49f952 renaming h333 → _p2mH333
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h332 {count : ℕ} (raw : Vector _root_.AFT.BinaryArithmetic.RationalBits (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) :
    _root_.Integration9_9.TM2NativePositiveDraw.current (List.ofFn (fun i => (raw.get i).decode),List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.AFT.BinaryArithmetic.binaryPositiveDraw raw bits word).value := by
  rw [_root_.Integration9_9.TM2NativePositiveDraw.current,_p2mH333]
  have hn (i) : 0≤((_root_.AFT.BinaryArithmetic.RationalBits.binaryPositiveNormalize raw).data.get i).decode := by
    rw [_root_.AFT.BinaryArithmetic.RationalBits.binaryPositiveNormalize_value]
    exact _root_.AFT.RationalNumerics.positiveWeightProgram_nonneg _ i
  have hm : ∑i,((_root_.AFT.BinaryArithmetic.RationalBits.binaryPositiveNormalize raw).data.get i).decode=1 := by
    simpa only [_root_.AFT.BinaryArithmetic.RationalBits.binaryPositiveNormalize_value] using _root_.AFT.RationalNumerics.positiveWeightProgram_sum (fun i => (raw.get i).decode)
  rw [_p2mH418 _ hn hm]
  simp only [_root_.AFT.BinaryArithmetic.binaryPositiveDraw,_root_.AFT.BinaryArithmetic.binaryRationalDraw_cast,_root_.AFT.BinaryArithmetic.addCounter_value]
open _root_.P2Mba49f952 renaming h332 → _p2mH332
end Integration9_9.TM2NativePositiveDraw
open _root_.P2Mba49f952 renaming h332 → _p2mH332
open _root_.P2Mba49f952 renaming h333 → _p2mH333
open _root_.P2Mba49f952 renaming h334 → _p2mH334
open _root_.P2Mba49f952 renaming h335 → _p2mH335
end
open _root_.P2Mba49f952 renaming h332 → _p2mH332
open _root_.P2Mba49f952 renaming h333 → _p2mH333
open _root_.P2Mba49f952 renaming h334 → _p2mH334
open _root_.P2Mba49f952 renaming h335 → _p2mH335
namespace AFT.BinaryArithmetic.binaryUniformDrawPolynomial
end AFT.BinaryArithmetic.binaryUniformDrawPolynomial
namespace AFT.BinaryArithmetic.binaryUniformDrawWork
end AFT.BinaryArithmetic.binaryUniformDrawWork
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeArrayDraw
open AFT AFT.BinaryArithmetic CurrentAFT CurrentProbabilityArrayDraw
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h227 (count : ℕ) (hc : 0<count) (table : _root_.CurrentAFT.CurrentProbabilityArrayDraw.ProbabilityArray count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) :
    _root_.Integration9_9.TM2NativeTicketDraw.current (List.ofFn (fun i => (table.data.get i).decode),List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.CurrentAFT.CurrentProbabilityArrayDraw.positiveDraw count hc table bits word).value.val := by
  cases count with
  | zero => omega
  | succ count =>
    rw [_p2mH418 table.data table.nonneg table.mass]
    simp only [_root_.CurrentAFT.CurrentProbabilityArrayDraw.positiveDraw,_root_.CurrentAFT.CurrentProbabilityArrayDraw.draw,_root_.AFT.BinaryArithmetic.binaryRationalDraw_cast]
open _root_.P2Mba49f952 renaming h227 → _p2mH227
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h226 (count : ℕ) [NeZero count] (raw : Vector _root_.AFT.BinaryArithmetic.RationalBits count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) :
    _root_.Integration9_9.TM2NativePositiveDraw.current (List.ofFn (fun i => (raw.get i).decode),List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.AFT.BinaryArithmetic.binaryPositiveFinDraw raw bits word).value := by
  cases count with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ count => exact _p2mH332 raw bits word
open _root_.P2Mba49f952 renaming h226 → _p2mH226
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h228 (xs : List Unit) (hc : 0<xs.length) (bits : ℕ)
    (word : Fin (bits+xs.length+1) → Fin 2) :
    _root_.Integration9_9.TM2NativeArrayDraw.uniform (xs,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.AFT.BinaryArithmetic.binaryUniformDraw xs.length hc bits word).value.val := by
  letI : NeZero xs.length := ⟨Nat.ne_zero_of_lt hc⟩
  have h:=_p2mH226 xs.length
    (Vector.replicate xs.length (_root_.AFT.BinaryArithmetic.RationalBits.inverse (_root_.AFT.BinaryArithmetic.RationalBits.ofCounter xs.length).data).data) bits word
  have he : xs.map (fun _ => (xs.length : ℚ)⁻¹)=
      List.ofFn (fun i : Fin xs.length => ((Vector.replicate xs.length
        (_root_.AFT.BinaryArithmetic.RationalBits.inverse (_root_.AFT.BinaryArithmetic.RationalBits.ofCounter xs.length).data).data).get i).decode) := by
    simp only [Vector.get_replicate,_root_.AFT.BinaryArithmetic.RationalBits.inverse_value,_root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value,List.ofFn_const]
    apply List.ext_getElem
    · simp
    · intros; simp
  simpa only [_root_.Integration9_9.TM2NativeArrayDraw.uniform,he,_root_.AFT.BinaryArithmetic.binaryUniformDraw] using h
open _root_.P2Mba49f952 renaming h228 → _p2mH228
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h229 (xs : List Unit) (count : ℕ) (h : xs.length=count) (hc : 0<count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) :
    _root_.Integration9_9.TM2NativeArrayDraw.uniform (xs,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=(_root_.AFT.BinaryArithmetic.binaryUniformDraw count hc bits word).value.val := by
  subst count
  exact _p2mH228 xs hc bits word
open _root_.P2Mba49f952 renaming h229 → _p2mH229
end Integration9_9.TM2NativeArrayDraw
open _root_.P2Mba49f952 renaming h226 → _p2mH226
open _root_.P2Mba49f952 renaming h227 → _p2mH227
open _root_.P2Mba49f952 renaming h228 → _p2mH228
open _root_.P2Mba49f952 renaming h229 → _p2mH229
end
open _root_.P2Mba49f952 renaming h226 → _p2mH226
open _root_.P2Mba49f952 renaming h227 → _p2mH227
open _root_.P2Mba49f952 renaming h228 → _p2mH228
open _root_.P2Mba49f952 renaming h229 → _p2mH229
namespace CurrentAFT.ActualPublicLegCharge.activationLaw
end CurrentAFT.ActualPublicLegCharge.activationLaw
namespace CurrentAFT.CurrentActivationDraw
end CurrentAFT.CurrentActivationDraw
namespace CurrentAFT.CurrentActivationDraw.approximateLaw
end CurrentAFT.CurrentActivationDraw.approximateLaw
namespace CurrentAFT.CurrentActivationDraw.table
end CurrentAFT.CurrentActivationDraw.table
namespace CurrentAFT.CurrentProbabilityArrayDraw.law
end CurrentAFT.CurrentProbabilityArrayDraw.law
namespace CurrentAFT.CurrentSafeDraw
end CurrentAFT.CurrentSafeDraw
namespace CurrentAFT.CurrentSafeDraw.draw
end CurrentAFT.CurrentSafeDraw.draw
namespace CurrentAFT.CurrentSafeDraw.law
end CurrentAFT.CurrentSafeDraw.law
namespace CurrentAFT.CurrentSafeDraw.workBound
end CurrentAFT.CurrentSafeDraw.workBound
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeReferenceDraw
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeRootGroupProfiles
open scoped BigOperators
attribute [local irreducible] TM2NativePrime.modulus TM2NativePrime.upperSlots
  RationalProposalProgram.primary RationalProposalProgram.center LocalPairProgram.activationApprox
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h346 (xs : List Unit) : _root_.Integration9_9.TM2NativeBody.margin xs=(_root_.CurrentAFT.CurrentReferenceDraw.counts xs.length).margin := by
  rw [(_root_.CurrentAFT.CurrentReferenceDraw.counts_values xs.length).2.1,_root_.Integration9_9.TM2NativeBody.margin_value]
  rfl
open _root_.P2Mba49f952 renaming h346 → _p2mH346
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h349 (xs : List Unit) : _root_.Integration9_9.TM2NativeReferenceDraw.safeCount xs=(_root_.CurrentAFT.CurrentReferenceDraw.counts xs.length).safe := by
  rw [_root_.Integration9_9.TM2NativeReferenceDraw.safeCount,_root_.Integration9_9.TM2NativePrime.modulus_value,_p2mH346]
  rw [(_root_.CurrentAFT.CurrentReferenceDraw.counts_values xs.length).2.2,(_root_.CurrentAFT.CurrentReferenceDraw.counts_values xs.length).2.1]
open _root_.P2Mba49f952 renaming h349 → _p2mH349
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h351 (xs : List Unit) : (_root_.Integration9_9.TM2NativeReferenceDraw.safeTicks xs).length=(_root_.CurrentAFT.CurrentReferenceDraw.counts xs.length).safe := by
  rw [_root_.Integration9_9.TM2NativeReferenceDraw.safeTicks,List.length_take,_root_.Integration9_9.TM2NativeBodyKernel.paletteTicks_length,←_p2mH349]
  unfold _root_.Integration9_9.TM2NativeReferenceDraw.safeCount
  rw [_root_.Integration9_9.TM2NativePrime.modulus_value,Nat.min_eq_left (Nat.sub_le _ _)]
open _root_.P2Mba49f952 renaming h351 → _p2mH351
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h348 (x : _root_.Integration9_9.TM2NativeReferenceDraw.Meta) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length) :
    _root_.Integration9_9.TM2NativeReferenceDraw.primaryTable x=List.ofFn (fun i => (cache.primary.data.get i).decode) := by
  have hc : (_root_.Integration9_9.TM2NativeBodyKernel.paletteTicks x.1).length=(_root_.CurrentAFT.PublicParameterProgram.modulus x.1.length).count := by
    rw [_root_.Integration9_9.TM2NativeBodyKernel.paletteTicks_length,_root_.CurrentAFT.PublicParameterProgram.modulus_value]
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeReferenceDraw.primaryTable,_root_.Integration9_9.TM2NativeAnchor.indices,List.length_map,List.length_range,List.length_ofFn,hc]
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeReferenceDraw.primaryTable,_root_.Integration9_9.TM2NativeAnchor.indices,List.getElem_map,List.getElem_range,List.getElem_ofFn,cache.primary_value,_root_.Integration9_9.TM2NativeRootGroupProfiles.primary]
open _root_.P2Mba49f952 renaming h348 → _p2mH348
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h345 (x : _root_.Integration9_9.TM2NativeReferenceDraw.Meta) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length) :
    _root_.Integration9_9.TM2NativeReferenceDraw.bodyTable x=List.ofFn (fun i => (cache.body.data.get i).decode) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeReferenceDraw.bodyTable,List.length_map,List.length_range,List.length_ofFn,_p2mH351]
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeReferenceDraw.bodyTable,List.getElem_map,List.getElem_range,List.getElem_ofFn,cache.body_value,
      _root_.CurrentAFT.CurrentReferenceDraw.bodyEquiv_value,_root_.Integration9_9.TM2NativeRootGroupProfiles.center,_p2mH346]
open _root_.P2Mba49f952 renaming h345 → _p2mH345
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h347 (x : _root_.Integration9_9.TM2NativeReferenceDraw.Meta) (bits : ℕ) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length)
    (word : Fin (bits+(_root_.CurrentAFT.PublicParameterProgram.modulus x.1.length).count+1) → Fin 2) :
    _root_.Integration9_9.TM2NativeReferenceDraw.primaryDraw (x,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.CurrentAFT.CurrentReferenceDraw.primaryDraw x.1.length x.2.length bits cache word).value.val := by
  rw [_root_.Integration9_9.TM2NativeReferenceDraw.primaryDraw,_p2mH348 x cache,_p2mH227 _ (_root_.CurrentAFT.CurrentReferenceDraw.colors_positive _) _ bits word]
  rfl
open _root_.P2Mba49f952 renaming h347 → _p2mH347
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h344 (x : _root_.Integration9_9.TM2NativeReferenceDraw.Meta) (bits : ℕ) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length)
    (word : Fin (bits+(_root_.CurrentAFT.CurrentReferenceDraw.counts x.1.length).safe+1) → Fin 2) :
    _root_.Integration9_9.TM2NativeReferenceDraw.bodyDraw (x,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.CurrentAFT.CurrentReferenceDraw.bodyDraw x.1.length x.2.length bits cache word).value.val.val := by
  rw [_root_.Integration9_9.TM2NativeReferenceDraw.bodyDraw,_p2mH345 x cache,_p2mH227 _ (_root_.CurrentAFT.CurrentReferenceDraw.safe_positive _) _ bits word]
  rw [_p2mH183,_root_.CurrentAFT.CurrentReferenceDraw.bodyEquiv_value,_p2mH346]
open _root_.P2Mba49f952 renaming h344 → _p2mH344
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h350 (xs : List Unit) (bits : ℕ) (word : _root_.CurrentAFT.CurrentSafeDraw.Tape xs.length bits) :
    _root_.Integration9_9.TM2NativeReferenceDraw.safeDraw (xs,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=(_root_.CurrentAFT.CurrentSafeDraw.draw xs.length bits word).value.val := by
  rw [_root_.Integration9_9.TM2NativeReferenceDraw.safeDraw,_p2mH229 (_root_.Integration9_9.TM2NativeReferenceDraw.safeTicks xs) _ (_p2mH351 xs)
    (_root_.CurrentAFT.CurrentReferenceDraw.safe_positive _) bits word,_p2mH346,
    _p2mH184,_root_.CurrentAFT.CurrentReferenceDraw.bodyEquiv_value]
open _root_.P2Mba49f952 renaming h350 → _p2mH350
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h343 (x : _root_.Integration9_9.TM2NativeReferenceDraw.Meta) (bits : ℕ) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length)
    (word : Fin (bits+2+1) → Fin 2) :
    _root_.Integration9_9.TM2NativeReferenceDraw.activationDraw (x,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.CurrentAFT.CurrentActivationDraw.draw x.1.length x.2.length bits cache word).value := by
  have ha : _root_.Integration9_9.TM2NativeActivation.current x=cache.activation.decode := by
    rw [cache.activation_value,_root_.Integration9_9.TM2NativeActivation.current_value,_root_.CurrentAFT.BinaryActivationProgram.current_value]
  have ht : [1-_root_.Integration9_9.TM2NativeActivation.current x,_root_.Integration9_9.TM2NativeActivation.current x]=
      List.ofFn (fun i => ((_root_.CurrentAFT.CurrentActivationDraw.table x.1.length x.2.length cache).value.data.get i).decode) := by
    simp only [ha,_p2mH85,List.ofFn_succ,List.ofFn_zero]
    norm_num
  rw [_root_.Integration9_9.TM2NativeReferenceDraw.activationDraw,ht,_p2mH227 _ (by decide) _ bits word]
  change decide ((_root_.CurrentAFT.CurrentProbabilityArrayDraw.positiveDraw 2 (by decide)
    (_root_.CurrentAFT.CurrentActivationDraw.table x.1.length x.2.length cache).value bits word).value.val=1)=
    finTwoEquiv (_root_.CurrentAFT.CurrentProbabilityArrayDraw.positiveDraw 2 (by decide)
    (_root_.CurrentAFT.CurrentActivationDraw.table x.1.length x.2.length cache).value bits word).value
  generalize (_root_.CurrentAFT.CurrentProbabilityArrayDraw.positiveDraw 2 (by decide)
    (_root_.CurrentAFT.CurrentActivationDraw.table x.1.length x.2.length cache).value bits word).value=i
  fin_cases i <;> rfl
open _root_.P2Mba49f952 renaming h343 → _p2mH343
end Integration9_9.TM2NativeReferenceDraw
open _root_.P2Mba49f952 renaming h343 → _p2mH343
open _root_.P2Mba49f952 renaming h344 → _p2mH344
open _root_.P2Mba49f952 renaming h345 → _p2mH345
open _root_.P2Mba49f952 renaming h346 → _p2mH346
open _root_.P2Mba49f952 renaming h347 → _p2mH347
open _root_.P2Mba49f952 renaming h348 → _p2mH348
open _root_.P2Mba49f952 renaming h349 → _p2mH349
open _root_.P2Mba49f952 renaming h350 → _p2mH350
open _root_.P2Mba49f952 renaming h351 → _p2mH351
end
open _root_.P2Mba49f952 renaming h343 → _p2mH343
open _root_.P2Mba49f952 renaming h344 → _p2mH344
open _root_.P2Mba49f952 renaming h345 → _p2mH345
open _root_.P2Mba49f952 renaming h346 → _p2mH346
open _root_.P2Mba49f952 renaming h347 → _p2mH347
open _root_.P2Mba49f952 renaming h348 → _p2mH348
open _root_.P2Mba49f952 renaming h349 → _p2mH349
open _root_.P2Mba49f952 renaming h350 → _p2mH350
open _root_.P2Mba49f952 renaming h351 → _p2mH351
namespace CurrentAFT.CurrentPublicSeedDraw
end CurrentAFT.CurrentPublicSeedDraw
namespace CurrentAFT.CurrentPublicSeedDraw.draw
end CurrentAFT.CurrentPublicSeedDraw.draw
namespace CurrentAFT.CurrentPublicSeedDraw.law
end CurrentAFT.CurrentPublicSeedDraw.law
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativePublicSeed
open AFT AFT.RationalNumerics AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeRootGroupGaussian
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h340 (xs : List Unit) (bits : ℕ) (word : _root_.CurrentAFT.CurrentAnchorIndexDraw.Tape xs.length bits) :
    _root_.Integration9_9.TM2NativePublicSeed.anchorDraw (xs,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=(_root_.CurrentAFT.CurrentAnchorIndexDraw.draw xs.length bits word).value.val := by
  have he : (_root_.Integration9_9.TM2NativeProfile.widthTicks xs).length=(_root_.CurrentAFT.CurrentAnchorIndexDraw.width xs.length).count := by
    rw [_root_.Integration9_9.TM2NativeProfile.widthTicks_length,_root_.CurrentAFT.CurrentAnchorIndexDraw.width_value]
    simp only [_root_.CurrentAFT.Parameters.anchorWidth,_root_.CurrentAFT.Parameters.scale,_root_.CurrentAFT.Parameters.base,←pow_mul,Nat.reduceMul]
  rw [_root_.Integration9_9.TM2NativePublicSeed.anchorDraw,_p2mH229 _ _ he (_root_.CurrentAFT.CurrentAnchorIndexDraw.width_positive _) bits word]
  rfl
open _root_.P2Mba49f952 renaming h340 → _p2mH340
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h342 (x : _root_.Integration9_9.TM2NativePublicSeed.Meta) (word : _root_.CurrentAFT.CurrentPublicSeedDraw.EdgeTape x.1.length x.2.length) :
    _root_.Integration9_9.TM2NativePublicSeed.edgeDraw (x,List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.CurrentAFT.CurrentEdgeDrawProgram.draw x.1.length x.2.length word).value.val := by
  have he : (_root_.Integration9_9.TM2NativeProfile.edgeTicks x.1).length=_root_.CurrentAFT.DiffuseProfiles.edgeCutoff x.1.length := by
    rw [_root_.Integration9_9.TM2NativeProfile.edgeTicks_length]
    rfl
  have ht : _root_.Integration9_9.TM2NativeRootGroupGaussian.gaussian true (x.1,()::x.2)=List.ofFn (fun i =>
      ((_root_.CurrentAFT.CurrentGaussianBits.table x.1.length (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff x.1.length) (x.2.length+1)).data.get i).decode) := by
    rw [_root_.Integration9_9.TM2NativeRootGroupGaussian.gaussian_eq]
    simp only [_root_.Integration9_9.TM2NativeRootGroupGaussian.cutoff,ite_true,_root_.Integration9_9.TM2NativeProfile.gaussianList,List.length_cons,_root_.CurrentAFT.CurrentGaussianBits.table_value]
    rfl
  have hn (i) : 0≤((_root_.CurrentAFT.CurrentGaussianBits.table x.1.length (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff x.1.length) (x.2.length+1)).data.get i).decode := by
    rw [_root_.CurrentAFT.CurrentGaussianBits.table_value]
    exact _root_.AFT.RationalNumerics.windowGaussianWeights_nonneg _ _ _ _
  have hm : ∑i,((_root_.CurrentAFT.CurrentGaussianBits.table x.1.length (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff x.1.length) (x.2.length+1)).data.get i).decode=1 := by
    simp only [_root_.CurrentAFT.CurrentGaussianBits.table_value]
    exact _root_.AFT.RationalNumerics.windowGaussianWeights_sum _ _ _
  rw [_root_.Integration9_9.TM2NativePublicSeed.edgeDraw,ht,_p2mH418 _ hn hm,he]
  rw [_p2mH146,←_p2mH185]
  change _=(_root_.AFT.BinaryArithmetic.integerDifference _ _).value
  rw [_root_.AFT.BinaryArithmetic.integerDifference_value]
open _root_.P2Mba49f952 renaming h342 → _p2mH342
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h341 (x : _root_.Integration9_9.TM2NativePublicSeed.Meta) (ticks : List Unit) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length)
    (word : _root_.CurrentAFT.CurrentPublicSeedDraw.Tape x.1.length ticks.length) :
    _root_.Integration9_9.TM2NativePublicSeed.current ((x,ticks),_root_.Integration9_9.TM2NativePublicSeed.tapeData word)=_root_.Integration9_9.TM2NativePublicSeed.seedData (_root_.CurrentAFT.CurrentPublicSeedDraw.draw x.1.length x.2.length ticks.length cache word).value := by
  simp only [_root_.Integration9_9.TM2NativePublicSeed.current,_root_.Integration9_9.TM2NativePublicSeed.tapeData,_p2mH343 x ticks.length cache,
    _p2mH340,_p2mH342,_root_.Integration9_9.TM2NativePublicSeed.seedData,_root_.CurrentAFT.CurrentPublicSeedDraw.draw]
open _root_.P2Mba49f952 renaming h341 → _p2mH341
end Integration9_9.TM2NativePublicSeed
open _root_.P2Mba49f952 renaming h340 → _p2mH340
open _root_.P2Mba49f952 renaming h341 → _p2mH341
open _root_.P2Mba49f952 renaming h342 → _p2mH342
end
open _root_.P2Mba49f952 renaming h340 → _p2mH340
open _root_.P2Mba49f952 renaming h341 → _p2mH341
open _root_.P2Mba49f952 renaming h342 → _p2mH342
namespace AFT.BinaryArithmetic.binaryPermutationRows
end AFT.BinaryArithmetic.binaryPermutationRows
namespace AFT.BinaryArithmetic.binaryPermutationRows.match_1
end AFT.BinaryArithmetic.binaryPermutationRows.match_1
namespace AFT.BinaryArithmetic.insertionImage
end AFT.BinaryArithmetic.insertionImage
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativePermutationRows
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h330 (word : List Bool) (words : List (List Bool)) : _root_.Integration9_9.TM2NativePermutationRows.current (word::words)=_root_.Integration9_9.TM2NativePermutationRows.step (_root_.Integration9_9.TM2NativePermutationRows.current words) word := by
  simp only [_root_.Integration9_9.TM2NativePermutationRows.current,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
open _root_.P2Mba49f952 renaming h330 → _p2mH330
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h329 (rows : List ℕ) (bits : ℕ) (word : Fin bits→Fin 2) :
    _root_.Integration9_9.TM2NativePermutationRows.choice (rows,List.ofFn (fun i=>_root_.AFT.BinaryArithmetic.digitBoolean (word i)))=(_root_.AFT.PermutationProgram.choiceDraw rows.length bits word).val := by
  let weights := Vector.replicate (rows.length+1) (_root_.AFT.BinaryArithmetic.RationalBits.inverse (_root_.AFT.BinaryArithmetic.RationalBits.ofCounter (rows.length+1)).data).data
  have hv : (fun i=> (weights.get i).decode)=_root_.AFT.PermutationProgram.choiceWeight rows.length := by
    funext i
    simp only [weights,Vector.get_replicate,_root_.AFT.BinaryArithmetic.RationalBits.inverse_value,_root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value,_root_.AFT.PermutationProgram.choiceWeight]
  have he : (0::rows).map (fun _ => ((rows.length+1 : ℕ) : ℚ)⁻¹)=List.ofFn (fun i => (weights.get i).decode) := by
    rw [hv]
    simp only [List.map_const',List.length_cons]
    exact (List.ofFn_const _ _).symm
  have hn : ∀ i,0≤(weights.get i).decode := by
    intro i
    rw [congrFun hv i]
    exact _root_.AFT.PermutationProgram.choiceWeight_nonneg _ i
  have hm : ∑ i,(weights.get i).decode=1 := by rw [hv];exact _root_.AFT.PermutationProgram.choiceWeight_sum _
  rw [_root_.Integration9_9.TM2NativePermutationRows.choice,he,_p2mH418 weights hn hm,_root_.AFT.BinaryArithmetic.binaryRationalDraw_value weights hn hm]
  simp only [hv,_root_.AFT.PermutationProgram.choiceDraw]
open _root_.P2Mba49f952 renaming h329 → _p2mH329
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h331 (bits count : ℕ) (word : Fin count→Fin bits→Fin 2) :
    _root_.Integration9_9.TM2NativePermutationRows.current (List.ofFn (fun i => List.ofFn (fun j => _root_.AFT.BinaryArithmetic.digitBoolean (word i j))))=
      List.ofFn (fun i => (_root_.AFT.PermutationProgram.rows bits count word i).val) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.ofFn_succ,_p2mH330,ih]
    have hl : (List.ofFn (fun i => (_root_.AFT.PermutationProgram.rows bits count (Fin.tail word) i).val)).length=count := List.length_ofFn
    have hc:=_p2mH329 (List.ofFn (fun i => (_root_.AFT.PermutationProgram.rows bits count (Fin.tail word) i).val)) bits (word 0)
    rw [hl] at hc
    change _root_.Integration9_9.TM2NativePermutationRows.step (List.ofFn (fun i => (_root_.AFT.PermutationProgram.rows bits count (Fin.tail word) i).val))
      (List.ofFn (fun j => _root_.AFT.BinaryArithmetic.digitBoolean (word 0 j)))=_
    rw [_root_.Integration9_9.TM2NativePermutationRows.step,hc,hl]
    simp only [Nat.min_eq_left (Nat.le_of_lt_succ (_root_.AFT.PermutationProgram.choiceDraw count bits (word 0)).isLt),
      List.map_ofFn,List.ofFn_succ,_root_.AFT.PermutationProgram.rows,Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ]
    apply congrArg (List.cons (_root_.AFT.PermutationProgram.choiceDraw count bits (word 0)).val)
    apply congrArg List.ofFn
    funext i
    have hi := (_root_.AFT.PermutationProgram.rows bits count (Fin.tail word) i).isLt
    simp only [Function.comp_def,Nat.min_eq_left hi.le,Equiv.swap_apply_def,Fin.succ_ne_zero,ite_false]
    simp only [Fin.ext_iff,Fin.val_succ,apply_ite,Fin.val_zero]
    split_ifs <;> rfl
open _root_.P2Mba49f952 renaming h331 → _p2mH331
end Integration9_9.TM2NativePermutationRows
open _root_.P2Mba49f952 renaming h329 → _p2mH329
open _root_.P2Mba49f952 renaming h330 → _p2mH330
open _root_.P2Mba49f952 renaming h331 → _p2mH331
end
open _root_.P2Mba49f952 renaming h329 → _p2mH329
open _root_.P2Mba49f952 renaming h330 → _p2mH330
open _root_.P2Mba49f952 renaming h331 → _p2mH331
namespace CurrentAFT.CurrentPermutationDraw
end CurrentAFT.CurrentPermutationDraw
namespace CurrentAFT.CurrentPermutationDraw.CachedPermutation
end CurrentAFT.CurrentPermutationDraw.CachedPermutation
namespace CurrentAFT.CurrentPermutationDraw.CachedPermutation.mk
end CurrentAFT.CurrentPermutationDraw.CachedPermutation.mk
namespace CurrentAFT.CurrentPermutationDraw.inverseScan
end CurrentAFT.CurrentPermutationDraw.inverseScan
namespace CurrentAFT.CurrentPermutationDraw.inverseScan.match_1
end CurrentAFT.CurrentPermutationDraw.inverseScan.match_1
namespace CurrentAFT.CurrentPermutationDraw.inverseScanWork
end CurrentAFT.CurrentPermutationDraw.inverseScanWork
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativePermutationDraw
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h328 {α : Type} {rows columns : ℕ} (f : Fin (rows*columns) → α) (r : Fin rows) :
    ((List.ofFn f).drop (columns*r.val)).take columns=List.ofFn (fun c : Fin columns => f (finProdFinEquiv (r,c))) := by
  have hroom : columns*r.val+columns≤rows*columns := by
    calc
      columns*r.val+columns=(r.val+1)*columns := by ring
      _≤rows*columns := Nat.mul_le_mul_right columns r.isLt
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn];omega
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [finProdFinEquiv,Equiv.coe_fn_mk]
    omega
open _root_.P2Mba49f952 renaming h328 → Integration9_9.TM2NativePermutationDraw.slice_ofFn
open _root_.P2Mba49f952 renaming h328 → _p2mH328
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h325 (count bits : List Unit) (word : Fin (count.length*bits.length)→Fin 2) :
    _root_.Integration9_9.TM2NativePermutationDraw.grouped ((count,bits),List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      List.ofFn (fun i => List.ofFn (fun j => _root_.AFT.BinaryArithmetic.digitBoolean (word (finProdFinEquiv (i,j))))) := by
  have hr {α : Type} (n : ℕ) (f : ℕ→α) : (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
    apply List.ext_getElem
    · simp
    · intros;simp
  rw [_root_.Integration9_9.TM2NativePermutationDraw.grouped,hr]
  apply congrArg List.ofFn
  funext r
  exact _p2mH328 _ r
open _root_.P2Mba49f952 renaming h325 → _p2mH325
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h324 (count bits : List Unit) (word : Fin (count.length*bits.length)→Fin 2) :
    _root_.Integration9_9.TM2NativePermutationDraw.forward ((count,bits),List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      List.ofFn (fun i => (_root_.AFT.PermutationProgram.draw count.length bits.length word i).val) := by
  rw [_root_.Integration9_9.TM2NativePermutationDraw.forward,_p2mH325,_p2mH331]
  rfl
open _root_.P2Mba49f952 renaming h324 → _p2mH324
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h326 {count : ℕ} (p : Equiv.Perm (Fin count)) (target : Fin count) :
    _root_.Integration9_9.TM2NativePermutationDraw.inverseEntry (List.ofFn (fun i => (p i).val),target.val)=(p.symm target).val := by
  unfold _root_.Integration9_9.TM2NativePermutationDraw.inverseEntry
  rw [List.length_ofFn]
  apply (List.findIdx_eq (by simpa using (p.symm target).isLt)).mpr
  constructor
  · simp only [List.getElem_range,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,Equiv.apply_symm_apply,decide_true]
    change decide ((p (p.symm target)).val=target.val)=true
    simp
  · intro i hi
    have hib : i<count := hi.trans (p.symm target).isLt
    simp only [List.getElem_range,List.getElem?_ofFn,hib,dif_pos,Option.getD_some,decide_eq_false_iff_not]
    intro h
    have he : p ⟨i,hib⟩=target := Fin.ext h
    have hh : (⟨i,hib⟩ : Fin count)=p.symm target := p.apply_eq_iff_eq_symm_apply.mp he
    have hv:=congrArg Fin.val hh
    change i=(p.symm target).val at hv
    omega
open _root_.P2Mba49f952 renaming h326 → _p2mH326
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h327 {count : ℕ} (p : Equiv.Perm (Fin count)) :
    _root_.Integration9_9.TM2NativePermutationDraw.inverse (List.ofFn (fun i => (p i).val))=List.ofFn (fun i => (p.symm i).val) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativePermutationDraw.inverse,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativePermutationDraw.inverse,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact _p2mH326 p ⟨i,by simpa using hj⟩
open _root_.P2Mba49f952 renaming h327 → _p2mH327
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h322 (count bits : List Unit) (word : Fin (count.length*bits.length)→Fin 2) :
    _root_.Integration9_9.TM2NativePermutationDraw.current ((count,bits),List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      _root_.Integration9_9.TM2NativePermutationDraw.cacheData (_root_.CurrentAFT.CurrentPermutationDraw.draw count.length bits.length (Vector.ofFn word)).value := by
  simp only [_root_.Integration9_9.TM2NativePermutationDraw.current,_p2mH324,_p2mH327,_root_.Integration9_9.TM2NativePermutationDraw.cacheData,_p2mH174,
    _p2mH175]
  have h : (Vector.ofFn word).get=word := by funext i;exact Vector.get_ofFn _ _
  rw [h]
open _root_.P2Mba49f952 renaming h322 → _p2mH322
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h323 (count bits : List Unit) (n b : ℕ) (hc : count.length=n) (hb : bits.length=b)
    (word : Fin (n*b)→Fin 2) : _root_.Integration9_9.TM2NativePermutationDraw.current ((count,bits),List.ofFn (fun i => _root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      _root_.Integration9_9.TM2NativePermutationDraw.cacheData (_root_.CurrentAFT.CurrentPermutationDraw.draw n b (Vector.ofFn word)).value := by
  subst n
  subst b
  exact _p2mH322 count bits word
open _root_.P2Mba49f952 renaming h323 → _p2mH323
end Integration9_9.TM2NativePermutationDraw
open _root_.P2Mba49f952 renaming h322 → _p2mH322
open _root_.P2Mba49f952 renaming h323 → _p2mH323
open _root_.P2Mba49f952 renaming h324 → _p2mH324
open _root_.P2Mba49f952 renaming h325 → _p2mH325
open _root_.P2Mba49f952 renaming h326 → _p2mH326
open _root_.P2Mba49f952 renaming h327 → _p2mH327
open _root_.P2Mba49f952 renaming h328 → Integration9_9.TM2NativePermutationDraw.slice_ofFn
open _root_.P2Mba49f952 renaming h328 → _p2mH328
end
open _root_.P2Mba49f952 renaming h322 → _p2mH322
open _root_.P2Mba49f952 renaming h323 → _p2mH323
open _root_.P2Mba49f952 renaming h324 → _p2mH324
open _root_.P2Mba49f952 renaming h325 → _p2mH325
open _root_.P2Mba49f952 renaming h326 → _p2mH326
open _root_.P2Mba49f952 renaming h327 → _p2mH327
open _root_.P2Mba49f952 renaming h328 → Integration9_9.TM2NativePermutationDraw.slice_ofFn
open _root_.P2Mba49f952 renaming h328 → _p2mH328
namespace CurrentAFT.BinaryFullResponseCounts
end CurrentAFT.BinaryFullResponseCounts
namespace CurrentAFT.BinaryFullResponseCounts.Counts
end CurrentAFT.BinaryFullResponseCounts.Counts
namespace CurrentAFT.BinaryFullResponseCounts.Counts.mk
end CurrentAFT.BinaryFullResponseCounts.Counts.mk
namespace CurrentAFT.BinaryFullResponseCounts.current
end CurrentAFT.BinaryFullResponseCounts.current
namespace CurrentAFT.BinaryFullResponseCounts.workPolynomial
end CurrentAFT.BinaryFullResponseCounts.workPolynomial
namespace CurrentAFT.CurrentPreparedCoreProposal
end CurrentAFT.CurrentPreparedCoreProposal
namespace CurrentAFT.CurrentPreparedCoreProposal.law
end CurrentAFT.CurrentPreparedCoreProposal.law
namespace CurrentAFT.CurrentPreparedCoreProposal.preparePolynomial
end CurrentAFT.CurrentPreparedCoreProposal.preparePolynomial
namespace CurrentAFT.CurrentPreparedCoreProposal.workPolynomial
end CurrentAFT.CurrentPreparedCoreProposal.workPolynomial
namespace CurrentAFT.CurrentReferenceDraw.prepare
end CurrentAFT.CurrentReferenceDraw.prepare
namespace Integration9_9.TM2NativeFullResponseCounts
end Integration9_9.TM2NativeFullResponseCounts
namespace Integration9_9.TM2NativeFullResponseCounts.Kind
end Integration9_9.TM2NativeFullResponseCounts.Kind
namespace Integration9_9.TM2NativeFullResponseCounts.Kind.body
end Integration9_9.TM2NativeFullResponseCounts.Kind.body
namespace Integration9_9.TM2NativeFullResponseCounts.Kind.leg
end Integration9_9.TM2NativeFullResponseCounts.Kind.leg
namespace Integration9_9.TM2NativeFullResponseCounts.Kind.ordinary
end Integration9_9.TM2NativeFullResponseCounts.Kind.ordinary
namespace Integration9_9.TM2NativeFullResponseCounts.Kind.queue
end Integration9_9.TM2NativeFullResponseCounts.Kind.queue
namespace Integration9_9.TM2NativeFullResponseCounts.body
end Integration9_9.TM2NativeFullResponseCounts.body
namespace Integration9_9.TM2NativeFullResponseCounts.budget
end Integration9_9.TM2NativeFullResponseCounts.budget
namespace Integration9_9.TM2NativeFullResponseCounts.current
end Integration9_9.TM2NativeFullResponseCounts.current
namespace Integration9_9.TM2NativeFullResponseCounts.indices
end Integration9_9.TM2NativeFullResponseCounts.indices
namespace Integration9_9.TM2NativeFullResponseCounts.leg
end Integration9_9.TM2NativeFullResponseCounts.leg
namespace Integration9_9.TM2NativeFullResponseCounts.nativeValue
end Integration9_9.TM2NativeFullResponseCounts.nativeValue
namespace Integration9_9.TM2NativeFullResponseCounts.ordinary
end Integration9_9.TM2NativeFullResponseCounts.ordinary
namespace Integration9_9.TM2NativeFullResponseCounts.queue
end Integration9_9.TM2NativeFullResponseCounts.queue
namespace Integration9_9.TM2NativeFullResponseCounts.slots
end Integration9_9.TM2NativeFullResponseCounts.slots
namespace Integration9_9.TM2NativeFullResponseCounts.value
end Integration9_9.TM2NativeFullResponseCounts.value
namespace Integration9_9.TM2NativeFullResponseCounts.value.match_1
end Integration9_9.TM2NativeFullResponseCounts.value.match_1
namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeCoreProposal
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
attribute [local irreducible] CurrentProposalDimensions.current BinaryFullResponseCounts.current
  CurrentAFT.Parameters.legCount CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension
attribute [local irreducible] bodyTicks legTicks
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h266 (xs : List Unit) : (_root_.Integration9_9.TM2NativeCoreProposal.bodyTicks xs).length=(_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).body := by
  rw [_root_.Integration9_9.TM2NativeCoreProposal.bodyTicks,_root_.Integration9_9.TM2NativeFullResponseCounts.slots_native_length]
  change (_root_.CurrentAFT.BinaryFullResponseCounts.current xs.length).body=_
  rw [(_root_.CurrentAFT.BinaryFullResponseCounts.current_value xs.length).2.2.2,(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.2.1]
open _root_.P2Mba49f952 renaming h266 → _p2mH266
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h271 (xs : List Unit) : (_root_.Integration9_9.TM2NativeCoreProposal.legTicks xs).length=(_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).legs := by
  rw [_root_.Integration9_9.TM2NativeCoreProposal.legTicks,_root_.Integration9_9.TM2NativeFullResponseCounts.slots_native_length]
  change (_root_.CurrentAFT.BinaryFullResponseCounts.current xs.length).leg=_
  rw [(_root_.CurrentAFT.BinaryFullResponseCounts.current_value xs.length).1,(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.1]
open _root_.P2Mba49f952 renaming h271 → _p2mH271
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h269 (xs : List Unit) : (_root_.Integration9_9.TM2NativeCoreProposal.dimensionTicks xs).length=(_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).dimension := by
  rw [_root_.Integration9_9.TM2NativeCoreProposal.dimensionTicks,List.length_append,List.length_append,_p2mH266,_p2mH271]
  rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.2.1,(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.1,
    (_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.2.2.1]
  unfold _root_.CurrentAFT.Parameters.dimension
  omega
open _root_.P2Mba49f952 renaming h269 → _p2mH269
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h267 (x : _root_.Integration9_9.TM2NativeCoreProposal.Meta) (bits : ℕ) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length)
    (word : _root_.CurrentAFT.CurrentCoreProposal.ControlTape x.1.length bits) :
    _root_.Integration9_9.TM2NativeCoreProposal.controlDraw (x,_root_.Integration9_9.TM2NativeCoreProposal.controlTapeData word)=_root_.Integration9_9.TM2NativeCoreProposal.controlData (_root_.CurrentAFT.CurrentCoreProposal.controlDraw x.1.length x.2.length bits cache word).value := by
  simp only [_root_.Integration9_9.TM2NativeCoreProposal.controlDraw,_root_.Integration9_9.TM2NativeCoreProposal.controlTapeData,_p2mH347 x bits cache,
    _p2mH344 x bits cache,_root_.Integration9_9.TM2NativeCoreProposal.controlData,_root_.CurrentAFT.CurrentCoreProposal.controlDraw]
open _root_.P2Mba49f952 renaming h267 → _p2mH267
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h270 (x : _root_.Integration9_9.TM2NativeCoreProposal.Meta) (ticks : List Unit) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length)
    (word : _root_.CurrentAFT.CurrentCoreProposal.LegTape x.1.length ticks.length) :
    _root_.Integration9_9.TM2NativeCoreProposal.legDraw ((x,ticks),_root_.Integration9_9.TM2NativeCoreProposal.legTapeData word)=_root_.Integration9_9.TM2NativeCoreProposal.legData (_root_.CurrentAFT.CurrentCoreProposal.legDraw x.1.length x.2.length ticks.length cache word).value := by
  simp only [_root_.Integration9_9.TM2NativeCoreProposal.legDraw,_root_.Integration9_9.TM2NativeCoreProposal.legTapeData,_p2mH341 x ticks cache,
    _p2mH350,_root_.Integration9_9.TM2NativeCoreProposal.legData,_root_.CurrentAFT.CurrentCoreProposal.legDraw]
open _root_.P2Mba49f952 renaming h270 → _p2mH270
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h268 (x : _root_.Integration9_9.TM2NativeCoreProposal.Meta) (ticks : List Unit) (cache : _root_.CurrentAFT.CurrentReferenceDraw.Cache x.1.length x.2.length)
    (word : _root_.CurrentAFT.CurrentCoreProposal.Tapes x.1.length ticks.length) :
    _root_.Integration9_9.TM2NativeCoreProposal.current ((x,ticks),_root_.Integration9_9.TM2NativeCoreProposal.tapesData word)=_root_.Integration9_9.TM2NativeCoreProposal.coreData (_root_.CurrentAFT.CurrentCoreProposal.draw x.1.length x.2.length ticks.length cache word).value := by
  simp only [_root_.Integration9_9.TM2NativeCoreProposal.current,_root_.Integration9_9.TM2NativeCoreProposal.tapesData,List.map_ofFn,Function.comp_def,
    _p2mH267 x ticks.length cache,_p2mH270 x ticks cache,_p2mH350,
    _p2mH323 _ _ _ _ (_p2mH266 x.1) rfl,
    _p2mH323 _ _ _ _ (_p2mH269 x.1) rfl,
    _root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.CurrentAFT.CurrentCoreProposal.draw,_root_.AFT.BinaryArithmetic.storeData_get,_p2mH179]
open _root_.P2Mba49f952 renaming h268 → _p2mH268
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h272 (x : _root_.Integration9_9.TM2NativeCoreProposal.Meta) (ticks : List Unit)
    (word : _root_.CurrentAFT.CurrentCoreProposal.Tapes x.1.length ticks.length) :
    _root_.Integration9_9.TM2NativeCoreProposal.current ((x,ticks),_root_.Integration9_9.TM2NativeCoreProposal.tapesData word)=_root_.Integration9_9.TM2NativeCoreProposal.coreData (_root_.CurrentAFT.CurrentPreparedCoreProposal.draw x.1.length x.2.length ticks.length word).value := by
  exact _p2mH268 x ticks (_root_.CurrentAFT.CurrentReferenceDraw.prepare x.1.length x.2.length
    (_root_.CurrentAFT.BinaryReferenceTables.current x.1.length x.2.length) rfl).value word
open _root_.P2Mba49f952 renaming h272 → _p2mH272
end Integration9_9.TM2NativeCoreProposal
open _root_.P2Mba49f952 renaming h266 → _p2mH266
open _root_.P2Mba49f952 renaming h267 → _p2mH267
open _root_.P2Mba49f952 renaming h268 → _p2mH268
open _root_.P2Mba49f952 renaming h269 → _p2mH269
open _root_.P2Mba49f952 renaming h270 → _p2mH270
open _root_.P2Mba49f952 renaming h271 → _p2mH271
open _root_.P2Mba49f952 renaming h272 → _p2mH272
end
open _root_.P2Mba49f952 renaming h266 → _p2mH266
open _root_.P2Mba49f952 renaming h267 → _p2mH267
open _root_.P2Mba49f952 renaming h268 → _p2mH268
open _root_.P2Mba49f952 renaming h269 → _p2mH269
open _root_.P2Mba49f952 renaming h270 → _p2mH270
open _root_.P2Mba49f952 renaming h271 → _p2mH271
open _root_.P2Mba49f952 renaming h272 → _p2mH272
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeCoreCharge
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
open scoped BigOperators
attribute [local irreducible] CurrentProposalDimensions.current BinaryFullResponseCounts.current
  CurrentAFT.Parameters.legCount CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension
  TM2NativePrime.modulus TM2NativeProfile.widthTicks
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h264 (xs : List Unit) (primary : _root_.CurrentAFT.ActualControls.Palette xs.length)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed xs.length) :
    _root_.Integration9_9.TM2NativeCoreCharge.shift (xs,(primary.val,_root_.Integration9_9.TM2NativePublicSeed.seedData seed))=_root_.CurrentAFT.ActualPublicLegCharge.publicShift xs.length primary seed := by
  simp only [_root_.Integration9_9.TM2NativeCoreCharge.shift,_root_.Integration9_9.TM2NativePublicSeed.seedData,_root_.Integration9_9.TM2NativePrime.modulus_value,_root_.Integration9_9.TM2NativeProfile.widthTicks_length,
    _root_.CurrentAFT.ActualPublicLegCharge.publicShift,_root_.CurrentAFT.ActualPublicLegCharge.signedOffset,_root_.CurrentAFT.InwardAnchor.positiveDirection,_root_.CurrentAFT.InwardAnchor.offset,
    _root_.CurrentAFT.Parameters.anchorWidth,_root_.CurrentAFT.Parameters.scale,_root_.CurrentAFT.Parameters.base,←pow_mul,Nat.reduceMul,Nat.cast_add]
open _root_.P2Mba49f952 renaming h264 → _p2mH264
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h263 (count : ℕ) (f : ℕ → ℤ) : ((List.range count).map f).sum=∑i : Fin count,f i.val := by
  have h : (List.range count).map f=List.ofFn (fun i : Fin count => f i.val) := by
    apply List.ext_getElem
    · simp
    · intros;simp
  rw [h,List.sum_ofFn]
open _root_.P2Mba49f952 renaming h263 → _p2mH263
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h262 (xs : List Unit) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore xs.length)
    (i : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).legs) :
    _root_.Integration9_9.TM2NativeCoreCharge.legTerm ((xs,_root_.Integration9_9.TM2NativeCoreProposal.coreData data),i.val)=(_root_.CurrentAFT.BinaryCoreCharge.legTerm xs.length data i).value.decode := by
  have hc : i.val<(_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).controls := by
    have hi:=i.isLt
    have hl:=(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.1
    have hc:=(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.2.2.2.2
    omega
  simp only [_root_.Integration9_9.TM2NativeCoreCharge.legTerm,_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativeCoreProposal.legData,_root_.Integration9_9.TM2NativeCoreProposal.controlData,List.getElem?_ofFn,Fin.isLt,hc,dif_pos,Option.getD_some,
    _p2mH264,_root_.CurrentAFT.BinaryCoreCharge.legTerm,_root_.AFT.BinaryArithmetic.readVector_value,_root_.AFT.BinaryArithmetic.IntegerBits.add_value,
    _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value,_p2mH180,data.inputs_correct]
  rfl
open _root_.P2Mba49f952 renaming h262 → _p2mH262
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h265 (xs : List Unit) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore xs.length) :
    _root_.Integration9_9.TM2NativeCoreCharge.total (xs,_root_.Integration9_9.TM2NativeCoreProposal.coreData data)=(_root_.CurrentAFT.BinaryCoreCharge.total xs.length data).value.decode := by
  unfold _root_.Integration9_9.TM2NativeCoreCharge.total
  simp only [_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativeCoreCharge.intSum,List.map_ofFn,List.sum_ofFn,List.length_ofFn,_p2mH263]
  change (∑i,((data.controls.get i).2.val.val : ℤ))+
    (∑i : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).legs,_root_.Integration9_9.TM2NativeCoreCharge.legTerm ((xs,_root_.Integration9_9.TM2NativeCoreProposal.coreData data),i.val))+
    (∑i,((data.baselines.get i).val : ℤ))-(_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).legs=_
  simp only [_p2mH262,_root_.CurrentAFT.BinaryCoreCharge.total,_root_.AFT.BinaryArithmetic.IntegerBits.subtract_value,_root_.AFT.BinaryArithmetic.IntegerBits.add_value,_p2mH1,
    _root_.CurrentAFT.BinaryCoreCharge.controlTerm,_root_.CurrentAFT.BinaryCoreCharge.queueTerm,_root_.AFT.BinaryArithmetic.readVector_value,_root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value]
open _root_.P2Mba49f952 renaming h265 → _p2mH265
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h261 (xs : List Unit) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore xs.length) :
    _root_.Integration9_9.TM2NativeCoreCharge.current (xs,_root_.Integration9_9.TM2NativeCoreProposal.coreData data)=(_root_.CurrentAFT.BinaryCoreCharge.current xs.length data).value := by
  have hq : 0<_root_.AFT.BinaryArithmetic.value (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits := by
    rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value,_root_.CurrentAFT.PublicParameterProgram.modulus_value]
    exact (_root_.CurrentAFT.Parameters.modulus_spec xs.length).2.pos
  have hr:=_root_.AFT.BinaryArithmetic.IntegerBits.residue_value (_root_.CurrentAFT.BinaryCoreCharge.total xs.length data).value
    (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits hq
  rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value] at hr
  apply Bool.eq_iff_iff.mpr
  simp only [_root_.Integration9_9.TM2NativeCoreCharge.current,decide_eq_true_eq,_p2mH265,_root_.Integration9_9.TM2NativeBodyKernel.emodNatural_eq,_root_.Integration9_9.TM2NativePrime.modulus_native]
  change _ ↔ (_root_.AFT.BinaryArithmetic.normalize (_root_.AFT.BinaryArithmetic.IntegerBits.residue (_root_.CurrentAFT.BinaryCoreCharge.total xs.length data).value
    (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits).digits).digits.isEmpty=true
  rw [List.isEmpty_iff,_root_.AFT.BinaryArithmetic.normalize_nil_iff,←hr,Int.toNat_natCast]
open _root_.P2Mba49f952 renaming h261 → _p2mH261
end Integration9_9.TM2NativeCoreCharge
open _root_.P2Mba49f952 renaming h261 → _p2mH261
open _root_.P2Mba49f952 renaming h262 → _p2mH262
open _root_.P2Mba49f952 renaming h263 → _p2mH263
open _root_.P2Mba49f952 renaming h264 → _p2mH264
open _root_.P2Mba49f952 renaming h265 → _p2mH265
end
open _root_.P2Mba49f952 renaming h261 → _p2mH261
open _root_.P2Mba49f952 renaming h262 → _p2mH262
open _root_.P2Mba49f952 renaming h263 → _p2mH263
open _root_.P2Mba49f952 renaming h264 → _p2mH264
open _root_.P2Mba49f952 renaming h265 → _p2mH265
section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitterCoordinates
open AFT AFT.RationalNumerics AFT.BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeSliceProbability
open scoped BigOperators
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h438 {count : ℕ} (f : Fin (count+1)→ℤ) (delta : ℤ) (k : ℕ) (hk : 0<k) :
    ((List.ofFn (fun i=>f i+if i=0 then delta else 0)).take k).sum=
      ((List.ofFn f).take k).sum+delta := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [List.ofFn_succ,ite_true,Fin.succ_ne_zero,ite_false,add_zero,List.take_succ_cons,List.sum_cons]
  ring
open _root_.P2Mba49f952 renaming h438 → _p2mH438
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h285 (count : ℕ) (load : Vector ℤ (count+1)) (i : Fin count) :
    (_root_.AFT.pathInverseProgram count load).value.get i=((List.ofFn load.get).take (i.val+1)).sum := by
  induction count with
  | zero=>exact Fin.elim0 i
  | succ count ih=>
    refine Fin.cases ?_ (fun rest=>?_) i
    · simp only [_root_.AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_zero,List.ofFn_succ,List.take_succ_cons,
        List.take_zero,List.sum_nil,List.sum_cons,add_zero,Fin.val_zero]
    · simp only [_root_.AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_succ]
      rw [ih]
      simp only [_p2mH42]
      rw [_p2mH438 (fun j : Fin (count+1)=>load.get j.succ) (load.get 0) (rest.val+1) (by omega)]
      simp only [List.ofFn_succ,List.take_succ_cons,List.sum_cons,Fin.val_succ]
      ring
open _root_.P2Mba49f952 renaming h285 → _p2mH285
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h437 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h437 → _p2mH437
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h286 (count : ℕ) (load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) :
    _root_.Integration9_9.TM2NativeEmitterCoordinates.path (List.ofFn (fun i=>(load.get i).decode))=
      List.ofFn (fun i=>((_root_.AFT.BinaryArithmetic.binaryPathInverse count load).value.get i).decode) := by
  simp only [_root_.Integration9_9.TM2NativeEmitterCoordinates.path,List.length_ofFn,Nat.add_sub_cancel,_p2mH437]
  apply congrArg List.ofFn
  funext i
  rw [_p2mH19,_p2mH285]
  have hg : (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get=(fun j=>(load.get j).decode) := by
    funext j
    simp only [Vector.get_map]
  rw [hg]
open _root_.P2Mba49f952 renaming h286 → _p2mH286
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h288 (input : _root_.AFT.BinaryArithmetic.IntegerBits) (modulus : List Bool) (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus) :
    _root_.Integration9_9.TM2NativeEmitterCoordinates.truncQuot (input.decode,_root_.AFT.BinaryArithmetic.value modulus)=(_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient input modulus).value.decode := by
  have hv := (_root_.AFT.BinaryArithmetic.divide_value input.digits modulus hq).1
  cases hs : input.negative with
  | false => simp [_root_.Integration9_9.TM2NativeEmitterCoordinates.truncQuot,_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient,hv]
  | true =>
      by_cases hz : _root_.AFT.BinaryArithmetic.value input.digits=0
      · simp [_root_.Integration9_9.TM2NativeEmitterCoordinates.truncQuot,_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient,hv,hz]
      · have hp : 0 < (_root_.AFT.BinaryArithmetic.value input.digits : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hz
        simp [_root_.Integration9_9.TM2NativeEmitterCoordinates.truncQuot,_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient,hv,hz]
open _root_.P2Mba49f952 renaming h288 → _p2mH288
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h283 (count : ℕ) (modulus : List Bool)
    (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus) :
    _root_.Integration9_9.TM2NativeEmitterCoordinates.charge (_root_.AFT.BinaryArithmetic.value modulus,(List.ofFn (fun i=>(injection.get i).decode),List.ofFn (fun i=>(load.get i).decode)))=
      (_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).charge.decode := by
  have ht : (_root_.AFT.BinaryArithmetic.IntegerBits.sumFin (count+1) (_root_.AFT.BinaryArithmetic.readVector _root_.AFT.BinaryArithmetic.IntegerBits.zero load)).value.decode=
      (List.ofFn (fun i=>(load.get i).decode)).sum := by
    rw [_p2mH1,List.sum_ofFn]
    simp only [_root_.AFT.BinaryArithmetic.readVector_value]
  change _root_.Integration9_9.TM2NativeEmitterCoordinates.truncQuot (_,_root_.AFT.BinaryArithmetic.value modulus)=_
  rw [← ht,_p2mH288 _ _ hq]
  rfl
open _root_.P2Mba49f952 renaming h283 → _p2mH283
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h287 (count : ℕ) (modulus : List Bool)
    (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus) :
    _root_.Integration9_9.TM2NativeEmitterCoordinates.shifted (_root_.AFT.BinaryArithmetic.value modulus,(List.ofFn (fun i=>(injection.get i).decode),List.ofFn (fun i=>(load.get i).decode)))=
      List.ofFn (fun i=>((_root_.AFT.BinaryArithmetic.binaryShiftedLoad (_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).charge injection load).value.get i).decode) := by
  simp only [_root_.Integration9_9.TM2NativeEmitterCoordinates.shifted,List.length_ofFn,_p2mH437]
  apply congrArg List.ofFn
  funext i
  rw [_p2mH283 count modulus injection load hq,_p2mH26]
  simp only [List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
open _root_.P2Mba49f952 renaming h287 → _p2mH287
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h284 (count : ℕ) (modulus : List Bool)
    (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus) :
    _root_.Integration9_9.TM2NativeEmitterCoordinates.current (_root_.AFT.BinaryArithmetic.value modulus,(List.ofFn (fun i=>(injection.get i).decode),List.ofFn (fun i=>(load.get i).decode)))=
      (List.ofFn (fun i=>((_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).edges.get i).decode),
        (_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).charge.decode) := by
  unfold _root_.Integration9_9.TM2NativeEmitterCoordinates.current
  rw [_p2mH287 count modulus injection load hq,_p2mH286,_p2mH283 count modulus injection load hq]
  rfl
open _root_.P2Mba49f952 renaming h284 → _p2mH284
end Integration9_9.TM2NativeEmitterCoordinates
open _root_.P2Mba49f952 renaming h283 → _p2mH283
open _root_.P2Mba49f952 renaming h284 → _p2mH284
open _root_.P2Mba49f952 renaming h285 → _p2mH285
open _root_.P2Mba49f952 renaming h286 → _p2mH286
open _root_.P2Mba49f952 renaming h287 → _p2mH287
open _root_.P2Mba49f952 renaming h288 → _p2mH288
open _root_.P2Mba49f952 renaming h437 → _p2mH437
open _root_.P2Mba49f952 renaming h438 → _p2mH438
end
open _root_.P2Mba49f952 renaming h283 → _p2mH283
open _root_.P2Mba49f952 renaming h284 → _p2mH284
open _root_.P2Mba49f952 renaming h285 → _p2mH285
open _root_.P2Mba49f952 renaming h286 → _p2mH286
open _root_.P2Mba49f952 renaming h287 → _p2mH287
open _root_.P2Mba49f952 renaming h288 → _p2mH288
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitterLoads
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h300 (count column : ℕ) (root : Fin (count+1)) :
    _root_.Integration9_9.TM2NativeEmitterLoads.path (count,(column,root.val))=_root_.AFT.pathLoad count (fun edge=>if edge.val=column then 1 else 0) root := by
  exact (_p2mH118 count column root.val).symm.trans
    (_p2mH171 count column root)
open _root_.P2Mba49f952 renaming h300 → _p2mH300
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h298 (security column : ℕ)
    (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs)
    (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) (point : _root_.CurrentAFT.CurrentBinaryLoadColumns.Point security) :
    _root_.Integration9_9.TM2NativeEmitterLoads.entry (_root_.Integration9_9.TM2NativeEmitterLoads.nativeData security scale shear roots,(column,
      (_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1 point).val))=
    (_root_.CurrentAFT.CurrentBinaryLoadColumns.entry security column scale shear roots point).value.decode := by
  rw [_p2mH119]
  rcases point with ⟨leg|body,slot⟩
  · change Fin 3 at slot
    have hnum : (_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1 ⟨Sum.inl leg,slot⟩).val=slot.val+3*leg.val := rfl
    rw [hnum]
    have hl : leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := leg.isLt
    have hlt : slot.val+3*leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3 := by omega
    have hdiv : (slot.val+3*leg.val)/3=leg.val := by omega
    have hmod : (slot.val+3*leg.val)%3=slot.val := by omega
    simp only [_root_.Integration9_9.TM2NativeEmitterLoads.entry,_root_.Integration9_9.TM2NativeEmitterLoads.nativeData,List.length_ofFn,if_pos hlt,hdiv,hmod]
    simp only [_root_.Integration9_9.TM2NativeEmitterLoads.leg,_root_.Integration9_9.TM2NativeEmitterLoads.first,_root_.Integration9_9.TM2NativeEmitterLoads.second,List.length_ofFn,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
    have hr : leg.val < _root_.CurrentAFT.CurrentBinaryLoadColumns.Body security := by
      change leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).body
      have hc := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1
      omega
    have hp := _p2mH300 (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column
      ((roots.get ((_root_.AFT.blockNumbering _ _ (.inl leg)).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1)).cast
        (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    fin_cases slot <;> simp only [Fin.val_zero,Fin.val_succ,ite_true,ite_false,
      _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry,_root_.CurrentAFT.CurrentBinaryLoadColumns.primaryEntry,
      _root_.CurrentAFT.CurrentBinaryLoadColumns.secondEntry,_root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue,
      Matrix.cons_val_zero',Matrix.cons_val_succ',hp] <;> simp [_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs,hr,hp]
    exact hp
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    have hnum : (_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1 ⟨Sum.inr body,(0 : Fin 1)⟩).val=
      (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3+body.val := by
      change (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3+(0+1*body.val)=_
      omega
    rw [hnum]
    simp only [_root_.Integration9_9.TM2NativeEmitterLoads.entry,_root_.Integration9_9.TM2NativeEmitterLoads.nativeData,List.length_ofFn,show ¬(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3+body.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3 by omega,
      if_false,Nat.add_sub_cancel_left,_root_.Integration9_9.TM2NativeEmitterLoads.body,List.length_ofFn]
    have hr : (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs+body.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).body := by
      have hc := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1
      omega
    have hp := _p2mH300 (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column
      ((roots.get ((_root_.AFT.blockNumbering _ _ (.inr body)).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1)).cast
        (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    simp only [List.getElem?_ofFn,hr,dif_pos,Option.getD_some]
    exact congrArg (fun v : ℤ=>v+if (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers≤body.val ∧ column=(_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges then 1 else 0) hp
open _root_.P2Mba49f952 renaming h298 → _p2mH298
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h301 (security : ℕ)
    (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs)
    (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) :
    (_root_.Integration9_9.TM2NativeEmitterLoads.slots (_root_.Integration9_9.TM2NativeEmitterLoads.nativeData security scale shear roots)).length=(_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1 := by
  simp only [_root_.Integration9_9.TM2NativeEmitterLoads.slots,_root_.Integration9_9.TM2NativeEmitterLoads.nativeData,List.length_append,List.length_map,List.length_ofFn]
  have hb := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1
  have he := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.2.2
  change (_root_.CurrentAFT.CurrentProposalDimensions.current security).body+(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs+
    (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs=_
  omega
open _root_.P2Mba49f952 renaming h301 → _p2mH301
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h440 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h440 → Integration9_9.TM2NativeEmitterLoads.range_map
open _root_.P2Mba49f952 renaming h440 → _p2mH440
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h299 (security : ℕ)
    (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs)
    (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) :
    _root_.Integration9_9.TM2NativeEmitterLoads.matrix (_root_.Integration9_9.TM2NativeEmitterLoads.nativeData security scale shear roots)=
      List.ofFn (fun column=>List.ofFn (fun row=>
        (((_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix security scale shear roots).value.get column).get row).decode)) := by
  simp only [_root_.Integration9_9.TM2NativeEmitterLoads.matrix,_p2mH301,_p2mH440]
  apply congrArg List.ofFn
  funext column
  apply congrArg List.ofFn
  funext row
  rw [_p2mH120]
  have h := _p2mH298 security column.val scale shear roots
    ((_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1).symm row)
  rw [Equiv.apply_symm_apply,_p2mH119] at h
  exact h
open _root_.P2Mba49f952 renaming h299 → _p2mH299
end Integration9_9.TM2NativeEmitterLoads
open _root_.P2Mba49f952 renaming h298 → _p2mH298
open _root_.P2Mba49f952 renaming h299 → _p2mH299
open _root_.P2Mba49f952 renaming h300 → _p2mH300
open _root_.P2Mba49f952 renaming h301 → _p2mH301
open _root_.P2Mba49f952 renaming h440 → Integration9_9.TM2NativeEmitterLoads.range_map
open _root_.P2Mba49f952 renaming h440 → _p2mH440
end
open _root_.P2Mba49f952 renaming h298 → _p2mH298
open _root_.P2Mba49f952 renaming h299 → _p2mH299
open _root_.P2Mba49f952 renaming h300 → _p2mH300
open _root_.P2Mba49f952 renaming h301 → _p2mH301
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitterRoots
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
attribute [local irreducible] CurrentProposalDimensions.current
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h446 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h446 → Integration9_9.TM2NativeEmitterRoots.range_map
open _root_.P2Mba49f952 renaming h446 → _p2mH446
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h445 {α : Type} (n : ℕ) (f : Fin n→α) (i : Fin n) (zero : α) :
    (List.ofFn f)[i.val]?.getD zero=f i := by
  simp only [List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
open _root_.P2Mba49f952 renaming h445 → _p2mH445
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h309 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) :
    _root_.Integration9_9.TM2NativeEmitterRoots.current (_root_.Integration9_9.TM2NativeCoreProposal.coreData data,(_root_.Integration9_9.TM2NativePermutationDraw.cacheData layout).1)=
      List.ofFn (fun i=>((_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout data).value.get i).val) := by
  simp only [_root_.Integration9_9.TM2NativeEmitterRoots.current,_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativePermutationDraw.cacheData,List.length_ofFn,_p2mH446]
  apply congrArg List.ofFn
  funext i
  rw [_p2mH149]
  let rotated := (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate (_root_.CurrentAFT.CurrentProposalDimensions.current security).body
    (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs (_root_.CurrentAFT.CurrentEmissionRootOrder.legs_le_body security) i).value
  have hr : _root_.Integration9_9.TM2NativeEmitterRoots.rotate (((_root_.CurrentAFT.CurrentProposalDimensions.current security).body,(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs),i.val)=rotated.val := by
    exact (_p2mH151 _ _ _ i).symm
  rw [hr,_p2mH445 _ _ rotated,_p2mH445 _ _ (layout.forward.get rotated)]
open _root_.P2Mba49f952 renaming h309 → _p2mH309
end Integration9_9.TM2NativeEmitterRoots
open _root_.P2Mba49f952 renaming h309 → _p2mH309
open _root_.P2Mba49f952 renaming h445 → _p2mH445
open _root_.P2Mba49f952 renaming h446 → Integration9_9.TM2NativeEmitterRoots.range_map
open _root_.P2Mba49f952 renaming h446 → _p2mH446
end
open _root_.P2Mba49f952 renaming h309 → _p2mH309
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitterOffset
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h302 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)⊕Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    (_root_.Integration9_9.TM2NativeEmitterOffset.baselines (_root_.Integration9_9.TM2NativeCoreProposal.coreData core))[(_root_.AFT.blockNumbering _ _ point).val]?.getD 0=
      (_root_.CurrentAFT.CurrentBinaryBaselines.read security core point).value.decode := by
  simp only [_root_.Integration9_9.TM2NativeEmitterOffset.baselines,_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativeCoreProposal.legData,_root_.Integration9_9.TM2NativeCoreProposal.controlData,List.map_ofFn,Function.comp_def,List.append_assoc]
  rcases point with leg|body
  · change _[leg.val]?.getD 0=_
    have hl : leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := leg.isLt
    simp only [List.getElem?_append,List.length_ofFn,List.length_append,hl,if_pos,Nat.not_lt_zero,_root_.CurrentAFT.CurrentBinaryBaselines.read,
      _root_.AFT.BinaryArithmetic.readVector_value,_root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value,List.getElem?_ofFn,dif_pos,Option.getD_some]
  · change _[(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs+body.val]?.getD 0=_
    have hcenters := _root_.CurrentAFT.CurrentBinaryBaselines.controls_count security
    have hlen := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.2.1
    by_cases hb : body.val < (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers
    · have hs := (_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mpr hb
      have hc : body.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).controls := by omega
      simp only [List.getElem?_append,List.length_ofFn,List.length_append,_root_.CurrentAFT.CurrentBinaryBaselines.read,dif_pos hs,
        _root_.AFT.BinaryArithmetic.readVector_value,_root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value,List.getElem?_ofFn]
      simp only [show ¬(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs+body.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs by omega,
        if_false,Nat.add_sub_cancel_left,hc,dif_pos,if_pos,Option.getD_some]
    · have hs : ¬(_root_.AFT.BinaryArithmetic.lessCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).value=true := by
        simpa only [_root_.AFT.BinaryArithmetic.lessCounter_value] using hb
      have hc : ¬body.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).controls := by omega
      have hq : body.val-(_root_.CurrentAFT.CurrentProposalDimensions.current security).controls < (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors := by omega
      simp only [List.getElem?_append,List.length_ofFn,List.length_append,_root_.CurrentAFT.CurrentBinaryBaselines.read,dif_neg hs,
        _root_.AFT.BinaryArithmetic.readVector_value,_root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value,List.getElem?_ofFn,_root_.AFT.BinaryArithmetic.subtractCounter_value]
      simp only [show ¬(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs+body.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs by omega,
        if_false,Nat.add_sub_cancel_left,hc,if_false,hq,dif_pos,Option.getD_some]
      apply congrArg (fun index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors=>
        ((core.baselines.get index).val : ℤ))
      apply Fin.ext
      change body.val-(_root_.CurrentAFT.CurrentProposalDimensions.current security).controls=body.val-(_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers
      omega
open _root_.P2Mba49f952 renaming h302 → _p2mH302
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h441 (p : Prop) [Decidable p] (a b : _root_.AFT.BinaryArithmetic.IntegerBits) :
    (if p then a else b).decode=if p then a.decode else b.decode := by split_ifs <;> rfl
open _root_.P2Mba49f952 renaming h441 → _p2mH441
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h304 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (modulus : _root_.AFT.BinaryArithmetic.IntegerBits)
    (shift intercept : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security))
    (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) (scalar : _root_.AFT.BinaryArithmetic.IntegerBits) (point : _root_.CurrentAFT.CurrentBinaryLoadColumns.Point security) :
    _root_.Integration9_9.TM2NativeEmitterOffset.entry (_root_.Integration9_9.TM2NativeEmitterOffset.nativeData security core modulus shift intercept roots scalar,
      (_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1 point).val)=
      (_root_.CurrentAFT.CurrentBinaryOffsetLoad.entry security core modulus shift intercept roots scalar point).value.decode := by
  rcases point with ⟨leg|body,slot⟩
  · change Fin 3 at slot
    have hnum : (_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1 ⟨Sum.inl leg,slot⟩).val=slot.val+3*leg.val := rfl
    rw [hnum]
    have hl : leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := leg.isLt
    have hr : leg.val < _root_.CurrentAFT.CurrentBinaryLoadColumns.Body security := by
      change leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).body
      have hc := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1
      omega
    have hb : _root_.CurrentAFT.CurrentBinaryLoadColumns.Body security-1=(_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges := by
      have hc := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1
      change (_root_.CurrentAFT.CurrentProposalDimensions.current security).body-1=_
      omega
    have hlt : slot.val+3*leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3 := by omega
    have hdiv : (slot.val+3*leg.val)/3=leg.val := by omega
    have hmod : (slot.val+3*leg.val)%3=slot.val := by omega
    simp only [_root_.Integration9_9.TM2NativeEmitterOffset.entry,_root_.Integration9_9.TM2NativeEmitterOffset.nativeData,List.length_ofFn,if_pos hlt,hdiv,hmod,_root_.Integration9_9.TM2NativeEmitterOffset.leg,
      List.getElem?_ofFn,Fin.isLt,hr,dif_pos,Option.getD_some,hb]
    have hbase := _p2mH302 security core (Sum.inl leg)
    change (_root_.Integration9_9.TM2NativeEmitterOffset.baselines (_root_.Integration9_9.TM2NativeCoreProposal.coreData core))[leg.val]?.getD 0=_ at hbase
    fin_cases slot <;> simp [_root_.CurrentAFT.CurrentBinaryOffsetLoad.entry,_p2mH121,
      _root_.AFT.BinaryArithmetic.IntegerBits.add_value,_root_.AFT.BinaryArithmetic.IntegerBits.subtract_value,_root_.AFT.BinaryArithmetic.readVector_value,_root_.CurrentAFT.CurrentBinaryOffsetLoad.closure,
      _root_.AFT.BinaryArithmetic.equalCounter_value,_root_.Integration9_9.TM2NativeEmitterOffset.closure,_p2mH441,_root_.AFT.BinaryArithmetic.IntegerBits.zero_value,_root_.AFT.BinaryArithmetic.IntegerBits.one_value,hbase] <;> rfl
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    have hnum : (_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1 ⟨Sum.inr body,(0 : Fin 1)⟩).val=
      (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3+body.val := by
      change (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3+(0+1*body.val)=_
      omega
    rw [hnum]
    have hr : (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs+body.val < _root_.CurrentAFT.CurrentBinaryLoadColumns.Body security := by
      change _ < (_root_.CurrentAFT.CurrentProposalDimensions.current security).body
      have hc := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1
      omega
    have hb : _root_.CurrentAFT.CurrentBinaryLoadColumns.Body security-1=(_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges := by
      have hc := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1
      change (_root_.CurrentAFT.CurrentProposalDimensions.current security).body-1=_
      omega
    simp only [_root_.Integration9_9.TM2NativeEmitterOffset.entry,_root_.Integration9_9.TM2NativeEmitterOffset.nativeData,List.length_ofFn,show ¬(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3+body.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs*3 by omega,
      if_false,Nat.add_sub_cancel_left,_root_.Integration9_9.TM2NativeEmitterOffset.body,List.length_ofFn,List.getElem?_ofFn,hr,dif_pos,Option.getD_some,hb]
    have hbase := _p2mH302 security core (Sum.inr body)
    change (_root_.Integration9_9.TM2NativeEmitterOffset.baselines (_root_.Integration9_9.TM2NativeCoreProposal.coreData core))[(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs+body.val]?.getD 0=_ at hbase
    simp [_root_.CurrentAFT.CurrentBinaryOffsetLoad.entry,_p2mH121,
      _root_.AFT.BinaryArithmetic.IntegerBits.add_value,_root_.AFT.BinaryArithmetic.IntegerBits.subtract_value,_root_.AFT.BinaryArithmetic.readVector_value,_root_.CurrentAFT.CurrentBinaryOffsetLoad.closure,
      _root_.AFT.BinaryArithmetic.equalCounter_value,_root_.Integration9_9.TM2NativeEmitterOffset.closure,_p2mH441,_root_.AFT.BinaryArithmetic.IntegerBits.zero_value,_root_.AFT.BinaryArithmetic.IntegerBits.one_value,hbase] <;> rfl
open _root_.P2Mba49f952 renaming h304 → _p2mH304
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h305 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (modulus : _root_.AFT.BinaryArithmetic.IntegerBits)
    (shift intercept : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security))
    (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) (scalar : _root_.AFT.BinaryArithmetic.IntegerBits) :
    (_root_.Integration9_9.TM2NativeEmitterOffset.slots (_root_.Integration9_9.TM2NativeEmitterOffset.nativeData security core modulus shift intercept roots scalar)).length=(_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1 := by
  simp only [_root_.Integration9_9.TM2NativeEmitterOffset.slots,_root_.Integration9_9.TM2NativeEmitterOffset.nativeData,List.length_append,List.length_map,List.length_ofFn]
  have hb := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1
  have he := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.2.2
  change (_root_.CurrentAFT.CurrentProposalDimensions.current security).body+(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs+
    (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs=_
  omega
open _root_.P2Mba49f952 renaming h305 → _p2mH305
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h442 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h442 → Integration9_9.TM2NativeEmitterOffset.range_map
open _root_.P2Mba49f952 renaming h442 → _p2mH442
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h303 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (modulus : _root_.AFT.BinaryArithmetic.IntegerBits)
    (shift intercept : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security))
    (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) (scalar : _root_.AFT.BinaryArithmetic.IntegerBits) :
    _root_.Integration9_9.TM2NativeEmitterOffset.current (_root_.Integration9_9.TM2NativeEmitterOffset.nativeData security core modulus shift intercept roots scalar)=
      List.ofFn (fun row=>((_root_.CurrentAFT.CurrentBinaryOffsetLoad.load security core modulus shift intercept roots scalar).value.get row).decode) := by
  simp only [_root_.Integration9_9.TM2NativeEmitterOffset.current,_p2mH305,_p2mH442]
  apply congrArg List.ofFn
  funext row
  simp only [_root_.CurrentAFT.CurrentBinaryOffsetLoad.load,_root_.AFT.BinaryArithmetic.storeData_get,_p2mH22]
  have h := _p2mH304 security core modulus shift intercept roots scalar
    ((_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1).symm row)
  rw [Equiv.apply_symm_apply] at h
  exact h
open _root_.P2Mba49f952 renaming h303 → _p2mH303
end Integration9_9.TM2NativeEmitterOffset
open _root_.P2Mba49f952 renaming h302 → _p2mH302
open _root_.P2Mba49f952 renaming h303 → _p2mH303
open _root_.P2Mba49f952 renaming h304 → _p2mH304
open _root_.P2Mba49f952 renaming h305 → _p2mH305
open _root_.P2Mba49f952 renaming h441 → _p2mH441
open _root_.P2Mba49f952 renaming h442 → Integration9_9.TM2NativeEmitterOffset.range_map
open _root_.P2Mba49f952 renaming h442 → _p2mH442
end
open _root_.P2Mba49f952 renaming h302 → _p2mH302
open _root_.P2Mba49f952 renaming h303 → _p2mH303
open _root_.P2Mba49f952 renaming h304 → _p2mH304
open _root_.P2Mba49f952 renaming h305 → _p2mH305
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitterColumns
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h282 {size : ℕ} (load : Vector _root_.AFT.BinaryArithmetic.IntegerBits size) (permutation : Vector (Fin size) size) :
    _root_.Integration9_9.TM2NativeEmitterColumns.permute (_root_.Integration9_9.TM2NativeEmitterColumns.integerData load,_root_.Integration9_9.TM2NativeEmitterColumns.permutationData permutation)=List.ofFn (fun i=>(load.get (permutation.get i)).decode) := by
  simp only [_root_.Integration9_9.TM2NativeEmitterColumns.permute,_root_.Integration9_9.TM2NativeEmitterColumns.integerData,_root_.Integration9_9.TM2NativeEmitterColumns.permutationData,List.map_ofFn,Function.comp_def,
    List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
open _root_.P2Mba49f952 renaming h282 → _p2mH282
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h280 (count : ℕ) (modulus : List Bool) (injection : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1))
    (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (count+1))
    (permutation : Vector (Fin (count+1)) (count+1)) (selected : Fin (count+1))
    (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus) :
    _root_.Integration9_9.TM2NativeEmitterColumns.column ((_root_.AFT.BinaryArithmetic.value modulus,_root_.Integration9_9.TM2NativeEmitterColumns.integerData injection),(_root_.Integration9_9.TM2NativeEmitterColumns.integerData (matrix.get selected),_root_.Integration9_9.TM2NativeEmitterColumns.permutationData permutation))=
      _root_.Integration9_9.TM2NativeEmitterColumns.coordinateData (_root_.AFT.BinaryArithmetic.binaryAffineColumn count modulus injection matrix permutation selected).value := by
  rw [_root_.Integration9_9.TM2NativeEmitterColumns.column,_p2mH282]
  have h : List.ofFn (fun i=>((matrix.get selected).get (permutation.get i)).decode)=
      _root_.Integration9_9.TM2NativeEmitterColumns.integerData (_root_.AFT.BinaryArithmetic.binaryPermutedColumn count matrix permutation selected).value := by
    simp only [_root_.Integration9_9.TM2NativeEmitterColumns.integerData,_p2mH21]
  rw [h]
  exact _p2mH284 count modulus injection _ hq
open _root_.P2Mba49f952 renaming h280 → _p2mH280
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h281 (security : ℕ) (modulus : List Bool)
    (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security))
    (permutation : Vector (Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security))
    (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus) :
    _root_.Integration9_9.TM2NativeEmitterColumns.column ((_root_.AFT.BinaryArithmetic.value modulus,_root_.Integration9_9.TM2NativeEmitterColumns.integerData injection),(_root_.Integration9_9.TM2NativeEmitterColumns.integerData load,_root_.Integration9_9.TM2NativeEmitterColumns.permutationData permutation))=
      _root_.Integration9_9.TM2NativeEmitterColumns.coordinateData ((_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges modulus injection
        (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad security load permutation).value).edges,
        (_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges modulus injection
        (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad security load permutation).value).charge) := by
  rw [_root_.Integration9_9.TM2NativeEmitterColumns.column,_p2mH282]
  have h : List.ofFn (fun i=>(load.get (permutation.get i)).decode)=
      _root_.Integration9_9.TM2NativeEmitterColumns.integerData (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad security load permutation).value := by
    simp only [_root_.Integration9_9.TM2NativeEmitterColumns.integerData,_p2mH105]
  rw [h]
  exact _p2mH284 _ modulus injection _ hq
open _root_.P2Mba49f952 renaming h281 → _p2mH281
end Integration9_9.TM2NativeEmitterColumns
open _root_.P2Mba49f952 renaming h280 → _p2mH280
open _root_.P2Mba49f952 renaming h281 → _p2mH281
open _root_.P2Mba49f952 renaming h282 → _p2mH282
end
open _root_.P2Mba49f952 renaming h280 → _p2mH280
open _root_.P2Mba49f952 renaming h281 → _p2mH281
open _root_.P2Mba49f952 renaming h282 → _p2mH282
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitterData
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  TM2NativePrime.modulus TM2NativeProfile.widthTicks dimensionTicks
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h295 (security : ℕ) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security) :
    _root_.Integration9_9.TM2NativeEmitterData.scale (_root_.Integration9_9.TM2NativeEmitterData.chartsData charts)=List.ofFn (fun i=>((_root_.CurrentAFT.CurrentBinaryChartData.fieldArray security charts (fun chart=>chart.2.2.1)).value.get i).decode) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeEmitterData.scale,_root_.Integration9_9.TM2NativeEmitterData.chartsData,List.length_map,List.length_ofFn]
    exact (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1.symm
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeEmitterData.scale,_root_.Integration9_9.TM2NativeEmitterData.chartsData,List.getElem_map,List.getElem_ofFn,_p2mH108,_root_.Integration9_9.TM2NativeEmitterData.chartData]
    rfl
open _root_.P2Mba49f952 renaming h295 → _p2mH295
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h296 (security : ℕ) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security) :
    _root_.Integration9_9.TM2NativeEmitterData.shear (_root_.Integration9_9.TM2NativeEmitterData.chartsData charts)=List.ofFn (fun i=>((_root_.CurrentAFT.CurrentBinaryChartData.fieldArray security charts (fun chart=>chart.2.2.2)).value.get i).decode) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeEmitterData.shear,_root_.Integration9_9.TM2NativeEmitterData.chartsData,List.length_map,List.length_ofFn]
    exact (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1.symm
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeEmitterData.shear,_root_.Integration9_9.TM2NativeEmitterData.chartsData,List.getElem_map,List.getElem_ofFn,_p2mH108,_root_.Integration9_9.TM2NativeEmitterData.chartData]
    rfl
open _root_.P2Mba49f952 renaming h296 → _p2mH296
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h291 (security : ℕ) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security) :
    _root_.Integration9_9.TM2NativeEmitterData.intercept (_root_.Integration9_9.TM2NativeEmitterData.chartsData charts)=List.ofFn (fun i=>((_root_.CurrentAFT.CurrentBinaryChartData.fieldArray security charts (fun chart=>chart.2.1)).value.get i).decode) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeEmitterData.intercept,_root_.Integration9_9.TM2NativeEmitterData.chartsData,List.length_map,List.length_ofFn]
    exact (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1.symm
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeEmitterData.intercept,_root_.Integration9_9.TM2NativeEmitterData.chartsData,List.getElem_map,List.getElem_ofFn,_p2mH108,_root_.Integration9_9.TM2NativeEmitterData.chartData]
    rfl
open _root_.P2Mba49f952 renaming h291 → _p2mH291
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h439 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h439 → Integration9_9.TM2NativeEmitterData.range_map
open _root_.P2Mba49f952 renaming h439 → _p2mH439
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h297 (xs : List Unit) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore xs.length) :
    _root_.Integration9_9.TM2NativeEmitterData.shifts (xs,_root_.Integration9_9.TM2NativeCoreProposal.coreData core)=List.ofFn (fun i=>((_root_.CurrentAFT.CurrentBinaryChartData.shiftArray xs.length core).value.get i).decode) := by
  have hn : (_root_.Integration9_9.TM2NativeCoreProposal.coreData core).1.2.length=(_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).legs := by
    simp only [_root_.Integration9_9.TM2NativeCoreProposal.coreData,List.length_ofFn]
  rw [_root_.Integration9_9.TM2NativeEmitterData.shifts,hn,_p2mH439]
  apply congrArg List.ofFn
  funext i
  rw [_root_.Integration9_9.TM2NativeEmitterData.shiftAt,_p2mH262 xs core i]
  simp only [_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativeCoreProposal.legData,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,_root_.CurrentAFT.BinaryCoreCharge.legTerm,
    _root_.AFT.BinaryArithmetic.IntegerBits.add_value,_root_.AFT.BinaryArithmetic.readVector_value,_root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value,_p2mH180,
    core.inputs_correct,_p2mH109]
  change _+_root_.CurrentAFT.ActualPublicCharge.legShift xs.length core.core (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv xs.length i)-_=_
  ring
open _root_.P2Mba49f952 renaming h297 → _p2mH297
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h290 (xs : List Unit) :
    _root_.Integration9_9.TM2NativeEmitterData.injection xs=List.ofFn (fun i=>((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.injection xs.length).value.get i).decode) := by
  have hn : (_root_.Integration9_9.TM2NativeCoreProposal.dimensionTicks xs).length=(_root_.CurrentAFT.CurrentEmissionMetadata.current xs.length).edges+1 :=
    (_p2mH269 xs).trans (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts xs.length).2.1.symm
  simp only [_root_.Integration9_9.TM2NativeEmitterData.injection,hn,_p2mH439]
  apply congrArg List.ofFn
  funext i
  rw [_p2mH104,_root_.Integration9_9.TM2NativePrime.modulus_value]
  rfl
open _root_.P2Mba49f952 renaming h290 → _p2mH290
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h292 (xs : List Unit) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache xs.length)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result xs.length) :
    _root_.Integration9_9.TM2NativeEmitterData.loadData (_root_.Integration9_9.TM2NativeEmitterData.nativeContext xs layout sample)=
      _root_.Integration9_9.TM2NativeEmitterLoads.nativeData xs.length
        (_root_.CurrentAFT.CurrentBinaryChartData.fieldArray xs.length sample.charts (fun chart=>chart.2.2.1)).value
        (_root_.CurrentAFT.CurrentBinaryChartData.fieldArray xs.length sample.charts (fun chart=>chart.2.2.2)).value
        (_root_.CurrentAFT.CurrentEmissionRootOrder.positions xs.length layout sample.core).value := by
  have hb := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts xs.length).1
  have he := (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts xs.length).2.1
  have hc := _root_.CurrentAFT.CurrentBinaryBaselines.controls_count xs.length
  simp only [_root_.Integration9_9.TM2NativeEmitterData.loadData,_root_.Integration9_9.TM2NativeEmitterData.nativeContext,_root_.Integration9_9.TM2NativeEmitterData.roots]
  rw [_p2mH309,_p2mH295,_p2mH296]
  simp only [_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativePermutationDraw.cacheData,List.length_ofFn,_root_.Integration9_9.TM2NativeEmitterLoads.nativeData]
  congr 2 <;> try omega
  apply Prod.ext <;> omega
open _root_.P2Mba49f952 renaming h292 → _p2mH292
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h293 (xs : List Unit) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache xs.length)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result xs.length) :
    _root_.Integration9_9.TM2NativeEmitterData.offsetData (_root_.Integration9_9.TM2NativeEmitterData.nativeContext xs layout sample)=
      _root_.Integration9_9.TM2NativeEmitterOffset.nativeData xs.length sample.core
        ⟨false,(_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits⟩
        (_root_.CurrentAFT.CurrentBinaryChartData.shiftArray xs.length sample.core).value
        (_root_.CurrentAFT.CurrentBinaryChartData.fieldArray xs.length sample.charts (fun chart=>chart.2.1)).value
        (_root_.CurrentAFT.CurrentEmissionRootOrder.positions xs.length layout sample.core).value
        (_root_.CurrentAFT.CurrentPublicShiftProgram.encode sample.edge.val).value := by
  have hm : (⟨false,(_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits⟩ : _root_.AFT.BinaryArithmetic.IntegerBits).decode=
      (_root_.Integration9_9.TM2NativePrime.modulus xs : ℤ) := by
    simp only [_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,Bool.false_eq_true,ite_false,_root_.AFT.BinaryArithmetic.canonicalCounter_value,_root_.Integration9_9.TM2NativePrime.modulus_native]
  simp only [_root_.Integration9_9.TM2NativeEmitterData.offsetData,_root_.Integration9_9.TM2NativeEmitterData.nativeContext,_root_.Integration9_9.TM2NativeEmitterData.roots]
  rw [_p2mH309,_p2mH297,_p2mH291]
  simp only [_root_.Integration9_9.TM2NativeEmitterOffset.nativeData,hm,_root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value]
open _root_.P2Mba49f952 renaming h293 → _p2mH293
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h294 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) :
    _root_.Integration9_9.TM2NativeEmitterData.permutation (_root_.Integration9_9.TM2NativeCoreProposal.coreData core)=_root_.Integration9_9.TM2NativeEmitterColumns.permutationData (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeEmitterData.permutation,_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativePermutationDraw.cacheData,_root_.Integration9_9.TM2NativeEmitterColumns.permutationData,List.length_ofFn]
    exact (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.1.symm
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeEmitterData.permutation,_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativePermutationDraw.cacheData,_root_.Integration9_9.TM2NativeEmitterColumns.permutationData,List.getElem_ofFn,
      _root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation,_root_.AFT.BinaryArithmetic.storeData_get,_root_.AFT.BinaryArithmetic.readVector_value,Fin.val_cast]
    rfl
open _root_.P2Mba49f952 renaming h294 → _p2mH294
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h289 (xs : List Unit) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore xs.length)
    (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts xs.length) :
    _root_.Integration9_9.TM2NativeEmitterData.guard ((xs,_root_.Integration9_9.TM2NativeCoreProposal.coreData core),_root_.Integration9_9.TM2NativeEmitterData.chartsData charts)=(_root_.CurrentAFT.CurrentBinaryAffineGuard.current xs.length core charts).value := by
  apply Bool.eq_iff_iff.mpr
  simp only [_root_.Integration9_9.TM2NativeEmitterData.guard,_p2mH261,Bool.and_eq_true,
    _root_.CurrentAFT.CurrentBinaryAffineGuard.current,_root_.CurrentAFT.BinaryProposalGuard.allFin_value,_p2mH102,
    _root_.Integration9_9.TM2NativeEmitterData.chartsData,_root_.Integration9_9.TM2NativeEmitterData.chartData,List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,decide_eq_true_eq,
    ne_eq,ZMod.val_eq_zero]
open _root_.P2Mba49f952 renaming h289 → _p2mH289
end Integration9_9.TM2NativeEmitterData
open _root_.P2Mba49f952 renaming h289 → _p2mH289
open _root_.P2Mba49f952 renaming h290 → _p2mH290
open _root_.P2Mba49f952 renaming h291 → _p2mH291
open _root_.P2Mba49f952 renaming h292 → _p2mH292
open _root_.P2Mba49f952 renaming h293 → _p2mH293
open _root_.P2Mba49f952 renaming h294 → _p2mH294
open _root_.P2Mba49f952 renaming h295 → _p2mH295
open _root_.P2Mba49f952 renaming h296 → _p2mH296
open _root_.P2Mba49f952 renaming h297 → _p2mH297
open _root_.P2Mba49f952 renaming h439 → Integration9_9.TM2NativeEmitterData.range_map
open _root_.P2Mba49f952 renaming h439 → _p2mH439
end
open _root_.P2Mba49f952 renaming h289 → _p2mH289
open _root_.P2Mba49f952 renaming h290 → _p2mH290
open _root_.P2Mba49f952 renaming h291 → _p2mH291
open _root_.P2Mba49f952 renaming h292 → _p2mH292
open _root_.P2Mba49f952 renaming h293 → _p2mH293
open _root_.P2Mba49f952 renaming h294 → _p2mH294
open _root_.P2Mba49f952 renaming h295 → _p2mH295
open _root_.P2Mba49f952 renaming h296 → _p2mH296
open _root_.P2Mba49f952 renaming h297 → _p2mH297
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitterAssembly
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal TM2NativeEmitterData TM2NativeEmitterColumns
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  TM2NativePrime.modulus TM2NativeEmitterData.loadData TM2NativeEmitterData.offsetData
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h278 (security : ℕ) (modulus : List Bool)
    (injection initial : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security))
    (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security))
    (permutation : Vector (Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security))
    (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus) :
    _root_.Integration9_9.TM2NativeEmitterColumns.current ((_root_.AFT.BinaryArithmetic.value modulus,_root_.Integration9_9.TM2NativeEmitterColumns.integerData injection),
      ((List.ofFn (fun i=>_root_.Integration9_9.TM2NativeEmitterColumns.integerData (matrix.get i)),_root_.Integration9_9.TM2NativeEmitterColumns.integerData initial),_root_.Integration9_9.TM2NativeEmitterColumns.permutationData permutation))=
      (List.ofFn (fun i=>_root_.Integration9_9.TM2NativeEmitterColumns.pack (_root_.Integration9_9.TM2NativeEmitterColumns.coordinateData
        (_root_.AFT.BinaryArithmetic.binaryAffineColumn (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges modulus injection matrix permutation i).value)),
      _root_.Integration9_9.TM2NativeEmitterColumns.pack (_root_.Integration9_9.TM2NativeEmitterColumns.coordinateData
        ((_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges modulus injection
          (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad security initial permutation).value).edges,
         (_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges modulus injection
          (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad security initial permutation).value).charge))) := by
  simp only [_root_.Integration9_9.TM2NativeEmitterColumns.current,List.map_ofFn,Function.comp_def]
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    rw [_p2mH280 _ _ _ _ _ _ hq]
  · rw [_p2mH281 _ _ _ _ _ hq]
open _root_.P2Mba49f952 renaming h278 → _p2mH278
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h279 (xs : List Unit) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache xs.length)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result xs.length) :
    _root_.Integration9_9.TM2NativeEmitterAssembly.current (_root_.Integration9_9.TM2NativeEmitterData.nativeContext xs layout sample)=_root_.Integration9_9.TM2NativeEmitterAssembly.outputData (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled xs.length layout sample) := by
  have hq : 0 < _root_.AFT.BinaryArithmetic.value (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits := by
    rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value,_root_.CurrentAFT.PublicParameterProgram.modulus_value]
    exact (_root_.CurrentAFT.Parameters.modulus_spec xs.length).2.pos
  have hm : _root_.Integration9_9.TM2NativePrime.modulus xs=_root_.AFT.BinaryArithmetic.value (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits := by
    rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value,_root_.Integration9_9.TM2NativePrime.modulus_native]
  unfold _root_.Integration9_9.TM2NativeEmitterAssembly.current _root_.Integration9_9.TM2NativeEmitterAssembly.fields
  rw [_p2mH292,_p2mH293,_p2mH299,_p2mH303]
  simp only [_root_.Integration9_9.TM2NativeEmitterData.nativeContext]
  rw [_p2mH290,_p2mH294,hm]
  have hc := _p2mH278 xs.length (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits
    (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.injection xs.length).value
    (_root_.CurrentAFT.CurrentBinaryOffsetLoad.load xs.length sample.core
      ⟨false,(_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count).digits⟩
      (_root_.CurrentAFT.CurrentBinaryChartData.shiftArray xs.length sample.core).value
      (_root_.CurrentAFT.CurrentBinaryChartData.fieldArray xs.length sample.charts (fun chart=>chart.2.1)).value
      (_root_.CurrentAFT.CurrentEmissionRootOrder.positions xs.length layout sample.core).value
      (_root_.CurrentAFT.CurrentPublicShiftProgram.encode sample.edge.val).value).value
    (_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix xs.length
      (_root_.CurrentAFT.CurrentBinaryChartData.fieldArray xs.length sample.charts (fun chart=>chart.2.2.1)).value
      (_root_.CurrentAFT.CurrentBinaryChartData.fieldArray xs.length sample.charts (fun chart=>chart.2.2.2)).value
      (_root_.CurrentAFT.CurrentEmissionRootOrder.positions xs.length layout sample.core).value).value
    (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation xs.length sample.core).value hq
  exact hc.trans (by simp only [_root_.Integration9_9.TM2NativeEmitterAssembly.outputData,_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled,_root_.AFT.BinaryArithmetic.storeData_get])
open _root_.P2Mba49f952 renaming h279 → _p2mH279
end Integration9_9.TM2NativeEmitterAssembly
open _root_.P2Mba49f952 renaming h278 → _p2mH278
open _root_.P2Mba49f952 renaming h279 → _p2mH279
end
open _root_.P2Mba49f952 renaming h278 → _p2mH278
open _root_.P2Mba49f952 renaming h279 → _p2mH279
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitter
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal TM2NativeEmitterData TM2NativeEmitterColumns TM2NativeEmitterAssembly
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  dimensionTicks TM2NativeEmitterAssembly.current TM2NativeEmitterData.guard
  CurrentBinaryAffineEmitter.emit CurrentBinaryAffineEmitter.assembled CurrentBinaryAffineEmitter.fallback
  CurrentBinaryAffineGuard.current
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h436 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h436 → Integration9_9.TM2NativeEmitter.range_map
open _root_.P2Mba49f952 renaming h436 → _p2mH436
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h435 (p : Prop) [Decidable p] (a b : _root_.AFT.BinaryArithmetic.IntegerBits) :
    (if p then a else b).decode=if p then a.decode else b.decode := by split_ifs <;> rfl
open _root_.P2Mba49f952 renaming h435 → _p2mH435
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h277 (xs : List Unit) :
    _root_.Integration9_9.TM2NativeEmitter.fallback xs=_root_.Integration9_9.TM2NativeEmitterAssembly.outputData (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback xs.length) := by
  have hn : (_root_.Integration9_9.TM2NativeCoreProposal.dimensionTicks xs).length=(_root_.CurrentAFT.CurrentEmissionMetadata.current xs.length).edges+1 :=
    (_p2mH269 xs).trans (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts xs.length).2.1.symm
  have hz : (_root_.Integration9_9.TM2NativeCoreProposal.dimensionTicks xs).map (fun _=>(0 : ℤ))=List.ofFn (fun _ : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current xs.length).edges+1)=>(0 : ℤ)) := by
    simp only [List.map_const',List.ofFn_const,hn]
  simp only [_root_.Integration9_9.TM2NativeEmitter.fallback,hn,_p2mH436,hz,_root_.Integration9_9.TM2NativeEmitterAssembly.outputData,_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback,_root_.AFT.BinaryArithmetic.storeData_get,
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn,_root_.Integration9_9.TM2NativeEmitterColumns.pack,_root_.Integration9_9.TM2NativeEmitterColumns.coordinateData,_root_.AFT.BinaryArithmetic.IntegerBits.zero_value,
    _p2mH435,_root_.AFT.BinaryArithmetic.equalCounter_value,_root_.AFT.BinaryArithmetic.IntegerBits.one_value]
  apply Prod.ext
  · apply congrArg List.ofFn
    funext column
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append,Fin.val_castSucc,Fin.val_last,eq_comm]
  · simpa only [List.concat_eq_append] using
      (List.ofFn_succ' (fun _ : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current xs.length).edges+1)=>(0 : ℤ)))
open _root_.P2Mba49f952 renaming h277 → _p2mH277
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h276 (xs : List Unit) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache xs.length)
    (sample : Option (_root_.CurrentAFT.CurrentMaterializedCompletion.Result xs.length)) :
    _root_.Integration9_9.TM2NativeEmitter.current ((xs,(_root_.Integration9_9.TM2NativePermutationDraw.cacheData layout).1),_root_.Integration9_9.TM2NativeEmitter.resultData sample)=
      _root_.Integration9_9.TM2NativeEmitterAssembly.outputData (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit xs.length layout sample) := by
  cases sample with
  | none => simp only [_root_.Integration9_9.TM2NativeEmitter.current,_root_.Integration9_9.TM2NativeEmitter.resultData,Bool.false_and,Bool.false_eq_true,ite_false,_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit,_p2mH277]
  | some sample =>
    by_cases ht : (_root_.CurrentAFT.CurrentBinaryAffineGuard.current xs.length sample.core sample.charts).value=true
    · have hv := (_p2mH101 xs.length sample.core sample.charts).mp ht
      have he := _p2mH100 xs.length layout sample hv
      have hd : _root_.Integration9_9.TM2NativeEmitterAssembly.outputData (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit xs.length layout (some sample))=
          _root_.Integration9_9.TM2NativeEmitterAssembly.outputData (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled xs.length layout sample) := by
        simp only [_root_.Integration9_9.TM2NativeEmitterAssembly.outputData,he.1,he.2]
      rw [hd]
      simp only [_root_.Integration9_9.TM2NativeEmitter.current,_root_.Integration9_9.TM2NativeEmitter.resultData,Bool.true_and,_p2mH289,if_pos ht]
      exact _p2mH279 xs layout sample
    · have hv : ¬_root_.CurrentAFT.CurrentAffineData.Valid xs.length sample.core.core sample.charts.get := by
        intro hv
        exact ht ((_p2mH101 xs.length sample.core sample.charts).mpr hv)
      have he := _p2mH99 xs.length layout sample hv
      have hd : _root_.Integration9_9.TM2NativeEmitterAssembly.outputData (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit xs.length layout (some sample))=
          _root_.Integration9_9.TM2NativeEmitterAssembly.outputData (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback xs.length) := by
        simp only [_root_.Integration9_9.TM2NativeEmitterAssembly.outputData,he.1,he.2]
      rw [hd]
      simp only [_root_.Integration9_9.TM2NativeEmitter.current,_root_.Integration9_9.TM2NativeEmitter.resultData,Bool.true_and,_p2mH289,if_neg ht]
      exact _p2mH277 xs
open _root_.P2Mba49f952 renaming h276 → _p2mH276
end Integration9_9.TM2NativeEmitter
open _root_.P2Mba49f952 renaming h276 → _p2mH276
open _root_.P2Mba49f952 renaming h277 → _p2mH277
open _root_.P2Mba49f952 renaming h435 → _p2mH435
open _root_.P2Mba49f952 renaming h436 → Integration9_9.TM2NativeEmitter.range_map
open _root_.P2Mba49f952 renaming h436 → _p2mH436
end
open _root_.P2Mba49f952 renaming h276 → _p2mH276
open _root_.P2Mba49f952 renaming h277 → _p2mH277
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeEmitterOutput
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal TM2NativeEmitterData TM2NativeEmitterColumns TM2NativeEmitterAssembly
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  dimensionTicks CurrentAFT.Parameters.dimension CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.legCount
  CurrentBinaryAffineEmitter.decodeCoordinate CurrentBinaryAffineEmitter.matrix CurrentBinaryAffineEmitter.offset
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h443 {α : Type} (n : ℕ) (f : Fin n→α) (i : Fin n) (zero : α) :
    (List.ofFn f)[i.val]?.getD zero=f i := by
  simp only [List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
open _root_.P2Mba49f952 renaming h443 → _p2mH443
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h306 (security : ℕ) (point : _root_.CurrentAFT.CurrentBinaryAffineEmitter.Coordinate security)
    (row : Fin (_root_.CurrentAFT.Parameters.dimension security)) :
    (_root_.Integration9_9.TM2NativeEmitterColumns.pack (_root_.Integration9_9.TM2NativeEmitterColumns.coordinateData point))[row.val]?.getD 0=_root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security point row := by
  obtain ⟨edge|unit,rfl⟩ := (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).surjective row
  · have hn : (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (Sum.inl edge)).val=edge.val := rfl
    rw [hn]
    have hi : edge.val<(_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges := by
      rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1]
      exact edge.isLt
    simp only [_root_.Integration9_9.TM2NativeEmitterColumns.pack,_root_.Integration9_9.TM2NativeEmitterColumns.coordinateData,List.getElem?_append,List.length_ofFn,hi,if_pos,List.getElem?_ofFn,hi,dif_pos,Option.getD_some,
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate,_root_.CurrentAFT.CurrentAffineLoad.packSource,Equiv.symm_apply_apply,Sum.elim_inl]
    rfl
  · cases unit
    have hn : (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (Sum.inr ())).val=_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security := rfl
    rw [hn]
    have he := (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1
    simp only [_root_.Integration9_9.TM2NativeEmitterColumns.pack,_root_.Integration9_9.TM2NativeEmitterColumns.coordinateData,List.getElem?_append,List.length_ofFn,he,lt_self_iff_false,if_false,Nat.sub_self,
      List.getElem?_cons_zero,Option.getD_some,_root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate,_root_.CurrentAFT.CurrentAffineLoad.packSource,
      Equiv.symm_apply_apply,Sum.elim_inr]
open _root_.P2Mba49f952 renaming h306 → _p2mH306
attribute [local irreducible] indices
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h308 (xs : List Unit) (data : _root_.CurrentAFT.CurrentBinaryAffineEmitter.Data xs.length)
    (row column : Fin (_root_.CurrentAFT.Parameters.dimension xs.length)) :
    _root_.Integration9_9.TM2NativeEmitterOutput.entry ((xs,_root_.Integration9_9.TM2NativeEmitterAssembly.outputData data),(row.val,column.val))=_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix xs.length data row column := by
  let selected := (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv xs.length).symm column
  have hc : column.val=selected.val := rfl
  simp only [_root_.Integration9_9.TM2NativeEmitterOutput.entry,_root_.Integration9_9.TM2NativeEmitterAssembly.outputData]
  rw [hc,_p2mH443 _ _ selected]
  simpa only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix] using _p2mH306 xs.length (data.columns.get selected) row
open _root_.P2Mba49f952 renaming h308 → _p2mH308
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h444 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h444 → Integration9_9.TM2NativeEmitterOutput.range_map
open _root_.P2Mba49f952 renaming h444 → _p2mH444
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h307 (xs : List Unit) (data : _root_.CurrentAFT.CurrentBinaryAffineEmitter.Data xs.length) :
    _root_.Integration9_9.TM2NativeEmitterOutput.current (xs,_root_.Integration9_9.TM2NativeEmitterAssembly.outputData data)=
      (List.ofFn (fun row=>List.ofFn (fun column=>_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix xs.length data row column)),
        List.ofFn (fun row=>_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset xs.length data row)) := by
  simp only [_root_.Integration9_9.TM2NativeEmitterOutput.current,_root_.Integration9_9.TM2NativeEmitterOutput.row,_root_.Integration9_9.TM2NativeEmitterOutput.indices,_p2mH269,(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.2.2.1,_p2mH444]
  apply Prod.ext
  · dsimp only [Prod.fst,Prod.snd]
    apply congrArg List.ofFn
    funext row
    apply congrArg List.ofFn
    funext column
    exact _p2mH308 xs data row column
  · dsimp only [Prod.fst,Prod.snd]
    apply congrArg List.ofFn
    funext row
    simpa only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset,_root_.Integration9_9.TM2NativeEmitterAssembly.outputData] using _p2mH306 xs.length data.offset row
open _root_.P2Mba49f952 renaming h307 → _p2mH307
end Integration9_9.TM2NativeEmitterOutput
open _root_.P2Mba49f952 renaming h306 → _p2mH306
open _root_.P2Mba49f952 renaming h307 → _p2mH307
open _root_.P2Mba49f952 renaming h308 → _p2mH308
open _root_.P2Mba49f952 renaming h443 → _p2mH443
open _root_.P2Mba49f952 renaming h444 → Integration9_9.TM2NativeEmitterOutput.range_map
open _root_.P2Mba49f952 renaming h444 → _p2mH444
end
open _root_.P2Mba49f952 renaming h306 → _p2mH306
open _root_.P2Mba49f952 renaming h307 → _p2mH307
open _root_.P2Mba49f952 renaming h308 → _p2mH308
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineEmitter
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal TM2NativeEmitterData TM2NativeEmitterAssembly
open InfoLossLAR.WorstCase LARPlatformEncoding QAlgorithms.Complexity
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  CurrentAFT.Parameters.dimension CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.legCount
  TM2NativeEmitter.current TM2NativeEmitterOutput.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h220 {n : ℕ} (matrix : Matrix (Fin n) (Fin n) ℤ) (offset : Fin n→ℤ) :
    _root_.Integration9_9.TM2NativeAffineEmitter.serialize (List.ofFn (fun row=>List.ofFn (fun column=>matrix row column)),List.ofFn offset)=
      encPair (encMat encI matrix) (encVec encI offset) := by
  have hv (vector : Fin n→ℤ) : _root_.Integration9_9.TM2NativeAffineEmitter.serializeVector (List.ofFn vector)=encVec encI vector := by
    simp only [_root_.Integration9_9.TM2NativeAffineEmitter.serializeVector,_root_.Integration9_9.LARPlatformEncoding.serializeBinaryWords_map,encVec]
  have hm : _root_.Integration9_9.TM2NativeAffineEmitter.serializeMatrix (List.ofFn (fun row=>List.ofFn (fun column=>matrix row column)))=encMat encI matrix := by
    simp only [_root_.Integration9_9.TM2NativeAffineEmitter.serializeMatrix,List.map_ofFn,Function.comp_def,hv]
    simpa only [List.map_ofFn,Function.comp_def,encMat] using _root_.Integration9_9.LARPlatformEncoding.serializeBinaryWords_map (encVec encI) (List.ofFn matrix)
  exact congrArg₂ encPair hm (hv offset)
open _root_.P2Mba49f952 renaming h220 → _p2mH220
end Integration9_9.TM2NativeAffineEmitter
open _root_.P2Mba49f952 renaming h220 → _p2mH220
end
open _root_.P2Mba49f952 renaming h220 → _p2mH220
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeTapeCodec
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h365 (first second : ℕ) (word : Fin (first+second)→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCodec.take (first,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCodec.wordData (fun i : Fin first=>word (finSumFinEquiv (Sum.inl i))) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeTapeCodec.take,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.length_take,List.length_ofFn]
    omega
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeTapeCodec.take,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.getElem_take,List.getElem_ofFn]
    rfl
open _root_.P2Mba49f952 renaming h365 → _p2mH365
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h362 (first second : ℕ) (word : Fin (first+second)→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCodec.drop (first,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCodec.wordData (fun i : Fin second=>word (finSumFinEquiv (Sum.inr i))) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeTapeCodec.drop,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.length_drop,List.length_ofFn,Nat.add_sub_cancel_left]
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeTapeCodec.drop,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.getElem_drop,List.getElem_ofFn]
    rfl
open _root_.P2Mba49f952 renaming h362 → _p2mH362
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h364 {A B α β : Type} (first : _root_.CurrentAFT.PublicBitTapes.Encoding A) (second : _root_.CurrentAFT.PublicBitTapes.Encoding B)
    (da : _root_.Integration9_9.TM2NativeTapeCodec.Word→α) (db : _root_.Integration9_9.TM2NativeTapeCodec.Word→β) (ea : A→α) (eb : B→β)
    (ha : ∀ word,da (_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=ea (first.equiv word))
    (hb : ∀ word,db (_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=eb (second.equiv word))
    (word : Fin (first.bits+second.bits)→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCodec.product first.bits da db (_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      (ea ((first.prod second).equiv word).1,eb ((first.prod second).equiv word).2) := by
  simp only [_root_.Integration9_9.TM2NativeTapeCodec.product,_p2mH365,_p2mH362,ha,hb]
  rfl
open _root_.P2Mba49f952 renaming h364 → _p2mH364
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h363 (word : Fin 1→Fin 2) : _root_.Integration9_9.TM2NativeTapeCodec.flag (_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.CurrentAFT.PublicBitTapes.flag.equiv word := by
  simp only [_root_.Integration9_9.TM2NativeTapeCodec.flag,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.ofFn_succ,List.headD_cons,_root_.CurrentAFT.PublicBitTapes.flag]
  change _root_.AFT.BinaryArithmetic.digitBoolean (word 0)=finTwoEquiv (word 0)
  generalize hx : word 0=bit
  fin_cases bit <;> rfl
open _root_.P2Mba49f952 renaming h363 → _p2mH363
end Integration9_9.TM2NativeTapeCodec
open _root_.P2Mba49f952 renaming h362 → _p2mH362
open _root_.P2Mba49f952 renaming h363 → _p2mH363
open _root_.P2Mba49f952 renaming h364 → _p2mH364
open _root_.P2Mba49f952 renaming h365 → _p2mH365
end
open _root_.P2Mba49f952 renaming h362 → _p2mH362
open _root_.P2Mba49f952 renaming h363 → _p2mH363
open _root_.P2Mba49f952 renaming h364 → _p2mH364
open _root_.P2Mba49f952 renaming h365 → _p2mH365
section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeTapeLengths
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
  TM2NativePrime.modulus TM2NativeProfile.widthTicks TM2NativeBodyKernel.paletteTicks
  TM2NativeReferenceDraw.safeTicks TM2NativeProfile.edgeTicks bodyTicks legTicks dimensionTicks
  TM2NativeFullResponseCounts.slots BinaryPublicBitSizes.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h390 (xs : List Unit) :
    (_root_.Integration9_9.TM2NativeTapeLengths.controlsTicks xs).length=(_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).controls := by
  simp only [_root_.Integration9_9.TM2NativeTapeLengths.controlsTicks,List.length_append,_p2mH271,_root_.Integration9_9.TM2NativeFullResponseCounts.slots_native_length]
  change (_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).legs+(_root_.CurrentAFT.BinaryFullResponseCounts.current xs.length).ordinary=_
  rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.1,(_root_.CurrentAFT.BinaryFullResponseCounts.current_value xs.length).2.1,
    (_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.2.2.2.2]
open _root_.P2Mba49f952 renaming h390 → _p2mH390
attribute [local irreducible] controlsTicks
attribute [local irreducible] activation control safe anchor edge chart body endpoint
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h385 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeLengths.activation xs=(_root_.CurrentAFT.BinaryPublicBitSizes.current xs.length).activation := by
  rw [_root_.Integration9_9.TM2NativeTapeLengths.activation,_root_.CurrentAFT.BinaryPublicBitSizes.activation_value]
open _root_.P2Mba49f952 renaming h385 → _p2mH385
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h389 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeLengths.control xs=(_root_.CurrentAFT.BinaryPublicBitSizes.current xs.length).control := by
  rw [_root_.Integration9_9.TM2NativeTapeLengths.control,_root_.CurrentAFT.BinaryPublicBitSizes.control_value,_root_.Integration9_9.TM2NativePrime.modulus_native]
open _root_.P2Mba49f952 renaming h389 → _p2mH389
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h394 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeLengths.safe xs=(_root_.CurrentAFT.BinaryPublicBitSizes.current xs.length).safe := by
  rw [_root_.Integration9_9.TM2NativeTapeLengths.safe,_root_.CurrentAFT.BinaryPublicBitSizes.safe_value,_p2mH351]
open _root_.P2Mba49f952 renaming h394 → _p2mH394
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h386 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeLengths.anchor xs=(_root_.CurrentAFT.BinaryPublicBitSizes.current xs.length).anchor := by
  rw [_root_.Integration9_9.TM2NativeTapeLengths.anchor,_root_.CurrentAFT.BinaryPublicBitSizes.anchor_value,_root_.Integration9_9.TM2NativeProfile.widthTicks_length,_root_.CurrentAFT.CurrentAnchorIndexDraw.width_value,_root_.CurrentAFT.DiffuseProfiles.anchorWidth_eq]
  rfl
open _root_.P2Mba49f952 renaming h386 → _p2mH386
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h391 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeLengths.edge xs=(_root_.CurrentAFT.BinaryPublicBitSizes.current xs.length).edge := by
  rw [_root_.Integration9_9.TM2NativeTapeLengths.edge,_root_.CurrentAFT.BinaryPublicBitSizes.edge_value,_root_.Integration9_9.TM2NativeProfile.edgeTicks_length]
  rfl
open _root_.P2Mba49f952 renaming h391 → _p2mH391
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h388 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeLengths.chart xs=(_root_.CurrentAFT.BinaryPublicBitSizes.current xs.length).chart := by
  rw [_root_.Integration9_9.TM2NativeTapeLengths.chart,_root_.CurrentAFT.BinaryPublicBitSizes.chart_value,_root_.Integration9_9.TM2NativePrime.modulus_value]
open _root_.P2Mba49f952 renaming h388 → _p2mH388
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h387 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeLengths.body xs=(_root_.CurrentAFT.BinaryPublicBitSizes.current xs.length).body := by
  rw [_root_.Integration9_9.TM2NativeTapeLengths.body,_root_.CurrentAFT.BinaryPublicBitSizes.body_value,_p2mH266]
open _root_.P2Mba49f952 renaming h387 → _p2mH387
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h392 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeLengths.endpoint xs=(_root_.CurrentAFT.BinaryPublicBitSizes.current xs.length).endpoint := by
  rw [_root_.Integration9_9.TM2NativeTapeLengths.endpoint,_root_.CurrentAFT.BinaryPublicBitSizes.endpoint_value,_p2mH269]
open _root_.P2Mba49f952 renaming h392 → _p2mH392
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h393 (xs : List Unit) :
    (_root_.Integration9_9.TM2NativeTapeLengths.retriesTicks xs).length=(_root_.CurrentAFT.BinaryRejectionCap.current xs.length).count := by
  simp only [_root_.Integration9_9.TM2NativeTapeLengths.retriesTicks,List.length_flatMap,List.map_const',List.sum_replicate,List.length_replicate,
    _root_.Integration9_9.TM2NativeBodyKernel.paletteTicks_length,_root_.CurrentAFT.BinaryRejectionCap.current_value]
  ring
open _root_.P2Mba49f952 renaming h393 → _p2mH393
end Integration9_9.TM2NativeTapeLengths
open _root_.P2Mba49f952 renaming h385 → _p2mH385
open _root_.P2Mba49f952 renaming h386 → _p2mH386
open _root_.P2Mba49f952 renaming h387 → _p2mH387
open _root_.P2Mba49f952 renaming h388 → _p2mH388
open _root_.P2Mba49f952 renaming h389 → _p2mH389
open _root_.P2Mba49f952 renaming h390 → _p2mH390
open _root_.P2Mba49f952 renaming h391 → _p2mH391
open _root_.P2Mba49f952 renaming h392 → _p2mH392
open _root_.P2Mba49f952 renaming h393 → _p2mH393
open _root_.P2Mba49f952 renaming h394 → _p2mH394
end
open _root_.P2Mba49f952 renaming h385 → _p2mH385
open _root_.P2Mba49f952 renaming h386 → _p2mH386
open _root_.P2Mba49f952 renaming h387 → _p2mH387
open _root_.P2Mba49f952 renaming h388 → _p2mH388
open _root_.P2Mba49f952 renaming h389 → _p2mH389
open _root_.P2Mba49f952 renaming h390 → _p2mH390
open _root_.P2Mba49f952 renaming h391 → _p2mH391
open _root_.P2Mba49f952 renaming h392 → _p2mH392
open _root_.P2Mba49f952 renaming h393 → _p2mH393
open _root_.P2Mba49f952 renaming h394 → _p2mH394
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeTapeSeed
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeTapeCodec
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
  BinaryPublicBitSizes.current TM2NativeTapeLengths.activation TM2NativeTapeLengths.control
  TM2NativeTapeLengths.safe TM2NativeTapeLengths.anchor TM2NativeTapeLengths.edge
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h396 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.control xs.length xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeSeed.control (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeCoreProposal.controlTapeData ((_root_.CurrentAFT.PublicBitTapes.control xs.length xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeSeed.control _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH389,_root_.CurrentAFT.BinaryPublicBitSizes.control_value]
  exact _p2mH364 (_root_.CurrentAFT.PublicBitTapes.bits (xs.length+(_root_.CurrentAFT.PublicParameterProgram.modulus xs.length).count+1))
    (_root_.CurrentAFT.PublicBitTapes.safe xs.length xs.length) id id _root_.Integration9_9.TM2NativeTapeCodec.wordData _root_.Integration9_9.TM2NativeTapeCodec.wordData (fun _=>rfl) (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h396 → _p2mH396
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h397 (xs : List Unit)
    (word : Fin ((_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length).prod (_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length)).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeSeed.edgePair (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      (_root_.Integration9_9.TM2NativeTapeCodec.wordData (((_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length).prod (_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length)).equiv word).1,
       _root_.Integration9_9.TM2NativeTapeCodec.wordData (((_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length).prod (_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length)).equiv word).2) := by
  unfold _root_.Integration9_9.TM2NativeTapeSeed.edgePair _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH391,_root_.CurrentAFT.BinaryPublicBitSizes.edge_value]
  exact _p2mH364 (_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length) (_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length)
    id id _root_.Integration9_9.TM2NativeTapeCodec.wordData _root_.Integration9_9.TM2NativeTapeCodec.wordData (fun _=>rfl) (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h397 → _p2mH397
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h395 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapeSeed.anchorEdgesEncoding xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeSeed.anchorEdges (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      (_root_.Integration9_9.TM2NativeTapeCodec.wordData ((_root_.Integration9_9.TM2NativeTapeSeed.anchorEdgesEncoding xs.length).equiv word).1,
        (_root_.Integration9_9.TM2NativeTapeCodec.wordData ((_root_.Integration9_9.TM2NativeTapeSeed.anchorEdgesEncoding xs.length).equiv word).2.1,
          _root_.Integration9_9.TM2NativeTapeCodec.wordData ((_root_.Integration9_9.TM2NativeTapeSeed.anchorEdgesEncoding xs.length).equiv word).2.2)) := by
  unfold _root_.Integration9_9.TM2NativeTapeSeed.anchorEdges _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH386,_root_.CurrentAFT.BinaryPublicBitSizes.anchor_value]
  exact _p2mH364 (_root_.Integration9_9.TM2NativeTapeSeed.anchorEncoding xs.length) (_root_.Integration9_9.TM2NativeTapeSeed.edgesEncoding xs.length)
    id (fun word=>_root_.Integration9_9.TM2NativeTapeSeed.edgePair (xs,word)) _root_.Integration9_9.TM2NativeTapeCodec.wordData (fun p=>(_root_.Integration9_9.TM2NativeTapeCodec.wordData p.1,_root_.Integration9_9.TM2NativeTapeCodec.wordData p.2))
    (fun _=>rfl) (_p2mH397 xs) word
open _root_.P2Mba49f952 renaming h395 → _p2mH395
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h398 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapeSeed.flagAnchorEncoding xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeSeed.flagAnchor (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      (((_root_.Integration9_9.TM2NativeTapeSeed.flagAnchorEncoding xs.length).equiv word).1,
        (_root_.Integration9_9.TM2NativeTapeCodec.wordData ((_root_.Integration9_9.TM2NativeTapeSeed.flagAnchorEncoding xs.length).equiv word).2.1,
          (_root_.Integration9_9.TM2NativeTapeCodec.wordData ((_root_.Integration9_9.TM2NativeTapeSeed.flagAnchorEncoding xs.length).equiv word).2.2.1,
            _root_.Integration9_9.TM2NativeTapeCodec.wordData ((_root_.Integration9_9.TM2NativeTapeSeed.flagAnchorEncoding xs.length).equiv word).2.2.2))) := by
  exact _p2mH364 _root_.CurrentAFT.PublicBitTapes.flag (_root_.Integration9_9.TM2NativeTapeSeed.anchorEdgesEncoding xs.length)
    _root_.Integration9_9.TM2NativeTapeCodec.flag (fun word=>_root_.Integration9_9.TM2NativeTapeSeed.anchorEdges (xs,word)) id
    (fun p=>(_root_.Integration9_9.TM2NativeTapeCodec.wordData p.1,(_root_.Integration9_9.TM2NativeTapeCodec.wordData p.2.1,_root_.Integration9_9.TM2NativeTapeCodec.wordData p.2.2))) _p2mH363 (_p2mH395 xs) word
open _root_.P2Mba49f952 renaming h398 → _p2mH398
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h401 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.seed xs.length xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeSeed.seed (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativePublicSeed.tapeData ((_root_.CurrentAFT.PublicBitTapes.seed xs.length xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeSeed.seed _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH385,_root_.CurrentAFT.BinaryPublicBitSizes.activation_value]
  exact _p2mH364 (_root_.CurrentAFT.PublicBitTapes.bits (xs.length+3)) (_root_.Integration9_9.TM2NativeTapeSeed.flagAnchorEncoding xs.length)
    id (fun word=>_root_.Integration9_9.TM2NativeTapeSeed.flagAnchor (xs,word)) _root_.Integration9_9.TM2NativeTapeCodec.wordData
    (fun p=>(p.1,(_root_.Integration9_9.TM2NativeTapeCodec.wordData p.2.1,(_root_.Integration9_9.TM2NativeTapeCodec.wordData p.2.2.1,_root_.Integration9_9.TM2NativeTapeCodec.wordData p.2.2.2))))
    (fun _=>rfl) (_p2mH398 xs) word
open _root_.P2Mba49f952 renaming h401 → _p2mH401
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h400 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeSeed.seedBits xs=(_root_.CurrentAFT.PublicBitTapes.seed xs.length xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeSeed.seedBits,_p2mH385,_p2mH386,_p2mH391,
    _root_.CurrentAFT.BinaryPublicBitSizes.activation_value,_root_.CurrentAFT.BinaryPublicBitSizes.anchor_value,_root_.CurrentAFT.BinaryPublicBitSizes.edge_value,
    _root_.CurrentAFT.PublicBitTapes.seed,_root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.bits,_root_.CurrentAFT.PublicBitTapes.flag,_root_.CurrentAFT.PublicBitTapes.edge]
open _root_.P2Mba49f952 renaming h400 → _p2mH400
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h399 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.leg xs.length xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeSeed.leg (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeCoreProposal.legTapeData ((_root_.CurrentAFT.PublicBitTapes.leg xs.length xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeSeed.leg _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH400]
  exact _p2mH364 (_root_.CurrentAFT.PublicBitTapes.seed xs.length xs.length) (_root_.CurrentAFT.PublicBitTapes.safe xs.length xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapeSeed.seed (xs,word)) id _root_.Integration9_9.TM2NativePublicSeed.tapeData _root_.Integration9_9.TM2NativeTapeCodec.wordData (_p2mH401 xs) (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h399 → _p2mH399
end Integration9_9.TM2NativeTapeSeed
open _root_.P2Mba49f952 renaming h395 → _p2mH395
open _root_.P2Mba49f952 renaming h396 → _p2mH396
open _root_.P2Mba49f952 renaming h397 → _p2mH397
open _root_.P2Mba49f952 renaming h398 → _p2mH398
open _root_.P2Mba49f952 renaming h399 → _p2mH399
open _root_.P2Mba49f952 renaming h400 → _p2mH400
open _root_.P2Mba49f952 renaming h401 → _p2mH401
end
open _root_.P2Mba49f952 renaming h395 → _p2mH395
open _root_.P2Mba49f952 renaming h396 → _p2mH396
open _root_.P2Mba49f952 renaming h397 → _p2mH397
open _root_.P2Mba49f952 renaming h398 → _p2mH398
open _root_.P2Mba49f952 renaming h399 → _p2mH399
open _root_.P2Mba49f952 renaming h400 → _p2mH400
open _root_.P2Mba49f952 renaming h401 → _p2mH401
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeTapeCore
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal TM2NativeTapeCodec
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
  PublicParameterProgram.modulus TM2NativeTapeLengths.controlsTicks TM2NativeBodyKernel.paletteTicks legTicks
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h447 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h447 → Integration9_9.TM2NativeTapeCore.range_map
open _root_.P2Mba49f952 renaming h447 → _p2mH447
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h373 (slots : List Unit) (count width : ℕ) (hn : slots.length=count)
    (word : Fin (count*width)→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCodec.groups ((slots,width),_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=List.ofFn (fun i=>_root_.Integration9_9.TM2NativeTapeCodec.wordData (_root_.AFT.FiniteConditionProgram.groupBits count width word i)) := by
  simp only [_root_.Integration9_9.TM2NativeTapeCodec.groups,hn,_p2mH447]
  apply congrArg List.ofFn
  funext i
  apply List.ext_getElem
  · have hm := Nat.mul_le_mul_right width (show i.val+1 ≤ count by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hm
    simp only [_root_.Integration9_9.TM2NativeTapeCodec.take,_root_.Integration9_9.TM2NativeTapeCodec.drop,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro j hj hk
    simp only [_root_.Integration9_9.TM2NativeTapeCodec.take,_root_.Integration9_9.TM2NativeTapeCodec.drop,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    change _root_.AFT.BinaryArithmetic.digitBoolean (word ⟨i.val*width+j,_⟩)=_root_.AFT.BinaryArithmetic.digitBoolean (word (finProdFinEquiv (i,⟨j,_⟩)))
    apply congrArg _root_.AFT.BinaryArithmetic.digitBoolean
    apply congrArg word
    apply Fin.ext
    change i.val*width+j=j+width*i.val
    simp only [Nat.mul_comm,Nat.add_comm]
open _root_.P2Mba49f952 renaming h373 → _p2mH373
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h374 {Index State α : Type} (slots : List Unit) (count : ℕ) (hn : slots.length=count)
    (ordering : Fin count≃Index) (encoding : _root_.CurrentAFT.PublicBitTapes.Encoding State) (decode : _root_.Integration9_9.TM2NativeTapeCodec.Word→α) (encode : State→α)
    (ha : ∀ word,decode (_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=encode (encoding.equiv word))
    (word : Fin (count*encoding.bits)→Fin 2) :
    (_root_.Integration9_9.TM2NativeTapeCodec.groups ((slots,encoding.bits),_root_.Integration9_9.TM2NativeTapeCodec.wordData word)).map decode=
      List.ofFn (fun i=>encode (((encoding.indexed ordering).equiv word) (ordering i))) := by
  simp only [_p2mH373 slots count _ hn,List.map_ofFn,Function.comp_def,ha]
  apply congrArg List.ofFn
  funext i
  change encode (encoding.equiv (_root_.AFT.FiniteConditionProgram.groupBits count encoding.bits word i))=
    encode (encoding.equiv (_root_.AFT.FiniteConditionProgram.groupBits count encoding.bits word (ordering.symm (ordering i))))
  rw [Equiv.symm_apply_apply]
open _root_.P2Mba49f952 renaming h374 → _p2mH374
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h366 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.controlBits xs=(_root_.CurrentAFT.PublicBitTapes.control xs.length xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.controlBits,_p2mH389,_p2mH394,
    _root_.CurrentAFT.BinaryPublicBitSizes.control_value,_root_.CurrentAFT.BinaryPublicBitSizes.safe_value,_root_.CurrentAFT.PublicBitTapes.control,_root_.CurrentAFT.PublicBitTapes.safe,
    _root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.bits]
open _root_.P2Mba49f952 renaming h366 → _p2mH366
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h375 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.legBits xs=(_root_.CurrentAFT.PublicBitTapes.leg xs.length xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.legBits,_p2mH400,_p2mH394,
    _root_.CurrentAFT.BinaryPublicBitSizes.safe_value,_root_.CurrentAFT.PublicBitTapes.leg,_root_.CurrentAFT.PublicBitTapes.safe,_root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.bits]
open _root_.P2Mba49f952 renaming h375 → _p2mH375
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h370 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapeCore.controlsEncoding xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCore.controls (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCore.controlsData xs.length ((_root_.Integration9_9.TM2NativeTapeCore.controlsEncoding xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeCore.controls _root_.Integration9_9.TM2NativeTapeCodec.indexedWith
  rw [_p2mH366]
  exact _p2mH374 (_root_.Integration9_9.TM2NativeTapeLengths.controlsTicks xs) _ (_p2mH390 xs)
    (_root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv xs.length) (_root_.CurrentAFT.PublicBitTapes.control xs.length xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapeSeed.control (xs,word)) _root_.Integration9_9.TM2NativeCoreProposal.controlTapeData (_p2mH396 xs) word
open _root_.P2Mba49f952 renaming h370 → _p2mH370
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h377 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapeCore.legsEncoding xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCore.legs (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCore.legsData xs.length ((_root_.Integration9_9.TM2NativeTapeCore.legsEncoding xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeCore.legs _root_.Integration9_9.TM2NativeTapeCodec.indexedWith
  rw [_p2mH375]
  exact _p2mH374 (_root_.Integration9_9.TM2NativeCoreProposal.legTicks xs) _ (_p2mH271 xs)
    (_root_.CurrentAFT.CurrentProposalDimensions.legEquiv xs.length) (_root_.CurrentAFT.PublicBitTapes.leg xs.length xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapeSeed.leg (xs,word)) _root_.Integration9_9.TM2NativeCoreProposal.legTapeData (_p2mH399 xs) word
open _root_.P2Mba49f952 renaming h377 → _p2mH377
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h379 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapeCore.queuesEncoding xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCore.queues (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCore.queuesData xs.length ((_root_.Integration9_9.TM2NativeTapeCore.queuesEncoding xs.length).equiv word) := by
  have hn : (_root_.Integration9_9.TM2NativeBodyKernel.paletteTicks xs).length=(_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).colors := by
    rw [_root_.Integration9_9.TM2NativeBodyKernel.paletteTicks_length,(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).1]
  unfold _root_.Integration9_9.TM2NativeTapeCore.queues _root_.Integration9_9.TM2NativeTapeCodec.indexedWith
  rw [_p2mH394,_root_.CurrentAFT.BinaryPublicBitSizes.safe_value]
  exact _p2mH374 (_root_.Integration9_9.TM2NativeBodyKernel.paletteTicks xs) _ hn
    (_root_.CurrentAFT.CurrentProposalDimensions.queueEquiv xs.length) (_root_.CurrentAFT.PublicBitTapes.safe xs.length xs.length)
    id _root_.Integration9_9.TM2NativeTapeCodec.wordData (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h379 → _p2mH379
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h367 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.controlsBits xs=(_root_.Integration9_9.TM2NativeTapeCore.controlsEncoding xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.controlsBits,_root_.Integration9_9.TM2NativeTapeCore.controlsEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.indexed,_p2mH390,_p2mH366]
open _root_.P2Mba49f952 renaming h367 → _p2mH367
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h376 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.legsBits xs=(_root_.Integration9_9.TM2NativeTapeCore.legsEncoding xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.legsBits,_root_.Integration9_9.TM2NativeTapeCore.legsEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.indexed,_p2mH271,_p2mH375]
open _root_.P2Mba49f952 renaming h376 → _p2mH376
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h378 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.queuesBits xs=(_root_.Integration9_9.TM2NativeTapeCore.queuesEncoding xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.queuesBits,_root_.Integration9_9.TM2NativeTapeCore.queuesEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.indexed,_root_.Integration9_9.TM2NativeBodyKernel.paletteTicks_length,(_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).1,_p2mH394,_root_.CurrentAFT.BinaryPublicBitSizes.safe_value,_root_.CurrentAFT.PublicBitTapes.safe,_root_.CurrentAFT.PublicBitTapes.bits]
open _root_.P2Mba49f952 renaming h378 → _p2mH378
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h369 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapeCore.controlsLegsEncoding xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCore.controlsLegs (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCore.controlsLegsData xs.length ((_root_.Integration9_9.TM2NativeTapeCore.controlsLegsEncoding xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeCore.controlsLegs _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH367]
  exact _p2mH364 (_root_.Integration9_9.TM2NativeTapeCore.controlsEncoding xs.length) (_root_.Integration9_9.TM2NativeTapeCore.legsEncoding xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapeCore.controls (xs,word)) (fun word=>_root_.Integration9_9.TM2NativeTapeCore.legs (xs,word))
    (_root_.Integration9_9.TM2NativeTapeCore.controlsData xs.length) (_root_.Integration9_9.TM2NativeTapeCore.legsData xs.length) (_p2mH370 xs) (_p2mH377 xs) word
open _root_.P2Mba49f952 renaming h369 → _p2mH369
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h368 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.controlsLegsBits xs=(_root_.Integration9_9.TM2NativeTapeCore.controlsLegsEncoding xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.controlsLegsBits,_p2mH367,_p2mH376,_root_.Integration9_9.TM2NativeTapeCore.controlsLegsEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.prod]
open _root_.P2Mba49f952 renaming h368 → _p2mH368
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h384 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapeCore.withQueuesEncoding xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCore.withQueues (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCore.withQueuesData xs.length ((_root_.Integration9_9.TM2NativeTapeCore.withQueuesEncoding xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeCore.withQueues _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH368]
  exact _p2mH364 (_root_.Integration9_9.TM2NativeTapeCore.controlsLegsEncoding xs.length) (_root_.Integration9_9.TM2NativeTapeCore.queuesEncoding xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapeCore.controlsLegs (xs,word)) (fun word=>_root_.Integration9_9.TM2NativeTapeCore.queues (xs,word))
    (_root_.Integration9_9.TM2NativeTapeCore.controlsLegsData xs.length) (_root_.Integration9_9.TM2NativeTapeCore.queuesData xs.length) (_p2mH369 xs) (_p2mH379 xs) word
open _root_.P2Mba49f952 renaming h384 → _p2mH384
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h383 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.withQueuesBits xs=(_root_.Integration9_9.TM2NativeTapeCore.withQueuesEncoding xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.withQueuesBits,_p2mH368,_p2mH378,_root_.Integration9_9.TM2NativeTapeCore.withQueuesEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.prod]
open _root_.P2Mba49f952 renaming h383 → _p2mH383
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h382 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapeCore.withBodyEncoding xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCore.withBody (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCore.withBodyData xs.length ((_root_.Integration9_9.TM2NativeTapeCore.withBodyEncoding xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeCore.withBody _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH383]
  exact _p2mH364 (_root_.Integration9_9.TM2NativeTapeCore.withQueuesEncoding xs.length)
    (_root_.CurrentAFT.PublicBitTapes.bits ((_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).body*xs.length))
    (fun word=>_root_.Integration9_9.TM2NativeTapeCore.withQueues (xs,word)) id (_root_.Integration9_9.TM2NativeTapeCore.withQueuesData xs.length) _root_.Integration9_9.TM2NativeTapeCodec.wordData (_p2mH384 xs) (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h382 → _p2mH382
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h381 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.withBodyBits xs=(_root_.Integration9_9.TM2NativeTapeCore.withBodyEncoding xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.withBodyBits,_p2mH383,_p2mH387,_root_.CurrentAFT.BinaryPublicBitSizes.body_value,
    _root_.Integration9_9.TM2NativeTapeCore.withBodyEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.bits]
open _root_.P2Mba49f952 renaming h381 → _p2mH381
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h372 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.core xs.length xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCore.flat (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      (_root_.Integration9_9.TM2NativeTapeCore.withBodyData xs.length (((_root_.CurrentAFT.PublicBitTapes.core xs.length xs.length).equiv word).1),
        _root_.Integration9_9.TM2NativeTapeCodec.wordData (((_root_.CurrentAFT.PublicBitTapes.core xs.length xs.length).equiv word).2)) := by
  unfold _root_.Integration9_9.TM2NativeTapeCore.flat _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH381]
  exact _p2mH364 (_root_.Integration9_9.TM2NativeTapeCore.withBodyEncoding xs.length)
    (_root_.CurrentAFT.PublicBitTapes.bits ((_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).dimension*xs.length))
    (fun word=>_root_.Integration9_9.TM2NativeTapeCore.withBody (xs,word)) id (_root_.Integration9_9.TM2NativeTapeCore.withBodyData xs.length) _root_.Integration9_9.TM2NativeTapeCodec.wordData (_p2mH382 xs) (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h372 → _p2mH372
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h371 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.core xs.length xs.length).bits→Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCore.current (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeCoreProposal.tapesData ((_root_.CurrentAFT.PublicBitTapes.core xs.length xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapeCore.current
  rw [_p2mH372]
  rfl
open _root_.P2Mba49f952 renaming h371 → _p2mH371
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h380 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapeCore.totalBits xs=(_root_.CurrentAFT.PublicBitTapes.core xs.length xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapeCore.totalBits,_p2mH381,_p2mH392,_root_.CurrentAFT.BinaryPublicBitSizes.endpoint_value,
    _root_.CurrentAFT.PublicBitTapes.core,_root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.Encoding.indexed,_root_.CurrentAFT.PublicBitTapes.bits,
    _root_.Integration9_9.TM2NativeTapeCore.withBodyEncoding,_root_.Integration9_9.TM2NativeTapeCore.withQueuesEncoding,_root_.Integration9_9.TM2NativeTapeCore.controlsLegsEncoding,_root_.Integration9_9.TM2NativeTapeCore.controlsEncoding,_root_.Integration9_9.TM2NativeTapeCore.legsEncoding,_root_.Integration9_9.TM2NativeTapeCore.queuesEncoding]
open _root_.P2Mba49f952 renaming h380 → _p2mH380
end Integration9_9.TM2NativeTapeCore
open _root_.P2Mba49f952 renaming h366 → _p2mH366
open _root_.P2Mba49f952 renaming h367 → _p2mH367
open _root_.P2Mba49f952 renaming h368 → _p2mH368
open _root_.P2Mba49f952 renaming h369 → _p2mH369
open _root_.P2Mba49f952 renaming h370 → _p2mH370
open _root_.P2Mba49f952 renaming h371 → _p2mH371
open _root_.P2Mba49f952 renaming h372 → _p2mH372
open _root_.P2Mba49f952 renaming h373 → _p2mH373
open _root_.P2Mba49f952 renaming h374 → _p2mH374
open _root_.P2Mba49f952 renaming h375 → _p2mH375
open _root_.P2Mba49f952 renaming h376 → _p2mH376
open _root_.P2Mba49f952 renaming h377 → _p2mH377
open _root_.P2Mba49f952 renaming h378 → _p2mH378
open _root_.P2Mba49f952 renaming h379 → _p2mH379
open _root_.P2Mba49f952 renaming h380 → _p2mH380
open _root_.P2Mba49f952 renaming h381 → _p2mH381
open _root_.P2Mba49f952 renaming h382 → _p2mH382
open _root_.P2Mba49f952 renaming h383 → _p2mH383
open _root_.P2Mba49f952 renaming h384 → _p2mH384
open _root_.P2Mba49f952 renaming h447 → Integration9_9.TM2NativeTapeCore.range_map
open _root_.P2Mba49f952 renaming h447 → _p2mH447
end
open _root_.P2Mba49f952 renaming h366 → _p2mH366
open _root_.P2Mba49f952 renaming h367 → _p2mH367
open _root_.P2Mba49f952 renaming h368 → _p2mH368
open _root_.P2Mba49f952 renaming h369 → _p2mH369
open _root_.P2Mba49f952 renaming h370 → _p2mH370
open _root_.P2Mba49f952 renaming h371 → _p2mH371
open _root_.P2Mba49f952 renaming h372 → _p2mH372
open _root_.P2Mba49f952 renaming h373 → _p2mH373
open _root_.P2Mba49f952 renaming h374 → _p2mH374
open _root_.P2Mba49f952 renaming h375 → _p2mH375
open _root_.P2Mba49f952 renaming h376 → _p2mH376
open _root_.P2Mba49f952 renaming h377 → _p2mH377
open _root_.P2Mba49f952 renaming h378 → _p2mH378
open _root_.P2Mba49f952 renaming h379 → _p2mH379
open _root_.P2Mba49f952 renaming h380 → _p2mH380
open _root_.P2Mba49f952 renaming h381 → _p2mH381
open _root_.P2Mba49f952 renaming h382 → _p2mH382
open _root_.P2Mba49f952 renaming h383 → _p2mH383
open _root_.P2Mba49f952 renaming h384 → _p2mH384
namespace Integration9_9.TM2NativeDistinctTuples
end Integration9_9.TM2NativeDistinctTuples
namespace Integration9_9.TM2NativeDistinctTuples.indices
end Integration9_9.TM2NativeDistinctTuples.indices
namespace Integration9_9.TM2NativeDistinctTuples.ordered
end Integration9_9.TM2NativeDistinctTuples.ordered
namespace Integration9_9.TM2NativeDistinctTuples.pairCheck
end Integration9_9.TM2NativeDistinctTuples.pairCheck
namespace Integration9_9.TM2NativeDistinctTuples.pairs
end Integration9_9.TM2NativeDistinctTuples.pairs
namespace Integration9_9.TM2NativeDistinctTuples.relation
end Integration9_9.TM2NativeDistinctTuples.relation
namespace Integration9_9.TM2NativeDistinctTuples.sum
end Integration9_9.TM2NativeDistinctTuples.sum
namespace Integration9_9.TM2NativeTwoPoolAverage
end Integration9_9.TM2NativeTwoPoolAverage
namespace Integration9_9.TM2NativeTwoPoolAverage.current
end Integration9_9.TM2NativeTwoPoolAverage.current
namespace Integration9_9.TM2NativeTwoPoolAverage.normalizer
end Integration9_9.TM2NativeTwoPoolAverage.normalizer
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeWeightEvaluation
open AFT AFT.RationalNumerics CurrentAFT GradedControlAlgebra ControlCoordinates
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeRootGroupAlgebra
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h421 {α : Type} {order : ℕ} (F : _root_.Integration9_9.TM2NativeWeightEvaluation.Meta × α → _root_.CurrentAFT.RationalWeightProgram.RawTable order)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (x : _root_.Integration9_9.TM2NativeWeightEvaluation.Data α) : _root_.Integration9_9.TM2NativeWeightEvaluation.average F arity x=
      _root_.CurrentAFT.RationalWeightProgram.average arity.val.1.val arity.val.2.val x.2.1.length x.2.2.length
        (fun selected selectedCenters => _root_.CurrentAFT.RationalWeightProgram.pairedTensor x.1.1.1.length x.1.1.2.length arity.val.1.val
          (fun colors => F x.1 arity colors selectedCenters) selected)
        (fun i => x.2.1[i.val]?.getD (0,0)) (fun i => x.2.2[i.val]?.getD 0) := by
  rw [_root_.Integration9_9.TM2NativeWeightEvaluation.average,_root_.Integration9_9.TM2NativeTwoPoolAverage.current_value,List.length_map,List.length_map]
  have hp : _root_.CurrentAFT.CyclePatternProgram.selectionFintype x.2.1.length arity.val.1.val =
      (inferInstance : Fintype (Fin arity.val.1.val ↪ Fin x.2.1.length)) := Subsingleton.elim _ _
  have hb : _root_.CurrentAFT.CyclePatternProgram.selectionFintype x.2.2.length arity.val.2.val =
      (inferInstance : Fintype (Fin arity.val.2.val ↪ Fin x.2.2.length)) := Subsingleton.elim _ _
  unfold _root_.CurrentAFT.RationalWeightProgram.average
  rw [hp,hb]
  simp only [Fintype.sum_prod_type]
  congr 1
  apply Fintype.sum_equiv (Equiv.refl (Fin arity.val.1.val ↪ Fin x.2.1.length))
  intro primary
  apply Fintype.sum_equiv (Equiv.refl (Fin arity.val.2.val ↪ Fin x.2.2.length))
  intro body
  simp only [_root_.Integration9_9.TM2NativeWeightEvaluation.selected,_root_.Integration9_9.TM2NativePairedTensor.tensor,List.map_ofFn,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,Function.comp_def]
  apply congrArg (fun f => _root_.CurrentAFT.RationalWeightProgram.pairedTensor x.1.1.1.length x.1.1.2.length arity.val.1.val f _)
  funext word
  simp only [_root_.Integration9_9.TM2NativeWeightEvaluation.kernel,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
  rfl
open _root_.P2Mba49f952 renaming h421 → _p2mH421
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h422 {α : Type} (order : ℕ) (F : _root_.Integration9_9.TM2NativeWeightEvaluation.Meta × α → _root_.CurrentAFT.RationalWeightProgram.RawTable order) (x : _root_.Integration9_9.TM2NativeWeightEvaluation.Data α) :
    _root_.Integration9_9.TM2NativeWeightEvaluation.current order F x=_root_.CurrentAFT.RationalWeightProgram.current x.1.1.1.length x.1.1.2.length order x.2.1.length x.2.2.length
      (F x.1) (fun i => x.2.1[i.val]?.getD (0,0)) (fun i => x.2.2[i.val]?.getD 0) := by
  simp only [_root_.Integration9_9.TM2NativeWeightEvaluation.current,_root_.CurrentAFT.RationalWeightProgram.current,_p2mH421,_root_.CurrentAFT.GradedControlAlgebra.positiveArity]
open _root_.P2Mba49f952 renaming h422 → Integration9_9.TM2NativeWeightEvaluation.current_value
open _root_.P2Mba49f952 renaming h422 → _p2mH422
end Integration9_9.TM2NativeWeightEvaluation
open _root_.P2Mba49f952 renaming h421 → _p2mH421
open _root_.P2Mba49f952 renaming h422 → Integration9_9.TM2NativeWeightEvaluation.current_value
open _root_.P2Mba49f952 renaming h422 → _p2mH422
end
open _root_.P2Mba49f952 renaming h421 → _p2mH421
open _root_.P2Mba49f952 renaming h422 → Integration9_9.TM2NativeWeightEvaluation.current_value
open _root_.P2Mba49f952 renaming h422 → _p2mH422
namespace CurrentAFT.BinaryWeightProgram
end CurrentAFT.BinaryWeightProgram
namespace CurrentAFT.BinaryWeightProgram.current
end CurrentAFT.BinaryWeightProgram.current
namespace CurrentAFT.BinaryWeightProgram.evaluationWork
end CurrentAFT.BinaryWeightProgram.evaluationWork
namespace CurrentAFT.BinaryWeightProgram.term
end CurrentAFT.BinaryWeightProgram.term
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeWeightTable
open AFT AFT.RationalNumerics AFT.BinaryArithmetic CurrentAFT GradedControlAlgebra ControlCoordinates
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeRootGroupAlgebra TM2NativeBackgroundProfiles TM2NativeBackgroundLeg
open scoped BigOperators
 set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h424 (order : ℕ) (params : _root_.Integration9_9.TM2NativeWeightTable.Meta) (data : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors params.1.length) order) :
    _root_.Integration9_9.TM2NativeWeightTable.table order (params,List.ofFn (fun i => List.ofFn (fun j => ((data.get i).get j).decode)))=
      _root_.CurrentAFT.BinaryWeightLocal.rawTable params.1.length order data := by
  funext arity primary body
  unfold _root_.Integration9_9.TM2NativeWeightTable.table _root_.CurrentAFT.BinaryWeightLocal.rawTable
  change (if (∀i,primary i<_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1) ∧ (∀i,body i<_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1) then _ else 0) =
    (if h : (∀i,primary i<_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1) ∧ (∀i,body i<_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1) then _ else 0)
  by_cases h : (∀i,primary i<_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1) ∧ (∀i,body i<_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1)
  · have hb : 0<_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1 := _root_.CurrentAFT.BinaryWeightLocal.colors_pos _
    have ha := _root_.CurrentAFT.WeightCoordinates.arityCode_lt order arity.val.1.val arity.val.2.val
      (Nat.le_of_lt_succ arity.val.1.isLt) (Nat.le_of_lt_succ arity.val.2.isLt)
    have hj := _root_.CurrentAFT.WeightCoordinates.jointCode_lt_capacity (_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1) order arity.val.1.val arity.val.2.val hb arity.property primary body h.1 h.2
    rw [if_pos h,dif_pos h]
    change _root_.CurrentAFT.WeightCoordinates.jointCode (_root_.Integration9_9.TM2NativeBackgroundProfiles.colors params.1) arity.val.1.val arity.val.2.val primary body < _root_.CurrentAFT.BinaryWeightLocal.colors params.1.length ^ order at hj
    simp only [List.getElem?_ofFn,ha,hj,dif_pos,Option.getD_some,_root_.CurrentAFT.WeightCoordinates.arityIndex]
    rfl
  · rw [if_neg h,dif_neg h]
open _root_.P2Mba49f952 renaming h424 → _p2mH424
end Integration9_9.TM2NativeWeightTable
open _root_.P2Mba49f952 renaming h424 → _p2mH424
end
open _root_.P2Mba49f952 renaming h424 → _p2mH424
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeWeightProgram
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
attribute [local irreducible] RationalWeightProgram.current BinaryWeightProgram.current BinaryWeightLocal.rawTable
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h423 {order : ℕ} (x : _root_.Integration9_9.TM2NativeWeightProgram.Context order) :
    _root_.Integration9_9.TM2NativeWeightTable.current order (_root_.Integration9_9.TM2NativeWeightProgram.parse (_root_.Integration9_9.TM2NativeWeightProgram.rawInput x))=
      (_root_.CurrentAFT.BinaryWeightProgram.current x.params.1.length x.params.2.length order x.primaryPool x.bodyPool
        x.primary_pos x.body_pos x.table x.groups x.centers).data.decode := by
  rw [_p2mH82]
  unfold _root_.Integration9_9.TM2NativeWeightTable.current
  rw [_p2mH422]
  simp only [_root_.Integration9_9.TM2NativeWeightProgram.parse,_root_.Integration9_9.TM2NativeWeightProgram.rawInput,List.map_ofFn,Function.comp_def,List.length_ofFn,
    _p2mH424]
  rw [List.length_ofFn,List.length_ofFn]
  apply congrArg₂ (_root_.CurrentAFT.RationalWeightProgram.current x.params.1.length x.params.2.length order x.primaryPool x.bodyPool
    (_root_.CurrentAFT.BinaryWeightLocal.rawTable x.params.1.length order x.table))
  · funext i
    simp only [List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
  · funext i
    simp only [List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
open _root_.P2Mba49f952 renaming h423 → _p2mH423
end Integration9_9.TM2NativeWeightProgram
open _root_.P2Mba49f952 renaming h423 → _p2mH423
end
open _root_.P2Mba49f952 renaming h423 → _p2mH423
namespace CurrentAFT.BinaryCoreWeightData
end CurrentAFT.BinaryCoreWeightData
namespace CurrentAFT.BinaryCoreWeightData.centers
end CurrentAFT.BinaryCoreWeightData.centers
namespace CurrentAFT.BinaryCoreWeightData.color
end CurrentAFT.BinaryCoreWeightData.color
namespace CurrentAFT.BinaryCoreWeightData.current
end CurrentAFT.BinaryCoreWeightData.current
namespace CurrentAFT.BinaryCoreWeightData.groups
end CurrentAFT.BinaryCoreWeightData.groups
namespace CurrentAFT.BinaryCoreWeightData.ordinaryAddress
end CurrentAFT.BinaryCoreWeightData.ordinaryAddress
namespace CurrentAFT.BinaryCoreWeightData.ordinaryEntry
end CurrentAFT.BinaryCoreWeightData.ordinaryEntry
namespace CurrentAFT.BinaryCoreWeightData.primaryEntry
end CurrentAFT.BinaryCoreWeightData.primaryEntry
namespace Integration9_9.TM2NativeWeightProgram
end Integration9_9.TM2NativeWeightProgram
namespace Integration9_9.TM2NativeWeightProgram.Context
end Integration9_9.TM2NativeWeightProgram.Context
namespace Integration9_9.TM2NativeWeightProgram.Context.mk
end Integration9_9.TM2NativeWeightProgram.Context.mk
namespace Integration9_9.TM2NativeWeightProgram.parse
end Integration9_9.TM2NativeWeightProgram.parse
namespace Integration9_9.TM2NativeWeightProgram.rawInput
end Integration9_9.TM2NativeWeightProgram.rawInput
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeCoreWeight
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
attribute [local irreducible] CurrentProposalDimensions.current BinaryFullResponseCounts.current
  CurrentAFT.Parameters.legCount CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension
  RationalWeightProgram.current BinaryWeightProgram.current BinaryWeightLocal.rawTable
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h275 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) :
    _root_.Integration9_9.TM2NativeCoreWeight.groups (_root_.Integration9_9.TM2NativeCoreProposal.coreData data)=List.ofFn (fun i =>
      (((_root_.CurrentAFT.BinaryCoreWeightData.groups security data).value.get i).1.val,((_root_.CurrentAFT.BinaryCoreWeightData.groups security data).value.get i).2.val)) := by
  have hc : (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs≤(_root_.CurrentAFT.CurrentProposalDimensions.current security).controls := by
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1,(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.2.2.2.2]
    omega
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeCoreWeight.groups,_root_.Integration9_9.TM2NativeCoreProposal.coreData,List.length_take,List.length_ofFn,Nat.min_eq_left hc]
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeCoreWeight.groups,_root_.Integration9_9.TM2NativeCoreProposal.coreData,List.getElem_take,List.getElem_ofFn,_root_.Integration9_9.TM2NativeCoreProposal.controlData,
      _root_.CurrentAFT.BinaryCoreWeightData.groups,_root_.AFT.BinaryArithmetic.storeData_get,_root_.CurrentAFT.BinaryCoreWeightData.primaryEntry,_root_.AFT.BinaryArithmetic.readVector_value,_root_.CurrentAFT.BinaryCoreWeightData.color,Fin.val_cast]
    rfl
open _root_.P2Mba49f952 renaming h275 → _p2mH275
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h273 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) :
    _root_.Integration9_9.TM2NativeCoreWeight.centers (_root_.Integration9_9.TM2NativeCoreProposal.coreData data)=List.ofFn (fun i => ((_root_.CurrentAFT.BinaryCoreWeightData.centers security data).value.get i).val) := by
  have hc : (_root_.CurrentAFT.CurrentProposalDimensions.current security).controls-(_root_.CurrentAFT.CurrentProposalDimensions.current security).legs=
      (_root_.CurrentAFT.CurrentProposalDimensions.current security).ordinary := by
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1,(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.2.2.2.2,
      (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.2.2.2.1]
    omega
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeCoreWeight.centers,_root_.Integration9_9.TM2NativeCoreProposal.coreData,List.length_map,List.length_drop,List.length_ofFn,hc]
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeCoreWeight.centers,_root_.Integration9_9.TM2NativeCoreProposal.coreData,List.getElem_map,List.getElem_drop,List.getElem_ofFn,List.length_ofFn,_root_.Integration9_9.TM2NativeCoreProposal.controlData,
      _root_.CurrentAFT.BinaryCoreWeightData.centers,_root_.AFT.BinaryArithmetic.storeData_get,_root_.CurrentAFT.BinaryCoreWeightData.ordinaryEntry,_root_.AFT.BinaryArithmetic.readVector_value,
      _root_.CurrentAFT.BinaryCoreWeightData.ordinaryAddress,_root_.AFT.BinaryArithmetic.addCounter_value,_root_.CurrentAFT.BinaryCoreWeightData.color,Fin.val_cast]
open _root_.P2Mba49f952 renaming h273 → _p2mH273
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h274 (order : ℕ) (params : _root_.Integration9_9.TM2NativeCoreProposal.Meta)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors params.1.length) order)
    (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore params.1.length) :
    _root_.Integration9_9.TM2NativeCoreWeight.current order ((params,List.ofFn (fun i => List.ofFn (fun j => ((table.get i).get j).decode))),_root_.Integration9_9.TM2NativeCoreProposal.coreData data)=
      (_root_.CurrentAFT.BinaryCoreWeightData.current params.1.length params.2.length order table data).value.decode := by
  let ctx : _root_.Integration9_9.TM2NativeWeightProgram.Context order := ⟨params,_,_,_root_.CurrentAFT.BinaryCoreWeightData.primaryPool_pos _,
    _root_.CurrentAFT.BinaryCoreWeightData.bodyPool_pos _,table,(_root_.CurrentAFT.BinaryCoreWeightData.groups params.1.length data).value,
    (_root_.CurrentAFT.BinaryCoreWeightData.centers params.1.length data).value⟩
  have h:=_p2mH423 ctx
  rw [_root_.Integration9_9.TM2NativeCoreWeight.current,_p2mH275,_p2mH273]
  simpa only [ctx,_root_.Integration9_9.TM2NativeWeightProgram.parse,_root_.Integration9_9.TM2NativeWeightProgram.rawInput,List.map_ofFn,Function.comp_def,
    _root_.CurrentAFT.BinaryCoreWeightData.current] using h
open _root_.P2Mba49f952 renaming h274 → _p2mH274
end Integration9_9.TM2NativeCoreWeight
open _root_.P2Mba49f952 renaming h273 → _p2mH273
open _root_.P2Mba49f952 renaming h274 → _p2mH274
open _root_.P2Mba49f952 renaming h275 → _p2mH275
end
open _root_.P2Mba49f952 renaming h273 → _p2mH273
open _root_.P2Mba49f952 renaming h274 → _p2mH274
open _root_.P2Mba49f952 renaming h275 → _p2mH275
namespace CurrentAFT.BinaryArrayRejection
end CurrentAFT.BinaryArrayRejection
namespace CurrentAFT.BinaryArrayRejection.run
end CurrentAFT.BinaryArrayRejection.run
namespace CurrentAFT.BinaryArrayRejection.run.match_1
end CurrentAFT.BinaryArrayRejection.run.match_1
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeRejection
open AFT AFT.RationalNumerics AFT.BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeFiniteDraw
variable {α Tape State : Type}
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h352 (accepted : Bool) (candidate : State) (rest : List (Bool × State)) (fallback : State) :
    _root_.Integration9_9.TM2NativeRejection.select ((accepted,candidate)::rest,fallback)=if accepted then candidate else _root_.Integration9_9.TM2NativeRejection.select (rest,fallback) := by
  cases accepted <;> simp only [_root_.Integration9_9.TM2NativeRejection.select,List.findIdx_cons,Bool.cond_false,Bool.cond_true,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Bool.false_eq_true,ite_false,ite_true]
open _root_.P2Mba49f952 renaming h352 → _p2mH352
end Integration9_9.TM2NativeRejection
open _root_.P2Mba49f952 renaming h352 → _p2mH352
end
open _root_.P2Mba49f952 renaming h352 → _p2mH352
namespace CurrentAFT.BinaryPublicRejection
end CurrentAFT.BinaryPublicRejection
namespace CurrentAFT.BinaryPublicRejection.coreScore
end CurrentAFT.BinaryPublicRejection.coreScore
namespace CurrentAFT.BinaryPublicRejection.score
end CurrentAFT.BinaryPublicRejection.score
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativePublicRejection
open AFT AFT.RationalNumerics AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
attribute [local irreducible] CurrentProposalDimensions.current CurrentPreparedCoreProposal.draw
  BinaryCoreWeightData.current BinaryCoreCharge.current TM2NativeCoreProposal.current
  TM2NativeCoreWeight.current TM2NativeCoreCharge.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h337 (order : ℕ) (params : _root_.Integration9_9.TM2NativeCoreProposal.Meta) (drawTicks weightTicks : List Unit)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors params.1.length) order)
    (word : _root_.CurrentAFT.CurrentCoreProposal.Tapes params.1.length drawTicks.length) :
    _root_.Integration9_9.TM2NativePublicRejection.sample (_root_.Integration9_9.TM2NativePublicRejection.inputContext order params drawTicks weightTicks table,_root_.Integration9_9.TM2NativeCoreProposal.tapesData word)=
      _root_.Integration9_9.TM2NativePublicRejection.resultData (_root_.CurrentAFT.BinaryPublicRejection.sample params.1.length params.2.length drawTicks.length word).value := by
  simp only [_root_.Integration9_9.TM2NativePublicRejection.sample,_root_.Integration9_9.TM2NativePublicRejection.inputContext,_p2mH272,_root_.CurrentAFT.BinaryPublicRejection.sample,_root_.Integration9_9.TM2NativePublicRejection.resultData]
open _root_.P2Mba49f952 renaming h337 → _p2mH337
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h338 (order : ℕ) (params : _root_.Integration9_9.TM2NativeCoreProposal.Meta) (drawTicks weightTicks : List Unit)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors params.1.length) order)
    (point : Option (_root_.CurrentAFT.CurrentCoreProposal.MaterializedCore params.1.length)) :
    _root_.Integration9_9.TM2NativePublicRejection.score order (_root_.Integration9_9.TM2NativePublicRejection.inputContext order params drawTicks weightTicks table,_root_.Integration9_9.TM2NativePublicRejection.resultData point)=
      (_root_.CurrentAFT.BinaryPublicRejection.score params.1.length weightTicks.length order table point).value.decode := by
  cases point with
  | none => simp only [_root_.Integration9_9.TM2NativePublicRejection.score,_root_.Integration9_9.TM2NativePublicRejection.resultData,Bool.false_and,Bool.false_eq_true,ite_false,_root_.CurrentAFT.BinaryPublicRejection.score,_root_.AFT.BinaryArithmetic.RationalBits.zero_value]
  | some core =>
    simp only [_root_.Integration9_9.TM2NativePublicRejection.score,_root_.Integration9_9.TM2NativePublicRejection.resultData,_root_.Integration9_9.TM2NativePublicRejection.inputContext,Bool.true_and,_p2mH261,
      _p2mH274,_root_.CurrentAFT.BinaryPublicRejection.score]
    split_ifs <;> rfl
open _root_.P2Mba49f952 renaming h338 → _p2mH338
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h339 {S T D : Type} (encode : S→D)
    (draw : T→_root_.AFT.RationalRejectionProgram.CountedValue S)
    (weight : S→_root_.AFT.RationalRejectionProgram.CountedValue _root_.AFT.BinaryArithmetic.RationalBits)
    (envelope : _root_.AFT.BinaryArithmetic.RationalBits) (bits : ℕ) (fallback : _root_.AFT.RationalRejectionProgram.CountedValue S)
    (attempts : ℕ) (words : Fin attempts→T × (Fin bits→Fin 2)) :
    _root_.Integration9_9.TM2NativeRejection.select
      (List.ofFn (fun i => (decide ((_root_.AFT.BinaryArithmetic.binaryAcceptance
        (_root_.AFT.BinaryArithmetic.binaryPositiveRatio (weight (draw (words i).1).value).value envelope).data bits (words i).2).value=0),
        encode (draw (words i).1).value)),encode fallback.value)=
      encode (_root_.AFT.BinaryArithmetic.binaryRejectionDraw draw weight envelope bits fallback attempts words).value := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [List.ofFn_succ,_p2mH352,decide_eq_true_eq,_root_.AFT.BinaryArithmetic.binaryRejectionDraw]
    split_ifs
    · rfl
    · exact ih (Fin.tail words)
open _root_.P2Mba49f952 renaming h339 → _p2mH339
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h336 (order : ℕ) (params : _root_.Integration9_9.TM2NativeCoreProposal.Meta) (drawTicks weightTicks : List Unit)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors params.1.length) order)
    (coinBits attempts : ℕ) (words : Vector (_root_.CurrentAFT.CurrentCoreProposal.Tapes params.1.length drawTicks.length × (Fin coinBits→Fin 2)) attempts) :
    _root_.Integration9_9.TM2NativePublicRejection.current order (_root_.Integration9_9.TM2NativePublicRejection.inputContext order params drawTicks weightTicks table,
      List.ofFn (fun i => (_root_.Integration9_9.TM2NativeCoreProposal.tapesData (words.get i).1,List.ofFn (fun j => _root_.AFT.BinaryArithmetic.digitBoolean ((words.get i).2 j)))))=
      _root_.Integration9_9.TM2NativePublicRejection.resultData (_root_.CurrentAFT.BinaryPublicRejection.current params.1.length params.2.length drawTicks.length weightTicks.length coinBits order attempts table words).value := by
  let ctx:=_root_.Integration9_9.TM2NativePublicRejection.inputContext order params drawTicks weightTicks table
  let draw:=_root_.CurrentAFT.BinaryPublicRejection.sample params.1.length params.2.length drawTicks.length
  let weight:=_root_.CurrentAFT.BinaryPublicRejection.score params.1.length weightTicks.length order table
  have hc (word : _root_.CurrentAFT.CurrentCoreProposal.Tapes params.1.length drawTicks.length × (Fin coinBits→Fin 2)) :
      _root_.Integration9_9.TM2NativeRejection.candidate _root_.Integration9_9.TM2NativePublicRejection.sample (_root_.Integration9_9.TM2NativePublicRejection.score order) (fun _ => 2)
        (ctx,(_root_.Integration9_9.TM2NativeCoreProposal.tapesData word.1,List.ofFn (fun j => _root_.AFT.BinaryArithmetic.digitBoolean (word.2 j))))=
        (decide ((_root_.AFT.BinaryArithmetic.binaryAcceptance (_root_.AFT.BinaryArithmetic.binaryPositiveRatio (weight (draw word.1).value).value
          (_root_.AFT.BinaryArithmetic.RationalBits.ofCounter 2).data).data coinBits word.2).value=0),_root_.Integration9_9.TM2NativePublicRejection.resultData (draw word.1).value) := by
    simp only [_root_.Integration9_9.TM2NativeRejection.candidate,ctx,_p2mH337,_p2mH338]
    have hr : _root_.Integration9_9.TM2NativePositiveDraw.positive (weight (draw word.1).value).value.decode/2=
        (_root_.AFT.BinaryArithmetic.binaryPositiveRatio (weight (draw word.1).value).value (_root_.AFT.BinaryArithmetic.RationalBits.ofCounter 2).data).data.decode := by
      rw [_p2mH23,_p2mH335,_root_.AFT.BinaryArithmetic.RationalBits.ofCounter_value,max_comm]
      norm_num
    change (decide (_root_.Integration9_9.TM2NativeFiniteDraw.acceptance (_root_.Integration9_9.TM2NativePositiveDraw.positive (weight (draw word.1).value).value.decode/2,
      List.ofFn (fun j => _root_.AFT.BinaryArithmetic.digitBoolean (word.2 j)))=0),_root_.Integration9_9.TM2NativePublicRejection.resultData (draw word.1).value)=_
    rw [hr,_p2mH310]
  unfold _root_.Integration9_9.TM2NativePublicRejection.current _root_.Integration9_9.TM2NativeRejection.current
  simp only [List.map_ofFn,Function.comp_def]
  change _root_.Integration9_9.TM2NativeRejection.select (List.ofFn (fun i =>
    _root_.Integration9_9.TM2NativeRejection.candidate _root_.Integration9_9.TM2NativePublicRejection.sample (_root_.Integration9_9.TM2NativePublicRejection.score order) (fun _ => 2)
      (ctx,(_root_.Integration9_9.TM2NativeCoreProposal.tapesData (words.get i).1,List.ofFn (fun j => _root_.AFT.BinaryArithmetic.digitBoolean ((words.get i).2 j))))),(false,default))=_
  simp only [hc]
  have hs := _p2mH339 _root_.Integration9_9.TM2NativePublicRejection.resultData draw weight (_root_.AFT.BinaryArithmetic.RationalBits.ofCounter 2).data coinBits ⟨none,1⟩ attempts words.get
  trans _root_.Integration9_9.TM2NativePublicRejection.resultData (_root_.AFT.BinaryArithmetic.binaryRejectionDraw draw weight (_root_.AFT.BinaryArithmetic.RationalBits.ofCounter 2).data coinBits ⟨none,1⟩ attempts words.get).value
  · simpa only [_root_.Integration9_9.TM2NativePublicRejection.resultData] using hs
  change _root_.Integration9_9.TM2NativePublicRejection.resultData (_root_.AFT.BinaryArithmetic.binaryRejectionDraw draw weight _ _ _ _ _).value=
    _root_.Integration9_9.TM2NativePublicRejection.resultData (_root_.CurrentAFT.BinaryArrayRejection.run draw weight _ _ _ _ _).value
  rw [_p2mH52]
open _root_.P2Mba49f952 renaming h336 → _p2mH336
end Integration9_9.TM2NativePublicRejection
open _root_.P2Mba49f952 renaming h336 → _p2mH336
open _root_.P2Mba49f952 renaming h337 → _p2mH337
open _root_.P2Mba49f952 renaming h338 → _p2mH338
open _root_.P2Mba49f952 renaming h339 → _p2mH339
end
open _root_.P2Mba49f952 renaming h336 → _p2mH336
open _root_.P2Mba49f952 renaming h337 → _p2mH337
open _root_.P2Mba49f952 renaming h338 → _p2mH338
open _root_.P2Mba49f952 renaming h339 → _p2mH339
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeCappedRejection
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
attribute [local irreducible] CurrentProposalDimensions.current
  CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
  TM2NativePublicRejection.current BinaryPublicRejection.current BinaryPublicRejection.draw CappedPublicRejection.current
  BinaryRejectionCap.current BinaryProposalPrecision.current PublicParameterProgram.modulus
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h231 (xs : List Unit) :
    (_root_.Integration9_9.TM2NativeCappedRejection.precisionTicks xs).length=_root_.CurrentAFT.CurrentProposalPrecision.tableBits xs.length xs.length := by
  simp only [_root_.Integration9_9.TM2NativeCappedRejection.precisionTicks,List.length_replicate,_root_.CurrentAFT.CurrentProposalPrecision.tableBits,_root_.CurrentAFT.CurrentProposalPrecision.padding]
open _root_.P2Mba49f952 renaming h231 → _p2mH231
attribute [local irreducible] precisionTicks
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h230 (order : ℕ) (xs : List Unit)
    (table : _root_.CurrentAFT.BinaryWeightCoordinates.Table (_root_.CurrentAFT.BinaryWeightLocal.colors xs.length) order)
    (word : _root_.CurrentAFT.CappedPublicRejection.Tapes xs.length) :
    _root_.Integration9_9.TM2NativeCappedRejection.current order ((xs,List.ofFn (fun i=>List.ofFn (fun j=>((table.get i).get j).decode))),_root_.Integration9_9.TM2NativeCappedRejection.tapeData word)=
      _root_.Integration9_9.TM2NativePublicRejection.resultData (_root_.CurrentAFT.CappedPublicRejection.current xs.length order table word).value := by
  have hs : (_root_.AFT.BinaryArithmetic.storeData (_root_.CurrentAFT.BinaryRejectionCap.current xs.length).count (fun index=>⟨word index,1⟩)).value=Vector.ofFn word := by
    apply Vector.ext
    intro i hi
    change (_root_.AFT.BinaryArithmetic.storeData _ _).value.get ⟨i,hi⟩=(Vector.ofFn word).get ⟨i,hi⟩
    simp only [_root_.AFT.BinaryArithmetic.storeData_get,Vector.get_ofFn]
  have h := _p2mH336 order (xs,_root_.Integration9_9.TM2NativeCappedRejection.precisionTicks xs) xs xs table xs.length
    (_root_.CurrentAFT.BinaryRejectionCap.current xs.length).count (Vector.ofFn word)
  simp only [Vector.get_ofFn] at h
  change _root_.Integration9_9.TM2NativeCappedRejection.current order _=_
  have ht : (_root_.CurrentAFT.CappedPublicRejection.current xs.length order table word).value=
      (_root_.CurrentAFT.BinaryPublicRejection.current xs.length (_root_.Integration9_9.TM2NativeCappedRejection.precisionTicks xs).length xs.length xs.length xs.length order
        (_root_.CurrentAFT.BinaryRejectionCap.current xs.length).count table (Vector.ofFn word)).value := by
    simp only [_root_.CurrentAFT.CappedPublicRejection.current,_root_.CurrentAFT.BinaryPublicRejection.draw,hs,_p2mH68,
      _p2mH231]
  rw [ht]
  exact h
open _root_.P2Mba49f952 renaming h230 → _p2mH230
end Integration9_9.TM2NativeCappedRejection
open _root_.P2Mba49f952 renaming h230 → _p2mH230
open _root_.P2Mba49f952 renaming h231 → _p2mH231
end
open _root_.P2Mba49f952 renaming h230 → _p2mH230
open _root_.P2Mba49f952 renaming h231 → _p2mH231
namespace CurrentAFT.CurrentFlagBinaryMetadata.Data
end CurrentAFT.CurrentFlagBinaryMetadata.Data
namespace CurrentAFT.CurrentFlagBinaryMetadata.Data.mk
end CurrentAFT.CurrentFlagBinaryMetadata.Data.mk
namespace CurrentAFT.CurrentFlagBinaryMetadata.coordinates
end CurrentAFT.CurrentFlagBinaryMetadata.coordinates
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeChartCoordinates
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h232 (q point : ℕ) (hq : 0<q) :
    _root_.Integration9_9.TM2NativeChartCoordinates.coordinates (q,point)=((_root_.AFT.BinaryArithmetic.binaryChartCoordinates q point).offset,
      ((_root_.AFT.BinaryArithmetic.binaryChartCoordinates q point).scale,(_root_.AFT.BinaryArithmetic.binaryChartCoordinates q point).shear)) := by
  rcases _root_.AFT.BinaryArithmetic.binaryChartCoordinates_values q point hq with ⟨h0,h1,h2⟩
  simp only [_root_.Integration9_9.TM2NativeChartCoordinates.coordinates,h0,h1,h2]
open _root_.P2Mba49f952 renaming h232 → _p2mH232
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h233 (address cutoff q : ℕ) (hq : 0<q) :
    _root_.Integration9_9.TM2NativeChartCoordinates.difference ((address,cutoff),q)=(_root_.AFT.BinaryArithmetic.modularDifference address cutoff q).count := by
  simp only [_root_.Integration9_9.TM2NativeChartCoordinates.difference,_root_.AFT.BinaryArithmetic.modularDifference,(_root_.AFT.BinaryArithmetic.divideCounter_value _ _ hq).2,
    _root_.AFT.BinaryArithmetic.differenceCounter_value,_root_.AFT.BinaryArithmetic.addCounter_value]
open _root_.P2Mba49f952 renaming h233 → _p2mH233
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h234 (cutoff q input point : ℕ) (hq : 0<q) :
    _root_.Integration9_9.TM2NativeChartCoordinates.feature ((cutoff,q),(input,point))=(_root_.AFT.BinaryArithmetic.protectedFeatureAddress cutoff q input point).count := by
  simp only [_root_.Integration9_9.TM2NativeChartCoordinates.feature,_root_.Integration9_9.TM2NativeChartCoordinates.coordinates,_p2mH233 _ _ _ hq,_root_.AFT.BinaryArithmetic.protectedFeatureAddress,
    (_root_.AFT.BinaryArithmetic.divideCounter_value _ _ hq).2,_root_.AFT.BinaryArithmetic.addCounter_value,_root_.AFT.BinaryArithmetic.multiplyCounter_value,
    (_root_.AFT.BinaryArithmetic.divideCounter_value _ _ (Nat.mul_pos hq hq)).1,(_root_.AFT.BinaryArithmetic.divideCounter_value _ _ (Nat.mul_pos hq hq)).2,
    (_root_.AFT.BinaryArithmetic.divideCounter_value _ _ hq).1,_root_.AFT.BinaryArithmetic.doubleCounter_value,Nat.succ_eq_add_one,
    (_root_.AFT.BinaryArithmetic.divideCounter_value input (2*cutoff+1) (by omega)).1,(_root_.AFT.BinaryArithmetic.divideCounter_value input (2*cutoff+1) (by omega)).2]
open _root_.P2Mba49f952 renaming h234 → _p2mH234
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h235 (cutoff q : ℕ) (sign : Bool) (digits : List Bool) (input color : ℕ) :
    _root_.Integration9_9.TM2NativeChartCoordinates.palette (((cutoff,q),_root_.AFT.BinaryArithmetic.signedValue sign digits),(input,color))=
      (_root_.AFT.BinaryArithmetic.protectedPalette cutoff q false sign [true] digits input color).value := by
  apply Bool.eq_iff_iff.mpr
  rw [_p2mH33]
  simp only [_root_.Integration9_9.TM2NativeChartCoordinates.palette,decide_eq_true_eq,_root_.AFT.BinaryArithmetic.signedValue,Bool.false_eq_true,ite_false,_root_.AFT.BinaryArithmetic.value,Bool.toNat_true,Nat.cast_one,Nat.cast_zero,mul_zero,add_zero]
  omega
open _root_.P2Mba49f952 renaming h235 → _p2mH235
end Integration9_9.TM2NativeChartCoordinates
open _root_.P2Mba49f952 renaming h232 → _p2mH232
open _root_.P2Mba49f952 renaming h233 → _p2mH233
open _root_.P2Mba49f952 renaming h234 → _p2mH234
open _root_.P2Mba49f952 renaming h235 → _p2mH235
end
open _root_.P2Mba49f952 renaming h232 → _p2mH232
open _root_.P2Mba49f952 renaming h233 → _p2mH233
open _root_.P2Mba49f952 renaming h234 → _p2mH234
open _root_.P2Mba49f952 renaming h235 → _p2mH235
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeChartMetadata
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeChartCoordinates
attribute [local irreducible] chartTicks featureTicks
attribute [local irreducible] charts features colors
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h246 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) : (_root_.Integration9_9.TM2NativeChartMetadata.chartTicks p).length=p.2.length*(p.2.length*p.2.length) := by
  simp only [_root_.Integration9_9.TM2NativeChartMetadata.chartTicks,_root_.Integration9_9.TM2NativePrime.powerSlots_length,pow_succ,pow_zero,Nat.one_mul,Nat.mul_assoc]
open _root_.P2Mba49f952 renaming h246 → _p2mH246
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h248 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) : (_root_.Integration9_9.TM2NativeChartMetadata.featureTicks p).length=(2*p.1.length+1)*(2*p.1.length+1) := by
  simp only [_root_.Integration9_9.TM2NativeChartMetadata.featureTicks,_root_.Integration9_9.TM2NativePrime.powerSlots_length,List.length_append,List.length_singleton,pow_two]
  congr 1 <;> omega
open _root_.P2Mba49f952 renaming h248 → _p2mH248
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h245 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) [NeZero p.2.length] (sign : Bool) (digits : List Bool)
    (mark : Fin p.2.length) (i : Fin ((2*p.1.length+1)*(2*p.1.length+1)))
    (j : Fin (p.2.length*(p.2.length*p.2.length))) :
    _root_.Integration9_9.TM2NativeChartMetadata.allowedAt (((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),(i.val,j.val))=
      ((_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.allowed.get i).get
        (((_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.feature.get i).get j) := by
  simp only [_root_.Integration9_9.TM2NativeChartMetadata.allowedAt,_p2mH234 _ _ _ _ (NeZero.pos _),_p2mH235,
    _root_.CurrentAFT.CurrentFlagBinaryMetadata.build,_p2mH32,_root_.AFT.BinaryArithmetic.protectedMetadataCore,_root_.AFT.BinaryArithmetic.storeData_get,_root_.AFT.BinaryArithmetic.protectedFeature]
  rfl
open _root_.P2Mba49f952 renaming h245 → _p2mH245
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h250 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) (i : Fin ((2*p.1.length+1)*(2*p.1.length+1))) :
    _root_.Integration9_9.TM2NativeChartMetadata.line (p,i.val)=(_root_.CurrentAFT.CurrentFlagBinaryMasks.onLine p.1.length i).value := by
  apply Bool.eq_iff_iff.mpr
  simp only [_root_.Integration9_9.TM2NativeChartMetadata.line,decide_eq_true_eq,_root_.CurrentAFT.CurrentFlagBinaryMasks.onLine,_root_.AFT.BinaryArithmetic.equalCounter_value,_root_.AFT.BinaryArithmetic.doubleCounter_value,
    Nat.succ_eq_add_one,(_root_.AFT.BinaryArithmetic.divideCounter_value i.val (2*p.1.length+1) (by omega)).1]
open _root_.P2Mba49f952 renaming h250 → _p2mH250
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h251 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) [NeZero p.2.length] (sign : Bool) (digits : List Bool)
    (mark : Fin p.2.length) (j : Fin (p.2.length*(p.2.length*p.2.length))) :
    _root_.Integration9_9.TM2NativeChartMetadata.safe (((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),j.val)=
      (_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.safe.get j := by
  apply Bool.eq_iff_iff.mpr
  simp only [_root_.Integration9_9.TM2NativeChartMetadata.safe,_root_.Integration9_9.TM2NativeChartMetadata.features,_p2mH248,_root_.Integration9_9.TM2NativeChartMetadata.range_map,_root_.Integration9_9.TM2NativeChartMetadata.every,List.all_eq_true,List.mem_ofFn,
    id_eq,forall_exists_index,forall_apply_eq_imp_iff,Bool.and_eq_true,Bool.not_eq_true',
    Bool.eq_false_iff,decide_eq_true_eq,_p2mH245]
  simp only [_root_.CurrentAFT.CurrentFlagBinaryMetadata.build,_p2mH32,_root_.AFT.BinaryArithmetic.protectedMetadataCore,
    _root_.AFT.BinaryArithmetic.storeData_get,_p2mH36,_root_.AFT.BinaryArithmetic.protectedScale,_root_.AFT.BinaryArithmetic.protectedScaleAddress_value _ _ (NeZero.pos _),
    _root_.Integration9_9.TM2NativeChartCoordinates.coordinates,Fin.ext_iff,Fin.val_zero]
  simp only [ne_eq,decide_eq_true_eq,←Fin.val_eq_zero_iff,Fin.val_cast]
open _root_.P2Mba49f952 renaming h251 → _p2mH251
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h249 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) [NeZero p.2.length] (sign : Bool) (digits : List Bool)
    (mark : Fin p.2.length) (j : Fin (p.2.length*(p.2.length*p.2.length))) :
    _root_.Integration9_9.TM2NativeChartMetadata.fiber (((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),j.val)=
      (_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.fiber.get j := by
  apply Bool.eq_iff_iff.mpr
  simp only [_root_.Integration9_9.TM2NativeChartMetadata.fiber,_root_.Integration9_9.TM2NativeChartMetadata.features,_p2mH248,_root_.Integration9_9.TM2NativeChartMetadata.range_map,_root_.Integration9_9.TM2NativeChartMetadata.every,List.all_eq_true,List.mem_ofFn,
    id_eq,forall_exists_index,forall_apply_eq_imp_iff,Bool.and_eq_true,Bool.not_eq_true',
    Bool.eq_false_iff,decide_eq_true_eq,Bool.or_eq_true,_p2mH245,_p2mH250]
  simp only [_root_.CurrentAFT.CurrentFlagBinaryMetadata.build,_root_.AFT.BinaryArithmetic.storeData_get,_p2mH158,
    _root_.CurrentAFT.CurrentFlagBinaryMetadata.coordinates,Fin.ext_iff,Fin.val_zero,
    _root_.AFT.BinaryArithmetic.binaryChartCoordinates_values _ _ (NeZero.pos _),_root_.Integration9_9.TM2NativeChartCoordinates.coordinates]
  simp only [_p2mH32,_root_.AFT.BinaryArithmetic.protectedMetadataCore,_root_.AFT.BinaryArithmetic.storeData_get,_root_.AFT.BinaryArithmetic.protectedScale,
    _root_.AFT.BinaryArithmetic.protectedScaleAddress_value _ _ (NeZero.pos _),Fin.ext_iff,Fin.val_zero]
  simp only [or_iff_not_imp_left,ne_eq,decide_eq_true_eq,←Fin.val_eq_zero_iff,Fin.val_cast,and_assoc]
open _root_.P2Mba49f952 renaming h249 → _p2mH249
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h247 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) [NeZero p.2.length] (sign : Bool) (digits : List Bool)
    (mark : Fin p.2.length) :
    _root_.Integration9_9.TM2NativeChartMetadata.current ((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val)=
      _root_.Integration9_9.TM2NativeChartMetadata.data (_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value := by
  simp only [_root_.Integration9_9.TM2NativeChartMetadata.current,_root_.Integration9_9.TM2NativeChartMetadata.charts,_root_.Integration9_9.TM2NativeChartMetadata.features,_root_.Integration9_9.TM2NativeChartMetadata.colors,_p2mH246,_p2mH248,_root_.Integration9_9.TM2NativeChartMetadata.range_map,
    _p2mH251,_p2mH250,_p2mH249,_root_.Integration9_9.TM2NativeChartMetadata.data]
  refine Prod.ext ?_ ?_
  · refine Prod.ext ?_ ?_
    · apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      rw [_p2mH234 _ _ _ _ (NeZero.pos _)]
      simp only [_root_.CurrentAFT.CurrentFlagBinaryMetadata.build,_p2mH32,_root_.AFT.BinaryArithmetic.protectedMetadataCore,_root_.AFT.BinaryArithmetic.storeData_get,_root_.AFT.BinaryArithmetic.protectedFeature]
      rfl
    · apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext c
      rw [_p2mH235]
      simp only [_root_.CurrentAFT.CurrentFlagBinaryMetadata.build,_p2mH32,_root_.AFT.BinaryArithmetic.protectedMetadataCore,_root_.AFT.BinaryArithmetic.storeData_get]
  · refine Prod.ext rfl ?_
    refine Prod.ext ?_ rfl
    apply congrArg List.ofFn
    funext i
    simp only [_root_.CurrentAFT.CurrentFlagBinaryMetadata.build,_root_.AFT.BinaryArithmetic.storeData_get]
open _root_.P2Mba49f952 renaming h247 → _p2mH247
end Integration9_9.TM2NativeChartMetadata
open _root_.P2Mba49f952 renaming h245 → _p2mH245
open _root_.P2Mba49f952 renaming h246 → _p2mH246
open _root_.P2Mba49f952 renaming h247 → _p2mH247
open _root_.P2Mba49f952 renaming h248 → _p2mH248
open _root_.P2Mba49f952 renaming h249 → _p2mH249
open _root_.P2Mba49f952 renaming h250 → _p2mH250
open _root_.P2Mba49f952 renaming h251 → _p2mH251
end
open _root_.P2Mba49f952 renaming h245 → _p2mH245
open _root_.P2Mba49f952 renaming h246 → _p2mH246
open _root_.P2Mba49f952 renaming h247 → _p2mH247
open _root_.P2Mba49f952 renaming h248 → _p2mH248
open _root_.P2Mba49f952 renaming h249 → _p2mH249
open _root_.P2Mba49f952 renaming h250 → _p2mH250
open _root_.P2Mba49f952 renaming h251 → _p2mH251
namespace AFT.BinaryArithmetic.RationalBits.chartDeletionMatrix
end AFT.BinaryArithmetic.RationalBits.chartDeletionMatrix
namespace AFT.BinaryArithmetic.RationalBits.normalizeArray
end AFT.BinaryArithmetic.RationalBits.normalizeArray
namespace AFT.BinaryArithmetic.RationalBits.normalizeArrayWork
end AFT.BinaryArithmetic.RationalBits.normalizeArrayWork
namespace AFT.BinaryArithmetic.RationalBits.sumArray
end AFT.BinaryArithmetic.RationalBits.sumArray
namespace CurrentAFT.CurrentFlagBinary.defect
end CurrentAFT.CurrentFlagBinary.defect
namespace CurrentAFT.CurrentFlagBinary.defectTerm
end CurrentAFT.CurrentFlagBinary.defectTerm
namespace CurrentAFT.CurrentFlagBinary.maskedEntry
end CurrentAFT.CurrentFlagBinary.maskedEntry
namespace CurrentAFT.CurrentFlagBinary.regular
end CurrentAFT.CurrentFlagBinary.regular
namespace CurrentAFT.CurrentFlagBinary.targetEntry
end CurrentAFT.CurrentFlagBinary.targetEntry
namespace Integration9_9.TM2NativeIteration
end Integration9_9.TM2NativeIteration
namespace Integration9_9.TM2NativeIteration.NativeRequest
end Integration9_9.TM2NativeIteration.NativeRequest
namespace Integration9_9.TM2NativeIteration.NativeRequest.mk
end Integration9_9.TM2NativeIteration.NativeRequest.mk
namespace Integration9_9.TM2NativeIteration.Request
end Integration9_9.TM2NativeIteration.Request
namespace Integration9_9.TM2NativeIteration.Request.mk
end Integration9_9.TM2NativeIteration.Request.mk
namespace Integration9_9.TM2NativeIteration.State
end Integration9_9.TM2NativeIteration.State
namespace Integration9_9.TM2NativeIteration.State.mk
end Integration9_9.TM2NativeIteration.State.mk
namespace Integration9_9.TM2NativeIteration.baseSize
end Integration9_9.TM2NativeIteration.baseSize
namespace Integration9_9.TM2NativeIteration.body
end Integration9_9.TM2NativeIteration.body
namespace Integration9_9.TM2NativeIteration.decodeRequest
end Integration9_9.TM2NativeIteration.decodeRequest
namespace Integration9_9.TM2NativeIteration.fields
end Integration9_9.TM2NativeIteration.fields
namespace Integration9_9.TM2NativeIteration.fieldsCode
end Integration9_9.TM2NativeIteration.fieldsCode
namespace Integration9_9.TM2NativeIteration.fieldsNextProgram
end Integration9_9.TM2NativeIteration.fieldsNextProgram
namespace Integration9_9.TM2NativeIteration.fieldsStart
end Integration9_9.TM2NativeIteration.fieldsStart
namespace Integration9_9.TM2NativeIteration.heightBudget
end Integration9_9.TM2NativeIteration.heightBudget
namespace Integration9_9.TM2NativeIteration.nativeFields
end Integration9_9.TM2NativeIteration.nativeFields
namespace Integration9_9.TM2NativeIteration.nativeResult
end Integration9_9.TM2NativeIteration.nativeResult
namespace Integration9_9.TM2NativeIteration.next
end Integration9_9.TM2NativeIteration.next
namespace Integration9_9.TM2NativeIteration.qApply
end Integration9_9.TM2NativeIteration.qApply
namespace Integration9_9.TM2NativeIteration.qApplyProgram
end Integration9_9.TM2NativeIteration.qApplyProgram
namespace Integration9_9.TM2NativeIteration.qDot
end Integration9_9.TM2NativeIteration.qDot
namespace Integration9_9.TM2NativeIteration.qDotProgram
end Integration9_9.TM2NativeIteration.qDotProgram
namespace Integration9_9.TM2NativeIteration.requestCode
end Integration9_9.TM2NativeIteration.requestCode
namespace Integration9_9.TM2NativeIteration.requestFields
end Integration9_9.TM2NativeIteration.requestFields
namespace Integration9_9.TM2NativeIteration.requestFieldsCode
end Integration9_9.TM2NativeIteration.requestFieldsCode
namespace Integration9_9.TM2NativeIteration.requestResult
end Integration9_9.TM2NativeIteration.requestResult
namespace Integration9_9.TM2NativeIteration.result
end Integration9_9.TM2NativeIteration.result
namespace Integration9_9.TM2NativeIteration.sizeBudget
end Integration9_9.TM2NativeIteration.sizeBudget
namespace Integration9_9.TM2NativeIteration.start
end Integration9_9.TM2NativeIteration.start
namespace Integration9_9.TM2NativeIteration.stateCode
end Integration9_9.TM2NativeIteration.stateCode
namespace Integration9_9.TM2NativeLinearAlgebra
end Integration9_9.TM2NativeLinearAlgebra
namespace Integration9_9.TM2NativeLinearAlgebra.decodedVector
end Integration9_9.TM2NativeLinearAlgebra.decodedVector
namespace Integration9_9.TM2NativeLinearAlgebra.dot
end Integration9_9.TM2NativeLinearAlgebra.dot
namespace Integration9_9.TM2NativeLinearAlgebra.matrixList
end Integration9_9.TM2NativeLinearAlgebra.matrixList
namespace Integration9_9.TM2NativeLinearAlgebra.rawMatrixCode
end Integration9_9.TM2NativeLinearAlgebra.rawMatrixCode
namespace Integration9_9.TM2NativeLinearAlgebra.rawVectorCode
end Integration9_9.TM2NativeLinearAlgebra.rawVectorCode
namespace Integration9_9.TM2NativeLinearAlgebra.vectorList
end Integration9_9.TM2NativeLinearAlgebra.vectorList
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeChartProjection
open AFT AFT.BinaryArithmetic AFT.RationalNumerics AFT.BoundaryCalibration CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeChartMetadata
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h254 {n : ℕ} (mask : Vector Bool n) : _root_.Integration9_9.TM2NativeChartProjection.mass (List.ofFn mask.get)=((_root_.AFT.BinaryArithmetic.maskSet mask).card : ℚ) := by
  simp only [_root_.Integration9_9.TM2NativeChartProjection.mass,List.map_ofFn,Function.comp_def,List.sum_ofFn,_root_.AFT.BinaryArithmetic.maskSet,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num
open _root_.P2Mba49f952 renaming h254 → _p2mH254
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h253 {charts colors : ℕ} (feature : Fin charts→Fin colors)
    (profile : Fin charts→ℚ) (color : Fin colors) :
    _root_.Integration9_9.TM2NativeChartProjection.conditional ((colors,List.ofFn (fun i => (feature i).val)),(List.ofFn profile,color.val))=
      _root_.AFT.BoundaryCalibration.chartConditionalProgram charts colors feature profile color := by
  simp only [_root_.Integration9_9.TM2NativeChartProjection.conditional,List.length_ofFn,_root_.Integration9_9.TM2NativeChartMetadata.range_map,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,
    List.sum_ofFn,Fin.val_inj,_root_.AFT.BoundaryCalibration.chartConditionalProgram,_root_.AFT.BoundaryCalibration.chartExpectationProgram]
open _root_.P2Mba49f952 renaming h253 → _p2mH253
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h252 {charts colors : ℕ} (feature : Fin charts→Fin colors)
    (allowed : Vector Bool colors) (profile : Fin charts→ℚ) (point : Fin charts) :
    _root_.Integration9_9.TM2NativeChartProjection.component (((List.ofFn (fun i => (feature i).val),List.ofFn allowed.get),List.ofFn profile),point.val)=
      _root_.AFT.BoundaryCalibration.chartFeatureProgram charts colors feature (_root_.AFT.BinaryArithmetic.maskSet allowed) profile point := by
  simp only [_root_.Integration9_9.TM2NativeChartProjection.component,List.length_ofFn,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,_root_.Integration9_9.TM2NativeChartMetadata.range_map,
    _p2mH253,List.sum_ofFn,_p2mH254,_root_.AFT.BoundaryCalibration.chartFeatureProgram,_root_.AFT.BinaryArithmetic.maskSet,
    Finset.mem_filter,Finset.mem_univ,true_and,Finset.sum_filter]
open _root_.P2Mba49f952 renaming h252 → _p2mH252
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h255 {charts colors features : ℕ}
    (d : _root_.CurrentAFT.CurrentFlagBinaryMetadata.Data charts colors features) (profile : Fin charts→ℚ) (point : Fin charts) :
    _root_.Integration9_9.TM2NativeChartProjection.projection ((_root_.Integration9_9.TM2NativeChartMetadata.data d,List.ofFn profile),point.val)=
      _root_.AFT.BoundaryCalibration.chartProjectionProgram charts colors features (fun i => (d.feature.get i).get)
        (fun i => _root_.AFT.BinaryArithmetic.maskSet (d.allowed.get i)) profile point := by
  simp only [_root_.Integration9_9.TM2NativeChartProjection.projection,_root_.Integration9_9.TM2NativeChartMetadata.data,List.length_ofFn,_root_.Integration9_9.TM2NativeChartMetadata.range_map,List.sum_ofFn,List.getElem?_ofFn,
    Fin.isLt,dif_pos,Option.getD_some,_p2mH252,_root_.AFT.BoundaryCalibration.chartProjectionProgram,_root_.AFT.BoundaryCalibration.chartExpectationProgram]
open _root_.P2Mba49f952 renaming h255 → _p2mH255
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h256 {charts : ℕ} (fiber : Vector Bool charts) :
    _root_.Integration9_9.TM2NativeChartProjection.spike (List.ofFn fiber.get)=List.ofFn (_root_.AFT.BoundaryCalibration.chartSpikeProgram charts (_root_.AFT.BinaryArithmetic.maskSet fiber)) := by
  simp only [_root_.Integration9_9.TM2NativeChartProjection.spike,List.map_ofFn,List.length_ofFn,_p2mH254,Function.comp_def,_root_.AFT.BoundaryCalibration.chartSpikeProgram,
    _root_.AFT.BinaryArithmetic.maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
  apply congrArg List.ofFn
  funext i
  simp only [_root_.AFT.BoundaryCalibration.chartSpikeProgram,Finset.mem_filter,Finset.mem_univ,true_and]
open _root_.P2Mba49f952 renaming h256 → _p2mH256
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h257 {charts colors features : ℕ}
    (d : _root_.CurrentAFT.CurrentFlagBinaryMetadata.Data charts colors features) (point : Fin charts) :
    _root_.Integration9_9.TM2NativeChartProjection.target (_root_.Integration9_9.TM2NativeChartMetadata.data d,point.val)=
      _root_.CurrentAFT.CurrentFlagArray.target charts (fun i => (d.feature.get i).get)
        (fun i => _root_.AFT.BinaryArithmetic.maskSet (d.allowed.get i)) d.line.get (1/2)
        (_root_.AFT.BoundaryCalibration.chartSpikeProgram charts (_root_.AFT.BinaryArithmetic.maskSet d.fiber)) point := by
  simp only [_root_.Integration9_9.TM2NativeChartProjection.target,_root_.Integration9_9.TM2NativeChartMetadata.data,List.length_ofFn,_root_.Integration9_9.TM2NativeChartMetadata.range_map,_p2mH256,List.sum_ofFn,List.getElem?_ofFn,
    Fin.isLt,dif_pos,Option.getD_some,_p2mH252,_root_.CurrentAFT.CurrentFlagArray.target,_root_.CurrentAFT.CurrentFlagArray.defect,
    _p2mH152]
  norm_num
open _root_.P2Mba49f952 renaming h257 → _p2mH257
end Integration9_9.TM2NativeChartProjection
open _root_.P2Mba49f952 renaming h252 → _p2mH252
open _root_.P2Mba49f952 renaming h253 → _p2mH253
open _root_.P2Mba49f952 renaming h254 → _p2mH254
open _root_.P2Mba49f952 renaming h255 → _p2mH255
open _root_.P2Mba49f952 renaming h256 → _p2mH256
open _root_.P2Mba49f952 renaming h257 → _p2mH257
end
open _root_.P2Mba49f952 renaming h252 → _p2mH252
open _root_.P2Mba49f952 renaming h253 → _p2mH253
open _root_.P2Mba49f952 renaming h254 → _p2mH254
open _root_.P2Mba49f952 renaming h255 → _p2mH255
open _root_.P2Mba49f952 renaming h256 → _p2mH256
open _root_.P2Mba49f952 renaming h257 → _p2mH257
namespace CurrentAFT.CurrentFlagPublicProgram
end CurrentAFT.CurrentFlagPublicProgram
namespace CurrentAFT.CurrentFlagPublicProgram.half
end CurrentAFT.CurrentFlagPublicProgram.half
namespace Integration9_9.TM2NativeChartProjection
end Integration9_9.TM2NativeChartProjection
namespace Integration9_9.TM2NativeChartProjection.component
end Integration9_9.TM2NativeChartProjection.component
namespace Integration9_9.TM2NativeChartProjection.conditional
end Integration9_9.TM2NativeChartProjection.conditional
namespace Integration9_9.TM2NativeChartProjection.mass
end Integration9_9.TM2NativeChartProjection.mass
namespace Integration9_9.TM2NativeChartProjection.projection
end Integration9_9.TM2NativeChartProjection.projection
namespace Integration9_9.TM2NativeChartProjection.spike
end Integration9_9.TM2NativeChartProjection.spike
namespace Integration9_9.TM2NativeChartProjection.target
end Integration9_9.TM2NativeChartProjection.target
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeChartIteration
open AFT AFT.RationalNumerics AFT.BinaryArithmetic AFT.BoundaryCalibration CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeChartMetadata TM2NativeChartProjection
attribute [local irreducible] iterate
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h236 {charts : ℕ} (safe : Vector Bool charts) (input : Fin charts) :
    _root_.Integration9_9.TM2NativeChartIteration.basis (List.ofFn safe.get,input.val)=
      List.ofFn (fun point : Fin charts=>if point∈_root_.AFT.BinaryArithmetic.maskSet safe then 0 else if point=input then 1 else 0) := by
  simp only [_root_.Integration9_9.TM2NativeChartIteration.basis,List.length_ofFn,_root_.Integration9_9.TM2NativeChartMetadata.range_map,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some,
    Fin.val_inj,_root_.AFT.BinaryArithmetic.maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
open _root_.P2Mba49f952 renaming h236 → _p2mH236
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h239 {charts colors features : ℕ}
    (d : _root_.CurrentAFT.CurrentFlagBinaryMetadata.Data charts colors features) (output input : Fin charts) :
    _root_.Integration9_9.TM2NativeChartIteration.entry (_root_.Integration9_9.TM2NativeChartMetadata.data d,(output.val,input.val))=
      _root_.AFT.BoundaryCalibration.chartDeletionMatrixProgram charts colors features (fun i => (d.feature.get i).get)
        (fun i => _root_.AFT.BinaryArithmetic.maskSet (d.allowed.get i)) (_root_.AFT.BinaryArithmetic.maskSet d.safe) output input := by
  unfold _root_.Integration9_9.TM2NativeChartIteration.entry
  change -_root_.Integration9_9.TM2NativeChartProjection.projection ((_root_.Integration9_9.TM2NativeChartMetadata.data d,_root_.Integration9_9.TM2NativeChartIteration.basis (List.ofFn d.safe.get,input.val)),output.val)=_
  rw [_p2mH236,_p2mH255]
  rfl
open _root_.P2Mba49f952 renaming h239 → _p2mH239
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h238 {charts colors features : ℕ}
    (d : _root_.CurrentAFT.CurrentFlagBinaryMetadata.Data charts colors features) : (_root_.Integration9_9.TM2NativeChartMetadata.data d).2.1.length=charts := by
  simp only [_root_.Integration9_9.TM2NativeChartMetadata.data,List.length_ofFn]
open _root_.P2Mba49f952 renaming h238 → _p2mH238
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h241 (n m : ℕ) (h : n=m) (matrix : ℕ→ℕ→ℚ) (rhs : ℕ→ℚ) (steps : ℕ) :
    (fun i : Fin m => _root_.AFT.RationalNumerics.linearIteration (fun o j : Fin n => matrix o.val j.val)
      (fun i : Fin n => rhs i.val) steps (Fin.cast h.symm i))=
    _root_.AFT.RationalNumerics.linearIteration (fun o j : Fin m => matrix o.val j.val) (fun i : Fin m => rhs i.val) steps := by
  subst m
  rfl
open _root_.P2Mba49f952 renaming h241 → _p2mH241
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h240 {charts colors features : ℕ}
    (d : _root_.CurrentAFT.CurrentFlagBinaryMetadata.Data charts colors features) (ticks : List Unit) :
    _root_.Integration9_9.TM2NativeChartIteration.iterate (_root_.Integration9_9.TM2NativeChartMetadata.data d,ticks)=List.ofFn (_root_.AFT.RationalNumerics.linearIteration
      (_root_.AFT.BoundaryCalibration.chartDeletionMatrixProgram charts colors features (fun i => (d.feature.get i).get)
        (fun i => _root_.AFT.BinaryArithmetic.maskSet (d.allowed.get i)) (_root_.AFT.BinaryArithmetic.maskSet d.safe))
      (_root_.CurrentAFT.CurrentFlagArray.target charts (fun i => (d.feature.get i).get)
        (fun i => _root_.AFT.BinaryArithmetic.maskSet (d.allowed.get i)) d.line.get (1/2)
        (_root_.AFT.BoundaryCalibration.chartSpikeProgram charts (_root_.AFT.BinaryArithmetic.maskSet d.fiber))) ticks.length) := by
  unfold _root_.Integration9_9.TM2NativeChartIteration.iterate _root_.Integration9_9.TM2NativeIteration.requestResult _root_.Integration9_9.TM2NativeChartIteration.request
  simp only [_p2mH238,_root_.Integration9_9.TM2NativeChartIteration.get_ofFn,Vector.get_ofFn]
  rw [_p2mH241 (_root_.Integration9_9.TM2NativeChartMetadata.data d).2.1.length charts (_p2mH238 d)
    (fun i j => _root_.Integration9_9.TM2NativeChartIteration.entry (_root_.Integration9_9.TM2NativeChartMetadata.data d,(i,j))) (fun i => _root_.Integration9_9.TM2NativeChartProjection.target (_root_.Integration9_9.TM2NativeChartMetadata.data d,i)) ticks.length]
  have hm : (fun o j : Fin charts => _root_.Integration9_9.TM2NativeChartIteration.entry (_root_.Integration9_9.TM2NativeChartMetadata.data d,(o.val,j.val)))=
      _root_.AFT.BoundaryCalibration.chartDeletionMatrixProgram charts colors features (fun i => (d.feature.get i).get)
        (fun i => _root_.AFT.BinaryArithmetic.maskSet (d.allowed.get i)) (_root_.AFT.BinaryArithmetic.maskSet d.safe) := by funext o j;exact _p2mH239 d o j
  have hr : (fun i : Fin charts => _root_.Integration9_9.TM2NativeChartProjection.target (_root_.Integration9_9.TM2NativeChartMetadata.data d,i.val))=
      _root_.CurrentAFT.CurrentFlagArray.target charts (fun i => (d.feature.get i).get)
        (fun i => _root_.AFT.BinaryArithmetic.maskSet (d.allowed.get i)) d.line.get (1/2)
        (_root_.AFT.BoundaryCalibration.chartSpikeProgram charts (_root_.AFT.BinaryArithmetic.maskSet d.fiber)) := by funext i;exact _p2mH257 d i
  rw [hm,hr]
open _root_.P2Mba49f952 renaming h240 → _p2mH240
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h237 {charts colors features : ℕ} [NeZero colors]
    (d : _root_.CurrentAFT.CurrentFlagBinaryMetadata.Data charts colors features) (ticks : List Unit) :
    _root_.Integration9_9.TM2NativeChartIteration.current (_root_.Integration9_9.TM2NativeChartMetadata.data d,ticks)=List.ofFn (fun point =>
      ((_root_.CurrentAFT.CurrentFlagBinary.regular d.feature d.allowed d.line d.safe d.fiber
        _root_.CurrentAFT.CurrentFlagPublicProgram.half.data ticks.length).data.get point).decode) := by
  simp only [_root_.Integration9_9.TM2NativeChartIteration.current,_root_.Integration9_9.TM2NativeChartIteration.indices,_p2mH238,_root_.Integration9_9.TM2NativeChartMetadata.range_map,_p2mH240,_p2mH156,
    _p2mH164]
  apply congrArg List.ofFn
  funext point
  change (if (List.ofFn d.safe.get)[point.val]?.getD false then _ else 0)=_
  simp only [List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
open _root_.P2Mba49f952 renaming h237 → _p2mH237
end Integration9_9.TM2NativeChartIteration
open _root_.P2Mba49f952 renaming h236 → _p2mH236
open _root_.P2Mba49f952 renaming h237 → _p2mH237
open _root_.P2Mba49f952 renaming h238 → _p2mH238
open _root_.P2Mba49f952 renaming h239 → _p2mH239
open _root_.P2Mba49f952 renaming h240 → _p2mH240
open _root_.P2Mba49f952 renaming h241 → _p2mH241
end
open _root_.P2Mba49f952 renaming h236 → _p2mH236
open _root_.P2Mba49f952 renaming h237 → _p2mH237
open _root_.P2Mba49f952 renaming h238 → _p2mH238
open _root_.P2Mba49f952 renaming h239 → _p2mH239
open _root_.P2Mba49f952 renaming h240 → _p2mH240
open _root_.P2Mba49f952 renaming h241 → _p2mH241
namespace AFT.BinaryArithmetic.binaryLegalChartIndex
end AFT.BinaryArithmetic.binaryLegalChartIndex
namespace AFT.BinaryArithmetic.binaryPositiveFinDraw
end AFT.BinaryArithmetic.binaryPositiveFinDraw
namespace CurrentAFT.CurrentFlagDraw
end CurrentAFT.CurrentFlagDraw
namespace CurrentAFT.CurrentFlagDraw.draw
end CurrentAFT.CurrentFlagDraw.draw
namespace CurrentAFT.CurrentFlagDraw.workBound
end CurrentAFT.CurrentFlagDraw.workBound
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeChartLegalize
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h244 (xs : List Bool) : _root_.Integration9_9.TM2NativeChartLegalize.fallback xs=(_root_.AFT.BinaryArithmetic.firstTrue xs).value.getD 0 := by
  rw [_root_.AFT.BinaryArithmetic.firstTrue_value,List.findIdx?_eq_guard_findIdx_lt]
  simp only [_root_.Integration9_9.TM2NativeChartLegalize.fallback,Option.guard,decide_eq_true_eq]
  split_ifs <;> rfl
open _root_.P2Mba49f952 renaming h244 → _p2mH244
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h242 {charts : ℕ} [NeZero charts] (mask : Vector Bool charts) (point : Fin charts) :
    _root_.Integration9_9.TM2NativeChartLegalize.current (List.ofFn mask.get,point.val)=(_root_.AFT.BinaryArithmetic.binaryLegalChartIndex mask point).value.val := by
  have hm : List.ofFn mask.get=mask.toList := by
    apply List.ext_getElem
    · simp
    · intros
      simp only [List.getElem_ofFn,Vector.getElem_toList]
      rfl
  simp only [_root_.Integration9_9.TM2NativeChartLegalize.current,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
  simp only [_p2mH244,hm,_root_.AFT.BinaryArithmetic.binaryLegalChartIndex,_root_.AFT.BinaryArithmetic.legalChartScan,_root_.AFT.BinaryArithmetic.readVector_value]
  split_ifs <;> rfl
open _root_.P2Mba49f952 renaming h242 → _p2mH242
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h243 {charts : ℕ} [NeZero charts] (raw : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) (mask : Vector Bool charts)
    (bits : ℕ) (word : Fin (bits+charts+1)→Fin 2) :
    _root_.Integration9_9.TM2NativeChartLegalize.draw ((List.ofFn (fun i=>(raw.get i).decode),List.ofFn mask.get),
      List.ofFn (fun i=>_root_.AFT.BinaryArithmetic.digitBoolean (word i)))=(_root_.CurrentAFT.CurrentFlagDraw.draw raw mask bits word).value.val := by
  rw [_root_.Integration9_9.TM2NativeChartLegalize.draw,_p2mH226]
  have h:=_p2mH242 mask ⟨(_root_.AFT.BinaryArithmetic.binaryPositiveFinDraw raw bits word).value,_root_.AFT.BinaryArithmetic.binaryPositiveFinDraw_lt raw bits word⟩
  exact h
open _root_.P2Mba49f952 renaming h243 → _p2mH243
end Integration9_9.TM2NativeChartLegalize
open _root_.P2Mba49f952 renaming h242 → _p2mH242
open _root_.P2Mba49f952 renaming h243 → _p2mH243
open _root_.P2Mba49f952 renaming h244 → _p2mH244
end
open _root_.P2Mba49f952 renaming h242 → _p2mH242
open _root_.P2Mba49f952 renaming h243 → _p2mH243
open _root_.P2Mba49f952 renaming h244 → _p2mH244
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeFlagDraw
open AFT AFT.BinaryArithmetic AFT.RationalNumerics AFT.BoundaryCalibration CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeChartCoordinates TM2NativeChartMetadata TM2NativeChartProjection
attribute [local irreducible] steps
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h321 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) (bits : List Unit) :
    (_root_.Integration9_9.TM2NativeFlagDraw.steps (p,bits)).length=_root_.CurrentAFT.CurrentFlagTargetNorm.precisionSteps p.1.length bits.length := by
  simp only [_root_.Integration9_9.TM2NativeFlagDraw.steps,List.length_append,_p2mH248,_root_.CurrentAFT.CurrentFlagTargetNorm.precisionSteps,List.length_cons,List.length_nil,pow_two]
  omega
open _root_.P2Mba49f952 renaming h321 → _p2mH321
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h320 {charts : ℕ} (raw : Vector _root_.AFT.BinaryArithmetic.RationalBits charts) :
    _root_.Integration9_9.TM2NativeFlagDraw.scale (List.ofFn (fun i=>(raw.get i).decode))=
      List.ofFn (fun i=>((_root_.CurrentAFT.CurrentFlagWeightArray.scale raw).data.get i).decode) := by
  simp only [_root_.Integration9_9.TM2NativeFlagDraw.scale,List.length_ofFn,List.map_ofFn,Function.comp_def,_p2mH166]
open _root_.P2Mba49f952 renaming h320 → _p2mH320
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h319 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) [NeZero p.2.length] (sign : Bool) (digits : List Bool)
    (mark : Fin p.2.length) (bits : List Unit) (drawBits : ℕ)
    (word : Fin (drawBits+p.2.length*(p.2.length*p.2.length)+1)→Fin 2) :
    _root_.Integration9_9.TM2NativeFlagDraw.regular ((((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),bits),List.ofFn (fun i=>_root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.CurrentAFT.CurrentFlagBranchDraw.regular p.1.length p.2.length sign digits mark bits.length drawBits word).value.val := by
  unfold _root_.Integration9_9.TM2NativeFlagDraw.regular
  rw [_p2mH247]
  dsimp only
  rw [_p2mH237,_p2mH320]
  change _root_.Integration9_9.TM2NativeChartLegalize.draw ((List.ofFn (fun i =>
    ((_root_.CurrentAFT.CurrentFlagWeightArray.scale (_root_.CurrentAFT.CurrentFlagBinary.regular _ _ _ _ _ _
      (_root_.Integration9_9.TM2NativeFlagDraw.steps (p,bits)).length).data).data.get i).decode),_),_)=_
  rw [_p2mH321]
  exact _p2mH243
    (_root_.CurrentAFT.CurrentFlagWeightArray.regularWeights p.1.length p.2.length sign digits mark
      (_root_.CurrentAFT.CurrentFlagTargetNorm.precisionSteps p.1.length bits.length)).data
    (_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.safe drawBits word
open _root_.P2Mba49f952 renaming h319 → _p2mH319
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h318 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) [NeZero p.2.length] (sign : Bool) (digits : List Bool)
    (mark : Fin p.2.length) (bits : List Unit) (drawBits : ℕ)
    (word : Fin (drawBits+p.2.length*(p.2.length*p.2.length)+1)→Fin 2) :
    _root_.Integration9_9.TM2NativeFlagDraw.marked ((((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),bits),List.ofFn (fun i=>_root_.AFT.BinaryArithmetic.digitBoolean (word i)))=
      (_root_.CurrentAFT.CurrentFlagBranchDraw.marked p.1.length p.2.length sign digits mark drawBits word).value.val := by
  unfold _root_.Integration9_9.TM2NativeFlagDraw.marked
  rw [_p2mH247]
  change _root_.Integration9_9.TM2NativeChartLegalize.draw ((_root_.Integration9_9.TM2NativeFlagDraw.scale (_root_.Integration9_9.TM2NativeChartProjection.spike (List.ofFn
    (_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.fiber.get)),_),_)=_
  rw [_p2mH256]
  have hs : List.ofFn (_root_.AFT.BoundaryCalibration.chartSpikeProgram (p.2.length*(p.2.length*p.2.length))
      (_root_.AFT.BinaryArithmetic.maskSet (_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.fiber))=
    List.ofFn (fun i=>((_root_.AFT.BinaryArithmetic.RationalBits.buildArray _ (_root_.AFT.BinaryArithmetic.RationalBits.chartSpike
      (_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.fiber)).data.get i).decode) := by
    simp only [_root_.AFT.BinaryArithmetic.RationalBits.buildArray_get,_p2mH11]
  rw [hs,_p2mH320]
  exact _p2mH243
    (_root_.CurrentAFT.CurrentFlagWeightArray.markedWeights p.1.length p.2.length sign digits mark).data
    (_root_.CurrentAFT.CurrentFlagBinaryMetadata.build p.1.length p.2.length false sign [true] digits mark).value.fiber drawBits word
open _root_.P2Mba49f952 renaming h318 → _p2mH318
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h317 (q : ℕ) [NeZero q] (x : Fin q) : ((ZMod.finEquiv q) x).val=x.val := by
  rw [_p2mH160]
  exact ZMod.val_natCast_of_lt x.isLt
open _root_.P2Mba49f952 renaming h317 → _p2mH317
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h315 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) [NeZero p.2.length] (sign : Bool) (digits : List Bool)
    (mark : Fin p.2.length) (bits : List Unit) (drawBits : ℕ)
    (word : _root_.CurrentAFT.CurrentFlagJointDraw.Tape p.2.length drawBits) :
    _root_.Integration9_9.TM2NativeFlagDraw.current ((((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),bits),_root_.Integration9_9.TM2NativeFlagDraw.tapeData word)=
      _root_.Integration9_9.TM2NativeFlagDraw.chartData (_root_.CurrentAFT.CurrentFlagChartDraw.draw p.1.length p.2.length sign digits mark bits.length drawBits word).value := by
  let selected:=_root_.CurrentAFT.CurrentFlagJointDraw.draw p.1.length p.2.length sign digits mark bits.length drawBits word
  have hi : (if word.1 then
      _root_.Integration9_9.TM2NativeFlagDraw.marked ((((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),bits),List.ofFn (fun i=>_root_.AFT.BinaryArithmetic.digitBoolean (word.2 i)))
    else _root_.Integration9_9.TM2NativeFlagDraw.regular ((((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),bits),List.ofFn (fun i=>_root_.AFT.BinaryArithmetic.digitBoolean (word.2 i))))=
      selected.value.2.val := by
    simp only [_p2mH319,_p2mH318,selected,_p2mH163]
    split_ifs <;> rfl
  have hf : selected.value.1=word.1 := by simp only [selected,_p2mH163]
  unfold _root_.Integration9_9.TM2NativeFlagDraw.current _root_.Integration9_9.TM2NativeFlagDraw.tapeData
  change (word.1,_root_.Integration9_9.TM2NativeChartCoordinates.coordinates (p.2.length,_))=_
  rw [hi,_p2mH232 _ _ (NeZero.pos _)]
  simp only [_root_.Integration9_9.TM2NativeFlagDraw.chartData,_root_.CurrentAFT.CurrentFlagChartDraw.draw,_root_.CurrentAFT.CurrentFlagBinaryMetadata.coordinates,_p2mH317]
  rw [←hf]
open _root_.P2Mba49f952 renaming h315 → _p2mH315
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h316 (p : _root_.Integration9_9.TM2NativeChartCoordinates.Params) (cutoff q : ℕ) [NeZero q]
    (hc : p.1.length=cutoff) (hq : p.2.length=q) (sign : Bool) (digits : List Bool)
    (mark : Fin q) (bits : List Unit) (drawBits : ℕ) (word : _root_.CurrentAFT.CurrentFlagJointDraw.Tape q drawBits) :
    _root_.Integration9_9.TM2NativeFlagDraw.current ((((p,_root_.AFT.BinaryArithmetic.signedValue sign digits),mark.val),bits),_root_.Integration9_9.TM2NativeFlagDraw.tapeData word)=
      _root_.Integration9_9.TM2NativeFlagDraw.chartData (_root_.CurrentAFT.CurrentFlagChartDraw.draw cutoff q sign digits mark bits.length drawBits word).value := by
  subst cutoff
  subst q
  exact _p2mH315 p sign digits mark bits drawBits word
open _root_.P2Mba49f952 renaming h316 → _p2mH316
end Integration9_9.TM2NativeFlagDraw
open _root_.P2Mba49f952 renaming h315 → _p2mH315
open _root_.P2Mba49f952 renaming h316 → _p2mH316
open _root_.P2Mba49f952 renaming h317 → _p2mH317
open _root_.P2Mba49f952 renaming h318 → _p2mH318
open _root_.P2Mba49f952 renaming h319 → _p2mH319
open _root_.P2Mba49f952 renaming h320 → _p2mH320
open _root_.P2Mba49f952 renaming h321 → _p2mH321
end
open _root_.P2Mba49f952 renaming h315 → _p2mH315
open _root_.P2Mba49f952 renaming h316 → _p2mH316
open _root_.P2Mba49f952 renaming h317 → _p2mH317
open _root_.P2Mba49f952 renaming h318 → _p2mH318
open _root_.P2Mba49f952 renaming h319 → _p2mH319
open _root_.P2Mba49f952 renaming h320 → _p2mH320
open _root_.P2Mba49f952 renaming h321 → _p2mH321
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeFlagCompletion
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeChartCoordinates TM2NativeFlagDraw
attribute [local irreducible] TM2NativeProfile.scalarTicks TM2NativeBodyKernel.paletteTicks TM2NativeCoreCharge.shift TM2NativeFlagDraw.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h314 (x : _root_.Integration9_9.TM2NativeFlagCompletion.Meta) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette x.1.length)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed x.1.length) (bits : ℕ)
    (word : _root_.CurrentAFT.CurrentFlagJointDraw.Tape (_root_.CurrentAFT.Parameters.modulus x.1.length) bits) :
    _root_.Integration9_9.TM2NativeFlagCompletion.current ((x,(primary.val,_root_.Integration9_9.TM2NativePublicSeed.seedData seed)),_root_.Integration9_9.TM2NativeFlagDraw.tapeData word)=
      _root_.Integration9_9.TM2NativeFlagDraw.chartData (_root_.CurrentAFT.CurrentFlagCompletionProgram.draw x.1.length primary seed x.2.length bits word).value := by
  letI : NeZero (_root_.CurrentAFT.Parameters.modulus x.1.length) := ⟨(_root_.CurrentAFT.Parameters.modulus_spec x.1.length).2.ne_zero⟩
  unfold _root_.Integration9_9.TM2NativeFlagCompletion.current
  rw [_p2mH264,_p2mH162]
  have hs : _root_.AFT.BinaryArithmetic.signedValue (_root_.CurrentAFT.CurrentPublicShiftProgram.current x.1.length primary seed).value.negative
      (_root_.CurrentAFT.CurrentPublicShiftProgram.current x.1.length primary seed).value.digits=
      _root_.CurrentAFT.ActualPublicLegCharge.publicShift x.1.length primary seed := _p2mH180 _ _ _
  rw [←hs]
  exact _p2mH316 (_root_.Integration9_9.TM2NativeFlagCompletion.params x.1) (_root_.CurrentAFT.Parameters.sourceCutoff x.1.length-1) (_root_.CurrentAFT.Parameters.modulus x.1.length)
    (by simp only [_root_.Integration9_9.TM2NativeFlagCompletion.params,_root_.Integration9_9.TM2NativeProfile.scalarTicks_length,_root_.CurrentAFT.Parameters.sourceCutoff,_root_.CurrentAFT.Parameters.base])
    (by simp only [_root_.Integration9_9.TM2NativeFlagCompletion.params,_root_.Integration9_9.TM2NativeBodyKernel.paletteTicks_length]) _ _ primary x.2 bits word
open _root_.P2Mba49f952 renaming h314 → _p2mH314
end Integration9_9.TM2NativeFlagCompletion
open _root_.P2Mba49f952 renaming h314 → _p2mH314
end
open _root_.P2Mba49f952 renaming h314 → _p2mH314
namespace CurrentAFT.CurrentChartsDraw
end CurrentAFT.CurrentChartsDraw
namespace CurrentAFT.CurrentChartsDraw.draw
end CurrentAFT.CurrentChartsDraw.draw
namespace CurrentAFT.CurrentChartsDraw.drawStored
end CurrentAFT.CurrentChartsDraw.drawStored
namespace CurrentAFT.CurrentChartsDraw.inputsOfCore
end CurrentAFT.CurrentChartsDraw.inputsOfCore
namespace CurrentAFT.CurrentPublicAffineSample.chartsLaw
end CurrentAFT.CurrentPublicAffineSample.chartsLaw
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeCharts
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal TM2NativeFlagDraw
attribute [local irreducible] CurrentProposalDimensions.current CurrentAFT.Parameters.legCount
  TM2NativeFlagCompletion.current CurrentChartsDraw.drawStored CurrentChartsDraw.draw
  CurrentFlagCompletionProgram.draw
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h259 (x : _root_.Integration9_9.TM2NativeFlagCompletion.Meta) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore x.1.length)
    (i : Fin (_root_.CurrentAFT.Parameters.legCount x.1.length)) :
    _root_.Integration9_9.TM2NativeCharts.input ((x,_root_.Integration9_9.TM2NativeCoreProposal.coreData core),i.val)=
      (x,((core.inputs.get i).1.val,_root_.Integration9_9.TM2NativePublicSeed.seedData (core.inputs.get i).2)) := by
  have hi : i.val<(_root_.CurrentAFT.CurrentProposalDimensions.current x.1.length).legs := by
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values x.1.length).2.1];exact i.isLt
  have hc : i.val<(_root_.CurrentAFT.CurrentProposalDimensions.current x.1.length).controls := by
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values x.1.length).2.2.2.2.2]
    exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  simp only [_root_.Integration9_9.TM2NativeCharts.input,_root_.Integration9_9.TM2NativeCoreProposal.coreData,_root_.Integration9_9.TM2NativeCoreProposal.controlData,_root_.Integration9_9.TM2NativeCoreProposal.legData,List.getElem?_ofFn,hi,hc,dif_pos,Option.getD_some,
    core.inputs_correct]
  rfl
open _root_.P2Mba49f952 renaming h259 → _p2mH259
attribute [local irreducible] input coreData
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h258 (x : _root_.Integration9_9.TM2NativeFlagCompletion.Meta) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore x.1.length)
    (bits : ℕ) (word : _root_.CurrentAFT.CurrentChartsDraw.Tapes x.1.length bits) :
    _root_.Integration9_9.TM2NativeCharts.current ((x,_root_.Integration9_9.TM2NativeCoreProposal.coreData core),List.ofFn (fun i=>_root_.Integration9_9.TM2NativeFlagDraw.tapeData (word i)))=
      _root_.Integration9_9.TM2NativeEmitterData.chartsData (_root_.CurrentAFT.CurrentChartsDraw.drawStored x.1.length core.inputs x.2.length bits word).value := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeCharts.current,List.length_map,List.length_range,_root_.Integration9_9.TM2NativeCoreProposal.coreData,List.length_ofFn,
      _root_.Integration9_9.TM2NativeEmitterData.chartsData]
    exact (_root_.CurrentAFT.CurrentProposalDimensions.current_values x.1.length).2.1
  · intro i hi hj
    have hb : i<_root_.CurrentAFT.Parameters.legCount x.1.length := by
      simpa only [_root_.Integration9_9.TM2NativeEmitterData.chartsData,List.length_ofFn] using hj
    simp only [_root_.Integration9_9.TM2NativeCharts.current,List.getElem_map,List.getElem_range,List.getElem?_ofFn,hb,dif_pos,Option.getD_some]
    have hinput:=_p2mH259 x core ⟨i,hb⟩
    have hfirst:=congrArg (fun inp=>_root_.Integration9_9.TM2NativeFlagCompletion.current (inp,_root_.Integration9_9.TM2NativeFlagDraw.tapeData (word ⟨i,hb⟩))) hinput
    have hsecond:=_p2mH314 x (core.inputs.get ⟨i,hb⟩).1
      (core.inputs.get ⟨i,hb⟩).2 bits (word ⟨i,hb⟩)
    have hlast:=congrArg _root_.Integration9_9.TM2NativeFlagDraw.chartData (_p2mH144 x.1.length core.inputs x.2.length bits word ⟨i,hb⟩)
    have h:=hfirst.trans (hsecond.trans hlast.symm)
    simpa only [_root_.Integration9_9.TM2NativeEmitterData.chartsData,List.getElem_ofFn,_root_.CurrentAFT.CurrentChartsDraw.draw,
      _root_.Integration9_9.TM2NativeEmitterData.chartData,_root_.Integration9_9.TM2NativeFlagDraw.chartData] using h
open _root_.P2Mba49f952 renaming h258 → _p2mH258
end Integration9_9.TM2NativeCharts
open _root_.P2Mba49f952 renaming h258 → _p2mH258
open _root_.P2Mba49f952 renaming h259 → _p2mH259
end
open _root_.P2Mba49f952 renaming h258 → _p2mH258
open _root_.P2Mba49f952 renaming h259 → _p2mH259
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeCompletion
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal
attribute [local irreducible] TM2NativeCharts.current TM2NativePublicSeed.edgeDraw
  CurrentMaterializedCompletion.complete CurrentChartsDraw.drawStored
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h260 (p : _root_.Integration9_9.TM2NativeCompletion.Meta) (input : Option (_root_.CurrentAFT.CurrentCoreProposal.MaterializedCore p.1.1.length))
    (bits : ℕ) (word : _root_.CurrentAFT.CurrentPublicCompletion.Tapes p.1.1.length bits p.2.length) :
    _root_.Integration9_9.TM2NativeCompletion.current ((p,_root_.Integration9_9.TM2NativePublicRejection.resultData input),_root_.Integration9_9.TM2NativeCompletion.tapesData word)=
      _root_.Integration9_9.TM2NativeEmitter.resultData (_root_.CurrentAFT.CurrentMaterializedCompletion.complete p.1.1.length input p.1.2.length bits p.2.length word).value := by
  cases input with
  | none => simp only [_root_.Integration9_9.TM2NativeCompletion.current,_root_.Integration9_9.TM2NativePublicRejection.resultData,Bool.false_eq_true,ite_false,
      _root_.CurrentAFT.CurrentMaterializedCompletion.complete,_root_.Integration9_9.TM2NativeEmitter.resultData]
  | some core =>
    simp only [_root_.Integration9_9.TM2NativeCompletion.current,_root_.Integration9_9.TM2NativePublicRejection.resultData,ite_true,_root_.Integration9_9.TM2NativeCompletion.tapesData,_p2mH258,
      _p2mH342,_root_.CurrentAFT.CurrentMaterializedCompletion.complete,_root_.Integration9_9.TM2NativeEmitter.resultData]
open _root_.P2Mba49f952 renaming h260 → _p2mH260
end Integration9_9.TM2NativeCompletion
open _root_.P2Mba49f952 renaming h260 → _p2mH260
end
open _root_.P2Mba49f952 renaming h260 → _p2mH260
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeTapes
open AFT AFT.BinaryArithmetic CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal TM2NativeTapeCodec
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
  PublicParameterProgram.modulus BinaryRejectionCap.current BinaryPublicBitSizes.current
  TM2NativeTapeLengths.retriesTicks TM2NativeTapeLengths.chart legTicks
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h403 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapes.attemptEncoding xs.length).bits → Fin 2) :
    _root_.Integration9_9.TM2NativeTapes.attempt (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      (_root_.Integration9_9.TM2NativeCoreProposal.tapesData ((_root_.Integration9_9.TM2NativeTapes.attemptEncoding xs.length).equiv word).1,_root_.Integration9_9.TM2NativeTapeCodec.wordData ((_root_.Integration9_9.TM2NativeTapes.attemptEncoding xs.length).equiv word).2) := by
  unfold _root_.Integration9_9.TM2NativeTapes.attempt _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH380]
  exact _p2mH364 (_root_.CurrentAFT.PublicBitTapes.core xs.length xs.length) (_root_.CurrentAFT.PublicBitTapes.bits xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapeCore.current (xs,word)) id _root_.Integration9_9.TM2NativeCoreProposal.tapesData _root_.Integration9_9.TM2NativeTapeCodec.wordData
    (_p2mH371 xs) (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h403 → _p2mH403
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h402 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapes.attemptBits xs=(_root_.Integration9_9.TM2NativeTapes.attemptEncoding xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapes.attemptBits,_p2mH380,_root_.Integration9_9.TM2NativeTapes.attemptEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.bits]
open _root_.P2Mba49f952 renaming h402 → _p2mH402
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h405 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.rejection xs.length).bits → Fin 2) :
    _root_.Integration9_9.TM2NativeTapes.attempts (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeCappedRejection.tapeData ((_root_.CurrentAFT.PublicBitTapes.rejection xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapes.attempts _root_.Integration9_9.TM2NativeTapeCodec.indexedWith
  rw [_p2mH402]
  exact _p2mH374 (_root_.Integration9_9.TM2NativeTapeLengths.retriesTicks xs) _
    (_p2mH393 xs) (Equiv.refl _) (_root_.Integration9_9.TM2NativeTapes.attemptEncoding xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapes.attempt (xs,word)) (fun p=>(_root_.Integration9_9.TM2NativeCoreProposal.tapesData p.1,_root_.Integration9_9.TM2NativeTapeCodec.wordData p.2)) (_p2mH403 xs) word
open _root_.P2Mba49f952 renaming h405 → _p2mH405
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h404 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapes.attemptsBits xs=(_root_.CurrentAFT.PublicBitTapes.rejection xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapes.attemptsBits,_p2mH393,_p2mH402,
    _root_.CurrentAFT.PublicBitTapes.rejection,_root_.Integration9_9.TM2NativeTapes.attemptEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.indexed]
open _root_.P2Mba49f952 renaming h404 → _p2mH404
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h413 (xs : List Unit) (word : Fin (_root_.Integration9_9.TM2NativeTapes.flagChartEncoding xs.length).bits → Fin 2) :
    _root_.Integration9_9.TM2NativeTapes.flagChart (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeFlagDraw.tapeData ((_root_.Integration9_9.TM2NativeTapes.flagChartEncoding xs.length).equiv word) := by
  exact _p2mH364 _root_.CurrentAFT.PublicBitTapes.flag
    (_root_.CurrentAFT.PublicBitTapes.bits (xs.length+_root_.CurrentAFT.Parameters.modulus xs.length*(_root_.CurrentAFT.Parameters.modulus xs.length*_root_.CurrentAFT.Parameters.modulus xs.length)+1))
    _root_.Integration9_9.TM2NativeTapeCodec.flag id id _root_.Integration9_9.TM2NativeTapeCodec.wordData _p2mH363 (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h413 → _p2mH413
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h412 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapes.flagChartBits xs=(_root_.Integration9_9.TM2NativeTapes.flagChartEncoding xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapes.flagChartBits,_p2mH388,_root_.CurrentAFT.BinaryPublicBitSizes.chart_value,
    _root_.Integration9_9.TM2NativeTapes.flagChartEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.flag,_root_.CurrentAFT.PublicBitTapes.bits]
open _root_.P2Mba49f952 renaming h412 → _p2mH412
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h407 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.charts xs.length xs.length).bits → Fin 2) :
    _root_.Integration9_9.TM2NativeTapes.charts (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapes.chartsData ((_root_.CurrentAFT.PublicBitTapes.charts xs.length xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapes.charts _root_.Integration9_9.TM2NativeTapeCodec.indexedWith
  rw [_p2mH412]
  have h := _p2mH374 (_root_.Integration9_9.TM2NativeCoreProposal.legTicks xs) _ (_p2mH271 xs)
    (_root_.CurrentAFT.CurrentProposalDimensions.legEquiv xs.length) (_root_.Integration9_9.TM2NativeTapes.flagChartEncoding xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapes.flagChart (xs,word)) _root_.Integration9_9.TM2NativeFlagDraw.tapeData (_p2mH413 xs) word
  rw [h]
  apply List.ext_getElem
  · simp only [List.length_ofFn,_root_.Integration9_9.TM2NativeTapes.chartsData]
    exact (_root_.CurrentAFT.CurrentProposalDimensions.current_values xs.length).2.1
  · intro i hi hj
    simp only [List.getElem_ofFn,_root_.Integration9_9.TM2NativeTapes.chartsData]
    rfl
open _root_.P2Mba49f952 renaming h407 → _p2mH407
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h406 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapes.chartsBits xs=(_root_.CurrentAFT.PublicBitTapes.charts xs.length xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapes.chartsBits,_p2mH271,_p2mH412,_root_.CurrentAFT.PublicBitTapes.charts,_root_.Integration9_9.TM2NativeTapes.flagChartEncoding,_root_.CurrentAFT.PublicBitTapes.Encoding.indexed]
open _root_.P2Mba49f952 renaming h406 → _p2mH406
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h409 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.completion xs.length).bits → Fin 2) :
    _root_.Integration9_9.TM2NativeTapes.completion (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeCompletion.tapesData ((_root_.CurrentAFT.PublicBitTapes.completion xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapes.completion _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH406]
  exact _p2mH364 (_root_.CurrentAFT.PublicBitTapes.charts xs.length xs.length) (_root_.CurrentAFT.PublicBitTapes.edge xs.length xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapes.charts (xs,word)) id _root_.Integration9_9.TM2NativeTapes.chartsData _root_.Integration9_9.TM2NativeTapeCodec.wordData (_p2mH407 xs) (fun _=>rfl) word
open _root_.P2Mba49f952 renaming h409 → _p2mH409
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h408 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapes.completionBits xs=(_root_.CurrentAFT.PublicBitTapes.completion xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapes.completionBits,_p2mH406,_p2mH391,_root_.CurrentAFT.BinaryPublicBitSizes.edge_value,
    _root_.CurrentAFT.PublicBitTapes.completion,_root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.edge,_root_.CurrentAFT.PublicBitTapes.bits]
open _root_.P2Mba49f952 renaming h408 → _p2mH408
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h415 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.materialized xs.length).bits → Fin 2) :
    _root_.Integration9_9.TM2NativeTapes.materialized (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      (_root_.Integration9_9.TM2NativeCappedRejection.tapeData ((_root_.CurrentAFT.PublicBitTapes.materialized xs.length).equiv word).1,
        _root_.Integration9_9.TM2NativeCompletion.tapesData ((_root_.CurrentAFT.PublicBitTapes.materialized xs.length).equiv word).2) := by
  unfold _root_.Integration9_9.TM2NativeTapes.materialized _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH404]
  exact _p2mH364 (_root_.CurrentAFT.PublicBitTapes.rejection xs.length) (_root_.CurrentAFT.PublicBitTapes.completion xs.length)
    (fun word=>_root_.Integration9_9.TM2NativeTapes.attempts (xs,word)) (fun word=>_root_.Integration9_9.TM2NativeTapes.completion (xs,word))
    _root_.Integration9_9.TM2NativeCappedRejection.tapeData _root_.Integration9_9.TM2NativeCompletion.tapesData (_p2mH405 xs) (_p2mH409 xs) word
open _root_.P2Mba49f952 renaming h415 → _p2mH415
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h414 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapes.materializedBits xs=(_root_.CurrentAFT.PublicBitTapes.materialized xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapes.materializedBits,_p2mH404,_p2mH408,_root_.CurrentAFT.PublicBitTapes.materialized,_root_.CurrentAFT.PublicBitTapes.Encoding.prod]
open _root_.P2Mba49f952 renaming h414 → _p2mH414
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h411 (xs : List Unit) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current xs.length).bits → Fin 2) :
    _root_.Integration9_9.TM2NativeTapes.decoded (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapes.tapesData ((_root_.CurrentAFT.PublicBitTapes.current xs.length).equiv word) := by
  unfold _root_.Integration9_9.TM2NativeTapes.decoded _root_.Integration9_9.TM2NativeTapeCodec.productWith
  rw [_p2mH387,_root_.CurrentAFT.BinaryPublicBitSizes.body_value]
  exact _p2mH364 (_root_.CurrentAFT.PublicBitTapes.bits ((_root_.CurrentAFT.CurrentProposalDimensions.current xs.length).body*xs.length))
    (_root_.CurrentAFT.PublicBitTapes.materialized xs.length) id (fun word=>_root_.Integration9_9.TM2NativeTapes.materialized (xs,word)) _root_.Integration9_9.TM2NativeTapeCodec.wordData
    (fun p=>(_root_.Integration9_9.TM2NativeCappedRejection.tapeData p.1,_root_.Integration9_9.TM2NativeCompletion.tapesData p.2))
    (fun _=>rfl) (_p2mH415 xs) word
open _root_.P2Mba49f952 renaming h411 → _p2mH411
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h417 (xs : List Unit) : _root_.Integration9_9.TM2NativeTapes.totalBits xs=(_root_.CurrentAFT.PublicBitTapes.current xs.length).bits := by
  simp only [_root_.Integration9_9.TM2NativeTapes.totalBits,_p2mH387,_root_.CurrentAFT.BinaryPublicBitSizes.body_value,_p2mH414,
    _root_.CurrentAFT.PublicBitTapes.current,_root_.CurrentAFT.PublicBitTapes.Encoding.prod,_root_.CurrentAFT.PublicBitTapes.bits]
open _root_.P2Mba49f952 renaming h417 → _p2mH417
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h416 (count total : ℕ) (h : count ≤ total) (word : Fin total → Fin 2) :
    _root_.Integration9_9.TM2NativeTapeCodec.take (count,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativeTapeCodec.wordData (fun i : Fin count=>word (i.castLE h)) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.TM2NativeTapeCodec.take,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.length_take,List.length_ofFn,Nat.min_eq_left h]
  · intro i hi hj
    simp only [_root_.Integration9_9.TM2NativeTapeCodec.take,_root_.Integration9_9.TM2NativeTapeCodec.wordData,List.getElem_take,List.getElem_ofFn]
    rfl
open _root_.P2Mba49f952 renaming h416 → _p2mH416
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h410 (xs : List Unit) (total : ℕ) (h : (_root_.CurrentAFT.PublicBitTapes.current xs.length).bits ≤ total)
    (word : Fin total → Fin 2) :
    _root_.Integration9_9.TM2NativeTapes.current (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      _root_.Integration9_9.TM2NativeTapes.tapesData ((_root_.CurrentAFT.PublicBitTapes.current xs.length).equiv (fun i=>word (i.castLE h))) := by
  unfold _root_.Integration9_9.TM2NativeTapes.current
  rw [_p2mH417,_p2mH416 _ _ h,_p2mH411]
open _root_.P2Mba49f952 renaming h410 → _p2mH410
end Integration9_9.TM2NativeTapes
open _root_.P2Mba49f952 renaming h402 → _p2mH402
open _root_.P2Mba49f952 renaming h403 → _p2mH403
open _root_.P2Mba49f952 renaming h404 → _p2mH404
open _root_.P2Mba49f952 renaming h405 → _p2mH405
open _root_.P2Mba49f952 renaming h406 → _p2mH406
open _root_.P2Mba49f952 renaming h407 → _p2mH407
open _root_.P2Mba49f952 renaming h408 → _p2mH408
open _root_.P2Mba49f952 renaming h409 → _p2mH409
open _root_.P2Mba49f952 renaming h410 → _p2mH410
open _root_.P2Mba49f952 renaming h411 → _p2mH411
open _root_.P2Mba49f952 renaming h412 → _p2mH412
open _root_.P2Mba49f952 renaming h413 → _p2mH413
open _root_.P2Mba49f952 renaming h414 → _p2mH414
open _root_.P2Mba49f952 renaming h415 → _p2mH415
open _root_.P2Mba49f952 renaming h416 → _p2mH416
open _root_.P2Mba49f952 renaming h417 → _p2mH417
end
open _root_.P2Mba49f952 renaming h402 → _p2mH402
open _root_.P2Mba49f952 renaming h403 → _p2mH403
open _root_.P2Mba49f952 renaming h404 → _p2mH404
open _root_.P2Mba49f952 renaming h405 → _p2mH405
open _root_.P2Mba49f952 renaming h406 → _p2mH406
open _root_.P2Mba49f952 renaming h407 → _p2mH407
open _root_.P2Mba49f952 renaming h408 → _p2mH408
open _root_.P2Mba49f952 renaming h409 → _p2mH409
open _root_.P2Mba49f952 renaming h410 → _p2mH410
open _root_.P2Mba49f952 renaming h411 → _p2mH411
open _root_.P2Mba49f952 renaming h412 → _p2mH412
open _root_.P2Mba49f952 renaming h413 → _p2mH413
open _root_.P2Mba49f952 renaming h414 → _p2mH414
open _root_.P2Mba49f952 renaming h415 → _p2mH415
open _root_.P2Mba49f952 renaming h416 → _p2mH416
open _root_.P2Mba49f952 renaming h417 → _p2mH417
namespace AFT.BinaryArithmetic.RationalBits.copy
end AFT.BinaryArithmetic.RationalBits.copy
namespace AFT.BinaryArithmetic.copy
end AFT.BinaryArithmetic.copy
namespace AFT.BinaryArithmetic.copy.match_1
end AFT.BinaryArithmetic.copy.match_1
namespace CurrentAFT.ActualConstructiveSampler
end CurrentAFT.ActualConstructiveSampler
namespace CurrentAFT.ActualConstructiveSampler.law
end CurrentAFT.ActualConstructiveSampler.law
namespace CurrentAFT.ActualConstructiveSampler.run
end CurrentAFT.ActualConstructiveSampler.run
namespace CurrentAFT.ActualConstructiveSampler.workPolynomial
end CurrentAFT.ActualConstructiveSampler.workPolynomial
namespace CurrentAFT.BinaryBackgroundPopulation
end CurrentAFT.BinaryBackgroundPopulation
namespace CurrentAFT.BinaryBackgroundPopulation.Role
end CurrentAFT.BinaryBackgroundPopulation.Role
namespace CurrentAFT.BinaryBackgroundPopulation.Role.free
end CurrentAFT.BinaryBackgroundPopulation.Role.free
namespace CurrentAFT.BinaryBackgroundPopulation.Role.leg
end CurrentAFT.BinaryBackgroundPopulation.Role.leg
namespace CurrentAFT.BinaryBackgroundPopulation.Role.queue
end CurrentAFT.BinaryBackgroundPopulation.Role.queue
namespace CurrentAFT.BinaryBackgroundPopulation.factorWorkPolynomial
end CurrentAFT.BinaryBackgroundPopulation.factorWorkPolynomial
namespace CurrentAFT.BinaryBackgroundPopulation.population
end CurrentAFT.BinaryBackgroundPopulation.population
namespace CurrentAFT.BinaryControlChoiceAverage
end CurrentAFT.BinaryControlChoiceAverage
namespace CurrentAFT.BinaryControlChoiceAverage.heightPolynomial
end CurrentAFT.BinaryControlChoiceAverage.heightPolynomial
namespace CurrentAFT.BinaryControlChoiceAverage.workPolynomial
end CurrentAFT.BinaryControlChoiceAverage.workPolynomial
namespace CurrentAFT.BinaryCounterTupleDecode
end CurrentAFT.BinaryCounterTupleDecode
namespace CurrentAFT.BinaryCounterTupleDecode.append
end CurrentAFT.BinaryCounterTupleDecode.append
namespace CurrentAFT.BinaryCounterTupleDecode.current
end CurrentAFT.BinaryCounterTupleDecode.current
namespace CurrentAFT.BinaryCounterTupleDecode.current.match_1
end CurrentAFT.BinaryCounterTupleDecode.current.match_1
namespace CurrentAFT.BinaryCounterTupleDecode.workBound
end CurrentAFT.BinaryCounterTupleDecode.workBound
namespace CurrentAFT.BinaryDiffuseCurrent
end CurrentAFT.BinaryDiffuseCurrent
namespace CurrentAFT.BinaryDiffuseCurrent.currentHeight
end CurrentAFT.BinaryDiffuseCurrent.currentHeight
namespace CurrentAFT.BinaryDiffuseProgram
end CurrentAFT.BinaryDiffuseProgram
namespace CurrentAFT.BinaryDiffuseProgram.sumHeight
end CurrentAFT.BinaryDiffuseProgram.sumHeight
namespace CurrentAFT.BinaryFullResponseMatrixEntry.validEntry
end CurrentAFT.BinaryFullResponseMatrixEntry.validEntry
namespace CurrentAFT.BinaryFullResponseProgram
end CurrentAFT.BinaryFullResponseProgram
namespace CurrentAFT.BinaryGaussianAverage
end CurrentAFT.BinaryGaussianAverage
namespace CurrentAFT.BinaryGaussianAverage.sumHeight
end CurrentAFT.BinaryGaussianAverage.sumHeight
namespace CurrentAFT.BinaryMarkedCurrent
end CurrentAFT.BinaryMarkedCurrent
namespace CurrentAFT.BinaryMarkedCurrent.currentHeight
end CurrentAFT.BinaryMarkedCurrent.currentHeight
namespace CurrentAFT.BinaryPairProgram
end CurrentAFT.BinaryPairProgram
namespace CurrentAFT.BinaryPairProgram.current
end CurrentAFT.BinaryPairProgram.current
namespace CurrentAFT.BinaryPairProgram.currentHeightPolynomial
end CurrentAFT.BinaryPairProgram.currentHeightPolynomial
namespace CurrentAFT.BinaryPairProgram.currentWorkPolynomial
end CurrentAFT.BinaryPairProgram.currentWorkPolynomial
namespace CurrentAFT.BinaryPairProgram.diffuseHeightPolynomial
end CurrentAFT.BinaryPairProgram.diffuseHeightPolynomial
namespace CurrentAFT.BinaryPairProgram.markedHeightPolynomial
end CurrentAFT.BinaryPairProgram.markedHeightPolynomial
namespace CurrentAFT.BinaryRectangleDecode
end CurrentAFT.BinaryRectangleDecode
namespace CurrentAFT.BinaryRectangleDecode.Data
end CurrentAFT.BinaryRectangleDecode.Data
namespace CurrentAFT.BinaryRectangleDecode.Data.mk
end CurrentAFT.BinaryRectangleDecode.Data.mk
namespace CurrentAFT.BinaryRectangleDecode.Data.point
end CurrentAFT.BinaryRectangleDecode.Data.point
namespace CurrentAFT.BinaryRectangleDecode.safeWord
end CurrentAFT.BinaryRectangleDecode.safeWord
namespace CurrentAFT.BinaryRectangleEntry
end CurrentAFT.BinaryRectangleEntry
namespace CurrentAFT.BinaryRectangleEntry.current
end CurrentAFT.BinaryRectangleEntry.current
namespace CurrentAFT.BinaryRectangleEntry.current.match_1
end CurrentAFT.BinaryRectangleEntry.current.match_1
namespace CurrentAFT.BinaryRectangleEntry.current.match_1.splitter
end CurrentAFT.BinaryRectangleEntry.current.match_1.splitter
namespace CurrentAFT.BinaryRectangleIteration
end CurrentAFT.BinaryRectangleIteration
namespace CurrentAFT.BinaryRectangleIteration.entry
end CurrentAFT.BinaryRectangleIteration.entry
namespace CurrentAFT.BinaryRectangleIteration.entryWork
end CurrentAFT.BinaryRectangleIteration.entryWork
namespace CurrentAFT.BinaryRectangleIteration.position
end CurrentAFT.BinaryRectangleIteration.position
namespace CurrentAFT.BinaryRectangleIteration.reshape
end CurrentAFT.BinaryRectangleIteration.reshape
namespace CurrentAFT.BinaryRectangleIteration.reshapePolynomial
end CurrentAFT.BinaryRectangleIteration.reshapePolynomial
namespace CurrentAFT.BinaryRectangleIteration.reshapeWork
end CurrentAFT.BinaryRectangleIteration.reshapeWork
namespace CurrentAFT.BinaryRectangleIteration.run
end CurrentAFT.BinaryRectangleIteration.run
namespace CurrentAFT.BinaryRectangleIteration.workPolynomial
end CurrentAFT.BinaryRectangleIteration.workPolynomial
namespace CurrentAFT.BinaryRootGroupProgram
end CurrentAFT.BinaryRootGroupProgram
namespace CurrentAFT.BinaryRootGroupProgram.Data
end CurrentAFT.BinaryRootGroupProgram.Data
namespace CurrentAFT.BinaryRootGroupProgram.Data.mk
end CurrentAFT.BinaryRootGroupProgram.Data.mk
namespace CurrentAFT.BinaryRootGroupProgram.heightPolynomial
end CurrentAFT.BinaryRootGroupProgram.heightPolynomial
namespace CurrentAFT.BinaryRootGroupProgram.localTable
end CurrentAFT.BinaryRootGroupProgram.localTable
namespace CurrentAFT.BinaryRootGroupProgram.primary
end CurrentAFT.BinaryRootGroupProgram.primary
namespace CurrentAFT.BinaryRootGroupProgram.workPolynomial
end CurrentAFT.BinaryRootGroupProgram.workPolynomial
namespace CurrentAFT.BinaryRootMetadataSerializer
end CurrentAFT.BinaryRootMetadataSerializer
namespace CurrentAFT.BinaryRootMetadataSerializer.Result
end CurrentAFT.BinaryRootMetadataSerializer.Result
namespace CurrentAFT.BinaryRootMetadataSerializer.Result.mk
end CurrentAFT.BinaryRootMetadataSerializer.Result.mk
namespace CurrentAFT.BinaryRootMetadataSerializer.candidate
end CurrentAFT.BinaryRootMetadataSerializer.candidate
namespace CurrentAFT.BinaryRootMetadataSerializer.countEquiv
end CurrentAFT.BinaryRootMetadataSerializer.countEquiv
namespace CurrentAFT.BinaryRootMetadataSerializer.filter
end CurrentAFT.BinaryRootMetadataSerializer.filter
namespace CurrentAFT.BinaryRootMetadataSerializer.filter.match_1
end CurrentAFT.BinaryRootMetadataSerializer.filter.match_1
namespace CurrentAFT.BinaryRootMetadataSerializer.find
end CurrentAFT.BinaryRootMetadataSerializer.find
namespace CurrentAFT.BinaryRootMetadataSerializer.groupCount
end CurrentAFT.BinaryRootMetadataSerializer.groupCount
namespace CurrentAFT.BinaryRootMetadataSerializer.isKept
end CurrentAFT.BinaryRootMetadataSerializer.isKept
namespace CurrentAFT.BinaryRootMetadataSerializer.matchesBlock
end CurrentAFT.BinaryRootMetadataSerializer.matchesBlock
namespace CurrentAFT.BinaryRootMetadataSerializer.matchesBlock.match_1
end CurrentAFT.BinaryRootMetadataSerializer.matchesBlock.match_1
namespace CurrentAFT.BinaryRootMetadataSerializer.ordinaryMissing
end CurrentAFT.BinaryRootMetadataSerializer.ordinaryMissing
namespace CurrentAFT.BinaryRootMetadataSerializer.position
end CurrentAFT.BinaryRootMetadataSerializer.position
namespace CurrentAFT.BinaryRootMetadataSerializer.primaryMissing
end CurrentAFT.BinaryRootMetadataSerializer.primaryMissing
namespace CurrentAFT.BinaryRootMetadataSerializer.role
end CurrentAFT.BinaryRootMetadataSerializer.role
namespace CurrentAFT.BinaryRootMetadataSerializer.tagBlockEquiv
end CurrentAFT.BinaryRootMetadataSerializer.tagBlockEquiv
namespace CurrentAFT.BinaryRootSignedMass
end CurrentAFT.BinaryRootSignedMass
namespace CurrentAFT.BinaryRootSignedMass.bodyProgram
end CurrentAFT.BinaryRootSignedMass.bodyProgram
namespace CurrentAFT.BinaryRootSignedMass.references
end CurrentAFT.BinaryRootSignedMass.references
namespace CurrentAFT.BinarySparseCycleSemantic
end CurrentAFT.BinarySparseCycleSemantic
namespace CurrentAFT.BinarySparseCycleSemantic.coordinates
end CurrentAFT.BinarySparseCycleSemantic.coordinates
namespace CurrentAFT.BinaryTouchedCycleBuffer
end CurrentAFT.BinaryTouchedCycleBuffer
namespace CurrentAFT.BinaryTouchedCycleBuffer.lookup
end CurrentAFT.BinaryTouchedCycleBuffer.lookup
namespace CurrentAFT.BinaryTouchedCycleRanks
end CurrentAFT.BinaryTouchedCycleRanks
namespace CurrentAFT.BinaryTouchedCycleRanks.positions
end CurrentAFT.BinaryTouchedCycleRanks.positions
namespace CurrentAFT.CountedBoundedRootTags
end CurrentAFT.CountedBoundedRootTags
namespace CurrentAFT.CountedBoundedRootTags.Tag
end CurrentAFT.CountedBoundedRootTags.Tag
namespace CurrentAFT.CountedBoundedRootTags.Tag.mk
end CurrentAFT.CountedBoundedRootTags.Tag.mk
namespace CurrentAFT.CountedBoundedRootTags.Tag.read
end CurrentAFT.CountedBoundedRootTags.Tag.read
namespace CurrentAFT.CountedBoundedRootTags.Tag.set
end CurrentAFT.CountedBoundedRootTags.Tag.set
namespace CurrentAFT.CountedBoundedRootTags.Tag.vector
end CurrentAFT.CountedBoundedRootTags.Tag.vector
namespace CurrentAFT.CountedBoundedRootTags.bounded_sum
end CurrentAFT.CountedBoundedRootTags.bounded_sum
namespace CurrentAFT.CountedBoundedRootTags.countPolynomial
end CurrentAFT.CountedBoundedRootTags.countPolynomial
namespace CurrentAFT.CountedBoundedRootTags.current
end CurrentAFT.CountedBoundedRootTags.current
namespace CurrentAFT.CountedBoundedRootTags.entry
end CurrentAFT.CountedBoundedRootTags.entry
namespace CurrentAFT.CountedBoundedRootTags.entryWorkBound
end CurrentAFT.CountedBoundedRootTags.entryWorkBound
namespace CurrentAFT.CountedBoundedRootTags.generationWorkPolynomial
end CurrentAFT.CountedBoundedRootTags.generationWorkPolynomial
namespace CurrentAFT.CountedBoundedRootTags.heightPolynomial
end CurrentAFT.CountedBoundedRootTags.heightPolynomial
namespace CurrentAFT.CountedBoundedRootTags.lengthBound
end CurrentAFT.CountedBoundedRootTags.lengthBound
namespace CurrentAFT.CountedBoundedRootTags.source
end CurrentAFT.CountedBoundedRootTags.source
namespace CurrentAFT.CountedBoundedRootTags.sum
end CurrentAFT.CountedBoundedRootTags.sum
namespace CurrentAFT.CountedBoundedRootTags.workBound
end CurrentAFT.CountedBoundedRootTags.workBound
namespace CurrentAFT.CountedBoundedRootTags.workPolynomial
end CurrentAFT.CountedBoundedRootTags.workPolynomial
namespace CurrentAFT.CurrentCycleEntryProgram
end CurrentAFT.CurrentCycleEntryProgram
namespace CurrentAFT.CurrentCycleEntryProgram.selectedEntry
end CurrentAFT.CurrentCycleEntryProgram.selectedEntry
namespace CurrentAFT.CurrentGroupSourcePadding
end CurrentAFT.CurrentGroupSourcePadding
namespace CurrentAFT.CurrentGroupSourcePadding.groupKind
end CurrentAFT.CurrentGroupSourcePadding.groupKind
namespace CurrentAFT.CurrentGroupSourcePadding.groupKind.match_1
end CurrentAFT.CurrentGroupSourcePadding.groupKind.match_1
namespace CurrentAFT.CycleSelections.centeredRootAtom
end CurrentAFT.CycleSelections.centeredRootAtom
namespace CurrentAFT.GroupSourcePadding
end CurrentAFT.GroupSourcePadding
namespace CurrentAFT.GroupSourcePadding.indexEquiv
end CurrentAFT.GroupSourcePadding.indexEquiv
namespace CurrentAFT.GroupSourcePadding.sourceDecode
end CurrentAFT.GroupSourcePadding.sourceDecode
namespace CurrentAFT.LocalDiffuseProgram
end CurrentAFT.LocalDiffuseProgram
namespace CurrentAFT.LocalDiffuseProgram.evaluate
end CurrentAFT.LocalDiffuseProgram.evaluate
namespace CurrentAFT.LocalMarkedProgram
end CurrentAFT.LocalMarkedProgram
namespace CurrentAFT.LocalMarkedProgram.evaluate
end CurrentAFT.LocalMarkedProgram.evaluate
namespace CurrentAFT.LocalPairProgram
end CurrentAFT.LocalPairProgram
namespace CurrentAFT.LocalPairProgram.current
end CurrentAFT.LocalPairProgram.current
namespace CurrentAFT.MarkedPairCertificates
end CurrentAFT.MarkedPairCertificates
namespace CurrentAFT.MarkedPairCertificates.markedMixedCertificate
end CurrentAFT.MarkedPairCertificates.markedMixedCertificate
namespace CurrentAFT.PublicAffinePipeline.addWork
end CurrentAFT.PublicAffinePipeline.addWork
namespace CurrentAFT.PublicAffinePipeline.fairBitRun
end CurrentAFT.PublicAffinePipeline.fairBitRun
namespace CurrentAFT.PublicAffinePipeline.fairGaussian
end CurrentAFT.PublicAffinePipeline.fairGaussian
namespace CurrentAFT.RationalConditionalPairProgram
end CurrentAFT.RationalConditionalPairProgram
namespace CurrentAFT.RationalConditionalPairProgram.centeredMean
end CurrentAFT.RationalConditionalPairProgram.centeredMean
namespace CurrentAFT.RationalConditionalPairProgram.colors
end CurrentAFT.RationalConditionalPairProgram.colors
namespace CurrentAFT.RationalConditionalPairProgram.computedBound
end CurrentAFT.RationalConditionalPairProgram.computedBound
namespace CurrentAFT.RationalConditionalPairProgram.current
end CurrentAFT.RationalConditionalPairProgram.current
namespace CurrentAFT.RationalConditionalPairProgram.errorConstant
end CurrentAFT.RationalConditionalPairProgram.errorConstant
namespace CurrentAFT.RationalConditionalPairProgram.profileErrorConstant
end CurrentAFT.RationalConditionalPairProgram.profileErrorConstant
namespace CurrentAFT.RationalDiffuseFamilyProgram
end CurrentAFT.RationalDiffuseFamilyProgram
namespace CurrentAFT.RationalDiffuseFamilyProgram.bodyTable
end CurrentAFT.RationalDiffuseFamilyProgram.bodyTable
namespace CurrentAFT.RationalDiffuseFamilyProgram.primaryTable
end CurrentAFT.RationalDiffuseFamilyProgram.primaryTable
namespace CurrentAFT.RationalDiffuseResidualProgram
end CurrentAFT.RationalDiffuseResidualProgram
namespace CurrentAFT.RationalDiffuseResidualProgram.evaluate
end CurrentAFT.RationalDiffuseResidualProgram.evaluate
namespace CurrentAFT.RationalDiffuseResidualProgram.pair
end CurrentAFT.RationalDiffuseResidualProgram.pair
namespace CurrentAFT.RationalFullResponseProgram
end CurrentAFT.RationalFullResponseProgram
namespace CurrentAFT.RationalFullResponseProgram.selected
end CurrentAFT.RationalFullResponseProgram.selected
namespace CurrentAFT.RationalLegBackgroundProgram
end CurrentAFT.RationalLegBackgroundProgram
namespace CurrentAFT.RationalLegBackgroundProgram.base_one
end CurrentAFT.RationalLegBackgroundProgram.base_one
namespace CurrentAFT.RationalLegBackgroundProgram.current
end CurrentAFT.RationalLegBackgroundProgram.current
namespace CurrentAFT.RationalLegCoefficientExtraction
end CurrentAFT.RationalLegCoefficientExtraction
namespace CurrentAFT.RationalLegCoefficientExtraction.orderPermutation
end CurrentAFT.RationalLegCoefficientExtraction.orderPermutation
namespace CurrentAFT.RationalLegCoefficientExtraction.selectedKernel
end CurrentAFT.RationalLegCoefficientExtraction.selectedKernel
namespace CurrentAFT.RationalLegMassProgram
end CurrentAFT.RationalLegMassProgram
namespace CurrentAFT.RationalLegMassProgram.difference
end CurrentAFT.RationalLegMassProgram.difference
namespace CurrentAFT.RationalMarkedPairProgram
end CurrentAFT.RationalMarkedPairProgram
namespace CurrentAFT.RationalMarkedSeedProgram
end CurrentAFT.RationalMarkedSeedProgram
namespace CurrentAFT.RationalMarkedSeedProgram.fixedAnchor
end CurrentAFT.RationalMarkedSeedProgram.fixedAnchor
namespace CurrentAFT.RationalMassLiftTensorProgram
end CurrentAFT.RationalMassLiftTensorProgram
namespace CurrentAFT.RationalMassLiftTensorProgram.current
end CurrentAFT.RationalMassLiftTensorProgram.current
namespace CurrentAFT.RationalPackedRootProgram
end CurrentAFT.RationalPackedRootProgram
namespace CurrentAFT.RationalPackedRootProgram.Valid
end CurrentAFT.RationalPackedRootProgram.Valid
namespace CurrentAFT.RationalPackedRootProgram.actualMetadata
end CurrentAFT.RationalPackedRootProgram.actualMetadata
namespace CurrentAFT.RationalPackedRootProgram.control
end CurrentAFT.RationalPackedRootProgram.control
namespace CurrentAFT.RationalPackedRootProgram.nativeKind
end CurrentAFT.RationalPackedRootProgram.nativeKind
namespace CurrentAFT.RationalPackedRootProgram.nativeKind.match_1
end CurrentAFT.RationalPackedRootProgram.nativeKind.match_1
namespace CurrentAFT.RationalPackedRootProgram.nativeRole
end CurrentAFT.RationalPackedRootProgram.nativeRole
namespace CurrentAFT.RationalPackedRootProgram.nativeRole.match_3
end CurrentAFT.RationalPackedRootProgram.nativeRole.match_3
namespace CurrentAFT.RationalPackedRootProgram.signed
end CurrentAFT.RationalPackedRootProgram.signed
namespace CurrentAFT.RationalPackedRootProgram.sourceIndex
end CurrentAFT.RationalPackedRootProgram.sourceIndex
namespace CurrentAFT.RationalPackedRootProgram.validGroup
end CurrentAFT.RationalPackedRootProgram.validGroup
namespace CurrentAFT.RationalPackedRootProgram.validGroup.match_1
end CurrentAFT.RationalPackedRootProgram.validGroup.match_1
namespace CurrentAFT.RationalPositiveFamilyProgram
end CurrentAFT.RationalPositiveFamilyProgram
namespace CurrentAFT.RationalPositiveReferenceProgram
end CurrentAFT.RationalPositiveReferenceProgram
namespace CurrentAFT.RationalRootMassProgram
end CurrentAFT.RationalRootMassProgram
namespace CurrentAFT.RationalRootMassProgram.controlRest
end CurrentAFT.RationalRootMassProgram.controlRest
namespace CurrentAFT.RationalUnselectedLegProgram
end CurrentAFT.RationalUnselectedLegProgram
namespace CurrentAFT.RectanglePointIndex
end CurrentAFT.RectanglePointIndex
namespace CurrentAFT.RectanglePointIndex.encode
end CurrentAFT.RectanglePointIndex.encode
namespace CurrentAFT.RootSignedMassProgram
end CurrentAFT.RootSignedMassProgram
namespace CurrentAFT.RootSignedMassProgram.referenceEntry
end CurrentAFT.RootSignedMassProgram.referenceEntry
namespace CurrentAFT.RootSignedMassProgram.signedTest
end CurrentAFT.RootSignedMassProgram.signedTest
namespace CurrentAFT.RootSignedMassProgram.weightedEntry
end CurrentAFT.RootSignedMassProgram.weightedEntry
namespace CurrentAFT.WeightedPointKernelProgram
end CurrentAFT.WeightedPointKernelProgram
namespace CurrentAFT.WeightedPointKernelProgram.current
end CurrentAFT.WeightedPointKernelProgram.current
namespace CurrentAFT.WeightedPointKernelProgram.weightedTensor
end CurrentAFT.WeightedPointKernelProgram.weightedTensor
namespace Integration9_9.NativePipelineSemantic
end Integration9_9.NativePipelineSemantic
namespace Integration9_9.TM2NativeBackgroundDiffuse
end Integration9_9.TM2NativeBackgroundDiffuse
namespace Integration9_9.TM2NativeBackgroundDiffuse.canonical
end Integration9_9.TM2NativeBackgroundDiffuse.canonical
namespace Integration9_9.TM2NativeBackgroundDiffuse.coinAverage
end Integration9_9.TM2NativeBackgroundDiffuse.coinAverage
namespace Integration9_9.TM2NativeBackgroundDiffuse.fixedPair
end Integration9_9.TM2NativeBackgroundDiffuse.fixedPair
namespace Integration9_9.TM2NativeBackgroundDiffuse.pair
end Integration9_9.TM2NativeBackgroundDiffuse.pair
namespace Integration9_9.TM2NativeBackgroundDiffuse.residual
end Integration9_9.TM2NativeBackgroundDiffuse.residual
namespace Integration9_9.TM2NativeBackgroundDiffuse.restricted
end Integration9_9.TM2NativeBackgroundDiffuse.restricted
namespace Integration9_9.TM2NativeBackgroundDiffuse.rightAverage
end Integration9_9.TM2NativeBackgroundDiffuse.rightAverage
namespace Integration9_9.TM2NativeBackgroundDiffuse.width
end Integration9_9.TM2NativeBackgroundDiffuse.width
namespace Integration9_9.TM2NativeBackgroundLeg
end Integration9_9.TM2NativeBackgroundLeg
namespace Integration9_9.TM2NativeBackgroundMarked
end Integration9_9.TM2NativeBackgroundMarked
namespace Integration9_9.TM2NativeBackgroundMarked.fixedAnchor
end Integration9_9.TM2NativeBackgroundMarked.fixedAnchor
namespace Integration9_9.TM2NativeBackgroundPopulation
end Integration9_9.TM2NativeBackgroundPopulation
namespace Integration9_9.TM2NativeBackgroundPopulation.Context
end Integration9_9.TM2NativeBackgroundPopulation.Context
namespace Integration9_9.TM2NativeBackgroundPopulation.Context.mk
end Integration9_9.TM2NativeBackgroundPopulation.Context.mk
namespace Integration9_9.TM2NativeBackgroundPopulation.rawInput
end Integration9_9.TM2NativeBackgroundPopulation.rawInput
namespace Integration9_9.TM2NativeBackgroundTensor
end Integration9_9.TM2NativeBackgroundTensor
namespace Integration9_9.TM2NativeBackgroundTensor.current
end Integration9_9.TM2NativeBackgroundTensor.current
namespace Integration9_9.TM2NativeBackgroundTensor.entry
end Integration9_9.TM2NativeBackgroundTensor.entry
namespace Integration9_9.TM2NativeBackgroundTensor.primaryValue
end Integration9_9.TM2NativeBackgroundTensor.primaryValue
namespace Integration9_9.TM2NativeChoiceAverage
end Integration9_9.TM2NativeChoiceAverage
namespace Integration9_9.TM2NativeChoiceAverage.current
end Integration9_9.TM2NativeChoiceAverage.current
namespace Integration9_9.TM2NativeCycleAverage
end Integration9_9.TM2NativeCycleAverage
namespace Integration9_9.TM2NativeCycleAverage.body
end Integration9_9.TM2NativeCycleAverage.body
namespace Integration9_9.TM2NativeCycleAverage.bodySlots
end Integration9_9.TM2NativeCycleAverage.bodySlots
namespace Integration9_9.TM2NativeCycleAverage.current
end Integration9_9.TM2NativeCycleAverage.current
namespace Integration9_9.TM2NativeCycleAverage.numerator
end Integration9_9.TM2NativeCycleAverage.numerator
namespace Integration9_9.TM2NativeCycleEvaluation
end Integration9_9.TM2NativeCycleEvaluation
namespace Integration9_9.TM2NativeCycleEvaluation.roots
end Integration9_9.TM2NativeCycleEvaluation.roots
namespace Integration9_9.TM2NativeCycleEvaluation.term
end Integration9_9.TM2NativeCycleEvaluation.term
namespace Integration9_9.TM2NativeCycleRanks
end Integration9_9.TM2NativeCycleRanks
namespace Integration9_9.TM2NativeCycleTouched
end Integration9_9.TM2NativeCycleTouched
namespace Integration9_9.TM2NativeCycleTouched.candidates
end Integration9_9.TM2NativeCycleTouched.candidates
namespace Integration9_9.TM2NativeCycleTouched.contains
end Integration9_9.TM2NativeCycleTouched.contains
namespace Integration9_9.TM2NativeCycleTouched.contains_iff
end Integration9_9.TM2NativeCycleTouched.contains_iff
namespace Integration9_9.TM2NativeCycleTouched.prepare
end Integration9_9.TM2NativeCycleTouched.prepare
namespace Integration9_9.TM2NativeCycleTouched.unique
end Integration9_9.TM2NativeCycleTouched.unique
namespace Integration9_9.TM2NativeCycleTouched.unique.match_1
end Integration9_9.TM2NativeCycleTouched.unique.match_1
namespace Integration9_9.TM2NativeFullResponse
end Integration9_9.TM2NativeFullResponse
namespace Integration9_9.TM2NativeFullResponse.Context
end Integration9_9.TM2NativeFullResponse.Context
namespace Integration9_9.TM2NativeFullResponse.Context.mk
end Integration9_9.TM2NativeFullResponse.Context.mk
namespace Integration9_9.TM2NativeFullResponse.defect
end Integration9_9.TM2NativeFullResponse.defect
namespace Integration9_9.TM2NativeFullResponse.input
end Integration9_9.TM2NativeFullResponse.input
namespace Integration9_9.TM2NativeFullResponseMatrix
end Integration9_9.TM2NativeFullResponseMatrix
namespace Integration9_9.TM2NativeFullResponseMatrix.Context
end Integration9_9.TM2NativeFullResponseMatrix.Context
namespace Integration9_9.TM2NativeFullResponseMatrix.Context.mk
end Integration9_9.TM2NativeFullResponseMatrix.Context.mk
namespace Integration9_9.TM2NativeFullResponseMatrix.sourceLeaf
end Integration9_9.TM2NativeFullResponseMatrix.sourceLeaf
namespace Integration9_9.TM2NativeLocalPair
end Integration9_9.TM2NativeLocalPair
namespace Integration9_9.TM2NativeLocalPair.average
end Integration9_9.TM2NativeLocalPair.average
namespace Integration9_9.TM2NativeLocalPair.context
end Integration9_9.TM2NativeLocalPair.context
namespace Integration9_9.TM2NativeLocalPair.current
end Integration9_9.TM2NativeLocalPair.current
namespace Integration9_9.TM2NativeLocalPair.gaussianRequest
end Integration9_9.TM2NativeLocalPair.gaussianRequest
namespace Integration9_9.TM2NativeLocalPair.kernel
end Integration9_9.TM2NativeLocalPair.kernel
namespace Integration9_9.TM2NativeLocalPair.term
end Integration9_9.TM2NativeLocalPair.term
namespace Integration9_9.TM2NativeLocalPair.withBlur
end Integration9_9.TM2NativeLocalPair.withBlur
namespace Integration9_9.TM2NativeMetadataDispatch
end Integration9_9.TM2NativeMetadataDispatch
namespace Integration9_9.TM2NativeMetadataDispatch.constant_list_poly
end Integration9_9.TM2NativeMetadataDispatch.constant_list_poly
namespace Integration9_9.TM2NativeMetadataDispatch.metadataCode
end Integration9_9.TM2NativeMetadataDispatch.metadataCode
namespace Integration9_9.TM2NativeMetadataDispatch.roleFintype
end Integration9_9.TM2NativeMetadataDispatch.roleFintype
namespace Integration9_9.TM2NativeMetadataDispatch.tagged
end Integration9_9.TM2NativeMetadataDispatch.tagged
namespace Integration9_9.TM2NativePackedRoot
end Integration9_9.TM2NativePackedRoot
namespace Integration9_9.TM2NativePackedRoot.control
end Integration9_9.TM2NativePackedRoot.control
namespace Integration9_9.TM2NativePackedRoot.current
end Integration9_9.TM2NativePackedRoot.current
namespace Integration9_9.TM2NativePackedRoot.signed
end Integration9_9.TM2NativePackedRoot.signed
namespace Integration9_9.TM2NativePackedRoot.signedMass
end Integration9_9.TM2NativePackedRoot.signedMass
namespace Integration9_9.TM2NativePackedRoot.summand
end Integration9_9.TM2NativePackedRoot.summand
namespace Integration9_9.TM2NativeProducer
end Integration9_9.TM2NativeProducer
namespace Integration9_9.TM2NativeProducer.columnSlots
end Integration9_9.TM2NativeProducer.columnSlots
namespace Integration9_9.TM2NativeProducer.current
end Integration9_9.TM2NativeProducer.current
namespace Integration9_9.TM2NativeProducer.fields
end Integration9_9.TM2NativeProducer.fields
namespace Integration9_9.TM2NativeProducer.indices
end Integration9_9.TM2NativeProducer.indices
namespace Integration9_9.TM2NativeProducer.iterate
end Integration9_9.TM2NativeProducer.iterate
namespace Integration9_9.TM2NativeProducer.matrix
end Integration9_9.TM2NativeProducer.matrix
namespace Integration9_9.TM2NativeProducer.request
end Integration9_9.TM2NativeProducer.request
namespace Integration9_9.TM2NativeProducer.rhs
end Integration9_9.TM2NativeProducer.rhs
namespace Integration9_9.TM2NativeProducer.slots
end Integration9_9.TM2NativeProducer.slots
namespace Integration9_9.TM2NativeRadix
end Integration9_9.TM2NativeRadix
namespace Integration9_9.TM2NativeRadix.digits
end Integration9_9.TM2NativeRadix.digits
namespace Integration9_9.TM2NativeRadix.digits.match_1
end Integration9_9.TM2NativeRadix.digits.match_1
namespace Integration9_9.TM2NativeRectangle
end Integration9_9.TM2NativeRectangle
namespace Integration9_9.TM2NativeRectangle.Request
end Integration9_9.TM2NativeRectangle.Request
namespace Integration9_9.TM2NativeRectangle.Request.mk
end Integration9_9.TM2NativeRectangle.Request.mk
namespace Integration9_9.TM2NativeRectangle.chunks
end Integration9_9.TM2NativeRectangle.chunks
namespace Integration9_9.TM2NativeRectangle.rowProgram
end Integration9_9.TM2NativeRectangle.rowProgram
namespace Integration9_9.TM2NativeRectangle.slice_ofFn
end Integration9_9.TM2NativeRectangle.slice_ofFn
namespace Integration9_9.TM2NativeRectangleDecode
end Integration9_9.TM2NativeRectangleDecode
namespace Integration9_9.TM2NativeRectangleDecode.body
end Integration9_9.TM2NativeRectangleDecode.body
namespace Integration9_9.TM2NativeRectangleDecode.branchData
end Integration9_9.TM2NativeRectangleDecode.branchData
namespace Integration9_9.TM2NativeRootGroup
end Integration9_9.TM2NativeRootGroup
namespace Integration9_9.TM2NativeRootGroup.Context
end Integration9_9.TM2NativeRootGroup.Context
namespace Integration9_9.TM2NativeRootGroup.Context.mk
end Integration9_9.TM2NativeRootGroup.Context.mk
namespace Integration9_9.TM2NativeRootGroup.localTable
end Integration9_9.TM2NativeRootGroup.localTable
namespace Integration9_9.TM2NativeRootGroup.rawInput
end Integration9_9.TM2NativeRootGroup.rawInput
namespace Integration9_9.TM2NativeRootGroupCoefficient
end Integration9_9.TM2NativeRootGroupCoefficient
namespace Integration9_9.TM2NativeRootGroupCoefficient.atom
end Integration9_9.TM2NativeRootGroupCoefficient.atom
namespace Integration9_9.TM2NativeRootGroupCoefficient.density
end Integration9_9.TM2NativeRootGroupCoefficient.density
namespace Integration9_9.TM2NativeRootGroupCoefficient.selectedKernel
end Integration9_9.TM2NativeRootGroupCoefficient.selectedKernel
namespace Integration9_9.TM2NativeRootGroupCoefficient.tupleSum
end Integration9_9.TM2NativeRootGroupCoefficient.tupleSum
namespace Integration9_9.TM2NativeRootGroupLeg
end Integration9_9.TM2NativeRootGroupLeg
namespace Integration9_9.TM2NativeRootGroupLegMass
end Integration9_9.TM2NativeRootGroupLegMass
namespace Integration9_9.TM2NativeRootGroupLegMass.difference
end Integration9_9.TM2NativeRootGroupLegMass.difference
namespace Integration9_9.TM2NativeRootGroupLegMass.mean
end Integration9_9.TM2NativeRootGroupLegMass.mean
namespace Integration9_9.TM2NativeRootGroupMass
end Integration9_9.TM2NativeRootGroupMass
namespace Integration9_9.TM2NativeRootGroupMass.controlRest
end Integration9_9.TM2NativeRootGroupMass.controlRest
namespace Integration9_9.TM2NativeRootGroupMass.positiveAttachment
end Integration9_9.TM2NativeRootGroupMass.positiveAttachment
namespace Integration9_9.TM2NativeRootGroupMass.positiveCompensator
end Integration9_9.TM2NativeRootGroupMass.positiveCompensator
namespace Integration9_9.TM2NativeRootGroupMass.positiveMass
end Integration9_9.TM2NativeRootGroupMass.positiveMass
namespace Integration9_9.TM2NativeRootGroupMass.positiveScalar
end Integration9_9.TM2NativeRootGroupMass.positiveScalar
namespace Integration9_9.TM2NativeRootGroupMass.primaryMass
end Integration9_9.TM2NativeRootGroupMass.primaryMass
namespace Integration9_9.TM2NativeRootGroupMass.residue
end Integration9_9.TM2NativeRootGroupMass.residue
namespace Integration9_9.TM2NativeRootGroupOrdinary
end Integration9_9.TM2NativeRootGroupOrdinary
namespace Integration9_9.TM2NativeRootGroupOrdinary.referencePoint
end Integration9_9.TM2NativeRootGroupOrdinary.referencePoint
namespace Integration9_9.TM2NativeRootGroupPrimary
end Integration9_9.TM2NativeRootGroupPrimary
namespace Integration9_9.TM2NativeRootGroupReference
end Integration9_9.TM2NativeRootGroupReference
namespace Integration9_9.TM2NativeRootGroupReference.average
end Integration9_9.TM2NativeRootGroupReference.average
namespace Integration9_9.TM2NativeRootGroupReference.current
end Integration9_9.TM2NativeRootGroupReference.current
namespace Integration9_9.TM2NativeRootGroupReference.left
end Integration9_9.TM2NativeRootGroupReference.left
namespace Integration9_9.TM2NativeRootGroupReference.right
end Integration9_9.TM2NativeRootGroupReference.right
namespace Integration9_9.TM2NativeRootGroupSingleton
end Integration9_9.TM2NativeRootGroupSingleton
namespace Integration9_9.TM2NativeRootMetadata
end Integration9_9.TM2NativeRootMetadata
namespace Integration9_9.TM2NativeRootMetadata.Context
end Integration9_9.TM2NativeRootMetadata.Context
namespace Integration9_9.TM2NativeRootMetadata.Context.mk
end Integration9_9.TM2NativeRootMetadata.Context.mk
namespace Integration9_9.TM2NativeRootMetadata.candidate
end Integration9_9.TM2NativeRootMetadata.candidate
namespace Integration9_9.TM2NativeRootMetadata.input
end Integration9_9.TM2NativeRootMetadata.input
namespace Integration9_9.TM2NativeRootMetadata.isKept
end Integration9_9.TM2NativeRootMetadata.isKept
namespace Integration9_9.TM2NativeRootMetadata.kept
end Integration9_9.TM2NativeRootMetadata.kept
namespace Integration9_9.TM2NativeRootMetadata.keptRole
end Integration9_9.TM2NativeRootMetadata.keptRole
namespace Integration9_9.TM2NativeRootMetadata.legs
end Integration9_9.TM2NativeRootMetadata.legs
namespace Integration9_9.TM2NativeRootMetadata.nativeValue
end Integration9_9.TM2NativeRootMetadata.nativeValue
namespace Integration9_9.TM2NativeRootMetadata.ordinary
end Integration9_9.TM2NativeRootMetadata.ordinary
namespace Integration9_9.TM2NativeRootMetadata.position
end Integration9_9.TM2NativeRootMetadata.position
namespace Integration9_9.TM2NativeRootMetadata.positionIndices
end Integration9_9.TM2NativeRootMetadata.positionIndices
namespace Integration9_9.TM2NativeRootMetadata.retained
end Integration9_9.TM2NativeRootMetadata.retained
namespace Integration9_9.TM2NativeRootMetadata.roleCode
end Integration9_9.TM2NativeRootMetadata.roleCode
namespace Integration9_9.TM2NativeRootMetadata.roleCode.match_1
end Integration9_9.TM2NativeRootMetadata.roleCode.match_1
namespace Integration9_9.TM2NativeRootMetadata.roles
end Integration9_9.TM2NativeRootMetadata.roles
namespace Integration9_9.TM2NativeRootSignedMass
end Integration9_9.TM2NativeRootSignedMass
namespace Integration9_9.TM2NativeRootSignedMass.current
end Integration9_9.TM2NativeRootSignedMass.current
namespace Integration9_9.TM2NativeRootSignedMass.test
end Integration9_9.TM2NativeRootSignedMass.test
namespace Integration9_9.TM2NativeRootTags
end Integration9_9.TM2NativeRootTags
namespace Integration9_9.TM2NativeRootTags.current
end Integration9_9.TM2NativeRootTags.current
namespace Integration9_9.TM2NativeRootTags.entry
end Integration9_9.TM2NativeRootTags.entry
namespace Integration9_9.TM2NativeRootTags.guarded
end Integration9_9.TM2NativeRootTags.guarded
namespace Integration9_9.TM2NativeSelectedResponse
end Integration9_9.TM2NativeSelectedResponse
namespace Integration9_9.TM2NativeSelectedResponse.current
end Integration9_9.TM2NativeSelectedResponse.current
namespace Integration9_9.TM2NativeSelectedResponse.input
end Integration9_9.TM2NativeSelectedResponse.input
namespace Integration9_9.TM2NativeTensorInverse
end Integration9_9.TM2NativeTensorInverse
namespace Integration9_9.TM2NativeTensorInverse.current
end Integration9_9.TM2NativeTensorInverse.current
namespace Integration9_9.TM2NativeTensorInverse.factor
end Integration9_9.TM2NativeTensorInverse.factor
namespace Integration9_9.TM2NativeTensorInverse.product
end Integration9_9.TM2NativeTensorInverse.product
namespace Integration9_9.TM2NativeTensorInverse.term
end Integration9_9.TM2NativeTensorInverse.term
namespace Integration9_9.TM2NativeWeightedPoint
end Integration9_9.TM2NativeWeightedPoint
namespace Integration9_9.TM2NativeWeightedPoint.current
end Integration9_9.TM2NativeWeightedPoint.current
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeSampler
open AFT AFT.BinaryArithmetic CurrentAFT QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeCoreProposal TM2NativeTapeCodec TM2NativeEmitterAssembly
open InfoLossLAR.WorstCase
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
  PublicParameterProgram.modulus BinaryRejectionCap.current CurrentLayoutDraw.draw CurrentMaterializedCompletion.current
  CurrentMaterializedCompletion.complete CappedPublicRejection.current CurrentBinaryAffineEmitter.emit
  TM2NativeProducer.current TM2NativeCappedRejection.current TM2NativeCompletion.current TM2NativeEmitter.current
  TM2NativeEmitterOutput.current
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h357 (order : ℕ) (xs : List Unit) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache xs.length) :
    _root_.Integration9_9.TM2NativeSampler.producer order xs=List.ofFn (fun i=>List.ofFn (fun j=>
      (((_root_.CurrentAFT.ActualConstructiveSampler.producer xs.length order data layout).value.get i).get j).decode)) := by
  exact TM2NativeProducer.current_value order (xs,xs) xs data hdata
open _root_.P2Mba49f952 renaming h357 → _p2mH357
attribute [local irreducible] producer
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h356 (xs : List Unit) (word : _root_.CurrentAFT.CurrentLayoutDraw.Tape xs.length xs.length) :
    _root_.Integration9_9.TM2NativeSampler.layout (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=_root_.Integration9_9.TM2NativePermutationDraw.cacheData (_root_.CurrentAFT.CurrentLayoutDraw.draw xs.length xs.length word).value := by
  simpa only [_root_.Integration9_9.TM2NativeSampler.layout,_root_.Integration9_9.TM2NativeTapeCodec.wordData,_root_.CurrentAFT.CurrentLayoutDraw.draw] using
    _p2mH323 (_root_.Integration9_9.TM2NativeCoreProposal.bodyTicks xs) xs _ _ (_p2mH266 xs) rfl word
open _root_.P2Mba49f952 renaming h356 → _p2mH356
attribute [local irreducible] layout
attribute [local irreducible] accepted
attribute [local irreducible] completed
attribute [local irreducible] typed
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h353 (order : ℕ) (xs : List Unit) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (storedLayout : _root_.CurrentAFT.CurrentLayoutDraw.Cache xs.length)
    (word : _root_.CurrentAFT.PublicBitTapes.Tapes xs.length) :
    _root_.Integration9_9.TM2NativeSampler.accepted order (xs,_root_.Integration9_9.TM2NativeTapes.tapesData word)=
      _root_.Integration9_9.TM2NativePublicRejection.resultData (_root_.CurrentAFT.CappedPublicRejection.current xs.length order
        (_root_.CurrentAFT.ActualConstructiveSampler.producer xs.length order data storedLayout).value word.2.1).value := by
  unfold _root_.Integration9_9.TM2NativeSampler.accepted
  simp only [_root_.Integration9_9.TM2NativeTapes.tapesData]
  rw [_p2mH357 order xs data hdata storedLayout]
  exact _p2mH230 order xs _ word.2.1
open _root_.P2Mba49f952 renaming h353 → _p2mH353
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h354 (order : ℕ) (xs : List Unit) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (storedLayout : _root_.CurrentAFT.CurrentLayoutDraw.Cache xs.length)
    (word : _root_.CurrentAFT.PublicBitTapes.Tapes xs.length) :
    _root_.Integration9_9.TM2NativeSampler.completed order (xs,_root_.Integration9_9.TM2NativeTapes.tapesData word)=
      _root_.Integration9_9.TM2NativeEmitter.resultData (_root_.CurrentAFT.CurrentMaterializedCompletion.current xs.length order
        (_root_.CurrentAFT.ActualConstructiveSampler.producer xs.length order data storedLayout).value word.2).value := by
  unfold _root_.Integration9_9.TM2NativeSampler.completed
  rw [_p2mH353 order xs data hdata storedLayout word]
  simp only [_root_.Integration9_9.TM2NativeTapes.tapesData]
  simpa only [_root_.CurrentAFT.CurrentMaterializedCompletion.current] using
    _p2mH260 ((xs,xs),xs)
      (_root_.CurrentAFT.CappedPublicRejection.current xs.length order
        (_root_.CurrentAFT.ActualConstructiveSampler.producer xs.length order data storedLayout).value word.2.1).value xs.length word.2.2
open _root_.P2Mba49f952 renaming h354 → _p2mH354
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h358 (order : ℕ) (xs : List Unit) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (word : _root_.CurrentAFT.PublicBitTapes.Tapes xs.length) :
    _root_.Integration9_9.TM2NativeSampler.typed order (xs,_root_.Integration9_9.TM2NativeTapes.tapesData word)=
      (List.ofFn (fun row=>List.ofFn (fun column=>_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix xs.length
        (_root_.CurrentAFT.PublicAffinePipeline.run xs.length order (_root_.CurrentAFT.ActualConstructiveSampler.producer xs.length order data) word) row column)),
       List.ofFn (fun row=>_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset xs.length
        (_root_.CurrentAFT.PublicAffinePipeline.run xs.length order (_root_.CurrentAFT.ActualConstructiveSampler.producer xs.length order data) word) row)) := by
  let storedLayout := (_root_.CurrentAFT.CurrentLayoutDraw.draw xs.length xs.length word.1).value
  let table := (_root_.CurrentAFT.ActualConstructiveSampler.producer xs.length order data storedLayout).value
  have hl := _p2mH356 xs word.1
  have hc := _p2mH354 order xs data hdata storedLayout word
  have he := congrArg₂ (fun cache state=>_root_.Integration9_9.TM2NativeEmitter.current ((xs,cache.1),state)) hl hc
  have hn := _p2mH276 xs storedLayout
    (_root_.CurrentAFT.CurrentMaterializedCompletion.current xs.length order table word.2).value
  have ho := congrArg (fun out=>_root_.Integration9_9.TM2NativeEmitterOutput.current (xs,out)) (he.trans hn)
  have hfinish := ho.trans (_p2mH307 xs _)
  simpa only [_root_.Integration9_9.TM2NativeSampler.typed,_root_.Integration9_9.TM2NativeTapes.tapesData, _p2mH211,
    _p2mH212] using hfinish
open _root_.P2Mba49f952 renaming h358 → _p2mH358
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h355 (order : ℕ) (xs : List Unit) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (total : ℕ)
    (h : (_root_.CurrentAFT.PublicBitTapes.current xs.length).bits ≤ total) (word : Fin total → Fin 2) :
    _root_.Integration9_9.TM2NativeSampler.current order (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      encPair (encMat encI (_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix xs.length
        (_root_.CurrentAFT.ActualConstructiveSampler.run xs.length order data (fun i=>word (i.castLE h)))))
        (encVec encI (_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset xs.length
          (_root_.CurrentAFT.ActualConstructiveSampler.run xs.length order data (fun i=>word (i.castLE h))))) := by
  unfold _root_.Integration9_9.TM2NativeSampler.current
  rw [_p2mH410 xs total h,_p2mH358 order xs data hdata,_p2mH220]
  rw [_p2mH44,_p2mH45]
  rfl
open _root_.P2Mba49f952 renaming h355 → _p2mH355
end Integration9_9.TM2NativeSampler
open _root_.P2Mba49f952 renaming h353 → _p2mH353
open _root_.P2Mba49f952 renaming h354 → _p2mH354
open _root_.P2Mba49f952 renaming h355 → _p2mH355
open _root_.P2Mba49f952 renaming h356 → _p2mH356
open _root_.P2Mba49f952 renaming h357 → _p2mH357
open _root_.P2Mba49f952 renaming h358 → _p2mH358
end
open _root_.P2Mba49f952 renaming h353 → _p2mH353
open _root_.P2Mba49f952 renaming h354 → _p2mH354
open _root_.P2Mba49f952 renaming h355 → _p2mH355
open _root_.P2Mba49f952 renaming h356 → _p2mH356
open _root_.P2Mba49f952 renaming h357 → _p2mH357
open _root_.P2Mba49f952 renaming h358 → _p2mH358
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.mk
end AFT.FiniteDist.mk
namespace AFT.FiniteDist.totalVariation
end AFT.FiniteDist.totalVariation
namespace AFT.FiniteDist.uniform
end AFT.FiniteDist.uniform
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.independentCoordinates
end AFT.GaussianSource.independentCoordinates
namespace AFT.GaussianSource.independentCoordinates.match_1
end AFT.GaussianSource.independentCoordinates.match_1
namespace AFT.GaussianSource.integerGaussian
end AFT.GaussianSource.integerGaussian
namespace AFT.GaussianSource.latticeGaussian
end AFT.GaussianSource.latticeGaussian
namespace AFT.GaussianSource.latticeWeight
end AFT.GaussianSource.latticeWeight
namespace AFT.GaussianSource.residueGaussian
end AFT.GaussianSource.residueGaussian
namespace AFT.GaussianSource.weight
end AFT.GaussianSource.weight
namespace AFT.canonicalEndpointEquiv
end AFT.canonicalEndpointEquiv
namespace AFT.endpointIntegralPreimage
end AFT.endpointIntegralPreimage
namespace AFT.endpointLift
end AFT.endpointLift
namespace AFT.endpointProjection
end AFT.endpointProjection
namespace AFT.integerLabel
end AFT.integerLabel
namespace AFT.liftCoordinates
end AFT.liftCoordinates
namespace AFT.pathIncidence
end AFT.pathIncidence
namespace AFT.reduceCoordinates
end AFT.reduceCoordinates
namespace AFT.uniformZeroFiber
end AFT.uniformZeroFiber
namespace AFT.zeroFiberPullback
end AFT.zeroFiberPullback
namespace CurrentAFT.CurrentHiddenSourceTransport
end CurrentAFT.CurrentHiddenSourceTransport
namespace CurrentAFT.CurrentSourceLayout
end CurrentAFT.CurrentSourceLayout
namespace CurrentAFT.CurrentSourceLayout.splitWord
end CurrentAFT.CurrentSourceLayout.splitWord
namespace CurrentAFT.CurrentZeroFiber
end CurrentAFT.CurrentZeroFiber
namespace CurrentAFT.CurrentZeroFiber.label
end CurrentAFT.CurrentZeroFiber.label
namespace CurrentAFT.CurrentZeroFiber.pullback
end CurrentAFT.CurrentZeroFiber.pullback
namespace CurrentAFT.CurrentZeroFiber.rawPullback
end CurrentAFT.CurrentZeroFiber.rawPullback
namespace CurrentAFT.CurrentZeroFiber.uniformFiber
end CurrentAFT.CurrentZeroFiber.uniformFiber
namespace InfoLossLAR.WorstCase.Integration
end InfoLossLAR.WorstCase.Integration
namespace InfoLossLAR.WorstCase.Integration.actualSampler
end InfoLossLAR.WorstCase.Integration.actualSampler
namespace InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler
end InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler
namespace InfoLossLAR.WorstCase.Integration.paddedActualSampler
end InfoLossLAR.WorstCase.Integration.paddedActualSampler
namespace InfoLossLAR.WorstCase.Integration.reindexAffine
end InfoLossLAR.WorstCase.Integration.reindexAffine
namespace InfoLossLAR.WorstCase.TDef63
end InfoLossLAR.WorstCase.TDef63
namespace InfoLossLAR.WorstCase.avg
end InfoLossLAR.WorstCase.avg
namespace InfoLossLAR.WorstCase.famL
end InfoLossLAR.WorstCase.famL
namespace InfoLossLAR.WorstCase.famd
end InfoLossLAR.WorstCase.famd
namespace InfoLossLAR.WorstCase.famq
end InfoLossLAR.WorstCase.famq
namespace InfoLossLAR.WorstCase.transportLaw
end InfoLossLAR.WorstCase.transportLaw
namespace InfoLossLAR.WorstCase.unifOn
end InfoLossLAR.WorstCase.unifOn
namespace InfoLossLAR.WorstCase.unifZeroFiber
end InfoLossLAR.WorstCase.unifZeroFiber
namespace InfoLossLAR.WorstCase.zeroFiber63
end InfoLossLAR.WorstCase.zeroFiber63
namespace Integration9_9.FairBitPadding
end Integration9_9.FairBitPadding
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeSamplerEncoding
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.Integration
open AFT.BinaryArithmetic CurrentAFT QAlgorithms.Complexity
attribute [local irreducible] ActualConstructiveSampler.run CurrentBinaryAffineEmitter.matrix
  CurrentBinaryAffineEmitter.offset CurrentAFT.Parameters.dimension famd
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h361 {d d' : ℕ} (hd : d=d')
    (matrix : Matrix (Fin d) (Fin d) ℤ) (offset : Fin d→ℤ) :
    encPair (encMat encI (fun i j : Fin d' => matrix (Fin.cast hd.symm i) (Fin.cast hd.symm j)))
      (encVec encI (fun i : Fin d' => offset (Fin.cast hd.symm i)))=
      encPair (encMat encI matrix) (encVec encI offset) := by
  subst d'
  rfl
open _root_.P2Mba49f952 renaming h361 → _p2mH361
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h359 (b : Bool) : _root_.AFT.BinaryArithmetic.digitBoolean (finTwoEquiv.symm b)=b := by cases b <;> rfl
open _root_.P2Mba49f952 renaming h359 → _p2mH359
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h360 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (m : Polynomial ℕ) (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (security : ℕ) (tape : Fin (m.eval security)→Bool) :
    encPair (encMat encI (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security tape).1)
      (encVec encI (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security tape).2)=
    encPair (encMat encI (_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security
      (_root_.CurrentAFT.ActualConstructiveSampler.run security order data
        (fun i=>finTwoEquiv.symm (tape (Fin.castLE (hbits security) i))))))
      (encVec encI (_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security
        (_root_.CurrentAFT.ActualConstructiveSampler.run security order data
          (fun i=>finTwoEquiv.symm (tape (Fin.castLE (hbits security) i)))))) := by
  unfold _root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler _root_.InfoLossLAR.WorstCase.Integration.reindexAffine _root_.InfoLossLAR.WorstCase.Integration.paddedActualSampler _root_.InfoLossLAR.WorstCase.Integration.actualSampler
  exact _p2mH361 (_root_.InfoLossLAR.WorstCase.Integration.local_dimension_eq security)
    (_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.ActualConstructiveSampler.run security order data
      (fun i=>finTwoEquiv.symm (tape (Fin.castLE (hbits security) i)))))
    (_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.ActualConstructiveSampler.run security order data
      (fun i=>finTwoEquiv.symm (tape (Fin.castLE (hbits security) i)))))
open _root_.P2Mba49f952 renaming h360 → _p2mH360
end Integration9_9.TM2NativeSamplerEncoding
open _root_.P2Mba49f952 renaming h359 → _p2mH359
open _root_.P2Mba49f952 renaming h360 → _p2mH360
open _root_.P2Mba49f952 renaming h361 → _p2mH361
end
open _root_.P2Mba49f952 renaming h359 → _p2mH359
open _root_.P2Mba49f952 renaming h360 → _p2mH360
open _root_.P2Mba49f952 renaming h361 → _p2mH361
namespace InfoLossLAR.WorstCase.famInput
end InfoLossLAR.WorstCase.famInput
namespace Integration9_9.AFTToPlatformTheorem
end Integration9_9.AFTToPlatformTheorem
namespace Integration9_9.TM2NativePrime.primeFromParameter
end Integration9_9.TM2NativePrime.primeFromParameter
namespace Integration9_9.TM2NativePrime.primeFromSamplerRequest
end Integration9_9.TM2NativePrime.primeFromSamplerRequest
namespace Integration9_9.TM2NativeSamplerEncoding
end Integration9_9.TM2NativeSamplerEncoding
namespace Integration9_9.TM2NativeSamplerRequest
end Integration9_9.TM2NativeSamplerRequest
namespace Integration9_9.TM2NativeSamplerRequest.fields
end Integration9_9.TM2NativeSamplerRequest.fields
namespace Integration9_9.TM2NativeSamplerRequest.run
end Integration9_9.TM2NativeSamplerRequest.run
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.Integration
open CurrentAFT
open _root_.Integration9_9
attribute [local irreducible] ActualConstructiveSampler.run CurrentBinaryAffineEmitter.matrix
  CurrentBinaryAffineEmitter.offset CurrentAFT.Parameters.dimension famd
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h198 (order : ℕ) (xs : List Unit) (security : ℕ)
    (hlen : xs.length=security) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (total : ℕ)
    (hbits : (_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ total) (word : Fin total→Fin 2) :
    _root_.Integration9_9.TM2NativeSampler.current order (xs,_root_.Integration9_9.TM2NativeTapeCodec.wordData word)=
      encPair (encMat encI (_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security
        (_root_.CurrentAFT.ActualConstructiveSampler.run security order data (fun i=>word (Fin.castLE hbits i)))))
        (encVec encI (_root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security
          (_root_.CurrentAFT.ActualConstructiveSampler.run security order data (fun i=>word (Fin.castLE hbits i))))) := by
  subst security
  exact _p2mH355 order xs data hdata total hbits word
open _root_.P2Mba49f952 renaming h198 → _p2mH198
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mba49f952 renaming h198 → _p2mH198
end
open _root_.P2Mba49f952 renaming h198 → _p2mH198
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineApply
open AFT AFT.BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase
open scoped BigOperators
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h432 {α β : Type} {n : ℕ} (f : Fin n→α) (g : Fin n→β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i=>(f i,g i)) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h432 → _p2mH432
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h214 {n : ℕ} (f g : Fin n→ℤ) : _root_.Integration9_9.TM2NativeAffineApply.dot (List.ofFn f,List.ofFn g)=∑i,f i*g i := by
  simp only [_root_.Integration9_9.TM2NativeAffineApply.dot,_p2mH432,List.map_ofFn,Function.comp_def,List.sum_ofFn]
open _root_.P2Mba49f952 renaming h214 → _p2mH214
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h431 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h431 → Integration9_9.TM2NativeAffineApply.range_map
open _root_.P2Mba49f952 renaming h431 → _p2mH431
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h216 (q : ℕ) [NeZero q] (z : ℤ) : _root_.Integration9_9.TM2NativeBodyKernel.emodNatural (z,q)=(z : ZMod q).val := by
  rw [_root_.Integration9_9.TM2NativeBodyKernel.emodNatural_eq]
  have h := ZMod.val_intCast (n:=q) z
  simpa only [Int.toNat_natCast] using (congrArg Int.toNat h).symm
open _root_.P2Mba49f952 renaming h216 → Integration9_9.TM2NativeAffineApply.residue_value
open _root_.P2Mba49f952 renaming h216 → _p2mH216
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h215 (q d N : ℕ) [NeZero q] (Q : Matrix (Fin d) (Fin d) ℤ) (beta : Fin d→ℤ)
    (A : Matrix (Fin d) (Fin N) (ZMod q)) (b : Fin d→ZMod q) :
    _root_.Integration9_9.TM2NativeAffineApply.matrix ((q,(List.ofFn (fun i=>List.ofFn (Q i)),List.ofFn beta)),
      (List.ofFn (fun i=>List.ofFn (fun j=>(A i j).val)),List.ofFn (fun i=>(b i).val)))=
      List.ofFn (fun i=>List.ofFn (fun j=>((matModq q Q*A) i j).val)) := by
  simp only [_root_.Integration9_9.TM2NativeAffineApply.matrix,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  have hd : 0<d := by have h:=i.isLt;omega
  have hN : ((List.ofFn (fun i=>List.ofFn (fun j=>(A i j).val)))[0]?.getD []).length=N := by
    simp only [List.getElem?_ofFn,hd,dif_pos,Option.getD_some,List.length_ofFn]
  simp only [_root_.Integration9_9.TM2NativeAffineApply.row,hN,_p2mH431]
  apply congrArg List.ofFn
  funext j
  simp only [_root_.Integration9_9.TM2NativeAffineApply.entry,_root_.Integration9_9.TM2NativeAffineApply.column,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
  rw [_p2mH214,_p2mH216]
  apply congrArg ZMod.val
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,Matrix.mul_apply,matModq]
  rfl
open _root_.P2Mba49f952 renaming h215 → _p2mH215
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h217 (q d N : ℕ) [NeZero q] (Q : Matrix (Fin d) (Fin d) ℤ) (beta : Fin d→ℤ)
    (A : Matrix (Fin d) (Fin N) (ZMod q)) (b : Fin d→ZMod q) :
    _root_.Integration9_9.TM2NativeAffineApply.response ((q,(List.ofFn (fun i=>List.ofFn (Q i)),List.ofFn beta)),
      (List.ofFn (fun i=>List.ofFn (fun j=>(A i j).val)),List.ofFn (fun i=>(b i).val)))=
      List.ofFn (fun i=>(evalAffine Q beta b i).val) := by
  simp only [_root_.Integration9_9.TM2NativeAffineApply.response,List.length_ofFn,_p2mH431]
  apply congrArg List.ofFn
  funext i
  simp only [_root_.Integration9_9.TM2NativeAffineApply.responseEntry,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
  rw [_p2mH214,_p2mH216]
  apply congrArg ZMod.val
  simp only [Int.cast_add,Int.cast_sum,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,
    evalAffine,Matrix.mulVec,matModq,modq,Pi.add_apply,dotProduct]
  rfl
open _root_.P2Mba49f952 renaming h217 → _p2mH217
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h213 (q d N : ℕ) [NeZero q] (Q : Matrix (Fin d) (Fin d) ℤ) (beta : Fin d→ℤ)
    (A : Matrix (Fin d) (Fin N) (ZMod q)) (b : Fin d→ZMod q) :
    _root_.Integration9_9.TM2NativeAffineApply.current ((q,(List.ofFn (fun i=>List.ofFn (Q i)),List.ofFn beta)),
      (List.ofFn (fun i=>List.ofFn (fun j=>(A i j).val)),List.ofFn (fun i=>(b i).val)))=
      (List.ofFn (fun i=>List.ofFn (fun j=>((matModq q Q*A) i j).val)),List.ofFn (fun i=>(evalAffine Q beta b i).val)) := by
  exact congrArg₂ Prod.mk (_p2mH215 q d N Q beta A b) (_p2mH217 q d N Q beta A b)
open _root_.P2Mba49f952 renaming h213 → Integration9_9.TM2NativeAffineApply.current_value
open _root_.P2Mba49f952 renaming h213 → _p2mH213
end Integration9_9.TM2NativeAffineApply
open _root_.P2Mba49f952 renaming h213 → Integration9_9.TM2NativeAffineApply.current_value
open _root_.P2Mba49f952 renaming h213 → _p2mH213
open _root_.P2Mba49f952 renaming h214 → _p2mH214
open _root_.P2Mba49f952 renaming h215 → _p2mH215
open _root_.P2Mba49f952 renaming h216 → Integration9_9.TM2NativeAffineApply.residue_value
open _root_.P2Mba49f952 renaming h216 → _p2mH216
open _root_.P2Mba49f952 renaming h217 → _p2mH217
open _root_.P2Mba49f952 renaming h431 → Integration9_9.TM2NativeAffineApply.range_map
open _root_.P2Mba49f952 renaming h431 → _p2mH431
open _root_.P2Mba49f952 renaming h432 → _p2mH432
end
open _root_.P2Mba49f952 renaming h213 → Integration9_9.TM2NativeAffineApply.current_value
open _root_.P2Mba49f952 renaming h213 → _p2mH213
open _root_.P2Mba49f952 renaming h214 → _p2mH214
open _root_.P2Mba49f952 renaming h215 → _p2mH215
open _root_.P2Mba49f952 renaming h216 → Integration9_9.TM2NativeAffineApply.residue_value
open _root_.P2Mba49f952 renaming h216 → _p2mH216
open _root_.P2Mba49f952 renaming h217 → _p2mH217
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineBlock
open AFT AFT.BinaryArithmetic CurrentAFT QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.Integration
attribute [local irreducible] CurrentAFT.Parameters.dimension CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.legCount
  TM2NativeSampler.current ActualConstructiveSampler.run CurrentBinaryAffineEmitter.matrix CurrentBinaryAffineEmitter.offset famd
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h218 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data)
    (m : Polynomial ℕ) (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (security : ℕ) (coins : Fin (m.eval security)→Bool) :
    _root_.Integration9_9.TM2NativeAffineBlock.affine order (List.replicate security (),List.ofFn coins)=
      (List.ofFn (fun i=>List.ofFn ((_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security coins).1 i)),
        List.ofFn (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security coins).2) := by
  have hn := _p2mH198 order (List.replicate security ()) security (List.length_replicate ..)
    data hdata (m.eval security) (hbits security) (fun i=>finTwoEquiv.symm (coins i))
  have hf := _p2mH360 order data m hbits security coins
  have he : _root_.Integration9_9.TM2NativeSampler.current order (List.replicate security (),List.ofFn coins)=
      encPair (encMat encI (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security coins).1)
        (encVec encI (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security coins).2) := by
    simpa only [_root_.Integration9_9.TM2NativeTapeCodec.wordData,_p2mH359] using hn.trans hf.symm
  exact (congrArg _root_.Integration9_9.TM2NativeAffineEncoding.readAffine he).trans (_root_.Integration9_9.TM2NativeAffineEncoding.readAffine_exact _ _)
open _root_.P2Mba49f952 renaming h218 → _p2mH218
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h219 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data)
    (m : Polynomial ℕ) (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (security N : ℕ) (coins : Fin (m.eval security)→Bool)
    (A : Matrix (Fin (famd security)) (Fin N) (ZMod (famq security)))
    (b : Fin (famd security)→ZMod (famq security)) :
    _root_.Integration9_9.TM2NativeAffineBlock.current order (((List.replicate security (),famq security),List.ofFn coins),
      (List.ofFn (fun i=>List.ofFn (fun j=>(A i j).val)),List.ofFn (fun i=>(b i).val)))=
      (List.ofFn (fun i=>List.ofFn (fun j=>
        ((matModq (famq security) (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security coins).1*A) i j).val)),
        List.ofFn (fun i=>(evalAffine (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security coins).1
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security coins).2 b i).val)) := by
  letI : NeZero (famq security) := ⟨by
    rw [← _root_.InfoLossLAR.WorstCase.Integration.local_modulus_eq]
    exact (_root_.CurrentAFT.Parameters.modulus_spec security).2.ne_zero⟩
  unfold _root_.Integration9_9.TM2NativeAffineBlock.current
  rw [_p2mH218 order data hdata m hbits security coins]
  exact _p2mH213 _ _ _ _ _ A b
open _root_.P2Mba49f952 renaming h219 → Integration9_9.TM2NativeAffineBlock.current_value
open _root_.P2Mba49f952 renaming h219 → _p2mH219
end Integration9_9.TM2NativeAffineBlock
open _root_.P2Mba49f952 renaming h218 → _p2mH218
open _root_.P2Mba49f952 renaming h219 → Integration9_9.TM2NativeAffineBlock.current_value
open _root_.P2Mba49f952 renaming h219 → _p2mH219
end
open _root_.P2Mba49f952 renaming h218 → _p2mH218
open _root_.P2Mba49f952 renaming h219 → Integration9_9.TM2NativeAffineBlock.current_value
open _root_.P2Mba49f952 renaming h219 → _p2mH219
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineTable
open AFT AFT.BinaryArithmetic CurrentAFT QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.Integration
attribute [local irreducible] CurrentAFT.Parameters.dimension CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.legCount
  famd TM2NativeAffineBlock.current
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h434 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h434 → Integration9_9.TM2NativeAffineTable.range_map
open _root_.P2Mba49f952 renaming h434 → _p2mH434
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h225 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data)
    (m : Polynomial ℕ) (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (security N count : ℕ) (coins : Fin count → Fin (m.eval security) → Bool)
    (table : Fin count → Matrix (Fin (famd security)) (Fin N) (ZMod (famq security)) ×
      (Fin (famd security) → ZMod (famq security))) :
    _root_.Integration9_9.TM2NativeAffineTable.current order ((((List.replicate security (),famq security),List.ofFn (fun i=>List.ofFn (coins i)))),
      List.ofFn (fun i=>(List.ofFn (fun row=>List.ofFn (fun col=>((table i).1 row col).val)),
        List.ofFn (fun row=>((table i).2 row).val))))=
      List.ofFn (fun i=>(List.ofFn (fun row=>List.ofFn (fun col=>
        ((matModq (famq security) (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (coins i)).1*(table i).1) row col).val)),
        List.ofFn (fun row=>(evalAffine (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (coins i)).1
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (coins i)).2 (table i).2 row).val))) := by
  simp only [_root_.Integration9_9.TM2NativeAffineTable.current,List.length_ofFn,_p2mH434]
  apply congrArg List.ofFn
  funext i
  simp only [_root_.Integration9_9.TM2NativeAffineTable.entry,List.getElem?_ofFn,Fin.isLt,dif_pos,Option.getD_some]
  exact _p2mH219 order data hdata m hbits security N (coins i) (table i).1 (table i).2
open _root_.P2Mba49f952 renaming h225 → Integration9_9.TM2NativeAffineTable.current_value
open _root_.P2Mba49f952 renaming h225 → _p2mH225
end Integration9_9.TM2NativeAffineTable
open _root_.P2Mba49f952 renaming h225 → Integration9_9.TM2NativeAffineTable.current_value
open _root_.P2Mba49f952 renaming h225 → _p2mH225
open _root_.P2Mba49f952 renaming h434 → Integration9_9.TM2NativeAffineTable.range_map
open _root_.P2Mba49f952 renaming h434 → _p2mH434
end
open _root_.P2Mba49f952 renaming h225 → Integration9_9.TM2NativeAffineTable.current_value
open _root_.P2Mba49f952 renaming h225 → _p2mH225
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffinePre
open AFT AFT.BinaryArithmetic CurrentAFT QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.Integration LARPlatformEncoding
attribute [local irreducible] CurrentAFT.Parameters.dimension CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.legCount
  famd famq famN famσ TM2NativeAffineTable.current
attribute [local irreducible] blockBits
attribute [local irreducible] current fields transformed
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h222 {q d N count : ℕ} (security : ℕ) (pp coins : Str)
    (table : Fin count → Matrix (Fin d) (Fin N) (ZMod q)×(Fin d → ZMod q)) :
    _root_.Integration9_9.TM2NativeAffinePre.fields (encPair coins (encInput security pp (encTable table)))=
      ((unary security,(pp,List.ofFn (fun i=>(List.ofFn (fun row=>List.ofFn (fun col=>((table i).1 row col).val)),
        List.ofFn (fun row=>((table i).2 row).val))))),coins) := by
  have hr (word : Str) : _root_.Integration9_9.LARPlatformEncoding.readS (encS word)=([],word) := by simpa only [List.append_nil] using _root_.Integration9_9.LARPlatformEncoding.readS_append word []
  have ht := _root_.Integration9_9.LARPlatformEncoding.readObservedInput_append security pp [] table
  simp only [List.append_nil] at ht
  simp only [_root_.Integration9_9.TM2NativeAffinePre.fields,encPair,_root_.Integration9_9.LARPlatformEncoding.readS_append,hr,ht]
open _root_.P2Mba49f952 renaming h222 → _p2mH222
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h433 {β : Type} (n : ℕ) (f : ℕ→β) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by apply List.ext_getElem <;> simp
open _root_.P2Mba49f952 renaming h433 → Integration9_9.TM2NativeAffinePre.range_map
open _root_.P2Mba49f952 renaming h433 → _p2mH433
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h223 (slots : List Unit) (count width total : ℕ) (hn : slots.length=count)
    (h : count*width ≤ total) (coins : Fin total → Bool) :
    _root_.Integration9_9.TM2NativeTapeCodec.groups ((slots,width),List.ofFn coins)=
      List.ofFn (fun i : Fin count=>List.ofFn (fun j : Fin width=>coins ((finProdFinEquiv (i,j)).castLE h))) := by
  simp only [_root_.Integration9_9.TM2NativeTapeCodec.groups,hn,_p2mH433]
  apply congrArg List.ofFn
  funext i
  apply List.ext_getElem
  · have hm := Nat.mul_le_mul_right width (show i.val+1 ≤ count by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hm
    simp only [_root_.Integration9_9.TM2NativeTapeCodec.take,_root_.Integration9_9.TM2NativeTapeCodec.drop,List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro j hj hk
    simp only [_root_.Integration9_9.TM2NativeTapeCodec.take,_root_.Integration9_9.TM2NativeTapeCodec.drop,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg coins
    apply Fin.ext
    change i.val*width+j=j+width*i.val
    simp only [Nat.mul_comm,Nat.add_comm]
open _root_.P2Mba49f952 renaming h223 → _p2mH223
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h224 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data)
    (m : Polynomial ℕ) (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (security N count total : ℕ) (h : count*m.eval security ≤ total) (coins : Fin total → Bool)
    (table : Fin count → Matrix (Fin (famd security)) (Fin N) (ZMod (famq security)) ×
      (Fin (famd security) → ZMod (famq security))) :
    _root_.Integration9_9.TM2NativeAffinePre.transformed order m ((unary security,(famPP security,List.ofFn (fun i=>
        (List.ofFn (fun row=>List.ofFn (fun col=>((table i).1 row col).val)),List.ofFn (fun row=>((table i).2 row).val))))),List.ofFn coins)=
      List.ofFn (fun i=>(List.ofFn (fun row=>List.ofFn (fun col=>
        ((matModq (famq security)
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).1*(table i).1) row col).val)),
        List.ofFn (fun row=>(evalAffine
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).1
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).2 (table i).2 row).val))) := by
  have hp : (_root_.Integration9_9.LARPlatformEncoding.readParameters (famPP security)).2.1=famq security := by
    simp only [famPP,_root_.Integration9_9.LARPlatformEncoding.readParameters,List.append_assoc,_root_.Integration9_9.LARPlatformEncoding.readB_append]
  unfold _root_.Integration9_9.TM2NativeAffinePre.transformed
  simp only [unary,List.map_replicate,List.length_replicate,_root_.Integration9_9.TM2NativeAffinePre.blockBits,hp]
  rw [_p2mH223 _ count (m.eval security) total (by simp) h coins]
  exact _p2mH225 order data hdata m hbits security N count
    (fun i j=>coins ((finProdFinEquiv (i,j)).castLE h)) table
open _root_.P2Mba49f952 renaming h224 → _p2mH224
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h221 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data)
    (m : Polynomial ℕ) (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (security N count total : ℕ) (h : count*m.eval security ≤ total) (coins : Fin total → Bool)
    (table : Fin count → Matrix (Fin (famd security)) (Fin N) (ZMod (famq security)) ×
      (Fin (famd security) → ZMod (famq security))) :
    _root_.Integration9_9.TM2NativeAffinePre.current order m (encPair (List.ofFn coins) (encInput security (famPP security) (encTable table)))=
      encInput security (famPP security) (encTable (fun i=>
        (matModq (famq security)
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).1*(table i).1,
         evalAffine
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).1
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).2 (table i).2))) := by
  have hf := _p2mH222 security (famPP security) (List.ofFn coins) table
  have hc := congrArg (fun parsed : _root_.Integration9_9.TM2NativeAffinePre.Fields×Str=>
    _root_.Integration9_9.LARPlatformEncoding.serializeObservedInput (parsed.1.1,(parsed.1.2.1,_root_.Integration9_9.TM2NativeAffinePre.transformed order m parsed))) hf
  have ht := _p2mH224 order data hdata m hbits security N count total h coins table
  have hv := congrArg (fun transformedTable : List _root_.Integration9_9.TM2NativeAffinePre.Sample=>
    _root_.Integration9_9.LARPlatformEncoding.serializeObservedInput (unary security,(famPP security,transformedTable))) ht
  have hs := _root_.Integration9_9.LARPlatformEncoding.serializeObservedInput_ofFn security (famPP security) (fun i=>
    (matModq (famq security)
      (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).1*(table i).1,
     evalAffine
      (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).1
      (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security (fun j=>coins ((finProdFinEquiv (i,j)).castLE h))).2 (table i).2))
  simpa only [_root_.Integration9_9.TM2NativeAffinePre.current] using hc.trans (hv.trans hs)
open _root_.P2Mba49f952 renaming h221 → Integration9_9.TM2NativeAffinePre.current_value
open _root_.P2Mba49f952 renaming h221 → _p2mH221
end Integration9_9.TM2NativeAffinePre
open _root_.P2Mba49f952 renaming h221 → Integration9_9.TM2NativeAffinePre.current_value
open _root_.P2Mba49f952 renaming h221 → _p2mH221
open _root_.P2Mba49f952 renaming h222 → _p2mH222
open _root_.P2Mba49f952 renaming h223 → _p2mH223
open _root_.P2Mba49f952 renaming h224 → _p2mH224
open _root_.P2Mba49f952 renaming h433 → Integration9_9.TM2NativeAffinePre.range_map
open _root_.P2Mba49f952 renaming h433 → _p2mH433
end
open _root_.P2Mba49f952 renaming h221 → Integration9_9.TM2NativeAffinePre.current_value
open _root_.P2Mba49f952 renaming h221 → _p2mH221
open _root_.P2Mba49f952 renaming h222 → _p2mH222
open _root_.P2Mba49f952 renaming h223 → _p2mH223
open _root_.P2Mba49f952 renaming h224 → _p2mH224
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARCoinMachine
open InfoLossLAR.WorstCase QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open LARPlatformEncoding Polynomial
open scoped BigOperators
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h448 (slots : List Unit) (base value : ℕ) :
    slots.foldl _root_.Integration9_9.LARCoinMachine.powerStep (base,value)=(base,value*base^slots.length) := by
  induction slots generalizing value with
  | nil => simp
  | cons slot slots ih =>
    simp only [List.foldl_cons,_root_.Integration9_9.LARCoinMachine.powerStep,ih,List.length_cons,pow_succ]
    congr 1
    ring
open _root_.P2Mba49f952 renaming h448 → _p2mH448
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h207 (base : ℕ) (slots : List Unit) : _root_.Integration9_9.LARCoinMachine.powerWithSlots (base,slots)=base^slots.length := by
  simp only [_root_.Integration9_9.LARCoinMachine.powerWithSlots,_p2mH448,one_mul]
open _root_.P2Mba49f952 renaming h207 → _p2mH207
end Integration9_9.LARCoinMachine
open _root_.P2Mba49f952 renaming h207 → _p2mH207
open _root_.P2Mba49f952 renaming h448 → _p2mH448
end
open _root_.P2Mba49f952 renaming h207 → _p2mH207
namespace InfoLossLAR.WorstCase.boundedSplit
end InfoLossLAR.WorstCase.boundedSplit
namespace InfoLossLAR.WorstCase.computableFixedRoundingDirection
end InfoLossLAR.WorstCase.computableFixedRoundingDirection
namespace InfoLossLAR.WorstCase.computableRoundingDirectionInteger
end InfoLossLAR.WorstCase.computableRoundingDirectionInteger
namespace Integration9_9.LARCoinMachine
end Integration9_9.LARCoinMachine
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARRankOneMachine
open InfoLossLAR.WorstCase QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open LARPlatformEncoding LARCoinMachine TM2PlatformSerialization
set_option maxRecDepth 8192
private theorem _root_.P2Mba49f952.h449 {q N n t : ℕ}
    (table : Fin (t+1) → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.observedAuxiliarySlots (List.ofFn (fun index =>
      (List.ofFn (fun i => List.ofFn (fun j => ((table index).1 i j).val)),
        List.ofFn (fun i => ((table index).2 i).val))))=List.replicate N () := by
  simp only [_root_.Integration9_9.LARRankOneMachine.observedAuxiliarySlots,List.ofFn_succ,List.head?_cons,Option.getD_some]
  rw [List.map_const']
  simp
open _root_.P2Mba49f952 renaming h449 → _p2mH449
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h209 {q N n t : ℕ} (ht : 0<t)
    (table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.observedJointSlots (List.ofFn (fun index =>
      (List.ofFn (fun i => List.ofFn (fun j => ((table index).1 i j).val)),
        List.ofFn (fun i => ((table index).2 i).val))))=List.replicate (N+t) () := by
  cases t with
  | zero => omega
  | succ t =>
    rw [_root_.Integration9_9.LARRankOneMachine.observedJointSlots,_p2mH449,List.map_const']
    simp only [List.length_ofFn,←List.replicate_add]
open _root_.P2Mba49f952 renaming h209 → _p2mH209
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h210 {q N n t : ℕ} (ht : 0<t) (lam width : ℕ)
    (table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.observedTicketCount (encInput lam (encB q++encB N++encB (n+1)++encB width) (encTable table))=q^(N+t) := by
  unfold _root_.Integration9_9.LARRankOneMachine.observedTicketCount
  have hinput := _root_.Integration9_9.LARPlatformEncoding.readObservedInput_append lam (encB q++encB N++encB (n+1)++encB width) [] table
  simp only [List.append_nil] at hinput
  rw [hinput]
  dsimp only
  have hpp := _root_.Integration9_9.LARPlatformEncoding.readParameters_append q N (n+1) width []
  simp only [List.append_nil] at hpp
  rw [hpp,_p2mH209 ht table,_p2mH207,List.length_replicate]
open _root_.P2Mba49f952 renaming h210 → _p2mH210
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h208 (fallback coins observed : Str) :
    _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair coins observed)=
      _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback
        (encPair (coins.take (Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount observed))) observed) := by
  let input := (_root_.Integration9_9.LARPlatformEncoding.readObservedInput observed).2
  let q := (_root_.Integration9_9.LARPlatformEncoding.readParameters input.2.1).2.1
  let slots := _root_.Integration9_9.LARRankOneMachine.observedJointSlots input.2.2
  have hdraw : _root_.Integration9_9.LARCoinMachine.jointDrawNumbers (q,(slots,coins.take (Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount observed))))=
      _root_.Integration9_9.LARCoinMachine.jointDrawNumbers (q,(slots,coins)) := by
    unfold _root_.Integration9_9.LARCoinMachine.jointDrawNumbers
    dsimp only [_root_.Integration9_9.LARRankOneMachine.observedTicketCount,input,q,slots]
    rw [List.take_take,Nat.min_self]
  unfold _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre
  rw [_root_.Integration9_9.LARRankOneMachine.readCoinObserved_encPair,_root_.Integration9_9.LARRankOneMachine.readCoinObserved_encPair]
  unfold _root_.Integration9_9.LARRankOneMachine.makeBoundedContext
  dsimp only
  rw [hdraw]
open _root_.P2Mba49f952 renaming h208 → _p2mH208
end Integration9_9.LARRankOneMachine
open _root_.P2Mba49f952 renaming h208 → _p2mH208
open _root_.P2Mba49f952 renaming h209 → _p2mH209
open _root_.P2Mba49f952 renaming h210 → _p2mH210
open _root_.P2Mba49f952 renaming h449 → _p2mH449
end
open _root_.P2Mba49f952 renaming h208 → _p2mH208
open _root_.P2Mba49f952 renaming h209 → _p2mH209
open _root_.P2Mba49f952 renaming h210 → _p2mH210
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Integration9_9.BlockCoins
open InfoLossLAR.WorstCase QAlgorithms.Complexity
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h200 {total : ℕ} (tape : Fin total → Bool) (start count : ℕ)
    (h : start+count ≤ total) :
    ((List.ofFn tape).drop start).take count=
      List.ofFn (fun bit : Fin count => tape ⟨start+bit.val,by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro index hi hj
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
open _root_.P2Mba49f952 renaming h200 → _p2mH200
end Integration9_9.BlockCoins
open _root_.P2Mba49f952 renaming h200 → _p2mH200
end
open _root_.P2Mba49f952 renaming h200 → _p2mH200
namespace Integration9_9.BlockCoins
end Integration9_9.BlockCoins
namespace Integration9_9.GenericBodySemantics
end Integration9_9.GenericBodySemantics
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GaussianRankOnePre
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.Integration
open QAlgorithms.Complexity Polynomial CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime LARRankOneMachine LARCoinLayout TM2PlatformSerialization LARPlatformEncoding
attribute [local irreducible] TM2NativeAffinePre.fields TM2NativeAffinePre.current TM2NativeAffinePre.blockBits
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h206 {q N d count : ℕ} (hd : 0 < d) (ht : 0 < count)
    (security width : ℕ)
    (table : Fin count → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.observedTicketCount (encInput security (encB q++encB N++encB d++encB width) (encTable table))=q^(N+count) := by
  cases d with
  | zero => omega
  | succ n => exact _p2mH210 ht security width table
open _root_.P2Mba49f952 renaming h206 → _p2mH206
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h205 (m : Polynomial ℕ) {q d N count : ℕ} (security : ℕ) (pp tape : Str)
    (table : Fin count → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) :
    _root_.Integration9_9.GaussianRankOnePre.remainingCoins m (encPair tape (encInput security pp (encTable table)))=tape.drop (count*m.eval security) := by
  unfold _root_.Integration9_9.GaussianRankOnePre.remainingCoins _root_.Integration9_9.GaussianRankOnePre.usedCoins
  rw [_p2mH222]
  simp only [List.length_ofFn,unary,List.map_replicate,List.length_replicate,_root_.Integration9_9.TM2NativeAffinePre.blockBits]
open _root_.P2Mba49f952 renaming h205 → _p2mH205
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h202 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (m : Polynomial ℕ)
    (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (fallback : Str) (security N count total : ℕ) (h : count*m.eval security ≤ total)
    (tape : Fin total → Bool)
    (table : Fin count → Matrix (Fin (famd security)) (Fin N) (ZMod (famq security)) ×
      (Fin (famd security) → ZMod (famq security))) :
    _root_.Integration9_9.GaussianRankOnePre.current order m fallback (encPair (List.ofFn tape) (encInput security (famPP security) (encTable table)))=
      _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair ((List.ofFn tape).drop (count*m.eval security))
        (encInput security (famPP security) (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable
          (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security)
          (fun block bit => tape (Fin.castLE h (finProdFinEquiv (block,bit)))) table)))) := by
  unfold _root_.Integration9_9.GaussianRankOnePre.current _root_.Integration9_9.GaussianRankOnePre.preparedInput
  rw [_p2mH205,_p2mH221 order data hdata m hbits security N count total h tape table]
  rfl
open _root_.P2Mba49f952 renaming h202 → Integration9_9.GaussianRankOnePre.current_value
open _root_.P2Mba49f952 renaming h202 → _p2mH202
end Integration9_9.GaussianRankOnePre
open _root_.P2Mba49f952 renaming h202 → Integration9_9.GaussianRankOnePre.current_value
open _root_.P2Mba49f952 renaming h202 → _p2mH202
open _root_.P2Mba49f952 renaming h205 → _p2mH205
open _root_.P2Mba49f952 renaming h206 → _p2mH206
end
end
open _root_.P2Mba49f952 renaming h202 → Integration9_9.GaussianRankOnePre.current_value
open _root_.P2Mba49f952 renaming h202 → _p2mH202
open _root_.P2Mba49f952 renaming h205 → _p2mH205
open _root_.P2Mba49f952 renaming h206 → _p2mH206
namespace Integration9_9.RandomizedCircuit
end Integration9_9.RandomizedCircuit
namespace Integration9_9.RandomizedCircuit.uniform_expectation_avg
end Integration9_9.RandomizedCircuit.uniform_expectation_avg
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open Integration9_9.RandomizedCircuit
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h199 (lam : ℕ) : 0 < famd lam := by
  unfold famd famL
  positivity
open _root_.P2Mba49f952 renaming h199 → _p2mH199
attribute [local irreducible] famq famd famL famσ
end InfoLossLAR.WorstCase
open _root_.P2Mba49f952 renaming h199 → _p2mH199
end
open _root_.P2Mba49f952 renaming h199 → _p2mH199
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GaussianRankOnePre
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.Integration
open QAlgorithms.Complexity Polynomial CurrentAFT
open OAI.MetricKMedian.Binary
open LARRankOneMachine LARCoinLayout GenericBodySemantics
attribute [local irreducible] famq famd current rankCoinBudget coins currentProgram
  boundedRankOneStringPre observedTicketCount fixedFamilyActualSampler
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h203 (security count : ℕ) (ht : 0 < count)
    (table : Fin count → Matrix (Fin (famd security)) (Fin (famN security)) (ZMod (famq security)) ×
      (Fin (famd security) → ZMod (famq security))) :
    _root_.Integration9_9.LARRankOneMachine.observedTicketCount (encInput security (famPP security) (encTable table))=(famq security)^(famN security+count) := by
  simpa only [famPP] using _p2mH206 (_p2mH199 security) ht security (famσ security) table
open _root_.P2Mba49f952 renaming h203 → _p2mH203
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h204 (fallback input : Str) (start bits total : ℕ) (h : start+bits ≤ total)
    (tape : Fin total → Bool) (hticket : Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount input)=bits) :
    _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair ((List.ofFn tape).drop start) input)=
      _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn (fun bit : Fin bits =>
        tape (Fin.castLE h (Fin.natAdd start bit)))) input) := by
  have hp := _p2mH208 fallback ((List.ofFn tape).drop start) input
  rw [hticket] at hp
  have hw := _p2mH200 tape start bits h
  exact hp.trans (congrArg (fun suffix => _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair suffix input)) hw)
open _root_.P2Mba49f952 renaming h204 → _p2mH204
set_option maxRecDepth 8192
theorem _root_.P2Mba49f952.h201 {q d N count total bits rankBits : ℕ} [NeZero q]
    (samp : (Fin bits → Bool) → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (table : Fin count → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q))
    (security : ℕ) (pp fallback input : Str) (pre : Str → Str)
    (h : count*bits+rankBits ≤ total) (tape : Fin total → Bool) (ha : count*bits ≤ total)
    (hraw : pre (encPair (List.ofFn tape) input)=_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback
      (encPair ((List.ofFn tape).drop (count*bits)) (encInput security pp
        (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp
          (fun block bit => tape (Fin.castLE ha (finProdFinEquiv (block,bit)))) table)))))
    (hticket : ∀ output : Fin count → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q),
      Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount (encInput security pp (encTable output)))=rankBits) :
    pre (encPair (List.ofFn tape) input)=_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback
      (encPair (List.ofFn (fun bit : Fin rankBits => tape (Fin.castLE h (Fin.natAdd (count*bits) bit))))
        (encInput security pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp
          (fun block bit => tape (Fin.castLE h (Fin.castAdd rankBits (finProdFinEquiv (block,bit))))) table)))) := by
  have hseed : (fun block : Fin count => fun bit : Fin bits => tape (Fin.castLE ha (finProdFinEquiv (block,bit))))=
      (fun block : Fin count => fun bit : Fin bits => tape (Fin.castLE h
        (Fin.castAdd rankBits (finProdFinEquiv (block,bit))))) := rfl
  let output := encInput security pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp
    (fun block bit => tape (Fin.castLE h (Fin.castAdd rankBits (finProdFinEquiv (block,bit))))) table))
  have hout : encInput security pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp
      (fun block bit => tape (Fin.castLE ha (finProdFinEquiv (block,bit)))) table))=output :=
    congrArg (fun seeds => encInput security pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp seeds table))) hseed
  exact hraw.trans ((congrArg (fun observed => _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback
    (encPair ((List.ofFn tape).drop (count*bits)) observed)) hout).trans
      (_p2mH204 fallback output (count*bits) rankBits total h tape (hticket _)))
open _root_.P2Mba49f952 renaming h201 → _p2mH201
set_option maxRecDepth 8192
theorem _root_.Integration9_9.GaussianRankOnePre.__p2m_proof_ba49f9522e39df1bd365 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (m : Polynomial ℕ)
    (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (fallback : Str) (security count total : ℕ) (ht : 0 < count)
    (h : count*m.eval security+Nat.size ((famq security)^(famN security+count)) ≤ total)
    (tape : Fin total → Bool)
    (table : Fin count → Matrix (Fin (famd security)) (Fin (famN security)) (ZMod (famq security)) ×
      (Fin (famd security) → ZMod (famq security))) :
    _root_.Integration9_9.GaussianRankOnePre.current order m fallback (encPair (List.ofFn tape) (encInput security (famPP security) (encTable table)))=
      _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback
        (encPair (List.ofFn (fun bit : Fin (Nat.size ((famq security)^(famN security+count))) =>
            tape (Fin.castLE h (Fin.natAdd (count*m.eval security) bit))))
          (encInput security (famPP security) (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable
            (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security)
            (fun block bit => tape (Fin.castLE h (Fin.castAdd _ (finProdFinEquiv (block,bit))))) table)))) := by
  have ha : count*m.eval security ≤ total := by omega
  exact _p2mH201 (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security) table
    security (famPP security) fallback (encInput security (famPP security) (encTable table))
    (_root_.Integration9_9.GaussianRankOnePre.current order m fallback) h tape ha
    (_p2mH202 order data hdata m hbits fallback security (famN security) count total ha tape table)
    (fun output => congrArg Nat.size (_p2mH203 security count ht output))
end Integration9_9.GaussianRankOnePre
open _root_.P2Mba49f952 renaming h201 → _p2mH201
open _root_.P2Mba49f952 renaming h203 → _p2mH203
open _root_.P2Mba49f952 renaming h204 → _p2mH204
end
end
open _root_.P2Mba49f952 renaming h201 → _p2mH201
open _root_.P2Mba49f952 renaming h203 → _p2mH203
open _root_.P2Mba49f952 renaming h204 → _p2mH204
set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.Integration9_9.GaussianRankOnePre.__p2m_proof_ba49f9522e39df1bd365) := @_root_.Integration9_9.GaussianRankOnePre.__p2m_proof_ba49f9522e39df1bd365
