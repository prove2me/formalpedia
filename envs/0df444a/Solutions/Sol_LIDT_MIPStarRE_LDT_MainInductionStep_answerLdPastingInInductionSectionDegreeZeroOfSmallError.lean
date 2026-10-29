-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.answerLdPastingInInductionSectionDegreeZeroOfSmallError
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:35:13.746647+00:00
-- url     : https://prove2.me/submissions/eaa3e3c6-2767-485a-a16d-30634bd28991

-- Generated proof for MIPStarRE.LDT.MainInductionStep.answerLdPastingInInductionSectionDegreeZeroOfSmallError.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionPMF
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_MainTheorems
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_SumForm
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_AvgSliceErrors_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_AvgSliceErrors_Successor
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_MainError
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_AnswerValued
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Axis
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Diagonal
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_AnswerSlice
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_StageDataConstructors
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_ErrorBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_AddInUFullStatement
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUPointConsistency
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Transfer
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_BoundednessGap
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_Decomposition
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistency
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistencyLiteral
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Assembly
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_PostDeleteA
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_FinalFields
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_SelfCloseness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimp
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Lean.Elab.Tactic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_answerLdPastingInInductionError_le_mainInductionError_of_smallError
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_degreeZeroPastedPointConsistency_of_axis_self

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.MainInductionStep
end LIDT.MIPStarRE.LDT.MainInductionStep
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Test/StrategyFailures.lean. -/
/-!
# Symmetrized-strategy failure probabilities and test bounds

Failure-probability surrogates and basic low-individual-degree test bounds for
the split strategy interface.
-/

@[expose] public section

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-! ### Symmetrized strategies and tested-branch bounds -/

namespace SymStrat









end SymStrat









/-! ### Answer-valued symmetric strategies -/

/-- The answer-valued diagonal-line failure surrogate is nonnegative. -/
theorem answer_diagonalFailureProbability_nonneg
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    0 ≤ strategy.diagonalFailureProbability := by
  unfold AnswerSymStrat.diagonalFailureProbability
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro j _
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
      (AnswerSymStrat.diagonalLineAnswerFamily strategy j)

/-- A good answer-valued symmetric strategy has a nonnegative axis-parallel
error parameter `ε`. -/
theorem answer_eps_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ eps := by
  exact le_trans
    (bipartiteConsError_nonneg strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (AnswerSymStrat.axisParallelPointAnswerFamily strategy)
      (AnswerSymStrat.axisParallelLineAnswerFamily strategy))
    hgood.axisParallelTest

/-- A good answer-valued symmetric strategy has a nonnegative self-consistency
error parameter `δ`. -/
theorem answer_delta_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ delta := by
  exact le_trans
    (bipartiteSSCError_nonneg strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
    hgood.selfConsistencyTest

/-- A good answer-valued symmetric strategy has a nonnegative diagonal-lines
error parameter `γ`. -/
theorem answer_gamma_nonneg_of_isGood
    (params : Parameters)
    [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma) :
    0 ≤ gamma := by
  exact le_trans (answer_diagonalFailureProbability_nonneg params strategy)
    hgood.diagonalLineTest



end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Section 6 — Pasting Assembly: Error Bounds

This module contains the scalar absorption and degree-zero answer-valued pasting
constructions for the small-error branch.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat params.next ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params.next k eps delta gamma < 1)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (kappa : _root_.LIDT.MIPStarRE.LDT.Error)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.evaluatedAtNextPoint family)
        (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionError params.next eps delta gamma))
    (_hself :
      family.StronglySelfConsistent strategy.state
        (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionError params.next eps delta gamma))
    (_hbound :
      _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput
        (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerSelfImprovementCarrier params.next strategy)
        family
        (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionError params.next eps delta gamma))
    (hkappa_le :
      kappa ≤
        ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
            (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionNu params.next k eps delta gamma +
              Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))))
          + _root_.LIDT.MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionError params.next eps delta gamma)
    (hzeta_le_nu :
      _root_.LIDT.MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionError params.next eps delta gamma ≤
        _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionNu params.next k eps delta gamma)
    (_hk : 400 * params.m * params.d ≤ k)
    (hd_zero : params.d = 0) :
    _root_.LIDT.MIPStarRE.LDT.MainInductionStep.AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  let carrier := _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerSelfImprovementCarrier params.next strategy
  let zeta : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionError params.next eps delta gamma
  have haxis :
      carrier.axisParallelFailureProbability ≤ eps := by
    have hfail :
        carrier.axisParallelFailureProbability =
          strategy.axisParallelFailureProbability := by
      unfold _root_.LIDT.MIPStarRE.LDT.SymStrat.axisParallelFailureProbability
        _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.axisParallelFailureProbability
        _root_.LIDT.MIPStarRE.LDT.axisParallelPointAnswerFamily _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.axisParallelPointAnswerFamily
        _root_.LIDT.MIPStarRE.LDT.axisParallelLineAnswerFamily _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.axisParallelLineAnswerFamily
      simp [carrier, _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerSelfImprovementCarrier]
    simpa [hfail] using hgood.axisParallelTest
  have hself_good :
      carrier.selfConsistencyFailureProbability ≤ delta := by
    have hfail :
        carrier.selfConsistencyFailureProbability =
          strategy.selfConsistencyFailureProbability := by
      unfold _root_.LIDT.MIPStarRE.LDT.SymStrat.selfConsistencyFailureProbability
        _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.selfConsistencyFailureProbability
      simp [carrier, _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerSelfImprovementCarrier]
    simpa [hfail] using hgood.selfConsistencyTest
  have heps_nonneg := _root_.LIDT.MIPStarRE.LDT.answer_eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := _root_.LIDT.MIPStarRE.LDT.answer_delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := _root_.LIDT.MIPStarRE.LDT.answer_gamma_nonneg_of_isGood params.next strategy hgood
  have hcompleteCarrier : family.Complete carrier.state kappa := by
    simpa [carrier, _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerSelfImprovementCarrier] using hcomplete
  have hconsCarrier : family.ConsistentWithPoints carrier zeta := by
    exact ⟨by simpa [carrier, _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerSelfImprovementCarrier, zeta] using hcons⟩
  obtain ⟨H, _hHdef, hpastedCarrier⟩ :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.degreeZeroPastedPointConsistency_of_axis_self params carrier
      eps delta gamma kappa zeta haxis hself_good
      heps_nonneg hdelta_nonneg hgamma_nonneg
      family hcompleteCarrier hconsCarrier hd_zero k
  have hpasted :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H.toSubMeas)
        (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionError params k eps delta gamma kappa zeta) := by
    simpa [carrier, _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerSelfImprovementCarrier, zeta] using hpastedCarrier
  have herror_le :
      _root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionError params k eps delta gamma kappa zeta ≤
        _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params.next k eps delta gamma := by
    exact _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerLdPastingInInductionError_le_mainInductionError_of_smallError
      params strategy eps delta gamma kappa k hgood hsmall
      hkappa_le hzeta_le_nu
  refine ⟨H, ?_⟩
  exact ⟨le_trans hpasted.offDiagonalBound herror_le⟩
