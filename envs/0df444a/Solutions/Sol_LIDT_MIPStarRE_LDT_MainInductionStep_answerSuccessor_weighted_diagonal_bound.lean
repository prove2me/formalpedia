-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.answerSuccessor_weighted_diagonal_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:06:23.023103+00:00
-- url     : https://prove2.me/submissions/4e1e0d38-8f4e-401d-b883-20bb03c1b25c

-- Generated proof for MIPStarRE.LDT.MainInductionStep.answerSuccessor_weighted_diagonal_bound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_MainError
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_AnswerValued
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Axis
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Diagonal
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_AnswerSlice
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_Core
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_avgOver_uniform_restrictedDiagonalSample_append
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_weighted_embedded_average_le_full_average

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

/- Source helpers from MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/AnswerValued.lean. -/
/-!
# Section 6 -- Answer-Valued Restricted Probability Statement

This module contains the answer-valued form of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uF uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]















/-! ### Answer-valued successor restrictions

The preceding lemmas start from an ordinary successor strategy and build the
answer-valued slice profile used in the current Section 6 successor route.  For
the simultaneous answer-valued induction theorem, the successor strategy itself
has answer-valued diagonal measurements.  The next definitions and lemmas
record the corresponding restricted-probability theorem without replacing that
diagonal measurement by an ordinary low-degree realization.
-/















private lemma answerSuccessorRestrictedDiagonalSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily
        (xRestrictedAnswerSymStratOfAnswer params strategy x) j s)
      (AnswerSymStrat.diagonalLineAnswerFamily
        (xRestrictedAnswerSymStratOfAnswer params strategy x) j s) =
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2))
      (AnswerSymStrat.diagonalLineAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2)) := by
  have hdir :
      appendPoint params (extendRestrictedDirection j s.2) zeroCoord =
        extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 := by
    funext k
    by_cases hkm : k.1 < params.m
    · by_cases hk : k.1 ≤ j.1
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
    · have hnotle : ¬ k.1 ≤ j.1 := by
          intro hk
          exact hkm (lt_of_le_of_lt hk j.2)
      simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hnotle]
      rfl
  have hline :
      DiagonalLine.appendAtHeight params
          { base := s.1, direction := extendRestrictedDirection j s.2 } x =
        ({ base := appendPoint params s.1 x,
           direction :=
             extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 } :
          DiagonalLine params.next) := by
    simp [DiagonalLine.appendAtHeight, hdir]
  simp [AnswerSymStrat.diagonalPointAnswerFamily,
    AnswerSymStrat.diagonalLineAnswerFamily, xRestrictedAnswerSymStratOfAnswer]
  simp [diagonalPointAnswerFamilyOf, diagonalLineAnswerFamilyOf, hline]





private lemma answerSuccessorDiagonalSliceIndexErrorAverage_eq_diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι)
    (j : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j) =
      answerSuccessorDiagonalIndexError params strategy (embedCoord params j) := by
  let g : RestrictedDiagonalSample params.next (embedCoord params j) → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (embedCoord params j) s)
      (AnswerSymStrat.diagonalLineAnswerFamily strategy (embedCoord params j) s)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
            (fun s => g (appendPoint params s.1 x, s.2))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold answerSuccessorDiagonalSliceIndexError bipartiteConsError
              refine avgOver_congr _ _ _ ?_
              intro s
              simpa [g] using
                answerSuccessorRestrictedDiagonalSampleError_eq params strategy x j s
    _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
          (fun xs => g (appendPoint params xs.2.1 xs.1, xs.2.2)) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params)
                (β := RestrictedDiagonalSample params j)
                (f := fun x s => g (appendPoint params s.1 x, s.2))).symm
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params.next (embedCoord params j)))
          g := by
            exact avgOver_uniform_restrictedDiagonalSample_append params j g
    _ = answerSuccessorDiagonalIndexError params strategy (embedCoord params j) := by
            rfl

private lemma answerSuccessorAverageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun j => answerSuccessorDiagonalSliceIndexError params strategy x j)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold AnswerSymStrat.diagonalFailureProbability
                answerSuccessorDiagonalSliceIndexError
              calc
                (1 / (params.m : Error)) *
                    ∑ j : Fin params.m,
                      bipartiteConsError strategy.state
                        (uniformDistribution (RestrictedDiagonalSample params j))
                        (AnswerSymStrat.diagonalPointAnswerFamily
                          (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                        (AnswerSymStrat.diagonalLineAnswerFamily
                          (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                  = ∑ j : Fin params.m,
                      (1 / (params.m : Error)) *
                        bipartiteConsError strategy.state
                          (uniformDistribution (RestrictedDiagonalSample params j))
                          (AnswerSymStrat.diagonalPointAnswerFamily
                            (xRestrictedAnswerSymStratOfAnswer params strategy x) j)
                          (AnswerSymStrat.diagonalLineAnswerFamily
                            (xRestrictedAnswerSymStratOfAnswer params strategy x) j) := by
                              rw [Finset.mul_sum]
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun j => answerSuccessorDiagonalSliceIndexError params strategy x j) := by
                              simp [avgOver, uniformDistribution, Fintype.card_fin,
                                answerSuccessorDiagonalSliceIndexError]
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => avgOver (uniformDistribution (Fq params))
            (fun x => answerSuccessorDiagonalSliceIndexError params strategy x j)) := by
            exact avgOver_uniform_comm
              (fun x j => answerSuccessorDiagonalSliceIndexError params strategy x j)
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => answerSuccessorDiagonalIndexError params strategy (embedCoord params j)) := by
            refine avgOver_congr _ _ _ ?_
            intro j
            exact answerSuccessorDiagonalSliceIndexErrorAverage_eq_diagonalIndexError
              params strategy j









end MIPStarRE.LDT.MainInductionStep

end

end LIDT

open LIDT
/-!
# Section 6 -- Answer-Valued Restricted Probability Statement

This module contains the answer-valued form of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uF uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]















/-! ### Answer-valued successor restrictions

The preceding lemmas start from an ordinary successor strategy and build the
answer-valued slice profile used in the current Section 6 successor route.  For
the simultaneous answer-valued induction theorem, the successor strategy itself
has answer-valued diagonal measurements.  The next definitions and lemmas
record the corresponding restricted-probability theorem without replacing that
diagonal measurement by an ordinary low-degree realization.
-/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat params.next ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (fun x => _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      ≤ gamma := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (fun x => _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedAnswerSymStratOfAnswer params strategy x).diagonalFailureProbability)
      = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (fun x =>
              _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalFailureProbability
                (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedAnswerSymStratOfAnswer params strategy x)) := by
              rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    _ = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.m))
            (fun j => answerSuccessorDiagonalIndexError params strategy (_root_.LIDT.MIPStarRE.LDT.embedCoord params j)) := by
              rw [answerSuccessorAverageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
                params strategy]
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m))
          (answerSuccessorDiagonalIndexError params strategy) :=
        _root_.LIDT.MIPStarRE.LDT.MainInductionStep.weighted_embedded_average_le_full_average params
          (f := answerSuccessorDiagonalIndexError params strategy)
          (hf := by
            intro j
            unfold answerSuccessorDiagonalIndexError
            exact _root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next j))
              (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily strategy j)
              (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalLineAnswerFamily strategy j))
    _ = strategy.diagonalFailureProbability := by
        unfold answerSuccessorDiagonalIndexError _root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalFailureProbability
        calc
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m))
              (fun j =>
                _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next j))
                  (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily strategy j)
                  (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalLineAnswerFamily strategy j))
            = ∑ j : Fin params.next.m,
                (1 / (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error)) *
                  _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next j))
                    (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily strategy j)
                    (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalLineAnswerFamily strategy j) := by
                      simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, Fintype.card_fin]
          _ = (1 / (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error)) *
                ∑ j : Fin params.next.m,
                  _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next j))
                    (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily strategy j)
                    (_root_.LIDT.MIPStarRE.LDT.AnswerSymStrat.diagonalLineAnswerFamily strategy j) := by
                      symm
                      rw [Finset.mul_sum]
          _ = strategy.diagonalFailureProbability := by
                rfl
    _ ≤ gamma := hgood.diagonalLineTest
