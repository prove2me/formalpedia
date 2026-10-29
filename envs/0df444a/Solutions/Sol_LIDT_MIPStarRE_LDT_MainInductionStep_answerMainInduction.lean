-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.answerMainInduction
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:18:37.709041+00:00
-- url     : https://prove2.me/submissions/e7ece7e0-b408-4bc7-bf17-5801f30c1ded

-- Generated proof for MIPStarRE.LDT.MainInductionStep.answerMainInduction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_SelfImprovement
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_ErrorBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_Successor
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_answerLdPastingInInductionSectionOfSmallError
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_answerMainInductionBaseCase
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis

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

/- Source helpers from MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/MainError.lean. -/
/-!
# Section 6 — Main-Induction Error Bounds

This file is one leaf of `InductionParameterBounds`. It contains the scalar
consequences of the non-vacuous hypothesis `mainInductionError < 1`, including
the bounds `eps ≤ 1`, `delta ≤ 1`, `gamma ≤ 1`, `params.d ≤ params.q`, and
`mainInductionNu < 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





















/-! ### Answer-valued small-error scalar consequences -/











/-- The successor large-`k` hypothesis implies the predecessor large-`k`
hypothesis used by recursive slice calls.

This is the elementary arithmetic comparison between the successor dimension
`params.m + 1` and the predecessor dimension `params.m`. -/
theorem mainInductionSuccessorBound_pred
    (params : Parameters) {k : ℕ}
    (hk : 400 * params.next.m * params.next.d ≤ k) :
    400 * params.m * params.d ≤ k := by
  have hm_le : params.m ≤ params.next.m := by
    simp
  have hcoef : 400 * params.m ≤ 400 * params.next.m :=
    Nat.mul_le_mul_left 400 hm_le
  have hmul :
      400 * params.m * params.d ≤ 400 * params.next.m * params.next.d := by
    simpa [Parameters.next, Nat.mul_assoc] using
      Nat.mul_le_mul_right params.d hcoef
  exact le_trans hmul hk

end MIPStarRE.LDT.MainInductionStep

end

/- Source helpers from MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems/Base.lean. -/
/-!
# Section 6 — Main Induction Theorems: Base and Large-Error Branches

This module contains the base cases and the trivial large-error branches for the
ordinary and answer-valued main induction statements.
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]







/-- Trivial branch of the answer-valued main induction when the target error is
at least `1`.

This is the answer-valued analogue of `mainInductionOfOneLeError`.  It supplies
the large-error branch needed by a simultaneous answer-valued induction proof:
the diagonal answer interface is irrelevant because the consistency defect
between the point measurement and a distinguished trivial polynomial measurement
is bounded by `1`. -/
theorem answerMainInductionOfOneLeError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (herror : 1 ≤ mainInductionError params k eps delta gamma) :
    AnswerMainInductionConclusion params strategy eps delta gamma k := by
  classical
  let G : Measurement (Polynomial params) ι :=
    Measurement.trivialDistinguishedOutcome
      (Classical.choice (inferInstance : Nonempty (Polynomial params)))
  refine ⟨G, ?_⟩
  exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas))
    herror⟩


end MIPStarRE.LDT.MainInductionStep

end

/- Source helpers from MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/Successor.lean. -/
/-!
# Section 6 — Pasting Assembly: Successor Assembly

This module contains the final answer-valued pasting invocation, averaged
pasting data constructors, and ordinary successor assembly corollaries.
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]



/-- Internal successor reduction from the predecessor answer-valued induction
hypothesis and the answer-valued pasting theorem.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

**Conditional:** This theorem is not the source successor theorem.  It records
that, once the
recursive predecessor hypothesis is available inside a genuine induction on
the dimension, all remaining slice restriction, self-improvement, averaging,
and scalar fields reduce the successor branch to
`answerLdPastingInInductionSectionOfSmallError`.  It is tracked in issue #1507.
Discharge: proved here from the predecessor answer-valued induction hypothesis
and the proved answer-valued pasting invocation. -/
theorem answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : AnswerSymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    AnswerMainInductionConclusion params.next strategy eps delta gamma k := by
  rcases answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis
      params strategy eps delta gamma k hgood hinduction hk_next hsmall with
    ⟨family, kappa, hcomplete, hcons, hself, hbound, hkappa_le, hzeta_le_nu⟩
  exact
    answerLdPastingInInductionSectionOfSmallError
      params strategy eps delta gamma k hgood hsmall family kappa hcomplete hcons hself hbound
      hkappa_le hzeta_le_nu (mainInductionSuccessorBound_pred params hk_next)

namespace AnswerSelfImprovementData









end AnswerSelfImprovementData











end MIPStarRE.LDT.MainInductionStep

end

end LIDT

open LIDT
/-!
# Section 6 — Main Induction Theorems: Successor and Public Interfaces

This module contains the answer-valued induction theorem, successor reductions,
and the public corrected large-`k` main-induction interface.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem solution.{uF, vι}
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel.{uF} params.q] :
    _root_.LIDT.MIPStarRE.LDT.MainInductionStep.AnswerMainInductionHypothesis.{uF, vι} params := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (params : _root_.LIDT.MIPStarRE.LDT.Parameters), params.m = n → ∀ instField : _root_.LIDT.MIPStarRE.LDT.FieldModel.{uF} params.q,
      @_root_.LIDT.MIPStarRE.LDT.MainInductionStep.AnswerMainInductionHypothesis.{uF, vι} params instField
  have hAll : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih params hm instField
    let : _root_.LIDT.MIPStarRE.LDT.FieldModel.{uF} params.q := instField
    intro ι instFintype instDecEq strategy eps delta gamma k hgood _hk_pos hk
    let : Fintype ι := instFintype
    let : DecidableEq ι := instDecEq
    by_cases hm1 : params.m = 1
    · exact _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerMainInductionBaseCase params strategy eps delta gamma k hm1 hgood
    · by_cases hsmall : _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k eps delta gamma < 1
      · rcases _root_.LIDT.MIPStarRE.LDT.Parameters.successorDecompositionOfNeOne params hm1 with ⟨pred, hnext⟩
        have hq : pred.q = params.q := by
          simpa [_root_.LIDT.MIPStarRE.LDT.Parameters.next] using congrArg _root_.LIDT.MIPStarRE.LDT.Parameters.q hnext
        let : _root_.LIDT.MIPStarRE.LDT.FieldModel.{uF} pred.q := hq.symm ▸ instField
        have hpred_lt : pred.m < n := by
          rw [← hm]
          cases hnext
          simp
        have hinduction : _root_.LIDT.MIPStarRE.LDT.MainInductionStep.AnswerMainInductionHypothesis.{uF, vι} pred :=
          ih pred.m hpred_lt pred rfl inferInstance
        cases hnext
        exact
          _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting
            pred strategy eps delta gamma k hgood hinduction hk hsmall
      · exact _root_.LIDT.MIPStarRE.LDT.MainInductionStep.answerMainInductionOfOneLeError params strategy eps delta gamma k
          (le_of_not_gt hsmall)
  exact hAll params.m params rfl inferInstance
