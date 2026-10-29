-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.sourceRoleRegisterTwoSidedProjectiveSubmeasurements
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:41:01.417023+00:00
-- url     : https://prove2.me/submissions/68a2e223-d5b3-447e-8b80-70643441e8d3

-- Generated proof for MIPStarRE.LDT.ProjStrat.sourceRoleRegisterTwoSidedProjectiveSubmeasurements.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_SchwartzZippelStep
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_answerMainInduction
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_mainInductionBaseCase
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_mainInductionSuccessorNext_ofAnswerCarrier
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_roleRegisterSymmStrategy_is_good_three_mul
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_sourceRoleRegisterPointConsistency_ofSymConsistency

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
namespace LIDT.MIPStarRE.LDT.ProjStrat
end LIDT.MIPStarRE.LDT.ProjStrat
namespace LIDT.MIPStarRE.LDT.Test
end LIDT.MIPStarRE.LDT.Test

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





/-- Trivial branch of `thm:main-induction` when the target error is at least
`1`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the
successor proof reduces to the nontrivial small-error regime before invoking the
pasting argument.  In the complementary branch the normalized consistency defect
is bounded by `1`, so a distinguished trivial polynomial measurement suffices.
-/
theorem mainInductionOfOneLeError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (herror : 1 ≤ mainInductionError params k eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
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

/- Source helpers from MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems/Successor.lean. -/
/-!
# Section 6 — Main Induction Theorems: Successor and Public Interfaces

This module contains the answer-valued induction theorem, successor reductions,
and the public corrected large-`k` main-induction interface.
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]





/-- Internal successor assembly from the successor large-`k` hypothesis, using
the answer-valued slice self-improvement construction.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This is an internal reduction for the successor proof of `thm:main-induction`,
not a paper theorem.  It replaces the predecessor large-`k` hypothesis in
`mainInductionSuccessorNext_ofAnswerCarrier` by the successor large-`k`
hypothesis through the elementary successor-to-predecessor bound. -/
theorem mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound.{uF}
    (params : Parameters)
    [FieldModel.{uF} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hinduction : AnswerMainInductionHypothesis.{uF, uι} params)
    (hk_next : 400 * params.next.m * params.next.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerCarrier
      params strategy eps delta gamma k hgood hsmall hinduction
      (mainInductionSuccessorBound_pred params hk_next)

/-- Small-error construction for the native successor step of
`thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, restricted to
the nontrivial regime
`mainInductionError params.next k eps delta gamma < 1`.

This theorem is the named construction for the nontrivial branch of the
successor proof.  Its public parameters are the
successor strategy hypotheses and the branch condition
`mainInductionError < 1`, so downstream users do not acquire
restricted-probability records, slice-induction data, self-improvement data,
pasting data, residual packages, or arbitrary implication hypotheses as
assumptions of the theorem.

The proof constructs the answer-valued restricted slice profile,
applies the recursive predecessor induction conclusion for each slice, assembles
the pasting input, and prove the scalar absorption estimates.  The checked
answer-carrier assembly obtains the predecessor induction argument from the
genuine strong-induction theorem `answerMainInduction`; it
does not postulate that predecessor conclusion as a hypothesis of the ordinary
successor theorem.  The predecessor induction hypothesis is no longer
restricted by `0 < params.d`; in the nontrivial branch, `1 ≤ k` follows from
`mainInductionError < 1`, and the answer-valued self-improvement data are
constructed by `AnswerSelfImprovementData.ofAnswerCarrier`.

The proof calls `answerMainInduction`, whose successor branch is a genuine
strong-induction argument.  The answer-valued pasting theorem is now proved and
is used inside that route, so this ordinary successor construction does not
carry a transitive `sorryAx` dependency. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound
      params strategy eps delta gamma k hgood hsmall
      (answerMainInduction params)
      hk

/-- Native successor step for `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the proof
passes from dimension `m` to dimension `m + 1`.

This is the native successor step for the corrected large-`k` Lean interface:
the ambient strategy already lives in dimension `params.next`, so no predecessor
compatibility record is introduced.  The checked reductions above show that the
small-error branch now passes through the genuine answer-valued induction
theorem and the proved answer-valued pasting invocation.

In the small-error regime, the proof uses the recursive predecessor
conclusion for the answer-valued restricted slices, construct the
answer-valued self-improvement data by the carrier route, and apply the
answer-valued analogue of the final induction-section pasting theorem.  No
ordinary `SymStrat` realization of the answer-valued diagonal measurement is
needed for this successor reduction, and the recursive predecessor conclusion
is supplied by `answerMainInduction` rather than by a public hypothesis.

The small-error branch calls
`mainInductionSuccessorNext_ofSmallErrorConstruction`, whose proof depends on
the internal theorem `answerMainInduction`.  That internal theorem supplies the
predecessor induction hypothesis by strong induction and invokes the proved
answer-valued pasting theorem, so the native successor step is now
standard-axiom clean. -/
theorem mainInductionSuccessorNext
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.next.m * params.next.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · exact
      mainInductionSuccessorNext_ofSmallErrorConstruction
        params strategy eps delta gamma k hgood hk hsmall
  · exact mainInductionOfOneLeError params.next strategy eps delta gamma k
      (le_of_not_gt hsmall)

/-- Successor branch of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, the induction
step after the restricted-probability estimates and the slice-wise recursive
calls have been set up.

This theorem is the parameter-decomposition form used by `mainInduction`.
Its assumptions are the corrected large-`k` hypotheses for
`thm:main-induction`, together with the branch condition `params.m ≠ 1`; it
does not accept restricted-probability records, per-slice induction data,
self-improvement data, pasting data, auxiliary implication hypotheses, residual
inputs, or data record hypotheses.  The proof decomposes the non-base parameter
bundle as `pred.next` and then invokes the native successor-step theorem
`mainInductionSuccessorNext`.

The proof transitively uses the answer-valued induction theorem
`answerMainInduction`.  That theorem now proves the successor branch by strong
induction, including the answer-valued pasting step, so this decomposition
theorem is standard-axiom clean. -/
theorem mainInductionSuccessor
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k)
    (hm1 : params.m ≠ 1) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  rcases Parameters.successorDecompositionOfNeOne params hm1 with ⟨pred, hnext⟩
  have hq : pred.q = params.q := by
    simpa [Parameters.next] using congrArg Parameters.q hnext
  let : FieldModel pred.q := hq.symm ▸ (inferInstance : FieldModel params.q)
  cases hnext
  exact mainInductionSuccessorNext pred strategy eps delta gamma k hgood hk

/-- Corrected large-`k` interface for `thm:main-induction`.

This is the Lean theorem linked from the corrected blueprint statement: a good
symmetric strategy and an integer `k ≥ 400 m d` produce a polynomial
measurement consistent with the point measurement at error `mainInductionError`.
The strengthening from the printed `k ≥ m d` hypothesis in
`references/ldt-paper/inductive_step.tex` is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` as a confirmed statement
correction.

The proof uses the base case `mainInductionBaseCase` and the corrected
large-`k` successor theorem `mainInductionSuccessor`.  In the small-error
successor branch the recursive predecessor calls are supplied by the genuine
strong-induction theorem `answerMainInduction`, and the answer-valued pasting
conclusion is derived inside that route. -/
theorem mainInduction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  by_cases hm1 : params.m = 1
  · exact mainInductionBaseCase params strategy eps delta gamma k hm1 hgood
  · exact mainInductionSuccessor params strategy eps delta gamma k hgood hk hm1


end MIPStarRE.LDT.MainInductionStep

end

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Core.lean. -/
/-!
# Source-Boundary Role-Register Handoff: Core Reductions

This module contains the main-induction handoff, unsymmetrization, and the first
two-space projectivization outputs for the source route toward `thm:main-formal`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

namespace ProjStrat

/-- Apply the source-shaped main-induction theorem to the heterogeneous
role-register symmetrization of a two-space strategy.

Paper origin: `references/ldt-paper/inductive_step.tex:26-83`, where the
general projective strategy of `thm:main-formal` is symmetrized by adding role
registers and `thm:main-induction` is applied to the resulting symmetric
strategy.

This theorem is not a proof of `thm:main-formal`: it stops at the polynomial
measurement produced by corrected large-`k` main induction on the role-register
space.  It does, however, discharge the Step 1 handoff for the two-space
strategy container under the confirmed `400md` correction.  The downstream
unsymmetrization and two-sided projective-submeasurement construction are
formalized later in this file; completion, line-169 transport, and scalar
absorption remain separate. -/
theorem roleRegisterSymmStrategy_sourceMainInduction
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) (RoleRegisterLocal ιA ιB),
      ConsRel (strategy.roleRegisterSymmStrategy).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (MainInductionStep.mainInductionError params k
          (3 * eps) (3 * eps) (3 * eps)) := by
  exact
    MainInductionStep.mainInduction params
      (strategy := strategy.roleRegisterSymmStrategy)
      (eps := 3 * eps) (delta := 3 * eps) (gamma := 3 * eps) (k := k)
      (roleRegisterSymmStrategy_is_good_three_mul
        (strategy := strategy) (eps := eps) hpass)
      hk

-- The proof compares two averaged consistency defects after expanding the
-- role-register symmetrization and polynomial-evaluation extraction maps.






/-- The two unsymmetrized polynomial measurements obtained from the
source-shaped role-register main-induction call.

Paper origin: `references/ldt-paper/inductive_step.tex:68-109`.

This theorem packages the first two quantitative conclusions of the
role-register reduction in the proof of `thm:main-formal`: after applying
source main induction to the heterogeneous role-register symmetrization, the
occupied principal blocks of the resulting polynomial measurement are
consistent with the original two-space point measurements, with the expected
factor-two loss.

It is not the final theorem.  The outputs here are complete polynomial
measurements, not projective measurements, and no self-consistency conclusion is
claimed.  Those are the later projectivization, completion, and scalar
absorption steps in `references/ldt-paper/inductive_step.tex:111-185`.

It uses the corrected large-`k` main-induction handoff; no additional bridge,
package, residual, repair, producer, input, or generic hypothesis is introduced
at the theorem boundary. -/
theorem sourceRoleRegisterUnsymmetrizedPointConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (2 * MainInductionStep.mainInductionError params k
              (3 * eps) (3 * eps) (3 * eps)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (2 * MainInductionStep.mainInductionError params k
              (3 * eps) (3 * eps) (3 * eps)) := by
  rcases roleRegisterSymmStrategy_sourceMainInduction
      params strategy eps hpass k hk with ⟨G, hG⟩
  refine
    ⟨Measurement.extractRoleRegisterAlice G, Measurement.extractRoleRegisterBob G, ?_⟩
  exact
    sourceRoleRegisterPointConsistency_ofSymConsistency params strategy G
      (MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) hG

/-- Complete polynomial measurements obtained from the two-space source
role-register route, including full-polynomial self-consistency.

Paper origin: `references/ldt-paper/inductive_step.tex:68-133`.

This is the source-boundary route through the end of the paper's
Schwartz--Zippel Step 5 calculation.  It applies source main induction to the
heterogeneous role-register symmetrization, extracts the occupied principal
blocks, proves the two factor-two point-consistency estimates, and then applies
the heterogeneous triangle and Schwartz--Zippel calculation to obtain
full-polynomial consistency.

It is still not `thm:main-formal`: the measurements are complete POVMs, not
projective measurements, and the scalar cascade has not yet been absorbed into
`mainFormalError`.

It uses the corrected large-`k` role-register handoff and remains an
intermediate construction, not the final theorem. -/
theorem sourceRoleRegisterCompletePolynomialSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (2 * MainInductionStep.mainInductionError params k
              (3 * eps) (3 * eps) (3 * eps)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (2 * MainInductionStep.mainInductionError params k
              (3 * eps) (3 * eps) (3 * eps)) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (2 * MainInductionStep.mainInductionError params k
                (3 * eps) (3 * eps) (3 * eps) +
              2 * Real.sqrt (3 * eps +
                2 * MainInductionStep.mainInductionError params k
                  (3 * eps) (3 * eps) (3 * eps)) +
              (params.m * params.d : Error) / params.q) := by
  rcases sourceRoleRegisterUnsymmetrizedPointConsistency
      params strategy eps hpass k hk with ⟨G_A, G_B, hpointAGB, hGApointB⟩
  refine ⟨G_A, G_B, hpointAGB, hGApointB, ?_⟩
  exact
    sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
      params strategy eps
      (2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps))
      hpass G_A G_B hpointAGB hGApointB

/-- Alice-side projective submeasurement obtained from a two-space
complete-measurement Step 5 output.

Paper origin: `references/ldt-paper/inductive_step.tex:135-143`, applying
`lem:orthonormalization-main-lemma` to the complete polynomial measurements
whose full-polynomial consistency has just been proved.

This is a genuine two-space consequence of the source-facing orthonormalization
lemma.  It constructs the Alice-side projective submeasurement from the
complete measurement `G_A` and the cross-consistency relation with `G_B`, without
assuming permutation-invariance or identifying the two local Hilbert spaces. -/
theorem sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (ζ : Error)
    (hfull : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ) :
    ∃ P_A : ProjSubMeas (Polynomial params) ιA,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ) := by
  have hζ : 0 ≤ ζ := by
    have hq : qBipartiteConsDefect strategy.state G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
      simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
        hfull.offDiagonalBound
    exact le_trans (qBipartiteConsDefect_nonneg strategy.state G_A.toSubMeas G_B.toSubMeas)
      hq
  exact
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous
      strategy.state strategy.isNormalized G_A G_B ζ hζ hfull

/-- Bob-side projective submeasurement obtained from a two-space
complete-measurement Step 5 output.

Paper origin: `references/ldt-paper/inductive_step.tex:135-143`, applying
`lem:orthonormalization-main-lemma` to the complete polynomial measurements
whose full-polynomial consistency has just been proved.

This is the right-register counterpart of
`sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency`.  It
constructs the Bob-side projective submeasurement from the complete measurement
`G_B` and the cross-consistency relation with `G_A`, without assuming
permutation-invariance or identifying the two local Hilbert spaces. -/
theorem sourceRoleRegisterRightProjectiveSubmeasurement_ofFullConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (ζ : Error)
    (hfull : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ) :
    ∃ P_B : ProjSubMeas (Polynomial params) ιB,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ) := by
  have hζ : 0 ≤ ζ := by
    have hq : qBipartiteConsDefect strategy.state G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
      simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
        hfull.offDiagonalBound
    exact le_trans (qBipartiteConsDefect_nonneg strategy.state G_A.toSubMeas G_B.toSubMeas)
      hq
  exact
    orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous
      strategy.state strategy.isNormalized G_A G_B ζ hζ hfull


end ProjStrat

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Source-Boundary Role-Register Handoff: Final Point Consistency

This module contains the final completed-measurement and point-consistency
statements used by the paper-facing `thm:main-formal` route.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

open LIDT.MIPStarRE.LDT.ProjStrat

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : _root_.LIDT.MIPStarRE.LDT.ProjStrat params ιA ιB)
    (eps : _root_.LIDT.MIPStarRE.LDT.Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G_A : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA,
      ∃ G_B : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB,
        ∃ P_A : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA,
          ∃ P_B : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB,
            _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
                (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
                (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G_B.toSubMeas)
                (2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k
                  (3 * eps) (3 * eps) (3 * eps)) ∧
              _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
                (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G_A.toSubMeas)
                (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
                (2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k
                  (3 * eps) (3 * eps) (3 * eps)) ∧
              _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
                (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_A.toSubMeas)
                (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_B.toSubMeas)
                (2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k
                    (3 * eps) (3 * eps) (3 * eps) +
                  2 * Real.sqrt (3 * eps +
                    2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k
                      (3 * eps) (3 * eps) (3 * eps)) +
                  (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) ∧
              _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
                (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
                (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
                (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError
                  (2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k
                      (3 * eps) (3 * eps) (3 * eps) +
                    2 * Real.sqrt (3 * eps +
                      2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k
                        (3 * eps) (3 * eps) (3 * eps)) +
                    (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)) ∧
              _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
                (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
                (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
                (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError
                  (2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k
                      (3 * eps) (3 * eps) (3 * eps) +
                    2 * Real.sqrt (3 * eps +
                      2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k
                        (3 * eps) (3 * eps) (3 * eps)) +
                    (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)) := by
  rcases _root_.LIDT.MIPStarRE.LDT.ProjStrat.sourceRoleRegisterCompletePolynomialSelfConsistency
      params strategy eps hpass k hk with
    ⟨G_A, G_B, hpointAGB, hGApointB, hfull⟩
  let ζ₁ : _root_.LIDT.MIPStarRE.LDT.Error :=
    2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps) +
      2 * Real.sqrt (3 * eps +
        2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) +
      (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q
  have hfullζ : _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_B.toSubMeas) ζ₁ := by
    simpa [ζ₁] using hfull
  rcases _root_.LIDT.MIPStarRE.LDT.ProjStrat.sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency
      params strategy G_A G_B ζ₁ hfullζ with ⟨P_A, hP_A⟩
  rcases _root_.LIDT.MIPStarRE.LDT.ProjStrat.sourceRoleRegisterRightProjectiveSubmeasurement_ofFullConsistency
      params strategy G_A G_B ζ₁ hfullζ with ⟨P_B, hP_B⟩
  exact ⟨G_A, G_B, P_A, P_B, hpointAGB, hGApointB, hfull, by
    simpa [ζ₁] using hP_A, by
    simpa [ζ₁] using hP_B⟩
