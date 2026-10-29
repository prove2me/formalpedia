-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.mainFormalConclusion_ofRoleRegisterScalarBoundary
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:55:05.802052+00:00
-- url     : https://prove2.me/submissions/89f87fae-99e6-4962-a57a-028fa24e0bab

-- Generated proof for MIPStarRE.LDT.Test.mainFormalConclusion_ofRoleRegisterScalarBoundary.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_SourceScalars
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_orthonormalizeAndCompleteError_le_absorbedZeta2
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_sqrt_orthonormalizationError_eq
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_axisParallelRoleAverage_nonneg
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_diagonalRoleAverage_nonneg
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_lowIndividualDegreeFailureProbability_eq_role_averages
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_sourceRoleRegisterFinalPointConsistency
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_errorCascade_le_mainFormalError
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mainFormalError_ge_one_of_one_lt_eps
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mainFormalError_ge_one_of_q_lt_d
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mainFormalInductionNu_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mainFormalInductionNu_nonneg
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_zeta4Repaired_bound

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

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean. -/
/-!
# Error cascade — core definitions

This module defines the central error quantities `mainFormalError`,
`mainFormalEnvelope`, the cascade variables `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`,
and the `CascadeHypotheses` numeric regime used throughout the error-cascade
bookkeeping for Step 8 of `mainFormal`.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test



























namespace CascadeHypotheses

variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)

include h

/-- Non-negativity of `d/q` under the standing hypotheses. -/
theorem dqNN : 0 ≤ (params.d : Error) / (params.q : Error) :=
  div_nonneg (Nat.cast_nonneg _) h.hqPos.le





















end CascadeHypotheses

end Test

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Final.lean. -/
/-!
# Role-Register Averaging: Goodness Bound

This module packages the branch equalities into the three-times-error goodness
bound for the role-register symmetric strategy.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat



/-- The point-agreement branch of a two-space projective strategy is
nonnegative. -/
theorem pointAgreementFailureProbability_nonneg
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    0 ≤ strategy.pointAgreementFailureProbability := by
  unfold ProjStrat.pointAgreementFailureProbability
  exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)



/-- The full low-individual-degree failure probability of a two-space projective
strategy is nonnegative. -/
theorem lowIndividualDegreeFailureProbability_nonneg
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    0 ≤ strategy.lowIndividualDegreeFailureProbability := by
  have haxis : 0 ≤ strategy.axisParallelRoleAverage :=
    axisParallelRoleAverage_nonneg strategy
  have hpoint : 0 ≤ strategy.pointAgreementFailureProbability :=
    pointAgreementFailureProbability_nonneg strategy
  have hdiag : 0 ≤ strategy.diagonalRoleAverage :=
    diagonalRoleAverage_nonneg strategy
  rw [lowIndividualDegreeFailureProbability_eq_role_averages]
  nlinarith

/-- Any passing two-space projective strategy has a nonnegative error
parameter. -/
theorem eps_nonneg_of_passes
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    {strategy : ProjStrat params ιA ιB} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    0 ≤ eps :=
  (lowIndividualDegreeFailureProbability_nonneg strategy).trans hpass.soundnessHypothesis




end ProjStrat

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/SourceScalars.lean. -/
/-!
# Main-formal scalar bounds

Scalar estimates for the two-space `mainFormal` theorem.  This module defines
the five scalars that appear in the paper's error calculation:

* `σ` — the symmetrized induction consistency error
* `ζ₁` — the cross-consistency error after unsymmetrization
* `ζ₂` — the orthonormalize-and-complete closeness error
* `ζ₃` — the projective self-consistency error
* `ζ₄` — the final point-consistency error

The core structure `MainFormalScalarBounds` (Prop) bundles the three
hypotheses needed to invoke the checked Step 8 bound
`errorCascade_le_mainFormalError`:

* `cascadeHypotheses` — the standing scalar regime (`q > 0`, `k ≥ 1`,
  `m ≥ 1`, `0 ≤ ε ≤ 1`, `d ≤ q`).
* `inductionNu_nonneg` — nonnegativity of the symmetrized main-induction
  `ν` at `(3ε, 3ε, 3ε)`.
* `inductionNu_bound` — the paper line 71–73 coarsening
  `ν ≤ 10000 k² m² (ε^{1/1024} + (d/q)^{1/1024})`.

The cascade comparisons `ζ₁ ≤ …`, `ζ₃ ≤ 2·mainFormalError`, etc. are then
derived in the private theorem `cascadeBounds` via
`errorCascade_le_mainFormalError`, which calls the already-formalized
scalar cascade estimates from `LDT.Test.MainTheorem.ScalarBounds`.  The module also
provides the vacuous-branch analysis (`mainFormalError_ge_one_of_*`) and
the coarsening lemma that absorbs `orthonormalizeAndCompleteError` into
`ζ₂` (`orthonormalizeAndCompleteError_zeta1_le_zeta2`).

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  error computations (lines 68–75, 186–234).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-error-cascade}`,
  `\label{thm:sigma-bound-main-formal}`, and
  `\label{thm:zeta-bounds-main-formal}`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test



/-- The `σ` built from `mainFormalInductionNu` is definitionally the Section 6
main-induction error at `(3ε, 3ε, 3ε)`.

This is the exact scalar handoff between paper lines 75--81 and the cascade
notation used from line 133 onward. -/
theorem mainFormalScalarSigma_eq_mainInductionError (params : Parameters)
    (k : ℕ) (eps : Error) :
    cascadeSigma params k (mainFormalInductionNu params k eps) =
      MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps) :=
  rfl











/-- In the non-vacuous branch of `mainFormal`, the standing scalar hypotheses of
Step 8 follow from the theorem's basic positivity data.

**Source:** This is source-faithful scalar bookkeeping for
`references/ldt-paper/inductive_step.tex:186-234`, under the corrected
boundaries documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex`
and `docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`.

If either `ε > 1` or `d > q`, the final error `mainFormalError` is already at
least `1`, so `mainFormal_trivial_witness` handles the theorem. Hence under
`¬ 1 ≤ mainFormalError params k eps` we may safely enter the paper's cascade
regime `0 ≤ ε ≤ 1` and `d/q ≤ 1`. -/
theorem cascadeHypotheses_of_not_mainFormalError_ge_one
    {params : Parameters} {k : ℕ} {eps : Error}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    CascadeHypotheses params k eps where
  hk := Nat.one_le_cast.mpr hk0
  hm := Nat.one_le_cast.mpr params.hm
  hepsNN := hepsNN
  hepsOne := le_of_not_gt fun heps =>
    hsmall (mainFormalError_ge_one_of_one_lt_eps params k hk0 heps)
  hdq := le_of_not_gt fun hdq =>
    hsmall (mainFormalError_ge_one_of_q_lt_d params k eps hk0 hepsNN hdq)
  hqPos := params.q_cast_pos



namespace MainFormalScalarBounds

/-- Build the scalar data once the standing cascade hypotheses hold; the
main-induction `ν` nonnegativity and paper line 71--73 coarsening are discharged
by the checked scalar lemmas above.

**Source:** This is a source-faithful constructor for the scalar regime in
`references/ldt-paper/inductive_step.tex:68-75` and
`references/ldt-paper/inductive_step.tex:186-234`. -/
theorem ofCascadeHypotheses {params : Parameters} {eps : Error} {k : ℕ}
    (h : CascadeHypotheses params k eps) :
    MainFormalScalarBounds params eps k where
  cascadeHypotheses := h
  inductionNu_nonneg := mainFormalInductionNu_nonneg h
  inductionNu_bound := mainFormalInductionNu_bound h

/-- Build the scalar data in the non-vacuous branch of `mainFormal`.

The branch hypothesis `¬ 1 ≤ mainFormalError params k eps` rules out the
non-paper regimes `ε > 1` and `d > q`, while `hepsNN` and `hk0` supply the
remaining scalar positivity hypotheses. -/
theorem ofNontrivialMainFormal {params : Parameters} {eps : Error} {k : ℕ}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MainFormalScalarBounds params eps k :=
  ofCascadeHypotheses (cascadeHypotheses_of_not_mainFormalError_ge_one hepsNN hk0 hsmall)















private theorem cascadeBounds {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) :
    scalars.sigma ≤ mainFormalError params k eps ∧
      scalars.zeta1 ≤ mainFormalError params k eps ∧
      scalars.zeta2 ≤ mainFormalError params k eps ∧
      scalars.zeta3 ≤ 2 * mainFormalError params k eps ∧
      scalars.zeta4 ≤ mainFormalError params k eps := by
  exact errorCascade_le_mainFormalError
    (params := params) (k := k) (eps := eps)
    (ν := mainFormalInductionNu params k eps)
    (σ := scalars.sigma) (ζ₁ := scalars.zeta1)
    (ζ₂ := scalars.zeta2) (ζ₃ := scalars.zeta3)
    scalars.cascadeHypotheses scalars.inductionNu_nonneg scalars.inductionNu_bound
    rfl rfl rfl rfl

/-- Nonnegativity of the native cascade `σ`. -/
theorem sigma_nonneg {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) :
    0 ≤ scalars.sigma := by
  unfold sigma cascadeSigma
  positivity [scalars.inductionNu_nonneg]

/-- Nonnegativity of the native cascade `ζ₁`. -/
theorem zeta1_nonneg {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) :
    0 ≤ scalars.zeta1 := by
  have hσ : 0 ≤ scalars.sigma := sigma_nonneg scalars
  have hdq : 0 ≤ (params.d : Error) / (params.q : Error) :=
    scalars.cascadeHypotheses.dqNN
  unfold zeta1 cascadeZeta1
  positivity [hσ, scalars.cascadeHypotheses.hepsNN, hdq]

/-- Step 8 absorption for the native `ζ₁` target. -/
theorem zeta1_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) :
    scalars.zeta1 ≤ mainFormalError params k eps :=
  (cascadeBounds scalars).2.1

/-- In the non-vacuous branch, the cascade scalar `ζ₁` lies in the unit interval. -/
theorem zeta1_le_one_of_not_mainFormalError_ge_one
    {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    scalars.zeta1 ≤ 1 := by
  exact le_of_lt <|
    (zeta1_le_mainFormalError scalars).trans_lt (lt_of_not_ge hsmall)

/-- The formal `ζ₂` scalar absorbs the literal Step 6 orthonormalize-and-complete
error in the non-vacuous branch. -/
theorem orthonormalizeAndCompleteError_zeta1_le_zeta2
    {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1 ≤
      scalars.zeta2 := by
  have hζ0 : 0 ≤ scalars.zeta1 := zeta1_nonneg scalars
  have hζ1 : scalars.zeta1 ≤ 1 :=
    zeta1_le_one_of_not_mainFormalError_ge_one scalars hsmall
  simpa [zeta2, cascadeZeta2] using
    MakingMeasurementsProjective.orthonormalizeAndCompleteError_le_absorbedZeta2
      (ζ := scalars.zeta1) hζ0 hζ1

/-- Step 8 absorption for the repaired `ζ₄` point-consistency targets.

**Source:** This is source-faithful scalar bookkeeping for the repaired
line-169 route documented in `docs/paper-gaps/issue-1099-sharper-local-fix.tex`
and the final absorption estimate from
`references/ldt-paper/inductive_step.tex:186-234`. -/
theorem zeta4Repaired_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) :
    scalars.zeta4Repaired ≤ mainFormalError params k eps := by
  have hσEq : scalars.sigma = cascadeSigma params k (mainFormalInductionNu params k eps) := rfl
  have hζ₁Eq : scalars.zeta1 = cascadeZeta1 params eps scalars.sigma := rfl
  have hζ₂Eq : scalars.zeta2 = cascadeZeta2 scalars.zeta1 := rfl
  have hζ₃Eq : scalars.zeta3 = cascadeZeta3 scalars.zeta1 scalars.zeta2 := rfl
  unfold zeta4Repaired
  exact zeta4Repaired_bound
    scalars.cascadeHypotheses scalars.inductionNu_nonneg scalars.inductionNu_bound
    hσEq hζ₁Eq hζ₂Eq hζ₃Eq

/-- Step 8 absorption for the native `ζ₃/2` self-consistency target. -/
theorem zeta3_div_two_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) :
    scalars.zeta3 / 2 ≤ mainFormalError params k eps := by
  have hzeta3 := (cascadeBounds scalars).2.2.2.1
  linarith

end MainFormalScalarBounds

end Test

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Main-formal soundness theorem

This module contains the corrected two-space final theorem for
`thm:main-formal`.  The theorem starts from a general projective strategy
`ProjStrat params ιA ιB`, applies the heterogeneous role-register route, and
absorbs the explicit intermediate errors into the final parameter
`mainFormalError`.

The public theorem uses the confirmed large-`k` correction `k ≥ 400 m d` and
the nonzero sampling condition `0 < k`.  These are documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` and
`docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`.

## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `thm:main-formal` at line 180; its proof is in
  `references/ldt-paper/inductive_step.tex` (lines 26–236).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal}`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

/-! ### Two-space source route -/

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
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps) :
    ∃ G_A : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA,
      ∃ G_B : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB,
        _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G_B.toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps) ∧
          _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G_A.toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps) ∧
          _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_A.toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_B.toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps) := by
  classical
  have hepsNN : 0 ≤ eps := _root_.LIDT.MIPStarRE.LDT.ProjStrat.eps_nonneg_of_passes hpass
  let scalars : _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds params eps k :=
    _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.ofNontrivialMainFormal hepsNN hk0 hsmall
  let σsrc : _root_.LIDT.MIPStarRE.LDT.Error :=
    2 * _root_.LIDT.MIPStarRE.LDT.MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let ζ₁src : _root_.LIDT.MIPStarRE.LDT.Error :=
    σsrc + 2 * Real.sqrt (3 * eps + σsrc) + (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q
  let ζ₂src : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁src
  let ηsrc : _root_.LIDT.MIPStarRE.LDT.Error :=
    ζ₁src + Real.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError ζ₁src)
  let ζ₃src : _root_.LIDT.MIPStarRE.LDT.Error := 6 * ζ₁src + 6 * ζ₂src
  have hσsrc : σsrc = 2 * scalars.sigma := by
    simp [σsrc, _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.sigma, _root_.LIDT.MIPStarRE.LDT.Test.mainFormalScalarSigma_eq_mainInductionError]
  have hζ₁src : ζ₁src = scalars.zeta1 := by
    simp [ζ₁src, σsrc, _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.zeta1, _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta1,
      _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.sigma, _root_.LIDT.MIPStarRE.LDT.Test.mainFormalScalarSigma_eq_mainInductionError]
  have hζ₂src : ζ₂src ≤ scalars.zeta2 := by
    change _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁src ≤ scalars.zeta2
    rw [hζ₁src]
    exact _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.orthonormalizeAndCompleteError_zeta1_le_zeta2
      scalars hsmall
  have hηsrc : ηsrc = scalars.line169Error := by
    have hζ0 : 0 ≤ scalars.zeta1 := _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.zeta1_nonneg scalars
    have hsqrt :
        Real.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError scalars.zeta1) =
          10 * Real.rpow scalars.zeta1 (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.sqrt_orthonormalizationError_eq hζ0
    simp [ηsrc, hζ₁src, _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.line169Error,
      _root_.LIDT.MIPStarRE.LDT.Test.cascadeLine169RepairError, hsqrt]
  have hζ₃src : ζ₃src ≤ scalars.zeta3 := by
    have hζ₁le : ζ₁src ≤ scalars.zeta1 := le_of_eq hζ₁src
    have hcore : 6 * ζ₁src + 6 * ζ₂src ≤ 6 * scalars.zeta1 + 6 * scalars.zeta2 := by
      nlinarith
    simpa [ζ₃src, _root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.zeta3, _root_.LIDT.MIPStarRE.LDT.Test.cascadeZeta3] using hcore
  have hsourcePoint :
      σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2) ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps := by
    have hrad :
        ηsrc + ζ₃src / 2 ≤ scalars.line169Error + scalars.zeta3 / 2 := by
      have hηle : ηsrc ≤ scalars.line169Error := le_of_eq hηsrc
      nlinarith
    have hsqrt :
        Real.sqrt (ηsrc + ζ₃src / 2) ≤
          Real.sqrt (scalars.line169Error + scalars.zeta3 / 2) :=
      Real.sqrt_le_sqrt hrad
    have hrepaired :
        σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2) ≤ scalars.zeta4Repaired := by
      calc
        σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2)
            = 2 * scalars.sigma + 2 * Real.sqrt (ηsrc + ζ₃src / 2) := by
              rw [hσsrc]
        _ ≤ 2 * scalars.sigma + 2 *
              Real.sqrt (scalars.line169Error + scalars.zeta3 / 2) := by
            nlinarith
        _ = scalars.zeta4Repaired := by
            rfl
    exact hrepaired.trans (_root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.zeta4Repaired_le_mainFormalError scalars)
  have hsourceSelf :
      ζ₃src / 2 ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps := by
    have htoCascade : ζ₃src / 2 ≤ scalars.zeta3 / 2 := by
      nlinarith
    exact htoCascade.trans (_root_.LIDT.MIPStarRE.LDT.Test.MainFormalScalarBounds.zeta3_div_two_le_mainFormalError scalars)
  rcases _root_.LIDT.MIPStarRE.LDT.ProjStrat.sourceRoleRegisterFinalPointConsistency
      params strategy eps hpass k hk with ⟨Q_A, Q_B, hA, hrest⟩
  rcases hrest with ⟨hB, hrest⟩
  rcases hrest with ⟨_hQQEval, hQQ⟩
  refine ⟨Q_A, Q_B, ?_, ?_, ?_⟩
  · exact _root_.LIDT.MIPStarRE.LDT.ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourcePoint) hA
  · exact _root_.LIDT.MIPStarRE.LDT.ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourcePoint) hB
  · exact _root_.LIDT.MIPStarRE.LDT.ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourceSelf) hQQ
