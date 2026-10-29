-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.sourceRoleRegisterPointConsistency_ofSymConsistency
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:23:18.724978+00:00
-- url     : https://prove2.me/submissions/742a20ab-5461-4d42-84c5-95de0ac9e2b4

-- Generated proof for MIPStarRE.LDT.ProjStrat.sourceRoleRegisterPointConsistency_ofSymConsistency.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average

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

/- Source helpers from MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean. -/
/-!
# Heterogeneous role-register measurement extraction

This file contains the principal-block extraction used to unsymmetrize a
measurement on the heterogeneous role-register space
`Role × (ιA ⊕ ιB)`.  The Alice extraction is the block indexed by
`(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by
`(Role.B, Sum.inr _)`.

These are the two-space analogues of the same-space extractions in
`MIPStarRE.LDT.Test.Unsymmetrization`.  They preserve POVM completeness, but
they do not assert that arbitrary principal blocks of a projective measurement
remain projective.  As in the paper proof, projectivity is restored later by
the projectivization step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 84--109.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace ProjStrat

/-! ### Principal blocks of heterogeneous role-register operators -/













































end ProjStrat

namespace SubMeas













/-- Alice extraction commutes with outcome postprocessing. -/
theorem extractRoleRegisterAlice_postprocess {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (f : α → β) :
    (postprocess A f).extractRoleRegisterAlice =
      postprocess A.extractRoleRegisterAlice f := by
  classical
  refine SubMeas.ext ?_ rfl
  intro b
  change ProjStrat.extractRoleRegisterAliceBlock
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a) =
    ∑ a ∈ Finset.univ.filter (fun a => f a = b),
      ProjStrat.extractRoleRegisterAliceBlock (A.outcome a)
  exact ProjStrat.extractRoleRegisterAliceBlock_finset_sum
    (Finset.univ.filter (fun a => f a = b)) A.outcome

/-- Bob extraction commutes with outcome postprocessing. -/
theorem extractRoleRegisterBob_postprocess {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (f : α → β) :
    (postprocess A f).extractRoleRegisterBob =
      postprocess A.extractRoleRegisterBob f := by
  classical
  refine SubMeas.ext ?_ rfl
  intro b
  change ProjStrat.extractRoleRegisterBobBlock
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a) =
    ∑ a ∈ Finset.univ.filter (fun a => f a = b),
      ProjStrat.extractRoleRegisterBobBlock (A.outcome a)
  exact ProjStrat.extractRoleRegisterBobBlock_finset_sum
    (Finset.univ.filter (fun a => f a = b)) A.outcome

end SubMeas

namespace Measurement













end Measurement

namespace ProjStrat

/-! ### Extraction on the constructed role-register measurements -/

/-! ### Trace compression for occupied role-register sectors -/







































/-- One heterogeneous questionwise factor-two consequence of the role-register
unsymmetrization identity. -/
theorem qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) :
    qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas ≤
      2 * qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas := by
  have h := qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average ψ hψ MA MB G
  have hnonneg :
      0 ≤ qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas :=
    qBipartiteConsDefect_nonneg ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas
  linarith

/-- The other heterogeneous questionwise factor-two consequence of the
role-register unsymmetrization identity. -/
theorem qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) :
    qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas ≤
      2 * qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas := by
  have h := qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average ψ hψ MA MB G
  have hnonneg :
      0 ≤ qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas :=
    qBipartiteConsDefect_nonneg ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas
  linarith

/-- Polynomial evaluation commutes with Alice extraction from a heterogeneous
role-register polynomial submeasurement. -/
theorem polynomialEvaluationFamily_extractRoleRegisterAlice
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (G : SubMeas (Polynomial params) (RoleRegisterLocal ιA ιB)) :
    polynomialEvaluationFamily params (SubMeas.extractRoleRegisterAlice G) =
      fun u => SubMeas.extractRoleRegisterAlice (polynomialEvaluationFamily params G u) := by
  funext u
  exact (SubMeas.extractRoleRegisterAlice_postprocess G
    (fun g : Polynomial params => g u)).symm

/-- Polynomial evaluation commutes with Bob extraction from a heterogeneous
role-register polynomial submeasurement. -/
theorem polynomialEvaluationFamily_extractRoleRegisterBob
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (G : SubMeas (Polynomial params) (RoleRegisterLocal ιA ιB)) :
    polynomialEvaluationFamily params (SubMeas.extractRoleRegisterBob G) =
      fun u => SubMeas.extractRoleRegisterBob (polynomialEvaluationFamily params G u) := by
  funext u
  exact (SubMeas.extractRoleRegisterBob_postprocess G
    (fun g : Polynomial params => g u)).symm

/-- Measurement-level form of
`polynomialEvaluationFamily_extractRoleRegisterAlice`. -/
theorem polynomialEvaluationFamily_measurement_extractRoleRegisterAlice
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (G : Measurement (Polynomial params) (RoleRegisterLocal ιA ιB)) :
    polynomialEvaluationFamily params
        (Measurement.extractRoleRegisterAlice G).toSubMeas =
      fun u => SubMeas.extractRoleRegisterAlice
        (polynomialEvaluationFamily params G.toSubMeas u) := by
  exact polynomialEvaluationFamily_extractRoleRegisterAlice G.toSubMeas

/-- Measurement-level form of
`polynomialEvaluationFamily_extractRoleRegisterBob`. -/
theorem polynomialEvaluationFamily_measurement_extractRoleRegisterBob
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (G : Measurement (Polynomial params) (RoleRegisterLocal ιA ιB)) :
    polynomialEvaluationFamily params
        (Measurement.extractRoleRegisterBob G).toSubMeas =
      fun u => SubMeas.extractRoleRegisterBob
        (polynomialEvaluationFamily params G.toSubMeas u) := by
  exact polynomialEvaluationFamily_extractRoleRegisterBob G.toSubMeas

end ProjStrat

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Source-Boundary Role-Register Handoff: Core Reductions

This module contains the main-induction handoff, unsymmetrization, and the first
two-space projectivization outputs for the source route toward `thm:main-formal`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

open LIDT.MIPStarRE.LDT.ProjStrat



-- The proof compares two averaged consistency defects after expanding the
-- role-register symmetrization and polynomial-evaluation extraction maps.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : _root_.LIDT.MIPStarRE.LDT.ProjStrat params ιA ιB)
    (G : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) (_root_.LIDT.MIPStarRE.LDT.ProjStrat.RoleRegisterLocal ιA ιB))
    (σ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hsym :
      _root_.LIDT.MIPStarRE.LDT.ConsRel (strategy.roleRegisterSymmStrategy).state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas)
        σ) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params
          (_root_.LIDT.MIPStarRE.LDT.Measurement.extractRoleRegisterBob G).toSubMeas)
        (2 * σ) ∧
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params
          (_root_.LIDT.MIPStarRE.LDT.Measurement.extractRoleRegisterAlice G).toSubMeas)
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        (2 * σ) := by
  have : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  have : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  constructor
  · refine ⟨?_⟩
    have hmono :
        _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params
              (_root_.LIDT.MIPStarRE.LDT.Measurement.extractRoleRegisterBob G).toSubMeas)
          ≤
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          2 * _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) u)) := by
      unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro u
      let Gu := _root_.LIDT.MIPStarRE.LDT.Test.polynomialEvaluationMeasurementFamily params G u
      have hpoint :=
        _root_.LIDT.MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm
          strategy.state strategy.isNormalized
          (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)
          Gu
      rw [congrFun (_root_.LIDT.MIPStarRE.LDT.ProjStrat.polynomialEvaluationFamily_measurement_extractRoleRegisterBob G) u]
      change
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
            (strategy.pointMeasurementA u).toSubMeas
            (Gu.extractRoleRegisterBob).toSubMeas
          ≤
          2 *
            _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState strategy.state)
              (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas (strategy.pointMeasurementA u)
                (strategy.pointMeasurementB u)).toSubMeas
              Gu.toSubMeas
      exact hpoint
    have hscale :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          2 * _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) u))
          =
        2 * _root_.LIDT.MIPStarRE.LDT.bipartiteConsError (strategy.roleRegisterSymmStrategy).state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) := by
      simp [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    calc
      _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params
            (_root_.LIDT.MIPStarRE.LDT.Measurement.extractRoleRegisterBob G).toSubMeas)
        ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
            2 * _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
              ((_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
                (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
              ((_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) u)) := hmono
      _ = 2 * _root_.LIDT.MIPStarRE.LDT.bipartiteConsError (strategy.roleRegisterSymmStrategy).state
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) := hscale
      _ ≤ 2 * σ := by
            exact mul_le_mul_of_nonneg_left hsym.offDiagonalBound (by norm_num)
  · refine ⟨?_⟩
    have hmono :
        _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params
              (_root_.LIDT.MIPStarRE.LDT.Measurement.extractRoleRegisterAlice G).toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          ≤
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          2 * _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) u)) := by
      unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro u
      let Gu := _root_.LIDT.MIPStarRE.LDT.Test.polynomialEvaluationMeasurementFamily params G u
      have hpoint :=
        _root_.LIDT.MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm
          strategy.state strategy.isNormalized
          (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)
          Gu
      rw [congrFun (_root_.LIDT.MIPStarRE.LDT.ProjStrat.polynomialEvaluationFamily_measurement_extractRoleRegisterAlice G) u]
      change
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
            (Gu.extractRoleRegisterAlice).toSubMeas
            (strategy.pointMeasurementB u).toSubMeas
          ≤
          2 *
            _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState strategy.state)
              (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas (strategy.pointMeasurementA u)
                (strategy.pointMeasurementB u)).toSubMeas
              Gu.toSubMeas
      exact hpoint
    have hscale :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          2 * _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) u))
          =
        2 * _root_.LIDT.MIPStarRE.LDT.bipartiteConsError (strategy.roleRegisterSymmStrategy).state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) := by
      simp [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    calc
      _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params
            (_root_.LIDT.MIPStarRE.LDT.Measurement.extractRoleRegisterAlice G).toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
            2 * _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
              ((_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
                (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
              ((_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) u)) := hmono
      _ = 2 * _root_.LIDT.MIPStarRE.LDT.bipartiteConsError (strategy.roleRegisterSymmStrategy).state
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params G.toSubMeas) := hscale
      _ ≤ 2 * σ := by
            exact mul_le_mul_of_nonneg_left hsym.offDiagonalBound (by norm_num)
