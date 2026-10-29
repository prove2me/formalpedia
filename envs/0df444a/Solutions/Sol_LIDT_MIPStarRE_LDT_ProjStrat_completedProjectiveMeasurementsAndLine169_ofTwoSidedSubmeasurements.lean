-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:12:25.920043+00:00
-- url     : https://prove2.me/submissions/bc1c8cd1-f8b1-48c0-a12d-3243c42978fd

-- Generated proof for MIPStarRE.LDT.ProjStrat.completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_completion_self_distance
import Theorems.Thm_LIDT_MIPStarRE_LDT_qBipartiteConsDefect_of_measurements

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

/- Source helpers from MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Completion.lean. -/
/-!
# Preliminary comparison theorems: bipartite self-consistency (completion)

Completion-transfer lemmas for bipartite self-consistency.  The constant
`Unit`-family reductions identify `sddError` and `sscError` with their pointwise
forms, and the later lemmas compare a submeasurement with its completion.

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- For a constant `Unit`-indexed family, `sddError` reduces to `qSDD`. -/
lemma constFamily_sdd_unit
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    sddError ψ (uniformDistribution Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) =
      qSDD ψ A B := by
  simp [sddError, avgOver, uniformDistribution, constSubMeasFamily]









end MIPStarRE.LDT.Preliminaries

end

/- Source helpers from MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Completion.lean. -/
/-!
# Source-Boundary Role-Register Handoff: Completion Lemmas

This module contains the completion and line-169 transport lemmas for the
two-space source role-register route.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

namespace ProjStrat

/-- Completing after left tensor placement agrees with left tensor placement
after completing the local submeasurement.

This is the bookkeeping needed to apply the standard completion-distance
identity on the product Hilbert space while returning the local completed
projective measurement appearing in the paper. -/
private lemma qSDD_leftPlaced_completeAtOutcome_eq
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (A B : SubMeas Outcome ιA) (a0 : Outcome) :
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) A)
        (Preliminaries.completeAtOutcome (leftPlacedSubMeas (ιB := ιB) B) a0).toSubMeas =
      qSDD ψ (leftPlacedSubMeas (ιB := ιB) A)
        (leftPlacedSubMeas (ιB := ιB)
          (Preliminaries.completeAtOutcome B a0).toSubMeas) := by
  have hcomplete_outcome :
      ∀ a : Outcome,
        (Preliminaries.completeAtOutcome
            (leftPlacedSubMeas (ιB := ιB) B) a0).toSubMeas.outcome a =
          (leftPlacedSubMeas (ιB := ιB)
            (Preliminaries.completeAtOutcome B a0).toSubMeas).outcome a := by
    intro a
    by_cases h : a = a0
    · subst h
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, leftPlacedSubMeas, leftTensor,
          sub_eq_add_neg, h₁, h₂, add_comm, add_assoc]
    · ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, leftPlacedSubMeas, leftTensor, h, h₁, h₂]
  unfold qSDD qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [hcomplete_outcome a]

/-- Completing after right tensor placement agrees with right tensor placement
after completing the local submeasurement. -/
private lemma qSDD_rightPlaced_completeAtOutcome_eq
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (A B : SubMeas Outcome ιB) (a0 : Outcome) :
    qSDD ψ (rightPlacedSubMeas (ιA := ιA) A)
        (Preliminaries.completeAtOutcome (rightPlacedSubMeas (ιA := ιA) B) a0).toSubMeas =
      qSDD ψ (rightPlacedSubMeas (ιA := ιA) A)
        (rightPlacedSubMeas (ιA := ιA)
          (Preliminaries.completeAtOutcome B a0).toSubMeas) := by
  have hcomplete_outcome :
      ∀ a : Outcome,
        (Preliminaries.completeAtOutcome
            (rightPlacedSubMeas (ιA := ιA) B) a0).toSubMeas.outcome a =
          (rightPlacedSubMeas (ιA := ιA)
            (Preliminaries.completeAtOutcome B a0).toSubMeas).outcome a := by
    intro a
    by_cases h : a = a0
    · subst h
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, rightPlacedSubMeas, rightTensor,
          sub_eq_add_neg, h₁, h₂, add_comm, add_assoc]
    · ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, rightPlacedSubMeas, rightTensor, h, h₁, h₂]
  unfold qSDD qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [hcomplete_outcome a]

/-- If the missing left total of a projective submeasurement is small on the
state, then the canonical completion is close to the submeasurement after left
tensor placement. -/
private lemma qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (P : ProjSubMeas Outcome ιA) (a0 : Outcome) {ζ : Error}
    (hgap : 1 - ev ψ (leftTensor (ι₂ := ιB) P.toSubMeas.total) ≤ ζ) :
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) P.toSubMeas)
      (leftPlacedSubMeas (ιB := ιB)
        (Preliminaries.completeAtOutcomeProj P a0).toSubMeas) ≤ ζ := by
  let R : MIPStarRE.Quantum.Op (ιA × ιB) :=
    (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
      (leftPlacedSubMeas (ιB := ιB) P.toSubMeas).total
  have hraw :
      qSDD ψ (leftPlacedSubMeas (ιB := ιB) P.toSubMeas)
          (Preliminaries.completeAtOutcome
            (leftPlacedSubMeas (ιB := ιB) P.toSubMeas) a0).toSubMeas ≤
        ζ := by
    have hcomp :
        qSDD ψ (leftPlacedSubMeas (ιB := ιB) P.toSubMeas)
            (Preliminaries.completeAtOutcome
              (leftPlacedSubMeas (ιB := ιB) P.toSubMeas) a0).toSubMeas =
          ev ψ (R * R) := by
      simpa [R] using
        (Preliminaries.completion_self_distance ψ
          (leftPlacedSubMeas (ιB := ιB) P.toSubMeas) a0)
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      exact sub_nonneg.mpr (leftPlacedSubMeas (ιB := ιB) P.toSubMeas).total_le_one
    have hR_le_one : R ≤ 1 := by
      dsimp [R]
      exact sub_le_self (1 : MIPStarRE.Quantum.Op (ιA × ιB))
        (leftPlacedSubMeas (ιB := ιB) P.toSubMeas).total_nonneg
    have hR_sq_le : R * R ≤ R :=
      MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
    have hR_sq_ev : ev ψ (R * R) ≤ ev ψ R :=
      ev_mono ψ _ _ hR_sq_le
    have hR_ev : ev ψ R ≤ ζ := by
      have hR_eq :
          ev ψ R =
            1 - ev ψ (leftTensor (ι₂ := ιB) P.toSubMeas.total) := by
        dsimp [R]
        rw [ev_sub]
        simp [ev_one_of_isNormalized ψ hψ]
      rw [hR_eq]
      exact hgap
    rw [hcomp]
    exact le_trans hR_sq_ev hR_ev
  have hq_eq :=
    qSDD_leftPlaced_completeAtOutcome_eq ψ P.toSubMeas P.toSubMeas a0
  rw [hq_eq] at hraw
  simpa [Preliminaries.completeAtOutcomeProj_toSubMeas] using hraw

/-- Right tensor-factor counterpart of
`qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap`. -/
private lemma qSDD_completeAtOutcomeProj_rightPlaced_le_of_total_gap
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (P : ProjSubMeas Outcome ιB) (a0 : Outcome) {ζ : Error}
    (hgap : 1 - ev ψ (rightTensor (ι₁ := ιA) P.toSubMeas.total) ≤ ζ) :
    qSDD ψ (rightPlacedSubMeas (ιA := ιA) P.toSubMeas)
      (rightPlacedSubMeas (ιA := ιA)
        (Preliminaries.completeAtOutcomeProj P a0).toSubMeas) ≤ ζ := by
  let R : MIPStarRE.Quantum.Op (ιA × ιB) :=
    (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
      (rightPlacedSubMeas (ιA := ιA) P.toSubMeas).total
  have hraw :
      qSDD ψ (rightPlacedSubMeas (ιA := ιA) P.toSubMeas)
          (Preliminaries.completeAtOutcome
            (rightPlacedSubMeas (ιA := ιA) P.toSubMeas) a0).toSubMeas ≤
        ζ := by
    have hcomp :
        qSDD ψ (rightPlacedSubMeas (ιA := ιA) P.toSubMeas)
            (Preliminaries.completeAtOutcome
              (rightPlacedSubMeas (ιA := ιA) P.toSubMeas) a0).toSubMeas =
          ev ψ (R * R) := by
      simpa [R] using
        (Preliminaries.completion_self_distance ψ
          (rightPlacedSubMeas (ιA := ιA) P.toSubMeas) a0)
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      exact sub_nonneg.mpr (rightPlacedSubMeas (ιA := ιA) P.toSubMeas).total_le_one
    have hR_le_one : R ≤ 1 := by
      dsimp [R]
      exact sub_le_self (1 : MIPStarRE.Quantum.Op (ιA × ιB))
        (rightPlacedSubMeas (ιA := ιA) P.toSubMeas).total_nonneg
    have hR_sq_le : R * R ≤ R :=
      MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
    have hR_sq_ev : ev ψ (R * R) ≤ ev ψ R :=
      ev_mono ψ _ _ hR_sq_le
    have hR_ev : ev ψ R ≤ ζ := by
      have hR_eq :
          ev ψ R =
            1 - ev ψ (rightTensor (ι₁ := ιA) P.toSubMeas.total) := by
        dsimp [R]
        rw [ev_sub]
        simp [ev_one_of_isNormalized ψ hψ]
      rw [hR_eq]
      exact hgap
    rw [hcomp]
    exact le_trans hR_sq_ev hR_ev
  have hq_eq :=
    qSDD_rightPlaced_completeAtOutcome_eq ψ P.toSubMeas P.toSubMeas a0
  rw [hq_eq] at hraw
  simpa [Preliminaries.completeAtOutcomeProj_toSubMeas] using hraw

/-- A left-factor SDD estimate controls the loss in bipartite matching mass
against a complete measurement on the right factor. -/
private lemma qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (G : Measurement Outcome ιA) (P : SubMeas Outcome ιA)
    (B : Measurement Outcome ιB) {ε : Error}
    (hclose : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P))
      ε) :
    qBipartiteMatchMass ψ P B.toSubMeas ≥
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas - Real.sqrt ε := by
  have hgap :=
    MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta ψ hψ
      (uniformDistribution Unit) (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      ε hclose
  have hgap' :
      |qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas -
          qBipartiteMatchMass ψ P B.toSubMeas| ≤
        Real.sqrt ε := by
    simpa [avgOver, uniformDistribution, constSubMeasFamily,
      qBipartiteMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
      leftTensor_mul_rightTensor_eq_opTensor] using hgap
  have hdiff :
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas -
          qBipartiteMatchMass ψ P B.toSubMeas ≤
        Real.sqrt ε :=
    (abs_le.mp hgap').2
  linarith

/-- A right-factor SDD estimate controls the loss in bipartite matching mass
against a complete measurement on the left factor. -/
private lemma qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (G : Measurement Outcome ιB)
    (P : SubMeas Outcome ιB) {ε : Error}
    (hclose : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P))
      ε) :
    qBipartiteMatchMass ψ A.toSubMeas P ≥
      qBipartiteMatchMass ψ A.toSubMeas G.toSubMeas - Real.sqrt ε := by
  have hgap :=
    MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta ψ hψ
      (uniformDistribution Unit) (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      ε hclose
  have hgap' :
      |qBipartiteMatchMass ψ A.toSubMeas G.toSubMeas -
          qBipartiteMatchMass ψ A.toSubMeas P| ≤
        Real.sqrt ε := by
    simpa [avgOver, uniformDistribution, constSubMeasFamily,
      qBipartiteMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
      rightTensor_mul_leftTensor_eq_opTensor] using hgap
  have hdiff :
      qBipartiteMatchMass ψ A.toSubMeas G.toSubMeas -
          qBipartiteMatchMass ψ A.toSubMeas P ≤
        Real.sqrt ε :=
    (abs_le.mp hgap').2
  linarith

/-- The bipartite matching mass against a complete right measurement is bounded
by the left total of the other submeasurement. -/
private lemma qBipartiteMatchMass_le_left_total_of_measurement_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas Outcome ιA)
    (B : Measurement Outcome ιB) :
    qBipartiteMatchMass ψ A B.toSubMeas ≤
      ev ψ (leftTensor (ι₂ := ιB) A.total) := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            opTensor_le_leftTensor (ι₂ := ιB)
              (A.outcome_pos a) (Measurement.outcome_le_one B a)
    _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
          rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
          rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
          rw [A.sum_eq_total]

/-- The bipartite matching mass against a complete left measurement is bounded
by the right total of the other submeasurement. -/
private lemma qBipartiteMatchMass_le_right_total_of_measurement_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : Measurement Outcome ιA)
    (B : SubMeas Outcome ιB) :
    qBipartiteMatchMass ψ A.toSubMeas B ≤
      ev ψ (rightTensor (ι₁ := ιA) B.total) := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a : Outcome, ev ψ (rightTensor (ι₁ := ιA) (B.outcome a)) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            calc
              opTensor (A.outcome a) (B.outcome a)
                  ≤ opTensor (1 : MIPStarRE.Quantum.Op ιA) (B.outcome a) :=
                    opTensor_mono_left (Measurement.outcome_le_one A a) (B.outcome_pos a)
              _ = rightTensor (ι₁ := ιA) (B.outcome a) := by
                    simp [rightTensor, opTensor]
    _ = ev ψ (rightTensor (ι₁ := ιA) B.total) := by
          rw [← ev_sum ψ (fun a : Outcome => rightTensor (ι₁ := ιA) (B.outcome a))]
          rw [rightTensor_finset_sum (ι₁ := ιA) Finset.univ B.outcome]
          rw [B.sum_eq_total]

/-- Completing a projective submeasurement on Alice's side can only increase
its bipartite matching mass against a fixed Bob-side submeasurement. -/
private lemma completeAtOutcomeProj_left_matchMass_ge_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (P : ProjSubMeas Outcome ιA)
    (B : SubMeas Outcome ιB) (a0 : Outcome) :
    qBipartiteMatchMass ψ (Preliminaries.completeAtOutcomeProj P a0).toSubMeas B ≥
      qBipartiteMatchMass ψ P.toSubMeas B := by
  classical
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : a = a0
  · subst a
    have hres_nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total :=
      sub_nonneg.mpr P.toSubMeas.total_le_one
    have hextra_nonneg :
        0 ≤ ev ψ (opTensor ((1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total)
          (B.outcome a0)) :=
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg hres_nonneg (B.outcome_pos a0)
    simp [Preliminaries.completeAtOutcome, opTensor_add_left_local, ev_add]
    linarith
  · simp [Preliminaries.completeAtOutcome, ha]

/-- Completing a projective submeasurement on Bob's side can only increase its
bipartite matching mass against a fixed Alice-side submeasurement. -/
private lemma completeAtOutcomeProj_right_matchMass_ge_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas Outcome ιA)
    (P : ProjSubMeas Outcome ιB) (a0 : Outcome) :
    qBipartiteMatchMass ψ A (Preliminaries.completeAtOutcomeProj P a0).toSubMeas ≥
      qBipartiteMatchMass ψ A P.toSubMeas := by
  classical
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : a = a0
  · subst a
    have hres_nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ιB) - P.toSubMeas.total :=
      sub_nonneg.mpr P.toSubMeas.total_le_one
    have hextra_nonneg :
        0 ≤ ev ψ (opTensor (A.outcome a0)
          ((1 : MIPStarRE.Quantum.Op ιB) - P.toSubMeas.total)) :=
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a0) hres_nonneg
    simp [Preliminaries.completeAtOutcome, opTensor_add_right_local, ev_add]
    linarith
  · simp [Preliminaries.completeAtOutcome, ha]

/-- Combine cross consistency and Alice-side orthonormalization closeness into
the completion estimate for the left tensor factor. -/
private lemma completedCloseness_left_of_consistency_and_sdd
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G_A : Measurement Outcome ιA) (G_B : Measurement Outcome ιB)
    (P_A : ProjSubMeas Outcome ιA) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ιB)
          (Preliminaries.completeAtOutcomeProj P_A a0).toSubMeas))
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
  let Q_A := Preliminaries.completeAtOutcomeProj P_A a0
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
      hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hmatch_G :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G_A G_B] at hpre_q
    have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) = 1 :=
      ev_one_of_isNormalized ψ hψ
    linarith
  have hmatch_P :
      qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
    qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous
      ψ hψ G_A P_A.toSubMeas G_B horth
  have hmass_P :
      1 - ev ψ (leftTensor (ι₂ := ιB) P_A.toSubMeas.total) ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    have hmatch_le :=
      qBipartiteMatchMass_le_left_total_of_measurement_heterogeneous
        ψ P_A.toSubMeas G_B
    linarith
  have hPP_q : qSDD ψ (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas)
      (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas) ≤
      ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    simpa [Q_A] using
      qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap ψ hψ P_A a0 hmass_P
  have hGP_q :
      qSDD ψ (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas) ≤
        MakingMeasurementsProjective.orthonormalizationError ζ := by
    simpa [Preliminaries.constFamily_sdd_unit] using horth.squaredDistanceBound
  constructor
  rw [Preliminaries.constFamily_sdd_unit]
  calc
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
        (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas)
      ≤ 2 * (qSDD ψ (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
            (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas) +
          qSDD ψ (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas)
            (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas)) := by
            exact Preliminaries.questionSDD_triangle ψ
              (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
              (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas)
              (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas)
    _ ≤ 2 * (MakingMeasurementsProjective.orthonormalizationError ζ +
          (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ))) := by
          gcongr
    _ = 2 * MakingMeasurementsProjective.orthonormalizationError ζ +
          2 * ζ + 2 * Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
          ring
    _ ≤ MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ := by
          have hsqrt_nonneg :
              0 ≤ Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
            Real.sqrt_nonneg _
          unfold MakingMeasurementsProjective.orthonormalizeAndCompleteError
          linarith [hζ0, hsqrt_nonneg]

/-- Bob/right-factor counterpart of
`completedCloseness_left_of_consistency_and_sdd`. -/
private lemma completedCloseness_right_of_consistency_and_sdd
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G_A : Measurement Outcome ιA) (G_B : Measurement Outcome ιB)
    (P_B : ProjSubMeas Outcome ιB) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ιA)
          (Preliminaries.completeAtOutcomeProj P_B a0).toSubMeas))
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
  let Q_B := Preliminaries.completeAtOutcomeProj P_B a0
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
      hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hmatch_G :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G_A G_B] at hpre_q
    have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) = 1 :=
      ev_one_of_isNormalized ψ hψ
    linarith
  have hmatch_P :
      qBipartiteMatchMass ψ G_A.toSubMeas P_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
    qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous
      ψ hψ G_A G_B P_B.toSubMeas horth
  have hmass_P :
      1 - ev ψ (rightTensor (ι₁ := ιA) P_B.toSubMeas.total) ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    have hmatch_le :=
      qBipartiteMatchMass_le_right_total_of_measurement_heterogeneous
        ψ G_A P_B.toSubMeas
    linarith
  have hPP_q : qSDD ψ (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas)
      (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas) ≤
      ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    simpa [Q_B] using
      qSDD_completeAtOutcomeProj_rightPlaced_le_of_total_gap ψ hψ P_B a0 hmass_P
  have hGP_q :
      qSDD ψ (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
          (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas) ≤
        MakingMeasurementsProjective.orthonormalizationError ζ := by
    simpa [Preliminaries.constFamily_sdd_unit] using horth.squaredDistanceBound
  constructor
  rw [Preliminaries.constFamily_sdd_unit]
  calc
    qSDD ψ (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)
      ≤ 2 * (qSDD ψ (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
            (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas) +
          qSDD ψ (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas)
            (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)) := by
            exact Preliminaries.questionSDD_triangle ψ
              (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
              (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas)
              (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)
    _ ≤ 2 * (MakingMeasurementsProjective.orthonormalizationError ζ +
          (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ))) := by
          gcongr
    _ = 2 * MakingMeasurementsProjective.orthonormalizationError ζ +
          2 * ζ + 2 * Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
          ring
    _ ≤ MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ := by
          have hsqrt_nonneg :
              0 ≤ Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
            Real.sqrt_nonneg _
          unfold MakingMeasurementsProjective.orthonormalizeAndCompleteError
          linarith [hζ0, hsqrt_nonneg]

/-- Alice-side repaired line-169 consistency after completing the projective
submeasurement.

This proves the heterogeneous analogue of the paper's
`Q^A_g \otimes I \simeq I \otimes G^B_g` step, with the checked repaired loss
`ζ + sqrt (orthonormalizationError ζ)`. -/
private lemma completedLeftConsistency_of_consistency_and_sdd
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G_A : Measurement Outcome ιA) (G_B : Measurement Outcome ιB)
    (P_A : ProjSubMeas Outcome ιA) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj P_A a0).toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ)) := by
  let Q_A := Preliminaries.completeAtOutcomeProj P_A a0
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) = 1 :=
    ev_one_of_isNormalized ψ hψ
  have hmatch_G :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G_A G_B] at hpre_q
    linarith
  have hmatch_P :
      qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
    qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous
      ψ hψ G_A P_A.toSubMeas G_B horth
  have hmatch_Q :
      qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    calc
      qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas
          ≥ qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas :=
            completeAtOutcomeProj_left_matchMass_ge_heterogeneous
              ψ P_A G_B.toSubMeas a0
      _ ≥ qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := hmatch_P
  have hmatch_Q' :
      1 - qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    linarith
  have hdefect_Q :
      qBipartiteConsDefect ψ Q_A.toSubMeas G_B.toSubMeas ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas) ≤
          ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
      exact max_le_iff.mpr
        ⟨add_nonneg hζ0 (Real.sqrt_nonneg _), by simpa [hone] using hmatch_Q'⟩
    simpa [qBipartiteConsDefect, qBipartiteMatchMass, Q_A.total_eq_one,
      G_B.total_eq_one, opTensor] using hmax
  constructor
  simpa [Q_A, bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefect_Q

/-- Bob-side repaired line-169 consistency after completing the projective
submeasurement.

This is the heterogeneous analogue of the role-reversed line-169 relation
`G^A_g \otimes I \simeq I \otimes Q^B_g`. -/
private lemma completedRightConsistency_of_consistency_and_sdd
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G_A : Measurement Outcome ιA) (G_B : Measurement Outcome ιB)
    (P_B : ProjSubMeas Outcome ιB) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj P_B a0).toSubMeas)
      (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ)) := by
  let Q_B := Preliminaries.completeAtOutcomeProj P_B a0
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) = 1 :=
    ev_one_of_isNormalized ψ hψ
  have hmatch_G :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G_A G_B] at hpre_q
    linarith
  have hmatch_P :
      qBipartiteMatchMass ψ G_A.toSubMeas P_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
    qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous
      ψ hψ G_A G_B P_B.toSubMeas horth
  have hmatch_Q :
      qBipartiteMatchMass ψ G_A.toSubMeas Q_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    calc
      qBipartiteMatchMass ψ G_A.toSubMeas Q_B.toSubMeas
          ≥ qBipartiteMatchMass ψ G_A.toSubMeas P_B.toSubMeas :=
            completeAtOutcomeProj_right_matchMass_ge_heterogeneous
              ψ G_A.toSubMeas P_B a0
      _ ≥ qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := hmatch_P
  have hmatch_Q' :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas Q_B.toSubMeas ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    linarith
  have hdefect_Q :
      qBipartiteConsDefect ψ G_A.toSubMeas Q_B.toSubMeas ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ G_A.toSubMeas Q_B.toSubMeas) ≤
          ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
      exact max_le_iff.mpr
        ⟨add_nonneg hζ0 (Real.sqrt_nonneg _), by simpa [hone] using hmatch_Q'⟩
    simpa [qBipartiteConsDefect, qBipartiteMatchMass, G_A.total_eq_one,
      Q_B.total_eq_one, opTensor] using hmax
  constructor
  simpa [Q_B, bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefect_Q







end ProjStrat

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Source-Boundary Role-Register Handoff: Completion Lemmas

This module contains the completion and line-169 transport lemmas for the
two-space source role-register route.
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
    (G_A : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA)
    (G_B : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB)
    (P_A : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA)
    (P_B : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB)
    (ζ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hfull : _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_B.toSubMeas) ζ)
    (hleft :
      _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError ζ))
    (hright :
      _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError ζ)) :
    ∃ Q_A : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA,
      ∃ Q_B : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB,
        _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) ∧
        _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) ∧
        _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Q_A.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_B.toSubMeas)
          (ζ + Real.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError ζ)) ∧
        _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_A.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Q_B.toSubMeas)
          (ζ + Real.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError ζ)) := by
  let a0 : _root_.LIDT.MIPStarRE.LDT.Polynomial params :=
    { poly := 0
      lowIndividualDegree := fun i =>
        (MvPolynomial.degreeOf_zero i).trans_le (Nat.zero_le _) }
  let Q_A := _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj P_A a0
  let Q_B := _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj P_B a0
  have hleftComplete :
      _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
    simpa [Q_A] using
      completedCloseness_left_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_A a0 hfull hleft
  have hrightComplete :
      _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
    simpa [Q_B] using
      completedCloseness_right_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_B a0 hfull hright
  have hleftLine169 :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Q_A.toSubMeas)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_B.toSubMeas)
        (ζ + Real.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError ζ)) := by
    simpa [Q_A] using
      completedLeftConsistency_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_A a0 hfull hleft
  have hrightLine169 :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily G_A.toSubMeas)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Q_B.toSubMeas)
        (ζ + Real.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError ζ)) := by
    simpa [Q_B] using
      completedRightConsistency_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_B a0 hfull hright
  exact ⟨Q_A, Q_B, hleftComplete, hrightComplete, hleftLine169, hrightLine169⟩
