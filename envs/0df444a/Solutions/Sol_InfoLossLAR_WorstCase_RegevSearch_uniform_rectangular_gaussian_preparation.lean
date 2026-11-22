-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.uniform_rectangular_gaussian_preparation
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:20:22.230412+00:00
-- url     : https://prove2.me/submissions/50aa01de-3f86-486a-83c7-333893adac41

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_CoherentGaussianTickets
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_01
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_07
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_08
import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_02
import Definitions.Def_InfoLossLAR_NativeCompactPrefix_01
import Definitions.Def_InfoLossLAR_NativeSparsePrefix_01
import Definitions.Def_InfoLossLAR_NativeSparsePrefix_02
import Definitions.Def_InfoLossLAR_NativeSupplement_01
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
import Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding
import Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
import Definitions.Def_InfoLossLAR_ReciprocallyScaledGaussianSource
import Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD
import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
import Definitions.Def_InfoLossLAR_RuntimeBundle_01
import Definitions.Def_InfoLossLAR_RuntimeBundle_02
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_LARLLL_CurrentData
import Definitions.Def_LARLLL_KernelTransport
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalStringListEncoding
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Mathlib
import Theorems.Thm_AFT_RationalNumerics_HeightBound_inv
import Theorems.Thm_CliffordTApprox_Ancilla_main_result
import Theorems.Thm_InfoLossLAR_WorstCase_RationalInverse_Native_current_correct
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_coherent_gaussian_ticket_preparation
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothing_le_short_independent
import Theorems.Thm_RegevLWE_GaussConv_claim_3_8
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_RegevLWE_GaussConv_smoothing_remark
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
set_option Elab.async true
set_option cleanup.letToHave false

set_option linter.all false

namespace AFT
end AFT

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace CurrentAFT.BinaryMassLiftFormula.Leaf.input
end CurrentAFT.BinaryMassLiftFormula.Leaf.input

namespace CurrentAFT.CurrentPhysicalNumbering.split
end CurrentAFT.CurrentPhysicalNumbering.split

namespace CurrentAFT.PublicBitTapes.split
end CurrentAFT.PublicBitTapes.split

namespace GridReadout
end GridReadout

namespace GridReadout.Axis
end GridReadout.Axis

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.BooleanExpr.input
end InfoLossLAR.WorstCase.BooleanExpr.input

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute
end InfoLossLAR.WorstCase.CoherentComputeUncompute

namespace InfoLossLAR.WorstCase.CoherentControlledSwap
end InfoLossLAR.WorstCase.CoherentControlledSwap

namespace InfoLossLAR.WorstCase.CoherentDecoder
end InfoLossLAR.WorstCase.CoherentDecoder

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative
end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

namespace InfoLossLAR.WorstCase.CoherentInjection
end InfoLossLAR.WorstCase.CoherentInjection

namespace InfoLossLAR.WorstCase.CoherentProjection
end InfoLossLAR.WorstCase.CoherentProjection

namespace InfoLossLAR.WorstCase.CoherentRejection
end InfoLossLAR.WorstCase.CoherentRejection

namespace InfoLossLAR.WorstCase.CoherentWeightedPreparation
end InfoLossLAR.WorstCase.CoherentWeightedPreparation

namespace InfoLossLAR.WorstCase.ControlledLetterPlan
end InfoLossLAR.WorstCase.ControlledLetterPlan

namespace InfoLossLAR.WorstCase.ControlledNativeCode
end InfoLossLAR.WorstCase.ControlledNativeCode

namespace InfoLossLAR.WorstCase.ControlledNativeGates
end InfoLossLAR.WorstCase.ControlledNativeGates

namespace InfoLossLAR.WorstCase.ControlledRelocation
end InfoLossLAR.WorstCase.ControlledRelocation

namespace InfoLossLAR.WorstCase.FiniteGateNative
end InfoLossLAR.WorstCase.FiniteGateNative

namespace InfoLossLAR.WorstCase.FiniteGateNativeEnumeration
end InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

namespace InfoLossLAR.WorstCase.FiniteGateTransport
end InfoLossLAR.WorstCase.FiniteGateTransport

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport
end InfoLossLAR.WorstCase.GaussianLatticeTransport

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
end InfoLossLAR.WorstCase.GaussianPoissonSeries

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.rationalCode
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.rationalCode

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

namespace InfoLossLAR.WorstCase.NativeDualQuotient
end InfoLossLAR.WorstCase.NativeDualQuotient

namespace InfoLossLAR.WorstCase.NativeDualQuotient.Codec.input
end InfoLossLAR.WorstCase.NativeDualQuotient.Codec.input

namespace InfoLossLAR.WorstCase.NativeLLL.input
end InfoLossLAR.WorstCase.NativeLLL.input

namespace InfoLossLAR.WorstCase.NativePaddedWords
end InfoLossLAR.WorstCase.NativePaddedWords

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile
end InfoLossLAR.WorstCase.NativeQFTPlanCompile

namespace InfoLossLAR.WorstCase.NativeTicketInteger
end InfoLossLAR.WorstCase.NativeTicketInteger

namespace InfoLossLAR.WorstCase.NativeTicketInteger.input
end InfoLossLAR.WorstCase.NativeTicketInteger.input

namespace InfoLossLAR.WorstCase.NativeTicketInteger.split
end InfoLossLAR.WorstCase.NativeTicketInteger.split

namespace InfoLossLAR.WorstCase.NativeWordCoherent
end InfoLossLAR.WorstCase.NativeWordCoherent

namespace InfoLossLAR.WorstCase.NativeWordControls
end InfoLossLAR.WorstCase.NativeWordControls

namespace InfoLossLAR.WorstCase.NativeWordDescription
end InfoLossLAR.WorstCase.NativeWordDescription

namespace InfoLossLAR.WorstCase.NativeWordLayout
end InfoLossLAR.WorstCase.NativeWordLayout

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

namespace InfoLossLAR.WorstCase.RationalInverse
end InfoLossLAR.WorstCase.RationalInverse

namespace InfoLossLAR.WorstCase.RectangularSource.Arena
end InfoLossLAR.WorstCase.RectangularSource.Arena

namespace InfoLossLAR.WorstCase.RectangularSource.Binary
end InfoLossLAR.WorstCase.RectangularSource.Binary

namespace InfoLossLAR.WorstCase.RectangularSource.Cell.input
end InfoLossLAR.WorstCase.RectangularSource.Cell.input

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires
end InfoLossLAR.WorstCase.RectangularSource.FineWires

namespace InfoLossLAR.WorstCase.RectangularSource.Public
end InfoLossLAR.WorstCase.RectangularSource.Public

namespace InfoLossLAR.WorstCase.RectangularSource.Settings
end InfoLossLAR.WorstCase.RectangularSource.Settings

namespace InfoLossLAR.WorstCase.RegevSearch
end InfoLossLAR.WorstCase.RegevSearch

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer.split
end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer.split

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.input
end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.input

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec
end InfoLossLAR.WorstCase.RegevSearch.FineCodec

namespace InfoLossLAR.WorstCase.RegevSearch.FineGridDecoding.input
end InfoLossLAR.WorstCase.RegevSearch.FineGridDecoding.input

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder
end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier
end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid
end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

namespace InfoLossLAR.WorstCase.RegevSearch.StageRegisters
end InfoLossLAR.WorstCase.RegevSearch.StageRegisters

namespace InfoLossLAR.WorstCase.TM2Boolean
end InfoLossLAR.WorstCase.TM2Boolean

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
end InfoLossLAR.WorstCase.TM2Boolean.RPN

namespace InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT
end InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT

namespace InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h1076ff82614707e5.AFT
end InfoLossLARNativeSupplements.h1076ff82614707e5.AFT

namespace InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT
end InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT

namespace InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT
end InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT

namespace InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT
end InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT

namespace InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT
end InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT

namespace InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT
end InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT

namespace InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT
end InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT

namespace InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT
end InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT

namespace InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT
end InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT

namespace InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT
end InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT

namespace InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT
end InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT

namespace InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT
end InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT

namespace InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT
end InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT

namespace InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT
end InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT

namespace InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic
end InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic

namespace InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT
end InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT

namespace InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT
end InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT

namespace InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT
end InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT

namespace InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h90032182500c2e77.AFT
end InfoLossLARNativeSupplements.h90032182500c2e77.AFT

namespace InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT
end InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT

namespace InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.ha562531658b7642e.AFT
end InfoLossLARNativeSupplements.ha562531658b7642e.AFT

namespace InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.had468f01f375d910.AFT
end InfoLossLARNativeSupplements.had468f01f375d910.AFT

namespace InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics
end InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT
end InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT

namespace InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT
end InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT

namespace InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT
end InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT

namespace InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic
end InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic

namespace InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT
end InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT

namespace InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT
end InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT

namespace InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT
end InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT

namespace InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT
end InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT

namespace InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics
end InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT
end InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT

namespace InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT
end InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT

namespace InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT
end InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT

namespace Integration9_9
end Integration9_9

namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding

namespace Integration9_9.LARPlatformEncoding.readB
end Integration9_9.LARPlatformEncoding.readB

namespace Integration9_9.LARPlatformEncoding.readBinaryList_append_mapped
end Integration9_9.LARPlatformEncoding.readBinaryList_append_mapped

namespace Integration9_9.LARPlatformEncoding.readS
end Integration9_9.LARPlatformEncoding.readS

namespace Integration9_9.LARPlatformEncoding.serializeBinaryWords
end Integration9_9.LARPlatformEncoding.serializeBinaryWords

namespace Integration9_9.LARRankOneMachine
end Integration9_9.LARRankOneMachine

namespace Integration9_9.TM2AdditionFrontend.Data.input
end Integration9_9.TM2AdditionFrontend.Data.input

namespace Integration9_9.TM2AdditionFrontend.Stack.input
end Integration9_9.TM2AdditionFrontend.Stack.input

namespace Integration9_9.TM2BinaryAddition.Stack.input
end Integration9_9.TM2BinaryAddition.Stack.input

namespace Integration9_9.TM2BinaryComparison.Stack.input
end Integration9_9.TM2BinaryComparison.Stack.input

namespace Integration9_9.TM2Canonical.Stack.input
end Integration9_9.TM2Canonical.Stack.input

namespace Integration9_9.TM2DynamicIntegerEncoding.Stack.input
end Integration9_9.TM2DynamicIntegerEncoding.Stack.input

namespace Integration9_9.TM2NativeAffineEmitter
end Integration9_9.TM2NativeAffineEmitter

namespace Integration9_9.TM2NativeAffineEncoding
end Integration9_9.TM2NativeAffineEncoding

namespace Integration9_9.TM2NativeBodyKernel
end Integration9_9.TM2NativeBodyKernel

namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2NativeGaussian
end Integration9_9.TM2NativeGaussian

namespace Integration9_9.TM2NativeRootMetadata.input
end Integration9_9.TM2NativeRootMetadata.input

namespace Integration9_9.TM2NativeSelectedResponse.input
end Integration9_9.TM2NativeSelectedResponse.input

namespace Integration9_9.TM2OutputEncoding.Stack.input
end Integration9_9.TM2OutputEncoding.Stack.input

namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength

namespace Integration9_9.TM2PairUnframe.Data.input
end Integration9_9.TM2PairUnframe.Data.input

namespace Integration9_9.TM2PairUnframe.Stack.input
end Integration9_9.TM2PairUnframe.Stack.input

namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization

namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget

namespace Integration9_9.TM2StockThread.Buffer.input
end Integration9_9.TM2StockThread.Buffer.input

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

namespace OAI.MetricKMedian.Binary.Transducer.Key.input
end OAI.MetricKMedian.Binary.Transducer.Key.input

namespace P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.PiPoissonSummation.SchwartzMap
end P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.PiPoissonSummation.SchwartzMap

namespace P2MW.S_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral.PiPoissonSummation.SchwartzMap
end P2MW.S_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral.PiPoissonSummation.SchwartzMap

namespace QAlgorithms
end QAlgorithms

namespace QAlgorithms.Complexity
end QAlgorithms.Complexity

namespace QAlgorithms.Papers.Independent.Renew46.P12
end QAlgorithms.Papers.Independent.Renew46.P12

namespace QMCNumericRuntime
end QMCNumericRuntime

namespace RegevLWE.GaussConv
end RegevLWE.GaussConv

namespace SchwartzMap
end SchwartzMap

namespace SharedPoolCoherence
end SharedPoolCoherence

namespace Turing
end Turing

/- Helper module AFT.GaussianConvolution. -/
section P2MDyadicModule0

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable def theta (width center : ℝ) : ℝ :=
  ∑' z : ℤ, shiftedWeight width center z

noncomputable def thetaFourier (width center : ℝ) (z : ℤ) : ℂ :=
  Complex.exp (-Real.pi * (width : ℂ) ^ 2 * (z : ℂ) ^ 2 +
    2 * Real.pi * Complex.I * center * z)

/-- Poisson summation for an arbitrarily shifted integer lattice. -/
theorem theta_poisson (width center : ℝ) (hw : 0 < width) :
    (theta width center : ℂ) / width = ∑' z : ℤ, thetaFourier width center z := by
  have hs : ((width : ℂ) ^ 2) ^ (1 / 2 : ℂ) = width := by
    have hr : (width ^ 2) ^ (1 / 2 : ℝ) = width := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hw.le]
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    rw [Complex.ofReal_cpow (sq_nonneg width)] at hc
    simpa using hc
  have hp := Complex.tsum_exp_neg_quadratic
    (a := (width : ℂ) ^ 2) (by simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos hw)
    (Complex.I * center)
  rw [hs] at hp
  have hleft : (∑' z : ℤ, Complex.exp (-Real.pi * (width : ℂ) ^ 2 * z ^ 2 +
      2 * Real.pi * (Complex.I * center) * z)) =
      ∑' z : ℤ, thetaFourier width center z := by
    apply tsum_congr
    intro z
    congr 1
    ring
  have hright : (∑' z : ℤ, Complex.exp
      (-Real.pi / (width : ℂ) ^ 2 * (z + Complex.I * (Complex.I * center)) ^ 2)) =
      (theta width center : ℂ) := by
    rw [theta, Complex.ofReal_tsum]
    apply tsum_congr
    intro z
    rw [shiftedWeight, Complex.ofReal_exp]
    congr 1
    push_cast
    have hI : Complex.I * (Complex.I * (center : ℂ)) = -(center : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [hI]
    ring
  rw [hleft, hright] at hp
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hp.symm

theorem thetaFourier_norm (width center : ℝ) (hw : 0 < width) (z : ℤ) :
    ‖thetaFourier width center z‖ = weight (1 / width) z := by
  rw [thetaFourier, Complex.norm_exp]
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re ]
  unfold weight
  congr 1
  field_simp

theorem summable_thetaFourier (width center : ℝ) (hw : 0 < width) :
    Summable (thetaFourier width center) := by
  apply Summable.of_norm
  simpa only [thetaFourier_norm width center hw] using summable_weight (1 / width) (by positivity)

/-- The nonzero Fourier modes control the entire relative error, uniformly
in the center, by the zero-centered dual Gaussian mass. -/
theorem theta_relative_error (width center : ℝ) (hw : 0 < width) :
    |theta width center / width - 1| ≤ realNormalizer (1 / width) - 1 := by
  let f := thetaFourier width center
  have hf := summable_thetaFourier width center hw
  have hnorm : Summable (fun z : ℤ => ‖if z = 0 then (0 : ℂ) else f z‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (summable_weight (1 / width) (by positivity))
    intro z
    split_ifs
    · exact (show ‖(0 : ℂ)‖ = 0 by norm_num).symm ▸ (weight_pos (1 / width) z).le
    · exact le_of_eq (thetaFourier_norm width center hw z)
  have hzero : f 0 = 1 := by simp [f, thetaFourier]
  have heq := hf.tsum_eq_add_tsum_ite (0 : ℤ)
  change (∑' z : ℤ, f z) = f 0 + ∑' z : ℤ, if z = 0 then 0 else f z at heq
  rw [hzero] at heq
  have hdual := (summable_weight (1 / width) (by positivity)).tsum_eq_add_tsum_ite (0 : ℤ)
  change realNormalizer (1 / width) = weight (1 / width) 0 + _ at hdual
  have hwzero : weight (1 / width) 0 = 1 := by simp [weight]
  rw [hwzero] at hdual
  have hnormsum : (∑' z : ℤ, ‖if z = 0 then (0 : ℂ) else f z‖) =
      realNormalizer (1 / width) - 1 := by
    have heq' : (∑' z : ℤ, ‖if z = 0 then (0 : ℂ) else f z‖) =
        ∑' z : ℤ, if z = 0 then 0 else weight (1 / width) z := by
      apply tsum_congr
      intro z
      split_ifs
      · exact norm_zero
      · exact thetaFourier_norm width center hw z
    rw [heq']
    linarith
  have hcomplex : ((theta width center / width - 1 : ℝ) : ℂ) =
      ∑' z : ℤ, if z = 0 then 0 else f z := by
    push_cast
    rw [theta_poisson width center hw]
    change (∑' z : ℤ, f z) - 1 = _
    rw [heq]
    ring
  have h := norm_tsum_le_tsum_norm hnorm
  rw [← hcomplex, Complex.norm_real, Real.norm_eq_abs, hnormsum] at h
  exact h

/-- Explicit exponentially small theta error. -/
noncomputable def thetaError (width : ℝ) : ℝ :=
  2 * (Real.exp (-Real.pi * width ^ 2) / (1 - Real.exp (-Real.pi * width ^ 2)))

theorem thetaError_nonneg (width : ℝ) (hw : 0 < width) : 0 ≤ thetaError width := by
  have h : Real.exp (-Real.pi * width ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hw])
  exact mul_nonneg (by norm_num) (div_nonneg (Real.exp_pos _).le (by linarith))

theorem theta_relative_error_exp (width center : ℝ) (hw : 0 < width) :
    |theta width center / width - 1| ≤ thetaError width := by
  apply (theta_relative_error width center hw).trans
  have h := realNormalizer_le_geometric (1 / width) (by positivity)
  have heq : Real.pi / (1 / width) ^ 2 = Real.pi * width ^ 2 := by field_simp
  rw [heq, ← neg_mul] at h
  unfold thetaError
  linarith

theorem summable_shiftedWeight (width center : ℝ) (hw : 0 < width) :
    Summable (shiftedWeight width center) := by
  let coefficient := Real.pi / width ^ 2
  have hc : 0 < coefficient := div_pos Real.pi_pos (sq_pos_of_pos hw)
  have hw' : 0 < Real.sqrt 2 * width := by positivity
  apply Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) _
    ((summable_weight (Real.sqrt 2 * width) hw').mul_left
      (Real.exp (coefficient * center ^ 2)))
  intro z
  unfold weight
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq := mul_nonneg hc.le (sq_nonneg ((z : ℝ) - 2 * center))
  change -coefficient * ((z : ℝ) - center) ^ 2 ≤ _
  have heq : coefficient * center ^ 2 + -(Real.pi / (2 * width ^ 2)) * (z : ℝ) ^ 2 =
      coefficient * center ^ 2 - coefficient * (z : ℝ) ^ 2 / 2 := by
    dsimp [coefficient]
    ring
  rw [heq]
  nlinarith

theorem theta_pos (width center : ℝ) (hw : 0 < width) : 0 < theta width center := by
  have hzero := (summable_shiftedWeight width center hw).le_tsum (0 : ℤ)
    (fun z _ => (Real.exp_pos _).le)
  change shiftedWeight width center 0 ≤ theta width center at hzero
  exact (show 0 < shiftedWeight width center 0 by
    unfold shiftedWeight
    positivity).trans_le hzero

/-- The theta error decreases with the Gaussian width. -/
theorem thetaError_antitone (left right : ℝ) (hl : 0 < left) (h : left ≤ right) :
    thetaError right ≤ thetaError left := by
  have hr : 0 < right := hl.trans_le h
  have hl1 : Real.exp (-Real.pi * left ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hl])
  have hr1 : Real.exp (-Real.pi * right ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hr])
  have hsq : left ^ 2 ≤ right ^ 2 := (sq_le_sq₀ hl.le hr.le).mpr h
  have he : Real.exp (-Real.pi * right ^ 2) ≤ Real.exp (-Real.pi * left ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  unfold thetaError
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - Real.exp (-Real.pi * right ^ 2))
    (by linarith : 0 < 1 - Real.exp (-Real.pi * left ^ 2))).mpr
  nlinarith

theorem thetaError_le_four_exp (width : ℝ) (hw : 1 ≤ width) :
    thetaError width ≤ 4 * Real.exp (-Real.pi * width ^ 2) := by
  have hw0 : 0 < width := zero_lt_one.trans_le hw
  have hcoef : 1 ≤ Real.pi * width ^ 2 := by
    have hsq : 1 ≤ width ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have he : 2 ≤ Real.exp (Real.pi * width ^ 2) :=
    (by linarith : 2 ≤ Real.pi * width ^ 2 + 1).trans (Real.add_one_le_exp _)
  have hhalf : Real.exp (-Real.pi * width ^ 2) ≤ 1 / 2 := by
    rw [neg_mul, Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by simpa using he)
  have hden : 0 < 1 - Real.exp (-Real.pi * width ^ 2) := by linarith
  unfold thetaError
  have hquot : Real.exp (-Real.pi * width ^ 2) /
      (1 - Real.exp (-Real.pi * width ^ 2)) ≤ 2 * Real.exp (-Real.pi * width ^ 2) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.exp_pos (-Real.pi * width ^ 2)]
  linarith

end AFT.GaussianSource

end P2MDyadicModule0

/- Helper module AFT.CenteredGaussianProgram. -/
section P2MDyadicModule1

namespace AFT.RationalNumerics

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem centeredGaussianAnchor_bounds (center : ℚ) :
    (centeredGaussianAnchor center : ℝ)≤(center : ℝ) ∧
      (center : ℝ)<(centeredGaussianAnchor center : ℝ)+1 := by
  constructor
  · exact_mod_cast (Int.floor_le center)
  · exact_mod_cast (Int.lt_floor_add_one center)

end

end AFT.RationalNumerics

end P2MDyadicModule1

/- Helper module AFT.RationalHeight. -/
section P2MDyadicModule2

namespace AFT.RationalNumerics

open scoped BigOperators

namespace HeightBound

private theorem reduced_le (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (Rat.divInt num (den : ℤ)).num.natAbs ≤ num.natAbs ∧ (Rat.divInt num (den : ℤ)).den ≤ den := by
  constructor
  · by_cases hn : num=0
    · simp [hn]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd num (by exact_mod_cast hd.ne')))
  · exact Nat.le_of_dvd hd (by exact_mod_cast Rat.den_dvd num (den : ℤ))

theorem of_int {value : ℤ} {bits : ℕ} (h : value.natAbs ≤ 2^bits) : HeightBound (value : ℚ) bits := by
  constructor
  · simpa using h
  · simpa using (Nat.one_le_pow bits 2 (by decide))

theorem mul {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first*second) (firstBits+secondBits) := by
  have heq : first*second=Rat.divInt (first.num*second.num) (first.den*second.den : ℤ) := by
    calc
      _ = Rat.divInt first.num first.den * Rat.divInt second.num second.den := by rw [Rat.num_divInt_den,Rat.num_divInt_den]
      _ = _ := Rat.divInt_mul_divInt _ _
  have hr := reduced_le (first.num*second.num) (first.den*second.den)
    (Nat.mul_pos first.den_pos second.den_pos)
  rw [Nat.cast_mul,← heq] at hr
  simp only [Int.natAbs_mul] at hr
  rw [HeightBound,pow_add]
  exact ⟨hr.1.trans (Nat.mul_le_mul hf.1 hs.1),hr.2.trans (Nat.mul_le_mul hf.2 hs.2)⟩

theorem div {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first/second) (firstBits+secondBits) := by
  simpa only [div_eq_mul_inv] using hf.mul hs.inv

end HeightBound

end AFT.RationalNumerics

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeWireRelocation. -/
section P2MDyadicModule3

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity

open scoped BigOperators

abbrev OutsideBits {k n : ℕ} (w : Fin k ↪ Fin n) :=
  {a : Fin n // a ∉ Set.range w} → Bool

/-- The selected wires and all remaining wires, with no restriction on their state. -/
noncomputable def wireBitsEquiv {k n : ℕ} (w : Fin k ↪ Fin n) :
    Bits n ≃ Bits k × OutsideBits w where
  toFun y := (fun i => y (w i), fun i => y i)
  invFun p a := if h : a ∈ Set.range w then
    p.1 ((Equiv.ofInjective w w.injective).symm ⟨a,h⟩) else p.2 ⟨a,h⟩
  left_inv y := by
    funext a
    dsimp
    split_ifs with h
    · exact congrArg y (congrArg Subtype.val ((Equiv.ofInjective w w.injective).apply_symm_apply ⟨a,h⟩))
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      dsimp
      simp only [dif_pos (Set.mem_range_self i),Equiv.ofInjective_symm_apply]
    · funext i
      dsimp
      rw [dif_neg i.property]

noncomputable def splitState {k n : ℕ} (w : Fin k ↪ Fin n) (ψ : QState n) :
    Bits k × OutsideBits w → ℂ := fun p => ψ ((wireBitsEquiv w).symm p)

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeInverseCircuit. -/
section P2MDyadicModule4

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-- Exact left inverse for the gate sequence, with every ancillary amplitude preserved. -/
theorem inverseGates_left {n : ℕ} (gates : List (Instr n)) (ψ : QState n) :
    runLayer (inverseGates gates) (runLayer gates ψ) = ψ := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g rest ih =>
    rw [inverseGates_cons, runLayer_append]
    change runLayer (inverseInstr g)
      (runLayer (inverseGates rest) (runLayer rest (g.apply ψ))) = ψ
    rw [ih, inverseInstr_left]

theorem runLayered_singletons {n : ℕ} (gates : List (Instr n)) (ψ : QState n) :
    runLayered (gates.map (fun g => [g])) ψ = runLayer gates ψ := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g rest ih =>
    change runLayered (rest.map (fun g => [g])) (g.apply ψ) =
      runLayer rest (g.apply ψ)
    exact ih _

theorem runLayered_flatten {n : ℕ} (circuit : Layered n) (ψ : QState n) :
    runLayered circuit ψ = runLayer circuit.flatten ψ := by
  induction circuit generalizing ψ with
  | nil => rfl
  | cons layer rest ih =>
    change runLayered rest (runLayer layer ψ) = runLayer (layer ++ rest.flatten) ψ
    rw [runLayer_append, ih]

theorem inverseCircuit_left {n : ℕ} (circuit : Layered n) (ψ : QState n) :
    runLayered (inverseCircuit circuit) (runLayered circuit ψ) = ψ := by
  rw [inverseCircuit, runLayered_singletons, runLayered_flatten, inverseGates_left]

end InfoLossLAR.WorstCase

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeToffoli. -/
section P2MDyadicModule5

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

private theorem phase_composition {N : ℕ} (f g : QState N → QState N)
    (a b : Bits N → ℂ)
    (hf : ∀ φ x, f φ x = a x * φ x) (hg : ∀ φ x, g φ x = b x * φ x)
    (φ : QState N) (x : Bits N) : g (f φ) x = b x * a x * φ x := by
  rw [hg, hf, mul_assoc]

private theorem cnot_conj_phase_map {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N)
    (F : QState N → QState N) (a : Bits N → ℂ)
    (hF : ∀ φ x, F φ x = a x * φ x) :
    cnotState i j hij (F (cnotState i j hij ψ)) =
      fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  funext x
  simp only [cnotState, hF, Function.update_self, Function.update_of_ne hij, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Function.update_idem, Function.update_eq_self]

private theorem apply1_tMat_eq_phase {N : ℕ} (i : Fin N) (ψ : QState N) :
    apply1 tMat i ψ = fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  funext x
  simp [apply1, tMat]

private theorem inv_sqrt_two_mul_self :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `shiTof_Ph F a`: `F` acts as multiplication by the diagonal phase `a`. -/
private abbrev shiTof_Ph {N : ℕ} (F : QState N → QState N) (a : Bits N → ℂ) : Prop :=
  ∀ (φ : QState N) (x : Bits N), F φ x = a x * φ x

private lemma shiTof_Ph_comp {N : ℕ} {f g : QState N → QState N} {a b : Bits N → ℂ}
    (hf : shiTof_Ph f a) (hg : shiTof_Ph g b) :
    shiTof_Ph (fun ψ => g (f ψ)) (fun x => b x * a x) := by
  intro ψ x
  exact phase_composition f g a b hf hg ψ x

private lemma shiTof_Ph_conj {N : ℕ} {F : QState N → QState N} {a : Bits N → ℂ}
    (i j : Fin N) (hij : i ≠ j) (hF : shiTof_Ph F a) :
    shiTof_Ph (fun ψ => cnotState i j hij (F (cnotState i j hij ψ)))
      (fun x => a (Function.update x j (xor (x j) (x i)))) := by
  intro ψ x
  exact congrFun (cnot_conj_phase_map i j hij ψ F a hF) x

private lemma shiTof_Ph_t {N : ℕ} (i : Fin N) :
    shiTof_Ph (apply1 tMat i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  simp only [apply1_tMat_eq_phase]

/-- `T ^ 7` on one wire, as seven `T` gates. -/
private noncomputable def shiTof_T7 {N : ℕ} (i : Fin N) (ψ : QState N) : QState N :=
  apply1 tMat i (apply1 tMat i (apply1 tMat i (apply1 tMat i
    (apply1 tMat i (apply1 tMat i (apply1 tMat i ψ))))))

private lemma shiTof_Ph_T7 {N : ℕ} (i : Fin N) :
    shiTof_Ph (shiTof_T7 i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  simp only [shiTof_T7, apply1_tMat_eq_phase]
  cases hx : x i with
  | false => simp [hx]
  | true =>
      simp only [hx, if_true]
      ring

/-- A `T^7` block conjugated by a CNOT: control `i`, target `j`. -/
private noncomputable def shiTof_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N) :
    QState N :=
  cnotState i j hij (shiTof_T7 j (cnotState i j hij ψ))

private lemma shiTof_Ph_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    shiTof_Ph (shiTof_cB i j hij)
      (fun x => if xor (x j) (x i) then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  have h := shiTof_Ph_conj i j hij (shiTof_Ph_T7 j) φ x
  simp only [Function.update_self] at h
  exact h

/-- The three-parity `T` block: `CNOT(p,r) CNOT(q,r) T_r CNOT(q,r) CNOT(p,r)`. -/
private noncomputable def shiTof_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) : QState N :=
  cnotState p r hpr (cnotState q r hqr (apply1 tMat r
    (cnotState q r hqr (cnotState p r hpr ψ))))

private lemma shiTof_Ph_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cB7 p q r hpr hqr)
      (fun x => if xor (xor (x r) (x p)) (x q) then
        Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  have h := shiTof_Ph_conj p r hpr (shiTof_Ph_conj q r hqr (shiTof_Ph_t r)) φ x
  simp only [Function.update_self, Function.update_of_ne hqr] at h
  exact h

/-- The seven block phases multiply to the CCZ sign. -/
private lemma shiTof_phase_prod (a b c : Bool) :
    (if xor (xor c a) b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
      ((if xor c a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
        ((if xor c b then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
          ((if xor b a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
            ((if c then Complex.exp (Complex.I * Real.pi / 4) else 1) *
              ((if b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
                (if a then Complex.exp (Complex.I * Real.pi / 4) else 1))))))
      = if a && b && c then (-1 : ℂ) else 1 := by
  let w : ℂ := Complex.exp (Complex.I * Real.pi / 4)
  have h4 : w ^ 4 = -1 := by
    rw [show w ^ 4 = Complex.exp (4 * (Complex.I * Real.pi / 4)) from
      (Complex.exp_nat_mul _ 4).symm]
    convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring
  have h16 : w ^ 16 = 1 := by
    rw [show 16 = 4 * 4 from rfl, pow_mul, h4]
    norm_num
  change (if xor (xor c a) b then w else 1) *
      ((if xor c a then w ^ 7 else 1) *
        ((if xor c b then w ^ 7 else 1) *
          ((if xor b a then w ^ 7 else 1) *
            ((if c then w else 1) * ((if b then w else 1) * (if a then w else 1)))))) = _
  cases a <;> cases b <;> cases c <;> norm_num <;> ring_nf <;> first | exact h16 | exact h4

/-- The CCZ part of the circuit, as a composition of the seven diagonal blocks. -/
private noncomputable def shiTof_cczOp {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) : QState N :=
  shiTof_cB7 p q r hpr hqr (shiTof_cB p r hpr (shiTof_cB q r hqr (shiTof_cB p q hpq
    (apply1 tMat r (apply1 tMat q (apply1 tMat p ψ))))))

private lemma shiTof_Ph_ccz {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cczOp p q r hpq hpr hqr)
      (fun x => if x p && x q && x r then (-1 : ℂ) else 1) := by
  have c7 := shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp
      (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_t p) (shiTof_Ph_t q)) (shiTof_Ph_t r))
      (shiTof_Ph_cB p q hpq)) (shiTof_Ph_cB q r hqr)) (shiTof_Ph_cB p r hpr))
      (shiTof_Ph_cB7 p q r hpr hqr)
  intro φ x
  first
    | exact (c7 φ x).trans
        (congrArg (fun z : ℂ => z * φ x) (shiTof_phase_prod (x p) (x q) (x r)))
    | (refine (c7 φ x).trans ?_
       rw [← shiTof_phase_prod (x p) (x q) (x r)])
    | (refine (c7 φ x).trans ?_
       beta_reduce
       rw [shiTof_phase_prod (x p) (x q) (x r)])

private lemma shiTof_hconj {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (F : QState N → QState N)
    (hF : ∀ (φ : QState N) (y : Bits N),
      F φ y = (if y p && y q && y r then (-1 : ℂ) else 1) * φ y)
    (ψ : QState N) :
    apply1 hMat r (F (apply1 hMat r ψ))
      = fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
    inv_sqrt_two_mul_self
  funext x
  have hup : ∀ b : Bool, F (apply1 hMat r ψ) (Function.update x r b)
      = (if x p && x q && b then (-1 : ℂ) else 1)
        * ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
    intro b
    have e1 : Function.update x r b p = x p := Function.update_of_ne hpr b x
    have e2 : Function.update x r b q = x q := Function.update_of_ne hqr b x
    have e3 : Function.update x r b r = b := Function.update_self r b x
    have e4 : apply1 hMat r ψ (Function.update x r b)
        = ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
      simp only [apply1, Function.update_self, Function.update_idem]
    simp only [hF, e1, e2, e3, e4]
  have main : apply1 hMat r (F (apply1 hMat r ψ)) x
      = ∑ b : Bool, hMat (x r) b * F (apply1 hMat r ψ) (Function.update x r b) := rfl
  rw [main]
  -- PHASE 1: split the outer Bool sum, `hMat` still FOLDED.
  simp only [Fintype.sum_bool]
  -- PHASE 2: expand `F` while `hMat` is still folded, so `hup`'s LHS still matches.
  -- Listing `hup` and `hMat` in one `simp only` unfolded `hMat` inside `F (apply1 hMat r ψ)`
  -- first, `hup` then matched nothing and was silently dropped ("unused simp argument"),
  -- leaving `ring` with two opaque `F …` atoms.
  first
    | rw [hup true, hup false]
    | simp only [hup]
  -- PHASE 3: only now unfold the matrix and split the two inner Bool sums.
  simp only [hMat, Matrix.of_apply, Fintype.sum_bool, Complex.ofReal_inv]
  -- PHASE 4: abstract the irrational AFTER all unfolding, so no `(↑√2)⁻¹` survives
  -- alongside `s` and `hs` applies to every quadratic term.
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hsdef
  -- `cases h : e` already substitutes the value, so `simp only [hr, hm]` has nothing to do,
  -- and a no-progress `simp only` is an ERROR in Lean 4 (it killed all four branches).
  cases hr : x r <;> cases hm : (x p && x q) <;> (try simp only [hr, hm]) <;> norm_num <;>
    first
      | linear_combination (2 * ψ (Function.update x r false)) * hs
      | linear_combination (2 * ψ (Function.update x r true)) * hs
      | linear_combination (-2 * ψ (Function.update x r false)) * hs
      | linear_combination (-2 * ψ (Function.update x r true)) * hs

private lemma shiTof_run_map {N : ℕ} (gs : List (Instr N)) (ψ : QState N) :
    runLayered (gs.map (fun g => [g])) ψ = gs.foldl (fun st g => Instr.apply g st) ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
      have hstep : runLayered ((g :: gs).map (fun z => [z])) ψ
          = runLayered (gs.map (fun z => [z])) (Instr.apply g ψ) := rfl
      rw [hstep, ih, List.foldl_cons]

private lemma shiTof_fold_eq {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) :
    (toffoliGates p q r hpq hpr hqr).foldl (fun st g => Instr.apply g st) ψ
      = apply1 hMat r (shiTof_cczOp p q r hpq hpr hqr (apply1 hMat r ψ)) := by
  first
    | rfl
    | simp only [toffoliGates, shiTof_cczOp, shiTof_cB, shiTof_cB7, shiTof_T7,
        List.foldl_cons, List.foldl_nil, Instr.apply]

theorem toffoliCircuit_apply {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) :
    runLayered (toffoliCircuit p q r hpq hpr hqr) ψ =
      fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  rw [toffoliCircuit, shiTof_run_map, shiTof_fold_eq]
  exact shiTof_hconj p q r hpr hqr _ (fun φ y => shiTof_Ph_ccz p q r hpq hpr hqr φ y) ψ

end InfoLossLAR.WorstCase

end P2MDyadicModule5

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2PlatformSerialization

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open QAlgorithms.Complexity

open Polynomial

theorem readUnary_rest_length (xs : Str) : (readUnary xs).2.length ≤ xs.length := by
  simp only [readUnary, List.length_drop]
  omega

@[fun_prop] theorem lengthToken_poly {α : Type} [Coding α] [Inhabited α] :
    Poly (lengthToken : List α → Str) := by
  unfold lengthToken
  fun_prop

@[fun_prop] theorem serializeWords_poly : Poly serializeWords := by
  unfold serializeWords
  have hf : Poly (List.flatten : List Str → Str) := ⟨PolyProgram.listFlatten encodeBool false⟩
  exact Poly.comp Poly.list_append (Poly.pair lengthToken_poly hf)

section RepeatedParser

variable {α : Type} [Coding α] [Inhabited α]

variable (read : Str → Str × α)

lemma readList_rest_length (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) (xs : Str) :
    (readList read xs).1.length ≤ xs.length := by
  exact (parser_fold_bounds read hr hrest (unarySlots xs) (readUnary xs).2 []).1.trans
    (readUnary_rest_length xs)

end RepeatedParser

end Integration9_9.TM2PlatformSerialization

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeInverseUniform. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readCircuitInstruction_poly : Poly readCircuitInstruction := by
  unfold readCircuitInstruction
  fun_prop

theorem readCircuitInstruction_rest_length (xs : Str) :
    (readCircuitInstruction xs).1.length ≤ xs.length := by
  unfold readCircuitInstruction
  split_ifs
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
  · exact (readUnary_rest_length _).trans (readUnary_rest_length _)

@[fun_prop] theorem readCircuitLayer_poly : Poly readCircuitLayer :=
  readList_poly readCircuitInstruction readCircuitInstruction_poly readCircuitInstruction_rest_length

theorem readCircuitLayer_rest_length (xs : Str) :
    (readCircuitLayer xs).1.length ≤ xs.length :=
  readList_rest_length readCircuitInstruction readCircuitInstruction_poly readCircuitInstruction_rest_length xs

@[fun_prop] theorem readCircuitLayers_poly : Poly readCircuitLayers :=
  readList_poly readCircuitLayer readCircuitLayer_poly readCircuitLayer_rest_length

/-- The S and T inverses require respectively three and seven copies; other gates one. -/
def inverseInstructionWords (xs : Str) : List Str :=
  if inputWidth xs = 1 then (List.replicate 3 ()).map (fun _ => xs)
  else if inputWidth xs = 2 then (List.replicate 7 ()).map (fun _ => xs)
  else [xs]

@[fun_prop] theorem inverseInstructionWords_poly : Poly inverseInstructionWords := by
  unfold inverseInstructionWords
  fun_prop

theorem inverseInstructionWords_encInstr {n : ℕ} (g : Instr n) :
    inverseInstructionWords (encInstr g) = (inverseInstr g).map encInstr := by
  cases g <;>
    simp [inverseInstructionWords, encInstr, List.append_assoc, inputWidth_encNat_append,
      inverseInstr, instrPeriod]

/-- Transform parsed gate strings into the exact singleton layers of the syntactic inverse. -/
def inverseCircuitWords (layers : List (List Str)) : List (List Str) :=
  (layers.flatten.reverse.flatMap inverseInstructionWords).map (fun word => [word])

@[fun_prop] theorem inverseCircuitWords_poly : Poly inverseCircuitWords := by
  unfold inverseCircuitWords
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  have hr := Poly.comp parser_reverse_poly hf
  have hm : Poly (fun layers : List (List Str) =>
      layers.flatten.reverse.flatMap inverseInstructionWords) :=
    Poly.list_flatMap (Poly.comp inverseInstructionWords_poly Poly.snd) hr
  apply Poly.list_map
  · fun_prop
  · exact hm

theorem inverseCircuitWords_correct {n : ℕ} (circuit : Layered n) :
    inverseCircuitWords (circuit.map (List.map encInstr)) =
      (inverseCircuit circuit).map (List.map encInstr) := by
  simp only [inverseCircuitWords, ← List.map_flatten, ← List.map_reverse, List.flatMap_map,
    Function.comp_def, inverseInstructionWords_encInstr,
    inverseCircuit, inverseGates, List.map_map]
  rw [← List.map_flatMap]
  simp only [List.map_map, Function.comp_def, List.map_cons, List.map_nil]

end InfoLossLAR.WorstCase

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

namespace ReversibleGate

theorem compile_apply {n : ℕ} (g : ReversibleGate n) (ψ : QState n) :
    runLayered g.compile ψ = fun x => ψ (g.act x) := by
  cases g with
  | flip i =>
    funext x
    simp only [compile, runLayered, runLayer, List.foldl_cons, List.foldl_nil, Instr.apply, apply1]
    cases hx : x i <;> simp [xMat, act, hx]
  | controlled i j hij => rfl
  | toffoli i j k hij hik hjk => exact toffoliCircuit_apply i j k hij hik hjk ψ

end ReversibleGate

private theorem runLayered_append {n : ℕ} (c d : Layered n) (ψ : QState n) :
    runLayered (c ++ d) ψ = runLayered d (runLayered c ψ) := List.foldl_append

/-- Amplitude semantics for every input state, including superpositions and garbage. -/
theorem compileReversible_apply {n : ℕ} (gates : List (ReversibleGate n)) (ψ : QState n) :
    runLayered (compileReversible gates) ψ = fun x => ψ ((reversibleAction gates).symm x) := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change runLayered (g.compile ++ compileReversible gs) ψ = _
    rw [runLayered_append, ih, g.compile_apply]
    rfl

/-- A computational basis input is sent to the exact classical output. -/
theorem compileReversible_basis {n : ℕ} (gates : List (ReversibleGate n)) (x : Bits n) :
    runLayered (compileReversible gates) (fun y => if y = x then (1 : ℂ) else 0) =
      fun y => if y = reversibleAction gates x then 1 else 0 := by
  rw [compileReversible_apply]
  funext y
  congr 1
  exact propext (Equiv.symm_apply_eq _)

end InfoLossLAR.WorstCase

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeReversibleUniform. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem toffoliInstructionWords_poly :
    Poly (fun x : Str × Str × Str => toffoliInstructionWords x.1 x.2.1 x.2.2) := by
  unfold toffoliInstructionWords
  fun_prop

@[fun_prop] theorem readReversibleInstruction_poly : Poly readReversibleInstruction := by
  unfold readReversibleInstruction
  fun_prop

theorem readReversibleInstruction_rest_length (xs : Str) :
    (readReversibleInstruction xs).1.length ≤ xs.length := by
  unfold readReversibleInstruction
  split_ifs
  · exact (readUnary_rest_length _).trans (readUnary_rest_length _)
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans
      ((readUnary_rest_length _).trans (readUnary_rest_length _)))

private theorem reversibleUniformUnaryWidth (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs

theorem readReversibleInstruction_append {n : ℕ} (g : ReversibleGate n) (xs : Str) :
    readReversibleInstruction (g.code ++ xs) = (xs, g.compile.flatten.map encInstr) := by
  cases g <;> simp only [ReversibleGate.code, List.append_assoc, readReversibleInstruction,
    reversibleUniformUnaryWidth, readUnary_append] <;> norm_num <;> rfl

@[fun_prop] theorem readReversibleProgram_poly : Poly readReversibleProgram :=
  readList_poly readReversibleInstruction readReversibleInstruction_poly readReversibleInstruction_rest_length

theorem readReversibleProgram_append {n : ℕ} (gates : List (ReversibleGate n)) (xs : Str) :
    readReversibleProgram (encStr (gates.map ReversibleGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.flatten.map encInstr)) :=
  readList_append_mapped readReversibleInstruction ReversibleGate.code
    (fun g => g.compile.flatten.map encInstr) readReversibleInstruction_append gates xs

private theorem compiledWords {n : ℕ} (gates : List (ReversibleGate n)) :
    ((gates.map (fun g => g.compile.flatten.map encInstr)).flatten).map (fun word => [word]) =
      (compileReversible gates).map (List.map encInstr) := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, compileReversible,
      List.flatMap_cons] at ih ⊢
    rw [ih]
    congr 1
    cases g <;> rfl

@[fun_prop] theorem compileReversibleDescription_poly : Poly compileReversibleDescription := by
  unfold compileReversibleDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem compileReversibleDescription_code (F : ReversibleFamily) (n : ℕ) :
    compileReversibleDescription (F.code n) = encFamilyAt F.compile n := by
  unfold ReversibleFamily.code compileReversibleDescription
  simp only [List.append_assoc, readUnary_append]
  have h := readReversibleProgram_append (F.gates n) []
  simp only [List.append_nil] at h
  rw [h]
  have hh := congrArg (fun xs : List (List Str) => serializeWords (xs.map serializeWords))
    (compiledWords (F.gates n))
  simp only [List.map_map, Function.comp_def] at hh
  rw [hh]
  simp only [serializeWords_eq, encFamilyAt, ReversibleFamily.compile, encCirc, List.append_assoc]
  rfl

end InfoLossLAR.WorstCase

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

namespace BooleanGate

theorem assign_other {n : ℕ} (g : BooleanGate n) (x : Bits n) (i : Fin n)
    (hi : i ≠ g.target) : g.assign x i = x i := Function.update_of_ne hi _ _

theorem compile_action {n : ℕ} (g : BooleanGate n) (x : Bits n)
    (hz : x g.target = false) : reversibleAction g.compile x = g.assign x := by
  cases g with
  | constant t b =>
    cases b <;> simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
  | copy s t h =>
    simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
  | negate s t h =>
    funext i
    by_cases hi : i = t
    · subst i
      cases hv : x s <;>
        simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
          Function.update_of_ne h]
    · simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
        Function.update_of_ne hi]
  | xor a b t ha hb =>
    simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
      Function.update_of_ne hb]
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
    · simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]

end BooleanGate

theorem reversibleAction_append {n : ℕ} (a b : List (ReversibleGate n)) :
    reversibleAction (a ++ b) = (reversibleAction a).trans (reversibleAction b) := by
  induction a with
  | nil => rfl
  | cons g a ih =>
    simp only [List.cons_append, reversibleAction, ih]
    rfl

/-- Complete Boolean-program semantics, with all intermediate values retained. -/
theorem booleanToReversible_action {n : ℕ} (gates : List (BooleanGate n))
    (hf : BooleanFresh gates) (x : Bits n)
    (hz : ∀ g ∈ gates, x g.target = false) :
    reversibleAction (booleanToReversible gates) x = booleanRun gates x := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gates ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hf
    have hzero : ∀ h ∈ gates, g.assign x h.target = false := by
      intro h hh
      rw [g.assign_other x h.target (Ne.symm (hhead h hh))]
      exact hz h (by simp [hh])
    change reversibleAction (g.compile ++ booleanToReversible gates) x = _
    rw [reversibleAction_append]
    change reversibleAction (booleanToReversible gates) (reversibleAction g.compile x) = _
    rw [g.compile_action x (hz g (by simp)), ih htail _ hzero]
    rfl

end InfoLossLAR.WorstCase

end P2MDyadicModule10

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

private theorem leftRegister_update_left {n m : ℕ} (state : Bits (n+m)) (wire : Fin n) (bit : Bool) :
    leftRegister (Function.update state (Fin.castAdd m wire) bit)=Function.update (leftRegister state) wire bit := by
  funext index
  by_cases h : index=wire
  · subst index
    simp [leftRegister]
  · have he : Fin.castAdd m index ≠ Fin.castAdd m wire := fun hh => h (Fin.ext (congrArg (fun k : Fin (n+m) => k.val) hh))
    simp [leftRegister,Function.update_of_ne h,Function.update_of_ne he]

private theorem rightRegister_update_left {n m : ℕ} (state : Bits (n+m)) (wire : Fin n) (bit : Bool) :
    rightRegister (Function.update state (Fin.castAdd m wire) bit)=rightRegister state := by
  funext index
  have he : Fin.natAdd n index ≠ Fin.castAdd m wire := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hi := wire.isLt
    omega
  simp [rightRegister,Function.update_of_ne he]

private theorem leftRegister_update_right {n m : ℕ} (state : Bits (n+m)) (wire : Fin m) (bit : Bool) :
    leftRegister (Function.update state (Fin.natAdd n wire) bit)=leftRegister state := by
  funext index
  have he : Fin.castAdd m index ≠ Fin.natAdd n wire := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hi := index.isLt
    omega
  simp [leftRegister,Function.update_of_ne he]

private theorem rightRegister_update_right {n m : ℕ} (state : Bits (n+m)) (wire : Fin m) (bit : Bool) :
    rightRegister (Function.update state (Fin.natAdd n wire) bit)=Function.update (rightRegister state) wire bit := by
  funext index
  by_cases h : index=wire
  · subst index
    simp [rightRegister]
  · have he : Fin.natAdd n index ≠ Fin.natAdd n wire := by
      intro hh
      exact h (Fin.ext (Nat.add_left_cancel (congrArg Fin.val hh)))
    simp [rightRegister,Function.update_of_ne h,Function.update_of_ne he]

private theorem apply1_left_tensor {n m : ℕ} (matrix : Matrix Bool Bool ℂ) (wire : Fin n)
    (first : QState n) (second : QState m) :
    apply1 matrix (Fin.castAdd m wire) (tensorState first second)=tensorState (apply1 matrix wire first) second := by
  funext state
  simp only [apply1,tensorState,leftRegister_update_left,rightRegister_update_left]
  change (∑ bit,matrix (leftRegister state wire) bit*
    (first (Function.update (leftRegister state) wire bit)*second (rightRegister state))) =
      (∑ bit,matrix (leftRegister state wire) bit*first (Function.update (leftRegister state) wire bit))*
        second (rightRegister state)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro bit _
  ring

private theorem apply1_right_tensor {n m : ℕ} (matrix : Matrix Bool Bool ℂ) (wire : Fin m)
    (first : QState n) (second : QState m) :
    apply1 matrix (Fin.natAdd n wire) (tensorState first second)=tensorState first (apply1 matrix wire second) := by
  funext state
  simp only [apply1,tensorState,leftRegister_update_right,rightRegister_update_right]
  change (∑ bit,matrix (rightRegister state wire) bit*
    (first (leftRegister state)*second (Function.update (rightRegister state) wire bit))) =
      first (leftRegister state)*
        (∑ bit,matrix (rightRegister state wire) bit*second (Function.update (rightRegister state) wire bit))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bit _
  ring

/-- All five actual Clifford+T gate constructors act on their designated
left register and leave the other register untouched. -/
theorem leftInstruction_tensor {n m : ℕ} (gate : Instr n) (first : QState n) (second : QState m) :
    (leftInstruction gate).apply (tensorState first second)=tensorState (gate.apply first) second := by
  cases gate with
  | h wire => exact apply1_left_tensor hMat wire first second
  | s wire => exact apply1_left_tensor sMat wire first second
  | t wire => exact apply1_left_tensor tMat wire first second
  | x wire => exact apply1_left_tensor xMat wire first second
  | cnot control target hct =>
    funext state
    simp only [leftInstruction,Instr.apply,cnotState,tensorState,leftRegister_update_left,rightRegister_update_left]
    rfl

/-- The same exact gate semantics for the right physical register. -/
theorem rightInstruction_tensor {n m : ℕ} (gate : Instr m) (first : QState n) (second : QState m) :
    (rightInstruction gate).apply (tensorState first second)=tensorState first (gate.apply second) := by
  cases gate with
  | h wire => exact apply1_right_tensor hMat wire first second
  | s wire => exact apply1_right_tensor sMat wire first second
  | t wire => exact apply1_right_tensor tMat wire first second
  | x wire => exact apply1_right_tensor xMat wire first second
  | cnot control target hct =>
    funext state
    simp only [rightInstruction,Instr.apply,cnotState,tensorState,leftRegister_update_right,rightRegister_update_right]
    rfl

private theorem leftLayer_tensor {n m : ℕ} (layer : List (Instr n)) (first : QState n) (second : QState m) :
    runLayer (layer.map leftInstruction) (tensorState first second)=tensorState (runLayer layer first) second := by
  induction layer generalizing first with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [leftInstruction_tensor]
    exact ih (gate.apply first)

private theorem rightLayer_tensor {n m : ℕ} (layer : List (Instr m)) (first : QState n) (second : QState m) :
    runLayer (layer.map rightInstruction) (tensorState first second)=tensorState first (runLayer layer second) := by
  induction layer generalizing second with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [rightInstruction_tensor]
    exact ih (gate.apply second)

theorem leftCircuit_tensor {n m : ℕ} (circuit : Layered n) (first : QState n) (second : QState m) :
    runLayered (leftCircuit circuit) (tensorState first second)=tensorState (runLayered circuit first) second := by
  induction circuit generalizing first with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [leftCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [leftLayer_tensor]
    exact ih (runLayer layer first)

theorem rightCircuit_tensor {n m : ℕ} (circuit : Layered m) (first : QState n) (second : QState m) :
    runLayered (rightCircuit circuit) (tensorState first second)=tensorState first (runLayered circuit second) := by
  induction circuit generalizing second with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [rightCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [rightLayer_tensor]
    exact ih (runLayer layer second)

/-- Two real circuits on disjoint registers have exactly their product action. -/
theorem disjointCircuits_tensor {n m : ℕ} (left : Layered n) (right : Layered m)
    (first : QState n) (second : QState m) :
    runLayered (leftCircuit left++rightCircuit right) (tensorState first second)=
      tensorState (runLayered left first) (runLayered right second) := by
  rw [runLayered,List.foldl_append]
  change runLayered (rightCircuit right) (runLayered (leftCircuit left) (tensorState first second)) = _
  rw [leftCircuit_tensor,rightCircuit_tensor]

end InfoLossLAR.WorstCase

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeCircuitRelocation. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity

open scoped BigOperators

theorem selected_value {k n : ℕ} (w : Fin k ↪ Fin n)
    (p : Bits k×OutsideBits w) (i : Fin k) : (wireBitsEquiv w).symm p (w i)=p.1 i :=
  congrFun (congrArg Prod.fst ((wireBitsEquiv w).apply_symm_apply p)) i

theorem split_update {k n : ℕ} (w : Fin k ↪ Fin n)
    (x : Bits n) (i : Fin k) (b : Bool) :
    wireBitsEquiv w (Function.update x (w i) b)=
      (Function.update (wireBitsEquiv w x).1 i b,(wireBitsEquiv w x).2) := by
  apply Prod.ext
  · funext j
    by_cases h : j=i
    · subst j; simp [wireBitsEquiv]
    · have hw : w j≠w i := w.injective.ne h
      simp [wireBitsEquiv,Function.update_of_ne hw,Function.update_of_ne h]
  · funext j
    have h : j.val≠w i := fun he => j.property ⟨i,he.symm⟩
    simp [wireBitsEquiv,Function.update_of_ne h]

theorem unsplit_update {k n : ℕ} (w : Fin k ↪ Fin n)
    (p : Bits k×OutsideBits w) (i : Fin k) (b : Bool) :
    Function.update ((wireBitsEquiv w).symm p) (w i) b=
      (wireBitsEquiv w).symm (Function.update p.1 i b,p.2) := by
  apply (wireBitsEquiv w).injective
  rw [split_update,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem relocate_apply1 {k n : ℕ} (w : Fin k ↪ Fin n)
    (M : Matrix Bool Bool ℂ) (i : Fin k) (ψ : QState n) :
    splitState w (apply1 M (w i) ψ)=
      fun p => apply1 M i (fun x => splitState w ψ (x,p.2)) p.1 := by
  funext p
  simp only [splitState,apply1,selected_value,unsplit_update]

/-- All spectator amplitudes are retained, including entanglement with the
selected register. No product-state assumption is used. -/
theorem relocateInstr_split {k n : ℕ} (w : Fin k ↪ Fin n) (g : Instr k) (ψ : QState n) :
    splitState w ((relocateInstr w g).apply ψ)=
      fun p => g.apply (fun x => splitState w ψ (x,p.2)) p.1 := by
  cases g with
  | h i => exact relocate_apply1 w hMat i ψ
  | s i => exact relocate_apply1 w sMat i ψ
  | t i => exact relocate_apply1 w tMat i ψ
  | x i => exact relocate_apply1 w xMat i ψ
  | cnot i j h =>
    funext p
    simp only [relocateInstr,Instr.apply,cnotState,splitState,selected_value,unsplit_update]

theorem relocateLayer_split {k n : ℕ} (w : Fin k ↪ Fin n) (gates : List (Instr k))
    (ψ : QState n) :
    splitState w (runLayer (gates.map (relocateInstr w)) ψ)=
      fun p => runLayer gates (fun x => splitState w ψ (x,p.2)) p.1 := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change splitState w (runLayer (gs.map (relocateInstr w)) ((relocateInstr w g).apply ψ))=_
    rw [ih,relocateInstr_split]
    rfl

/-- The actual relocated whole circuit acts on every reference slice. -/
theorem relocateCircuit_split {k n : ℕ} (w : Fin k ↪ Fin n) (circuit : Layered k)
    (ψ : QState n) :
    splitState w (runLayered (relocateCircuit w circuit) ψ)=
      fun p => runLayered circuit (fun x => splitState w ψ (x,p.2)) p.1 := by
  induction circuit generalizing ψ with
  | nil => rfl
  | cons layer rest ih =>
    change splitState w (runLayered (relocateCircuit w rest)
      (runLayer (layer.map (relocateInstr w)) ψ))=_
    rw [ih,relocateLayer_split]
    rfl

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgeInitializedRelocation. -/
section P2MDyadicModule13

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity QAlgorithms.Papers.Independent.Renew46.P12

open scoped BigOperators

/-- Reassemble the physical register after selecting local and spectator wires. -/
noncomputable def unsplitState {k n : ℕ} (w : Fin k ↪ Fin n)
    (ψ : Bits k × OutsideBits w → ℂ) : QState n := fun x => ψ (wireBitsEquiv w x)

@[simp] theorem split_unsplit {k n : ℕ} (w : Fin k ↪ Fin n)
    (ψ : Bits k × OutsideBits w → ℂ) : splitState w (unsplitState w ψ)=ψ := by
  funext p
  simp only [splitState,unsplitState,Equiv.apply_symm_apply]

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeFiniteGateNativeAlgebra. -/
section P2MDyadicModule14

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem addReal_poly : Poly (fun x : RealPair×RealPair => addReal x.1 x.2) := by unfold addReal;fun_prop

@[fun_prop] theorem negReal_poly : Poly negReal := by unfold negReal;fun_prop

@[fun_prop] theorem subReal_poly : Poly (fun x : RealPair×RealPair => subReal x.1 x.2) := by unfold subReal;fun_prop

@[fun_prop] theorem mulReal_poly : Poly (fun x : RealPair×RealPair => mulReal x.1 x.2) := by unfold mulReal;fun_prop

@[fun_prop] theorem add_poly : Poly (fun x : Scalar×Scalar => add x.1 x.2) := by unfold add;fun_prop

@[fun_prop] theorem neg_poly : Poly neg := by unfold neg;fun_prop

@[fun_prop] theorem sub_poly : Poly (fun x : Scalar×Scalar => sub x.1 x.2) := by unfold sub;fun_prop

@[fun_prop] theorem mul_poly : Poly (fun x : Scalar×Scalar => mul x.1 x.2) := by unfold mul;fun_prop

@[fun_prop] theorem normSq_poly : Poly normSq := by unfold normSq;fun_prop

@[fun_prop] theorem nonnegReal_poly : Poly nonnegReal := by unfold nonnegReal; simp only [pow_two];fun_prop

@[fun_prop] theorem leRational_poly : Poly (fun x : RealPair×ℚ => leRational x.1 x.2) := by
  unfold leRational
  fun_prop

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeFiniteGateNativeBounds. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def RealHeight (x : RealPair) (L : ℕ) : Prop := HasHeight x.1 L ∧ HasHeight x.2 L

def ScalarHeight (x : Scalar) (L : ℕ) : Prop := RealHeight x.1 L ∧ RealHeight x.2 L

theorem RealHeight.mono {x : RealPair} {L M : ℕ} (h : RealHeight x L) (hle : L≤M) : RealHeight x M :=
  ⟨h.1.mono hle,h.2.mono hle⟩

theorem ScalarHeight.mono {x : Scalar} {L M : ℕ} (h : ScalarHeight x L) (hle : L≤M) : ScalarHeight x M :=
  ⟨h.1.mono hle,h.2.mono hle⟩

theorem RealHeight.neg {x : RealPair} {L : ℕ} (h : RealHeight x L) : RealHeight (negReal x) L :=
  ⟨h.1.neg,h.2.neg⟩

theorem RealHeight.add {x y : RealPair} {L M : ℕ} (hx : RealHeight x L) (hy : RealHeight y M) :
    RealHeight (addReal x y) (L+M+1) := ⟨hx.1.add hy.1,hx.2.add hy.2⟩

theorem RealHeight.sub {x y : RealPair} {L M : ℕ} (hx : RealHeight x L) (hy : RealHeight y M) :
    RealHeight (subReal x y) (L+M+1) := hx.add hy.neg

theorem RealHeight.mul {x y : RealPair} {L M : ℕ} (hx : RealHeight x L) (hy : RealHeight y M) :
    RealHeight (mulReal x y) (2*(L+M)+2) := by
  have htwo : HasHeight (2 : ℚ) 1 := by norm_num [HasHeight]
  constructor
  · exact ((hx.1.mul hy.1).add ((htwo.mul hx.2).mul hy.2)).mono (by omega)
  · exact ((hx.1.mul hy.2).add (hx.2.mul hy.1)).mono (by omega)

theorem ScalarHeight.neg {x : Scalar} {L : ℕ} (h : ScalarHeight x L) : ScalarHeight (neg x) L :=
  ⟨h.1.neg,h.2.neg⟩

theorem ScalarHeight.add {x y : Scalar} {L M : ℕ} (hx : ScalarHeight x L) (hy : ScalarHeight y M) :
    ScalarHeight (add x y) (L+M+1) := ⟨hx.1.add hy.1,hx.2.add hy.2⟩

theorem ScalarHeight.mul {x y : Scalar} {L M : ℕ} (hx : ScalarHeight x L) (hy : ScalarHeight y M) :
    ScalarHeight (mul x y) (4*(L+M)+5) := by
  constructor
  · exact ((hx.1.mul hy.1).sub (hx.2.mul hy.2)).mono (by omega)
  · exact ((hx.1.mul hy.2).add (hx.2.mul hy.1)).mono (by omega)

theorem zero_height (L : ℕ) : ScalarHeight zero L :=
  ⟨⟨HasHeight.zero _,HasHeight.zero _⟩,⟨HasHeight.zero _,HasHeight.zero _⟩⟩

theorem one_height (L : ℕ) : ScalarHeight one L :=
  ⟨⟨HasHeight.one _,HasHeight.zero _⟩,⟨HasHeight.zero _,HasHeight.zero _⟩⟩

theorem hScale_height : ScalarHeight hScale 1 := by
  have hh : HasHeight (1/2 : ℚ) 1 := by norm_num [HasHeight]
  exact ⟨⟨HasHeight.zero _,hh⟩,⟨HasHeight.zero _,HasHeight.zero _⟩⟩

theorem tPhase_height : ScalarHeight tPhase 1 := by
  have hh : HasHeight (1/2 : ℚ) 1 := by norm_num [HasHeight]
  exact ⟨⟨HasHeight.zero _,hh⟩,⟨HasHeight.zero _,hh⟩⟩

theorem hCoefficient_height (row column : Bool) : ScalarHeight (hCoefficient row column) 1 := by
  unfold hCoefficient
  split
  · exact hScale_height.neg
  · exact hScale_height

theorem tCoefficient_height (row column : Bool) : ScalarHeight (tCoefficient row column) 1 := by
  unfold tCoefficient
  split
  · split
    · exact tPhase_height
    · exact one_height _
  · exact zero_height _

theorem realPair_encoding_length {x : RealPair} {L : ℕ} (h : RealHeight x L) :
    (enc x).length≤9*L+31 := by
  change (encodePair Ratio.encode Ratio.encode x).length≤_
  rw [encodePair_length]
  have h1 := Ratio.length_height h.1
  have h2 := Ratio.length_height h.2
  omega

theorem scalar_encoding_length {x : Scalar} {L : ℕ} (h : ScalarHeight x L) :
    (enc x).length≤27*L+94 := by
  change (encodePair enc enc x).length≤_
  rw [encodePair_length]
  have h1 := realPair_encoding_length h.1
  have h2 := realPair_encoding_length h.2
  omega

theorem scalar_encoding_height (x : Scalar) : ScalarHeight x (enc x).length := by
  have hlen : (enc x).length=4*(Ratio.encode x.1.1).length+2*(Ratio.encode x.1.2).length+
      2*(Ratio.encode x.2.1).length+(Ratio.encode x.2.2).length+4 := by
    change (encodePair (encodePair Ratio.encode Ratio.encode) (encodePair Ratio.encode Ratio.encode) x).length=_
    simp only [encodePair_length]
    omega
  exact ⟨⟨(Ratio.height_length _).mono (by omega),(Ratio.height_length _).mono (by omega)⟩,
    ⟨(Ratio.height_length _).mono (by omega),(Ratio.height_length _).mono (by omega)⟩⟩

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeFiniteGateNativeMatrix. -/
section P2MDyadicModule16

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

@[simp] theorem basis_length : basis.length=8 := rfl

def basisIndex (x : Bits) : ℕ :=
  (if x 0 then 4 else 0)+(if x 1 then 2 else 0)+(if x 2 then 1 else 0)

theorem basis_get (x : Bits) : basis[basisIndex x]?=some x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2
  all_goals simp only [basisIndex,h0,h1,h2,Bool.false_eq_true,ite_false,ite_true]
  all_goals simp only [basis,Nat.reduceAdd,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq]
  all_goals funext i;fin_cases i <;> simp_all

theorem mem_basis (x : Bits) : x∈basis := List.mem_of_getElem? (basis_get x)

def table (m : NativeMatrix) : List (List Scalar) := basis.map (fun r => basis.map (fun c => m r c))

def encodeMatrix (m : NativeMatrix) : List Bool := encodeList (encodeList enc) (table m)

instance nativeMatrixCoding : Coding NativeMatrix := ⟨encodeMatrix⟩

/-- A fixed finite table is the entire machine input. It contains rational coordinates only. -/
@[fun_prop] theorem table_poly : Poly table := by
  exact ⟨(PolyProgram.identity (enc : List (List Scalar)→List Bool)).recode table
    (fun _ => rfl) (fun _ => rfl)⟩

def tableEntry (m : NativeMatrix) (r c : Bits) : Scalar :=
  ((table m)[basisIndex r]?.getD [])[basisIndex c]?.getD zero

theorem tableEntry_eq (m : NativeMatrix) (r c : Bits) : tableEntry m r c=m r c := by
  simp [tableEntry,table,List.getElem?_map,basis_get]

theorem matrix_entry_poly (r c : Bits) : Poly (fun m : NativeMatrix => m r c) := by
  have hr : Poly (fun m : NativeMatrix => (table m)[basisIndex r]?.getD []) :=
    Poly.list_getD_comp [] table_poly (Automatic.Poly.const _)
  have hc : Poly (fun m : NativeMatrix => ((table m)[basisIndex r]?.getD [])[basisIndex c]?.getD zero) :=
    Poly.list_getD_comp zero hr (Automatic.Poly.const _)
  exact ⟨hc.program.congr _ (fun m => tableEntry_eq m r c)⟩

private theorem fixed_list_poly {α β ι : Type} [Coding α] [Coding β]
    (indices : List ι) (f : ι→α→β) (hf : ∀ i∈indices,Poly (f i)) :
    Poly (fun x => indices.map (fun i => f i x)) := by
  induction indices with
  | nil => exact Automatic.Poly.const []
  | cons i rest ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    exact Poly.comp Poly.list_cons (Poly.pair hi ht)

theorem matrix_build_poly {α : Type} [Coding α] (f : α→NativeMatrix)
    (hf : ∀ r∈basis,∀ c∈basis,Poly (fun x => f x r c)) : Poly f := by
  have htable : Poly (fun x => table (f x)) :=
    fixed_list_poly basis (fun r x => basis.map (fun c => f x r c))
      (fun r hr => fixed_list_poly basis (fun c x => f x r c) (hf r hr))
  exact ⟨htable.program.recode id (fun _ => rfl) (fun _ => rfl)⟩

theorem sumAt_poly {α : Type} [Coding α] (indices : List Bits) (f : α→Bits→Scalar)
    (hf : ∀ i∈indices,Poly (fun x => f x i)) : Poly (fun x => sumAt indices (f x)) := by
  induction indices with
  | nil => exact Automatic.Poly.const zero
  | cons i rest ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun x => add (f x i) (sumAt rest (f x)))
    exact Poly.comp add_poly (Poly.pair hi ht)

@[fun_prop] theorem matrixMul_poly : Poly (fun x : NativeMatrix×NativeMatrix => matrixMul x.1 x.2) := by
  apply matrix_build_poly
  intro r hr c hc
  apply sumAt_poly
  intro k hk
  exact Poly.comp mul_poly (Poly.pair
    (Poly.comp (matrix_entry_poly r k) Poly.fst)
    (Poly.comp (matrix_entry_poly k c) Poly.snd))

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeFiniteGateNativeMatrixBounds. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def MatrixHeight (m : NativeMatrix) (L : ℕ) : Prop := ∀ r c,ScalarHeight (m r c) L

theorem sumAt_height (indices : List Bits) (f : Bits→Scalar) (L : ℕ)
    (h : ∀ i∈indices,ScalarHeight (f i) L) :
    ScalarHeight (sumAt indices f) (indices.length*(L+1)) := by
  induction indices with
  | nil => exact zero_height _
  | cons i rest ih =>
    have hi := h i (by simp)
    have ht := ih (fun j hj => h j (by simp [hj]))
    exact (hi.add ht).mono (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega)

attribute [local irreducible] ScalarHeight sumAt

theorem matrixMul_height {first second : NativeMatrix} {L M : ℕ}
    (hfirst : MatrixHeight first L) (hsecond : MatrixHeight second M) :
    MatrixHeight (matrixMul first second) (32*(L+M)+48) := by
  intro r c
  have h := sumAt_height basis (fun k => mul (first r k) (second k c)) (4*(L+M)+5)
    (fun k _ => (hfirst r k).mul (hsecond k c))
  rw [basis_length] at h
  exact h.mono (by omega)

theorem matrixMul_left_gate_height {state gate : NativeMatrix} {L : ℕ}
    (hstate : MatrixHeight state L) (hgate : MatrixHeight gate 1) (hL : 1≤L) :
    MatrixHeight (matrixMul gate state) (128*L) := by
  intro r c
  exact (matrixMul_height hgate hstate r c).mono (by omega)

theorem matrix_encoding_length {m : NativeMatrix} {L : ℕ} (h : MatrixHeight m L) :
    (enc m).length≤32768*(L+1) := by
  have hrow (r : Bits) :
      (encodeList enc (basis.map (fun c => m r c))).length≤8*(2*(27*L+94)+1) := by
    have hh := EncodedList.length_bound enc (basis.map (fun c => m r c)) (27*L+94) (by
      intro x hx
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp hx
      exact scalar_encoding_length (h r c))
    simpa only [List.length_map,basis_length] using hh
  have hh := EncodedList.length_bound (encodeList enc) (table m) (8*(2*(27*L+94)+1)) (by
    intro row hr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact hrow r)
  change (encodeList (encodeList enc) (table m)).length≤_
  have ht : (table m).length=8 := by simp only [table,List.length_map,basis_length]
  rw [ht] at hh
  omega

theorem matrix_encoding_height (m : NativeMatrix) : MatrixHeight m (enc m).length := by
  intro r c
  have hrow : basis.map (fun column => m r column)∈table m :=
    List.mem_map.mpr ⟨r,mem_basis r,rfl⟩
  have hentry : m r c∈basis.map (fun column => m r column) :=
    List.mem_map.mpr ⟨c,mem_basis c,rfl⟩
  have h1 := EncodedList.member_length enc _ _ hentry
  have h2 := EncodedList.member_length (encodeList enc) _ _ hrow
  exact (scalar_encoding_height (m r c)).mono (h1.trans h2)

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeFiniteGateNativeEnumeration. -/
section P2MDyadicModule18

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

@[local fun_prop] private theorem natDiv_poly : Poly (fun x : ℕ × ℕ => x.1/x.2) := ⟨PolyProgram.natDiv⟩

@[local fun_prop] private theorem natMod_poly : Poly (fun x : ℕ × ℕ => x.1%x.2) := ⟨PolyProgram.natMod⟩

@[local fun_prop] private theorem listReverse_poly : Poly (List.reverse : List ℕ → List ℕ) :=
  ⟨PolyProgram.listReverse Nat.bits 0⟩

@[fun_prop] theorem step_poly : Poly step := by unfold step;fun_prop

theorem step_height (s : State) (u : Unit) :
    (enc (step (s,u))).length ≤ (enc s).length+9*(2*(enc u).length+1) := by
  have hd := NatBinary.length_mono (Nat.div_le_self s.1 13)
  have hm : (s.1%13-1).bits.length ≤ 4 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have ht := Nat.mod_lt s.1 (by decide : 0<13)
    norm_num
    omega
  change (encodePair Nat.bits (encodeList Nat.bits) (step (s,u))).length ≤
    (encodePair Nat.bits (encodeList Nat.bits) s).length+9*(2*0+1)
  unfold step
  split
  · change (encodePair Nat.bits (encodeList Nat.bits) s).length ≤ _; omega
  · simp only [encodePair_length,EncodedList.cons_length]
    omega

noncomputable def foldProgram : PolyProgram enc enc
    (fun x : List Unit × State => x.1.foldl (fun s u => step (s,u)) x.2) :=
  step_poly.program.listFoldLinear () 9 step_height

@[fun_prop] theorem fold_poly : Poly
    (fun x : List Unit × State => x.1.foldl (fun s u => step (s,u)) x.2) := ⟨foldProgram⟩

@[fun_prop] theorem decode_poly : Poly decode := by
  have hf : Poly (fun x : List Unit × ℕ => x.1.foldl (fun s u => step (s,u)) (x.2,[])) :=
    Poly.comp fold_poly (Poly.pair Poly.fst (Poly.pair Poly.snd (Automatic.Poly.const ([] : List ℕ))))
  unfold decode
  exact Poly.comp listReverse_poly (Poly.comp Poly.snd hf)

@[fun_prop] theorem candidates_poly : Poly candidates := by
  unfold candidates
  exact Poly.list_map (Poly.comp decode_poly (by fun_prop)) Poly.list_indices

/-- For every fixed search-length constant, this is a fixed polynomial in
    the unary inverse-accuracy budget. -/
noncomputable def budgetPolynomial (a : ℕ) : Polynomial ℕ :=
  Polynomial.C (13^(a+1))*(Polynomial.X+1)^(4*a)

@[fun_prop] theorem searchSlots_poly (a : ℕ) : Poly (searchSlots a) :=
  by unfold searchSlots; simpa only [budgetPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using polynomialSlots_poly (budgetPolynomial a)

theorem searchSlots_length (a : ℕ) (budget : List Unit) :
    (searchSlots a budget).length=13^(a+1)*(budget.length+1)^(4*a) := by
  simp [searchSlots]

@[fun_prop] theorem search_poly (a : ℕ) : Poly (search a) :=
  by unfold search;exact Poly.comp candidates_poly (searchSlots_poly a)

open FiniteGateTransport

end InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeFiniteGateNativeGates. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

theorem letterNative_height (letter : Letter 3) : MatrixHeight (letterNative letter) 1 := by
  cases letter with
  | h i =>
    intro row column
    change ScalarHeight (if column=Function.update row i (column i) then hCoefficient (row i) (column i) else zero) 1
    split
    · exact hCoefficient_height _ _
    · exact zero_height _
  | t i =>
    intro row column
    change ScalarHeight (if column=Function.update row i (column i) then tCoefficient (row i) (column i) else zero) 1
    split
    · exact tCoefficient_height _ _
    · exact zero_height _
  | cnot i j hij =>
    intro row column
    change ScalarHeight (if column=Function.update row j (xor (row j) (row i)) then one else zero) 1
    split
    · exact one_height _
    · exact zero_height _

theorem nativeGate_eq (code : ℕ) :
    nativeGate code=letterNative (FiniteGateNativeEnumeration.letterOfCode code) := by
  unfold nativeGate gateTable FiniteGateNativeEnumeration.letterOfCode
  rw [List.getElem?_map]
  cases alphabet[code]? <;> rfl

@[fun_prop] theorem nativeGate_poly : Poly nativeGate := by
  unfold nativeGate
  exact Poly.list_getD_comp _ (Automatic.Poly.const gateTable) Poly.identity

theorem nativeGate_height (code : ℕ) : MatrixHeight (nativeGate code) 1 := by
  rw [nativeGate_eq]
  exact letterNative_height _

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeFiniteGateNativeResourceBounds. -/
section P2MDyadicModule20

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

theorem two_pow_bits_length_le (K : ℕ) : 2^K.bits.length≤2*(K+1) := by
  rw [Nat.size_eq_bits_len]
  cases hs : K.size with
  | zero => simp only [pow_zero];omega
  | succ k =>
    have hp : 2^k≤K := Nat.lt_size.mp (by rw [hs];omega)
    rw [pow_succ]
    omega

/-- Exponential growth per gate is still polynomial in the unary search
budget, since every enumerated word has logarithmic length. -/
theorem matrix_height_budget (K : ℕ) :
    128^(K.bits.length+1)≤128*(2*(K+1))^7 := by
  have he : 128^K.bits.length=(2^K.bits.length)^7 := by
    rw [show (128 : ℕ)=2^7 by decide,←pow_mul,←pow_mul]
    congr 1
    omega
  rw [pow_succ,he,mul_comm]
  exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left (two_pow_bits_length_le K) 7)

end InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeFiniteGateNativeWord. -/
section P2MDyadicModule21

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

@[fun_prop] theorem natBits_poly : Poly (Nat.bits : ℕ→List Bool) := by
  exact ⟨BooleanLists.packProgram.recode Nat.bits (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem maxSteps_poly (a : ℕ) : Poly (maxSteps a) := by
  unfold maxSteps
  have hk : Poly (fun budget : List Unit => (FiniteGateNativeEnumeration.searchSlots a budget).length) :=
    Poly.comp Poly.list_length (FiniteGateNativeEnumeration.searchSlots_poly a)
  have hb := Poly.comp Poly.list_length (Poly.comp natBits_poly hk)
  simpa only [FiniteGateNativeEnumeration.searchSlots_length] using hb

attribute [local irreducible] matrixMul nativeGate maxSteps evalStep

theorem evalStep_poly (a : ℕ) : Poly (evalStep a) := by
  unfold evalStep
  have hbudget : Poly (fun x : EvalState×ℕ => x.1.1.1) :=
    Poly.comp Poly.fst (Poly.comp Poly.fst Poly.fst)
  have hcounter : Poly (fun x : EvalState×ℕ => x.1.1.2) :=
    Poly.comp Poly.snd (Poly.comp Poly.fst Poly.fst)
  have hmatrix : Poly (fun x : EvalState×ℕ => matrixMul (nativeGate x.2) x.1.2) :=
    Poly.comp matrixMul_poly (Poly.pair (Poly.comp nativeGate_poly Poly.snd) (Poly.comp Poly.snd Poly.fst))
  have hinc : Poly (fun x : EvalState×ℕ => x.1.1.2+1) :=
    Poly.comp (f:=fun p : ℕ×ℕ => p.1+p.2) (g:=fun x : EvalState×ℕ => (x.1.1.2,1))
      Poly.nat_add (Poly.pair hcounter (Automatic.Poly.const 1))
  have hnext : Poly (fun x : EvalState×ℕ =>
      ((x.1.1.1,x.1.1.2+1),matrixMul (nativeGate x.2) x.1.2)) :=
    Poly.pair (Poly.pair hbudget hinc) hmatrix
  exact Poly.ite_prop (Poly.nat_lt_comp hcounter (Poly.comp (maxSteps_poly a) hbudget)) hnext Poly.fst

theorem evalStep_budget (a : ℕ) (state : EvalState) (code : ℕ) :
    (evalStep a (state,code)).1.1=state.1.1 := by unfold evalStep;split <;> rfl

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeFiniteGateNativeBounded. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem MatrixHeight.mono {m : NativeMatrix} {L M : ℕ} (h : MatrixHeight m L) (hle : L≤ M) :
    MatrixHeight m M := by intro r c;exact (h r c).mono hle

def HeightInvariant (a H : ℕ) (state : EvalState) : Prop :=
  MatrixHeight state.2 (128^min state.1.2 (maxSteps a state.1.1)*(H+1))

attribute [local irreducible] ScalarHeight MatrixHeight matrixMul nativeGate maxSteps evalStep

theorem evalStep_height (a H : ℕ) (state : EvalState) (code : ℕ)
    (hstate : HeightInvariant a H state) : HeightInvariant a H (evalStep a (state,code)) := by
  by_cases h : state.1.2 < maxSteps a state.1.1
  · unfold HeightInvariant at hstate ⊢
    have hmin : min state.1.2 (maxSteps a state.1.1)=state.1.2 := Nat.min_eq_left h.le
    rw [hmin] at hstate
    have hp : 1≤128^state.1.2*(H+1) :=
      Nat.mul_pos (pow_pos (by decide : 0<128) _) (by omega)
    have hnext := matrixMul_left_gate_height hstate (nativeGate_height code) hp
    have he : 128*(128^state.1.2*(H+1))=128^(state.1.2+1)*(H+1) := by rw [pow_succ];ring
    rw [he] at hnext
    simp only [evalStep,if_pos h,Prod.fst,Prod.snd]
    rw [Nat.min_eq_left (by omega : state.1.2+1≤ maxSteps a state.1.1)]
    exact hnext
  · simpa only [evalStep,if_neg h] using hstate

theorem evalFold_height_invariant (a H : ℕ) (codes : List ℕ) (state : EvalState)
    (hstate : HeightInvariant a H state) : HeightInvariant a H (evalFold a codes state) := by
  induction codes generalizing state with
  | nil => exact hstate
  | cons code rest ih => exact ih _ (evalStep_height a H state code hstate)

theorem evalFold_budget (a : ℕ) (codes : List ℕ) (state : EvalState) :
    (evalFold a codes state).1.1=state.1.1 := by
  induction codes generalizing state with
  | nil => rfl
  | cons code rest ih =>
    change (evalFold a rest (evalStep a (state,code))).1.1=_
    rw [ih,evalStep_budget]

theorem evalStep_counter (a : ℕ) (state : EvalState) (code : ℕ) :
    (evalStep a (state,code)).1.2 ≤ max state.1.2 (maxSteps a state.1.1) := by
  by_cases h : state.1.2 < maxSteps a state.1.1
  · simp only [evalStep,if_pos h]
    exact (by omega : state.1.2+1≤ maxSteps a state.1.1).trans (le_max_right _ _)
  · simpa only [evalStep,if_neg h] using le_max_left state.1.2 (maxSteps a state.1.1)

theorem evalFold_counter (a : ℕ) (codes : List ℕ) (state : EvalState) :
    (evalFold a codes state).1.2 ≤ max state.1.2 (maxSteps a state.1.1) := by
  induction codes generalizing state with
  | nil => exact le_max_left _ _
  | cons code rest ih =>
    change (evalFold a rest (evalStep a (state,code))).1.2≤ _
    have hh := ih (evalStep a (state,code))
    rw [evalStep_budget] at hh
    exact hh.trans (max_le (evalStep_counter a state code) (le_max_right _ _))

theorem evalFold_height (a : ℕ) (codes : List ℕ) (state : EvalState) :
    MatrixHeight (evalFold a codes state).2
      (128^(maxSteps a state.1.1+1)*((enc state.2).length+1)) := by
  let H := (enc state.2).length
  have hinit : HeightInvariant a H state := by
    unfold HeightInvariant
    apply (matrix_encoding_height state.2).mono
    have hp : 1≤128^min state.1.2 (maxSteps a state.1.1) := Nat.one_le_pow _ _ (by decide)
    have hm := Nat.mul_le_mul_right (H+1) hp
    omega
  have hh := evalFold_height_invariant a H codes state hinit
  unfold HeightInvariant at hh
  rw [evalFold_budget] at hh
  exact hh.mono (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega)))

theorem evalFold_height_budget (a : ℕ) (codes : List ℕ) (state : EvalState) :
    MatrixHeight (evalFold a codes state).2
      (128*(2*(13^(a+1)*(state.1.1.length+1)^(4*a)+1))^7*((enc state.2).length+1)) := by
  have hh := evalFold_height a codes state
  apply hh.mono
  have hb := FiniteGateNativeEnumeration.matrix_height_budget (13^(a+1)*(state.1.1.length+1)^(4*a))
  simpa only [maxSteps] using Nat.mul_le_mul_right ((enc state.2).length+1) hb

theorem bits_length_le (n : ℕ) : n.bits.length≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem evalFold_counter_bits (a : ℕ) (codes : List ℕ) (state : EvalState) :
    (evalFold a codes state).1.2.bits.length ≤ state.1.2.bits.length+maxSteps a state.1.1+1 := by
  have hc := evalFold_counter a codes state
  have hle : (evalFold a codes state).1.2≤ state.1.2+maxSteps a state.1.1 := by omega
  have h1 := NatBinary.length_mono hle
  have h2 := NatBinary.add_length state.1.2 (maxSteps a state.1.1)
  have h3 := bits_length_le (maxSteps a state.1.1)
  omega

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeFiniteGateNativeWordPoly. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Polynomial

theorem evalState_encoding_length (state : EvalState) :
    (enc state).length=4*(enc state.1.1).length+2*state.1.2.bits.length+(enc state.2).length+3 := by
  change (encodePair (encodePair enc Nat.bits) enc state).length=_
  simp only [encodePair_length]
  omega

noncomputable def wordStateBudget (a : ℕ) : Polynomial ℕ :=
  let K : Polynomial ℕ := Polynomial.C (13^(a+1))*(Polynomial.X+1)^(4*a)
  10*(Polynomial.X+1)+4*K+32768*(128*(2*(K+1))^7*(Polynomial.X+1)+1)

theorem wordState_bound (a : ℕ) (codes : List ℕ) (state : EvalState)
    (pre suffix : List ℕ) (_hcodes : codes=pre++suffix) :
    (enc (evalFold a pre state)).length≤
      (wordStateBudget a).eval (encodePair (encodeList Nat.bits) enc (codes,state)).length := by
  let S := (encodePair (encodeList Nat.bits) enc (codes,state)).length
  let K := 13^(a+1)*(S+1)^(4*a)
  have hstate : (enc state).length≤ S := by
    change (enc state).length≤(encodePair (encodeList Nat.bits) enc (codes,state)).length
    simp only [encodePair_length,Prod.fst,Prod.snd]
    omega
  have hs := evalState_encoding_length state
  have hbudget : state.1.1.length≤ S := by
    have hb := EncodedList.length_le (fun _ : Unit => []) state.1.1
    change state.1.1.length≤(enc state.1.1).length at hb
    omega
  have hcounter : state.1.2.bits.length≤ S := by omega
  have hmatrix : (enc state.2).length≤ S := by omega
  have hK : 13^(a+1)*(state.1.1.length+1)^(4*a)≤ K :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hlimit : maxSteps a state.1.1≤ K := by
    have hh := bits_length_le (13^(a+1)*(state.1.1.length+1)^(4*a))
    exact hh.trans hK
  have hp : 128*(2*(13^(a+1)*(state.1.1.length+1)^(4*a)+1))^7≤128*(2*(K+1))^7 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hheight := (evalFold_height_budget a pre state).mono
    (Nat.mul_le_mul hp (by omega : (enc state.2).length+1≤ S+1))
  have hencoded := matrix_encoding_length hheight
  have hcount := evalFold_counter_bits a pre state
  have hstateout := evalState_encoding_length (evalFold a pre state)
  rw [evalFold_budget] at hstateout
  have heval : (wordStateBudget a).eval S=
      10*(S+1)+4*K+32768*(128*(2*(K+1))^7*(S+1)+1) := by
    simp only [wordStateBudget,K,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  change _≤(wordStateBudget a).eval S
  rw [heval]
  omega

noncomputable def evalFoldProgram (a : ℕ) : PolyProgram enc enc
    (fun x : List ℕ×EvalState => evalFold a x.1 x.2) :=
  (evalStep_poly a).program.listFold 0 (wordStateBudget a) (wordState_bound a)

theorem evalFold_poly (a : ℕ) : Poly (fun x : List ℕ×EvalState => evalFold a x.1 x.2) :=
  ⟨evalFoldProgram a⟩

theorem boundedMatrix_poly (a : ℕ) : Poly (boundedMatrix a) := by
  unfold boundedMatrix
  have hinit : Poly (fun x : List Unit×List ℕ => (x.2,((x.1,0),identityMatrix))) :=
    Poly.pair Poly.snd (Poly.pair (Poly.pair Poly.fst (Automatic.Poly.const 0))
      (Automatic.Poly.const identityMatrix))
  exact Poly.comp Poly.snd (Poly.comp (evalFold_poly a) hinit)

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeFiniteGateNativePredicate. -/
section P2MDyadicModule24
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

theorem sumReal_poly {α ι : Type} [Coding α] (indices : List ι) (f : α→ι→RealPair)
    (hf : ∀ i∈indices,Poly (fun x => f x i)) : Poly (fun x => sumReal indices (f x)) := by
  induction indices with
  | nil => exact Automatic.Poly.const (0,0)
  | cons i rest ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun x => addReal (f x i) (sumReal rest (f x)))
    exact Poly.comp addReal_poly (Poly.pair hi ht)

@[fun_prop] theorem rectangleError_poly : Poly (fun x : NativeMatrix×NativeMatrix => rectangleError x.1 x.2) := by
  apply sumReal_poly
  intro row _
  apply sumReal_poly
  intro column _
  exact Poly.comp normSq_poly (Poly.comp sub_poly (Poly.pair
    (Poly.comp (matrix_entry_poly row (initializedColumn column)) Poly.fst)
    (Poly.comp (matrix_entry_poly row (initializedColumn column)) Poly.snd)))

attribute [local irreducible] accepts rectangleError leRational

theorem accepts_poly :
    Poly (fun x : (NativeMatrix×NativeMatrix)×ℚ => accepts x.1.1 x.1.2 x.2) := by
  have ht : Poly (fun x : (NativeMatrix×NativeMatrix)×ℚ => x.2*x.2) :=
    Poly.comp Poly.rat_mul (Poly.pair Poly.snd Poly.snd)
  have h : Poly (fun x : (NativeMatrix×NativeMatrix)×ℚ =>
      leRational (rectangleError x.1.1 x.1.2) (x.2*x.2)) :=
    Poly.comp (f:=fun y : RealPair×ℚ => leRational y.1 y.2)
      leRational_poly (Poly.pair (Poly.comp rectangleError_poly Poly.fst) ht)
  simpa only [accepts,pow_two] using h

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeFiniteGateNativeCompiler. -/
section P2MDyadicModule25

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

attribute [local irreducible] accepts boundedMatrix compilerTest

theorem compilerTest_poly (a : ℕ) : Poly (compilerTest a) := by
  unfold compilerTest
  have hbudget : Poly (fun x : CompileRequest×List ℕ => x.1.1.1) :=
    Poly.comp Poly.fst (Poly.comp Poly.fst Poly.fst)
  have htarget : Poly (fun x : CompileRequest×List ℕ => x.1.1.2) :=
    Poly.comp Poly.snd (Poly.comp Poly.fst Poly.fst)
  have htolerance : Poly (fun x : CompileRequest×List ℕ => x.1.2) := Poly.comp Poly.snd Poly.fst
  have hword : Poly (fun x : CompileRequest×List ℕ => boundedMatrix a (x.1.1.1,x.2)) :=
    Poly.comp (boundedMatrix_poly a) (Poly.pair hbudget Poly.snd)
  exact Poly.comp accepts_poly (Poly.pair (Poly.pair hword htarget) htolerance)

theorem compileWord_poly (a : ℕ) : Poly (compileWord a) := by
  have hc : Poly (fun request : CompileRequest => FiniteGateNativeEnumeration.search a request.1.1) :=
    Poly.comp (FiniteGateNativeEnumeration.search_poly a) (Poly.comp Poly.fst Poly.fst)
  have hi : Poly (fun request : CompileRequest =>
      (FiniteGateNativeEnumeration.search a request.1.1).findIdx (fun codes => compilerTest a (request,codes))) :=
    Poly.list_findIdx (compilerTest_poly a) hc
  exact Poly.list_getD_comp [] hc hi

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeFiniteGateNativeGuarantee. -/
section P2MDyadicModule26
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

@[fun_prop] theorem compilerTolerance_poly : Poly compilerTolerance := by unfold compilerTolerance;fun_prop

attribute [local irreducible] compileWord nativeCompile compilerTolerance

theorem nativeCompile_poly (a : ℕ) : Poly (nativeCompile a) := by
  unfold nativeCompile
  exact Poly.comp (compileWord_poly a) (Poly.pair Poly.identity (Poly.comp compilerTolerance_poly Poly.fst))

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeNativePhaseTaylor. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativePhaseTaylor

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeFiniteSeries

open FiniteGateNative FiniteGateTransport

open scoped BigOperators

@[local fun_prop] private theorem cappedTaylor_poly : Poly cappedTaylor := ⟨taylorTermProgram⟩

@[local fun_prop] private theorem natMod_poly : Poly (fun x : ℕ×ℕ => x.1%x.2) := ⟨PolyProgram.natMod⟩

@[local fun_prop] private theorem ratSum_poly : Poly (List.sum : List ℚ → ℚ) := ⟨PolyProgram.ratSum⟩

@[fun_prop] theorem termValue_poly : Poly termValue := by unfold termValue;fun_prop

@[fun_prop] theorem realTerm_poly : Poly realTerm := by unfold realTerm;fun_prop

@[fun_prop] theorem imagTerm_poly : Poly imagTerm := by unfold imagTerm;fun_prop

@[fun_prop] theorem realSum_poly : Poly realSum := by
  have hindices : Poly (fun x : Input => List.range x.2.length) := Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=fun x : Input => x.2) Poly.list_indices Poly.snd
  unfold realSum
  apply Poly.comp ratSum_poly
  exact Poly.list_map (Poly.comp realTerm_poly (by fun_prop)) hindices

@[fun_prop] theorem imagSum_poly : Poly imagSum := by
  have hindices : Poly (fun x : Input => List.range x.2.length) := Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=fun x : Input => x.2) Poly.list_indices Poly.snd
  unfold imagSum
  apply Poly.comp ratSum_poly
  exact Poly.list_map (Poly.comp imagTerm_poly (by fun_prop)) hindices

@[fun_prop] theorem base_poly : Poly base := by unfold base;fun_prop

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

@[local fun_prop] private theorem pi_poly : Poly (fun ticks : List Unit => AFT.RationalNumerics.piApprox ticks.length) :=
  ⟨piProgram⟩

@[local fun_prop] private theorem power_poly : Poly powerValue := ⟨powerProgram⟩

@[fun_prop] theorem angle_poly : Poly angle := by
  have hp : Poly (fun x : QFTRequest => AFT.RationalNumerics.piApprox x.1.1.length) :=
    Poly.comp (f:=fun ticks : List Unit => AFT.RationalNumerics.piApprox ticks.length)
      (g:=fun x : QFTRequest => x.1.1) pi_poly (by fun_prop)
  unfold angle
  fun_prop

@[fun_prop] theorem signedAngle_poly : Poly signedAngle := by unfold signedAngle;fun_prop

@[fun_prop] theorem qftCurrent_poly : Poly qftCurrent := by unfold qftCurrent;fun_prop

end InfoLossLAR.WorstCase.NativePhaseTaylor

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeNativePhaseGates. -/
section P2MDyadicModule28
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativePhaseGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport FiniteGateNative

@[fun_prop] theorem target_poly : Poly target := by
  apply matrix_build_poly
  intro row _ col _
  unfold target singleGate coefficient
  by_cases h : col=Function.update row 0 (col 0)
  · simp only [if_pos h]
    cases row 0 <;> cases col 0 <;> simp only [Bool.false_eq_true,Bool.true_eq_false,if_false,if_true] <;> fun_prop
  · simp only [if_neg h]
    exact Automatic.Poly.const _

attribute [local irreducible] nativeCompile current target

theorem current_poly (a : ℕ) : Poly (current a) := by
  unfold current
  exact Poly.comp (nativeCompile_poly a) (Poly.pair Poly.fst (Poly.comp target_poly Poly.snd))

@[fun_prop] theorem termBudget_poly : Poly termBudget := by
  unfold termBudget
  exact Poly.list_flatMap (Automatic.Poly.const _) (by fun_prop)

@[fun_prop] theorem request_poly : Poly request := by unfold request;fun_prop

theorem automatic_poly (a : ℕ) : Poly (automatic a) := by
  unfold automatic
  exact Poly.comp (current_poly a) (Poly.pair Poly.fst request_poly)

end InfoLossLAR.WorstCase.NativePhaseGates

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeFreshPhaseRelocation. -/
section P2MDyadicModule29

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity

open scoped BigOperators

def prefixInstr {n : ℕ} : Instr n → Instr (n+2)
  | .h i => .h (i.castAdd 2)
  | .s i => .s (i.castAdd 2)
  | .t i => .t (i.castAdd 2)
  | .x i => .x (i.castAdd 2)
  | .cnot i j h => .cnot (i.castAdd 2) (j.castAdd 2) (by intro he;apply h;exact Fin.castAdd_inj.mp he)

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeControlledHadamard. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option maxHeartbeats 2400000

namespace InfoLossLAR.WorstCase.ControlledHadamard

open QAlgorithms QAlgorithms.Complexity

open FiniteGateNative

def turnWord {n : ℕ} (t : Fin n) : List (Instr n) :=
  [.h t]++List.replicate 3 (.s t)++[.h t,.t t,.h t,.s t]

/-- A fixed exact native gate sequence for controlled Hadamard. -/
def gates {n : ℕ} (c t : Fin n) (hct : c≠t) : List (Instr n) :=
  inverseGates (turnWord t)++[.cnot c t hct]++turnWord t

end InfoLossLAR.WorstCase.ControlledHadamard

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeControlledLetterPlan. -/
section P2MDyadicModule31

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ControlledLetterPlan

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

/-- Only the fixed public eighth-turn phase remains to be synthesized. -/
inductive Atom (n : ℕ) where
  | native (gate : Instr n)
  | eighth (i : Fin n) (negative : Bool)

def Avoids {n : ℕ} (c : Fin n) : Letter n → Prop
  | .h i => c≠i
  | .t i => c≠i
  | .cnot i j _ => c≠i ∧ c≠j

def plan {n : ℕ} (c : Fin n) (gate : Letter n) (h : Avoids c gate) : List (Atom n) :=
  match gate with
  | .h i => (ControlledHadamard.gates c i h).map Atom.native
  | .t i => [.eighth c false,.eighth i false,.native (.cnot c i h),.eighth i true,.native (.cnot c i h)]
  | .cnot i j hij => (toffoliGates c i j h.1 h.2 hij).map Atom.native

end InfoLossLAR.WorstCase.ControlledLetterPlan

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeControlledNativeCode. -/
section P2MDyadicModule32

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledNativeCode

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def encodeAtom {n : ℕ} : ControlledLetterPlan.Atom n → AtomCode
  | .native g => (encodeInstr g,false)
  | .eighth i negative => ((5,i.val,0),negative)

theorem decode_encode {n : ℕ} (g : Instr n) : decodeGate n (encodeInstr g)=some g := by
  cases g with
  | h i => simp [encodeInstr,decodeGate,i.isLt]
  | s i => simp [encodeInstr,decodeGate,i.isLt]
  | t i => simp [encodeInstr,decodeGate,i.isLt]
  | x i => simp [encodeInstr,decodeGate,i.isLt]
  | cnot i j h =>
    have hv : i.val≠j.val := by intro he;exact h (Fin.ext he)
    simp [encodeInstr,decodeGate,i.isLt,j.isLt,hv]

theorem localCode_eq (code : ℕ) :
    localCode code=encodeInstr (FiniteGateNativeEnumeration.letterOfCode code).toInstr := by
  unfold localCode localTable FiniteGateNativeEnumeration.letterOfCode
  rw [List.getElem?_map]
  cases alphabet[code]? <;> rfl

@[fun_prop] theorem localCode_poly : Poly localCode := by
  exact Poly.list_getD_comp (0,0,0) (Automatic.Poly.const localTable) Poly.identity

@[fun_prop] theorem address_poly : Poly (fun x : Layout×ℕ => address x.1 x.2) := by
  unfold address
  fun_prop

@[fun_prop] theorem relocateCode_poly : Poly (fun x : Layout×GateCode => relocateCode x.1 x.2) := by
  unfold relocateCode
  fun_prop

theorem address_layout {m : ℕ} (w : Fin 3 ↪ Fin m) (i : Fin 3) :
    address ((w 0).val,(w 1).val,(w 2).val) i.val=(w i).val := by
  fin_cases i <;> rfl

theorem relocateCode_encode {m : ℕ} (w : Fin 3 ↪ Fin m) (letter : Letter 3) :
    relocateCode ((w 0).val,(w 1).val,(w 2).val) (encodeInstr letter.toInstr)=
      encodeInstr (letter.relocate w).toInstr := by
  cases letter with
  | h i => simp [relocateCode,encodeInstr,Letter.toInstr,Letter.relocate,address_layout]
  | t i => simp [relocateCode,encodeInstr,Letter.toInstr,Letter.relocate,address_layout]
  | cnot i j h => simp [relocateCode,encodeInstr,Letter.toInstr,Letter.relocate,address_layout]

attribute [local irreducible] localCode relocateCode NativePhaseGates.automatic

@[fun_prop] theorem phaseCodes_poly (a : ℕ) : Poly (phaseCodes a) := by
  unfold phaseCodes
  apply Poly.list_map
  · exact Poly.comp relocateCode_poly (Poly.pair (by fun_prop) (Poly.comp localCode_poly Poly.snd))
  · exact Poly.comp (NativePhaseGates.automatic_poly a) (by fun_prop)

theorem phaseCodes_semantics (a : ℕ) (budget : List Unit) {m : ℕ}
    (w : Fin 3 ↪ Fin m) (negative : Bool) :
    phaseCodes a ((budget,((w 0).val,(w 1).val,(w 2).val)),negative)=
      (instructions ((FiniteGateNativeEnumeration.interpreted
        (NativePhaseGates.automatic a (budget,([(),()],negative)))).map (Letter.relocate w))).map encodeInstr := by
  simp only [phaseCodes,FiniteGateNativeEnumeration.interpreted,instructions,List.map_map]
  apply List.map_congr_left
  intro code _
  rw [localCode_eq,relocateCode_encode]
  rfl

@[fun_prop] theorem atomCodes_poly (a : ℕ) : Poly (atomCodes a) := by unfold atomCodes;fun_prop

theorem compile_poly (a : ℕ) : Poly (compile a) := by unfold compile;fun_prop

end InfoLossLAR.WorstCase.ControlledNativeCode

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeControlledNativeGates. -/
section P2MDyadicModule33

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledNativeGates

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan

open scoped BigOperators

def eighthWord (a : ℕ) (budget : List Unit) (negative : Bool) : List (Letter 3) :=
  FiniteGateNativeEnumeration.interpreted (NativePhaseGates.automatic a (budget,([(),()],negative)))

def atomGates (a : ℕ) (budget : List Unit) {n : ℕ} : Atom n → List (Instr (n+2))
  | .native gate => [prefixInstr gate]
  | .eighth i negative => instructions ((eighthWord a budget negative).map (Letter.relocate (freshPhaseWires i)))

def gates (a : ℕ) (budget : List Unit) {n : ℕ} (atoms : List (Atom n)) : List (Instr (n+2)) :=
  atoms.flatMap (atomGates a budget)

theorem atom_codes {n : ℕ} (a : ℕ) (budget : List Unit) (atom : Atom n) :
    ControlledNativeCode.atomCodes a ((budget,(n,n+1)),ControlledNativeCode.encodeAtom atom)=
      (atomGates a budget atom).map ControlledNativeCode.encodeInstr := by
  cases atom with
  | native gate =>
    cases gate <;> rfl
  | eighth i negative =>
    exact ControlledNativeCode.phaseCodes_semantics a budget (freshPhaseWires i) negative

theorem gates_codes {n : ℕ} (a : ℕ) (budget : List Unit) (atoms : List (Atom n)) :
    ControlledNativeCode.compile a ((budget,(n,n+1)),atoms.map ControlledNativeCode.encodeAtom)=
      (gates a budget atoms).map ControlledNativeCode.encodeInstr := by
  simp only [ControlledNativeCode.compile,gates,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro atom _
  exact atom_codes a budget atom

end InfoLossLAR.WorstCase.ControlledNativeGates

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeCoherentProjection. -/
section P2MDyadicModule34

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentProjection

open scoped BigOperators

theorem normalized_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : v≠0) : ‖normalized v‖=1 := by
  rw [normalized,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

theorem normalized_distance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : v≠0) : ‖normalized v-v‖=|1-‖v‖| := by
  have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  rw [normalized,show ‖v‖⁻¹ • v-v=(‖v‖⁻¹-1) • v by rw [sub_smul,one_smul],
    norm_smul,Real.norm_eq_abs]
  rw [←abs_of_nonneg (norm_nonneg v),←abs_mul]
  congr 1
  rw [abs_of_nonneg (norm_nonneg v)]
  field_simp

theorem normalized_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (hu : ‖u‖=1) (hv : v≠0) : ‖u-normalized v‖≤2*‖u-v‖ := by
  have h := abs_norm_sub_norm_le u v
  rw [hu] at h
  have hn := normalized_distance v hv
  calc
    _ ≤ ‖u-v‖+‖v-normalized v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖u-v‖+|1-‖v‖| := by rw [norm_sub_rev v (normalized v),hn]
    _ ≤ _ := by linarith

theorem tensorState_norm {O J : Type*} [Fintype O] [Fintype J]
    (target : EuclideanSpace ℂ O) (junk : EuclideanSpace ℂ J) :
    ‖tensorState target junk‖=‖target‖*‖junk‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  simp only [tensorState,Fintype.sum_prod_type,norm_mul,mul_pow]
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul]

end InfoLossLAR.WorstCase.CoherentProjection

end P2MDyadicModule34

/- Helper module Spectator. -/
section P2MDyadicModule35

set_option autoImplicit false

set_option maxHeartbeats 850000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.StageRegisters

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates

noncomputable section

variable {k N : ℕ}

def attach (w : Fin k ↪ Fin N) (φ : QState k) (j : OutsideBits w → ℂ) : QState N :=
  fun x => φ ((wireBitsEquiv w x).1)*j ((wireBitsEquiv w x).2)

@[simp] theorem split_attach (w : Fin k ↪ Fin N) (φ : QState k) (j : OutsideBits w → ℂ) :
    splitState w (attach w φ j)=fun p => φ p.1*j p.2 := by
  funext p; simp [splitState,attach]

theorem attach_norm (w : Fin k ↪ Fin N) (φ : QState k) (j : OutsideBits w→ℂ)
    (hj : ∑ r, ‖j r‖^2=1) : stateNorm (attach w φ j)=stateNorm φ := by
  have he : ∑ x, ‖attach w φ j x‖^2=∑ x, ‖φ x‖^2 := by
    calc _ = ∑ p : Bits k × OutsideBits w, ‖φ p.1 * j p.2‖^2 :=
            Fintype.sum_equiv (wireBitsEquiv w) _ _ (fun _ => rfl)
         _ = _ := by simp only [Fintype.sum_prod_type,norm_mul,mul_pow,←Finset.mul_sum,hj,mul_one]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [stateNorm,EuclideanSpace.norm_sq_eq] using he

theorem attach_dist (w : Fin k ↪ Fin N) (φ χ : QState k) (j : OutsideBits w→ℂ)
    (hj : ∑ r, ‖j r‖^2=1) : stateNorm (attach w φ j-attach w χ j)=stateNorm (φ-χ) := by
  rw [show attach w φ j-attach w χ j=attach w (φ-χ) j by ext x;simp [attach,sub_mul]]
  exact attach_norm w _ _ hj

theorem run_attach (w : Fin k ↪ Fin N) (c : Layered k) (φ : QState k) (j : OutsideBits w→ℂ) :
    runLayered (relocateCircuit w c) (attach w φ j)=attach w (runLayered c φ) j := by
  funext x
  let p := wireBitsEquiv w x
  have he := congrFun (relocateCircuit_split w c (attach w φ j)) p
  rw [split_attach] at he
  have hs : (fun y => φ y*j p.2)=(j p.2) • φ := by ext t;simp [mul_comm]
  change runLayered (relocateCircuit w c) (attach w φ j) ((wireBitsEquiv w).symm ((wireBitsEquiv w) x))=_ at he
  rw [Equiv.symm_apply_apply,hs] at he
  rw [he,←runLayeredLinearMap_apply,map_smul]
  simp [attach,p,mul_comm,runLayeredLinearMap_apply]

theorem propagate (w : Fin k ↪ Fin N) (c : Layered k) (φ χ : QState k) (j : OutsideBits w→ℂ)
    (hj : ∑ r, ‖j r‖^2=1) (actual : QState N) (ε δ : ℝ)
    (hε : stateNorm (actual-attach w φ j)≤ ε) (hδ : stateNorm (runLayered c φ-χ)≤δ) :
    stateNorm (runLayered (relocateCircuit w c) actual-attach w χ j) ≤ ε+δ := by
  let V := relocateCircuit w c
  have he : stateNorm (runLayered V actual-runLayered V (attach w φ j))=stateNorm (actual-attach w φ j) :=
    (show ‖(circuitIsometry V) (WithLp.toLp 2 actual) - (circuitIsometry V) (WithLp.toLp 2 (attach w φ j))‖=_ from
      by rw [←map_sub,(circuitIsometry V).norm_map];rfl)
  have hd : stateNorm (runLayered V (attach w φ j)-attach w χ j)≤δ := by
    rw [run_attach,attach_dist w _ _ j hj];exact hδ
  have h := norm_sub_le_norm_sub_add_norm_sub (WithLp.toLp 2 (runLayered V actual))
    (WithLp.toLp 2 (runLayered V (attach w φ j))) (WithLp.toLp 2 (attach w χ j))
  exact h.trans (add_le_add (he.le.trans hε) hd)

end

end InfoLossLAR.WorstCase.RegevSearch.StageRegisters

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeControlledPlanNative. -/
section P2MDyadicModule36

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledPlanNative

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem inverseCode_poly : Poly inverseCode := by unfold inverseCode;fun_prop

@[fun_prop] theorem turnCodes_poly : Poly turnCodes := by unfold turnCodes;fun_prop

@[fun_prop] theorem inverseTurnCodes_poly : Poly inverseTurnCodes := by
  unfold inverseTurnCodes
  have hr : Poly (fun target => (turnCodes target).reverse) :=
    Poly.comp QMCNumericRuntime.parser_reverse_poly turnCodes_poly
  exact Poly.list_flatMap (Poly.comp inverseCode_poly Poly.snd) hr

@[fun_prop] theorem hPlan_poly : Poly (fun x : ℕ×ℕ => hPlan x.1 x.2) := by unfold hPlan;fun_prop

@[fun_prop] theorem tPlan_poly : Poly (fun x : ℕ×ℕ => tPlan x.1 x.2) := by unfold tPlan;fun_prop

@[fun_prop] theorem cnotPlan_poly : Poly (fun x : ℕ×ℕ×ℕ => cnotPlan x.1 x.2.1 x.2.2) := by unfold cnotPlan;fun_prop

@[fun_prop] theorem gatePlan_poly : Poly (fun x : ℕ×GateCode => gatePlan x.1 x.2) := by
  unfold gatePlan
  fun_prop

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

theorem inverseCode_encode {n : ℕ} (gate : Instr n) :
    inverseCode (encodeInstr gate)=(inverseInstr gate).map encodeInstr := by cases gate <;> rfl

theorem turnCodes_encode {n : ℕ} (target : Fin n) :
    turnCodes target.val=(ControlledHadamard.turnWord target).map encodeInstr := rfl

theorem inverseTurnCodes_encode {n : ℕ} (target : Fin n) :
    inverseTurnCodes target.val=(inverseGates (ControlledHadamard.turnWord target)).map encodeInstr := by
  simp only [inverseTurnCodes,turnCodes_encode,←List.map_reverse,List.flatMap_map,
    inverseCode_encode,inverseGates]
  rw [←List.map_flatMap]

theorem hPlan_encode {n : ℕ} (control target : Fin n) (h : control≠target) :
    hPlan control.val target.val=(plan control (.h target) h).map encodeAtom := by
  simp only [hPlan,inverseTurnCodes_encode,turnCodes_encode,plan,ControlledHadamard.gates,
    List.map_append,List.map_map,List.map_cons,List.map_nil,Function.comp_def,encodeAtom,encodeInstr]

theorem tPlan_encode {n : ℕ} (control target : Fin n) (h : control≠target) :
    tPlan control.val target.val=(plan control (.t target) h).map encodeAtom := rfl

theorem cnotPlan_encode_exact {n : ℕ} (control i j : Fin n) (hij : i≠j)
    (h : Avoids control (.cnot i j hij)) :
    cnotPlan control.val i.val j.val=(plan control (.cnot i j hij) h).map encodeAtom := rfl

theorem gatePlan_encode {n : ℕ} (control : Fin n) (letter : Letter n) (h : Avoids control letter) :
    gatePlan control.val (encodeInstr letter.toInstr)=(plan control letter h).map encodeAtom := by
  cases letter with
  | h i => simpa only [Letter.toInstr,encodeInstr,gatePlan,ite_true] using hPlan_encode control i h
  | t i => simpa [Letter.toInstr,encodeInstr,gatePlan] using tPlan_encode control i h
  | cnot i j hij => simpa [Letter.toInstr,encodeInstr,gatePlan] using cnotPlan_encode_exact control i j hij h

def ControlFresh {n : ℕ} (control : Fin n) (data : Fin 3 ↪ Fin n) : Prop :=
  ∀ i,control≠data i

theorem relocated_avoids {n : ℕ} (control : Fin n) (data : Fin 3 ↪ Fin n)
    (h : ControlFresh control data) (letter : Letter 3) : Avoids control (letter.relocate data) := by
  cases letter with
  | h i => exact h i
  | t i => exact h i
  | cnot i j hij => exact ⟨h i,h j⟩

theorem current_encode {n : ℕ} (control : Fin n) (data : Fin 3 ↪ Fin n)
    (h : ControlFresh control data) (code : ℕ) :
    current (control.val,(((data 0).val,(data 1).val,(data 2).val),code))=
      (plan control ((FiniteGateNativeEnumeration.letterOfCode code).relocate data)
        (relocated_avoids control data h _)).map encodeAtom := by
  unfold current
  rw [localCode_eq,relocateCode_encode]
  exact gatePlan_encode control _ _

end InfoLossLAR.WorstCase.ControlledPlanNative

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeBooleanUniform. -/
section P2MDyadicModule37

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readBooleanInstruction_poly : Poly readBooleanInstruction := by
  unfold readBooleanInstruction
  fun_prop

theorem readBooleanInstruction_rest_length (xs : Str) :
    (readBooleanInstruction xs).1.length ≤ xs.length := by
  unfold readBooleanInstruction
  dsimp only
  split_ifs <;>
    first
      | exact (readUnary_rest_length _).trans (readUnary_rest_length _)
      | exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
      | exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans
          ((readUnary_rest_length _).trans (readUnary_rest_length _)))

private theorem unaryWidth_append (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs

private theorem unaryWidth (n : ℕ) : inputWidth (encNat n) = n := by
  simpa using unaryWidth_append n []

theorem readBooleanInstruction_append {n : ℕ} (g : BooleanGate n) (xs : Str) :
    readBooleanInstruction (g.code ++ xs) = (xs, g.compile.map ReversibleGate.code) := by
  cases g with
  | constant t b =>
    cases b <;> simp only [BooleanGate.code, Bool.false_eq_true, ite_false, ite_true,
      readBooleanInstruction, List.append_assoc, readUnary_append, unaryWidth_append] <;> norm_num <;> rfl
  | copy s t h =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | negate s t h =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | xor a b t ha hb =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
        unaryWidth_append, unaryWidth, BooleanGate.compile, ReversibleGate.code]
    · have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simp [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
        unaryWidth_append, unaryWidth, BooleanGate.compile, ReversibleGate.code, hab, habv]

@[fun_prop] theorem readBooleanProgram_poly : Poly readBooleanProgram :=
  readList_poly readBooleanInstruction readBooleanInstruction_poly readBooleanInstruction_rest_length

theorem readBooleanProgram_append {n : ℕ} (gates : List (BooleanGate n)) (xs : Str) :
    readBooleanProgram (encStr (gates.map BooleanGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.map ReversibleGate.code)) :=
  readList_append_mapped readBooleanInstruction BooleanGate.code
    (fun g => g.compile.map ReversibleGate.code) readBooleanInstruction_append gates xs

@[fun_prop] theorem compileBooleanDescription_poly : Poly compileBooleanDescription := by
  unfold compileBooleanDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem compileBooleanDescription_code (F : BooleanFamily) (n : ℕ) :
    compileBooleanDescription (F.code n) = F.reversible.code n := by
  unfold BooleanFamily.code compileBooleanDescription
  simp only [List.append_assoc, readUnary_append]
  have h := readBooleanProgram_append (F.gates n) []
  simp only [List.append_nil] at h
  rw [h, serializeWords_eq]
  have hh : (List.map (fun g => List.map ReversibleGate.code g.compile) (F.gates n)).flatten =
      (booleanToReversible (F.gates n)).map ReversibleGate.code := by
    simp only [booleanToReversible, List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def]
  rw [hh]
  simp only [ReversibleFamily.code, BooleanFamily.reversible, List.append_assoc]

end InfoLossLAR.WorstCase

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule38

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

namespace BooleanOp

theorem toGate_target {total : ℕ} (op : BooleanOp) (target : Fin total) :
    (op.toGate target).target = target := by
  cases op <;> simp only [toGate] <;> (try split_ifs) <;> rfl

theorem toGate_value {total : ℕ} (op : BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).value (fun i => s i.val) = op.eval s := by
  cases op <;> simp_all [Valid, sources, toGate, BooleanGate.value, eval]

theorem toGate_assign {total : ℕ} (op : BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).assign (fun i => s i.val) = fun i => op.assign target.val s i.val := by
  funext i
  rw [BooleanGate.assign, toGate_target, toGate_value op target hv]
  by_cases hi : i = target
  · subst i; simp [assign]
  · have hval : i.val ≠ target.val := fun h => hi (Fin.ext h)
    simp [assign, Function.update_of_ne hi, Function.update_of_ne hval]

end BooleanOp

namespace BooleanProgram

theorem target_range {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (g : BooleanGate total) (hg : g ∈ gates start ops h) :
    start ≤ g.target.val ∧ g.target.val < start + ops.length := by
  induction ops generalizing start with
  | nil => simp [gates] at hg
  | cons op rest ih =>
    simp only [gates, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [BooleanOp.toGate_target, List.length_cons]; omega
    · have hh := ih (start := start + 1) _ hg
      simp only [List.length_cons]; omega

theorem fresh {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) : BooleanFresh (gates start ops h) := by
  induction ops generalizing start with
  | nil => exact List.Pairwise.nil
  | cons op rest ih =>
    apply List.pairwise_cons.2
    constructor
    · intro g hg heq
      have hh := (target_range rest _ g hg).1
      rw [BooleanOp.toGate_target] at heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_mk] at hv
      omega
    · exact ih _

theorem run_below (start : ℕ) (ops : List BooleanOp) (s : ℕ → Bool)
    (i : ℕ) (hi : i < start) : run start ops s i = s i := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    rw [run, ih (start + 1) (op.assign start s) (by omega)]
    exact Function.update_of_ne (by omega) _ _

theorem run_append (start : ℕ) (a b : List BooleanOp) (s : ℕ → Bool) :
    run start (a ++ b) s = run (start + a.length) b (run start a s) := by
  induction a generalizing start s with
  | nil => simp [run]
  | cons op a ih =>
    simp only [List.cons_append, run, ih, List.length_cons]
    rw [show start + 1 + a.length = start + (a.length + 1) by omega]

theorem semantics {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool) :
    booleanRun (gates start ops h) (fun i => s i.val) = fun i => run start ops s i.val := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    change booleanRun (gates (start + 1) rest _) ((op.toGate _).assign (fun i => s i.val)) = _
    rw [BooleanOp.toGate_assign op _ hv.1, ih _ hv.2]
    rfl

theorem reversible_semantics {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    reversibleAction (booleanToReversible (gates start ops h)) (fun i => s i.val) =
      fun i => run start ops s i.val := by
  rw [booleanToReversible_action _ (fresh ops h)]
  · exact semantics ops h hv s
  · intro g hg
    obtain ⟨hl, hu⟩ := target_range ops h g hg
    exact hz _ hl hu

/-- The literal Clifford+T implementation has exactly the fresh-program basis semantics. -/
theorem circuit_basis {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    runLayered (compileReversible (booleanToReversible (gates start ops h)))
      (fun x => if x = (fun i => s i.val) then (1 : ℂ) else 0) =
        fun x => if x = (fun i => run start ops s i.val) then 1 else 0 := by
  rw [compileReversible_basis, reversible_semantics ops h hv s hz]

end BooleanProgram

end InfoLossLAR.WorstCase

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule39

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

namespace BooleanExpr

theorem eval_congr {bound : ℕ} (e : BooleanExpr) (hv : e.Valid bound)
    {s t : ℕ → Bool} (h : ∀ i, i < bound → s i = t i) : e.eval s = e.eval t := by
  induction e with
  | input i => exact h i hv
  | constant b => rfl
  | negate a ih => exact congrArg Bool.not (ih hv)
  | xor a b ia ib => exact congrArg₂ Bool.xor (ia hv.1) (ib hv.2)
  | and a b ia ib => exact congrArg₂ Bool.and (ia hv.1) (ib hv.2)

private theorem singleton_at (start : ℕ) (op : BooleanOp) (s : ℕ → Bool) :
    BooleanProgram.run start [op] s start = op.eval s := by
  simp [BooleanProgram.run, BooleanOp.assign]

private theorem append_singleton_at (start : ℕ) (ops : List BooleanOp) (op : BooleanOp)
    (s : ℕ → Bool) :
    BooleanProgram.run start (ops ++ [op]) s (start + ops.length) =
      op.eval (BooleanProgram.run start ops s) := by
  rw [BooleanProgram.run_append, singleton_at]

theorem compile_eval (e : BooleanExpr) (start : ℕ) (hv : e.Valid start) (s : ℕ → Bool) :
    BooleanProgram.run start (e.compile start).1 s (e.compile start).2 = e.eval s := by
  induction e generalizing start s with
  | input i => rfl
  | constant b => exact singleton_at start (.constant b) s
  | negate a ih =>
    simp only [compile, append_singleton_at, BooleanOp.eval, eval]
    rw [ih start hv]
  | xor a b ia ib | and a b ia ib =>
    have hca := (a.compile_valid start hv.1).2
    have hcb := b.valid_mono hv.2 (Nat.le_add_right start a.size)
    have hb := ib (start + a.size) hcb (BooleanProgram.run start (a.compile start).1 s)
    have heq : b.eval (BooleanProgram.run start (a.compile start).1 s) = b.eval s :=
      b.eval_congr hv.2 (fun i hi => BooleanProgram.run_below _ _ _ i hi)
    rw [heq] at hb
    simp only [compile, compile_length]
    rw [show start + a.size + b.size = start +
      ((a.compile start).1 ++ (b.compile (start + a.size)).1).length by simp; omega,
      append_singleton_at, BooleanProgram.run_append]
    simp only [BooleanOp.eval, compile_length, eval]
    rw [BooleanProgram.run_below _ _ _ _ hca, ia start hv.1, hb]

end BooleanExpr

end InfoLossLAR.WorstCase

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

namespace BooleanExpr

theorem lookup_eval {α : Type} [Fintype α] [DecidableEq α]
    (table : α → Bool) (inputs : α → BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (inputs a).eval s = decide (a = actual)) :
    (lookup table inputs).eval s = table actual := by
  rw [Bool.eq_iff_iff]
  simp only [lookup, eval_any_true, List.mem_map, List.mem_filter,
    Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, he⟩
    have heq : a = actual := by simpa only [h, decide_eq_true_eq] using he
    simpa only [heq] using ha
  · intro ha
    exact ⟨inputs actual, ⟨actual, ha, rfl⟩, by simp [h]⟩

theorem compileMany_eval (start : ℕ) (es : List BooleanExpr)
    (h : ∀ e ∈ es, e.Valid start) (s : ℕ → Bool) :
    (compileMany start es).2.map (BooleanProgram.run start (compileMany start es).1 s) =
      es.map (fun e => e.eval s) := by
  induction es generalizing start s with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hout := (e.compile_valid start he).2
    have ht := ih (start + e.size)
      (fun a ha => a.valid_mono (h a (by simp [ha])) (Nat.le_add_right _ _))
      (BooleanProgram.run start (e.compile start).1 s)
    have href : es.map (fun a => a.eval (BooleanProgram.run start (e.compile start).1 s)) =
        es.map (fun a => a.eval s) := by
      apply List.map_congr_left
      intro a ha
      exact a.eval_congr (h a (by simp [ha])) (fun i hi => BooleanProgram.run_below _ _ _ i hi)
    rw [href] at ht
    simp only [compileMany, compile_length, List.map_cons, BooleanProgram.run_append]
    rw [BooleanProgram.run_below _ _ _ _ hout, e.compile_eval start he, ht]

theorem multiplex_eval {α : Type} [Fintype α] [DecidableEq α]
    (control payload : α → BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (control a).eval s = decide (a = actual)) :
    (multiplex control payload).eval s = (payload actual).eval s := by
  rw [Bool.eq_iff_iff]
  simp only [multiplex, eval_any_true, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, he⟩
    simp only [eval, Bool.and_eq_true, h, decide_eq_true_eq] at he
    simpa only [he.1] using he.2
  · intro hp
    exact ⟨.and (control actual) (payload actual), ⟨actual, rfl⟩, by simp [eval, h, hp]⟩

end BooleanExpr

end InfoLossLAR.WorstCase

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule41

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

namespace Symbolic

variable {width : ℕ}

theorem load_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (f : σ → σ) :
    Encodes (sym.load f) {cfg with var := f cfg.var} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state

theorem push_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (k : K) (f : σ → Bool) :
    Encodes (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [push, Function.update_self, ↓reduceIte]
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte, List.getElem?_cons_zero]
      exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state
    · simp only [hi, ↓reduceDIte]
      rw [h.stack]
      congr 1
      have he : i.val = (i.val - 1) + 1 := by omega
      conv_rhs => rw [he]
      simp only [List.getElem?_cons_succ]
  · simpa only [push, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b

theorem read_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (hw : 0 < width)
    (k : K) (f : σ → Option Bool → σ) :
    Encodes (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  apply BooleanExpr.lookup_eval _ _ _ (cfg.var, (cfg.stk k).head?)
  intro a
  simp only [BooleanExpr.eval, h.state, h.stack]
  simp [Prod.ext_iff, List.head?_eq_getElem?]

theorem pop_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (k : K)
    (hsize : (cfg.stk k).length ≤ width) :
    Encodes (sym.pop k) {cfg with stk := Function.update cfg.stk k (cfg.stk k).tail} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [pop, Function.update_self, ↓reduceIte]
    by_cases hi : i.val + 1 < width
    · simp only [hi, ↓reduceDIte, h.stack]
      congr 1
      simp
    · simp only [hi, ↓reduceDIte, BooleanExpr.eval]
      have he : (cfg.stk k).tail[i.val]? = none :=
        List.getElem?_eq_none (by simp only [List.length_tail]; omega)
      rw [he]
  · simpa only [pop, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b

theorem jump_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (f : σ → Λ) :
    Encodes (sym.jump f) {cfg with l := some (f cfg.var)} bits := by
  refine ⟨?_, h.state, h.stack⟩
  intro l
  exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state

theorem halt_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) :
    Encodes sym.halt {cfg with l := none} bits := ⟨fun _ => rfl, h.state, h.stack⟩

theorem select_encodes (condition : BooleanExpr) (a b : Symbolic K Λ σ width)
    (cfgA cfgB : Configuration K Λ σ) (bits : ℕ → Bool)
    (ha : Encodes a cfgA bits) (hb : Encodes b cfgB bits) :
    Encodes (select condition a b) (if condition.eval bits then cfgA else cfgB) bits := by
  cases hc : condition.eval bits
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.label l
    · intro v; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.state v
    · intro k i b; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.stack k i b
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.label l
    · intro v; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.state v
    · intro k i b; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.stack k i b

end Symbolic

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule42

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

/-- The stack-size premise is precisely the allocated capacity, including all pushes in this step. -/
theorem auxiliary_encodes (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (h : Encodes sym cfg bits) (hsize : stackSize cfg.stk + pushBound q ≤ width) :
    Encodes (auxiliary hw q sym) (TM2.stepAux q cfg.var cfg.stk) bits := by
  induction q generalizing sym cfg with
  | push k f q ih =>
    have hs : stackSize (Function.update cfg.stk k (f cfg.var :: cfg.stk k)) ≤ stackSize cfg.stk + 1 :=
      stackSize_update_le cfg.stk k _ _ (Nat.le_add_right _ _)
        (by simpa only [List.length_cons] using Nat.succ_le_succ (length_le_stackSize cfg.stk k))
    exact ih (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)}
      (sym.push_encodes cfg bits h k f) (by simp only [pushBound] at hsize; dsimp only; omega)
  | peek k f q ih =>
    exact ih (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?}
      (sym.read_encodes cfg bits h hw k f) hsize
  | pop k f q ih =>
    have hs : stackSize (Function.update cfg.stk k (cfg.stk k).tail) ≤ stackSize cfg.stk :=
      stackSize_update_le cfg.stk k _ _ le_rfl
        (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (length_le_stackSize cfg.stk k))
    have hr := sym.read_encodes cfg bits h hw k f
    have hp := (sym.read hw k f).pop_encodes {cfg with var := f cfg.var (cfg.stk k).head?}
      bits hr k ((length_le_stackSize cfg.stk k).trans (by simp only [pushBound] at hsize; omega))
    exact ih ((sym.read hw k f).pop k)
      {cfg with var := f cfg.var (cfg.stk k).head?, stk := Function.update cfg.stk k (cfg.stk k).tail}
      hp (by simp only [pushBound] at hsize; dsimp only; omega)
  | load f q ih =>
    exact ih (sym.load f) {cfg with var := f cfg.var} (sym.load_encodes cfg bits h f) hsize
  | branch f q r iq ir =>
    have hq := iq sym cfg h (by simp only [pushBound] at hsize; have := le_max_left (pushBound q) (pushBound r); omega)
    have hr := ir sym cfg h (by simp only [pushBound] at hsize; have := le_max_right (pushBound q) (pushBound r); omega)
    have he := Symbolic.select_encodes (BooleanExpr.lookup f sym.state)
      (auxiliary hw q sym) (auxiliary hw r sym) _ _ bits hq hr
    rw [BooleanExpr.lookup_eval f sym.state bits cfg.var h.state] at he
    cases hf : f cfg.var <;> simpa only [auxiliary, TM2.stepAux, hf, Bool.cond_false,
      Bool.cond_true, Bool.false_eq_true, ↓reduceIte] using he
  | goto f => exact sym.jump_encodes cfg bits h f
  | halt => exact sym.halt_encodes cfg bits h

theorem multiplex_encodes {α : Type} [Fintype α] [DecidableEq α]
    (control : α → BooleanExpr) (choices : α → Symbolic K Λ σ width)
    (bits : ℕ → Bool) (actual : α) (cfg : Configuration K Λ σ)
    (hc : ∀ a, (control a).eval bits = decide (a = actual))
    (h : Encodes (choices actual) cfg bits) : Encodes (multiplex control choices) cfg bits := by
  constructor
  · intro l
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.label l
  · intro v
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.state v
  · intro k i b
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.stack k i b

theorem transition_encodes (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (h : Encodes sym cfg bits) (hsize : stackSize cfg.stk + programPushBound program ≤ width) :
    Encodes (transition hw program sym) (stickyStep program cfg) bits := by
  apply multiplex_encodes sym.label _ bits cfg.l _ h.label
  cases hl : cfg.l with
  | none => simpa only [hl, Option.elim_none, stickyStep] using h
  | some l =>
    have hq : pushBound (program l) ≤ programPushBound program :=
      Finset.le_sup (f := fun l => pushBound (program l)) (Finset.mem_univ l)
    simpa only [hl, Option.elim_some, stickyStep] using
      auxiliary_encodes hw (program l) sym cfg bits h (by omega)

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeBooleanSize. -/
section P2MDyadicModule43

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.BooleanExpr

theorem size_any_le (es : List BooleanExpr) (bound : ℕ)
    (h : ∀ e ∈ es, e.size ≤ bound) : (any es).size ≤ (bound + 4) * es.length + 1 := by
  induction es with
  | nil => simp [any, size]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [any, size_or, List.length_cons]
    nlinarith

theorem size_lookup_le {α : Type} [Fintype α]
    (table : α → Bool) (inputs : α → BooleanExpr) (bound : ℕ)
    (h : ∀ a, (inputs a).size ≤ bound) :
    (lookup table inputs).size ≤ (bound + 4) * Fintype.card α + 1 := by
  have he := size_any_le ((Finset.univ.toList.filter table).map inputs) bound (by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
    exact h a)
  have hl : (Finset.univ.toList.filter table).length ≤ Fintype.card α := by
    simpa only [Finset.length_toList, Finset.card_univ] using
      List.length_filter_le table (Finset.univ.toList : List α)
  simp only [List.length_map] at he
  simpa only [lookup] using he.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) 1)

theorem size_multiplex_le {α : Type} [Fintype α]
    (control payload : α → BooleanExpr) (controlBound payloadBound : ℕ)
    (hc : ∀ a, (control a).size ≤ controlBound)
    (hp : ∀ a, (payload a).size ≤ payloadBound) :
    (multiplex control payload).size ≤
      (controlBound + payloadBound + 5) * Fintype.card α + 1 := by
  have he := size_any_le (Finset.univ.toList.map (fun a => and (control a) (payload a)))
    (controlBound + payloadBound + 1) (by
      intro e he
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
      simp only [size]
      have := hc a
      have := hp a
      omega)
  simpa only [multiplex, List.length_map, Finset.length_toList, Finset.card_univ, Nat.add_assoc]
    using he

end InfoLossLAR.WorstCase.BooleanExpr

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule44

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

namespace Symbolic

end Symbolic

namespace Symbolic

/-- Each output reference evaluates to the formula it replaces after fresh compilation. -/
theorem output_eval (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (bits : ℕ → Bool) (i : Slot K Λ σ width) :
    BooleanProgram.run start (sym.compiled start).1 bits (sym.output start i) = (sym.get i).eval bits := by
  have he := BooleanExpr.compileMany_eval start sym.formulas (sym.formulas_valid h) bits
  have hi := congrArg (fun xs : List Bool => xs[(slotEquiv K Λ σ width i).val]?) he
  simp only [List.getElem?_map] at hi
  have ho : (sym.compiled start).2[(slotEquiv K Λ σ width i).val]? = some (sym.output start i) :=
    List.getElem?_eq_getElem _
  change (sym.compiled start).2[(slotEquiv K Λ σ width i).val]?.map
    (BooleanProgram.run start (sym.compiled start).1 bits) = _ at hi
  rw [ho] at hi
  simp only [formulas, List.getElem?_ofFn, dif_pos (slotEquiv K Λ σ width i).isLt,
    Fin.eta, Equiv.symm_apply_apply, Option.map_some, Option.some.injEq] at hi
  exact hi

theorem rebound_encodes (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (cfg : Configuration K Λ σ) (bits : ℕ → Bool) (he : Encodes sym cfg bits) :
    Encodes (sym.rebound start) cfg (BooleanProgram.run start (sym.compiled start).1 bits) := by
  constructor
  · intro l
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inl l)]
    exact he.label l
  · intro v
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inr (.inl v))]
    exact he.state v
  · intro k i b
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inr (.inr (k, i, b)))]
    exact he.stack k i b

end Symbolic

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeBooleanRPN. -/
section P2MDyadicModule45

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem step_poly : Poly (fun x : State × Token => step x.1 x.2) := by
  unfold step emit
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule45

/- Helper module Solutions.RegevBridgeBooleanRPNRun. -/
section P2MDyadicModule46

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open Polynomial

theorem Bounded.mono {N M : ℕ} {s : State} (h : Bounded N s) (hm : N ≤ M) :
    Bounded M s := by
  exact ⟨h.slots.trans hm, h.operands.trans hm, h.nodes.trans hm,
    fun x hx => (h.refs x hx).trans hm,
    fun x hx => ⟨(h.code x hx).1.trans hm, (h.code x hx).2.1.trans hm,
      (h.code x hx).2.2.trans hm⟩⟩

theorem getD_bound (xs : List ℕ) (i N : ℕ) (h : ∀ x ∈ xs, x.bits.length ≤ N) :
    ((xs[i]?).getD 0).bits.length ≤ N := by
  by_cases hi : i < xs.length
  · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (show xs.length ≤ i by omega)]
    simp

theorem emit_bounded {N : ℕ} {s : State} (h : Bounded N s) (x : Node)
    (hx : NodeBound (N+1) x) (rest : List ℕ) (hl : rest.length ≤ N)
    (hr : ∀ a ∈ rest, a.bits.length ≤ N+1) : Bounded (N+1) (emit s x rest) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [emit] using Nat.add_le_add_right h.slots 1
  · simpa [emit] using Nat.add_le_add_right hl 1
  · simpa [emit] using Nat.add_le_add_right h.nodes 1
  · intro a ha
    simp only [emit, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (Nat.add_le_add_right h.slots 1)
    · exact hr a ha
  · intro a ha
    simp only [emit, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact (h.mono (Nat.le_succ N)).code a ha
    · exact hx

theorem step_bounded {N : ℕ} {s : State} (h : Bounded N s) (hN : 3 ≤ N)
    (token : Token) (ht : token.2.bits.length ≤ N+1) : Bounded (N+1) (step s token) := by
  have hh := h.mono (Nat.le_succ N)
  have h0 := getD_bound s.2.1 0 (N+1) hh.refs
  have h1 := getD_bound s.2.1 1 (N+1) hh.refs
  have tailLen : s.2.1.tail.length ≤ N := by rw [List.length_tail]; exact (Nat.sub_le _ _).trans h.operands
  have tailTailLen : s.2.1.tail.tail.length ≤ N :=
    by rw [List.length_tail]; omega
  have tailRefs : ∀ a ∈ s.2.1.tail, a.bits.length ≤ N+1 :=
    fun a ha => hh.refs a (List.mem_of_mem_tail ha)
  have tailTailRefs : ∀ a ∈ s.2.1.tail.tail, a.bits.length ≤ N+1 :=
    fun a ha => tailRefs a (List.mem_of_mem_tail ha)
  unfold step
  split
  · refine ⟨hh.slots, ?_, hh.nodes, ?_, hh.code⟩
    · simpa using Nat.add_le_add_right h.operands 1
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hh.refs x hx
  · split
    · apply emit_bounded h _ _ _ h.operands hh.refs
      norm_num [NodeBound]
    · split
      · apply emit_bounded h _ _ _ h.operands hh.refs
        norm_num [NodeBound]
      · split
        · apply emit_bounded h _ _ _ tailLen tailRefs
          change (3:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ 0 ≤ N+1
          rw [show (3:ℕ).bits.length = 2 by decide]
          exact ⟨by omega, h0, Nat.zero_le _⟩
        · split
          · apply emit_bounded h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩
          · apply emit_bounded h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩

theorem run_bounded (tokens : List Token) {N : ℕ} {s : State} (h : Bounded N s)
    (hN : 3 ≤ N) (ht : ∀ t ∈ tokens, t.2.bits.length ≤ N) :
    Bounded (N+tokens.length) (run tokens s) := by
  induction tokens generalizing N s with
  | nil => simpa [run] using h
  | cons t ts ih =>
    have hs := step_bounded h hN t ((ht t (by simp)).trans (Nat.le_succ N))
    have hh := ih hs (by omega) (fun u hu => (ht u (by simp [hu])).trans (Nat.le_succ N))
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem encodedUnit_length (xs : List Unit) : (enc xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (encodeList (fun _ : Unit => []) (x::xs)).length = _
    rw [EncodedList.cons_length]
    change (encodeList (fun _ : Unit => []) xs).length = xs.length at ih
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.length_cons]
    omega

theorem bounded_of_encoding (s : State) : Bounded (enc s).length s := by
  have hs := encodedUnit_length s.1
  have ho := EncodedList.length_le Nat.bits s.2.1
  have hn := EncodedList.length_le (enc : Node → List Bool) s.2.2
  have he : (enc s).length = 2*(enc s.1).length+1+2*(enc s.2.1).length+1+(enc s.2.2).length := by
    simp only [enc, Coding.encode, encodePair_length]; omega
  change s.2.1.length ≤ (enc s.2.1).length at ho
  change s.2.2.length ≤ (enc s.2.2).length at hn
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro x hx
    have hh := EncodedList.member_length Nat.bits s.2.1 x hx
    change x.bits.length ≤ (enc s.2.1).length at hh
    omega
  · intro x hx
    have hh := EncodedList.member_length (enc : Node → List Bool) s.2.2 x hx
    change (enc x).length ≤ (enc s.2.2).length at hh
    have he' : (enc x).length = 2*x.1.bits.length+1+2*x.2.1.bits.length+1+x.2.2.bits.length := by
      simp only [enc, Coding.encode, encodePair_length]; omega
    exact ⟨by omega, by omega, by omega⟩

theorem encoding_bound {N : ℕ} {s : State} (h : Bounded N s) :
    (enc s).length ≤ 20*(N+1)^2 := by
  have hs := encodedUnit_length s.1
  have ho := EncodedList.length_bound Nat.bits s.2.1 N h.refs
  have hn := EncodedList.length_bound (enc : Node → List Bool) s.2.2 (5*N+2) (by
    intro x hx
    have hb := h.code x hx
    rcases hb with ⟨hb1, hb2, hb3⟩
    change (encodePair Nat.bits (encodePair Nat.bits Nat.bits) x).length ≤ _
    simp only [encodePair_length]
    omega)
  have ho' : (enc s.2.1).length ≤ N*(2*N+1) := ho.trans (Nat.mul_le_mul_right _ h.operands)
  have hn' : (enc s.2.2).length ≤ N*(2*(5*N+2)+1) := hn.trans (Nat.mul_le_mul_right _ h.nodes)
  change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) s).length ≤ _
  simp only [encodePair_length]
  nlinarith [h.slots]

theorem run_partial_bound (tokens : List Token) (s : State) (pre suf : List Token)
    (he : tokens = pre ++ suf) :
    (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2 := by
  let L := (enc (tokens,s)).length
  have heL : L = 2*(enc tokens).length+1+(enc s).length := encodePair_length _ _ _
  have hpenc : (enc pre).length ≤ (enc tokens).length := by
    change (encodeList enc pre).length ≤ (encodeList enc tokens).length
    rw [he, EncodedList.append, List.length_append]; omega
  have hplen : pre.length ≤ L := by
    have hh := EncodedList.length_le (enc : Token → List Bool) pre
    change pre.length ≤ (enc pre).length at hh
    omega
  have hs := (bounded_of_encoding s).mono (show (enc s).length ≤ L+3 by omega)
  have ht : ∀ t ∈ pre, t.2.bits.length ≤ L+3 := by
    intro t ht
    have hh := EncodedList.member_length (enc : Token → List Bool) pre t ht
    change (enc t).length ≤ (enc pre).length at hh
    have hte : (enc t).length = 2*t.1.bits.length+1+t.2.bits.length := encodePair_length _ _ _
    omega
  have hb := run_bounded pre hs (by omega) ht
  have hb' := hb.mono (show L+3+pre.length ≤ 2*L+3 by omega)
  have hh := encoding_bound hb'
  simpa [L, Nat.add_assoc] using hh

@[fun_prop] theorem run_poly : Poly (fun x : List Token × State => run x.1 x.2) := by
  apply Poly.of_program
  exact step_poly.program.listFold (0,0) (20*(2*Polynomial.X+4)^2) (by
    intro tokens s pre suf he
    simp only [eval_mul, eval_ofNat, eval_pow, eval_add, eval_X]
    change (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2
    exact run_partial_bound tokens s pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeBooleanCodePoly. -/
section P2MDyadicModule47

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace CodePoly

variable {α β : Type} [Coding α] [Coding β]

theorem comp {f : β → BooleanExpr} {g : α → β} (hf : CodePoly f) (hg : Poly g) :
    CodePoly (fun a => f (g a)) := Automatic.Poly.comp (f := fun b => code (f b)) (g := g) hf hg

theorem input {f : α → ℕ} (hf : Poly f) : CodePoly (fun a => .input (f a)) := by
  unfold CodePoly code
  fun_prop

theorem constant (b : Bool) : CodePoly (fun _ : α => .constant b) := by
  unfold CodePoly
  exact Automatic.Poly.const _

theorem negate {f : α → BooleanExpr} (hf : CodePoly f) : CodePoly (fun a => .negate (f a)) := by
  unfold CodePoly at hf ⊢
  change Poly (fun a => code (f a) ++ [(3,0)])
  fun_prop

theorem and {f g : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => .and (f a) (g a)) := by
  unfold CodePoly at hf hg ⊢
  change Poly (fun a => code (f a) ++ code (g a) ++ [(5,0)])
  fun_prop

theorem or {f g : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => BooleanExpr.or (f a) (g a)) := by
  exact (hf.negate.and hg.negate).negate

theorem select {f g h : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) (hh : CodePoly h) :
    CodePoly (fun a => BooleanExpr.select (f a) (g a) (h a)) := by
  exact (hf.and hg).or (hf.negate.and hh)

theorem ite {p : α → Bool} {f g : α → BooleanExpr} (hp : Poly p)
    (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => if p a then f a else g a) := by
  change Poly (fun a => code (if p a then f a else g a))
  have he : (fun a => code (if p a then f a else g a)) =
      (fun a => if p a then code (f a) else code (g a)) := by funext a; split <;> rfl
  rw [he]
  exact Poly.ite hp hf hg

theorem any {ι : Type} (indices : List ι) (f : ι → α → BooleanExpr)
    (hf : ∀ i ∈ indices, CodePoly (f i)) :
    CodePoly (fun a => BooleanExpr.any (indices.map (fun i => f i a))) := by
  induction indices with
  | nil => exact constant false
  | cons i is ih =>
    exact (hf i (by simp)).or (ih (fun j hj => hf j (by simp [hj])))

theorem lookup {ι : Type} [Fintype ι] (table : ι → Bool) (f : ι → α → BooleanExpr)
    (hf : ∀ i, CodePoly (f i)) :
    CodePoly (fun a => BooleanExpr.lookup table (fun i => f i a)) :=
  any _ f (fun i _ => hf i)

theorem multiplex {ι : Type} [Fintype ι] (f g : ι → α → BooleanExpr)
    (hf : ∀ i, CodePoly (f i)) (hg : ∀ i, CodePoly (g i)) :
    CodePoly (fun a => BooleanExpr.multiplex (fun i => f i a) (fun i => g i a)) :=
  any _ _ (fun i _ => (hf i).and (hg i))

end CodePoly

@[fun_prop] theorem compileTokens_poly :
    Poly (fun x : List Token × List Unit => compileTokens x.1 x.2) := by
  unfold compileTokens
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule47

/- Helper module Solutions.RegevBridgeTM2CodeFamily. -/
section P2MDyadicModule48

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

namespace CodeFamily

variable [Coding α]

theorem load_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → σ) : (sym.load f).IsPoly :=
  ⟨h.label, fun v => CodePoly.lookup _ sym.state h.state, h.stack⟩

theorem push_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Bool) :
    (sym.push k f).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [push, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2 = 0)) := by fun_prop
    have hf := CodePoly.lookup (fun v => decide (b = some (f v)))
      (fun v (x : α × ℕ) => sym.state v x.1) (fun v => (h.state v).comp (by fun_prop))
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2-1)) by fun_prop)
    simpa only [decide_eq_true_eq] using CodePoly.ite hi hf ht
  · simpa only [push, hj, ↓reduceIte] using h.stack j b

theorem read_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Option Bool → σ) :
    (sym.read k f).IsPoly := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  change CodePoly (fun a => BooleanExpr.lookup (fun u : σ × Option Bool => decide (v = f u.1 u.2)) (fun u => .and (sym.state u.1 a) (sym.stack k u.2 (a,0))))
  apply CodePoly.lookup
  intro u
  exact (h.state u.1).and ((h.stack k u.2).comp (by fun_prop))

theorem pop_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (width : α → ℕ)
    (hw : Poly width) (k : K) : (sym.pop width k).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [pop, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2+1 < width x.1)) := by fun_prop
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2+1)) by fun_prop)
    simpa only [decide_eq_true_eq] using CodePoly.ite hi ht (CodePoly.constant (decide (b=none)))
  · simpa only [pop, hj, ↓reduceIte] using h.stack j b

theorem jump_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → Λ) : (sym.jump f).IsPoly :=
  ⟨fun l => CodePoly.lookup _ sym.state h.state, h.state, h.stack⟩

theorem halt_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) : sym.halt.IsPoly :=
  ⟨fun l => CodePoly.constant (decide (l=none)), h.state, h.stack⟩

theorem select_poly (condition : α → BooleanExpr) (a b : CodeFamily K Λ σ α)
    (hc : CodePoly condition) (ha : a.IsPoly) (hb : b.IsPoly) : (select condition a b).IsPoly :=
  ⟨fun l => hc.select (ha.label l) (hb.label l),
    fun v => hc.select (ha.state v) (hb.state v),
    fun k v => (hc.comp (by fun_prop)).select (ha.stack k v) (hb.stack k v)⟩

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule48

/- Helper module Solutions.RegevBridgeTM2CodeTransition. -/
section P2MDyadicModule49

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable [Coding α]

theorem auxiliaryCode_poly (width : α → ℕ) (hw : Poly width)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (auxiliaryCode width q sym).IsPoly := by
  induction q generalizing sym with
  | push k f q ih => exact ih _ (sym.push_poly h k f)
  | peek k f q ih => exact ih _ (sym.read_poly h k f)
  | pop k f q ih => exact ih _ ((sym.read k f).pop_poly (sym.read_poly h k f) width hw k)
  | load f q ih => exact ih _ (sym.load_poly h f)
  | branch f q r iq ir =>
    exact select_poly _ _ _ (CodePoly.lookup f sym.state h.state) (iq _ h) (ir _ h)
  | goto f => exact sym.jump_poly h f
  | halt => exact sym.halt_poly h

theorem multiplexCode_poly {ι : Type} [Fintype ι]
    (control : ι → α → BooleanExpr) (choices : ι → CodeFamily K Λ σ α)
    (hc : ∀ i, CodePoly (control i)) (hp : ∀ i, (choices i).IsPoly) :
    (multiplexCode control choices).IsPoly :=
  ⟨fun l => CodePoly.multiplex _ _ hc (fun i => (hp i).label l),
    fun v => CodePoly.multiplex _ _ hc (fun i => (hp i).state v),
    fun k b => CodePoly.multiplex _ _ (fun i => (hc i).comp (by fun_prop)) (fun i => (hp i).stack k b)⟩

theorem transitionCode_poly (width : α → ℕ) (hw : Poly width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (transitionCode width program sym).IsPoly := by
  apply multiplexCode_poly _ _ h.label
  intro l
  cases l with
  | none => exact h
  | some l => exact auxiliaryCode_poly width hw (program l) sym h

end InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeTM2CodeEnumeration. -/
section P2MDyadicModule50

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

theorem fixed_flatMap_poly {α β ι : Type} [Coding α] [Coding β] [Inhabited β]
    (indices : List ι) (f : ι → α → List β) (hf : ∀ i ∈ indices, Poly (f i)) :
    Poly (fun a => indices.flatMap (fun i => f i a)) := by
  induction indices with
  | nil => exact Automatic.Poly.const []
  | cons i is ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun a => f i a ++ is.flatMap (fun j => f j a))
    fun_prop

namespace CodeFamily

variable {K Λ σ α : Type} [Fintype K] [Fintype Λ] [Fintype σ]

theorem codes_poly [Coding α] (sym : CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width : α → List Unit) (hw : Poly width) : Poly (sym.codes width) := by
  have hlabel := fixed_flatMap_poly (enumerate (Fintype.equivFin (Option Λ)))
    (fun l a => code (sym.label l a)) (fun l _ => h.label l)
  have hstate := fixed_flatMap_poly (enumerate (Fintype.equivFin σ))
    (fun v a => code (sym.state v a)) (fun v _ => h.state v)
  have hstack : ∀ k, Poly (fun a : α =>
      (List.range (width a).length).flatMap (fun i =>
        (enumerate (Fintype.equivFin (Option Bool))).flatMap (fun b => code (sym.stack k b (a,i))))) := by
    intro k
    have hcell := fixed_flatMap_poly (enumerate (Fintype.equivFin (Option Bool)))
      (fun b (x : α × ℕ) => code (sym.stack k b x)) (fun b _ => h.stack k b)
    apply Automatic.Poly.list_flatMap hcell
    exact Automatic.Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := width) Automatic.Poly.list_indices hw
  have hstackAll := fixed_flatMap_poly (enumerate (Fintype.equivFin K)) _ (fun k _ => hstack k)
  unfold codes
  fun_prop

theorem compile_poly [Coding α] (sym : CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width slots : α → List Unit) (hw : Poly width) (hs : Poly slots) : Poly (sym.compile width slots) := by
  have hc := sym.codes_poly h width hw
  unfold compile
  fun_prop

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule51

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing StateTransition

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem stickyStep_size (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (cfg : Configuration K Λ σ) :
    stackSize (stickyStep program cfg).stk ≤ stackSize cfg.stk + programPushBound program := by
  cases hl : cfg.l with
  | none => simpa only [stickyStep, hl, Option.elim_none] using Nat.le_add_right (stackSize cfg.stk) _
  | some l =>
    have hc := stepAux_stackSize_le (program l) cfg.var cfg.stk
    have hb : pushBound (program l) ≤ programPushBound program :=
      Finset.le_sup (f := fun l => pushBound (program l)) (Finset.mem_univ l)
    simpa only [stickyStep, hl, Option.elim_some] using hc.trans (Nat.add_le_add_left hb _)

/-- Full bounded execution: each step is compiled and its formula outputs are rebound to fresh wires. -/
theorem compileRun_encodes (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (hv : sym.Valid start) (he : Encodes sym cfg bits)
    (hsize : stackSize cfg.stk + programPushBound program * ticks ≤ width) :
    Encodes (compileRun hw program ticks start sym).2 ((stickyStep program)^[ticks] cfg)
      (BooleanProgram.run start (compileRun hw program ticks start sym).1 bits) := by
  induction ticks generalizing start sym cfg bits with
  | zero => exact he
  | succ ticks ih =>
    have ht := transition_valid hw program sym hv
    have hcap : stackSize cfg.stk + programPushBound program ≤ width := by nlinarith
    have hs := transition_encodes hw program sym cfg bits he hcap
    have hf := (transition hw program sym).rebound_encodes start ht _ bits hs
    have hv' := (transition hw program sym).rebound_valid start ht
    have hg := stickyStep_size program cfg
    have hremaining : stackSize (stickyStep program cfg).stk + programPushBound program * ticks ≤ width := by
      nlinarith
    have hh := ih _ _ _ _ hv' hf hremaining
    simpa only [compileRun, BooleanProgram.run_append, Function.iterate_succ_apply] using hh

theorem stickyStep_of_step (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : Configuration K Λ σ) (h : TM2.step program a = some b) : stickyStep program a = b := by
  rcases a with ⟨l, v, stackStore⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l => simpa only [TM2.step, Option.some.injEq, stickyStep, Option.elim_some] using h

theorem stickyStep_of_halted (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a : Configuration K Λ σ) (h : a.l = none) : stickyStep program a = a := by
  simp only [stickyStep, h, Option.elim_none]

private theorem iterate_none {α : Type} (step : α → Option α) (n : ℕ) :
    ((fun c : Option α => c.bind step)^[n]) none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih

theorem sticky_iterate_of_steps (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (steps : ℕ) (a b : Configuration K Λ σ)
    (h : ((fun c : Option (Configuration K Λ σ) => c.bind (TM2.step program))^[steps]) (some a) = some b) :
    (stickyStep program)^[steps] a = b := by
  induction steps generalizing a with
  | zero => simpa using h
  | succ steps ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : TM2.step program a with
    | none => simp only [Option.bind_some, hs, iterate_none] at h; contradiction
    | some next =>
      simp only [Option.bind_some, hs] at h
      rw [Function.iterate_succ_apply, stickyStep_of_step program a next hs]
      exact ih next h

/-- A successful machine's budget can be padded after halt without changing its output. -/
theorem sticky_iterate_of_outputs (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : Configuration K Λ σ) (ticks : ℕ)
    (h : EvalsToInTime (TM2.step program) a (some b) ticks) (hb : b.l = none) :
    (stickyStep program)^[ticks] a = b := by
  have hs := sticky_iterate_of_steps program h.steps a b h.evals_in_steps
  have he : ticks = (ticks - h.steps) + h.steps := by have := h.steps_le_m; omega
  rw [he, Function.iterate_add_apply, hs]
  exact Function.iterate_fixed (stickyStep_of_halted program b hb) _

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeTM2Size. -/
section P2MDyadicModule52

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

namespace Symbolic

theorem Bounded.mono {small big : ℕ} {sym : Symbolic K Λ σ width}
    (h : sym.Bounded small) (hle : small ≤ big) : sym.Bounded big :=
  ⟨fun l => (h.label l).trans hle, fun v => (h.state v).trans hle,
    fun k i b => (h.stack k i b).trans hle⟩

private theorem old_le_operation (bound : ℕ) : bound ≤ operationBound σ bound := by
  unfold operationBound; omega

private theorem lookup_le_operation (bound : ℕ) : lookupBound σ bound ≤ operationBound σ bound := by
  unfold operationBound; omega

private theorem read_le_operation (bound : ℕ) : readBound σ bound ≤ operationBound σ bound := by
  unfold operationBound; omega

theorem load_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → σ) :
    (sym.load f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound), ?_,
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro v
  exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)

theorem push_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (k : K) (f : σ → Bool) :
    (sym.push k f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound),
    fun v => (h.state v).trans (old_le_operation bound), ?_⟩
  intro j i b
  dsimp only [push]
  split_ifs
  · exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)
  · exact (h.stack _ _ _).trans (old_le_operation bound)
  · exact (h.stack _ _ _).trans (old_le_operation bound)

theorem read_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hw : 0 < width) (k : K) (f : σ → Option Bool → σ) :
    (sym.read hw k f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound), ?_,
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro v
  have hi : ∀ a : σ × Option Bool,
      (BooleanExpr.and (sym.state a.1) (sym.stack k ⟨0, hw⟩ a.2)).size ≤ 2 * bound + 1 := by
    intro a
    simp only [BooleanExpr.size]
    have := h.state a.1
    have := h.stack k ⟨0, hw⟩ a.2
    omega
  have ht := BooleanExpr.size_lookup_le (fun a : σ × Option Bool => decide (v = f a.1 a.2)) _
    (2 * bound + 1) hi
  have hb : ((sym.read hw k f).state v).size ≤ readBound σ bound := by
    simpa only [read, readBound, Nat.add_assoc] using ht
  exact hb.trans (read_le_operation bound)

theorem pop_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hb : 1 ≤ bound) (k : K) : (sym.pop k).Bounded bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [pop]
  split_ifs
  · exact h.stack _ _ _
  · exact hb
  · exact h.stack _ _ _

theorem jump_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → Λ) :
    (sym.jump f).Bounded (operationBound σ bound) := by
  refine ⟨?_, fun v => (h.state v).trans (old_le_operation bound),
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro l
  exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)

theorem halt_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) :
    sym.halt.Bounded (bound + 1) :=
  ⟨fun _ => by simp only [halt, BooleanExpr.size]; omega,
    fun v => (h.state v).trans (Nat.le_add_right _ _),
    fun k i b => (h.stack k i b).trans (Nat.le_add_right _ _)⟩

theorem select_bounded (condition : BooleanExpr) (a b : Symbolic K Λ σ width)
    (conditionBound firstBound secondBound : ℕ)
    (hc : condition.size ≤ conditionBound) (ha : a.Bounded firstBound) (hb : b.Bounded secondBound) :
    (select condition a b).Bounded (2 * conditionBound + firstBound + secondBound + 7) := by
  have hh (e f : BooleanExpr) (he : e.size ≤ firstBound) (hf : f.size ≤ secondBound) :
      (BooleanExpr.select condition e f).size ≤ 2 * conditionBound + firstBound + secondBound + 7 := by
    rw [BooleanExpr.size_select]; omega
  exact ⟨fun l => hh _ _ (ha.label l) (hb.label l),
    fun v => hh _ _ (ha.state v) (hb.state v),
    fun k i b => hh _ _ (ha.stack k i b) (hb.stack k i b)⟩

theorem compiled_length_le (sym : Symbolic K Λ σ width) (start bound : ℕ) (h : sym.Bounded bound) :
    (sym.compiled start).1.length ≤ bound * Fintype.card (Slot K Λ σ width) := by
  rw [compiled, BooleanExpr.compileMany_length]
  have hh : ∀ e ∈ sym.formulas, e.size ≤ bound := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    generalize (slotEquiv K Λ σ width).symm i = slot
    rcases slot with l | v | ⟨k, i, b⟩
    · exact h.label l
    · exact h.state v
    · exact h.stack k i b
  have sumBound : ∀ es : List BooleanExpr, (∀ e ∈ es, e.size ≤ bound) →
      (es.map BooleanExpr.size).sum ≤ es.length * bound := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
      intro hx
      have he := hx e (by simp)
      have ht := ih (fun a ha => hx a (by simp [ha]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hl := sumBound sym.formulas hh
  simpa only [formulas_length, Nat.mul_comm] using hl

end Symbolic

theorem auxiliary_bounded (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (auxiliary hw q sym).Bounded (auxiliaryBound q bound) := by
  induction q generalizing sym bound with
  | push k f q ih => exact ih _ _ (sym.push_bounded h k f)
  | peek k f q ih => exact ih _ _ (sym.read_bounded h hw k f)
  | pop k f q ih =>
    exact ih _ _ ((sym.read hw k f).pop_bounded (sym.read_bounded h hw k f)
      (by simp only [Symbolic.operationBound, Symbolic.lookupBound, Symbolic.readBound]; omega) k)
  | load f q ih => exact ih _ _ (sym.load_bounded h f)
  | branch f q r iq ir =>
    exact Symbolic.select_bounded _ _ _ _ _ _ (BooleanExpr.size_lookup_le f sym.state bound h.state)
      (iq _ _ h) (ir _ _ h)
  | goto f => exact sym.jump_bounded h f
  | halt => exact sym.halt_bounded h

theorem transition_bounded (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (transition hw program sym).Bounded (transitionBound program bound) := by
  have hh : ∀ l : Option Λ,
      (l.elim sym (fun l => auxiliary hw (program l) sym)).Bounded
        (bound + Finset.univ.sup (fun l => auxiliaryBound (program l) bound)) := by
    intro l
    cases l with
    | none => exact h.mono (Nat.le_add_right _ _)
    | some l =>
      exact (auxiliary_bounded hw (program l) sym bound h).mono
        ((Finset.le_sup (f := fun l => auxiliaryBound (program l) bound) (Finset.mem_univ l)).trans
          (Nat.le_add_left _ _))
  exact ⟨fun l => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).label l),
    fun v => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).state v),
    fun k i b => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).stack k i b)⟩

/-- After rebinding, every new step has constant formula size per configuration slot. -/
theorem compileRun_length_le (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (compileRun hw program ticks start sym).1.length ≤
      ticks * (transitionBound program 0 * Fintype.card (Slot K Λ σ width)) := by
  induction ticks generalizing start sym with
  | zero => simp [compileRun]
  | succ ticks ih =>
    have hf := (transition hw program sym).compiled_length_le start _ (transition_bounded hw program sym 0 h)
    have hr := ih (start + ((transition hw program sym).compiled start).1.length) _
      ((transition hw program sym).rebound_bounded_zero start)
    simp only [compileRun, List.length_append]
    nlinarith

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule53

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem inputCell_eval (wire : ℕ) (b : Option Bool) (bits : ℕ → Bool) :
    (inputCell wire b).eval bits = decide (b = some (bits wire)) := by
  cases b with
  | none => rfl
  | some b => cases b <;> cases h : bits wire <;> simp [inputCell, BooleanExpr.eval, h]

theorem initial_bounded (input : K) (main : Λ) (initialState : σ) (length width : ℕ) :
    (initial input main initialState length width).Bounded 1 := by
  refine ⟨fun _ => le_rfl, fun _ => le_rfl, ?_⟩
  intro k i b
  dsimp only [initial]
  split_ifs
  · cases b with
    | none => exact le_rfl
    | some b => cases b <;> simp [inputCell, BooleanExpr.size]
  · exact le_rfl

theorem initial_encodes (input : K) (main : Λ) (initialState : σ) (width : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i]) :
    Encodes (initial input main initialState word.length width)
      (initialConfiguration input main initialState word) bits := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro k i b
  dsimp only [initial, initialConfiguration]
  by_cases hk : k = input
  · simp only [hk, ↓reduceIte, true_and]
    by_cases hi : i.val < word.length
    · simp only [hi, ↓reduceIte, inputCell_eval, hbits i.val hi, List.getElem?_eq_getElem hi]
    · simp only [hi, ↓reduceIte, BooleanExpr.eval, List.getElem?_eq_none (by omega : word.length ≤ i.val)]
  · simp [hk, BooleanExpr.eval]

theorem initial_size_le (input : K) (main : Λ) (initialState : σ) (word : List Bool) :
    stackSize (initialConfiguration input main initialState word).stk ≤ word.length := by
  apply Finset.sup_le
  intro k hk
  by_cases he : k = input
  · simp [initialConfiguration, he]
  · simp [initialConfiguration, he]

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeTM2CodeRegisters. -/
section P2MDyadicModule54

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

namespace CodeFamily

theorem initialCode_poly [Coding α] (input : K) (main : Λ) (initialState : σ)
    (length : α → ℕ) (hl : Poly length) : (initialCode input main initialState length).IsPoly := by
  refine ⟨fun l => CodePoly.constant _, fun v => CodePoly.constant _, ?_⟩
  intro k b
  have hc : CodePoly (fun x : α × ℕ => inputCell x.2 b) := by
    cases b with
    | none => exact CodePoly.constant false
    | some b => cases b
                · exact (CodePoly.input (show Poly (fun x : α × ℕ => x.2) by fun_prop)).negate
                · exact CodePoly.input (by fun_prop)
  by_cases hk : k = input
  · simp only [initialCode, hk, true_and]
    have hp : Poly (fun x : α × ℕ => decide (x.2 < length x.1)) := by fun_prop
    simpa only [decide_eq_true_eq] using CodePoly.ite hp hc (CodePoly.constant (decide (b=none)))
  · simpa only [initialCode, hk, false_and, ↓reduceIte] using
      (CodePoly.constant (α := α × ℕ) (decide (b=none)))

theorem reboundCode_poly [Coding α] (width : α → ℕ) (refs : α → List ℕ)
    (hw : Poly width) (hr : Poly refs) : (reboundCode (K := K) (Λ := Λ) (σ := σ) width refs).IsPoly := by
  constructor
  · intro l
    apply CodePoly.input
    fun_prop
  · intro v
    apply CodePoly.input
    fun_prop
  · intro k b
    apply CodePoly.input
    fun_prop

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule54

/- Helper module Solutions.RegevBridgeBooleanRPNBounds. -/
section P2MDyadicModule55

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

theorem code_length (e : BooleanExpr) : (code e).length ≤ 2*e.size+1 := by
  induction e with
  | input i => simp [code, BooleanExpr.size]
  | constant b => cases b <;> simp [code, BooleanExpr.size]
  | negate a ih => simp only [code, List.length_append, List.length_singleton, BooleanExpr.size]; omega
  | xor a b ia ib | and a b ia ib =>
    simp only [code, List.length_append, List.length_singleton, BooleanExpr.size]; omega

theorem valid_code_bits (e : BooleanExpr) (N : ℕ) (h : e.Valid (2^N)) :
    ∀ t ∈ code e, t.2.bits.length ≤ N := by
  induction e with
  | input i =>
    intro t ht
    simp only [code, List.mem_singleton] at ht
    subst t
    change i.bits.length ≤ N
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr h
  | constant b => cases b <;> simp [code]
  | negate a ih =>
    intro t ht
    simp only [code, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ih h t ht
    · simp
  | xor a b ia ib | and a b ia ib =>
    intro t ht
    simp only [code, List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact ia h.1 t ht
    · exact ib h.2 t ht
    · simp

theorem codes_length (es : List BooleanExpr) (C : ℕ) (h : ∀ e ∈ es, e.size ≤ C) :
    (es.flatMap code).length ≤ (2*C+1)*es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := (code_length e).trans (show 2*e.size+1 ≤ 2*C+1 by have := h e (by simp); omega)
    have hh := ih (fun f hf => h f (by simp [hf]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem reverse_operands_bounded {N : ℕ} {s : State} (h : Bounded N s) :
    Bounded N (s.1, s.2.1.reverse, s.2.2) := by
  refine ⟨h.slots, ?_, h.nodes, ?_, h.code⟩
  · simpa only [List.length_reverse] using h.operands
  · intro x hx
    exact h.refs x (List.mem_reverse.mp hx)

theorem clear_operands_bounded {N : ℕ} {s : State} (h : Bounded N s) :
    Bounded N (s.1, [], s.2.2) := ⟨h.slots, Nat.zero_le _, h.nodes, by simp, h.code⟩

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeTM2CodeStep. -/
section P2MDyadicModule56

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem registers_poly : (registers (K := K) (Λ := Λ) (σ := σ)).IsPoly :=
  CodeFamily.reboundCode_poly _ _ (by fun_prop) (by fun_prop)

theorem registers_bounded (x : Input) :
    ((registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Bounded 0 := by
  exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl⟩

theorem registers_valid (x : Input) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ((registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Valid (2^N) := by
  have hb : ∀ i : ℕ, ((x.2.2.1[i]?).getD 0) < 2^N := by
    intro i
    have hi := getD_bound x.2.2.1 i N h
    rw [Nat.size_eq_bits_len] at hi
    exact Nat.size_le.mp hi
  exact ⟨fun _ => hb _, fun _ => hb _, fun _ _ _ => hb _⟩

@[fun_prop] theorem tokens_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (tokens program) :=
  CodeFamily.codes_poly _ (CodeFamily.transitionCode_poly _ (by fun_prop) program _ registers_poly) _ (by fun_prop)

@[fun_prop] theorem step_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (step program) := by
  unfold step
  fun_prop

theorem tokens_length (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) : (tokens program x).length ≤ tokenBound program x.1.length := by
  rw [tokens_eq program x hw]
  have hb := transition_bounded hw program _ 0 (registers_bounded (K := K) (Λ := Λ) (σ := σ) x)
  have hh := codes_length (transition hw program (registers.restrict x x.1.length)).formulas
    (transitionBound program 0) (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      rcases (slotEquiv K Λ σ x.1.length).symm i with l | v | ⟨k,i,b⟩
      · exact hb.label l
      · exact hb.state v
      · exact hb.stack k i b)
  simpa only [Symbolic.formulas_length, tokenBound] using hh

theorem tokens_bits (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ∀ t ∈ tokens program x, t.2.bits.length ≤ N := by
  rw [tokens_eq program x hw]
  have hv := transition_valid hw program _ (registers_valid (K := K) (Λ := Λ) (σ := σ) x N h)
  intro t ht
  obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
  exact valid_code_bits e N ((transition hw program (registers.restrict x x.1.length)).formulas_valid hv e he) t ht

theorem step_bounded (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (N : ℕ) (hN : 3 ≤ N) (h : RPN.Bounded N x.2) :
    RPN.Bounded (N+tokenBound program x.1.length) (step program x).2 := by
  unfold step
  split
  · exact h.mono (Nat.le_add_right _ _)
  · rename_i hw
    have hw' : 0 < x.1.length := by
      have hx : x.1 ≠ [] := by simpa only [List.isEmpty_iff] using hw
      exact List.length_pos_iff.mpr hx
    have hb := run_bounded (tokens program x) (clear_operands_bounded h) hN (tokens_bits program x hw' N h.refs)
    exact (reverse_operands_bounded hb).mono (Nat.add_le_add_left (tokens_length program x hw') N)

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule56

/- Helper module Solutions.RegevBridgeTM2CodeLoop. -/
section P2MDyadicModule57

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem iterateCode_bounded (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit)
    (x : Input) (N : ℕ) (hN : 3 ≤ N) (h : RPN.Bounded N x.2) :
    RPN.Bounded (N+fuel.length*tokenBound program x.1.length) (iterateCode program fuel x).2 := by
  induction fuel generalizing x N with
  | nil => simpa only [iterateCode, List.foldl_nil, List.length_nil, Nat.zero_mul, Nat.add_zero] using h
  | cons u fuel ih =>
    have hs := step_bounded program x N hN h
    have hh := ih (step program x) (N+tokenBound program x.1.length) (by omega) hs
    simpa only [iterateCode, List.foldl_cons, List.length_cons, step_width, Nat.add_mul,
      Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem tokenBound_le (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (width : ℕ) :
    tokenBound program width ≤ tokenRate program*(width+1) := by
  unfold tokenBound tokenRate
  rw [slot_count]
  have h : Fintype.card Λ+1+Fintype.card σ+Fintype.card K*width*3 ≤
      (Fintype.card Λ+1+Fintype.card σ+Fintype.card K*3)*(width+1) := by nlinarith
  have hh := Nat.mul_le_mul_left (2*transitionBound program 0+1) h
  simpa only [Nat.mul_assoc] using hh

theorem iterateCode_partial_bound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (fuel : List Unit) (x : Input) (pre suf : List Unit) (he : fuel=pre++suf) :
    (enc (iterateCode program pre x)).length ≤ (loopBound program).eval (enc (fuel,x)).length := by
  let L := (enc (fuel,x)).length
  have heL : L = 2*fuel.length+1+2*x.1.length+1+(enc x.2).length := by
    change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) (fuel,x)).length = _
    simp only [encodePair_length, encodedUnit_length]
    omega
  have hw : x.1.length ≤ L := by omega
  have hp : pre.length ≤ L := by have hh := congrArg List.length he; simp only [List.length_append] at hh; omega
  have hs := (bounded_of_encoding x.2).mono (show (enc x.2).length ≤ L+3 by omega)
  have hb := iterateCode_bounded program pre x (L+3) (by omega) hs
  have ht := (tokenBound_le program x.1.length).trans
    (Nat.mul_le_mul_left (tokenRate program) (Nat.add_le_add_right hw 1))
  have hm : pre.length * tokenBound program x.1.length ≤ L*tokenRate program*(L+1) := by
    exact (Nat.mul_le_mul hp ht).trans_eq (Nat.mul_assoc _ _ _).symm
  have hb' := hb.mono (Nat.add_le_add_left hm (L+3))
  have hh := encoding_bound hb'
  have hwidth := iterateCode_width program pre x
  have henc : (enc (iterateCode program pre x)).length = 2*x.1.length+1+(enc (iterateCode program pre x).2).length := by
    change (encodePair (enc : List Unit → List Bool) enc (iterateCode program pre x)).length = _
    rw [encodePair_length, encodedUnit_length, hwidth]
  simp only [loopBound, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_pow, eval_C]
  change _ ≤ 2*L+1+20*(L+3+L*tokenRate program*(L+1)+1)^2
  omega

@[fun_prop] theorem iterateCode_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Poly (fun x : List Unit × Input => iterateCode program x.1 x.2) := by
  have hs : Poly (fun x : Input × Unit => step program x.1) := by fun_prop
  apply Automatic.Poly.of_program
  exact hs.program.listFold () (loopBound program) (by
    intro fuel x pre suf he
    change (enc (iterateCode program pre x)).length ≤ (loopBound program).eval (enc (fuel,x)).length
    exact iterateCode_partial_bound program fuel x pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule57

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule58

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem Encodes.get {sym : Symbolic K Λ σ width} {cfg : Configuration K Λ σ}
    {bits : ℕ → Bool} (h : Encodes sym cfg bits) (i : Slot K Λ σ width) :
    (sym.get i).eval bits = configurationBit cfg i := by
  rcases i with l | v | ⟨k, i, b⟩
  · exact h.label l
  · exact h.state v
  · exact h.stack k i b

theorem compileRun_rebound_bounded (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (compileRun hw program ticks start sym).2.Bounded 0 := by
  induction ticks generalizing start sym with
  | zero => exact h
  | succ ticks ih => exact ih _ _ ((transition hw program sym).rebound_bounded_zero start)

theorem machineProgram_length_le (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    (machineProgram hw program input main initialState ticks length).ops.length ≤
      (1 + ticks * transitionBound program 0) * Fintype.card (Slot K Λ σ width) := by
  let init := initial input main initialState length width
  have hi : init.Bounded 1 := initial_bounded input main initialState length width
  have hp := init.compiled_length_le length 1 hi
  have hm := compileRun_length_le hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  have hz := compileRun_rebound_bounded hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  let middle := compileRun hw program ticks (length + (init.compiled length).1.length) (init.rebound length)
  have he := middle.2.compiled_length_le
    (length + (init.compiled length).1.length + middle.1.length) 0 hz
  change ((init.compiled length).1 ++ middle.1 ++
    (middle.2.compiled (length + (init.compiled length).1.length + middle.1.length)).1).length ≤ _
  simp only [List.length_append]
  nlinarith

/-- The whole generated straight-line program computes every field of the budgeted machine execution. -/
theorem machineProgram_semantics (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i])
    (hsize : word.length + programPushBound program * ticks ≤ width) (i : Slot K Λ σ width) :
    BooleanProgram.run word.length (machineProgram hw program input main initialState ticks word.length).ops bits
      ((machineProgram hw program input main initialState ticks word.length).output i) =
      configurationBit ((stickyStep program)^[ticks] (initialConfiguration input main initialState word)) i := by
  let init := initial input main initialState word.length width
  have hi : init.Valid word.length := initial_valid input main initialState word.length width
  have he : Encodes init (initialConfiguration input main initialState word) bits :=
    initial_encodes input main initialState width word bits hbits
  have hp := init.rebound_encodes word.length hi _ bits he
  have hr := compileRun_encodes hw program ticks _ _ _ _
    (init.rebound_valid word.length hi) hp
    ((Nat.add_le_add_right (initial_size_le input main initialState word) _).trans hsize)
  have hv := (compileRun_valid hw program ticks _ _ (init.rebound_valid word.length hi)).2
  let middle := compileRun hw program ticks (word.length + (init.compiled word.length).1.length)
    (init.rebound word.length)
  have ho := middle.2.output_eval _ hv
    (BooleanProgram.run (word.length + (init.compiled word.length).1.length) middle.1
      (BooleanProgram.run word.length (init.compiled word.length).1 bits)) i
  rw [hr.get i] at ho
  simpa only [machineProgram, BooleanProgram.run_append, List.length_append, Nat.add_assoc, init, middle] using ho

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule58

/- Helper module Solutions.RegevBridgeTM2CodeGenerate. -/
section P2MDyadicModule59

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

@[fun_prop] theorem initialResult_poly (input : K) (main : Λ) (initialState : σ) :
    Poly (initialResult input main initialState) :=
  CodeFamily.compile_poly _ (CodeFamily.initialCode_poly _ _ _ _ (by fun_prop)) _ _ (by fun_prop) (by fun_prop)

@[fun_prop] theorem initialInput_poly (input : K) (main : Λ) (initialState : σ) :
    Poly (initialInput input main initialState) := by
  unfold initialInput
  fun_prop

@[fun_prop] theorem generate_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) : Poly (generate program input main initialState) := by
  unfold generate
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule59

/- Helper module Solutions.RegevBridgeBooleanNodeSerialization. -/
section P2MDyadicModule60

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem boundedNat_poly : Poly (fun x : List Unit × ℕ => boundedNat x.1 x.2) := by
  unfold boundedNat
  fun_prop

@[fun_prop] theorem instructionWord_poly :
    Poly (fun x : List Unit × (ℕ × Node) => instructionWord x.1 x.2.1 x.2.2) := by
  unfold instructionWord
  fun_prop

@[fun_prop] theorem instructionWords_poly :
    Poly (fun x : List Unit × (ℕ × List Node) => instructionWords x.1 x.2.1 x.2.2) := by
  unfold instructionWords
  apply Automatic.Poly.list_map
  · fun_prop
  · exact Automatic.Poly.comp (f := fun xs : List Node => List.range xs.length)
      (g := fun x : List Unit × (ℕ × List Node) => x.2.2) Automatic.Poly.list_indices (by fun_prop)

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule60

/- Helper module Solutions.AdvantageBridgeQuantumCoins. -/
section P2MDyadicModule61

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

theorem coinZero_mass (count : ℕ) : (∑ state,‖coinZero count state‖^2)=(1 : ℝ) := by
  classical
  rw [Finset.sum_eq_single (fun _ : Fin count => false)]
  · simp [coinZero]
  · intro state _ hne
    simp [coinZero,hne]
  · simp

theorem coinZero_tensor (first second : ℕ) : coinZero (first+second)=tensorState (coinZero first) (coinZero second) := by
  funext state
  have hzero : state=(fun _ => false) ↔ leftRegister state=(fun _ => false) ∧ rightRegister state=(fun _ => false) := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · rintro ⟨hl,hr⟩
      funext index
      refine Fin.addCases ?_ ?_ index
      · intro i
        exact congrArg (fun word => word i) hl
      · intro i
        exact congrArg (fun word => word i) hr
  by_cases hl : leftRegister state=(fun _ => false)
  · by_cases hr : rightRegister state=(fun _ => false)
    · change (if state=(fun _ => false) then (1 : ℂ) else 0)=
        (if leftRegister state=(fun _ => false) then 1 else 0)*
          (if rightRegister state=(fun _ => false) then 1 else 0)
      rw [if_pos (hzero.mpr ⟨hl,hr⟩),if_pos hl,if_pos hr,mul_one]
    · have hs : state ≠ (fun _ => false) := fun h => hr (hzero.mp h).2
      simp [coinZero,tensorState,hl,hr,hs]
  · have hs : state ≠ (fun _ => false) := fun h => hl (hzero.mp h).1
    simp [coinZero,tensorState,hl,hs]

private theorem one_coin_uniform : runLayered [[.h (0 : Fin 1)]] (coinZero 1)=
    (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) := by
  funext state
  have hf : Function.update state (0 : Fin 1) false=(fun _ => false) := by
    funext index
    have hi : index=0 := Subsingleton.elim _ _
    subst index
    simp
  have ht : Function.update state (0 : Fin 1) true ≠ (fun _ => false) := by
    intro h
    have hh := congrArg (fun word => word 0) h
    simp at hh
  simp only [runLayered,runLayer,List.foldl_cons,List.foldl_nil,Instr.apply,apply1,Fintype.sum_bool]
  simp [coinZero,hf,ht,hMat]

/-- The actual coin preparation circuit has uniform positive amplitudes,
not only the correct total norm. -/
theorem coinCircuit_uniform (count : ℕ) : runLayered (coinCircuit count) (coinZero count)=
    (fun _ => coinAmplitude count) := by
  induction count with
  | zero =>
    funext state
    have hs : state=(fun _ : Fin 0 => false) := Subsingleton.elim _ _
    simp [coinCircuit,runLayered,coinZero,coinAmplitude,hs]
  | succ count ih =>
    rw [coinCircuit,coinZero_tensor count 1,disjointCircuits_tensor,ih,one_coin_uniform]
    funext state
    exact (pow_succ _ count).symm

/-- Each actual Hadamard output has precisely uniform Boolean point mass. -/
theorem coinAmplitude_mass (count : ℕ) : ‖coinAmplitude count‖^2=(Fintype.card (Bits count) : ℝ)⁻¹ := by
  have h := runLayered_mass (coinCircuit count) (coinZero count)
  simp only [coinCircuit_uniform,Complex.normSq_eq_norm_sq] at h
  rw [coinZero_mass] at h
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  have hc : (Fintype.card (Bits count) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (mul_left_cancel₀ hc)
  rw [h,mul_inv_cancel₀ hc]

section Description

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

end Description

end InfoLossLAR.WorstCase

end P2MDyadicModule61

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule62

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

private theorem append_registers_iff {n m : ℕ} (state : Bits (n+m)) (left : Bits n) (right : Bits m) :
    state=Fin.append left right ↔ leftRegister state=left ∧ rightRegister state=right := by
  constructor
  · rintro rfl
    exact ⟨by funext i; simp [leftRegister],by funext i; simp [rightRegister]⟩
  · rintro ⟨hl,hr⟩
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro i
      simpa only [Fin.append_left,leftRegister] using congrArg (fun word => word i) hl
    · intro i
      simpa only [Fin.append_right,rightRegister] using congrArg (fun word => word i) hr

/-- The actual platform input state is exactly the full computational-basis
word consisting of its input followed by the required zero ancillas. -/
theorem basisInput_eq_computationalBasis {n a : ℕ} (input : Bits n) :
    basisInput (a := a) input=computationalBasis (Fin.append input (fun _ => false)) := by
  funext state
  unfold basisInput computationalBasis
  congr 1
  apply propext
  rw [append_registers_iff]
  simp only [funext_iff,leftRegister,rightRegister]

theorem computationalBasis_tensor {n m : ℕ} (left : Bits n) (right : Bits m) :
    computationalBasis (Fin.append left right)=tensorState (computationalBasis left) (computationalBasis right) := by
  funext state
  change (if state=Fin.append left right then (1 : ℂ) else 0)=
    (if leftRegister state=left then 1 else 0)*(if rightRegister state=right then 1 else 0)
  by_cases hl : leftRegister state=left
  · by_cases hr : rightRegister state=right
    · rw [if_pos ((append_registers_iff state left right).mpr ⟨hl,hr⟩),if_pos hl,if_pos hr,mul_one]
    · have hs : state ≠ Fin.append left right := fun h => hr ((append_registers_iff state left right).mp h).2
      rw [if_neg hs,if_pos hl,if_neg hr,mul_zero]
  · have hs : state ≠ Fin.append left right := fun h => hl ((append_registers_iff state left right).mp h).1
    rw [if_neg hs,if_neg hl,zero_mul]

end InfoLossLAR.WorstCase

end P2MDyadicModule62

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule63

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem wordExtension_before (word : List Bool) (i : ℕ) (h : i < word.length) :
    wordExtension word i = word[i] := by simp only [wordExtension, List.getElem?_eq_getElem h, Option.getD_some]

theorem wordExtension_after (word : List Bool) (i : ℕ) (h : word.length ≤ i) :
    wordExtension word i = false := by simp only [wordExtension, List.getElem?_eq_none h, Option.getD_none]

theorem wordExtension_basis (word : List Bool) (ancillas : ℕ) :
    Fin.append (toBits word) (fun _ : Fin (ancillas + 1) => false) =
      (fun i : Fin (word.length + (ancillas + 1)) => wordExtension word i.val) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left, Fin.coe_castAdd, toBits, List.get_eq_getElem] using
      (wordExtension_before word j.val j.isLt).symm
  · intro j
    simp only [Fin.append_right, Fin.val_natAdd]
    exact (wordExtension_after word _ (Nat.le_add_right _ _)).symm

/-- This is the literal Clifford+T circuit on the platform's actual input basis state. -/
theorem machineCircuit_basis (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ) (word : List Bool) :
    runLayered (machineCircuit hw program input main initialState ticks word.length)
      (basisInput (toBits word)) = computationalBasis (fun j =>
        BooleanProgram.run word.length (machineProgram hw program input main initialState ticks word.length).ops
          (wordExtension word) j.val) := by
  rw [basisInput_eq_computationalBasis, wordExtension_basis]
  exact BooleanProgram.circuit_basis _ _
    (machineProgram_valid hw program input main initialState ticks word.length).1
    (wordExtension word) (fun i hi _ => wordExtension_after word i hi)

/-- Reading any output slot of the compiled basis state recovers the actual budgeted machine field. -/
theorem machineCircuit_output (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ) (word : List Bool)
    (hsize : word.length + programPushBound program * ticks ≤ width) (i : Slot K Λ σ width) :
    (fun j => BooleanProgram.run word.length
      (machineProgram hw program input main initialState ticks word.length).ops (wordExtension word) j.val)
      (machineOutputWire hw program input main initialState ticks word.length i) =
      configurationBit ((stickyStep program)^[ticks] (initialConfiguration input main initialState word)) i :=
  machineProgram_semantics hw program input main initialState ticks word (wordExtension word)
    (wordExtension_before word) hsize i

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule63

/- Helper module Solutions.RegevBridgeTM2CodeDescription. -/
section P2MDyadicModule64

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

@[fun_prop] theorem description_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) :
    Poly (fun x : Request × ℕ => description program input main initialState x.1 x.2) := by
  unfold description
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule64

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule65

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing StateTransition QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

open OAI.MetricKMedian.Binary

namespace PolyProgramCircuit

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions

theorem final_configuration (word : Str) :
    (stickyStep P.machine.code)^[P.time.eval word.length]
      (initialConfiguration P.machine.input P.machine.main P.machine.initial word) =
        P.machine.finalCfg (f word) := by
  have hh := P.outputs word
  change EvalsToInTime (TM2.step P.machine.code)
    (initialConfiguration P.machine.input P.machine.main P.machine.initial word)
    (some (P.machine.finalCfg (f word))) (P.time.eval word.length) at hh
  exact sticky_iterate_of_outputs P.machine.code _ _ _ hh rfl

/-- The real fixed-gate circuit computes the machine's complete deterministic basis output. -/
theorem circuit_basis (word : Str) :
    runLayered (circuit P word.length) (basisInput (toBits word)) = computationalBasis (result P word) :=
  machineCircuit_basis _ _ _ _ _ _ word

/-- An actual output wire gives each present/absent symbol of the encoded function output. -/
theorem output_correct (word : Str) (i : Fin (capacity P word.length)) (b : Option Bool) :
    result P word (outputWire P word.length i b) = decide (b = (f word)[i.val]?) := by
  have hh := machineCircuit_output (capacity_pos P word.length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval word.length) word (by unfold capacity; omega)
    (.inr (.inr (P.machine.output, i, b)))
  rw [final_configuration P word] at hh
  simpa only [result, outputWire, compiled, configurationBit, Machine.finalCfg, ↓reduceIte] using hh

theorem spacePolynomial_eval (length : ℕ) :
    (spacePolynomial P).eval length =
      (1 + P.time.eval length * transitionBound P.machine.code 0) *
        Fintype.card (Slot P.machine.K P.machine.Label P.machine.State (capacity P length)) := by
  simp only [spacePolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, slot_count, capacity]
  ring

theorem ancilla_bound (length : ℕ) : (compiled P length).ops.length ≤ (spacePolynomial P).eval length := by
  rw [spacePolynomial_eval]
  exact machineProgram_length_le _ _ _ _ _ _ _

end PolyProgramCircuit

end InfoLossLAR.WorstCase.TM2Boolean

end

end P2MDyadicModule65

/- Helper module Solutions.RegevBridgeTM2PolyUniform. -/
section P2MDyadicModule66

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open Turing StateTransition QAlgorithms.Complexity Polynomial

open Integration9_9.TM2OutputLength Integration9_9.TM2PlatformSerialization

open Integration9_9.TM2PolynomialBudget

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CodeGenerator

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_1

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_1

@[fun_prop] theorem request_poly : Poly (request P) := by
  unfold request
  fun_prop

@[fun_prop] theorem descriptionGenerator_poly : Poly (descriptionGenerator P) := by
  unfold descriptionGenerator outputIndex
  fun_prop

theorem family_circuit (n : ℕ) : (family P).circ n = circuit P n := rfl

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule66

/- Helper module Solutions.RegevBridgeNativeWordControlProgram. -/
section P2MDyadicModule67

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.NativeWordControls

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

theorem rawControls_length (x : Input) : (rawControls x).length=12*x.2.length := by
  simp [rawControls]

theorem rawCurrent_length (words : Str → List ℕ) (p : Polynomial ℕ) (word : Str) :
    (rawCurrent words p word).length=12*p.eval word.length := by
  simp only [rawCurrent,rawControls_length,List.length_replicate]

end InfoLossLAR.WorstCase.NativeWordControls

end P2MDyadicModule67

/- Helper module Solutions.AdvantageBridgeCoinMachine. -/
section P2MDyadicModule68

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

private theorem word_value_ofFn (count : ℕ) (tape : Fin count → Bool) :
    Word.value (List.ofFn tape)=∑ index,(tape index).toNat*2^index.val := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [List.ofFn_succ,Word.value_cons,Fin.sum_univ_succ,Fin.val_zero,pow_zero,
      mul_one,Fin.val_succ]
    rw [ih]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [pow_succ]
    ring

/-- The actual binary-value machine reads precisely the fair-bit ticket
used by the proved rejection-sampling law. -/
theorem bitValue_boundedBoolTicket (count : ℕ) (tape : Fin count → Bool) :
    bitValue (List.ofFn tape)=(boundedBoolTicket count tape).val := by
  rw [bitValue_eq_word,word_value_ofFn]
  change (∑ index,(tape index).toNat*2^index.val)=
    ∑ index,((finTwoEquiv.symm (tape index)).val)*2^index.val
  apply Finset.sum_congr rfl
  intro index _
  cases tape index <;> rfl

end Integration9_9.LARCoinMachine

end P2MDyadicModule68

/- Helper module Solutions.AdvantageBridgeQueryQuantum. -/
section P2MDyadicModule69

set_option autoImplicit false

set_option maxHeartbeats 500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open Integration9_9.TM2OutputLength

/-- The real machine's complete output fits in the compiled finite slot register. -/
theorem actualOutput_length_lt_capacity {f : Str → Str} (P : PolyProgram id id f) (word : Str) :
    (f word).length<capacity P word.length := by
  have h := output_length_le P.machine.tm word (f word) (P.time.eval word.length) (P.outputs word)
  change (f word).length≤word.length+programPushBound P.machine.code*P.time.eval word.length at h
  unfold capacity
  omega

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

open LARRankOneMachine

end Integration9_9.LARCoinLayout

end P2MDyadicModule69

/- Helper module Solutions.AdvantageBridgeQueryMetadata. -/
section P2MDyadicModule70

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CodeGenerator

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_3

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_3

@[fun_prop] theorem outputSlotIndex_poly :
    Poly (fun x : ℕ × ℕ => outputSlotIndex P x.1 x.2) := by
  unfold outputSlotIndex
  fun_prop

theorem outputSlotIndex_eq (width : ℕ) (index : Fin width) :
    outputSlotIndex P width index.val=
      (slotEquiv P.machine.K P.machine.Label P.machine.State width
        (.inr (.inr (P.machine.output,index,some true)))).val :=
  (slot_stack_index width P.machine.output index (some true)).symm

@[fun_prop] theorem generatedOutputAddress_poly :
    Poly (fun x : Request × ℕ => generatedOutputAddress P x.1 x.2) := by
  unfold generatedOutputAddress
  fun_prop

theorem generatedOutputAddress_eq (x : Request) (hw : 0<x.2.1.length) (index : Fin x.2.1.length) :
    generatedOutputAddress P x index.val=
      (machineProgram hw P.machine.code P.machine.input P.machine.main P.machine.initial
        x.2.2.length x.1.length).output (.inr (.inr (P.machine.output,index,some true))) := by
  unfold generatedOutputAddress
  rw [outputSlotIndex_eq]
  exact (generate_machineProgram P.machine.code P.machine.input P.machine.main P.machine.initial x hw).2.2 _

@[fun_prop] theorem generatedProgramOutputAddress_poly :
    Poly (fun x : Str × ℕ => generatedProgramOutputAddress P x.1 x.2) := by
  unfold generatedProgramOutputAddress
  fun_prop

/-- Exact transport of the physical program output across an equal stack capacity. -/
theorem outputProgram_transport {a b : ℕ} (he : a=b) (ha : 0<a) (hb : 0<b)
    (ticks length : ℕ) (index : Fin a) :
    (machineProgram ha P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).output
      (.inr (.inr (P.machine.output,index,some true)))=
    (machineProgram hb P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).output
      (.inr (.inr (P.machine.output,Fin.cast he index,some true))) := by
  cases he
  rfl

/-- On each unary request, the emitted natural address is literally the
physical outputWire of the verified uniform compiler. -/
theorem generatedProgramOutputAddress_eq (length : ℕ) (index : Fin (capacity P length)) :
    generatedProgramOutputAddress P (unary length) index.val=(outputWire P length index (some true)).val := by
  unfold generatedProgramOutputAddress
  rw [request_unary]
  let width := (List.replicate (capacity P length) ()).length
  have hwidth : width=capacity P length := List.length_replicate
  have hw : 0<width := by rw [hwidth]; exact capacity_pos P length
  let i : Fin width := ⟨index.val,by rw [hwidth]; exact index.isLt⟩
  have hi : Fin.cast hwidth i=index := Fin.ext rfl
  have h := generatedOutputAddress_eq P
    (List.replicate length (),List.replicate (capacity P length) (),List.replicate (P.time.eval length) ()) hw i
  simp only [List.length_replicate] at h
  have he := outputProgram_transport P hwidth hw (capacity_pos P length) (P.time.eval length) length i
  rw [he,hi] at h
  simpa only [outputWire,machineOutputWire,compiled,i] using h

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule70

/- Helper module Solutions.RegevBridgeTM2MultiOutput. -/
section P2MDyadicModule71

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget RPN

open scoped BigOperators Classical

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_4

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_4

@[fun_prop] theorem quantumDescription_poly : Poly (quantumDescription P) := by
  unfold quantumDescription
  fun_prop

theorem quantumDescription_code (n : ℕ) : quantumDescription P (unary n)=encFamilyAt (family P) n := by
  unfold quantumDescription
  rw [descriptionGenerator_code,compileBooleanDescription_code,compileReversibleDescription_code]
  rfl

@[fun_prop] theorem multiTotalSlots_poly : Poly (multiTotalSlots P) := by
  have hp : Poly (fun word : Str => List.replicate ((spacePolynomial P).eval word.length) ()) := by
    have h := Poly.comp (f := fun xs : List Unit => List.replicate ((spacePolynomial P).eval xs.length) ())
      (g := fun word : Str => word.map (fun _ => ())) (polynomialSlots_poly (spacePolynomial P)) (by fun_prop)
    simpa only [List.length_map] using h
  unfold multiTotalSlots
  fun_prop

theorem paddedOutput_eq_append (word : Str) :
    paddedOutput P word=f word++List.replicate (capacity P word.length-(f word).length) false := by
  have hl := actualOutput_length_lt_capacity P word
  apply List.ext_getElem
  · simp only [paddedOutput,List.length_ofFn,List.length_append,List.length_replicate]
    omega
  · intro index hleft hright
    simp only [paddedOutput,List.getElem_ofFn]
    by_cases hi : index < (f word).length
    · simp [List.getElem_append_left hi,List.getElem?_eq_getElem hi]
    · simp [List.getElem_append_right (Nat.le_of_not_gt hi),List.getElem?_eq_none (Nat.le_of_not_gt hi)]

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule71

/- Helper module Solutions.RegevBridgeControlledRelocation. -/
section P2MDyadicModule72

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ControlledRelocation

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open ControlledLetterPlan

/-- Every control is a retained spectator, never a data or local ancilla wire. -/
abbrev Operation {k n : ℕ} (w : Fin k ↪ Fin n) :=
  {c : Fin n // c ∉ Set.range w} × Letter k

theorem outside_avoids {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : {c : Fin n // c ∉ Set.range w}) (gate : Letter k) : Avoids c.val (gate.relocate w) := by
  have hc (i : Fin k) : c.val≠w i := by
    intro h
    exact c.property ⟨i,h.symm⟩
  cases gate with
  | h i => exact hc i
  | t i => exact hc i
  | cnot i j hij => exact ⟨hc i,hc j⟩

def program {k n : ℕ} (w : Fin k ↪ Fin n) (ops : List (Operation w)) : List (Atom n) :=
  ops.flatMap (fun op => plan op.1.val (op.2.relocate w) (outside_avoids w op.1 op.2))

end InfoLossLAR.WorstCase.ControlledRelocation

end P2MDyadicModule72

/- Helper module Solutions.RegevBridgeControlledWordInterpreter. -/
section P2MDyadicModule73

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ControlledWordInterpreter

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport FiniteGateNativeEnumeration

open ControlledRelocation NativeWordControls

/-- Publicly placed one-hot controls. All are outside the data register. -/
def operationGrid {n : ℕ} (w : Fin 3 ↪ Fin n)
    (controls : ℕ → ℕ → {c : Fin n // c∉Set.range w}) (slots : ℕ) :
    List (Operation w) :=
  (List.range slots).flatMap (fun slot => (List.range 12).map
    (fun code => (controls slot code,letterOfCode code)))

end InfoLossLAR.WorstCase.ControlledWordInterpreter

end P2MDyadicModule73

/- Helper module Solutions.RegevBridgeNativeWordLayout. -/
section P2MDyadicModule74

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordLayout

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan ControlledRelocation

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

variable {f : Str → Str} (P : PolyProgram id id f) (p : Polynomial ℕ)

local instance : DecidableEq P.machine.Label := Classical.decEq _

local instance : DecidableEq P.machine.State := Classical.decEq _

@[fun_prop] theorem machineWidth_poly : Poly (machineWidth P) := by unfold machineWidth;fun_prop

private theorem machine_ops_transport {a b : ℕ} (he : a=b) (ha : 0<a) (hb : 0<b)
    (ticks length : ℕ) :
    (machineProgram ha P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).ops=
      (machineProgram hb P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).ops := by
  cases he
  rfl

theorem machineWidth_eq (n : ℕ) : machineWidth P (unary n)=width P n := by
  have hwidth : (request P (unary n)).2.1.length=capacity P n := by
    rw [request_unary,List.length_replicate]
  have hw : 0<(request P (unary n)).2.1.length := hwidth.symm ▸ capacity_pos P n
  have ht : (request P (unary n)).2.2.length=P.time.eval n := by
    rw [request_unary,List.length_replicate]
  have hn : (request P (unary n)).1.length=n := by rw [request_unary,List.length_replicate]
  have hh :=(generate_machineProgram P.machine.code P.machine.input P.machine.main P.machine.initial
    (request P (unary n)) hw).1
  have ho:=machine_ops_transport P hwidth hw (capacity_pos P n) (P.time.eval n) n
  rw [ht,hn,ho] at hh
  unfold machineWidth
  rw [hh,List.length_map]
  simp only [unary,List.length_replicate,compiled,width]
  omega

@[fun_prop] theorem slots_poly : Poly (slots p) := by
  have hh :=Poly.comp (polynomialSlots_poly p) (by fun_prop : Poly (fun word : Str => word.map (fun _ => ())))
  unfold slots
  simpa only [List.length_map] using hh

theorem slots_length (word : Str) : (slots p word).length=p.eval word.length := by
  simp only [slots,List.length_replicate]

@[fun_prop] theorem address_poly : Poly (fun x : Str×(ℕ×ℕ) => address P x.1 x.2.1 x.2.2) := by
  unfold address
  fun_prop

/-- The three data wires are strictly after every machine control/output wire. -/
def dataWires (n : ℕ) : Fin 3 ↪ Fin (width P n+3) := Fin.natAddEmb (width P n)

def controlIndex (n slot code : ℕ) : Fin (capacity P n) :=
  if h : 12*slot+code< capacity P n then ⟨12*slot+code,h⟩ else ⟨0,capacity_pos P n⟩

def controlWire (n slot code : ℕ) : Fin (width P n+3) :=
  (outputWire P n (controlIndex P n slot code) (some true)).castAdd 3

def controls (n slot code : ℕ) : {c : Fin (width P n+3) // c∉Set.range (dataWires P n)} :=
  ⟨controlWire P n slot code,by
    rintro ⟨i,hi⟩
    have hv :=congrArg Fin.val hi
    have ht :=(outputWire P n (controlIndex P n slot code) (some true)).isLt
    change width P n+i.val=(outputWire P n (controlIndex P n slot code) (some true)).val at hv
    change _< width P n at ht
    omega⟩

def SlotsFit : Prop := ∀ n,12*p.eval n< capacity P n

theorem address_eq (hfit : SlotsFit P p) (n slot code : ℕ)
    (hs : slot< p.eval n) (hc : code<12) :
    address P (unary n) slot code=(controls P n slot code).val.val := by
  have hin : 12*slot+code< capacity P n := by have hh:=hfit n;omega
  change generatedProgramOutputAddress P (unary n) (12*slot+code)=_
  rw [show 12*slot+code=(controlIndex P n slot code).val by simp only [controlIndex,dif_pos hin]]
  rw [generatedProgramOutputAddress_eq]
  rfl

def typedGrid (n : ℕ) : List (Operation (dataWires P n)) :=
  ControlledWordInterpreter.operationGrid (dataWires P n) (controls P n) (p.eval n)

def idealAtoms (n : ℕ) : List (Atom (width P n+3)) := program (dataWires P n) (typedGrid P p n)

attribute [local irreducible] machineWidth address slots

@[fun_prop] theorem atomGrid_poly : Poly (atomGrid P p) := by
  unfold atomGrid
  apply Poly.list_flatMap
  · apply Poly.list_flatMap
    · have ha : Poly (fun x : (Str×ℕ)×ℕ => address P x.1.1 x.1.2 x.2) :=
        Poly.comp (f:=fun x : Str×(ℕ×ℕ) => address P x.1 x.2.1 x.2.2)
          (g:=fun x : (Str×ℕ)×ℕ => (x.1.1,(x.1.2,x.2))) (address_poly P) (by fun_prop)
      have hm : Poly (fun x : (Str×ℕ)×ℕ => machineWidth P x.1.1) :=
        Poly.comp (f:=machineWidth P) (g:=fun x : (Str×ℕ)×ℕ => x.1.1) (machineWidth_poly P) (by fun_prop)
      have hi : Poly (fun x : (Str×ℕ)×ℕ =>
          (address P x.1.1 x.1.2 x.2,((machineWidth P x.1.1,machineWidth P x.1.1+1,machineWidth P x.1.1+2),x.2))) := by
        fun_prop
      exact Poly.comp ControlledPlanNative.current_poly hi
    · exact Automatic.Poly.const (List.range 12)
  · exact Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=slots p) Poly.list_indices (slots_poly p)

theorem current_poly (a : ℕ) : Poly (current P p a) := by
  unfold current
  exact Poly.comp (ControlledNativeCode.compile_poly a) (by fun_prop)

end InfoLossLAR.WorstCase.NativeWordLayout

end

end P2MDyadicModule74

/- Helper module Solutions.RegevBridgeNativeWordLayoutSemantics. -/
section P2MDyadicModule75

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordLayout

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan ControlledRelocation

open ControlledNativeCode ControlledNativeGates

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable {f : Str → Str} (P : PolyProgram id id f) (p : Polynomial ℕ)

theorem plan_code_eq (hfit : SlotsFit P p) (n slot code : ℕ)
    (hs : slot< p.eval n) (hc : code<12) :
    ControlledPlanNative.current (address P (unary n) slot code,
      ((machineWidth P (unary n),machineWidth P (unary n)+1,machineWidth P (unary n)+2),code))=
      (plan (controls P n slot code).val ((FiniteGateNativeEnumeration.letterOfCode code).relocate (dataWires P n))
        (outside_avoids (dataWires P n) (controls P n slot code) _)).map encodeAtom := by
  rw [machineWidth_eq,address_eq P p hfit n slot code hs hc]
  have hh :=ControlledPlanNative.current_encode (controls P n slot code).val (dataWires P n)
    (by intro i he;exact (controls P n slot code).property ⟨i,he.symm⟩) code
  exact hh

theorem atomGrid_eq (hfit : SlotsFit P p) (n : ℕ) :
    atomGrid P p (unary n)=(idealAtoms P p n).map encodeAtom := by
  simp only [atomGrid,slots_length,unary,List.length_replicate,idealAtoms,typedGrid,program,
    ControlledWordInterpreter.operationGrid,List.map_flatMap,List.flatMap_assoc,List.flatMap_map,Function.comp_def]
  apply List.flatMap_congr
  intro slot hs
  apply List.flatMap_congr
  intro code hc
  exact plan_code_eq P p hfit n slot code (List.mem_range.mp hs) (List.mem_range.mp hc)

theorem current_codes (hfit : SlotsFit P p) (n a : ℕ) (budget : List Unit) :
    current P p a (unary n,budget)=
      (gates a budget (idealAtoms P p n)).map encodeInstr := by
  unfold current
  rw [machineWidth_eq,atomGrid_eq P p hfit n]
  exact gates_codes a budget (idealAtoms P p n)

theorem current_decode (hfit : SlotsFit P p) (n a : ℕ) (budget : List Unit) :
    (current P p a (unary n,budget)).filterMap (decodeGate (width P n+3+2))=
      gates a budget (idealAtoms P p n) := by
  rw [current_codes P p hfit n a budget,List.filterMap_map]
  simp only [Function.comp_def,decode_encode,List.filterMap_some]

/-- The genuine raw-control native TM2 program always has enough output cells
for all twelve one-hot flags at every public polynomially bounded slot. -/
theorem rawSlotsFit (words : Str → List ℕ) (hw : Poly words) (bound : Polynomial ℕ) :
    SlotsFit (NativeWordControls.rawCurrentProgram words hw bound) bound := by
  intro n
  have hh:=actualOutput_length_lt_capacity (NativeWordControls.rawCurrentProgram words hw bound) (unary n)
  change (NativeWordControls.rawCurrent words bound (unary n)).length< _ at hh
  simpa only [NativeWordControls.rawCurrent_length,unary,List.length_replicate] using hh

end InfoLossLAR.WorstCase.NativeWordLayout

end

end P2MDyadicModule75

/- Helper module Solutions.RegevBridgeCoherentComputeUncompute. -/
section P2MDyadicModule76

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open FiniteGateTransport

open scoped BigOperators

variable {D W I : Type*} [Fintype D] [Fintype W] [DecidableEq W]

noncomputable def tensor (v : D → ℂ) (w : W) : D×W → ℂ := fun p => v p.1*basis w p.2

/-- Reversible work computation acts on the full work register, retaining the
fresh data register as an arbitrary coherent reference. -/
noncomputable def onWork (U : (W → ℂ) →ₗ[ℂ] (W → ℂ)) :
    (D×W → ℂ) →ₗ[ℂ] (D×W → ℂ) where
  toFun ψ p := U (fun r => ψ (p.1,r)) p.2
  map_add' ψ φ := by
    funext p
    change U ((fun r => ψ (p.1,r))+(fun r => φ (p.1,r))) p.2=_
    rw [map_add]
    rfl
  map_smul' c ψ := by
    funext p
    change U (c • (fun r => ψ (p.1,r))) p.2=_
    rw [map_smul]
    rfl

theorem onWork_tensor (U : (W → ℂ) →ₗ[ℂ] (W → ℂ)) (v : D → ℂ) (w r : W)
    (hU : U (basis w)=basis r) : onWork U (tensor v w)=tensor v r := by
  funext p
  change U ((v p.1) • basis w) p.2=v p.1*basis r p.2
  rw [map_smul,hU]
  rfl

/-- Actual circuit inversion supplies cleanup from the basis semantics of
the forward computation; no independent inverse-oracle assumption is needed. -/
theorem inverse_basis {n : ℕ} (gates : QAlgorithms.Complexity.Layered n)
    (input computed : QAlgorithms.Complexity.Bits n)
    (h : runLayeredLinearMap gates (basis input)=basis computed) :
    runLayeredLinearMap (inverseCircuit gates) (basis computed)=basis input := by
  rw [←h,runLayeredLinearMap_apply,runLayeredLinearMap_apply]
  exact inverseCircuit_left gates (basis input)

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end P2MDyadicModule76

/- Helper module Solutions.RegevBridgeNativeWordCoherentCompute. -/
section P2MDyadicModule77

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan

open NativeWordLayout ControlledNativeGates

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

/-- Physical ordering is the complete work register followed by data. -/
def assembleMap (W k : ℕ) : (Bits k×Bits W → ℂ) →ₗ[ℂ] QState (W+k) where
  toFun φ x :=φ (fun j => x (Fin.natAdd W j),fun j => x (j.castAdd k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def separateMap (W k : ℕ) : QState (W+k) →ₗ[ℂ] (Bits k×Bits W → ℂ) where
  toFun φ pair :=φ (Fin.append pair.2 pair.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem separate_assemble (W k : ℕ) (φ : Bits k×Bits W → ℂ) :
    separateMap W k (assembleMap W k φ)=φ := by
  funext pair
  simp only [separateMap,assembleMap,LinearMap.coe_mk,AddHom.coe_mk,Fin.append_left,Fin.append_right]

@[simp] theorem assemble_separate (W k : ℕ) (φ : QState (W+k)) :
    assembleMap W k (separateMap W k φ)=φ := by
  funext x
  change φ (Fin.append (fun j => x (j.castAdd k)) (fun j => x (Fin.natAdd W j)))=φ x
  exact congrArg φ ((qubitsAppendEquiv W k).symm_apply_apply x)

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

variable {I : Type*} [Fintype I]

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule77

/- Helper module Solutions.RegevBridgeNativeWordLift. -/
section P2MDyadicModule78

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open scoped BigOperators

theorem append_update {W k : ℕ} (work : Bits W) (data : Bits k) (i : Fin W) (b : Bool) :
    Function.update (Fin.append work data) (i.castAdd k) b=Fin.append (Function.update work i b) data := by
  funext x
  refine Fin.addCases ?_ ?_ x
  · intro j
    by_cases h : j=i
    · subst j;simp
    · have hn : j.castAdd k≠i.castAdd k := by intro he;exact h (Fin.castAdd_inj.mp he)
      simp only [Function.update_of_ne hn,Fin.append_left,Function.update_of_ne h]
  · intro j
    have hn : Fin.natAdd W j≠i.castAdd k := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
    simp only [Function.update_of_ne hn,Fin.append_right]

theorem separate_instr {W k : ℕ} (gate : Instr W) (ψ : QState (W+k)) :
    separateMap W k ((extendInstr k gate).apply ψ)=
      fun pair => gate.apply (fun work => separateMap W k ψ (pair.1,work)) pair.2 := by
  funext pair
  cases gate <;>
    simp [extendInstr,Instr.apply,apply1,cnotState,append_update,separateMap]

theorem separate_layer {W k : ℕ} (gates : List (Instr W)) (ψ : QState (W+k)) :
    separateMap W k (runLayer (gates.map (extendInstr k)) ψ)=
      fun pair => runLayer gates (fun work => separateMap W k ψ (pair.1,work)) pair.2 := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons gate rest ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons] at *
    rw [ih]
    funext pair
    have he : (fun work => separateMap W k ((extendInstr k gate).apply ψ) (pair.1,work))=
        gate.apply (fun work => separateMap W k ψ (pair.1,work)) := by
      funext work
      exact congrFun (separate_instr gate ψ) (pair.1,work)
    rw [he]

theorem separate_circuit {W k : ℕ} (gates : Layered W) (ψ : QState (W+k)) :
    separateMap W k (runLayered (extendCircuit k gates) ψ)=
      fun pair => runLayered gates (fun work => separateMap W k ψ (pair.1,work)) pair.2 := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons layer rest ih =>
    simp only [extendCircuit,List.map_cons,runLayered,List.foldl_cons] at *
    rw [ih]
    funext pair
    have he : (fun work => separateMap W k (runLayer (layer.map (extendInstr k)) ψ) (pair.1,work))=
        runLayer layer (fun work => separateMap W k ψ (pair.1,work)) := by
      funext work
      exact congrFun (separate_layer layer ψ) (pair.1,work)
    rw [he]

def workAction {W : ℕ} (gates : Layered W) (k : ℕ) : QState (W+k) →ₗ[ℂ] QState (W+k) :=
  (assembleMap W k).comp ((CoherentComputeUncompute.onWork (runLayeredLinearMap gates)).comp (separateMap W k))

/-- This tensor action is exactly the literal extended original circuit. -/
theorem extendCircuit_semantics {W : ℕ} (gates : Layered W) (k : ℕ) (ψ : QState (W+k)) :
    runLayered (extendCircuit k gates) ψ=workAction gates k ψ := by
  have hh : separateMap W k (runLayered (extendCircuit k gates) ψ)=
      CoherentComputeUncompute.onWork (runLayeredLinearMap gates) (separateMap W k ψ) := by
    simpa only [CoherentComputeUncompute.onWork,LinearMap.coe_mk,AddHom.coe_mk,runLayeredLinearMap_apply] using
      separate_circuit gates ψ
  have he:=congrArg (assembleMap W k) hh
  rw [assemble_separate] at he
  exact he

@[simp] theorem encInstr_extend (k : ℕ) {W : ℕ} (gate : Instr W) :
    encInstr (extendInstr k gate)=encInstr gate := by cases gate <;> rfl

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule78

/- Helper module Solutions.RegevBridgeNativeWordSerializer. -/
section P2MDyadicModule79

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordDescription

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open NativeWordLayout NativeWordCoherent ControlledNativeGates ControlledNativeCode

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator RPN

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

/-- A bounded total emitter, so invalid binary addresses cannot cause an
exponential unary output. The correctness theorem uses only valid gate codes. -/
def gateWord (ticks : List Unit) (gate : GateCode) : Str :=
  boundedNat (List.replicate 4 ()) gate.1++boundedNat ticks gate.2.1++
    if gate.1=4 then boundedNat ticks gate.2.2 else []

@[fun_prop] theorem gateWord_poly : Poly (fun x : List Unit×GateCode => gateWord x.1 x.2) := by
  unfold gateWord
  fun_prop

theorem gateWord_encode {m : ℕ} (ticks : List Unit) (gate : Instr m) (h : m≤ ticks.length) :
    gateWord ticks (encodeInstr gate)=encInstr gate := by
  cases gate with
  | h i =>
    have hi:=i.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq (List.replicate 4 ()) 0 (by decide)]
    simp
  | s i =>
    have hi:=i.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq (List.replicate 4 ()) 1 (by decide)]
    simp
  | t i =>
    have hi:=i.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq (List.replicate 4 ()) 2 (by decide)]
    simp
  | x i =>
    have hi:=i.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq (List.replicate 4 ()) 3 (by decide)]
    simp
  | cnot i j hij =>
    have hi:=i.isLt.le.trans h
    have hj:=j.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq ticks j.val hj]
    rfl

variable {f : Str → Str} (program : PolyProgram id id f)

def forwardWords (word : Str) : List (List Str) :=
  (readCircuitLayers (readUnary (readUnary (quantumDescription program word)).2).2).2

@[fun_prop] theorem forwardWords_poly : Poly (forwardWords program) := by
  have hfirst : Poly (fun word => readUnary (quantumDescription program word)) :=
    Poly.comp readUnary_poly (quantumDescription_poly program)
  have hsecond : Poly (fun word => readUnary (readUnary (quantumDescription program word)).2) :=
    Poly.comp readUnary_poly (Poly.comp Poly.snd hfirst)
  unfold forwardWords
  exact Poly.comp Poly.snd (Poly.comp readCircuitLayers_poly (Poly.comp Poly.snd hsecond))

theorem forwardWords_code (n : ℕ) :
    forwardWords program (unary n)=(circuit program n).map (List.map encInstr) := by
  unfold forwardWords
  rw [quantumDescription_code]
  simp only [encFamilyAt,List.append_assoc,readUnary_append]
  have hh:=congrArg Prod.snd (readCircuitLayers_append ((family program).circ n) [])
  simpa only [List.append_nil,family_circuit] using hh

theorem extendCircuit_code {W : ℕ} (k : ℕ) (circ : Layered W) :
    (extendCircuit k circ).map (List.map encInstr)=circ.map (List.map encInstr) := by
  simp only [extendCircuit,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  simp only [List.map_map,encInstr_extend]

def totalSlots (word : Str) : List Unit := multiTotalSlots program word++List.replicate 5 ()

@[fun_prop] theorem totalSlots_poly : Poly (totalSlots program) := by unfold totalSlots;fun_prop

theorem totalSlots_bound (n : ℕ) : width program n+5≤(totalSlots program (unary n)).length := by
  have hh:=ancilla_bound program n
  simp only [totalSlots,multiTotalSlots,List.length_append,List.length_map,List.length_replicate,
    List.length_singleton,unary]
  unfold width
  omega

def precision (q : Polynomial ℕ) (word : Str) : List Unit := List.replicate (q.eval word.length) ()

@[fun_prop] theorem precision_poly (q : Polynomial ℕ) : Poly (precision q) := by
  unfold precision
  have hh:=Poly.comp (f:=fun xs : List Unit => List.replicate (q.eval xs.length) ())
    (g:=fun word : Str => word.map (fun _ => ())) (polynomialSlots_poly q) (by fun_prop)
  simpa only [List.length_map] using hh

@[simp] theorem precision_unary (q : Polynomial ℕ) (n : ℕ) :
    precision q (unary n)=List.replicate (q.eval n) () := by simp only [precision,unary,List.length_replicate]

variable (words : Str → List ℕ) (hw : Poly words) (p q : Polynomial ℕ)

def nativeWords (a : ℕ) (word : Str) : List Str :=
  (NativeWordLayout.current (P words hw p) p a (word,precision q word)).map
    (gateWord (totalSlots (P words hw p) word))

@[fun_prop] theorem nativeWords_poly (a : ℕ) : Poly (nativeWords words hw p q a) := by
  unfold nativeWords
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (NativeWordLayout.current_poly (P words hw p) p a) (by fun_prop)

theorem nativeWords_code (n a : ℕ) :
    nativeWords words hw p q a (unary n)=
      (nativeMiddle words hw p n a (List.replicate (q.eval n) ())).map encInstr := by
  unfold nativeWords
  rw [precision_unary,current_codes (P words hw p) p (rawSlotsFit words hw p) n a]
  unfold nativeMiddle
  rw [current_decode (P words hw p) p (rawSlotsFit words hw p) n a]
  simp only [List.map_map]
  apply List.map_congr_left
  intro gate _
  exact gateWord_encode _ gate (totalSlots_bound (P words hw p) n)

end InfoLossLAR.WorstCase.NativeWordDescription

end

end P2MDyadicModule79

/- Helper module Solutions.RegevBridgeCircuitRelocationNative. -/
section P2MDyadicModule80

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity ControlledNativeCode NativeWordDescription

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

/-- Lookup uses binary addresses in a supplied finite public wire table. -/
def wireAddress (layout : List ℕ) (i : ℕ) : ℕ := layout[i]?.getD 0

@[fun_prop] theorem wireAddress_poly : Poly (fun x : List ℕ×ℕ => wireAddress x.1 x.2) :=
  Poly.list_getD_comp 0 Poly.fst Poly.snd

def relocatedCode (layout : List ℕ) (gate : GateCode) : GateCode :=
  (gate.1,wireAddress layout gate.2.1,if gate.1=4 then wireAddress layout gate.2.2 else 0)

@[fun_prop] theorem relocatedCode_poly : Poly (fun x : List ℕ×GateCode => relocatedCode x.1 x.2) := by
  unfold relocatedCode
  fun_prop

theorem wireAddress_exact {k n : ℕ} (w : Fin k ↪ Fin n) (i : Fin k) :
    wireAddress (List.ofFn (fun i => (w i).val)) i.val=(w i).val := by
  simp [wireAddress]

theorem relocatedCode_exact {k n : ℕ} (w : Fin k ↪ Fin n) (g : Instr k) :
    relocatedCode (List.ofFn (fun i => (w i).val)) (encodeInstr g)=
      encodeInstr (relocateInstr w g) := by
  cases g <;> simp only [relocatedCode,encodeInstr,relocateInstr,wireAddress_exact] <;> rfl

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule80

/- Helper module Solutions.RegevBridgeCircuitRelocationWords. -/
section P2MDyadicModule81

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity ControlledNativeCode NativeWordDescription

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

open QMCNumericRuntime

/-- Bounded parsing of the actual five-constructor unary instruction code. -/
def readGateCode (word : Str) : GateCode :=
  (inputWidth word,inputWidth (readUnary word).2,
    if inputWidth word=4 then inputWidth (readUnary (readUnary word).2).2 else 0)

@[fun_prop] theorem readGateCode_poly : Poly readGateCode := by
  have hr : Poly (fun word : Str => (readUnary word).2) := Poly.comp Poly.snd readUnary_poly
  have hrr : Poly (fun word : Str => (readUnary (readUnary word).2).2) :=
    Poly.comp (f:=fun word : Str => (readUnary word).2) (g:=fun word : Str => (readUnary word).2) hr hr
  unfold readGateCode
  fun_prop

private theorem codeWidth_append (n : ℕ) (tail : Str) : inputWidth (encNat n++tail)=n := by
  simpa only [encNat,List.append_assoc,List.singleton_append] using inputWidth_prefix n tail

private theorem codeWidth (n : ℕ) : inputWidth (encNat n)=n := by
  simpa only [List.append_nil] using codeWidth_append n []

theorem readGateCode_exact {n : ℕ} (gate : Instr n) : readGateCode (encInstr gate)=encodeInstr gate := by
  cases gate <;> simp [readGateCode,encInstr,encodeInstr,List.append_assoc,readUnary_append,codeWidth_append,codeWidth]

abbrev RelocationWordRequest := List Unit×(List ℕ×List (List Str))

def relocatedWordLayers (x : RelocationWordRequest) : List (List Str) :=
  x.2.2.map (fun layer => layer.map (fun word => gateWord x.1 (relocatedCode x.2.1 (readGateCode word))))

@[fun_prop] theorem relocatedWordLayers_poly : Poly relocatedWordLayers := by
  unfold relocatedWordLayers
  fun_prop

/-- Each source instruction decodes exactly and is emitted at its true
physical location. No invalid-code filtering can lose a gate. -/
theorem relocatedWordLayers_exact {k n : ℕ} (w : Fin k↪Fin n) (C : Layered k)
    (ticks : List Unit) (ht : n≤ticks.length) :
    relocatedWordLayers (ticks,(List.ofFn (fun i => (w i).val),C.map (List.map encInstr)))=
      (relocateCircuit w C).map (List.map encInstr) := by
  simp only [relocatedWordLayers,relocateCircuit,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  rw [readGateCode_exact,relocatedCode_exact,gateWord_encode ticks _ ht]

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule81

/- Helper module Solutions.RegevBridgeCoherentInjectionLayout. -/
section P2MDyadicModule82

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms.Complexity FiniteGateTransport

/-- Physical order: padded original input, forward output, forward machine
workspace, inverse machine workspace. Both machine workspaces are retained. -/
def width (x y a b : ℕ) := x+y+a+b

def forwardWires (n x y a b : ℕ) (hn : n ≤ x) : Fin (n+a+y) ↪ Fin (width x y a b) where
  toFun i :=
    if h : i.val<n then ⟨i.val,by unfold width;omega⟩
    else if h' : i.val<n+a then ⟨x+y+(i.val-n),by unfold width;omega⟩
    else ⟨x+(i.val-(n+a)),by unfold width;omega⟩
  inj' := by
    intro i j he
    have hv := congrArg Fin.val he
    simp only at hv
    split_ifs at hv <;> simp_all only <;> apply Fin.ext <;> omega

def backwardWires (x y a b : ℕ) : Fin (y+b+x) ↪ Fin (width x y a b) where
  toFun i :=
    if h : i.val<y then ⟨x+i.val,by unfold width;omega⟩
    else if h' : i.val<y+b then ⟨x+y+a+(i.val-y),by unfold width;omega⟩
    else ⟨i.val-(y+b),by unfold width;omega⟩
  inj' := by
    intro i j he
    have hv := congrArg Fin.val he
    simp only at hv
    split_ifs at hv <;> simp_all only <;> apply Fin.ext <;> omega

def dataBits {x y a b : ℕ} (old : Bits x) (fresh : Bits y) : Bits (width x y a b) :=
  fun i => if hx : i.val<x then old ⟨i.val,hx⟩
    else if hy : i.val<x+y then fresh ⟨i.val-x,by omega⟩ else false

theorem forward_input (n x y a b : ℕ) (hn : n ≤ x) (i : Fin n) :
    (forwardWires n x y a b hn) ((i.castAdd a).castAdd y)=⟨i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [forwardWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,dif_pos i.isLt]

theorem forward_work (n x y a b : ℕ) (hn : n ≤ x) (i : Fin a) :
    (forwardWires n x y a b hn) ((i.natAdd n).castAdd y)=⟨x+y+i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [forwardWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]
  rw [dif_neg (by omega),dif_pos (by omega)]
  simp

theorem forward_output (n x y a b : ℕ) (hn : n ≤ x) (i : Fin y) :
    (forwardWires n x y a b hn) (i.natAdd (n+a))=⟨x+i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [forwardWires,Function.Embedding.coeFn_mk,Fin.val_natAdd]
  rw [dif_neg (by omega),dif_neg (by omega)]
  simp

theorem backward_input (x y a b : ℕ) (i : Fin y) :
    (backwardWires x y a b) ((i.castAdd b).castAdd x)=⟨x+i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [backwardWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,dif_pos i.isLt]

theorem backward_work (x y a b : ℕ) (i : Fin b) :
    (backwardWires x y a b) ((i.natAdd y).castAdd x)=⟨x+y+a+i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [backwardWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]
  rw [dif_neg (by omega),dif_pos (by omega)]
  simp

theorem backward_output (x y a b : ℕ) (i : Fin x) :
    (backwardWires x y a b) (i.natAdd (y+b))=⟨i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [backwardWires,Function.Embedding.coeFn_mk,Fin.val_natAdd]
  rw [dif_neg (by omega),dif_neg (by omega)]
  simp

@[simp] theorem dataBits_old {x y a b : ℕ} (old : Bits x) (fresh : Bits y) (i : Fin x) :
    dataBits (a:=a) (b:=b) old fresh ⟨i.val,by unfold width;omega⟩=old i := by
  simp only [dataBits,dif_pos i.isLt]

@[simp] theorem dataBits_fresh {x y a b : ℕ} (old : Bits x) (fresh : Bits y) (i : Fin y) :
    dataBits (a:=a) (b:=b) old fresh ⟨x+i.val,by unfold width;omega⟩=fresh i := by
  simp only [dataBits]
  rw [dif_neg (by omega),dif_pos (by omega)]
  simp

theorem dataBits_work {x y a b : ℕ} (old : Bits x) (fresh : Bits y)
    (i : Fin (width x y a b)) (hi : x+y ≤ i.val) : dataBits old fresh i=false := by
  simp only [dataBits]
  rw [dif_neg (by omega),dif_neg (by omega)]

end InfoLossLAR.WorstCase.CoherentInjection

end P2MDyadicModule82

/- Helper module Solutions.RegevBridgeCoherentInjectionRegisters. -/
section P2MDyadicModule83

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms.Complexity FiniteGateTransport

theorem forward_selected (n x y a b : ℕ) (hn : n ≤ x) (old : Bits x) (fresh : Bits y) :
    (wireBitsEquiv (forwardWires n x y a b hn) (dataBits old fresh)).1=
      Fin.append (Fin.append (fun i : Fin n => old ⟨i.val,by omega⟩) (fun _ => false)) fresh := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [Fin.append_left]
      change dataBits old fresh (forwardWires n x y a b hn ((k.castAdd a).castAdd y))=_
      rw [forward_input]
      simp only [dataBits,dif_pos (by omega : k.val<x)]
    · intro k
      simp only [Fin.append_left,Fin.append_right]
      change dataBits old fresh (forwardWires n x y a b hn ((k.natAdd n).castAdd y))=_
      rw [forward_work]
      exact dataBits_work old fresh _ (by dsimp;omega)
  · intro k
    simp only [Fin.append_right]
    change dataBits old fresh (forwardWires n x y a b hn (k.natAdd (n+a)))=_
    rw [forward_output,dataBits_fresh]

theorem backward_selected (x y a b : ℕ) (old : Bits x) (fresh : Bits y) :
    (wireBitsEquiv (backwardWires x y a b) (dataBits old fresh)).1=
      Fin.append (Fin.append fresh (fun _ => false)) old := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [Fin.append_left]
      change dataBits old fresh (backwardWires x y a b ((k.castAdd b).castAdd x))=_
      rw [backward_input,dataBits_fresh]
    · intro k
      simp only [Fin.append_left,Fin.append_right]
      change dataBits old fresh (backwardWires x y a b ((k.natAdd y).castAdd x))=_
      rw [backward_work]
      exact dataBits_work old fresh _ (by dsimp;omega)
  · intro k
    simp only [Fin.append_right]
    change dataBits old fresh (backwardWires x y a b (k.natAdd (y+b)))=_
    rw [backward_output,dataBits_old]

theorem forward_outside (n x y a b : ℕ) (hn : n ≤ x)
    (old : Bits x) (fresh fresh' : Bits y) :
    (wireBitsEquiv (forwardWires n x y a b hn) (dataBits old fresh)).2=
      (wireBitsEquiv (forwardWires n x y a b hn) (dataBits old fresh')).2 := by
  funext i
  have hy : ¬(x ≤ i.val.val ∧ i.val.val<x+y) := by
    rintro ⟨hlo,hhi⟩
    have hk : i.val.val-x<y := by omega
    apply i.property
    refine ⟨(⟨i.val.val-x,hk⟩ : Fin y).natAdd (n+a),?_⟩
    rw [forward_output]
    apply Fin.ext
    simp only
    omega
  change dataBits old fresh i.val=dataBits old fresh' i.val
  simp only [dataBits]
  split_ifs <;> first | rfl | omega

theorem backward_outside (x y a b : ℕ) (old old' : Bits x) (fresh : Bits y) :
    (wireBitsEquiv (backwardWires x y a b) (dataBits old fresh)).2=
      (wireBitsEquiv (backwardWires x y a b) (dataBits old' fresh)).2 := by
  funext i
  have hx : ¬i.val.val<x := by
    intro h
    apply i.property
    refine ⟨(⟨i.val.val,h⟩ : Fin x).natAdd (y+b),?_⟩
    rw [backward_output]
  change dataBits old fresh i.val=dataBits old' fresh i.val
  simp only [dataBits,dif_neg hx]

end InfoLossLAR.WorstCase.CoherentInjection

end P2MDyadicModule83

/- Helper module Solutions.RegevBridgeCoherentBasisEmbedding. -/
section P2MDyadicModule84

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open scoped BigOperators

variable {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W]

theorem basisEmbedding_at (e : I ↪ W) (ψ : I → ℂ) (i : I) :
    basisEmbedding e ψ (e i)=ψ i := by
  classical
  simp [basisEmbedding,basis,e.injective.eq_iff]

theorem basisEmbedding_outside (e : I ↪ W) (ψ : I → ℂ) (w : W)
    (h : w∉Set.range e) : basisEmbedding e ψ w=0 := by
  have he (i : I) : w≠e i := fun hh => h ⟨i,hh.symm⟩
  simp [basisEmbedding,basis,he]

theorem basisEmbedding_mass (e : I ↪ W) (ψ : I → ℂ) :
    (∑ w,‖basisEmbedding e ψ w‖^2)=∑ i,‖ψ i‖^2 := by
  classical
  calc
    _ = ∑ w∈Finset.univ.image e,‖basisEmbedding e ψ w‖^2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      have hn : w∉Set.range e := by
        rintro ⟨i,rfl⟩
        exact hw (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      simp [basisEmbedding_outside e ψ w hn]
    _ = ∑ i,‖basisEmbedding e ψ (e i)‖^2 :=
      Finset.sum_image (fun _ _ _ _ he => e.injective he)
    _ = _ := by simp only [basisEmbedding_at]

theorem basisEmbedding_norm (e : I ↪ W) (ψ : I → ℂ) :
    ‖(WithLp.toLp 2 (basisEmbedding e ψ) : EuclideanSpace ℂ W)‖=
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ I)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,basisEmbedding_mass]

theorem basisEmbedding_error (e : I ↪ W) (ψ φ : I → ℂ) :
    ‖(WithLp.toLp 2 (basisEmbedding e ψ-basisEmbedding e φ) : EuclideanSpace ℂ W)‖=
      ‖(WithLp.toLp 2 (ψ-φ) : EuclideanSpace ℂ I)‖ := by
  rw [←map_sub,basisEmbedding_norm]

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end P2MDyadicModule84

/- Helper module Solutions.RegevBridgeCoherentXorCopy. -/
section P2MDyadicModule85

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentXorCopy

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent

open scoped BigOperators

variable {W k : ℕ}

theorem gate_append (controls : Fin k → Fin W) (i : Fin k) (work : Bits W) (data : Bits k) :
    (gate controls i).act (Fin.append work data)=
      Fin.append work (Function.update data i (xor (data i) (work (controls i)))) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro l
    have hn : l.castAdd k≠Fin.natAdd W i := by
      intro h;have hv:=congrArg Fin.val h;dsimp at hv;have hl:=l.isLt;omega
    simp [gate,ReversibleGate.act,Function.update_of_ne hn]
  · intro l
    by_cases h : l=i
    · subst l;simp [gate,ReversibleGate.act]
    · have hn : Fin.natAdd W l≠Fin.natAdd W i := by
        intro he;exact h (Fin.ext (Nat.add_left_cancel (congrArg Fin.val he)))
      simp [gate,ReversibleGate.act,Function.update_of_ne hn,Function.update_of_ne h]

def xorData (controls : Fin k → Fin W) (work : Bits W) (data : Bits k) : Bits k :=
  fun j => xor (data j) (work (controls j))

theorem action_slots (controls : Fin k → Fin W) (slots : List (Fin k)) (hn : slots.Nodup)
    (work : Bits W) (data : Bits k) :
    reversibleAction (slots.map (gate controls)) (Fin.append work data)=
      Fin.append work (fun j => xor (data j) (if j∈slots then work (controls j) else false)) := by
  induction slots generalizing data with
  | nil => simp [reversibleAction]
  | cons i slots ih =>
    change reversibleAction (slots.map (gate controls)) ((gate controls i).act (Fin.append work data))=_
    rw [gate_append,ih (List.nodup_cons.mp hn).2]
    congr 1
    funext j
    by_cases h : j=i
    · subst j
      simp only [Function.update_self,List.mem_cons_self,if_true,
        if_neg (List.nodup_cons.mp hn).1,Bool.xor_false]
    · simp only [Function.update_of_ne h,List.mem_cons,h,false_or]

theorem action_all (controls : Fin k → Fin W) (work : Bits W) (data : Bits k) :
    reversibleAction ((List.finRange k).map (gate controls)) (Fin.append work data)=
      Fin.append work (xorData controls work data) := by
  rw [action_slots controls _ (List.nodup_finRange k)]
  simp only [List.mem_finRange,if_true]
  rfl

theorem compile_basis {n : ℕ} (gates : List (ReversibleGate n)) (x : Bits n) :
    runLayered (compileReversible gates) (basis x)=basis (reversibleAction gates x) := by
  rw [compileReversible_apply]
  funext y
  simp only [basis,Equiv.symm_apply_eq]

theorem circuit_basis (controls : Fin k → Fin W) (work : Bits W) (data : Bits k) :
    runLayered (circuit controls) (basis (Fin.append work data))=
      basis (Fin.append work (xorData controls work data)) := by
  rw [circuit,compile_basis,action_all]

theorem append_eq_iff (a c : Bits W) (b d : Bits k) :
    Fin.append a b=Fin.append c d ↔ a=c ∧ b=d := by
  change (qubitsAppendEquiv W k).symm (a,b)=(qubitsAppendEquiv W k).symm (c,d) ↔ _
  rw [(qubitsAppendEquiv W k).symm.injective.eq_iff,Prod.mk.injEq]

/-- The full finite circuit has the same XOR action on arbitrary coherent
data amplitudes while its computed work basis remains unchanged. -/
theorem circuit_tensor (controls : Fin k → Fin W) (work : Bits W) (v : QState k) :
    runLayered (circuit controls) (assembleMap W k (tensor v work))=
      assembleMap W k (tensor (fun data => v (xorData controls work data)) work) := by
  have hs : assembleMap W k (tensor v work)=∑ data : Bits k,v data • basis (Fin.append work data) := by
    funext x
    simp only [assembleMap,LinearMap.coe_mk,AddHom.coe_mk,tensor,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    have hx : x=Fin.append (fun i => x (i.castAdd k)) (fun i => x (Fin.natAdd W i)) :=
      ((qubitsAppendEquiv W k).symm_apply_apply x).symm
    rw [hx]
    by_cases hw : (fun i => x (i.castAdd k))=work <;> simp [basis,append_eq_iff,hw]
  rw [hs,←runLayeredLinearMap_apply,map_sum]
  simp only [map_smul,runLayeredLinearMap_apply,circuit_basis]
  have hi : Function.Involutive (xorData controls work) := by intro d;funext j;simp [xorData,Bool.xor_assoc]
  have he := Fintype.sum_equiv (hi.toPerm (xorData controls work))
    (fun d => v d • basis (Fin.append work (xorData controls work d)))
    (fun d => v (xorData controls work d) • basis (Fin.append work d)) (by
      intro d
      change v d • basis (Fin.append work (xorData controls work d))=
        v (xorData controls work (xorData controls work d)) • basis (Fin.append work (xorData controls work d))
      rw [hi])
  rw [he]
  have hs' : assembleMap W k (tensor (fun data => v (xorData controls work data)) work)=
      ∑ data : Bits k,v (xorData controls work data) • basis (Fin.append work data) := by
    funext x
    simp only [assembleMap,LinearMap.coe_mk,AddHom.coe_mk,tensor,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    have hx : x=Fin.append (fun i => x (i.castAdd k)) (fun i => x (Fin.natAdd W i)) :=
      ((qubitsAppendEquiv W k).symm_apply_apply x).symm
    rw [hx]
    by_cases hw : (fun i => x (i.castAdd k))=work <;> simp [basis,append_eq_iff,hw]
  exact hs'.symm

end InfoLossLAR.WorstCase.CoherentXorCopy

end

end P2MDyadicModule85

/- Helper module Solutions.RegevBridgeNativeWordDescription. -/
section P2MDyadicModule86

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordDescription

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open NativeWordLayout NativeWordCoherent ControlledNativeGates ControlledNativeCode

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator RPN

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

variable (words : Str → List ℕ) (hw : Poly words) (p q : Polynomial ℕ)

attribute [local irreducible] NativeWordControls.rawCurrentProgram forwardWords nativeWords inverseCircuitWords

def layerWords (a : ℕ) (word : Str) : List (List Str) :=
  forwardWords (P words hw p) word++
    (nativeWords words hw p q a word).map (fun gate => [gate])++
    inverseCircuitWords (forwardWords (P words hw p) word)

theorem layerWords_poly (a : ℕ) : Poly (layerWords words hw p q a) := by
  unfold layerWords
  have hf :=forwardWords_poly (P words hw p)
  have hm : Poly (fun word => (nativeWords words hw p q a word).map (fun gate => [gate])) := by
    apply Poly.list_map
    · fun_prop
    · exact nativeWords_poly words hw p q a
  have hi :=Poly.comp inverseCircuitWords_poly hf
  exact Poly.comp Poly.list_append (Poly.pair (Poly.comp Poly.list_append (Poly.pair hf hm)) hi)

theorem layerWords_code (n a : ℕ) :
    layerWords words hw p q a (unary n)=
      (wholeCircuit words hw p n a (List.replicate (q.eval n) ())).map (List.map encInstr) := by
  unfold layerWords wholeCircuit
  rw [forwardWords_code,nativeWords_code,inverseCircuitWords_correct]
  simp only [List.map_append,extendCircuit_code,baseCircuit,List.map_map,
    Function.comp_def,List.map_cons,List.map_nil]

end InfoLossLAR.WorstCase.NativeWordDescription

end

end P2MDyadicModule86

/- Helper module Solutions.RegevBridgeCoherentClassicalOracle. -/
section P2MDyadicModule87

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f : Str → Str} (P : PolyProgram id id f)

def initialWork (n : ℕ) (word : Str) : Bits (width P n) := fun i => wordExtension word i.val

def computedWork (word : Str) : Bits (width P word.length) := result P word

def controls (n : ℕ) (i : Fin (capacity P n)) : Fin (width P n) := outputWire P n i (some true)

def base (n : ℕ) : Layered (width P n) := PolyProgramCircuit.circuit P n

def fullCircuit (n : ℕ) : Layered (width P n+capacity P n) :=
  extendCircuit (capacity P n) (base P n)++CoherentXorCopy.circuit (controls P n)++
    extendCircuit (capacity P n) (inverseCircuit (base P n))

def inputState (word : Str) (v : QState (capacity P word.length)) : QState (width P word.length+capacity P word.length) :=
  assembleMap _ _ (tensor v (initialWork P word.length word))

def maskedData (word : Str) (data : Bits (capacity P word.length)) : Bits (capacity P word.length) :=
  fun i => xor (data i) (wordExtension (f word) i.val)

def cleanState (word : Str) (v : QState (capacity P word.length)) : QState (width P word.length+capacity P word.length) :=
  inputState P word (fun data => v (maskedData P word data))

theorem base_computes (word : Str) :
    runLayeredLinearMap (base P word.length) (basis (initialWork P word.length word))=basis (computedWork P word) := by
  have h := PolyProgramCircuit.circuit_basis P word
  rw [basisInput_eq_computationalBasis,wordExtension_basis] at h
  rw [runLayeredLinearMap_apply]
  exact h

theorem inverse_computed (word : Str) :
    runLayeredLinearMap (inverseCircuit (base P word.length)) (basis (computedWork P word))=
      basis (initialWork P word.length word) :=
  CoherentComputeUncompute.inverse_basis _ _ _ (base_computes P word)

theorem control_value (word : Str) (i : Fin (capacity P word.length)) :
    computedWork P word (controls P word.length i)=wordExtension (f word) i.val := by
  change result P word (outputWire P word.length i (some true))=wordExtension (f word) i.val
  rw [output_correct]
  unfold wordExtension
  cases h : (f word)[i.val]? with
  | none => simp [h]
  | some bit => cases bit <;> simp [h]

theorem xorData_result (word : Str) (data : Bits (capacity P word.length)) :
    CoherentXorCopy.xorData (controls P word.length) (computedWork P word) data=maskedData P word data := by
  funext i
  simp only [CoherentXorCopy.xorData,control_value,maskedData]

/- The actual compute/output-XOR/inverse circuit evaluates the native
polynomial-time function without leaving any of its machine workspace.
Its original input remains, and the target register may be in any coherent state. -/
section
attribute [local irreducible] initialWork computedWork controls base maskedData width capacity
theorem fullCircuit_exact (word : Str) (v : QState (capacity P word.length)) :
    runLayered (fullCircuit P word.length) (inputState P word v)=cleanState P word v := by
  have hf : runLayered (extendCircuit (capacity P word.length) (base P word.length)) (inputState P word v)=
      assembleMap _ _ (tensor v (computedWork P word)) := by
    rw [extendCircuit_semantics]
    simp only [workAction,inputState,LinearMap.comp_apply,separate_assemble]
    exact congrArg (fun φ => assembleMap (width P word.length) (capacity P word.length) φ)
      (CoherentComputeUncompute.onWork_tensor (runLayeredLinearMap (base P word.length)) v
        (initialWork P word.length word) (computedWork P word) (base_computes P word))
  have hm : runLayered (CoherentXorCopy.circuit (controls P word.length))
      (assembleMap _ _ (tensor v (computedWork P word)))=
      assembleMap _ _ (tensor (fun data => v (maskedData P word data)) (computedWork P word)) := by
    rw [CoherentXorCopy.circuit_tensor]
    simp only [xorData_result]
  have hb : runLayered (extendCircuit (capacity P word.length) (inverseCircuit (base P word.length)))
      (assembleMap _ _ (tensor (fun data => v (maskedData P word data)) (computedWork P word)))=
      cleanState P word v := by
    rw [extendCircuit_semantics]
    simp only [workAction,cleanState,inputState,LinearMap.comp_apply,separate_assemble]
    exact congrArg (fun φ => assembleMap (width P word.length) (capacity P word.length) φ)
      (CoherentComputeUncompute.onWork_tensor (runLayeredLinearMap (inverseCircuit (base P word.length)))
        (fun data => v (maskedData P word data)) (computedWork P word) (initialWork P word.length word)
        (inverse_computed P word))
  have he : runLayered (fullCircuit P word.length) (inputState P word v)=
      runLayered (extendCircuit (capacity P word.length) (inverseCircuit (base P word.length)))
        (runLayered (CoherentXorCopy.circuit (controls P word.length))
          (runLayered (extendCircuit (capacity P word.length) (base P word.length)) (inputState P word v))) := by
    simp only [fullCircuit,runLayered,List.foldl_append]
  rw [he,hf,hm,hb]

end


end InfoLossLAR.WorstCase.CoherentClassicalOracle

end

end P2MDyadicModule87

/- Helper module Solutions.RegevBridgeCoherentClassicalOracleNative. -/
section P2MDyadicModule88

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle

open QAlgorithms.Complexity NativeWordLayout NativeWordDescription ControlledNativeCode

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

variable {f : Str → Str} (P : PolyProgram id id f)

def copyCodes (word : Str) : List GateCode :=
  (List.range (request P word).2.1.length).map (fun i =>
    (4,generatedProgramOutputAddress P word i,machineWidth P word+i))

@[fun_prop] theorem copyCodes_poly : Poly (copyCodes P) := by
  unfold copyCodes
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (f:=fun xs : List Unit => List.range xs.length)
      (g:=fun word => (request P word).2.1) Poly.list_indices (by fun_prop)

def copySlots (word : Str) : List Unit := multiTotalSlots P word++(request P word).2.1

@[fun_prop] theorem copySlots_poly : Poly (copySlots P) := by unfold copySlots;fun_prop

theorem copySlots_bound (n : ℕ) : width P n+capacity P n ≤ (copySlots P (unary n)).length := by
  have hb := ancilla_bound P n
  have hs : (request P (unary n)).2.1.length=capacity P n := by rw [request_unary];simp
  simp only [copySlots,List.length_append]
  rw [hs]
  simp only [multiTotalSlots,List.length_append,List.length_map,List.length_replicate,
    List.length_singleton,unary]
  unfold width
  omega

theorem copyCodes_exact (n : ℕ) :
    copyCodes P (unary n)=((List.finRange (capacity P n)).map
      (fun i => encodeInstr (.cnot ((controls P n i).castAdd (capacity P n)) (Fin.natAdd (width P n) i)
        (by intro h;have hv:=congrArg Fin.val h;dsimp at hv;have hi:=(controls P n i).isLt;omega)))) := by
  unfold copyCodes
  have hs : (request P (unary n)).2.1.length=capacity P n := by rw [request_unary];simp
  have hr : List.range (capacity P n)=(List.finRange (capacity P n)).map Fin.val := by simp
  rw [hs,hr,List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,encodeInstr,Fin.val_castAdd,Fin.val_natAdd,machineWidth_eq]
  rw [generatedProgramOutputAddress_eq P n i]
  rfl

def copyWords (word : Str) : List (List Str) := (copyCodes P word).map (fun g => [gateWord (copySlots P word) g])

@[fun_prop] theorem copyWords_poly : Poly (copyWords P) := by unfold copyWords;fun_prop

theorem copyWords_exact (n : ℕ) :
    copyWords P (unary n)=(CoherentXorCopy.circuit (controls P n)).map (List.map encInstr) := by
  unfold copyWords
  rw [copyCodes_exact]
  simp only [List.map_map,Function.comp_def,gateWord_encode _ _ (copySlots_bound P n)]
  simp [CoherentXorCopy.circuit,compileReversible,CoherentXorCopy.gate,ReversibleGate.compile,
    List.map_flatMap,List.flatMap_map,Function.comp_def]
  rw [List.map_eq_flatMap]

def publicLayers (word : Str) : List (List Str) :=
  forwardWords P word++copyWords P word++inverseCircuitWords (forwardWords P word)

attribute [local irreducible] forwardWords copyWords inverseCircuitWords

@[fun_prop] theorem publicLayers_poly : Poly (publicLayers P) := by
  unfold publicLayers
  exact Poly.comp Poly.list_append (Poly.pair
    (Poly.comp Poly.list_append (Poly.pair (forwardWords_poly P) (copyWords_poly P)))
    (Poly.comp inverseCircuitWords_poly (forwardWords_poly P)))

theorem publicLayers_exact (n : ℕ) :
    publicLayers P (unary n)=(fullCircuit P n).map (List.map encInstr) := by
  unfold publicLayers fullCircuit
  rw [forwardWords_code,copyWords_exact,inverseCircuitWords_correct]
  simp only [List.map_append,extendCircuit_code,base]

end InfoLossLAR.WorstCase.CoherentClassicalOracle

end

end P2MDyadicModule88

/- Helper module Solutions.RegevBridgeCoherentClassicalOracleBasis. -/
section P2MDyadicModule89

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

variable {f : Str → Str} (P : PolyProgram id id f)

theorem initialWork_append (word : Str) :
    initialWork P word.length word=Fin.append (toBits word) (fun _ => false) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [initialWork,Fin.val_castAdd,Fin.append_left,wordExtension_before _ _ j.isLt]
    rfl
  · intro j
    simp only [initialWork,Fin.val_natAdd,Fin.append_right]
    exact wordExtension_after word _ (by omega)

theorem inputState_basis (word : Str) (data : Bits (capacity P word.length)) :
    inputState P word (basis data)=basis (Fin.append (initialWork P word.length word) data) := by
  rw [show basis (Fin.append (initialWork P word.length word) data)=
      tensorState (basis (initialWork P word.length word)) (basis data) from
        computationalBasis_tensor _ _]
  funext x
  change basis data (rightRegister x)*basis (initialWork P word.length word) (leftRegister x)=_
  exact mul_comm _ _

theorem maskedData_involutive (word : Str) : Function.Involutive (maskedData P word) := by
  intro data
  funext i
  simp [maskedData]

theorem basis_maskedData (word : Str) (data : Bits (capacity P word.length)) :
    (fun x => basis data (maskedData P word x))=basis (maskedData P word data) := by
  funext x
  have he : maskedData P word x=data ↔ x=maskedData P word data := by
    constructor
    · intro h;rw [←h,maskedData_involutive]
    · intro h;rw [h,maskedData_involutive]
  simp only [basis,he]

/-- The whole actual program implements a clean classical XOR oracle on
basis states, preserving its input and returning every machine-work bit to zero. -/
theorem fullCircuit_basis (word : Str) (data : Bits (capacity P word.length)) :
    runLayered (fullCircuit P word.length) (basis (Fin.append (initialWork P word.length word) data))=
      basis (Fin.append (initialWork P word.length word) (maskedData P word data)) := by
  rw [←inputState_basis,fullCircuit_exact,cleanState,basis_maskedData,inputState_basis]

def paddedOutput (word : Str) : Str :=
  List.ofFn (fun i : Fin (capacity P word.length) => wordExtension (f word) i.val)

@[simp] theorem paddedOutput_length (word : Str) : (paddedOutput P word).length=capacity P word.length :=
  List.length_ofFn

/-- Zero target bits produce the literal function output followed by false
padding in the fixed public output capacity. -/
theorem fullCircuit_zero (word : Str) :
    runLayered (fullCircuit P word.length)
      (basis (Fin.append (initialWork P word.length word) (fun _ => false)))=
      basis (Fin.append (initialWork P word.length word)
        (fun i : Fin (capacity P word.length) => wordExtension (f word) i.val)) := by
  rw [fullCircuit_basis]
  apply congrArg (fun mask : Bits (capacity P word.length) => basis (Fin.append (initialWork P word.length word) mask))
  funext i
  simp [maskedData]

end InfoLossLAR.WorstCase.CoherentClassicalOracle

end

end P2MDyadicModule89

/- Helper module Solutions.RegevBridgeCircuitInitializedEmbedding. -/
section P2MDyadicModule90

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity CoherentComputeUncompute

open scoped BigOperators

/-- Put a local quantum state into public wires and initialize exactly the
complementary physical wires. This is an amplitude specification. -/
noncomputable def initializedWires {k n : ℕ} (w : Fin k ↪ Fin n)
    (outside : OutsideBits w) (ψ : QState k) : QState n :=
  unsplitState w (fun p => ψ p.1*basis outside p.2)

/-- The actual relocated whole circuit implements its local action with
all complementary wires present and fixed, with no assumed state-preparation
oracle and no renormalization. -/
theorem relocateCircuit_initialized {k n : ℕ} (w : Fin k ↪ Fin n)
    (outside : OutsideBits w) (circuit : Layered k) (ψ : QState k) :
    runLayered (relocateCircuit w circuit) (initializedWires w outside ψ)=
      initializedWires w outside (runLayered circuit ψ) := by
  have hh : splitState w (runLayered (relocateCircuit w circuit) (initializedWires w outside ψ))=
      splitState w (initializedWires w outside (runLayered circuit ψ)) := by
        rw [relocateCircuit_split]
        simp only [initializedWires,split_unsplit]
        funext p
        have hs : (fun x => ψ x*basis outside p.2)=basis outside p.2 • ψ := by
          funext x;simp only [Pi.smul_apply,smul_eq_mul,mul_comm]
        rw [hs,←runLayeredLinearMap_apply,map_smul,runLayeredLinearMap_apply]
        simp only [Pi.smul_apply,smul_eq_mul,mul_comm]
  funext x
  have he := congrFun hh (wireBitsEquiv w x)
  simpa only [splitState,Equiv.symm_apply_apply] using he

end InfoLossLAR.WorstCase.FiniteGateTransport

end

end P2MDyadicModule90

/- Helper module Solutions.RegevBridgeCircuitRelocationBasis. -/
section P2MDyadicModule91

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity CoherentComputeUncompute

theorem initializedWires_basis {k n : ℕ} (w : Fin k ↪ Fin n)
    (outside : OutsideBits w) (localBits : Bits k) :
    initializedWires w outside (basis localBits)=
      basis ((wireBitsEquiv w).symm (localBits,outside)) := by
  classical
  funext x
  have he : x=(wireBitsEquiv w).symm (localBits,outside) ↔
      (wireBitsEquiv w x).1=localBits ∧ (wireBitsEquiv w x).2=outside := by
    rw [Equiv.eq_symm_apply,Prod.mk.injEq]
  simp only [initializedWires,unsplitState,basis,he]
  split_ifs <;> simp_all

/-- Relocating a literal circuit preserves every physical bit outside its
wire image, even when those bits vary between coherent input branches. -/
theorem relocateCircuit_basis {k n : ℕ} (w : Fin k ↪ Fin n)
    (circuit : Layered k) (input output : Bits n)
    (hlocal : runLayered circuit (basis ((wireBitsEquiv w input).1))=
      basis ((wireBitsEquiv w output).1))
    (houtside : (wireBitsEquiv w input).2=(wireBitsEquiv w output).2) :
    runLayered (relocateCircuit w circuit) (basis input)=basis output := by
  have hi : basis input=initializedWires w (wireBitsEquiv w input).2
      (basis (wireBitsEquiv w input).1) := by
    rw [initializedWires_basis,Prod.mk.eta,Equiv.symm_apply_apply]
  rw [hi,relocateCircuit_initialized,hlocal,houtside,initializedWires_basis,
    Prod.mk.eta,Equiv.symm_apply_apply]

end InfoLossLAR.WorstCase.FiniteGateTransport

end

end P2MDyadicModule91

/- Helper module Solutions.RegevBridgeCoherentInjectionOracle. -/
section P2MDyadicModule92

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g)

abbrev outputSize (n : ℕ) := capacity P n

abbrev originalSize (n : ℕ) := capacity Q (outputSize P n)

abbrev forwardWork (n : ℕ) := (compiled P n).ops.length+1

abbrev backwardWork (n : ℕ) := (compiled Q (outputSize P n)).ops.length+1

theorem originalSize_ge (n : ℕ) : n ≤ originalSize P Q n := by
  simp only [originalSize,outputSize,capacity]
  omega

abbrev totalWidth (n : ℕ) := width (originalSize P Q n) (outputSize P n) (forwardWork P n) (backwardWork P Q n)

def firstWires (n : ℕ) : Fin (NativeWordLayout.width P n+capacity P n) ↪ Fin (totalWidth P Q n) :=
  forwardWires n (originalSize P Q n) (outputSize P n) (forwardWork P n) (backwardWork P Q n)
    (originalSize_ge P Q n)

def secondWires (n : ℕ) : Fin (NativeWordLayout.width Q (outputSize P n)+capacity Q (outputSize P n)) ↪ Fin (totalWidth P Q n) :=
  backwardWires (originalSize P Q n) (outputSize P n) (forwardWork P n) (backwardWork P Q n)

def firstCircuit (n : ℕ) : Layered (totalWidth P Q n) :=
  relocateCircuit (firstWires P Q n) (CoherentClassicalOracle.fullCircuit P n)

def secondCircuit (n : ℕ) : Layered (totalWidth P Q n) :=
  relocateCircuit (secondWires P Q n) (CoherentClassicalOracle.fullCircuit Q (outputSize P n))

def circuit (n : ℕ) : Layered (totalWidth P Q n) := firstCircuit P Q n++secondCircuit P Q n

def originalBits (word : Str) : Bits (originalSize P Q word.length) := fun i => wordExtension word i.val

def outputBits (word : Str) : Bits (outputSize P word.length) := fun i => wordExtension (f word) i.val

def inputBits (word : Str) : Bits (totalWidth P Q word.length) :=
  dataBits (originalBits P Q word) (fun _ => false)

def middleBits (word : Str) : Bits (totalWidth P Q word.length) :=
  dataBits (originalBits P Q word) (outputBits P word)

def finalBits (word : Str) : Bits (totalWidth P Q word.length) :=
  dataBits (fun _ => false) (outputBits P word)

theorem forward_selected_word (word : Str) (fresh : Bits (outputSize P word.length)) :
    (wireBitsEquiv (firstWires P Q word.length) (dataBits (originalBits P Q word) fresh)).1=
      Fin.append (CoherentClassicalOracle.initialWork P word.length word) fresh := by
  calc
    _ = Fin.append (Fin.append (fun i : Fin word.length => wordExtension word i.val) (fun _ => false)) fresh :=
      forward_selected _ _ _ _ _ _ _ _
    _ = _ := by
      rw [CoherentClassicalOracle.initialWork_append]
      congr 2
      funext i
      exact wordExtension_before word i.val i.isLt

theorem firstCircuit_basis (word : Str) :
    runLayered (firstCircuit P Q word.length) (basis (inputBits P Q word))=basis (middleBits P Q word) := by
  apply relocateCircuit_basis
  · change runLayered (CoherentClassicalOracle.fullCircuit P word.length)
      (basis ((wireBitsEquiv (firstWires P Q word.length) (dataBits (originalBits P Q word) (fun _ => false))).1))=
        basis ((wireBitsEquiv (firstWires P Q word.length) (dataBits (originalBits P Q word) (outputBits P word))).1)
    rw [forward_selected_word,forward_selected_word]
    exact CoherentClassicalOracle.fullCircuit_zero P word
  · exact forward_outside _ _ _ _ _ _ _ _ _

theorem paddedOutput_bits (word : Str) :
    (fun i : Fin (outputSize P word.length) =>
      wordExtension (CoherentClassicalOracle.paddedOutput P word) i.val)=outputBits P word := by
  funext i
  have hi : i.val<(CoherentClassicalOracle.paddedOutput P word).length := by
    simpa only [CoherentClassicalOracle.paddedOutput_length,outputSize] using i.isLt
  rw [wordExtension_before _ _ hi]
  change (List.ofFn (fun j : Fin (capacity P word.length) => wordExtension (f word) j.val))[i.val]=_
  rw [List.getElem_ofFn]
  rfl

theorem initialWork_at (word : Str) (n : ℕ) (hn : word.length=n) :
    CoherentClassicalOracle.initialWork P n word=
      Fin.append (fun i : Fin n => wordExtension word i.val) (fun _ => false) := by
  subst n
  rw [CoherentClassicalOracle.initialWork_append]
  congr 1
  funext i
  exact (wordExtension_before word i.val i.isLt).symm

theorem fullCircuit_basis_at (word : Str) (n : ℕ) (hn : word.length=n)
    (data : Bits (capacity P n)) :
    runLayered (CoherentClassicalOracle.fullCircuit P n)
        (basis (Fin.append (CoherentClassicalOracle.initialWork P n word) data))=
      basis (Fin.append (CoherentClassicalOracle.initialWork P n word)
        (fun i => xor (data i) (wordExtension (f word) i.val))) := by
  subst n
  exact CoherentClassicalOracle.fullCircuit_basis P word data

theorem backward_selected_word (word : Str) (old : Bits (originalSize P Q word.length)) :
    (wireBitsEquiv (secondWires P Q word.length) (dataBits old (outputBits P word))).1=
      Fin.append (CoherentClassicalOracle.initialWork Q (outputSize P word.length)
        (CoherentClassicalOracle.paddedOutput P word)) old := by
  have hlen : (CoherentClassicalOracle.paddedOutput P word).length=outputSize P word.length :=
    CoherentClassicalOracle.paddedOutput_length P word
  have hw : CoherentClassicalOracle.initialWork Q (outputSize P word.length)
      (CoherentClassicalOracle.paddedOutput P word)=Fin.append (outputBits P word) (fun _ => false) := by
    rw [initialWork_at Q _ _ hlen,paddedOutput_bits]
  calc
    _ = Fin.append (Fin.append (outputBits P word) (fun _ => false)) old := backward_selected _ _ _ _ _ _
    _ = _ := congrArg (fun work : Bits (NativeWordLayout.width Q (outputSize P word.length)) =>
      Fin.append work old) hw.symm

/-- The inverse is evaluated on the literal padded output of the forward
machine. Its contract must therefore hold on that actual fixed-length word,
not on an abstract unpadded value. -/
theorem secondCircuit_basis (word : Str)
    (hinverse : g (CoherentClassicalOracle.paddedOutput P word)=word) :
    runLayered (secondCircuit P Q word.length) (basis (middleBits P Q word))=
      basis (finalBits P Q word) := by
  apply relocateCircuit_basis
  · change runLayered (CoherentClassicalOracle.fullCircuit Q (outputSize P word.length))
        (basis ((wireBitsEquiv (secondWires P Q word.length) (dataBits (originalBits P Q word) (outputBits P word))).1))=
      basis ((wireBitsEquiv (secondWires P Q word.length) (dataBits (fun _ => false) (outputBits P word))).1)
    rw [backward_selected_word,backward_selected_word]
    have hlen : (CoherentClassicalOracle.paddedOutput P word).length=outputSize P word.length :=
      CoherentClassicalOracle.paddedOutput_length P word
    rw [fullCircuit_basis_at Q _ _ hlen]
    congr 2
    funext i
    simp [originalBits,hinverse]
  · exact backward_outside _ _ _ _ _ _ _

/-- A literal two-machine fixed-gate circuit realizes an injective native
map coherently, erasing the old input and returning both workspaces to zero. -/
theorem circuit_basis (word : Str)
    (hinverse : g (CoherentClassicalOracle.paddedOutput P word)=word) :
    runLayered (circuit P Q word.length) (basis (inputBits P Q word))=
      basis (finalBits P Q word) := by
  have he : runLayered (circuit P Q word.length) (basis (inputBits P Q word))=
      runLayered (secondCircuit P Q word.length)
        (runLayered (firstCircuit P Q word.length) (basis (inputBits P Q word))) := by
    simp only [circuit,runLayered,List.foldl_append]
  rw [he,firstCircuit_basis,secondCircuit_basis P Q word hinverse]

end InfoLossLAR.WorstCase.CoherentInjection

end

end P2MDyadicModule92

/- Helper module Solutions.RegevBridgeCoherentInjectionSuperposition. -/
section P2MDyadicModule93

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g)

def inputBitsAt (n : ℕ) (word : Str) : Bits (totalWidth P Q n) :=
  dataBits (fun i => wordExtension word i.val) (fun _ => false)

def finalBitsAt (n : ℕ) (word : Str) : Bits (totalWidth P Q n) :=
  dataBits (fun _ => false) (fun i => wordExtension (f word) i.val)

theorem circuit_basis_at (n : ℕ) (word : Str) (hlen : word.length=n)
    (hinverse : g (CoherentClassicalOracle.paddedOutput P word)=word) :
    runLayered (circuit P Q n) (basis (inputBitsAt P Q n word))=basis (finalBitsAt P Q n word) := by
  subst n
  exact circuit_basis P Q word hinverse

theorem inputBitsAt_injective (n : ℕ) (word other : Str) (ha : word.length=n) (hb : other.length=n)
    (he : inputBitsAt P Q n word=inputBitsAt P Q n other) : word=other := by
  apply List.ext_getElem
  · omega
  · intro i hi hj
    have hsize := originalSize_ge P Q n
    have hw : i<originalSize P Q n := by omega
    have hh := congrFun he ⟨i,by unfold totalWidth width;omega⟩
    change dataBits (a:=forwardWork P n) (b:=backwardWork P Q n)
      (fun j : Fin (originalSize P Q n) => wordExtension word j.val) (fun _ => false) ⟨i,_⟩=
        dataBits (fun j : Fin (originalSize P Q n) => wordExtension other j.val) (fun _ => false) ⟨i,_⟩ at hh
    simp only [dataBits,dif_pos hw] at hh
    simpa only [wordExtension_before word i hi,wordExtension_before other i hj] using hh

theorem finalBitsAt_injective (n : ℕ) (word other : Str) (ha : word.length=n) (hb : other.length=n)
    (hia : g (CoherentClassicalOracle.paddedOutput P word)=word)
    (hib : g (CoherentClassicalOracle.paddedOutput P other)=other)
    (he : finalBitsAt P Q n word=finalBitsAt P Q n other) : word=other := by
  have hp : CoherentClassicalOracle.paddedOutput P word=CoherentClassicalOracle.paddedOutput P other := by
    unfold CoherentClassicalOracle.paddedOutput
    simp only [ha,hb]
    apply congrArg List.ofFn
    funext i
    have hi : i.val<outputSize P n := i.isLt
    have hh := congrFun he ⟨originalSize P Q n+i.val,by unfold totalWidth width;omega⟩
    change dataBits (a:=forwardWork P n) (b:=backwardWork P Q n) (fun _ : Fin (originalSize P Q n) => false)
      (fun j : Fin (outputSize P n) => wordExtension (f word) j.val) ⟨originalSize P Q n+i.val,_⟩=
        dataBits (fun _ : Fin (originalSize P Q n) => false)
          (fun j : Fin (outputSize P n) => wordExtension (f other) j.val) ⟨originalSize P Q n+i.val,_⟩ at hh
    simpa only [dataBits_fresh,Fin.val_cast] using hh
  rw [←hia,←hib,hp]

variable {I : Type*} [Fintype I]

def inputEncoding (n : ℕ) (words : I → Str) (hlen : ∀ i,(words i).length=n)
    (hinj : Function.Injective words) : I ↪ Bits (totalWidth P Q n) where
  toFun i := inputBitsAt P Q n (words i)
  inj' := by intro i j he;exact hinj (inputBitsAt_injective P Q n _ _ (hlen i) (hlen j) he)

def outputEncoding (n : ℕ) (words : I → Str) (hlen : ∀ i,(words i).length=n)
    (hinj : Function.Injective words)
    (hinverse : ∀ i,g (CoherentClassicalOracle.paddedOutput P (words i))=words i) : I ↪ Bits (totalWidth P Q n) where
  toFun i := finalBitsAt P Q n (words i)
  inj' := by
    intro i j he
    exact hinj (finalBitsAt_injective P Q n _ _ (hlen i) (hlen j) (hinverse i) (hinverse j) he)

/-- One public native circuit, chosen only by the common input length,
acts on all amplitudes and phases at once. The output retains exactly the
injective value, while the entire old-input and two-workspace register is zero. -/
theorem circuit_superposition (n : ℕ) (words : I → Str) (hlen : ∀ i,(words i).length=n)
    (hinj : Function.Injective words)
    (hinverse : ∀ i,g (CoherentClassicalOracle.paddedOutput P (words i))=words i) (ψ : I → ℂ) :
    runLayered (circuit P Q n) (basisEmbedding (inputEncoding P Q n words hlen hinj) ψ)=
      basisEmbedding (outputEncoding P Q n words hlen hinj hinverse) ψ := by
  change runLayered (circuit P Q n) (∑ i,ψ i • basis (inputBitsAt P Q n (words i)))=
    ∑ i,ψ i • basis (finalBitsAt P Q n (words i))
  rw [←runLayeredLinearMap_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,runLayeredLinearMap_apply,circuit_basis_at P Q n (words i) (hlen i) (hinverse i)]

end InfoLossLAR.WorstCase.CoherentInjection

end

end P2MDyadicModule93

/- Helper module RectWindow. -/
section P2MDyadicModule94

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.Window

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

def wires {k N : ℕ} (off : ℕ) (h : off+k≤N) : Fin k ↪ Fin N where
  toFun i := ⟨off+i.val,by omega⟩
  inj' _ _ he := Fin.ext (by have hh := congrArg Fin.val he;dsimp at hh;omega)

def indices (x : ℕ×List Unit) := (List.range x.2.length).map (x.1+·)

@[fun_prop] theorem indices_poly : Poly indices := by
  unfold indices
  apply Poly.list_map (by fun_prop) (Poly.comp Poly.list_indices Poly.snd)

theorem indices_eq {N : ℕ} (off : ℕ) (ks : List Unit) (h : off+ks.length≤N) :
    indices (off,ks)=List.ofFn (fun i => (wires off h i).val) := by
  apply List.ext_getElem <;> simp [indices,wires]

def emit (x : (List Unit×ℕ)×(List Unit×List (List Str))) :=
  relocatedWordLayers (x.1.1,indices (x.1.2,x.2.1),x.2.2)

@[fun_prop] theorem emit_poly : Poly emit := by unfold emit;fun_prop

theorem emit_exact {N : ℕ} (ticks : List Unit) (ht : N≤ticks.length)
    (off : ℕ) (ks : List Unit) (h : off+ks.length≤N) (c : Layered ks.length) :
    emit ((ticks,off),ks,c.map (List.map encInstr))=(relocateCircuit (wires off h) c).map (List.map encInstr) := by
  unfold emit
  rw [indices_eq off ks h]
  exact relocatedWordLayers_exact _ _ _ ht

theorem inside {k N : ℕ} (off : ℕ) (h : off+k≤N) (pre post : Str) (hp : pre.length=off)
    (global : Bits N) (localBits : Bits k) (hword : List.ofFn global=pre++List.ofFn localBits++post) :
    (wireBitsEquiv (wires off h) global).1=localBits := by
  funext i
  let pos : Fin N := wires off h i
  change global pos=_
  have hw := congrArg (fun s : Str => s[pos.val]?) hword
  simp only [List.getElem?_ofFn,pos.isLt,↓reduceDIte] at hw
  have hi : pos.val<(pre++List.ofFn localBits).length := by simp [pos,wires,hp]
  have hj : pre.length≤pos.val := by simp [pos,wires,hp]
  change some (global pos) = (pre++List.ofFn localBits++post)[pos.val]? at hw
  rw [List.getElem?_append_left hi,List.getElem?_append_right hj] at hw
  simp only [pos,wires,Function.Embedding.coeFn_mk,hp,
    Nat.add_sub_cancel_left,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.some.injEq] at hw
  exact hw

theorem outside {k N : ℕ} (off : ℕ) (h : off+k≤N) (pre post : Str) (hp : pre.length=off)
    (x y : Bits N) (a b : Bits k) (hx : List.ofFn x=pre++List.ofFn a++post) (hy : List.ofFn y=pre++List.ofFn b++post) :
    (wireBitsEquiv (wires off h) x).2=(wireBitsEquiv (wires off h) y).2 := by
  funext v
  let i := v.val.val
  have hs : i < off ∨ off+k ≤ i := by
    by_contra! hn
    apply v.property
    refine ⟨⟨i-off,by omega⟩,Fin.ext ?_⟩
    change off+(i-off)=i
    omega
  have hx' := congrArg (fun s : Str => s[i]?) hx
  have hy' := congrArg (fun s : Str => s[i]?) hy
  have hi : i<N := v.val.isLt
  simp only [List.getElem?_ofFn,hi,↓reduceDIte] at hx' hy'
  change x v.val=y v.val
  apply Option.some.inj
  refine hx'.trans (Eq.trans ?_ hy'.symm)
  rcases hs with hpre|hpost
  · have hh : i<pre.length := by omega
    simp only [List.append_assoc,List.getElem?_append_left hh]
  · have hl (a : Bits k) : (pre++List.ofFn a).length=off+k := by simp [hp]
    rw [List.getElem?_append_right (by rw [hl];omega),List.getElem?_append_right (by rw [hl];omega),hl,hl]

variable {I J : Type} [Fintype I] [Fintype J] {k N : ℕ}

theorem tensor_attach (w : Fin k↪Fin N) (e : I×J ↪ Bits N) (a : I ↪ Bits k)
    (b : J ↪ OutsideBits w) (h : ∀ i j,wireBitsEquiv w (e (i,j))=(a i,b j))
    (v : I→ℂ) (u : J→ℂ) :
    basisEmbedding e (fun p => v p.1*u p.2) = attach w (basisEmbedding a v) (basisEmbedding b u) := by
  funext z
  by_cases he : z∈Set.range e
  · obtain ⟨⟨i,j⟩,rfl⟩ := he
    simp only [basisEmbedding_at,attach,h]
  · rw [basisEmbedding_outside e _ _ he,attach]
    let p := wireBitsEquiv w z
    change 0=basisEmbedding a v p.1*basisEmbedding b u p.2
    by_cases ha : p.1∈Set.range a
    · obtain ⟨i,hi⟩ := ha
      have hb : p.2∉Set.range b := by
        rintro ⟨j,hj⟩
        apply he
        refine ⟨(i,j),(wireBitsEquiv w).injective ?_⟩
        exact (h i j).trans (Prod.ext hi hj)
      rw [basisEmbedding_outside b _ _ hb,mul_zero]
    · rw [basisEmbedding_outside a _ _ ha,zero_mul]

def exterior (w : Fin k↪Fin N) (e : I×J ↪ Bits N) (a : I→Bits k) (i₀ : I)
    (ha : ∀ i j,(wireBitsEquiv w (e (i,j))).1=a i) : J ↪ OutsideBits w where
  toFun j := (wireBitsEquiv w (e (i₀,j))).2
  inj' j l he := by
    apply congrArg Prod.snd (e.injective ((wireBitsEquiv w).injective (Prod.ext ((ha i₀ j).trans (ha i₀ l).symm) he)))

theorem fixed_exterior (w : Fin k↪Fin N) (e : I×J ↪ Bits N) (a : I↪Bits k) (i₀ : I)
    (ha : ∀ i j,(wireBitsEquiv w (e (i,j))).1=a i)
    (hb : ∀ i j,(wireBitsEquiv w (e (i,j))).2=(wireBitsEquiv w (e (i₀,j))).2)
    (v : I→ℂ) (u : EuclideanSpace ℂ J) (hu : ‖u‖=1) :
    ∃ junk : OutsideBits w→ℂ, (∑ j,‖junk j‖^2)=1 ∧
      basisEmbedding e (fun ij => v ij.1 * u ij.2)=attach w (basisEmbedding a v) junk := by
  let b := exterior w e a i₀ ha
  refine ⟨basisEmbedding b u,?_,tensor_attach w e a b (fun i j => Prod.ext (ha i j) (hb i j)) _ _⟩
  have hn := basisEmbedding_norm b u.ofLp
  change ‖(WithLp.toLp 2 (basisEmbedding b u.ofLp) : EuclideanSpace ℂ _)‖=‖u‖ at hn
  rw [hu] at hn
  have he := congrArg (fun t : ℝ => t^2) hn
  simpa only [EuclideanSpace.norm_sq_eq,one_pow] using he

end

end InfoLossLAR.WorstCase.RectangularSource.Window

end P2MDyadicModule94

/- Helper module Solutions.RegevBridgeGaussianRandomizedRounding. -/
section P2MDyadicModule95

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource

open scoped BigOperators Classical ENNReal

noncomputable section

def roundingNormalizer (width center : ℝ) : ℝ≥0∞ :=
  ∑' value : ℤ,ENNReal.ofReal (shiftedWeight width center value)

theorem roundingNormalizer_ne_zero (width center : ℝ) : roundingNormalizer width center≠0 := by
  intro hz
  have hv := ENNReal.tsum_eq_zero.mp hz (0 : ℤ)
  exact (not_le_of_gt (show 0<shiftedWeight width center 0 from Real.exp_pos _)) (ENNReal.ofReal_eq_zero.mp hv)

theorem roundingNormalizer_ne_top (width center : ℝ) (hwidth : 0<width) :
    roundingNormalizer width center≠⊤ :=
  (summable_shiftedWeight width center hwidth).tsum_ofReal_ne_top

/-- The kernel uses the existing shifted theta normalizer exactly. -/
theorem roundingNormalizer_toReal (width center : ℝ) :
    (roundingNormalizer width center).toReal=theta width center := by
  unfold roundingNormalizer theta
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro value
  exact ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-- The displayed error is genuinely below one for widths at least one. -/
theorem roundingError_lt_one (width : ℝ) (hwidth : 1≤width) : thetaError width<1 := by
  have hs : 1≤width^2 := one_le_pow₀ hwidth
  have hp : 3<Real.pi*width^2 := by nlinarith [Real.pi_gt_three]
  have he : 4<Real.exp (Real.pi*width^2) :=
    (by linarith : (4 : ℝ)<Real.pi*width^2+1).trans_le (Real.add_one_le_exp _)
  have hn : Real.exp (-Real.pi*width^2)<1/4 := by
    rw [show -Real.pi*width^2=-(Real.pi*width^2) by ring,Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ)<1/4)).2
    simpa using he
  exact (thetaError_le_four_exp width hwidth).trans_lt (by linarith)

/-- The actual conditional PMF D_(Z-center),width shifted back to Z. -/
def roundingPMF (width : ℝ) (hwidth : 0<width) (center : ℝ) : PMF ℤ :=
  PMF.normalize (fun value => ENNReal.ofReal (shiftedWeight width center value))
    (roundingNormalizer_ne_zero width center) (roundingNormalizer_ne_top width center hwidth)

/-- Exact real conditional density of the normalized rounding PMF. -/
theorem roundingPMF_toReal (width : ℝ) (hwidth : 0<width) (center : ℝ) (value : ℤ) :
    (roundingPMF width hwidth center value).toReal=shiftedWeight width center value/theta width center := by
  change (ENNReal.ofReal (shiftedWeight width center value)*(roundingNormalizer width center)⁻¹).toReal=_
  rw [ENNReal.toReal_mul,ENNReal.toReal_inv,roundingNormalizer_toReal,
    ENNReal.toReal_ofReal (show 0 ≤ shiftedWeight width center value from Real.exp_nonneg _)]
  rfl

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule95

/- Helper module Solutions.RegevBridgeGaussianRoundingFiniteBits. -/
section P2MDyadicModule96

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

noncomputable section

theorem windowMass_pos (width : ℝ) (center : ℚ) (cutoff : ℕ) :
    0<∑ index : Fin (2*cutoff+1),shiftedWeight width center (windowPoint center cutoff index) := by
  have hz : 0< shiftedWeight width center (windowPoint center cutoff 0) := Real.exp_pos _
  exact hz.trans_le (Finset.single_le_sum
    (f := fun index : Fin (2*cutoff+1) => shiftedWeight width center (windowPoint center cutoff index))
    (fun index _ => (show 0 ≤ shiftedWeight width center (windowPoint center cutoff index) from Real.exp_nonneg _))
    (Finset.mem_univ 0))

/-- The exact truncated law, using the same true Gaussian weights as the
infinite randomized-rounding PMF. -/
def windowLaw (width : ℝ) (center : ℚ) (cutoff : ℕ) : FiniteDist (Fin (2*cutoff+1)) :=
  FiniteDist.normalize (fun index => shiftedWeight width center (windowPoint center cutoff index))
    (fun _ => Real.exp_nonneg _) (windowMass_pos width center cutoff)

/-- The finite reference is literally the full kernel conditioned to the
public integer window; the full theta normalization cancels exactly. -/
theorem windowLaw_eq_conditional (width : ℝ) (hwidth : 0< width) (center : ℚ) (cutoff : ℕ)
    (index : Fin (2*cutoff+1)) :
    (windowLaw width center cutoff).weight index=
      (roundingPMF width hwidth center (windowPoint center cutoff index)).toReal /
        ∑ point : Fin (2*cutoff+1),(roundingPMF width hwidth center (windowPoint center cutoff point)).toReal := by
  simp_rw [roundingPMF_toReal]
  simp only [windowLaw,FiniteDist.normalize]
  rw [←Finset.sum_div]
  field_simp [(theta_pos width center hwidth).ne',(windowMass_pos width center cutoff).ne']

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule96

/- Helper module Solutions.RegevBridgeGaussianRoundingTail. -/
section P2MDyadicModule97

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

noncomputable section

def tailEnvelope (width radius : ℝ) : ℝ :=
  Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width)*
    Real.exp (-Real.pi*radius^2/(2*width^2))

theorem summable_roundingMass (width : ℝ) (hwidth : 0<width) (center : ℝ) :
    Summable (fun value : ℤ => (roundingPMF width hwidth center value).toReal) := by
  simp_rw [roundingPMF_toReal]
  exact (summable_shiftedWeight width center hwidth).div_const _

private theorem theta_ratio_bound (width : ℝ) (hwidth : 1≤width) (center : ℝ) :
    theta (Real.sqrt 2*width) center/theta width center ≤
      Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width) := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hb : 0<Real.sqrt 2*width := by positivity
  have hs := roundingError_lt_one width hwidth
  have hl := (abs_le.mp (theta_relative_error_exp width center hw)).1
  have hu := (abs_le.mp (theta_relative_error_exp (Real.sqrt 2*width) center hb)).2
  have hlow : width*(1-thetaError width)≤theta width center := by
    rw [mul_comm]
    exact (le_div_iff₀ hw).mp (by linarith)
  have hupp : theta (Real.sqrt 2*width) center≤
      (Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)) := by
    have hn : theta (Real.sqrt 2*width) center/(Real.sqrt 2*width)≤1+thetaError (Real.sqrt 2*width) := by linarith
    exact ((div_le_iff₀ hb).mp hn).trans_eq (mul_comm _ _)
  have hpos : 0<width*(1-thetaError width) := mul_pos hw (by linarith)
  have ha : 0≤(Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)) := by
    have he := thetaError_nonneg (Real.sqrt 2*width) hb
    positivity
  calc
    _ ≤ ((Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)))/theta width center :=
      div_le_div_of_nonneg_right hupp (theta_pos width center hw).le
    _ ≤ ((Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)))/(width*(1-thetaError width)) :=
      div_le_div_of_nonneg_left ha hpos hlow
    _ = _ := by field_simp [hw.ne']

/-- Pointwise tail domination uses the actual shifted Gaussian at both
widths, so it is uniform over all real centers. -/
theorem shiftedWeight_tail_le (width center radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (value : ℤ) (hfar : radius≤|(value : ℝ)-center|) :
    shiftedWeight width center value≤
      Real.exp (-Real.pi*radius^2/(2*width^2))*shiftedWeight (Real.sqrt 2*width) center value := by
  have hroot : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsq : radius^2≤((value : ℝ)-center)^2 := by
    have h := (sq_le_sq₀ hradius (abs_nonneg ((value : ℝ)-center))).2 hfar
    simpa only [sq_abs] using h
  let a := Real.pi/(2*width^2)
  have ha : 0≤a := by dsimp [a];positivity
  have hh := mul_le_mul_of_nonneg_left hsq ha
  unfold shiftedWeight
  rw [←Real.exp_add,mul_pow,hroot]
  apply Real.exp_le_exp.mpr
  have he0 : -(Real.pi/width^2)*((value : ℝ)-center)^2=-2*a*((value : ℝ)-center)^2 := by dsimp [a];ring
  have he1 : -Real.pi*radius^2/(2*width^2)=-a*radius^2 := by dsimp [a];ring
  rw [he0,he1]
  change -2*a*((value : ℝ)-center)^2≤-a*radius^2+(-a)*((value : ℝ)-center)^2
  nlinarith

def roundingTail (width : ℝ) (hwidth : 0<width) (center radius : ℝ) : ℝ :=
  ∑' value : ℤ,if radius≤|(value : ℝ)-center| then (roundingPMF width hwidth center value).toReal else 0

/-- Full countable tail probability of the true normalized rounding PMF. -/
theorem roundingTail_le (width : ℝ) (hwidth : 1≤width) (center radius : ℝ) (hradius : 0≤radius) :
    roundingTail width (zero_lt_one.trans_le hwidth) center radius≤tailEnvelope width radius := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hb : 0<Real.sqrt 2*width := by positivity
  let factor := Real.exp (-Real.pi*radius^2/(2*width^2))/theta width center
  have hf : 0≤factor := div_nonneg (Real.exp_nonneg _) (theta_pos width center hw).le
  have hsum := (summable_shiftedWeight (Real.sqrt 2*width) center hb).mul_left factor
  have hp (value : ℤ) :
      (if radius≤|(value : ℝ)-center| then (roundingPMF width hw center value).toReal else 0)≤
        factor*shiftedWeight (Real.sqrt 2*width) center value := by
    split_ifs with hfar
    · rw [roundingPMF_toReal]
      have h := div_le_div_of_nonneg_right (shiftedWeight_tail_le width center radius hw hradius value hfar)
        (theta_pos width center hw).le
      exact h.trans_eq (by dsimp [factor];ring)
    · exact mul_nonneg hf (Real.exp_nonneg _)
  have hs : Summable (fun value : ℤ => if radius≤|(value : ℝ)-center| then
      (roundingPMF width hw center value).toReal else 0) :=
    Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) hp hsum
  have ht := hs.tsum_le_tsum hp hsum
  rw [tsum_mul_left] at ht
  change roundingTail width hw center radius≤factor*theta (Real.sqrt 2*width) center at ht
  apply ht.trans
  unfold tailEnvelope factor
  have hr := mul_le_mul_of_nonneg_right (theta_ratio_bound width hwidth center)
    (Real.exp_nonneg (-Real.pi*radius^2/(2*width^2)))
  convert hr using 1
  ring

/-- Omitted points from the floor-centered palette are genuinely far from
the original rational center, using integer discreteness on both sides. -/
theorem outsideWindow_far (center : ℚ) (cutoff : ℕ) (value : ℤ)
    (hout : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))) :
    (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| := by
  have hs := centeredGaussianAnchor_bounds center
  have ho : value≤centeredGaussianAnchor center-(cutoff : ℤ)-1 ∨
      centeredGaussianAnchor center+(cutoff : ℤ)+1≤value := by
    simp only [Finset.mem_Icc,not_and_or] at hout
    omega
  rcases ho with hl|hr
  · have hlR : (value : ℝ)≤(centeredGaussianAnchor center : ℝ)-(cutoff : ℝ)-1 := by exact_mod_cast hl
    apply le_trans _ (neg_le_abs ((value : ℝ)-(center : ℝ)))
    linarith [hs.1]
  · have hrR : (centeredGaussianAnchor center : ℝ)+(cutoff : ℝ)+1≤(value : ℝ) := by exact_mod_cast hr
    apply le_trans _ (le_abs_self ((value : ℝ)-(center : ℝ)))
    linarith [hs.2]

def outsideWindowMass (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) : ℝ :=
  ∑' value : ℤ,if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
    (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hwidth center value).toReal else 0

/-- A uniform analytic bound on the entire omitted probability of the same
infinite kernel approximated by the executed finite-bit sampler. -/
theorem outsideWindowMass_le (width : ℝ) (hwidth : 1≤width) (center : ℚ) (cutoff : ℕ) :
    outsideWindowMass width (zero_lt_one.trans_le hwidth) center cutoff≤tailEnvelope width cutoff := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hmass := summable_roundingMass width hw center
  have hs : Summable (fun value : ℤ => if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hw center value).toReal else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hmass
    intro value
    by_cases h : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have ht : Summable (fun value : ℤ => if (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| then
      (roundingPMF width hw center value).toReal else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hmass
    intro value
    by_cases h : (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)|
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have hp (value : ℤ) :
      (if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
        (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hw center value).toReal else 0)≤
      (if (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| then (roundingPMF width hw center value).toReal else 0) := by
    by_cases hout : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))
    · have hfar := outsideWindow_far center cutoff value hout
      rw [if_pos hout,if_pos hfar]
    · rw [if_neg hout]
      split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
  exact (hs.tsum_le_tsum hp ht).trans (roundingTail_le width hwidth center cutoff (Nat.cast_nonneg _))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule97

/- Helper module Solutions.RegevBridgeGaussianRoundingTruncation. -/
section P2MDyadicModule98

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

noncomputable section

/-- Exact indexing of the actual integer window around the computed floor. -/
def windowPointEquiv (center : ℚ) (cutoff : ℕ) : Fin (2*cutoff+1) ≃
    ↥(Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))) where
  toFun index := ⟨windowPoint center cutoff index,by
    have hi := index.isLt
    simp only [Finset.mem_Icc,windowPoint]
    constructor <;> omega⟩
  invFun point := ⟨(point.val-centeredGaussianAnchor center+(cutoff : ℤ)).toNat,by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    omega⟩
  left_inv index := by
    apply Fin.ext
    change ((windowPoint center cutoff index)-centeredGaussianAnchor center+(cutoff : ℤ)).toNat=index.val
    simp only [windowPoint]
    have hi := index.isLt
    omega
  right_inv point := by
    apply Subtype.ext
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    change windowPoint center cutoff ⟨(point.val-centeredGaussianAnchor center+(cutoff : ℤ)).toNat,_⟩=point.val
    simp only [windowPoint]
    omega

theorem windowPoint_sum (center : ℚ) (cutoff : ℕ) (test : ℤ → ℝ) :
    (∑ index : Fin (2*cutoff+1),test (windowPoint center cutoff index))=
      ∑ value ∈ Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
        (centeredGaussianAnchor center+(cutoff : ℤ)),test value := by
  have h := (windowPointEquiv center cutoff).sum_comp (fun point => test point.val)
  rw [Finset.sum_coe_sort] at h
  exact h

/-- Real masses of the genuine countable rounding kernel sum to one. -/
theorem roundingMass_sum (width : ℝ) (hwidth : 0<width) (center : ℝ) :
    (∑' value : ℤ,(roundingPMF width hwidth center value).toReal)=1 := by
  simp_rw [roundingPMF_toReal]
  rw [tsum_div_const]
  exact div_self (theta_pos width center hwidth).ne'

def retainedResidue (q : ℕ) (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) (output : ZMod q) : ℝ :=
  ∑ index : Fin (2*cutoff+1),@ite ℝ ((windowPoint center cutoff index : ZMod q)=output)
    (Classical.propDecidable _) (roundingPMF width hwidth center (windowPoint center cutoff index)).toReal 0

theorem retainedResidue_sum (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) :
    (∑ output : ZMod q,retainedResidue q width hwidth center cutoff output)=
      ∑ index : Fin (2*cutoff+1),(roundingPMF width hwidth center (windowPoint center cutoff index)).toReal := by
  unfold retainedResidue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  exact @Fintype.sum_ite_eq (ZMod q) ℝ _ _
    (fun first second => Classical.propDecidable (first=second))
      (windowPoint center cutoff index : ZMod q)
      (fun _ => (roundingPMF width hwidth center (windowPoint center cutoff index)).toReal)

/-- The discarded countable mass is exactly one minus the retained finite
mass. This identity retains the true kernel normalization throughout. -/
theorem outsideWindowMass_eq (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) :
    outsideWindowMass width hwidth center cutoff=
      1-∑ output : ZMod q,retainedResidue q width hwidth center cutoff output := by
  rw [retainedResidue_sum,windowPoint_sum center cutoff
    (fun value : ℤ => (roundingPMF width hwidth center value).toReal)]
  let window := Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
    (centeredGaussianAnchor center+(cutoff : ℤ))
  let mass := fun value : ℤ => (roundingPMF width hwidth center value).toReal
  have hs := summable_roundingMass width hwidth center
  have hinside : Summable (fun value : ℤ => if value∈window then mass value else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hs
    intro value
    split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  have houtside : Summable (fun value : ℤ => if value∉window then mass value else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hs
    intro value
    by_cases h : value∉window
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have he : (∑' value : ℤ,if value∈window then mass value else 0)+
      (∑' value : ℤ,if value∉window then mass value else 0)=1 := by
    rw [←hinside.tsum_add houtside]
    calc
      _ = ∑' value : ℤ,mass value := by
        apply tsum_congr
        intro value
        by_cases h : value∈window <;> simp [h]
      _ = _ := roundingMass_sum width hwidth center
  have hi : (∑' value : ℤ,if value∈window then mass value else 0)=∑ value∈window,mass value := by
    rw [tsum_eq_sum (s := window) (fun value hv => if_neg hv)]
    apply Finset.sum_congr rfl
    intro value hv
    rw [if_pos hv]
  rw [hi] at he
  change (∑' value : ℤ,if value∉window then mass value else 0)=1-∑ value∈window,mass value
  linarith

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule98

/- Helper module Solutions.RegevBridgeGaussianRoundingContinuous. -/
section P2MDyadicModule99

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency true

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource MeasureTheory

open scoped BigOperators Classical

noncomputable section

theorem roundingError_lt_half (width : ℝ) (hwidth : 1 ≤ width) : thetaError width<1/2 := by
  have hs : 1 ≤ width^2 := one_le_pow₀ hwidth
  have hp : 3<Real.pi*width^2 := by nlinarith [Real.pi_gt_three]
  have he3 : (8 : ℝ)<Real.exp 3 := by
    have h := Real.exp_one_gt_two
    have he : Real.exp 3=(Real.exp 1)^3 := by rw [←Real.exp_nat_mul];norm_num
    rw [he]
    have he2 : 4<(Real.exp 1)^2 := by nlinarith
    nlinarith [mul_pos (by linarith : 0<Real.exp 1-2) (by linarith : 0<(Real.exp 1)^2-4)]
  have he := he3.trans (Real.exp_lt_exp.mpr hp)
  have hn : Real.exp (-Real.pi*width^2)<1/8 := by
    rw [show -Real.pi*width^2=-(Real.pi*width^2) by ring,Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ)<1/8)).2
    simpa using he
  exact (thetaError_le_four_exp width hwidth).trans_lt (by linarith)

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule99

/- Helper module Solutions.RegevBridgeGaussianRoundingNative. -/
section P2MDyadicModule100

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteSeries TM2NativeGaussian

open scoped BigOperators

theorem anchor_eq (center : ℚ) : anchor center=(centeredGaussianAnchor center : ℚ) := by
  unfold anchor
  split <;> rename_i hc
  · have hn := Int.natCast_ceil_eq_ceil (neg_nonneg.mpr hc.le)
    rw [←Int.cast_natCast,hn,Int.ceil_neg,Int.cast_neg,neg_neg]
    rfl
  · rw [←Int.cast_natCast,Int.natCast_floor_eq_floor (le_of_not_gt hc)]
    rfl

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

end P2MDyadicModule100

/- Helper module Solutions.RegevBridgeGaussianLatticeTransport. -/
section P2MDyadicModule101

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- Self-adjointness transports dual membership through the forward map. -/
theorem mem_dual_image_iff (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : Space (dimension := dimension)) :
    value ∈ dual (imageLattice lattice transform) ↔ transform value ∈ dual lattice := by
  change (∀ test ∈ imageLattice lattice transform,
    inner ℝ value test ∈ (1 : Submodule ℤ ℝ)) ↔
    ∀ test ∈ lattice, inner ℝ (transform value) test ∈ (1 : Submodule ℤ ℝ)
  constructor
  · intro membership test test_mem
    rw [selfAdjoint]
    apply membership
    simpa using test_mem
  · intro membership test test_mem
    have h := membership (transform.symm test) test_mem
    rw [selfAdjoint, transform.apply_symm_apply] at h
    exact h

/-- The dual of the image is parametrized by the inverse map on the old dual. -/
def dualEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) :
    dual lattice ≃ dual (imageLattice lattice transform) where
  toFun value := ⟨transform.symm value,
    (mem_dual_image_iff lattice transform selfAdjoint _).mpr (by simpa using value.property)⟩
  invFun value := ⟨transform value,
    (mem_dual_image_iff lattice transform selfAdjoint _).mp value.property⟩
  left_inv value := by ext; simp
  right_inv value := by ext; simp

@[simp] theorem dualEquiv_apply (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : dual lattice) :
    ((dualEquiv lattice transform selfAdjoint value : dual (imageLattice lattice transform)) :
      Space (dimension := dimension)) = transform.symm value := rfl


@[simp] theorem dualEquiv_eq_zero_iff (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : dual lattice) :
    dualEquiv lattice transform selfAdjoint value = 0 ↔ value = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    have h' := congrArg (fun z : dual (imageLattice lattice transform) =>
      transform (z : Space (dimension := dimension))) h
    simpa using h'
  · rintro rfl
    apply Subtype.ext
    simp

def dualNonzeroEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) :
    {value : dual lattice // value ≠ 0} ≃
      {value : dual (imageLattice lattice transform) // value ≠ 0} :=
  (dualEquiv lattice transform selfAdjoint).subtypeEquiv (by
    intro value
    exact not_congr (dualEquiv_eq_zero_iff lattice transform selfAdjoint value).symm)

/-- Exact reindexing of the entire nonzero-dual Gaussian sum. -/
theorem rhoDualNonzero_image (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (width : ℝ) :
    rhoDualNonzero width (imageLattice lattice transform) =
      ∑' value : {value : dual lattice // value ≠ 0},
        rho width (transform.symm ((value : dual lattice) : Space (dimension := dimension))) := by
  unfold rhoDualNonzero
  symm
  have reindex := (dualNonzeroEquiv lattice transform selfAdjoint).tsum_eq
    (fun value : {value : dual (imageLattice lattice transform) // value ≠ 0} =>
      rho width ((value.val : dual (imageLattice lattice transform)) : Space (dimension := dimension)))
  exact reindex

end

end InfoLossLAR.WorstCase.GaussianLatticeTransport

end P2MDyadicModule101

/- Helper module Solutions.RegevBridgeGaussianProjectionSmoothing. -/
section P2MDyadicModule102

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv

noncomputable section

open scoped BigOperators

/-- A usable public version of the smoothing-threshold consequence. The
zero-dimensional case is discharged, and the positive-dimensional case
uses the recovered, proved exact characterization of smoothingParam. -/
theorem dual_mass_le_of_smoothing {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0<error) (hwidth : 0<width) (hsmoothing : smoothingParam lattice error ≤ width) :
    rhoDualNonzero (1/width) lattice ≤ error := by
  rcases Nat.eq_zero_or_pos dimension with rfl | hdimension
  · have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have : IsEmpty {value : dual lattice // value≠0} :=
      ⟨fun value => value.property (Subsingleton.elim value.val 0)⟩
    unfold rhoDualNonzero
    simp [herror.le]
  · obtain ⟨_,hantitone,_,_,hthreshold⟩ := RegevLWE.GaussConv.smoothing_remark hdimension lattice
    obtain ⟨hpositive,hequal⟩ := hthreshold error herror
    rw [←hequal]
    exact hantitone.antitoneOn hpositive hwidth hsmoothing

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule102

/- Helper module Solutions.RegevBridgeGaussianLatticeScaling. -/
section P2MDyadicModule103

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem dilation_apply (factor : ℝ) (hfactor : 0<factor) (value : ScalingSpace (dimension:=dimension)) :
    dilation factor hfactor value=factor • value := rfl

theorem dilation_symmetric (factor : ℝ) (hfactor : 0<factor) (first second : ScalingSpace (dimension:=dimension)) :
    inner ℝ (dilation factor hfactor first) second=inner ℝ first (dilation factor hfactor second) := by
  rw [dilation_apply,dilation_apply,real_inner_smul_left,real_inner_smul_right]

theorem rho_dilation_inverse (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width)
    (value : ScalingSpace (dimension:=dimension)) :
    rho width ((dilation factor hfactor).symm value)=rho (factor*width) value := by
  unfold rho
  rw [dilation_symm_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hfactor)]
  congr 1
  field_simp [hfactor.ne',hwidth.ne']

theorem rhoDualNonzero_dilation (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension)))
    (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width) :
    rhoDualNonzero width (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor))=
      rhoDualNonzero (factor*width) lattice := by
  rw [rhoDualNonzero_image lattice (dilation factor hfactor) (dilation_symmetric factor hfactor)]
  simp_rw [rho_dilation_inverse factor width hfactor hwidth]
  rfl

/-- A proved smoothing upper bound under actual lattice dilation.
Only the source smoothing condition is required. -/
theorem dilation_smoothing_le
    (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (factor width error : ℝ) (hfactor : 0<factor) (hwidth : 0<width) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ width) :
    smoothingParam (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) error ≤ factor*width := by
  have hm : rhoDualNonzero (1/(factor*width)) (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) ≤ error := by
    rw [rhoDualNonzero_dilation lattice factor (1/(factor*width)) hfactor (by positivity)]
    have he : factor*(1/(factor*width))=1/width := by field_simp
    rw [he]
    exact dual_mass_le_of_smoothing lattice herror hwidth hsmoothing
  unfold smoothingParam
  apply csInf_le
  · exact ⟨0,fun value membership => membership.1.le⟩
  · exact ⟨mul_pos hfactor hwidth,hm⟩

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule103

/- Helper module Solutions.RegevBridgeGaussianGridProjection. -/
section P2MDyadicModule104

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

/-- Uniform truncation error profile over the publicly enumerated width
interval. The upper width controls the Gaussian tail; the lower width
controls both theta normalizers. -/
def intervalTail (lower upper radius : ℝ) : ℝ :=
  Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower)*Real.exp (-Real.pi*radius^2/(2*upper^2))

theorem tailEnvelope_interval {lower width upper : ℝ} (radius : ℝ)
    (hlower : 1 ≤ lower) (hlowerWidth : lower ≤ width) (hwidthUpper : width ≤ upper) :
    tailEnvelope width radius ≤ intervalTail lower upper radius := by
  have hlo : 0<lower := zero_lt_one.trans_le hlower
  have hw : 0<width := hlo.trans_le hlowerWidth
  have hu : 0<upper := hw.trans_le hwidthUpper
  have hwOne : 1 ≤ width := hlower.trans hlowerWidth
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  have ht := thetaError_antitone lower width hlo hlowerWidth
  have htb := thetaError_antitone lower (Real.sqrt 2*width) hlo
    (hlowerWidth.trans (le_mul_of_one_le_left hw.le hroot))
  have hdlo : 0<1-thetaError lower := sub_pos.mpr (roundingError_lt_one lower hlower)
  have hdw : 0<1-thetaError width := sub_pos.mpr (roundingError_lt_one width hwOne)
  have hnum : 0 ≤ Real.sqrt 2*(1+thetaError lower) := by
    have he := thetaError_nonneg lower hlo
    positivity
  have hfactor : Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width) ≤
      Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower) := by
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl htb) (Real.sqrt_nonneg 2)) hdw.le).trans
    exact div_le_div_of_nonneg_left hnum hdlo (by linarith)
  have hn : 0 ≤ Real.pi*radius^2 := mul_nonneg Real.pi_pos.le (sq_nonneg radius)
  have hsq : 2*width^2 ≤ 2*upper^2 := by nlinarith [(sq_le_sq₀ hw.le hu.le).mpr hwidthUpper]
  have hfrac := div_le_div_of_nonneg_left hn (mul_pos (by norm_num : (0 : ℝ)<2) (sq_pos_of_pos hw)) hsq
  have hexp : Real.exp (-Real.pi*radius^2/(2*width^2)) ≤ Real.exp (-Real.pi*radius^2/(2*upper^2)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -(Real.pi*radius^2/(2*width^2)) := by ring
      _ ≤ -(Real.pi*radius^2/(2*upper^2)) := neg_le_neg hfrac
      _ = _ := by ring
  unfold tailEnvelope intervalTail
  exact (mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hexp (div_nonneg hnum hdlo.le))

end

end InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

end P2MDyadicModule104

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule105

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

theorem integerBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    (integerBasis basis hdet index : Space (dimension:=dimension))=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  exact (Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index).trans (realBasis_apply basis hdet index)

/-- The coefficient vector sent to the native program represents exactly
its target-defined lattice point `latVec basis value`. -/
theorem coefficient_point (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) :
    ((integerBasis basis hdet).equivFun.symm value : Space (dimension:=dimension))=latVec basis value := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,integerBasis_apply]
  ext row
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_toLp,Finset.sum_apply,latVec,Matrix.mulVec,dotProduct,
    Int.cast_sum,Int.cast_mul,zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule105

/- Helper module Solutions.RegevBridgeIntegerBasisNative. -/
section P2MDyadicModule106

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

private theorem zip_ofFn {α β : Type*} {count : ℕ} (left : Fin count → α) (right : Fin count → β) :
    (List.ofFn left).zip (List.ofFn right)=List.ofFn (fun index => (left index,right index)) := by
  apply List.ext_getElem
  · simp
  · intros;simp

theorem matrixApply_ofFn {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (value : Fin dimension → ℤ) :
    matrixApply (List.ofFn (fun row => List.ofFn (basis row)),List.ofFn value)=List.ofFn (basis.mulVec value) := by
  simp only [matrixApply,List.map_ofFn]
  apply congrArg List.ofFn
  funext row
  simp only [Function.comp_apply,Integration9_9.TM2NativeAffineApply.dot,zip_ofFn,List.map_ofFn,List.sum_ofFn]
  rfl

end InfoLossLAR.WorstCase.IntegerBasis.Native

end P2MDyadicModule106

/- Helper module Solutions.RegevBridgeGaussianNumericalBudget. -/
section P2MDyadicModule107

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

/-- The complete shifted-normalizer prefactor is uniformly bounded in
the actual wide-kernel regime, including its dependence on both widths. -/
theorem intervalTail_le_six {lower upper radius : ℝ} (hlower : 1 ≤ lower) :
    VarianceGrid.intervalTail lower upper radius ≤ 6*Real.exp (-Real.pi*radius^2/(2*upper^2)) := by
  have ht := roundingError_lt_half lower hlower
  have htzero := thetaError_nonneg lower (zero_lt_one.trans_le hlower)
  have hroot : Real.sqrt (2 : ℝ) ≤ 2 := by apply Real.sqrt_le_iff.mpr;norm_num
  have hden : 0<1-thetaError lower := by linarith
  have hnum : Real.sqrt 2*(1+thetaError lower) ≤ 3 := by nlinarith
  have hfactor : Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower) ≤ 6 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule107

/- Helper module Solutions.RegevBridgeWideGaussianScale. -/
section P2MDyadicModule108

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteDraw

open scoped BigOperators

/-- A binary power-of-two width envelope is derived from numerator and
denominator bit lengths, without evaluating an irrational square root. -/
def scaleEnvelope (numerator denominator : ℕ) : ℕ :=
  2^((Nat.size numerator-Nat.size denominator+2)/2)

theorem binary_size_bounds (value : ℕ) (hvalue : 0<value) :
    2^(Nat.size value-1) ≤ value ∧ value<2^Nat.size value := by
  have hs : 0<Nat.size value := Nat.size_pos.mpr hvalue
  exact ⟨Nat.lt_size.mp (by omega),Nat.lt_size_self value⟩

/-- The envelope is within a fixed factor in squared width, even when
the width itself is exponentially large in the input bit length. -/
theorem scaleEnvelope_bounds (numerator denominator : ℕ) (hdenominator : 0<denominator)
    (hratio : denominator ≤ numerator) :
    numerator ≤ (scaleEnvelope numerator denominator)^2*denominator ∧
      (scaleEnvelope numerator denominator)^2*denominator ≤ 8*numerator := by
  have hnum : 0<numerator := hdenominator.trans_le hratio
  have hsize := Nat.size_le_size hratio
  have hnsize : 0<Nat.size numerator := Nat.size_pos.mpr hnum
  have hdsize : 0<Nat.size denominator := Nat.size_pos.mpr hdenominator
  obtain ⟨hnlower,hnupper⟩ := binary_size_bounds numerator hnum
  obtain ⟨hdlower,hdupper⟩ := binary_size_bounds denominator hdenominator
  let gap := Nat.size numerator-Nat.size denominator
  have hsum : Nat.size numerator=gap+Nat.size denominator := (Nat.sub_add_cancel hsize).symm
  have hsquare : (scaleEnvelope numerator denominator)^2=2^(2*((gap+2)/2)) := by
    unfold scaleEnvelope
    rw [←pow_mul]
    congr 1
    change ((gap+2)/2)*2=2*((gap+2)/2)
    omega
  have hlowExponent : gap+1 ≤ 2*((gap+2)/2) := by omega
  have huppExponent : 2*((gap+2)/2) ≤ gap+2 := by omega
  have hlowPow : 2^(gap+1) ≤ (scaleEnvelope numerator denominator)^2 := by
    rw [hsquare]
    exact Nat.pow_le_pow_right (by norm_num) hlowExponent
  have huppPow : (scaleEnvelope numerator denominator)^2 ≤ 2^(gap+2) := by
    rw [hsquare]
    exact Nat.pow_le_pow_right (by norm_num) huppExponent
  constructor
  · calc
      numerator ≤ 2^Nat.size numerator := hnupper.le
      _ = 2^(gap+1)*2^(Nat.size denominator-1) := by
        rw [←pow_add]
        congr 1
        omega
      _ ≤ 2^(gap+1)*denominator := Nat.mul_le_mul_left _ hdlower
      _ ≤ _ := Nat.mul_le_mul_right _ hlowPow
  · calc
      _ ≤ 2^(gap+2)*2^Nat.size denominator := Nat.mul_le_mul huppPow hdupper.le
      _ = 8*2^(Nat.size numerator-1) := by
        rw [←pow_add,show (8 : ℕ)=2^3 by norm_num,←pow_add]
        congr 1
        omega
      _ ≤ _ := Nat.mul_le_mul_left _ hnlower

@[fun_prop] theorem naturalBits_poly : Poly Nat.bits := ⟨PolyProgram.natAsList⟩

@[fun_prop] theorem signedAbsolute_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩

@[fun_prop] theorem dropTicks_poly : Poly (fun input : List Unit × ℕ => input.1.drop input.2) :=
  ⟨PolyProgram.listDrop Automatic.enc ()⟩

@[fun_prop] theorem numeratorTicks_poly : Poly numeratorTicks := by unfold numeratorTicks;fun_prop

@[fun_prop] theorem rawScaleTicks_poly : Poly rawScaleTicks := by
  have hd : Poly (fun squaredWidth : ℚ => (numeratorTicks squaredWidth).drop (Nat.size squaredWidth.den)) :=
    Poly.comp (f:=fun input : List Unit × ℕ => input.1.drop input.2)
      (g:=fun squaredWidth : ℚ => (numeratorTicks squaredWidth,Nat.size squaredWidth.den)) dropTicks_poly (by fun_prop)
  unfold rawScaleTicks
  exact Poly.comp (f:=fun ticks : List Unit => ticks++[(),()])
    (g:=fun squaredWidth : ℚ => (numeratorTicks squaredWidth).drop (Nat.size squaredWidth.den)) (by fun_prop) hd

@[fun_prop] theorem takeTicks_poly : Poly (fun input : List Unit × ℕ => input.1.take input.2) :=
  ⟨PolyProgram.listTake Automatic.enc ()⟩

@[fun_prop] theorem scaleTicks_poly : Poly scaleTicks := by
  unfold scaleTicks
  exact Poly.comp (f:=fun input : List Unit × ℕ => input.1.take input.2)
    (g:=fun squaredWidth : ℚ => (rawScaleTicks squaredWidth,(rawScaleTicks squaredWidth).length/2))
    takeTicks_poly (by fun_prop)

@[fun_prop] theorem scale_poly : Poly scale := by unfold scale;fun_prop

theorem scale_eq (squaredWidth : ℚ) : scale squaredWidth=scaleEnvelope squaredWidth.num.natAbs squaredWidth.den := by
  simp only [scale,dyadicPower,scaleTicks,rawScaleTicks,numeratorTicks,List.length_take,List.length_append,List.length_drop,
    List.length_map,List.length_cons,List.length_nil,Nat.size_eq_bits_len]
  rw [Nat.min_eq_left (Nat.div_le_self _ _)]
  rfl

/-- The real sampler receives the rational variance. Its native scale is
proved to sandwich that exact variance without an irrational-width input. -/
theorem scale_variance_bounds (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth) :
    squaredWidth ≤ (scale squaredWidth : ℚ)^2 ∧
      (scale squaredWidth : ℚ)^2 ≤ 8*squaredWidth := by
  have hpositive : 0<squaredWidth := zero_lt_one.trans_le hwidth
  have hnpositive : 0<squaredWidth.num := Rat.num_pos.mpr hpositive
  have hncast : (squaredWidth.num.natAbs : ℚ)=(squaredWidth.num : ℚ) := by
    have he : (squaredWidth.num.natAbs : ℤ)=squaredWidth.num := by
      rw [Int.natCast_natAbs,abs_of_pos hnpositive]
    simpa only [Int.cast_natCast] using congrArg (fun value : ℤ => (value : ℚ)) he
  have hd : (0 : ℚ)<squaredWidth.den := by exact_mod_cast squaredWidth.pos
  have heq : squaredWidth=(squaredWidth.num.natAbs : ℚ)/(squaredWidth.den : ℚ) := by
    rw [hncast,Rat.num_div_den]
  have hratio : squaredWidth.den ≤ squaredWidth.num.natAbs := by
    have h := (le_div_iff₀ hd).mp (heq ▸ hwidth)
    simp only [one_mul] at h
    exact_mod_cast h
  have hbounds := scaleEnvelope_bounds squaredWidth.num.natAbs squaredWidth.den squaredWidth.pos hratio
  rw [←scale_eq squaredWidth] at hbounds
  constructor
  · conv_lhs => rw [heq]
    apply (div_le_iff₀ hd).mpr
    exact_mod_cast hbounds.1
  · conv_rhs => rw [heq,←mul_div_assoc]
    apply (le_div_iff₀ hd).mpr
    exact_mod_cast hbounds.2

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule108

/- Helper module Solutions.RegevBridgeWideGaussianPoint. -/
section P2MDyadicModule109

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeGaussian

open scoped BigOperators

@[fun_prop] theorem variance_poly : Poly variance := by unfold variance;fun_prop

@[fun_prop] theorem radius_poly : Poly radius := by unfold radius;fun_prop

@[fun_prop] theorem intervalCount_poly : Poly intervalCount := by unfold intervalCount;fun_prop

@[fun_prop] theorem anchorInteger_poly : Poly anchorInteger := by unfold anchorInteger;fun_prop

theorem anchorInteger_eq (center : ℚ) : anchorInteger center=⌊center⌋ := by
  simp only [anchorInteger,GaussianRandomizedRounding.Native.anchor_eq,centeredGaussianAnchor,Rat.num_intCast]

@[fun_prop] theorem point_poly : Poly point := by unfold point;fun_prop

@[fun_prop] theorem pointRatio_poly : Poly pointRatio := by
  have h : Poly (fun input : PointRequest × ℕ => (((point input : ℚ)-input.1.1.2)*((point input : ℚ)-input.1.1.2))/variance input.1) := by fun_prop
  unfold pointRatio
  simpa only [pow_two] using h

@[fun_prop] theorem pointGuardTicks_poly : Poly pointGuardTicks := by unfold pointGuardTicks;fun_prop

noncomputable def pointProgram : PolyProgram Automatic.enc Ratio.encode pointValue := by
  let prepare : PolyProgram Automatic.enc TM2NativeGaussian.requestCode
      (fun input : PointRequest × ℕ => ((pointRatio input,input.1.2.2),pointGuardTicks input.1)) :=
    (show Poly (fun input : PointRequest × ℕ => ((pointRatio input,input.1.2.2),pointGuardTicks input.1)) by fun_prop).program
  exact prepare.comp gaussianProgram

@[fun_prop] theorem pointValue_poly : Poly pointValue := ⟨pointProgram⟩

noncomputable section

theorem variance_ge_one (input : PointRequest) : 1 ≤ variance input := by unfold variance;split <;> first | assumption | exact le_rfl

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule109

/- Helper module Solutions.RegevBridgeWideGaussianMass. -/
section P2MDyadicModule110

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

theorem scale_width_bounds (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) :
    width ≤ (scale (variance input) : ℝ) ∧ (scale (variance input) : ℝ) ≤ 3*width := by
  have h := scale_variance_bounds (variance input) (variance_ge_one input)
  have hl : width^2 ≤ (scale (variance input) : ℝ)^2 := by
    have hh : (variance input : ℝ) ≤ (scale (variance input) : ℝ)^2 := by exact_mod_cast h.1
    rwa [←hsquare] at hh
  have hu : (scale (variance input) : ℝ)^2 ≤ 8*width^2 := by
    have hh : (scale (variance input) : ℝ)^2 ≤ 8*(variance input : ℝ) := by exact_mod_cast h.2
    rwa [←hsquare] at hh
  constructor
  · exact (sq_le_sq₀ (zero_lt_one.trans_le hwidth).le (Nat.cast_nonneg _)).mp hl
  · nlinarith [show (0 : ℝ) ≤ scale (variance input) by positivity,sq_nonneg width]

theorem point_eq_windowPoint (input : PointRequest) (index : Fin (intervalCount input)) :
    point (input,index.val)=windowPoint input.1.2 (radius input) index := by
  rw [point,anchorInteger_eq]
  rfl

def trueWindowMass (input : PointRequest) (width : ℝ) : ℝ :=
  ∑ index : Fin (intervalCount input),shiftedWeight width input.1.2 (point (input,index.val))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule110

/- Helper module Solutions.RegevBridgeNativeSquareRoot. -/
section P2MDyadicModule111

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.NativeSquareRoot

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem capacity_poly : Poly capacity := by unfold capacity;fun_prop

@[fun_prop] theorem test_poly : Poly test := by unfold test;fun_prop

@[fun_prop] theorem index_poly : Poly index := by
  unfold index
  apply Poly.list_findIdx test_poly
  have h := Poly.comp (f:=fun xs : List Unit => List.range xs.length)
    (g:=fun x : Input => x.2++[()]) Poly.list_indices (by fun_prop)
  simpa only [List.length_append,List.length_singleton,capacity] using h

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

end InfoLossLAR.WorstCase.NativeSquareRoot

end P2MDyadicModule111

/- Helper module Solutions.RegevBridgeAcceptanceRotation. -/
section P2MDyadicModule112
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.AcceptanceRotation

open QAlgorithms FiniteGateTransport

open scoped BigOperators

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem cValue_poly : Poly cValue := by unfold cValue;fun_prop

@[fun_prop] theorem sValue_poly : Poly sValue := by unfold sValue;fun_prop

@[fun_prop] theorem nativeTarget_poly : Poly nativeTarget := by
  apply FiniteGateNative.matrix_build_poly
  intro row _ col _
  unfold nativeTarget FiniteGateNative.singleGate coefficient
  by_cases h : col=Function.update row 0 (col 0)
  · simp only [if_pos h]
    cases row 0 <;> cases col 0 <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
  · simp only [if_neg h]
    exact Automatic.Poly.const _

end InfoLossLAR.WorstCase.AcceptanceRotation

end P2MDyadicModule112

/- Helper module Solutions.RegevBridgeNativeAcceptanceGates. -/
section P2MDyadicModule113
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativeAcceptanceGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport FiniteGateNative

@[fun_prop] theorem sqrtBudget_poly : Poly sqrtBudget := by unfold sqrtBudget;fun_prop

@[fun_prop] theorem target_poly : Poly target := by unfold target;fun_prop

attribute [local irreducible] nativeCompile current target

theorem current_poly (a : ℕ) : Poly (current a) := by
  unfold current
  exact Poly.comp (nativeCompile_poly a) (Poly.pair Poly.snd target_poly)

end InfoLossLAR.WorstCase.NativeAcceptanceGates

end P2MDyadicModule113

/- Helper module Solutions.RegevBridgeCoherentWideGaussian. -/
section P2MDyadicModule114

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open AFT GaussianSource RationalNumerics

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

instance ticketCount_neZero (input : PointRequest) : NeZero (ticketCount input) :=
  ⟨pow_ne_zero _ (by decide)⟩

@[fun_prop] theorem numericalProbability_poly : Poly numericalProbability := by
  unfold numericalProbability
  fun_prop

theorem sum_weight (input : PointRequest) (width : ℝ) :
    (∑ ticket : Ticket input,weight input width ticket.val)=trueWindowMass input width := by
  rw [Fin.sum_univ_eq_sum_range]
  have hs := Finset.sum_subset (Finset.range_mono (Nat.lt_size_self (intervalCount input)).le)
    (f:=weight input width) (by
      intro index _ hn
      simp only [Finset.mem_range,not_lt] at hn
      simp only [weight,if_neg (Nat.not_lt.mpr hn)])
  change (∑ i∈Finset.range (2^Nat.size (intervalCount input)),weight input width i)=_
  rw [←hs]
  unfold trueWindowMass
  rw [Fin.sum_univ_eq_sum_range (fun index => shiftedWeight width input.1.2 (point (input,index))) (intervalCount input)]
  apply Finset.sum_congr rfl
  intro index hi
  simp only [weight,if_pos (Finset.mem_range.mp hi)]

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end P2MDyadicModule114

/- Helper module Solutions.RegevBridgeCoherentWideGaussianGates. -/
section P2MDyadicModule115
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QAlgorithms FiniteGateTransport FiniteGateNativeEnumeration

open QAlgorithms.Papers.Independent.Renew46.P12

@[fun_prop] theorem gateWord_poly (a : ℕ) : Poly (gateWord a) := by
  unfold gateWord
  exact Poly.comp (NativeAcceptanceGates.current_poly a)
    (Poly.pair (Poly.comp numericalProbability_poly Poly.fst) Poly.snd)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end P2MDyadicModule115

/- Helper module Solutions.RegevBridgeCoherentWideGaussianProposal. -/
section P2MDyadicModule116

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem proposalTicket_value (input : PointRequest) (tape : Bits (Nat.size (intervalCount input))) :
    QMCNumericRuntime.bitValue (List.ofFn tape)=(proposalTicket input tape).val :=
  Integration9_9.LARCoinMachine.bitValue_boundedBoolTicket _ _

theorem coinAmplitude_sqrt (bits : ℕ) :
    coinAmplitude bits=((Real.sqrt ((2 : ℝ)^bits))⁻¹ : ℝ) := by
  have hs : Real.sqrt ((2 : ℝ)^bits)=(Real.sqrt 2)^bits := by
    induction bits with
    | zero => simp
    | succ bits ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  simp only [coinAmplitude,hs,inv_pow,Complex.ofReal_pow,Complex.ofReal_inv]

@[fun_prop] theorem gateWordBits_poly (a : ℕ) : Poly (gateWordBits a) := by
  unfold gateWordBits
  exact Poly.comp (gateWord_poly a)
    (Poly.pair (Poly.pair (by fun_prop)
      (Poly.comp QMCNumericRuntime.bitValue_poly (by fun_prop))) Poly.snd)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end P2MDyadicModule116

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingBuilder. -/
section P2MDyadicModule117

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

open QAlgorithms QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

@[fun_prop] theorem publicHeader_poly : Poly publicHeader := by unfold publicHeader;fun_prop

@[fun_prop] theorem paddedPublic_poly : Poly (fun x : List Unit×Str => paddedPublic x.1 x.2) := by
  unfold paddedPublic
  exact Poly.comp (g:=fun x : List Unit×Str => (publicHeader x.2++x.1.map (fun _ => false),x.1.length))
    QMCNumericRuntime.parser_take_poly (by fun_prop)

@[simp] theorem paddedPublic_length (slots : List Unit) (word : Str) : (paddedPublic slots word).length=slots.length := by
  simp only [paddedPublic,List.length_take,List.length_append,List.length_map]
  omega

@[simp] theorem rawInput_length (slots : List Unit) (word tape : Str) :
    (rawInput slots word tape).length=2*slots.length+1+tape.length := by
  simp only [rawInput,List.length_append,paddedPublic_length,lengthToken,List.length_map,List.length_singleton]
  omega

@[fun_prop] theorem parsePublic_poly : Poly parsePublic := by
  have hu : Poly (fun word : Str => (readUnary word).2) := Poly.comp Poly.snd readUnary_poly
  have hb : Poly (fun word : Str => (readUnary (readUnary word).2).2) :=
    Poly.comp (f:=fun xs : Str => (readUnary xs).2) (g:=fun word : Str => (readUnary word).2) hu hu
  have hn : Poly (fun word : Str => (unarySlots word).length) := Poly.comp Poly.list_length unarySlots_poly
  have hn' : Poly (fun word : Str => (unarySlots (readUnary word).2).length) :=
    Poly.comp (f:=fun xs : Str => (unarySlots xs).length) (g:=fun word : Str => (readUnary word).2) hn hu
  have ht := Poly.comp QMCNumericRuntime.parser_take_poly (Poly.pair hb hn')
  have hd := Poly.comp QMCNumericRuntime.parser_drop_poly (Poly.pair hu hn)
  exact Poly.pair ht hd

variable (request : Str→PointRequest×List Unit) (hr : Poly request)

include hr in
@[fun_prop] theorem parse_poly : Poly (parse request) := by
  have hp : Poly (fun word : Str => (parsePublic word).1) := Poly.comp Poly.fst parsePublic_poly
  have ht : Poly (fun word : Str => (parsePublic word).2) := Poly.comp Poly.snd parsePublic_poly
  have hx : Poly (fun word : Str => request (parsePublic word).1) := Poly.comp hr hp
  have hi : Poly (fun word : Str => (request (parsePublic word).1).1) := Poly.comp Poly.fst hx
  have hb : Poly (fun word : Str => (request (parsePublic word).1).2) := Poly.comp Poly.snd hx
  have hk : Poly (fun input : PointRequest => (Nat.bits (intervalCount input)).length) := by fun_prop
  have hf := Poly.comp QMCNumericRuntime.parser_take_poly (Poly.pair ht (Poly.comp hk hi))
  exact Poly.pair (Poly.pair hi hf) hb

include hr in
@[fun_prop] theorem gateWord_poly (a : ℕ) : Poly (gateWord request a) := by
  unfold gateWord
  exact Poly.comp (gateWordBits_poly a) (parse_poly request hr)

noncomputable def wordBound (a : ℕ) : Polynomial ℕ :=
  (gateWord_poly request hr a).program.sizeBound.comp (3*Polynomial.X)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

end P2MDyadicModule117

/- Helper module Solutions.RegevBridgeNativeWordInputEmbedding. -/
section P2MDyadicModule118

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity NativeWordLayout ControlledNativeGates ControlledLetterPlan FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean

open scoped BigOperators

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

theorem initialWork_injective (n : ℕ) (a b : Str) (ha : a.length=n) (hb : b.length=n)
    (he : initialWork words hw p n a=initialWork words hw p n b) : a=b := by
  apply List.ext_getElem
  · omega
  · intro i hi hj
    have hwidth : i < width (P words hw p) n := by unfold width;omega
    have hh := congrFun he ⟨i,hwidth⟩
    change wordExtension a i=wordExtension b i at hh
    simpa only [wordExtension_before a i hi,wordExtension_before b i hj] using hh

variable {I : Type*} [Fintype I] [DecidableEq I]

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule118

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingBuilderPhysical. -/
section P2MDyadicModule119

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeWordCoherent NativeWordLayout ControlledNativeGates FiniteGateNativeEnumeration

open QAlgorithms.Papers.Independent.Renew46.P12

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

theorem encoded_length (slots : List Unit) (word : Str) {K : ℕ} (tape : Bits K) :
    (encoded slots word tape).length=2*slots.length+1+K := by
  simp only [encoded,rawInput_length,List.length_ofFn]

theorem encoded_injective (slots : List Unit) (word : Str) (K : ℕ) :
    Function.Injective (encoded slots word (K:=K)) := by
  intro a b h
  have hh := congrArg (List.drop (lengthToken slots++paddedPublic slots word).length) h
  simp only [encoded,rawInput,List.drop_left] at hh
  exact List.ofFn_inj.mp hh

variable (request : Str→PointRequest×List Unit) (hr : _root_.OAI.MetricKMedian.Binary.Automatic.Poly request)

def physicalCircuit (synthesis interpreter : ℕ) (slots : List Unit) (K : ℕ)
    (interpreterBudget : List Unit) :=
  wholeCircuit (gateWord request synthesis) (gateWord_poly request hr synthesis)
    (wordBound request hr synthesis) (2*slots.length+1+K) interpreter interpreterBudget

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

end

end P2MDyadicModule119

/- Helper module Solutions.RegevBridgeCoherentProductError. -/
section P2MDyadicModule120

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentProjection

open scoped BigOperators

variable {O : Type*} [Fintype O]

noncomputable def repeatState (m : ℕ) (ψ : EuclideanSpace ℂ O) :
    EuclideanSpace ℂ (Fin m → O) := WithLp.toLp 2 (fun x => ∏ i,ψ (x i))

theorem repeatState_normalized (m : ℕ) (ψ : EuclideanSpace ℂ O) (hψ : ‖ψ‖=1) :
    ‖repeatState m ψ‖=1 := by
  have hs : (∑ o,‖ψ o‖^2)=1 := by rw [←EuclideanSpace.norm_sq_eq,hψ];norm_num
  have hh : ‖repeatState m ψ‖^2=1 := by
    simp only [EuclideanSpace.norm_sq_eq,repeatState,norm_prod,←Finset.prod_pow]
    rw [←Fintype.prod_sum (fun (_ : Fin m) (o : O) => ‖ψ o‖^2)]
    simp only [hs,Finset.prod_const_one]
  nlinarith [norm_nonneg (repeatState m ψ)]

theorem repeatState_cons (m : ℕ) (ψ : EuclideanSpace ℂ O) (o : O) (x : Fin m → O) :
    repeatState (m+1) ψ (Fin.cons o x)=tensorState ψ (repeatState m ψ) (o,x) := by
  simp [repeatState,tensorState,Fin.prod_univ_succ]

theorem repeatState_distance_succ (m : ℕ) (ψ φ : EuclideanSpace ℂ O) :
    ‖repeatState (m+1) ψ-repeatState (m+1) φ‖=
      ‖tensorState ψ (repeatState m ψ)-tensorState φ (repeatState m φ)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,PiLp.sub_apply]
  symm
  apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => O))
  intro x
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,repeatState_cons]

theorem tensorState_error {J : Type*} [Fintype J]
    (ψ φ : EuclideanSpace ℂ O) (u v : EuclideanSpace ℂ J) :
    ‖tensorState ψ u-tensorState φ v‖≤‖ψ-φ‖*‖u‖+‖φ‖*‖u-v‖ := by
  have he : tensorState ψ u-tensorState φ v=tensorState (ψ-φ) u+tensorState φ (u-v) := by
    ext x
    simp only [tensorState,PiLp.sub_apply,PiLp.add_apply]
    ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [tensorState_norm,tensorState_norm])

/-- Independent finite pure-state errors add linearly in the number of
trials. This is a complete vector estimate before any reversible selection. -/
theorem repeatState_error (m : ℕ) (ψ φ : EuclideanSpace ℂ O)
    (hψ : ‖ψ‖=1) (hφ : ‖φ‖=1) (ε : ℝ) (herr : ‖ψ-φ‖≤ε) :
    ‖repeatState m ψ-repeatState m φ‖≤(m : ℝ)*ε := by
  induction m with
  | zero => simp [repeatState]
  | succ m ih =>
    rw [repeatState_distance_succ]
    have hh := tensorState_error ψ φ (repeatState m ψ) (repeatState m φ)
    rw [repeatState_normalized m ψ hψ,hφ,mul_one,one_mul] at hh
    have hn : ((m+1 : ℕ) : ℝ)*ε=ε+(m : ℝ)*ε := by push_cast;ring
    rw [hn]
    exact hh.trans (add_le_add herr ih)

end InfoLossLAR.WorstCase.CoherentProjection

end P2MDyadicModule120

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingProposal. -/
section P2MDyadicModule121

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentWeightedPreparation

open scoped BigOperators

section Product

variable {O E : Type*} [Fintype O] [Fintype E] [Nonempty O] [Nonempty E]

theorem weightSum_product (w : O→ℝ) :
    weightSum (fun x : O×E => w x.1)=(Fintype.card E : ℝ)*weightSum w := by
  simp only [weightSum,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem target_product (w : O→ℝ) (x : O×E) :
    target (fun y : O×E => w y.1) x=target w x.1*
      (((Real.sqrt (Fintype.card E : ℝ))⁻¹ : ℝ) : ℂ) := by
  simp only [target,weightSum_product,Real.sqrt_mul (Nat.cast_nonneg (Fintype.card E)),
    div_eq_mul_inv,mul_inv_rev,Complex.ofReal_mul,Complex.ofReal_inv]
  ring

end Product

section Reindex

variable {O E : Type*} [Fintype O] [Fintype E] [Nonempty O] [Nonempty E]

theorem weightSum_equiv (e : O≃E) (w : E→ℝ) : weightSum (fun x => w (e x))=weightSum w := by
  exact Fintype.sum_equiv e _ _ (by intro i;rfl)

theorem target_equiv (e : O≃E) (w : E→ℝ) (x : O) :
    target (fun y => w (e y)) x=target w (e x) := by simp only [target,weightSum_equiv]

end Reindex

/-- All public capacity qubits receive H. Under the exact register split,
the inactive suffix is a retained positive uniform tensor factor. -/
def ticketEquiv (input : PointRequest) (extra : ℕ) :
    Bits (Nat.size (intervalCount input)+extra)≃Ticket input×Bits extra :=
  (qubitsAppendEquiv _ extra).trans (Equiv.prodCongr (proposalTicket input) (Equiv.refl _))

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

end

end P2MDyadicModule121

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingPreparation. -/
section P2MDyadicModule122

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Preparation

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentWeightedPreparation

open CoherentComputeUncompute ControlledNativeGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

/-- The original binary B/control word is retained in this fixed-capacity
self-delimited prefix, and the actual native request builder reads it. -/
def builderHeader (slots : List Unit) (word : Str) : Str :=
  lengthToken slots++Builder.paddedPublic slots word

@[fun_prop] theorem builderHeader_poly : Poly (fun x : List Unit×Str => builderHeader x.1 x.2) := by
  unfold builderHeader
  fun_prop

@[simp] theorem builderHeader_length (slots : List Unit) (word : Str) :
    (builderHeader slots word).length=2*slots.length+1 := by
  simp only [builderHeader,List.length_append,lengthToken,List.length_map,List.length_singleton,
    Builder.paddedPublic_length]
  omega

/-- The native emitter reads only supplied public unary capacities. -/
def ticketPositions (x : List Unit×List Unit) : List ℕ :=
  (List.range x.2.length).map (fun i => 2*x.1.length+1+i)

@[fun_prop] theorem ticketPositions_poly : Poly ticketPositions := by
  unfold ticketPositions
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (f:=fun slots : List Unit => List.range slots.length) (g:=fun x : List Unit×List Unit => x.2)
      Poly.list_indices Poly.snd

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Preparation

end

end P2MDyadicModule122

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingCapacity. -/
section P2MDyadicModule123

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentWeightedPreparation

open scoped BigOperators

/-- A value-preserving relabeling of equal-size binary registers. -/
def bitsCast {m n : ℕ} (h : m=n) : Bits m≃Bits n where
  toFun tape i := tape ⟨i.val,by omega⟩
  invFun tape i := tape ⟨i.val,by omega⟩
  left_inv tape := by funext i;rfl
  right_inv tape := by funext i;rfl

def capacityTicketEquiv (input : PointRequest) (K : ℕ)
    (hK : Nat.size (intervalCount input)≤K) : Bits K≃Ticket input×Bits (K-Nat.size (intervalCount input)) :=
  (bitsCast (show K=Nat.size (intervalCount input)+(K-Nat.size (intervalCount input)) by omega)).trans
    (ticketEquiv input (K-Nat.size (intervalCount input)))

@[simp] theorem capacityTicketEquiv_first (input : PointRequest) (K : ℕ)
    (hK : Nat.size (intervalCount input)≤K) (tape : Bits K) :
    (capacityTicketEquiv input K hK tape).1=activeTicket input hK tape := rfl

theorem capacityWeight_eq (input : PointRequest) (s : ℝ) (K : ℕ)
    (hK : Nat.size (intervalCount input)≤K) :
    capacityWeight input s K hK=(fun tape =>
      (fun x : Ticket input×Bits (K-Nat.size (intervalCount input)) => weight input s x.1.val)
        (capacityTicketEquiv input K hK tape)) := rfl

/-- The exact successful pure state factors into the original Gaussian
weighted target and one untouched positive uniform suffix, with all phases. -/
theorem capacity_target_tensor (input : PointRequest) (s : ℝ) (K : ℕ)
    (hK : Nat.size (intervalCount input)≤K) (tape : Bits K) :
    target (capacityWeight input s K hK) tape=
      target (fun t : Ticket input => weight input s t.val) (activeTicket input hK tape)*
        coinAmplitude (K-Nat.size (intervalCount input)) := by
  rw [capacityWeight_eq,target_equiv (capacityTicketEquiv input K hK)
    (fun x : Ticket input×Bits (K-Nat.size (intervalCount input)) => weight input s x.1.val) tape,
    target_product (E:=Bits (K-Nat.size (intervalCount input)))
      (fun t : Ticket input => weight input s t.val) (capacityTicketEquiv input K hK tape),coinAmplitude_sqrt]
  simp only [capacityTicketEquiv_first,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

end

end P2MDyadicModule123

/- Helper module Solutions.RegevBridgeCoherentControlledSwap. -/
section P2MDyadicModule124

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity ControlledLetterPlan

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- The literal 39-entry finite-data generator uses the established native
Toffoli word and requires no numerical phase approximation. -/
def codes (x : ℕ×ℕ×ℕ) : List GateCode :=
  [(4,x.2.2,x.2.1)]++(ControlledPlanNative.cnotPlan x.1 x.2.1 x.2.2).map Prod.fst++
    [(4,x.2.2,x.2.1)]

@[fun_prop] theorem codes_poly : Poly codes := by
  unfold codes
  fun_prop

theorem codes_encode {n : ℕ} (c i j : Fin n) (hci : c≠i) (hcj : c≠j) (hij : i≠j) :
    codes (c.val,i.val,j.val)=(gates c i j hci hcj hij).map encodeInstr := rfl

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule124

/- Helper module Solutions.RegevBridgeCoherentRegisterSwap. -/
section P2MDyadicModule125

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b n : ℕ}

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- An ordinary finite-data generator visits only the supplied bit pairs. -/
def blockCodes (x : ℕ×List (ℕ×ℕ)) : List GateCode :=
  x.2.flatMap (fun p => codes (x.1,p))

@[fun_prop] theorem blockCodes_poly : Poly blockCodes := by
  unfold blockCodes
  apply Poly.list_flatMap
  · exact Poly.comp codes_poly (by fun_prop)
  · exact Poly.snd

theorem blockCodes_encode (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (hc : ∀ p,c≠w p) (slots : List (Fin b)) :
    blockCodes (c.val,slots.map (fun i => ((w (i,false)).val,(w (i,true)).val)))=
      (blockGates w c hc slots).map encodeInstr := by
  unfold blockCodes blockGates pairGates
  rw [List.flatMap_map,List.map_flatMap]
  apply congrArg (fun f : Fin b → List GateCode => slots.flatMap f)
  funext i
  exact codes_encode c _ _ (hc _) (hc _) _

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule125

/- Helper module Solutions.RegevBridgeCoherentSelectionCircuit. -/
section P2MDyadicModule126

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b m n : ℕ}

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def selectionCodes (x : List (ℕ×List (ℕ×ℕ))) : List GateCode := x.flatMap blockCodes

@[fun_prop] theorem selectionCodes_poly : Poly selectionCodes := by
  unfold selectionCodes
  exact Poly.list_flatMap (Poly.comp blockCodes_poly Poly.snd) (by fun_prop)

theorem selectionCodes_encode (w : Fin m → (Fin b×Bool) ↪ Fin n) (c : Fin m → Fin n)
    (hc : ∀ i j p,c i≠w j p) (slots : List (Fin m)) :
    selectionCodes (slots.map (fun i => ((c i).val,(List.finRange b).map
      (fun j => ((w i (j,false)).val,(w i (j,true)).val)))))=
      (selectionGates w c hc slots).map encodeInstr := by
  unfold selectionCodes selectionGates
  rw [List.flatMap_map,List.map_flatMap]
  apply congrArg (fun f : Fin m → List GateCode => slots.flatMap f)
  funext i
  exact blockCodes_encode _ _ _ _

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule126

/- Helper module Solutions.RegevBridgeCoherentSelectionLayout. -/
section P2MDyadicModule127

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b m W : ℕ}

theorem work_outside (work : Fin W) (chosen : Fin m) :
    work.castAdd ((m+1)*b)∉Set.range (candidateFullPairs (W:=W) (b:=b) chosen) := by
  rintro ⟨p,h⟩
  have he := congrArg Fin.val h
  change W+(candidatePairs chosen p).val=work.val at he
  omega

theorem controls_fresh (controls : Fin m → Fin W) :
    ∀ i j p,(controls i).castAdd ((m+1)*b)≠candidateFullPairs (W:=W) (b:=b) j p := by
  intro i j p h
  exact work_outside (controls i) j ⟨p,h.symm⟩

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule127

/- Helper module Solutions.RegevBridgeCoherentParallelTrials. -/
section P2MDyadicModule128

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentParallelTrials

open QAlgorithms QAlgorithms.Complexity

open scoped BigOperators

@[simp] theorem width_eq (n m : ℕ) : width n m=m*n := by
  induction m with
  | zero => simp [width]
  | succ m ih => simp only [width,ih,Nat.succ_mul];omega

def initial {n : ℕ} (ψ : QState n) : (m : ℕ) → QState (width n m)
  | 0 => fun _ => 1
  | m+1 => tensorState ψ (initial ψ m)

def coordinates (n : ℕ) : (m : ℕ) → Bits (width n m) ≃ (Fin m → Bits n)
  | 0 => by
    change Bits 0 ≃ (Fin 0 → Bits n)
    exact Equiv.ofUnique _ _
  | m+1 => (qubitsAppendEquiv n (width n m)).trans
      ((Equiv.prodCongr (Equiv.refl (Bits n)) (coordinates n m)).trans
        (Fin.consEquiv (fun _ : Fin (m+1) => Bits n)))

/-- The actual disjoint-register circuit prepares the full tensor product
of trial amplitudes. This is stronger than independence of measured flags. -/
theorem circuit_product {n : ℕ} (trial : Layered n) (ψ : QState n) (m : ℕ)
    (x : Bits (width n m)) :
    runLayered (circuit trial m) (initial ψ m) x=
      ∏ i : Fin m,runLayered trial ψ (coordinates n m x i) := by
  induction m with
  | zero => simp [circuit,initial,runLayered]
  | succ m ih =>
    change runLayered (leftCircuit trial++rightCircuit (circuit trial m))
      (tensorState ψ (initial ψ m)) x=_
    rw [disjointCircuits_tensor,Fin.prod_univ_succ]
    change runLayered trial ψ (leftRegister x)*
      runLayered (circuit trial m) (initial ψ m) (rightRegister x)=_
    rw [ih]
    rfl

theorem initial_product {n : ℕ} (ψ : QState n) (m : ℕ) (x : Bits (width n m)) :
    initial ψ m x=∏ i : Fin m,ψ (coordinates n m x i) := by
  have hc : circuit ([] : Layered n) m=[] := by
    clear x
    induction m with
    | zero => rfl
    | succ m ih => simp [circuit,ih,leftCircuit,rightCircuit]
  have h := circuit_product ([] : Layered n) ψ m x
  simpa only [hc,runLayered,List.foldl_nil] using h

end InfoLossLAR.WorstCase.CoherentParallelTrials

end P2MDyadicModule128

/- Helper module Solutions.RegevBridgeCoherentTrialPlacement. -/
section P2MDyadicModule129

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms QAlgorithms.Complexity CoherentControlledSwap NativeWordLayout

theorem trialPlacement_output (b m k : ℕ) (i : Fin m) (j : Fin b) :
    trialPlacement b m k (i,(j.castAdd 1).castAdd k)=
      (Fin.natAdd (width P m) (rowWire i.succ j)).castAdd (m*k) := by simp [trialPlacement,trialPositions,trialLocation,wholePositionEquiv]

theorem trialPlacement_flag (b m k : ℕ) (i : Fin m) :
    trialPlacement b m k (i,(Fin.natAdd b (0 : Fin 1)).castAdd k)=
      ((flagPosition i).castAdd ((m+1)*b)).castAdd (m*k) := by simp [trialPlacement,trialPositions,trialLocation,wholePositionEquiv]

theorem trialPlacement_junk (b m k : ℕ) (i : Fin m) (j : Fin k) :
    trialPlacement b m k (i,Fin.natAdd (b+1) j)=
      Fin.natAdd (width P m+(m+1)*b) (finProdFinEquiv (i,j)) := by simp [trialPlacement,trialPositions,trialLocation,wholePositionEquiv]

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule129

/- Helper module Solutions.RegevBridgeCoherentParallelPlacement. -/
section P2MDyadicModule130

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport CoherentProjection

open NativeWordLayout

open scoped BigOperators

@[simp] theorem allTrialWires_at (b m k : ℕ) (i : Fin m) (j : Fin (b+1+k)) :
    allTrialWires b m k (CoherentParallelTrials.flatWire (b+1+k) m (i,j))=
      trialPlacement b m k (i,j) := by
  simp [allTrialWires]

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule130

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingTrial. -/
section P2MDyadicModule131

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Trial

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent NativeWordLayout

open QAlgorithms.Papers.Independent.Renew46.P12

open CoherentWeightedPreparation CoherentComputeUncompute ControlledNativeGates CoherentRejection

open scoped BigOperators

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable (request : Str→PointRequest×List Unit) (hr : Poly request)

abbrev workSize (a : ℕ) (slots : List Unit) (K : ℕ) : ℕ :=
  width (P (gateWord request a) (gateWord_poly request hr a) (wordBound request hr a)) (2*slots.length+1+K)

def workTicket (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (tape : Bits K) :
    Bits (workSize request hr a slots K) :=
  NativeWordCoherent.initialWork (gateWord request a) (gateWord_poly request hr a)
    (wordBound request hr a) (2*slots.length+1+K) (encoded slots word tape)

def workEmbedding (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    Bits K↪Bits (workSize request hr a slots K) where
  toFun := workTicket request hr a slots word K
  inj' := by
    intro i j h
    apply encoded_injective slots word K
    exact initialWork_injective (gateWord request a) (gateWord_poly request hr a) (wordBound request hr a)
      _ _ _ (encoded_length slots word i) (encoded_length slots word j) h

def error (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) : ℝ :=
  180*(((wordBound request hr a).eval (2*slots.length+1+K) : ℕ) : ℝ)/((budget.length : ℝ)+1)+
    (5/(((request word).2.length : ℝ)+1)+2*Real.sqrt (1/(2 : ℝ)^((request word).1.2.2.length)))

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Trial

end

end P2MDyadicModule131

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingPure. -/
section P2MDyadicModule132

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Trial

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentWeightedPreparation CoherentComputeUncompute CoherentRejection

open scoped BigOperators

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable (request : Str→PointRequest×List Unit) (hr : Poly request)

def embeddedTarget (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (s : ℝ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K) :
    EuclideanSpace ℂ (Bits (workSize request hr a slots K)) :=
  WithLp.toLp 2 (CoherentEmbeddedWeightedTrial.target (workEmbedding request hr a slots word K)
    (capacityWeight (request word).1 s K hK))

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Trial

end

end P2MDyadicModule132

/- Helper module Solutions.RegevBridgeCoherentFirstSuccessEmitter. -/
section P2MDyadicModule133

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity NativeWordLayout CoherentControlledSwap ControlledNativeCode

open TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Both public dimensions are unary lists. No hidden success flag is read
by this generator: the computed physical wires control the emitted swaps. -/
abbrev Request := List Unit × List Unit

def publicWord (x : Request) : Str := x.1.map (fun _ => true)

@[fun_prop] theorem publicWord_poly : Poly publicWord := by unfold publicWord; fun_prop

theorem publicWord_eq (x : Request) : publicWord x=unary x.1.length := by
  simp [publicWord,unary]

def publicPairs (x : Request) (j : ℕ) : List (ℕ×ℕ) :=
  (List.range x.2.length).map (fun i =>
    (machineWidth P (publicWord x)+i,machineWidth P (publicWord x)+(j+1)*x.2.length+i))

@[fun_prop] theorem publicPairs_poly : Poly (fun z : Request×ℕ => publicPairs z.1 z.2) := by
  unfold publicPairs
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (f:=fun xs : List Unit => List.range xs.length)
      (g:=fun z : Request×ℕ => z.1.2) Poly.list_indices (by fun_prop)

def publicControls (x : Request) : List (ℕ×List (ℕ×ℕ)) :=
  (List.range x.1.length).map (fun j =>
    (generatedProgramOutputAddress P (publicWord x) j,publicPairs x j))

@[fun_prop] theorem publicControls_poly : Poly publicControls := by
  unfold publicControls
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (f:=fun xs : List Unit => List.range xs.length)
      (g:=fun z : Request => z.1) Poly.list_indices (by fun_prop)

def middleCodes (x : Request) : List GateCode := selectionCodes (publicControls x)

@[fun_prop] theorem middleCodes_poly : Poly middleCodes := by
  unfold middleCodes
  exact Poly.comp selectionCodes_poly publicControls_poly

private theorem range_eq_finRange (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  simp

theorem publicPairs_eq (x : Request) (j : Fin x.1.length) :
    publicPairs x j.val=(List.finRange x.2.length).map (fun i =>
      ((candidateFullPairs (W:=width P x.1.length) j (i,false)).val,
       (candidateFullPairs (W:=width P x.1.length) j (i,true)).val)) := by
  unfold publicPairs
  rw [publicWord_eq,machineWidth_eq,range_eq_finRange,List.map_map]
  apply List.map_congr_left
  intro i _
  simp [candidateFullPairs,appendPairs,candidatePairs,rowWire,finProdFinEquiv,Nat.add_assoc,Nat.add_comm,Nat.mul_comm]

theorem publicControls_eq (x : Request) :
    publicControls x=(List.finRange x.1.length).map (fun j =>
      ((controlWire j).val,(List.finRange x.2.length).map (fun i =>
        ((candidateFullPairs (W:=width P x.1.length) j (i,false)).val,
         (candidateFullPairs (W:=width P x.1.length) j (i,true)).val)))) := by
  unfold publicControls
  rw [range_eq_finRange,List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [publicPairs_eq,publicWord_eq]
  have he := generatedProgramOutputAddress_eq P x.1.length (controlIndex j)
  change generatedProgramOutputAddress P (unary x.1.length) j.val=(controlWire j).val at he
  rw [he]

/-- Exact syntax of the generated finite gates, with no real-valued oracle
or branch-dependent circuit choice. -/
theorem middleCodes_encode (x : Request) :
    middleCodes x=(middle x.2.length x.1.length).map encodeInstr := by
  unfold middleCodes
  rw [publicControls_eq]
  simpa only [middle,Fin.val_castAdd] using selectionCodes_encode
    (candidateFullPairs (W:=width P x.1.length) (b:=x.2.length))
    (fun j => (controlWire j).castAdd ((x.1.length+1)*x.2.length))
    (controls_fresh controlWire) (List.finRange x.1.length)

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule133

/- Helper module Solutions.RegevBridgeCoherentFirstSuccessDescription. -/
section P2MDyadicModule134

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity NativeWordLayout NativeWordCoherent NativeWordDescription

open TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

attribute [local irreducible] CoherentRejection.controlsProgram baseCircuit

def dataSlots (x : Request) : List Unit := (x.1++[()]).flatMap (fun _ => x.2)

@[fun_prop] theorem dataSlots_poly : Poly dataSlots := by unfold dataSlots; fun_prop

@[simp] theorem dataSlots_length (x : Request) : (dataSlots x).length=(x.1.length+1)*x.2.length := by
  simp [dataSlots,List.length_flatMap,Nat.mul_comm]
  ring

def allSlots (x : Request) : List Unit := totalSlots P (publicWord x)++dataSlots x

@[fun_prop] theorem allSlots_poly : Poly allSlots := by unfold allSlots; fun_prop

theorem allSlots_bound (x : Request) : width P x.1.length+(x.1.length+1)*x.2.length≤(allSlots x).length := by
  have h := totalSlots_bound P x.1.length
  simp only [allSlots,List.length_append,dataSlots_length,publicWord_eq]
  omega

def middleWords (x : Request) : List Str := (middleCodes x).map (gateWord (allSlots x))

@[fun_prop] theorem middleWords_poly : Poly middleWords := by unfold middleWords; fun_prop

theorem middleWords_code (x : Request) :
    middleWords x=(middle x.2.length x.1.length).map encInstr := by
  simp only [middleWords,middleCodes_encode,List.map_map]
  apply List.map_congr_left
  intro gate _
  exact gateWord_encode _ gate (allSlots_bound x)

def publicLayers (x : Request) : List (List Str) :=
  forwardWords P (publicWord x)++(middleWords x).map (fun g => [g])++
    inverseCircuitWords (forwardWords P (publicWord x))

attribute [local irreducible] forwardWords middleWords inverseCircuitWords

theorem publicLayers_poly : Poly publicLayers := by
  unfold publicLayers
  have hf : Poly (fun x : Request => forwardWords P (publicWord x)) :=
    Poly.comp (forwardWords_poly P) publicWord_poly
  have hm : Poly (fun x : Request => (middleWords x).map (fun g => [g])) := by
    apply Poly.list_map
    · fun_prop
    · exact middleWords_poly
  have hi := Poly.comp inverseCircuitWords_poly hf
  exact Poly.comp Poly.list_append (Poly.pair (Poly.comp Poly.list_append (Poly.pair hf hm)) hi)

theorem publicLayers_code (x : Request) :
    publicLayers x=(wholeCircuit x.2.length x.1.length).map (List.map encInstr) := by
  unfold publicLayers wholeCircuit
  rw [publicWord_eq,forwardWords_code,middleWords_code,inverseCircuitWords_correct]
  simp only [List.map_append,extendCircuit_code,baseCircuit,List.map_map,
    Function.comp_def,List.map_cons,List.map_nil]

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule134

/- Helper module Solutions.RegevBridgeCoherentParallelLayoutNative. -/
section P2MDyadicModule135

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms QAlgorithms.Complexity NativeWordLayout

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean.PolyProgramCircuit

abbrev PlacementRequest := Request×List Unit

def trialTicks (x : PlacementRequest) : List Unit := x.1.2++[()]++x.2

@[fun_prop] theorem trialTicks_poly : Poly trialTicks := by unfold trialTicks;fun_prop

@[simp] theorem trialTicks_length (x : PlacementRequest) : (trialTicks x).length=x.1.2.length+1+x.2.length := by simp [trialTicks];omega

def parallelTicks (x : PlacementRequest) : List Unit := x.1.1.flatMap (fun _ => trialTicks x)

@[fun_prop] theorem parallelTicks_poly : Poly parallelTicks := by unfold parallelTicks;fun_prop

@[simp] theorem parallelTicks_length (x : PlacementRequest) :
    (parallelTicks x).length=x.1.1.length*(x.1.2.length+1+x.2.length) := by
  simp [parallelTicks,List.length_flatMap,Nat.mul_comm]

def positionAddress (x : PlacementRequest) (ij : ℕ×ℕ) : ℕ :=
  let W := machineWidth P (publicWord x.1)
  if ij.2<x.1.2.length then W+(ij.1+1)*x.1.2.length+ij.2
  else if ij.2=x.1.2.length then ij.1
  else W+(x.1.1.length+1)*x.1.2.length+ij.1*x.2.length+(ij.2-(x.1.2.length+1))

@[fun_prop] theorem positionAddress_poly : Poly (fun x : PlacementRequest×(ℕ×ℕ) => positionAddress x.1 x.2) := by
  unfold positionAddress
  fun_prop

/-- Exact native addresses: row i+1, the actual original machine flag wire,
or the complete i-th spectator block. -/
theorem positionAddress_exact (x : PlacementRequest) (i : Fin x.1.1.length)
    (j : Fin (x.1.2.length+1+x.2.length)) :
    positionAddress x (i.val,j.val)=(trialPlacement x.1.2.length x.1.1.length x.2.length (i,j)).val := by
  refine Fin.addCases ?_ ?_ j
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro l
      rw [trialPlacement_output]
      simp only [positionAddress,Fin.val_castAdd,publicWord_eq,machineWidth_eq,if_pos l.isLt,
        Fin.val_natAdd,CoherentControlledSwap.rowWire,finProdFinEquiv]
      change width P x.1.1.length+(i.val+1)*x.1.2.length+l.val=
        width P x.1.1.length+(l.val+x.1.2.length*(i.val+1))
      ring
    · intro l
      have he : l=(0 : Fin 1) := Subsingleton.elim _ _
      subst l
      rw [trialPlacement_flag]
      simp [positionAddress,flagPosition]
  · intro l
    rw [trialPlacement_junk]
    have hn : ¬ x.1.2.length+1+l.val<x.1.2.length := by omega
    have he : ¬ x.1.2.length+1+l.val=x.1.2.length := by omega
    simp only [positionAddress,Fin.val_natAdd,publicWord_eq,machineWidth_eq,if_neg hn,if_neg he,
      finProdFinEquiv,Fin.coe_cast]
    change width P x.1.1.length+(x.1.1.length+1)*x.1.2.length+i.val*x.2.length+
        (x.1.2.length+1+l.val-(x.1.2.length+1))=
      width P x.1.1.length+(x.1.1.length+1)*x.1.2.length+(l.val+x.2.length*i.val)
    simp only [Nat.add_sub_cancel_left]
    ring

def wireAddress (x : PlacementRequest×ℕ) : ℕ :=
  positionAddress x.1 (x.2/(trialTicks x.1).length,x.2%(trialTicks x.1).length)

@[fun_prop] theorem wireAddress_poly : Poly wireAddress := by unfold wireAddress;fun_prop

def publicLayout (x : PlacementRequest) : List ℕ :=
  (List.range (parallelTicks x).length).map (fun i => wireAddress (x,i))

@[fun_prop] theorem publicLayout_poly : Poly publicLayout := by
  unfold publicLayout
  apply Poly.list_map
  · exact Poly.comp wireAddress_poly (by fun_prop)
  · exact Poly.comp (f:=fun slots : List Unit => List.range slots.length) (g:=parallelTicks)
      Poly.list_indices parallelTicks_poly

/-- Every generated entry is the actual physical wire injection. In
particular no malformed address is silently discarded by a decoder. -/
theorem publicLayout_exact (x : PlacementRequest) :
    publicLayout x=List.ofFn (fun j =>
      (allTrialWires x.1.2.length x.1.1.length x.2.length j).val) := by
  apply List.ext_getElem
  · simp [publicLayout,CoherentParallelTrials.width_eq]
  · intro index hleft hright
    have hi : index<CoherentParallelTrials.width (x.1.2.length+1+x.2.length) x.1.1.length := by
      simpa only [List.length_ofFn] using hright
    let q := (CoherentParallelTrials.flatWire (x.1.2.length+1+x.2.length) x.1.1.length).symm ⟨index,hi⟩
    have hq : CoherentParallelTrials.flatWire (x.1.2.length+1+x.2.length) x.1.1.length q=⟨index,hi⟩ :=
      Equiv.apply_symm_apply _ _
    have hv : q.1.val*(x.1.2.length+1+x.2.length)+q.2.val=index := by
      have h := congrArg Fin.val hq
      change q.2.val+(x.1.2.length+1+x.2.length)*q.1.val=index at h
      calc q.1.val*(x.1.2.length+1+x.2.length)+q.2.val
          =q.2.val+(x.1.2.length+1+x.2.length)*q.1.val := by ring
        _=index := h
    have hT : 0<x.1.2.length+1+x.2.length := by omega
    have hd : index/(x.1.2.length+1+x.2.length)=q.1.val := by
      rw [←hv,Nat.mul_comm q.1.val _,Nat.mul_add_div hT,Nat.div_eq_of_lt q.2.isLt,Nat.add_zero]
    have hm : index%(x.1.2.length+1+x.2.length)=q.2.val := by
      rw [←hv,Nat.mul_add_mod_of_lt q.2.isLt]
    simp only [publicLayout,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      wireAddress,trialTicks_length,hd,hm]
    rw [positionAddress_exact]
    have hh := congrArg (fun j => (allTrialWires x.1.2.length x.1.1.length x.2.length j).val) hq
    rw [allTrialWires_at] at hh
    exact hh

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule135

/- Helper module Solutions.AdvantageBridgeBundleEmitter. -/
section P2MDyadicModule136

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem unaryPayload_poly : Poly unaryPayload := by
  unfold unaryPayload
  exact Poly.comp parser_take_poly (Poly.pair Poly.identity inputWidth_poly)

@[fun_prop] theorem shiftInstructionWord_poly : Poly (fun input : Str × Str => shiftInstructionWord input.1 input.2) := by
  unfold shiftInstructionWord
  fun_prop

/-- The emitter offsets exactly the actual right-embedded platform gate. -/
theorem shiftInstructionWord_encInstr {n : ℕ} (prior : Str) (gate : Instr n) :
    shiftInstructionWord prior (encInstr gate)=encInstr (rightInstruction (n := prior.length) gate) := by
  cases gate <;>
    simp only [encInstr,List.append_assoc,shiftInstructionWord,readUnary_append,emitter_width_append,
      unaryPayload_encNat,unaryPayload_number,lengthToken_eq,List.length_append,unary,List.length_replicate,
      rightInstruction,Fin.val_natAdd] <;> norm_num <;> rfl

@[fun_prop] theorem shiftCircuitWords_poly :
    Poly (fun input : Str × List (List Str) => shiftCircuitWords input.1 input.2) := by
  have hg : Poly (fun x : ((Str × List (List Str)) × List Str) × Str =>
      shiftInstructionWord x.1.1.1 x.2) :=
    Poly.comp (f := fun p : Str × Str => shiftInstructionWord p.1 p.2)
      (g := fun x : ((Str × List (List Str)) × List Str) × Str => (x.1.1.1,x.2))
      shiftInstructionWord_poly (by fun_prop)
  have hl : Poly (fun x : (Str × List (List Str)) × List Str =>
      x.2.map (shiftInstructionWord x.1.1)) := Poly.list_map hg Poly.snd
  unfold shiftCircuitWords
  exact Poly.list_map hl Poly.snd

theorem shiftCircuitWords_correct {n : ℕ} (prior : Str) (circuit : Layered n) :
    shiftCircuitWords prior (circuit.map (List.map encInstr))=
      (rightCircuit (n := prior.length) circuit).map (List.map encInstr) := by
  simp only [shiftCircuitWords,rightCircuit,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  exact shiftInstructionWord_encInstr prior gate

@[fun_prop] theorem precedingWireSlots_poly : Poly precedingWireSlots := by
  unfold precedingWireSlots
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.comp parser_take_poly Poly.identity

@[fun_prop] theorem bundleCircuitWordLayers_poly : Poly bundleCircuitWordLayers := by
  unfold bundleCircuitWordLayers
  apply Poly.list_flatMap
  · exact Poly.comp shiftCircuitWords_poly
      (Poly.pair precedingWireSlots_poly (by fun_prop))
  · exact Poly.list_indices

private theorem emitter_read_number (number : ℕ) : readUnary (encNat number)=(encNat number,[]) := by
  simpa only [List.append_nil] using readUnary_append number []

theorem shiftInstructionWord_spec (prior xs : Str) :
    shiftInstructionWord prior xs=
      encNat (inputWidth xs)++encNat (prior.length+inputWidth (readUnary xs).2)++
        (if inputWidth xs=4 then
          encNat (prior.length+inputWidth (readUnary (readUnary xs).2).2) else []) := by
  unfold shiftInstructionWord
  simp only [lengthToken_eq,List.length_append,unaryPayload_length]
  split_ifs <;> simp

theorem shiftInstructionWord_canonical (prior : Str) (tag first second : ℕ) :
    shiftInstructionWord prior (encNat tag++encNat first++(if tag=4 then encNat second else []))=
      encNat tag++encNat (prior.length+first)++(if tag=4 then encNat (prior.length+second) else []) := by
  rw [shiftInstructionWord_spec]
  by_cases h : tag=4 <;>
    simp [h,List.append_assoc,readUnary_append,emitter_width_append,emitter_width_number,emitter_read_number]

/-- Offset composition is exact even on malformed original gate words,
because every shifted word is canonically unary-framed. -/
theorem shiftInstructionWord_comp (first second xs : Str) :
    shiftInstructionWord first (shiftInstructionWord second xs)=shiftInstructionWord (first++second) xs := by
  rw [shiftInstructionWord_spec second xs,shiftInstructionWord_canonical,shiftInstructionWord_spec]
  simp only [List.length_append,Nat.add_assoc]

theorem shiftCircuitWords_comp (first second : Str) (layers : List (List Str)) :
    shiftCircuitWords first (shiftCircuitWords second layers)=shiftCircuitWords (first++second) layers := by
  simp only [shiftCircuitWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro word _
  exact shiftInstructionWord_comp first second word

theorem shiftCircuitWords_flatMap {α : Type*} (prior : Str) (values : List α) (layers : α → List (List Str)) :
    shiftCircuitWords prior (values.flatMap layers)=values.flatMap (fun value => shiftCircuitWords prior (layers value)) := by
  simp only [shiftCircuitWords,List.map_flatMap]

theorem shiftCircuitWords_zero {n : ℕ} (circuit : Layered n) :
    shiftCircuitWords [] (circuit.map (List.map encInstr))=circuit.map (List.map encInstr) := by
  simp only [shiftCircuitWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  rw [shiftInstructionWord_encInstr]
  cases gate <;> simp [rightInstruction,encInstr]

/-- The polynomial indexed emitter has exactly the recursive physical
head/offset-tail composition, with a canonicalized head layer description. -/
theorem bundleCircuitWordLayers_cons (frame : PhysicalFrameWords) (frames : List PhysicalFrameWords) :
    bundleCircuitWordLayers (frame::frames)=
      shiftCircuitWords [] frame.2.2++shiftCircuitWords frame.1 (bundleCircuitWordLayers frames) := by
  unfold bundleCircuitWordLayers
  simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
    List.getElem?_cons_zero,Option.getD_some,precedingWireSlots,List.take_zero,List.flatMap_nil]
  rw [shiftCircuitWords_flatMap]
  apply congrArg (fun tail => shiftCircuitWords [] frame.2.2++tail)
  apply List.flatMap_congr
  intro index _
  simp only [List.getElem?_cons_succ,precedingWireSlots,List.take_succ_cons,List.flatMap_cons]
  exact (shiftCircuitWords_comp frame.1 _ _).symm

end InfoLossLAR.WorstCase

end P2MDyadicModule136

/- Helper module Solutions.RegevBridgeCoherentParallelInitialNative. -/
section P2MDyadicModule137

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative.InitialNative

open QAlgorithms QAlgorithms.Complexity CoherentControlledSwap NativeWordLayout

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit

abbrev Input := PlacementRequest×Str

def row (x : Input) : Str := (x.2++x.1.1.2.map (fun _ => false)).take x.1.1.2.length

@[fun_prop] theorem row_poly : Poly row := by
  unfold row
  exact Poly.comp (g:=fun x : Input => (x.2++x.1.1.2.map (fun _ => false),x.1.1.2.length))
    QMCNumericRuntime.parser_take_poly (by fun_prop)

theorem row_exact (x : PlacementRequest) (v : Bits x.1.2.length) : row (x,List.ofFn v)=List.ofFn v := by
  unfold row
  simpa only [List.length_ofFn] using
    (show (List.ofFn v++x.1.2.map (fun _ => false)).take (List.ofFn v).length=List.ofFn v from List.take_left)

def machineZeros (x : PlacementRequest) : Str :=
  ((allSlots x.1).map (fun _ => false)).take (machineWidth P (publicWord x.1))

@[fun_prop] theorem machineZeros_poly : Poly machineZeros := by
  unfold machineZeros
  exact Poly.comp (g:=fun x : PlacementRequest =>
    ((allSlots x.1).map (fun _ => false),machineWidth P (publicWord x.1)))
    QMCNumericRuntime.parser_take_poly (by fun_prop)

theorem machineZeros_exact (x : PlacementRequest) :
    machineZeros x=List.replicate (width P x.1.1.length) false := by
  unfold machineZeros
  rw [publicWord_eq,machineWidth_eq,List.map_const',List.take_replicate]
  have hb:=allSlots_bound x.1
  rw [Nat.min_eq_left (by omega)]

def format (x : Input) : Str :=
  machineZeros x.1++x.1.1.2.map (fun _ => false)++
    x.1.1.1.flatMap (fun _ => row x)++
    (x.1.1.1.flatMap (fun _ => x.1.2)).map (fun _ => false)

@[fun_prop] theorem format_poly : Poly format := by unfold format;fun_prop

private theorem repeat_flatMap (xs : List Unit) (bits : Str) :
    xs.flatMap (fun _ => bits)=(List.replicate xs.length bits).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.length_cons,List.replicate_succ,List.flatten_cons,ih]

theorem format_exact (x : PlacementRequest) (v : Bits x.1.2.length) :
    format (x,List.ofFn v)=
      List.replicate (width P x.1.1.length) false++List.replicate x.1.2.length false++
      (List.replicate x.1.1.length (List.ofFn v)).flatten++
      List.replicate (x.1.1.length*x.2.length) false := by
  simp only [format,machineZeros_exact,row_exact,List.map_const',repeat_flatMap,
    List.length_flatMap,List.map_const',List.length_map,List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

/-- Row-major storage is proved on every complete output row. -/
theorem assembleRows_ofFn {b m : ℕ} (out v : Bits b) :
    List.ofFn (assembleRows out (fun _ : Fin m => v))=
      List.ofFn out++(List.replicate m (List.ofFn v)).flatten := by
  rw [List.ofFn_mul]
  have hh : (fun i : Fin (m+1) => List.ofFn (fun j : Fin b =>
      assembleRows out (fun _ : Fin m => v) ⟨i.val*b+j.val,by
        calc i.val*b+j.val < (i.val+1)*b := by nlinarith [j.isLt]
             _≤(m+1)*b := Nat.mul_le_mul_right _ i.isLt⟩))=
      (fun i : Fin (m+1) => List.ofFn (Fin.cases out (fun _ : Fin m => v) i)) := by
    funext i
    apply congrArg List.ofFn
    funext j
    have he : (⟨i.val*b+j.val,by
        calc i.val*b+j.val < (i.val+1)*b := by nlinarith [j.isLt]
             _≤(m+1)*b := Nat.mul_le_mul_right _ i.isLt⟩ : Fin ((m+1)*b))=rowWire i j := by
      apply Fin.ext
      change i.val*b+j.val=j.val+b*i.val
      ring
    rw [he]
    simp only [assembleRows,rowWire,Equiv.symm_apply_apply]
  rw [hh,List.ofFn_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,List.ofFn_const,List.flatten_cons]

/-- The real native formatter writes exactly the initial basis encoding
consumed by the physical parallel-trial stage, including all original flag
inputs, distinguished output row and spectator auxiliaries at zero. -/
theorem format_copyEncoding (x : PlacementRequest) (v : Bits x.1.2.length) :
    format (x,List.ofFn v)=List.ofFn (copyEncoding x.1.2.length x.1.1.length x.2.length
      (fun _ => Fin.append (Fin.append v (fun _ : Fin 1 => false)) (fun _ : Fin x.2.length => false))) := by
  rw [format_exact]
  have hw : initialWork x.1.1.length (List.ofFn (fun _ : Fin x.1.1.length => false))=(fun _ => false) := by
    funext i
    by_cases h : i.val<x.1.1.length <;>
      simp [initialWork,wordExtension,List.ofFn_const,List.getElem?_replicate,h]
  simp only [copyEncoding,splitTrial,Equiv.coe_fn_mk,Fin.append_left,Fin.append_right,
    encoded,hw,List.ofFn_fin_append,packJunk]
  rw [assembleRows_ofFn]
  have hj : packJunk (fun _ : Fin x.1.1.length => fun _ : Fin x.2.length => false)=
      (fun _ : Fin (x.1.1.length*x.2.length) => false) := by funext i;rfl
  rw [hj]
  simp only [List.ofFn_const,List.append_assoc]

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative.InitialNative

end

end P2MDyadicModule137

/- Helper module Solutions.RegevBridgeCoherentParallelInitialPreparation. -/
section P2MDyadicModule138

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative.InitialNative

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentComputeUncompute CoherentProjection

open NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

theorem repeatState_basis {l : ℕ} (m : ℕ) (bits : Bits l) :
    repeatState m (WithLp.toLp 2 (basis bits))=WithLp.toLp 2 (basis (fun _ : Fin m => bits)) := by
  ext copies
  change (∏ i : Fin m,basis bits (copies i))=basis (fun _ : Fin m => bits) copies
  by_cases h : copies=(fun _ => bits)
  · subst copies
    simp [basis]
  · have hex : ∃ i,copies i≠bits := by
      by_contra hn
      apply h
      funext i
      have hh := (not_exists.mp hn) i
      exact not_not.mp hh
    obtain ⟨i,hi⟩:=hex
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (show basis bits (copies i)=0 by simp [basis,hi])]
    simp [basis,h]

variable {f : Str→Str} (program : PolyProgram id id f)

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative.InitialNative

end

end P2MDyadicModule138

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingPipeline. -/
section P2MDyadicModule139

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Pipeline

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent NativeWordLayout

open CoherentWeightedPreparation CoherentComputeUncompute ControlledNativeGates CoherentRejection

open CoherentFirstSuccessNative

open scoped BigOperators

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable (request : Str→PointRequest×List Unit) (hr : Poly request)

def proposalCircuit (a : ℕ) (slots : List Unit) (_word : Str) (K : ℕ) :
    Layered (Trial.workSize request hr a slots K+1+4) :=
  fixedProposalCircuit (gateWord request a) (gateWord_poly request hr a) (wordBound request hr a)
    (2*slots.length+1) K

def initialBasis (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    Bits (Trial.workSize request hr a slots K+1+4) :=
  fun i => TM2Boolean.wordExtension (encoded slots word (fun _ : Fin K => false)) i.val

theorem initialBasis_value (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ)
    (i : Fin (Trial.workSize request hr a slots K+1+4)) :
    initialBasis request hr a slots word K i=
      TM2Boolean.wordExtension (encoded slots word (fun _ : Fin K => false)) i.val := rfl

theorem initialBasis_append (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    initialBasis request hr a slots word K=
      Fin.append (Fin.append (Trial.workTicket request hr a slots word K (fun _ => false))
        (fun _ : Fin 1 => false)) (fun _ : Fin 4 => false) := by
  have hwidth : 2*slots.length+1+K ≤ Trial.workSize request hr a slots K := by unfold Trial.workSize width;omega
  funext i
  rw [initialBasis_value]
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [Fin.append_left,Fin.val_castAdd]
      rfl
    · intro k
      simp only [Fin.append_left,Fin.append_right,Fin.val_castAdd,Fin.val_natAdd]
      apply TM2Boolean.wordExtension_after
      rw [encoded_length]
      omega
  · intro j
    simp only [Fin.append_right,Fin.val_natAdd]
    apply TM2Boolean.wordExtension_after
    rw [encoded_length]
    omega

/-- Actual H preparation followed by the genuine native interpreter. Its
layout uses the two public capacities, never the computed active length. -/
def trialCircuit (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) :=
  proposalCircuit request hr a slots word K++physicalCircuit request hr a b slots K budget

/-- The literal complete finite-gate rejection circuit, including its own
H preparation, consumes an ordinary basis state with all auxiliary bits zero. -/
def circuit (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) (m : ℕ) :=
  pipelineCircuit (Trial.workSize request hr a slots K) m 4 (trialCircuit request hr a b slots word K budget)

def basisInput (a : ℕ) (slots : List Unit) (word : Str) (K m : ℕ) :=
  copyEncoding (Trial.workSize request hr a slots K) m 4 (fun _ => initialBasis request hr a slots word K)

theorem exists_pure_from_basis :
    ∃ synthesis interpreter : ℕ,0 < synthesis ∧ 0 < interpreter ∧
      ∀ (slots : List Unit) (word : Str) (s : ℝ) (budget : List Unit),
        2*word.length+1 ≤ slots.length →
        ∀ (K : ℕ) (hK : Nat.size (intervalCount (request word).1) ≤ K),
        1 ≤ s → s^2=(variance (request word).1 : ℝ) → 2 ≤ (request word).1.2.1.length →
        ∀ m : ℕ,m≠0 →
        ∃ clean : EuclideanSpace ℂ (Retained (Bits (Trial.workSize request hr synthesis slots K)) (Bits 4) m),
          ‖clean‖=1 ∧
          ‖(WithLp.toLp 2 (runLayered (circuit request hr synthesis interpreter slots word K budget m)
              (basis (basisInput request hr synthesis slots word K m))-
            basisEmbedding (abstractEmbedding (Trial.workSize request hr synthesis slots K) m 4)
              (CoherentProjection.tensorState (Trial.embeddedTarget request hr synthesis slots word K s hK) clean)) : EuclideanSpace ℂ _)‖ ≤
            (m : ℝ)*Trial.error request hr synthesis slots word K budget+
              2*Real.exp (-(m : ℝ)/(112*((request word).1.2.1.length : ℝ))) := by
  exact InfoLossLAR.WorstCase.RegevSearch.coherent_gaussian_ticket_preparation request hr (Builder.gateWord_poly request hr)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Pipeline

end

end P2MDyadicModule139

/- Helper module Solutions.RegevBridgeGaussianPoissonSeries. -/
section P2MDyadicModule140

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open MeasureTheory FourierTransform RegevLWE.GaussConv

open scoped FourierTransform SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- The genuine lattice periodization admits a Schwartz Gaussian with the
actual Regev pi/width convention, for every positive real width. -/
theorem exists_schwartz_rho (width : ℝ) (hwidth : 0 < width) :
    ∃ function : 𝓢(Space (dimension:=dimension),ℂ),
      ∀ point,function point=(rho width point : ℂ) := by
  obtain ⟨gaussian,hgaussian⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin dimension)
  let unit : ℝˣ := Units.mk0 width⁻¹ (inv_ne_zero hwidth.ne')
  let dilation : Space (dimension:=dimension) ≃L[ℝ] Space (dimension:=dimension) := ContinuousLinearEquiv.smulLeft unit
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ dilation gaussian,fun point => ?_⟩
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,hgaussian,rho]
  congr 2
  have hdilation : dilation point=width⁻¹ • point := rfl
  rw [hdilation,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hwidth)]
  ring

theorem fourier_schwartz_rho (width : ℝ) (hwidth : 0 < width)
    (function : 𝓢(Space (dimension:=dimension),ℂ))
    (hfunction : ∀ point,function point=(rho width point : ℂ)) (frequency : Space (dimension:=dimension)) :
    VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension))) (⇑function) frequency=
      (width : ℂ)^dimension*(rho (1/width) frequency : ℂ) := by
  have hequal : (⇑function : Space (dimension:=dimension) → ℂ)=fun point => (rhoShift width 0 point : ℂ) := by
    funext point
    rw [hfunction]
    simp [rhoShift]
  have h := fourier_rhoShift hwidth (0 : Space (dimension:=dimension)) frequency
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension)))
    (fun point => (rhoShift width 0 point : ℂ)) frequency=_ at h
  rw [hequal,h]
  simp [inner_zero_left]

private theorem inner_nondegenerate : (innerₗ (Space (dimension:=dimension))).Nondegenerate :=
  ⟨fun point hzero => inner_self_eq_zero.mp (hzero point),fun point hzero => inner_self_eq_zero.mp (hzero point)⟩

private theorem inner_flip_eq : LinearMap.BilinForm.flip (innerₗ (Space (dimension:=dimension)))=
    innerₗ (Space (dimension:=dimension)) := by
  ext first second
  exact real_inner_comm first second

/-- The literal complex Gaussian amplitude periodized over an actual
lattice, before extracting real mass or normalizing a quantum vector. -/
def periodizedGaussian (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) : ℂ :=
  ∑' point : lattice,(rho width (shift+(point : Space (dimension:=dimension))) : ℂ)

/-- Exact complete dual Fourier expansion of the genuine periodized
Gaussian amplitude. Every dual Gaussian coefficient is retained. -/
theorem periodized_poisson (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0 < width)
    (shift : Space (dimension:=dimension)) :
    periodizedGaussian lattice width shift=
      (ZLattice.covolume lattice : ℂ)⁻¹*
        ∑' frequency : dual lattice,((width : ℂ)^dimension*
          (rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
          (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have hpoisson := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral volume
    (innerₗ (Space (dimension:=dimension))) (inner_nondegenerate (dimension:=dimension)) lattice function shift
  rw [inner_flip_eq (dimension:=dimension)] at hpoisson
  simpa only [periodizedGaussian,hfunction,fourier_schwartz_rho width hwidth function hfunction,dual,innerₗ_apply_apply] using hpoisson

/-- Absolute summability of the same complete dual series, before any
finite Fourier reindexing or truncation is performed. -/
theorem summable_dual_series (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0 < width)
    (shift : Space (dimension:=dimension)) :
    Summable (fun frequency : dual lattice =>
      (rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ)*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have h := ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule volume
    (innerₗ (Space (dimension:=dimension))) (inner_nondegenerate (dimension:=dimension)) lattice function shift
  rw [inner_flip_eq] at h
  change Summable (fun frequency : dual lattice =>
    VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space (dimension:=dimension))) (⇑function)
      (frequency : Space (dimension:=dimension))*
      (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) at h
  simp only [fourier_schwartz_rho width hwidth function hfunction,mul_assoc] at h
  exact (summable_mul_left_iff (pow_ne_zero dimension (Complex.ofReal_ne_zero.mpr hwidth.ne'))).mp h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule140

/- Helper module Solutions.RegevBridgeLatticeGaussianSummable. -/
section P2MDyadicModule141

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- Schwartz decay gives absolute convergence on the actual lattice;
no Gaussian normalizer or sampling algorithm is assumed. -/
theorem summable_schwartz_lattice
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (function : 𝓢(Space (dimension:=dimension),ℂ)) :
    Summable (fun point : lattice => function (point : Space (dimension:=dimension))) := by
  let exponent := Module.finrank ℤ lattice+1
  have hs := ZLattice.summable_norm_pow_inv lattice exponent (Nat.lt_succ_self _)
  apply Summable.of_norm
  apply Summable.of_norm_bounded_eventually (g:=fun point : lattice =>
    SchwartzMap.seminorm ℝ exponent 0 function*‖point‖⁻¹^exponent) (hs.mul_left _)
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_singleton (0 : lattice))
  intro point hnot
  simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff] at hnot ⊢
  by_contra hne
  apply hnot
  have hpositive : 0<‖point‖^exponent := pow_pos (norm_pos_iff.mpr hne) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ function exponent (point : Space (dimension:=dimension))
  change ‖point‖^exponent*‖function (point : Space (dimension:=dimension))‖ ≤ _ at hdecay
  rw [norm_norm,inv_pow,←div_eq_mul_inv,le_div_iff₀ hpositive,mul_comm]
  exact hdecay

/-- In particular, every positive-width genuine lattice Gaussian is
summable over the original full-rank lattice. -/
theorem summable_gaussian_lattice
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) :
    Summable (fun point : lattice => rho width (point : Space (dimension:=dimension))) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  have h := (summable_schwartz_lattice lattice function).norm
  simp only [hfunction,Complex.norm_real,Real.norm_eq_abs] at h
  have habsolute (point : lattice) : |rho width (point : Space (dimension:=dimension))|=
      rho width (point : Space (dimension:=dimension)) := abs_of_pos (Real.exp_pos _)
  simpa only [habsolute] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule141

/- Helper module Solutions.RegevBridgeLatticeGaussianCosetSummable. -/
section P2MDyadicModule142

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- Every translate has absolutely summable genuine Gaussian mass. -/
theorem summable_gaussian_coset
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) (shift : Space (dimension:=dimension)) :
    Summable (fun point : lattice => rho width ((point : Space (dimension:=dimension))+shift)) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  let translated := SchwartzMap.compSubConstCLM ℂ (-shift) function
  have h := summable_schwartz_lattice lattice translated
  have hvalue (point : lattice) : translated point=(rho width ((point : Space (dimension:=dimension))+shift) : ℂ) := by
    simp only [translated,SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add,hfunction]
  simp only [hvalue] at h
  exact Complex.summable_ofReal.mp h

theorem rhoCoset_zero_pos (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    0<rhoCoset width lattice 0 := by
  have h := (summable_gaussian_lattice lattice width hwidth).tsum_pos
    (fun _ => (Real.exp_pos _).le) (0 : lattice) (Real.exp_pos _)
  simpa only [rhoCoset,add_zero] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule142

/- Helper module Solutions.RegevBridgeGaussianFiniteFourier. -/
section P2MDyadicModule143

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier

open GaussianPoissonSeries GaussianProjection.CosetGeometry RegevLWE.GaussConv

open scoped BigOperators FourierTransform

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- The complete unphased dual Gaussian has absolutely summable complex
coefficients. This statement makes no smoothing or tail approximation. -/
theorem summable_dual_gaussian (lattice : Submodule ℤ (CoordinateSpace (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    Summable (fun frequency : dual lattice => (rho (1/width) (frequency : CoordinateSpace (dimension:=dimension)) : ℂ)) := by
  simpa using GaussianPoissonSeries.summable_dual_series lattice width hwidth 0

end

end InfoLossLAR.WorstCase.FiniteLatticeFourier

end P2MDyadicModule143

/- Helper module Solutions.RegevBridgeLatticeGaussianMass. -/
section P2MDyadicModule144

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped FourierTransform

noncomputable section

variable {dimension : ℕ}

/-- The complex amplitude periodization is the canonical inclusion of the
real lattice Gaussian mass, with the same shift and summation filter. -/
theorem periodized_eq_rhoCoset (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) :
    periodizedGaussian lattice width shift=(rhoCoset width lattice shift : ℂ) := by
  unfold periodizedGaussian rhoCoset
  rw [Complex.ofReal_tsum (L:=.unconditional lattice)]
  apply tsum_congr
  intro point
  rw [add_comm]

/-- Poisson summation at zero gives the exact positive real mass identity. -/
theorem rhoCoset_zero_poisson (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    rhoCoset width lattice 0=width^dimension*(ZLattice.covolume lattice)⁻¹*
      ∑' frequency : dual lattice,rho (1/width) (frequency : Space (dimension:=dimension)) := by
  have h := periodized_poisson lattice width hwidth 0
  rw [periodized_eq_rhoCoset] at h
  simp only [inner_zero_left,AddChar.map_zero_eq_one,Circle.coe_one,mul_one,tsum_mul_left] at h
  rw [←Complex.ofReal_tsum (L:=.unconditional (dual lattice))] at h
  have hequal : (rhoCoset width lattice 0 : ℂ)=
      ((width^dimension*(ZLattice.covolume lattice)⁻¹*
        ∑' frequency : dual lattice,rho (1/width) (frequency : Space (dimension:=dimension)) : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast hequal

/-- Increasing inverse width can only decrease each actual Gaussian
coefficient, with the pi convention retained exactly. -/
theorem rho_inverse_antitone (point : Space (dimension:=dimension)) {first second : ℝ}
    (hfirst : 0<first) (hle : first ≤ second) : rho (1/second) point≤rho (1/first) point := by
  have hsecond : 0<second := hfirst.trans_le hle
  have hform (scale : ℝ) : rho (1/scale) point=Real.exp (-Real.pi*scale^2*‖point‖^2) := by
    unfold rho
    rw [one_div,inv_pow,div_inv_eq_mul]
    ring_nf
  rw [hform,hform]
  apply Real.exp_le_exp.mpr
  have hsquare : first^2 ≤ second^2 := sq_le_sq₀ hfirst.le hsecond.le |>.mpr hle
  nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg ‖point‖)]

/-- A width dilation raises true lattice Gaussian mass by at most the
ambient-dimensional power of its dilation factor. -/
theorem rhoCoset_dilation_le (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width factor : ℝ) (hwidth : 0<width) (hfactor : 1≤factor) :
    rhoCoset (factor*width) lattice 0≤factor^dimension*rhoCoset width lattice 0 := by
  have hfactorPos : 0<factor := lt_of_lt_of_le zero_lt_one hfactor
  have hscaled : 0<factor*width := mul_pos hfactorPos hwidth
  have hsfirst := Complex.summable_ofReal.mp
    (FiniteLatticeFourier.summable_dual_gaussian lattice (factor*width) hscaled)
  have hssecond := Complex.summable_ofReal.mp
    (FiniteLatticeFourier.summable_dual_gaussian lattice width hwidth)
  have hdual : (∑' frequency : dual lattice,rho (1/(factor*width)) (frequency : Space (dimension:=dimension)))≤
      ∑' frequency : dual lattice,rho (1/width) (frequency : Space (dimension:=dimension)) := by
    apply hsfirst.tsum_le_tsum _ hssecond
    intro frequency
    exact rho_inverse_antitone _ hwidth (le_mul_of_one_le_left hwidth.le hfactor)
  rw [rhoCoset_zero_poisson lattice (factor*width) hscaled,rhoCoset_zero_poisson lattice width hwidth]
  have hbound := mul_le_mul_of_nonneg_left hdual
    (mul_nonneg (pow_nonneg hscaled.le dimension)
      (inv_nonneg.mpr (ZLattice.covolume_pos lattice MeasureTheory.volume).le))
  simpa only [mul_pow,mul_assoc] using hbound

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule144

/- Helper module Solutions.RegevBridgeGaussianShiftAmplitude. -/
section P2MDyadicModule145

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

theorem rhoCoset_pos (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) :
    0 < rhoCoset width lattice shift := by
  exact (summable_gaussian_coset lattice width hwidth shift).tsum_pos
    (fun _ => (Real.exp_pos _).le) (0 : lattice) (Real.exp_pos _)

theorem gaussianAmplitude_nonneg (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) (point : lattice) :
    0 ≤ gaussianAmplitude lattice width shift point := div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

theorem gaussianAmplitude_sq (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) (point : lattice) :
    (gaussianAmplitude lattice width shift point)^2=
      rho width ((point : Space (dimension:=dimension))+shift)/rhoCoset width lattice shift := by
  rw [gaussianAmplitude,div_pow,Real.sq_sqrt (rhoCoset_pos lattice width hwidth shift).le,←Real.exp_nat_mul]
  congr 1
  unfold rho
  congr 1
  field_simp
  ring

/-- The complete true Gaussian amplitude has square norm exactly one. -/
theorem gaussianAmplitude_square_sum (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) :
    Summable (fun point : lattice => (gaussianAmplitude lattice width shift point)^2) ∧
      (∑' point : lattice,(gaussianAmplitude lattice width shift point)^2)=1 := by
  simp_rw [gaussianAmplitude_sq lattice width hwidth shift]
  refine ⟨(summable_gaussian_coset lattice width hwidth shift).div_const _,?_⟩
  rw [tsum_div_const]
  exact div_self (rhoCoset_pos lattice width hwidth shift).ne'

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule145

/- Helper module Solutions.RegevBridgeGaussianHilbertState. -/
section P2MDyadicModule146

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

theorem hilbert_norm_sq {Index : Type*} (value : Hilbert Index) :
    ‖value‖^2=∑' point : Index,‖value point‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p:=(2 : ENNReal)) (by norm_num) value

variable {dimension : ℕ}

theorem gaussianHilbertState_apply
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) (point : lattice) :
    gaussianHilbertState lattice width hwidth shift point=(gaussianAmplitude lattice width shift point : ℂ) := rfl

theorem gaussianHilbertState_norm
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) :
    ‖gaussianHilbertState lattice width hwidth shift‖=1 := by
  have h : ‖gaussianHilbertState lattice width hwidth shift‖^2=1 := by
    rw [hilbert_norm_sq]
    simpa only [gaussianHilbertState_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs] using
      (gaussianAmplitude_square_sum lattice width hwidth shift).2
  nlinarith [norm_nonneg (gaussianHilbertState lattice width hwidth shift)]

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule146

/- Helper module Solutions.RegevBridgePositiveHilbertState. -/
section P2MDyadicModule147

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

/-- Canonical positive amplitudes of a specified complete nonnegative law.
This definition does not turn an arbitrary classical sampler into a state. -/
def positiveHilbertState {Index : Type*} (mass : Index → ℝ) (hnonnegative : ∀ index,0 ≤ mass index)
    (hsummable : Summable mass) : Hilbert Index := by
  refine ⟨fun index => (Real.sqrt (mass index) : ℂ),?_⟩
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hnonnegative _)] using hsummable

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule147

/- Helper module Solutions.RegevBridgeFiniteProductMass. -/
section P2MDyadicModule148

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- The full countable joint product law, not just its coordinate marginals. -/
def finiteProductMass {Index : Type*} (dimension : ℕ) (mass : Index → ℝ) (word : Fin dimension → Index) : ℝ :=
  ∏ index,mass (word index)

theorem finiteProductMass_nonnegative {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (word : Fin dimension → Index) :
    0 ≤ finiteProductMass dimension mass word := Finset.prod_nonneg (fun _ _ => hnonnegative _)

/-- A genuine full infinite product-law normalization in finitely many
coordinates, valid without finiteness of the individual coordinate space. -/
theorem finiteProductMass_hasSum {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (hsummable : Summable mass) :
    HasSum (finiteProductMass dimension mass) ((∑' value,mass value)^dimension) := by
  classical
  induction dimension with
  | zero =>
    rw [pow_zero]
    have heq : finiteProductMass 0 mass=(fun _ : Fin 0 → Index => (1 : ℝ)) := by
      funext word
      simp only [finiteProductMass,Finset.univ_eq_empty,Finset.prod_empty]
    rw [heq]
    convert hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)) using 1
    simp
  | succ dimension ih =>
    have hs := hsummable.mul_of_nonneg ih.summable hnonnegative
      (finiteProductMass_nonnegative dimension mass hnonnegative)
    have hp := hsummable.hasSum.mul ih hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass pair.1*finiteProductMass dimension mass pair.2)=
        (finiteProductMass (dimension+1) mass) ∘ (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,finiteProductMass,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [pow_succ,mul_comm] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule148

/- Helper module Solutions.RegevBridgeFiniteHilbertEmbedding. -/
section P2MDyadicModule149

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- Literal finite support embedding into the complete Hilbert space.
Every physical source label keeps its own injectively assigned location. -/
def finiteEmbed {FiniteIndex Index : Type*} [Fintype FiniteIndex]
    (embedding : FiniteIndex ↪ Index) (value : EuclideanSpace ℂ FiniteIndex) : Hilbert Index := by
  classical
  exact ∑ index,lp.single 2 (embedding index) (value index)

theorem finiteEmbed_apply {FiniteIndex Index : Type*} [Fintype FiniteIndex]
    (embedding : FiniteIndex ↪ Index) (value : EuclideanSpace ℂ FiniteIndex) (index : FiniteIndex) :
    finiteEmbed embedding value (embedding index)=value index := by
  classical
  simp only [finiteEmbed,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Pi.single_apply]
  have hequal (other : FiniteIndex) : (embedding index=embedding other) ↔ index=other := embedding.injective.eq_iff
  simp only [hequal,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem finiteEmbed_apply_not_mem {FiniteIndex Index : Type*} [Fintype FiniteIndex]
    (embedding : FiniteIndex ↪ Index) (value : EuclideanSpace ℂ FiniteIndex) (index : Index)
    (hindex : index ∉ Set.range embedding) : finiteEmbed embedding value index=0 := by
  classical
  simp only [finiteEmbed,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Pi.single_apply]
  apply Finset.sum_eq_zero
  intro source _
  rw [if_neg (fun hequal => hindex ⟨source,hequal.symm⟩)]

/-- The actual finite-to-countable embedding preserves the full Hilbert
norm, including every amplitude and every zero outside its image. -/
theorem finiteEmbed_norm {FiniteIndex Index : Type*} [Fintype FiniteIndex]
    (embedding : FiniteIndex ↪ Index) (value : EuclideanSpace ℂ FiniteIndex) :
    ‖finiteEmbed embedding value‖=‖value‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hilbert_norm_sq,EuclideanSpace.norm_sq_eq]
  let selected := Finset.univ.image embedding
  have hsupport (index : Index) (hindex : index ∉ selected) : ‖finiteEmbed embedding value index‖^2=0 := by
    rw [finiteEmbed_apply_not_mem embedding value index]
    · simp
    · intro h
      obtain ⟨source,rfl⟩ := h
      exact hindex (Finset.mem_image.mpr ⟨source,Finset.mem_univ source,rfl⟩)
  rw [tsum_eq_sum hsupport]
  rw [show selected=Finset.univ.image embedding from rfl,Finset.sum_image]
  · simp only [finiteEmbed_apply]
  · exact embedding.injective.injOn

theorem finiteEmbed_add {FiniteIndex Index : Type*} [Fintype FiniteIndex]
    (embedding : FiniteIndex ↪ Index) (first second : EuclideanSpace ℂ FiniteIndex) :
    finiteEmbed embedding (first+second)=finiteEmbed embedding first+finiteEmbed embedding second := by
  classical
  simp only [finiteEmbed,PiLp.add_apply,lp.single_add,Finset.sum_add_distrib]

theorem finiteEmbed_smul {FiniteIndex Index : Type*} [Fintype FiniteIndex]
    (embedding : FiniteIndex ↪ Index) (scalar : ℂ) (value : EuclideanSpace ℂ FiniteIndex) :
    finiteEmbed embedding (scalar • value)=scalar • finiteEmbed embedding value := by
  classical
  simp only [finiteEmbed,PiLp.smul_apply,lp.single_smul,Finset.smul_sum]

/-- Every physical finite register embeds by a genuine linear isometry
into its complete countable amplitude model. -/
def finiteEmbedIsometry {FiniteIndex Index : Type*} [Fintype FiniteIndex]
    (embedding : FiniteIndex ↪ Index) : (EuclideanSpace ℂ FiniteIndex) →ₗᵢ[ℂ] Hilbert Index where
  toFun := finiteEmbed embedding
  map_add' := finiteEmbed_add embedding
  map_smul' scalar value := by simpa only [RingHom.id_apply] using finiteEmbed_smul embedding scalar value
  norm_map' := finiteEmbed_norm embedding

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule149

/- Helper module Solutions.RegevBridgeFinitePositivePushforward. -/
section P2MDyadicModule150

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open AFT

open scoped BigOperators

noncomputable section

variable {FiniteIndex Index : Type*} [Fintype FiniteIndex]

/-- The exact canonical positive pure state of a given finite law. -/
def finitePositiveState (law : FiniteDist FiniteIndex) : EuclideanSpace ℂ FiniteIndex :=
  WithLp.toLp 2 (fun index => (Real.sqrt (law.weight index) : ℂ))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule150

/- Helper module Solutions.RegevBridgeCoherentTicketPure. -/
section P2MDyadicModule151

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open AFT GaussianSource GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- The exact full countable integer Gaussian has positive canonical amplitudes. -/
def integerGaussianState (width : ℝ) (hwidth : 0 < width) (center : ℝ) : Hilbert ℤ :=
  positiveHilbertState (fun value => (roundingPMF width hwidth center value).toReal)
    (fun _ => ENNReal.toReal_nonneg) (summable_roundingMass width hwidth center)

theorem integerGaussianState_apply (width : ℝ) (hwidth : 0 < width) (center : ℝ) (value : ℤ) :
    integerGaussianState width hwidth center value=
      (Real.sqrt ((roundingPMF width hwidth center value).toReal) : ℂ) := rfl

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end P2MDyadicModule151

/- Helper module Solutions.RegevBridgeIntegerGaussianProduct. -/
section P2MDyadicModule152

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open GaussianRandomizedRounding GaussianRandomizedRounding.Wide.Coherent

open scoped BigOperators

noncomputable section

/-- Complete independent integer-coordinate Gaussian law. -/
def integerGaussianProductMass (dimension : ℕ) (width : ℝ) (hwidth : 0 < width) :
    (Fin dimension → ℤ) → ℝ :=
  finiteProductMass dimension (fun value => (roundingPMF width hwidth 0 value).toReal)

theorem integerGaussianProductMass_nonnegative (dimension : ℕ) (width : ℝ) (hwidth : 0 < width)
    (word : Fin dimension → ℤ) : 0 ≤ integerGaussianProductMass dimension width hwidth word :=
  finiteProductMass_nonnegative dimension _ (fun _ => ENNReal.toReal_nonneg) word

theorem integerGaussianProductMass_hasSum (dimension : ℕ) (width : ℝ) (hwidth : 0 < width) :
    HasSum (integerGaussianProductMass dimension width hwidth) 1 := by
  have h := finiteProductMass_hasSum dimension (fun value => (roundingPMF width hwidth 0 value).toReal)
    (fun _ => ENNReal.toReal_nonneg) (summable_roundingMass width hwidth 0)
  simpa only [integerGaussianProductMass,roundingMass_sum,one_pow] using h

/-- The canonical joint state has positive product amplitudes and norm one. -/
def integerGaussianProductState (dimension : ℕ) (width : ℝ) (hwidth : 0 < width) : Hilbert (Fin dimension → ℤ) :=
  positiveHilbertState (integerGaussianProductMass dimension width hwidth)
    (integerGaussianProductMass_nonnegative dimension width hwidth)
    (integerGaussianProductMass_hasSum dimension width hwidth).summable

theorem integerGaussianProductState_apply (dimension : ℕ) (width : ℝ) (hwidth : 0 < width)
    (word : Fin dimension → ℤ) :
    integerGaussianProductState dimension width hwidth word=
      ∏ index : Fin dimension,integerGaussianState width hwidth 0 (word index) := by
  change (Real.sqrt (∏ index : Fin dimension,(roundingPMF width hwidth 0 (word index)).toReal) : ℂ)=_
  rw [Real.sqrt_prod]
  · simp only [Complex.ofReal_prod,integerGaussianState_apply]
  · intro index _
    exact ENNReal.toReal_nonneg

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule152

/- Helper module Solutions.RegevBridgeWideGaussianSampler. -/
section P2MDyadicModule153

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic GaussianProjection GaussianProjection.CosetGeometry

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

noncomputable section

open scoped Classical

/-- The final infinite Gaussian tail estimate has no prefactor depending
on the numerical width. -/
theorem scaled_tail_bound (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) :
    tailEnvelope width (radius input) ≤ 6*Real.exp (-Real.pi*(input.2.1.length : ℝ)^2/2) := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hscale := (scale_width_bounds input width hwidth hsquare).1
  have hrad : (input.2.1.length : ℝ)*width ≤ (radius input : ℝ) := by
    simpa only [radius,Nat.cast_mul] using mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg input.2.1.length)
  have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (input.2.1.length : ℝ)*width) (Nat.cast_nonneg (radius input))).mpr hrad
  have hratio := div_le_div_of_nonneg_right hsq (show (0 : ℝ) ≤ 2*width^2 by positivity)
  have heq : ((input.2.1.length : ℝ)*width)^2/(2*width^2)=(input.2.1.length : ℝ)^2/2 := by field_simp
  rw [heq] at hratio
  have hexponent : -Real.pi*(radius input : ℝ)^2/(2*width^2) ≤ -Real.pi*(input.2.1.length : ℝ)^2/2 := by
    calc
      _ = -Real.pi*((radius input : ℝ)^2/(2*width^2)) := by ring
      _ ≤ -Real.pi*((input.2.1.length : ℝ)^2/2) := mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr Real.pi_pos.le)
      _ = _ := by ring
  have htail := (VarianceGrid.tailEnvelope_interval (radius input : ℝ) hwidth le_rfl le_rfl).trans (intervalTail_le_six hwidth)
  exact htail.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule153

/- Helper module Solutions.RegevBridgeRationalGramSchmidt. -/
section P2MDyadicModule154

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

theorem innerQ_real {dimension : ℕ} (left right : QVector dimension) :
    (innerQ left right : ℝ)=inner ℝ (realVec left) (realVec right) := by
  unfold innerQ realVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

noncomputable section

end

noncomputable section

theorem inputVectors_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (column : Fin dimension) :
    realVec (inputVectors basis column)=IntegerBasis.realBasis basis hdet column := by
  rw [IntegerBasis.realBasis_apply]
  ext row
  simp [realVec,inputVectors]

end

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule154

/- Helper module Solutions.RegevBridgeRationalInverseAlgebra. -/
section P2MDyadicModule155

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

noncomputable section

/-- Analytical Cramer specification only. The native implementation below
will use the cached rational orthogonalization and reverse substitution. -/
def dualVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : QVector n :=
  fun row => (Matrix.cramer B.transpose (Pi.single i 1) row : ℚ)/(B.det : ℚ)

theorem Native.current_correct_dual {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    Native.current (Native.inputRows B)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => dualVector B col row)) :=
  Native.current_correct B hdet

theorem dualVector_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (i k : Fin n) : innerQ (dualVector B i) (inputVectors B k)=if k=i then 1 else 0 := by
  have hD : (B.det : ℚ)≠0 := by exact_mod_cast hdet
  have hh:=congrFun (Matrix.mulVec_cramer B.transpose (Pi.single i 1)) k
  simp only [Matrix.mulVec,dotProduct,Matrix.det_transpose,Pi.smul_apply,smul_eq_mul,
    Matrix.transpose_apply,Pi.single_apply] at hh
  have hcast : (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))=
      (B.det : ℚ)*(if k=i then 1 else 0) := by exact_mod_cast hh
  calc
    _ = (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))/(B.det : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro row _
      simp only [innerQ,dualVector,inputVectors]
      ring
    _ = ((B.det : ℚ)*(if k=i then 1 else 0))/(B.det : ℚ) := by rw [hcast]
    _ = _ := by split_ifs <;> simp [hD]

/-- Pairings with the original input columns determine the entire real
vector, using the actual Euclidean dual basis. -/
theorem real_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : IntegerBasis.Space (dimension:=n))
    (h : ∀ k,inner ℝ x (IntegerBasis.realBasis B hdet k)=inner ℝ y (IntegerBasis.realBasis B hdet k)) : x=y := by
  apply (IntegerBasis.dualRealBasis B hdet).ext_elem
  intro k
  change ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
    (IntegerBasis.realBasis B hdet)).repr x) k=
    ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
      (IntegerBasis.realBasis B hdet)).repr y) k
  rw [LinearMap.BilinForm.dualBasis_repr_apply,LinearMap.BilinForm.dualBasis_repr_apply]
  exact h k

theorem dualVector_real {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (i : Fin n) :
    realVec (dualVector B i)=IntegerBasis.dualRealBasis B hdet i := by
  apply real_pairings_unique B hdet
  intro k
  have hx : inner ℝ (realVec (dualVector B i)) (IntegerBasis.realBasis B hdet k)=if k=i then 1 else 0 := by
    rw [←inputVectors_real B hdet k,←innerQ_real,dualVector_pairing B hdet]
    split_ifs <;> norm_num
  rw [hx]
  exact (LinearMap.BilinForm.apply_dualBasis_left IntegerBasis.inner_nondegenerate
    (IntegerBasis.realBasis B hdet) i k).symm

/-- A coarse binary determinant bound has polynomial exponent in dimension
and original integer entry height. -/
theorem determinant_binary_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) : |B.det|≤(2 : ℤ)^((n+H)*n) := by
  have hdim : (n : ℤ)≤2^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hfac : (n.factorial : ℤ)≤2^(n*n) := by
    calc
      _ ≤ (n : ℤ)^n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ ((2 : ℤ)^n)^n := pow_le_pow_left₀ (Nat.cast_nonneg _) hdim _
      _ = _ := by rw [←pow_mul]
  have hh:=Matrix.det_le (abv:=AbsoluteValue.abs) hentries
  have hd : |B.det|≤(n.factorial : ℤ)*((2 : ℤ)^H)^n := by
    simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using hh
  calc
    _ ≤ (n.factorial : ℤ)*((2 : ℤ)^H)^n := hd
    _ ≤ (2 : ℤ)^(n*n)*((2 : ℤ)^H)^n := mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring

theorem cramer_binary_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) (i row : Fin n) :
    |Matrix.cramer B.transpose (Pi.single i 1) row|≤(2 : ℤ)^((n+H)*n) := by
  rw [Matrix.cramer_apply]
  apply determinant_binary_bound _ H
  intro r c
  simp only [Matrix.updateCol_apply,Matrix.transpose_apply]
  split_ifs
  · simp only [Pi.single_apply]
    split_ifs <;> simp
    exact one_le_pow₀ (by norm_num : (1 : ℤ)≤2)
  · exact hentries c r

theorem dualVector_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) (i row : Fin n) :
    HeightBound (dualVector B i row) (dualHeight n H) := by
  have hnum : (Matrix.cramer B.transpose (Pi.single i 1) row).natAbs≤2^((n+H)*n) := by
    have hh : ((Matrix.cramer B.transpose (Pi.single i 1) row).natAbs : ℤ)≤(2 : ℤ)^((n+H)*n) := by
      simpa only [Int.natCast_natAbs] using cramer_binary_bound B H hentries i row
    exact_mod_cast hh
  have hden : B.det.natAbs≤2^((n+H)*n) := by
    have hh : (B.det.natAbs : ℤ)≤(2 : ℤ)^((n+H)*n) := by
      simpa only [Int.natCast_natAbs] using determinant_binary_bound B H hentries
    exact_mod_cast hh
  have hh:=(HeightBound.of_int hnum).div (HeightBound.of_int hden)
  simpa only [dualVector,dualHeight,two_mul] using hh

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule155

/- Helper module Solutions.RegevBridgeRationalGramSchmidtNative. -/
section P2MDyadicModule156

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

@[fun_prop] theorem dot_poly : Poly dot := by unfold dot;fun_prop

@[fun_prop] theorem projectionEntry_poly : Poly projectionEntry := by unfold projectionEntry;fun_prop

@[fun_prop] theorem rowValue_poly : Poly rowValue := by unfold rowValue;fun_prop

@[fun_prop] theorem orthogonalStep_poly : Poly orthogonalStep := by
  have hindices : Poly (fun input : List (List ℚ) × List ℚ => List.range input.2.length) :=
    Poly.comp (f:=fun values : List ℚ => List.range values.length) (g:=Prod.snd) Poly.list_indices Poly.snd
  unfold orthogonalStep
  exact Poly.list_map rowValue_poly hindices

@[fun_prop] theorem rationalTicks_poly : Poly rationalTicks := by unfold rationalTicks;fun_prop

@[fun_prop] theorem vectorTicks_poly : Poly vectorTicks := by unfold vectorTicks;fun_prop

@[fun_prop] theorem matrixTicks_poly : Poly matrixTicks := by unfold matrixTicks;fun_prop

theorem rationalTicks_length (value : ℚ) : (rationalTicks value).length=(Ratio.encode value).length := by
  rw [Ratio.encode_length]
  simp only [rationalTicks,List.length_append,List.length_replicate,List.length_flatMap,
    List.map_const',List.sum_replicate,List.length_cons,List.length_nil,nsmul_eq_mul,Nat.cast_id]
  omega

theorem vectorTicks_length (vector : List ℚ) :
    (vectorTicks vector).length=(encodeList Ratio.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [vectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      rationalTicks_length,EncodedList.cons_length] at *
    omega

theorem matrixTicks_length (matrix : List (List ℚ)) :
    (matrixTicks matrix).length=(encodeList (encodeList Ratio.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [matrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      vectorTicks_length,EncodedList.cons_length] at *
    omega

@[fun_prop] theorem cacheStep_poly : Poly (fun input : (List Unit × List (List ℚ)) × List ℚ =>
    cacheStep input.1 input.2) := by unfold cacheStep;fun_prop

theorem ticks_encoding_length (ticks : List Unit) : (enc ticks).length=ticks.length := by
  change (encodeList (fun _ : Unit => []) ticks).length=ticks.length
  induction ticks with
  | nil => rfl
  | cons head tail ih => simp only [EncodedList.cons_length,List.length_nil,List.length_cons,ih];omega

theorem state_encoding_length (state : List Unit × List (List ℚ)) :
    (enc state).length=2*state.1.length+1+(encodeList (encodeList Ratio.encode) state.2).length := by
  change (encodePair (encodeList enc) (encodeList (encodeList Ratio.encode)) state).length=_
  rw [encodePair_length]
  change 2*(enc state.1).length+1+_= _
  rw [ticks_encoding_length]

theorem cacheStep_length (state : List Unit × List (List ℚ)) (current : List ℚ) :
    (enc (cacheStep state current)).length ≤ 3*state.1.length+1 := by
  rw [state_encoding_length]
  unfold cacheStep
  simp only
  split_ifs with h
  · rw [matrixTicks_length] at h
    omega
  · change 2*state.1.length+1+0 ≤ _
    omega

theorem fold_encoding_length (columns : List (List ℚ)) (state : List Unit × List (List ℚ)) :
    (enc (columns.foldl cacheStep state)).length ≤ max (enc state).length (3*state.1.length+1) := by
  induction columns generalizing state with
  | nil => simp only [List.foldl_nil];exact le_max_left _ _
  | cons current rest ih =>
    rw [List.foldl_cons]
    apply (ih (cacheStep state current)).trans
    apply max_le
    · exact (cacheStep_length state current).trans (le_max_right _ _)
    · exact le_max_right _ _

theorem cacheFold_bound (columns : List (List ℚ)) (state : List Unit × List (List ℚ))
    (pre suffix : List (List ℚ)) (_hsplit : columns=pre++suffix) :
    (enc (pre.foldl cacheStep state)).length ≤
      (3*Polynomial.X+1 : Polynomial ℕ).eval
        (encodePair (encodeList (enc : List ℚ → List Bool)) enc (columns,state)).length := by
  let inputLength := (encodePair (encodeList (enc : List ℚ → List Bool)) enc (columns,state)).length
  have hstate : (enc state).length ≤ inputLength := by
    dsimp [inputLength]
    rw [encodePair_length]
    change (enc state).length ≤ 2*(encodeList (enc : List ℚ → List Bool) columns).length+1+(enc state).length
    omega
  have hticks : state.1.length ≤ inputLength := by
    rw [state_encoding_length] at hstate
    omega
  apply (fold_encoding_length pre state).trans
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change max _ _ ≤ 3*inputLength+1
  omega

@[fun_prop] theorem cacheFold_poly : Poly (fun input : List (List ℚ) × (List Unit × List (List ℚ)) =>
    input.1.foldl cacheStep input.2) :=
  ⟨cacheStep_poly.program.listFold [] (3*Polynomial.X+1) cacheFold_bound⟩

@[fun_prop] theorem cached_poly : Poly cached := by
  have hf := Poly.comp cacheFold_poly
    (show Poly (fun input : List (List ℚ) × List Unit => (input.1,(input.2,([] : List (List ℚ))))) by fun_prop)
  unfold cached
  exact Poly.comp Poly.snd hf

theorem dot_ofFn {dimension : ℕ} (first second : QVector dimension) :
    dot (List.ofFn first,List.ofFn second)=innerQ first second := by
  induction dimension with
  | zero => simp [dot,innerQ]
  | succ dimension ih =>
    simp only [dot,List.ofFn_succ,List.zip_cons_cons,List.map_cons,List.sum_cons]
    change first 0*second 0+dot (List.ofFn (Fin.tail first),List.ofFn (Fin.tail second))= _
    rw [ih]
    simp only [innerQ,Fin.sum_univ_succ,Fin.tail_def]

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule156

/- Helper module Solutions.RegevBridgeRationalGramSchmidtInput. -/
section P2MDyadicModule157

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

@[fun_prop] theorem integerTicks_poly : Poly integerTicks := by unfold integerTicks;fun_prop

@[fun_prop] theorem integerVectorTicks_poly : Poly integerVectorTicks := by unfold integerVectorTicks;fun_prop

@[fun_prop] theorem integerMatrixTicks_poly : Poly integerMatrixTicks := by unfold integerMatrixTicks;fun_prop

@[fun_prop] theorem inputBudget_poly : Poly inputBudget := by unfold inputBudget;fun_prop

@[fun_prop] theorem rationalColumn_poly : Poly rationalColumn := by
  unfold rationalColumn
  exact Poly.list_map (show Poly (fun input : List ℤ × ℤ => (input.2 : ℚ)) by fun_prop) Poly.identity

@[fun_prop] theorem rationalColumns_poly : Poly rationalColumns := by
  unfold rationalColumns
  exact Poly.list_map (Poly.comp rationalColumn_poly Poly.snd) Poly.identity

@[fun_prop] theorem inputCache_poly : Poly inputCache := by unfold inputCache;fun_prop

theorem integerTicks_length (value : ℤ) : (integerTicks value).length=(Signed.encode value).length := by
  simp only [integerTicks,List.length_append,List.length_replicate,List.length_map,Signed.encode_length]

theorem integerVectorTicks_length (vector : List ℤ) :
    (integerVectorTicks vector).length=(encodeList Signed.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerVectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerTicks_length,EncodedList.cons_length] at *
    omega

theorem integerMatrixTicks_length (matrix : List (List ℤ)) :
    (integerMatrixTicks matrix).length=(encodeList (encodeList Signed.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerMatrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerVectorTicks_length,EncodedList.cons_length] at *
    omega

@[fun_prop] theorem transposeColumn_poly : Poly transposeColumn := by unfold transposeColumn;fun_prop

@[fun_prop] theorem transpose_poly : Poly transpose := by
  unfold transpose
  exact Poly.list_map transposeColumn_poly Poly.list_indices

@[fun_prop] theorem basisCache_poly : Poly basisCache := by unfold basisCache;fun_prop

noncomputable section

theorem inputColumns_entry_height {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (row column : Fin dimension) :
    |basis row column| ≤ (2 : ℤ)^(integerMatrixTicks (inputColumns basis)).length := by
  have hcolumn : List.ofFn (fun position => basis position column) ∈ inputColumns basis :=
    List.mem_ofFn.mpr ⟨column,rfl⟩
  have hentry : basis row column ∈ List.ofFn (fun position => basis position column) :=
    List.mem_ofFn.mpr ⟨row,rfl⟩
  have hcolumnSize := EncodedList.member_length (encodeList Signed.encode) (inputColumns basis) _ hcolumn
  have hentrySize := EncodedList.member_length Signed.encode _ _ hentry
  have hbits : (basis row column).natAbs.bits.length ≤ (integerMatrixTicks (inputColumns basis)).length := by
    rw [integerMatrixTicks_length]
    rw [Signed.encode_length] at hentrySize
    omega
  have hvalue := (NatBinary.le_two_pow_length (basis row column).natAbs).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits)
  have hcast := (Nat.cast_le (α:=ℤ)).mpr hvalue
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using hcast

theorem transpose_input_rows {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    transpose (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=inputColumns basis := by
  apply List.ext_getElem
  · simp only [transpose,List.length_map,List.length_range,List.length_ofFn,inputColumns]
  · intro column hfirst hsecond
    have hcolumn : column < dimension := by
      simpa only [transpose,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [transpose,List.length_ofFn,List.getElem_map,List.getElem_range,transposeColumn,
      List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hcolumn,↓reduceDIte,Option.getD_some,
      inputColumns,List.getElem_ofFn]

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule157

/- Helper module Solutions.RegevBridgeRationalInverseNative. -/
section P2MDyadicModule158

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open RationalGramSchmidt.Native

open scoped BigOperators

@[fun_prop] theorem term_poly : Poly term := by unfold term;fun_prop

@[fun_prop] theorem entry_poly : Poly entry := by
  have hi : Poly (fun input : ((Context × List (List ℚ)) × ℕ) × ℕ => List.range input.1.1.1.1.length) :=
    Poly.comp (f:=fun values : List (List ℚ) => List.range values.length)
      (g:=fun input : ((Context × List (List ℚ)) × ℕ) × ℕ => input.1.1.1.1) Poly.list_indices (by fun_prop)
  have ht := Poly.list_map (f:=fun input j => term (input,j)) term_poly hi
  have hs := Poly.comp (show Poly (List.sum : List ℚ → ℚ) from ⟨PolyProgram.ratSum⟩) ht
  have hf : Poly (fun input : ((Context × List (List ℚ)) × ℕ) × ℕ =>
      let gs := input.1.1.1.2[input.1.2]?.getD []
      gs[input.2]?.getD 0/dot (gs,gs)) := by fun_prop
  unfold entry
  exact Poly.comp Poly.rat_sub (Poly.pair hf hs)

@[fun_prop] theorem column_poly : Poly column := by
  have hi : Poly (fun input : (Context × List (List ℚ)) × ℕ => List.range input.1.1.1.length) := by
    exact Poly.comp (f:=fun values : List (List ℚ) => List.range values.length)
      (g:=fun input : (Context × List (List ℚ)) × ℕ => input.1.1.1) Poly.list_indices (by fun_prop)
  unfold column
  exact Poly.list_map entry_poly hi

@[fun_prop] theorem replaceColumn_poly : Poly replaceColumn := by
  have hi : Poly (fun input : (List (List ℚ) × ℕ) × List ℚ => List.range input.1.1.length) :=
    Poly.comp (f:=fun values : List (List ℚ) => List.range values.length)
      (g:=fun input : (List (List ℚ) × ℕ) × List ℚ => input.1.1) Poly.list_indices (by fun_prop)
  unfold replaceColumn
  exact Poly.list_map (by fun_prop) hi

@[fun_prop] theorem step_poly : Poly (fun input : State × ℕ => step input.1 input.2) := by
  unfold step
  fun_prop

theorem state_encoding_length (state : State) :
    (enc state).length=2*(enc state.1).length+2*state.2.1.length+2+
      (encodeList (encodeList Ratio.encode) state.2.2).length := by
  change (encodePair enc enc state).length=_
  rw [encodePair_length,RationalGramSchmidt.Native.state_encoding_length]
  omega

theorem step_length (state : State) (counter : ℕ) :
    (enc (step state counter)).length≤ 2*(enc state.1).length+3*state.2.1.length+2 := by
  rw [state_encoding_length]
  unfold step
  simp only
  split_ifs with h
  · rw [matrixTicks_length] at h
    omega
  · change 2*(enc state.1).length+2*state.2.1.length+2+0≤ _
    omega

theorem fold_encoding_length (counters : List ℕ) (state : State) :
    (enc (counters.foldl step state)).length≤
      max (enc state).length (2*(enc state.1).length+3*state.2.1.length+2) := by
  induction counters generalizing state with
  | nil => exact le_max_left _ _
  | cons counter rest ih =>
    rw [List.foldl_cons]
    apply (ih (step state counter)).trans
    apply max_le
    · exact (step_length state counter).trans (le_max_right _ _)
    · exact le_max_right _ _

theorem fold_bound (counters : List ℕ) (state : State) (pre suffix : List ℕ)
    (_hsplit : counters=pre++suffix) :
    (enc (pre.foldl step state)).length≤
      (3*Polynomial.X+2 : Polynomial ℕ).eval
        (encodePair (encodeList (enc : ℕ → List Bool)) enc (counters,state)).length := by
  let inputLength := (encodePair (encodeList (enc : ℕ → List Bool)) enc (counters,state)).length
  have hs : (enc state).length≤ inputLength := by
    dsimp [inputLength]
    rw [encodePair_length]
    change (enc state).length≤ 2*(encodeList (enc : ℕ → List Bool) counters).length+1+(enc state).length
    omega
  have hc : 2*(enc state.1).length+2*state.2.1.length+2≤ inputLength := by
    rw [state_encoding_length] at hs
    omega
  apply (fold_encoding_length pre state).trans
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change max _ _≤ 3*inputLength+2
  omega

@[fun_prop] theorem fold_poly : Poly (fun input : List ℕ × State => input.1.foldl step input.2) :=
  ⟨step_poly.program.listFold 0 (3*Polynomial.X+2) fold_bound⟩

@[fun_prop] theorem cached_poly : Poly cached := by
  have hi : Poly (fun input : List (List ℤ) =>
      (List.range input.length,
        ((rationalColumns (transpose input),basisCache input),
          (inputBudget input,(rationalColumns (transpose input)).map (fun row => row.map (fun _ => (0 : ℚ))))))) := by
    fun_prop
  unfold cached
  exact Poly.comp (f:=fun state : State => state.2.2) (by fun_prop) (Poly.comp fold_poly hi)

@[fun_prop] theorem transposeRational_poly : Poly transposeRational := by
  have hi : Poly (fun input : List (List ℚ) => List.range input.length) := Poly.list_indices
  unfold transposeRational
  exact Poly.list_map (by fun_prop) hi

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule158

/- Helper module Solutions.RegevBridgeRationalInverseRefinement. -/
section P2MDyadicModule159

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open RationalGramSchmidt.Native

open scoped BigOperators

noncomputable section

theorem inputRows_entry_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (row col : Fin n) :
    |B row col|≤ (2 : ℤ)^(integerMatrixTicks (inputRows B)).length :=
  inputColumns_entry_height B.transpose col row

end

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule159

/- Helper module Solutions.RegevBridgeNativeDual. -/
section P2MDyadicModule160

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open scoped BigOperators

noncomputable section

/-- Total matrix interpretation of a finite row-major rational output. -/
def decodeMatrix (n : ℕ) (output : List (List ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  fun row col => (output[row.val]?.getD [])[col.val]?.getD 0

/-- Exact row-major target: inverse transpose of the original integer
matrix after its canonical embedding in the rationals. -/
theorem current_inverse_transpose {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    decodeMatrix n (current (inputRows B))=(Matrix.transpose (fun row col => (B row col : ℚ)))⁻¹ := by
  have hd : decodeMatrix n (current (inputRows B))=(fun row col => dualVector B col row) := by
    ext row col
    simp only [decodeMatrix,current_correct_dual B hdet,List.getElem?_ofFn,row.isLt,col.isLt,
      ↓reduceDIte,Option.getD_some]
  rw [hd]
  symm
  apply Matrix.inv_eq_right_inv
  ext i j
  change (∑ row,(B row i : ℚ)*dualVector B j row)=if i=j then 1 else 0
  calc
    _ = innerQ (dualVector B j) (inputVectors B i) := by
      unfold innerQ inputVectors
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ = _ := dualVector_pairing B hdet j i

end

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule160

/- Helper module Solutions.RegevBridgeBDDCoordinateRounding. -/
section P2MDyadicModule161

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

@[fun_prop] theorem nearestInteger_poly : Poly nearestInteger := by
  unfold nearestInteger
  exact ⟨(show Poly (fun center : ℚ => GaussianRandomizedRounding.Native.anchor (center+1/2)) by fun_prop).program.comp PolyProgram.ratNum⟩

theorem nearestInteger_eq (center : ℚ) : nearestInteger center=⌊center+1/2⌋ := by
  simp only [nearestInteger,GaussianRandomizedRounding.Native.anchor_eq,RationalNumerics.centeredGaussianAnchor,Rat.num_intCast]

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule161

/- Helper module Solutions.RegevBridgeNativeDualQuotient. -/
section P2MDyadicModule162

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open scoped BigOperators

@[local fun_prop] theorem ratDen_poly : Poly Rat.den := ⟨PolyProgram.ratDen⟩

@[local fun_prop] theorem ratNum_poly : Poly Rat.num := ⟨PolyProgram.ratNum⟩

@[local fun_prop] theorem rationalProd_poly : Poly (List.prod : List ℚ → ℚ) := ⟨PolyProgram.ratProd⟩

@[fun_prop] theorem denominators_poly : Poly denominators := by unfold denominators;fun_prop

@[fun_prop] theorem denominator_poly : Poly denominator := by unfold denominator;fun_prop

def integerMatrix (input : List (List ℤ)) : List (List ℤ) :=
  let d := denominator input
  (RationalInverse.Native.current input).map (fun row => row.map (fun value => ((d : ℚ)*value).num))

@[fun_prop] theorem integerMatrix_poly : Poly integerMatrix := by unfold integerMatrix;fun_prop

/-- Signed floor, including negative coordinates, implemented by the
already certified nearest-integer primitive with an exact shift. -/
def floor (value : ℚ) : ℤ := IntegerBasis.nearestInteger (value-1/2)

@[fun_prop] theorem floor_poly : Poly floor := by unfold floor;fun_prop

def quotient (input : List (List ℤ) × List ℤ) : List ℤ :=
  (IntegerBasis.Native.matrixApply (transpose input.1,input.2)).map
    (fun value : ℤ => floor ((value : ℚ)/(denominator input.1 : ℚ)))

@[fun_prop] theorem quotient_poly : Poly quotient := by unfold quotient;fun_prop

def remainder (input : List (List ℤ) × List ℤ) : List ℤ :=
  let translated := IntegerBasis.Native.matrixApply (integerMatrix input.1,quotient input)
  (List.range input.1.length).map (fun row => input.2[row]?.getD 0-translated[row]?.getD 0)

@[fun_prop] theorem remainder_poly : Poly remainder := by
  have hi : Poly (fun input : List (List ℤ) × List ℤ => List.range input.1.length) :=
    Poly.comp (f:=fun matrix : List (List ℤ) => List.range matrix.length)
      (g:=fun input : List (List ℤ) × List ℤ => input.1) Poly.list_indices Poly.fst
  unfold remainder
  exact Poly.list_map (by fun_prop) hi

/-- Forward public integer quotient map. The original basis is retained
by its caller; output consists only of the quotient and remainder. -/
def current (input : List (List ℤ) × List ℤ) : List ℤ × List ℤ := (quotient input,remainder input)

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

def reconstruct (input : List (List ℤ) × (List ℤ × List ℤ)) : List ℤ :=
  let translated := IntegerBasis.Native.matrixApply (integerMatrix input.1,input.2.1)
  (List.range input.1.length).map (fun row => translated[row]?.getD 0+input.2.2[row]?.getD 0)

@[fun_prop] theorem reconstruct_poly : Poly reconstruct := by
  have hi : Poly (fun input : List (List ℤ) × (List ℤ × List ℤ) => List.range input.1.length) :=
    Poly.comp (f:=fun matrix : List (List ℤ) => List.range matrix.length)
      (g:=fun input : List (List ℤ) × (List ℤ × List ℤ) => input.1) Poly.list_indices Poly.fst
  unfold reconstruct
  exact Poly.list_map (by fun_prop) hi

end InfoLossLAR.WorstCase.NativeDualQuotient

end P2MDyadicModule162

/- Helper module Solutions.RegevBridgeNativeDualClearing. -/
section P2MDyadicModule163

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

theorem denominator_eq (input : List (List ℤ)) : denominator input=(denominators input).prod := by
  have hcast : ((denominators input).map (fun value : ℕ => (value : ℚ))).prod=((denominators input).prod : ℚ) := by
    simp
  unfold denominator
  rw [hcast,Rat.num_natCast]
  exact Int.natAbs_natCast _

theorem denominator_pos (input : List (List ℤ)) : 0< denominator input := by
  rw [denominator_eq]
  apply List.prod_pos
  intro d hd
  obtain ⟨row,hr,hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hd
  exact q.den_pos

theorem denominator_divides (input : List (List ℤ)) (q : ℚ)
    (hq : q∈(RationalInverse.Native.current input).flatten) : q.den∣denominator input := by
  rw [denominator_eq]
  apply List.dvd_prod
  obtain ⟨row,hr,hq⟩ := List.mem_flatten.mp hq
  exact List.mem_flatMap.mpr ⟨row,hr,List.mem_map.mpr ⟨q,hq,rfl⟩⟩

/-- Numerator extraction is exact after the actual denominator product;
there is no truncation or approximate rational-to-integer conversion. -/
theorem scaled_num_cast (input : List (List ℤ)) (q : ℚ)
    (hq : q∈(RationalInverse.Native.current input).flatten) :
    (((denominator input : ℚ)*q).num : ℚ)=(denominator input : ℚ)*q := by
  obtain ⟨k,hk⟩ := denominator_divides input q hq
  have hd : (q.den : ℚ)≠0 := by exact_mod_cast q.den_nz
  have he : (denominator input : ℚ)*q=(((k : ℤ)*q.num : ℤ) : ℚ) := by
    calc
      _ = (denominator input : ℚ)*((q.num : ℚ)/(q.den : ℚ)) := by rw [Rat.num_div_den]
      _ = _ := by
        rw [hk,Nat.cast_mul]
        push_cast
        field_simp
  rw [he,Rat.num_intCast]

def cleared {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun row col => (((originalDenominator B : ℚ)*dualVector B col row).num)

theorem integerMatrix_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    integerMatrix (RationalInverse.Native.inputRows B)=List.ofFn (fun row => List.ofFn (cleared B row)) := by
  simp only [integerMatrix,RationalInverse.Native.current_correct_dual B hdet,List.map_ofFn,Function.comp_def]
  rfl

theorem cleared_cast {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (row col : Fin n) :
    (cleared B row col : ℚ)=(originalDenominator B : ℚ)*dualVector B col row := by
  apply scaled_num_cast
  rw [RationalInverse.Native.current_correct_dual B hdet]
  exact List.mem_flatten.mpr ⟨List.ofFn (fun col => dualVector B col row),List.mem_ofFn.mpr ⟨row,rfl⟩,
    List.mem_ofFn.mpr ⟨col,rfl⟩⟩

def dualMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun row col => dualVector B col row

theorem original_mul_dual {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    (Matrix.transpose (fun row col => (B row col : ℚ)))*dualMatrix B=1 := by
  ext i j
  change (∑ row,(B row i : ℚ)*dualVector B j row)=if i=j then 1 else 0
  calc
    _ = innerQ (dualVector B j) (inputVectors B i) := by
      unfold innerQ inputVectors
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ = _ := dualVector_pairing B hdet j i

theorem transpose_mul_cleared {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    B.transpose*cleared B=(originalDenominator B : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  ext row col
  apply Int.cast_injective (α:=ℚ)
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Int.cast_sum,Int.cast_mul,cleared_cast B hdet,
    Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,Int.cast_natCast]
  have h := congrFun (congrFun (original_mul_dual B hdet) row) col
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,dualMatrix] at h
  calc
    _ = (originalDenominator B : ℚ)*(∑ j,(B j row : ℚ)*dualVector B col j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [h];split_ifs <;> norm_num

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end P2MDyadicModule163

/- Helper module Solutions.RegevBridgeNativeDualQuotientSemantics. -/
section P2MDyadicModule164

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

theorem floor_eq (value : ℚ) : floor value=⌊value⌋ := by
  rw [floor,IntegerBasis.nearestInteger_eq]
  congr 1
  ring

def remainderVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) : Fin n → ℤ :=
  v-(cleared B).mulVec (quotientVector B v)

theorem quotient_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    quotient (RationalInverse.Native.inputRows B,List.ofFn v)=List.ofFn (quotientVector B v) := by
  have ht : RationalGramSchmidt.Native.transpose (RationalInverse.Native.inputRows B)=
      List.ofFn (fun row => List.ofFn (B.transpose row)) := by
    rw [RationalInverse.Native.inputRows,RationalGramSchmidt.Native.transpose_input_rows]
    rfl
  rw [quotient,ht,IntegerBasis.Native.matrixApply_ofFn,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact floor_eq _

theorem remainder_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (v : Fin n → ℤ) :
    remainder (RationalInverse.Native.inputRows B,List.ofFn v)=List.ofFn (remainderVector B v) := by
  unfold remainder
  rw [integerMatrix_ofFn B hdet,quotient_ofFn,IntegerBasis.Native.matrixApply_ofFn]
  simp only [RationalInverse.Native.inputRows,List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro row hr hs
    have hrow : row< n := by simpa using hs
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,List.getElem?_ofFn,hrow,
      ↓reduceDIte,Option.getD_some,remainderVector,Pi.sub_apply]

theorem current_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (v : Fin n → ℤ) :
    current (RationalInverse.Native.inputRows B,List.ofFn v)=
      (List.ofFn (quotientVector B v),List.ofFn (remainderVector B v)) := by
  rw [current,quotient_ofFn,remainder_ofFn B hdet]

theorem reconstruct_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (z r : Fin n → ℤ) :
    reconstruct (RationalInverse.Native.inputRows B,(List.ofFn z,List.ofFn r))=
      List.ofFn ((cleared B).mulVec z+r) := by
  unfold reconstruct
  rw [integerMatrix_ofFn B hdet,IntegerBasis.Native.matrixApply_ofFn]
  simp only [RationalInverse.Native.inputRows,List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro row hr hs
    have hrow : row< n := by simpa using hs
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,List.getElem?_ofFn,hrow,
      ↓reduceDIte,Option.getD_some,Pi.add_apply]

/-- The actual inverse native program reconstructs every original integer
input. Thus the original register can be erased after retaining z,r. -/
theorem reconstruct_current {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (v : Fin n → ℤ) :
    reconstruct (RationalInverse.Native.inputRows B,current (RationalInverse.Native.inputRows B,List.ofFn v))=List.ofFn v := by
  rw [current_ofFn B hdet,reconstruct_ofFn B hdet]
  congr 1
  unfold remainderVector
  abel

/-- Coordinates of the retained remainder in the actual scaled dual
basis. These are exact rationals, even for negative ambient grid points. -/
def cellCoordinates {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : Fin n → ℤ) : QVector n :=
  fun i => ((B.transpose.mulVec r) i : ℚ)/(originalDenominator B : ℚ)

def InFundamentalCell {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : Fin n → ℤ) : Prop :=
  ∀ i,0≤ cellCoordinates B r i ∧ cellCoordinates B r i< 1

theorem remainder_coordinates {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (v : Fin n → ℤ) (i : Fin n) :
    cellCoordinates B (remainderVector B v) i=cellCoordinates B v i-(quotientVector B v i : ℚ) := by
  have hd : (originalDenominator B : ℚ)≠0 := by exact_mod_cast (denominator_pos (RationalInverse.Native.inputRows B)).ne'
  have he : B.transpose.mulVec (remainderVector B v)=
      B.transpose.mulVec v-(originalDenominator B : ℤ) • quotientVector B v := by
    rw [remainderVector,Matrix.mulVec_sub,Matrix.mulVec_mulVec,transpose_mul_cleared B hdet]
    simp only [Matrix.smul_mulVec,Matrix.one_mulVec]
  rw [cellCoordinates,he]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  unfold cellCoordinates
  field_simp

theorem remainder_in_cell {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (v : Fin n → ℤ) :
    InFundamentalCell B (remainderVector B v) := by
  intro i
  rw [remainder_coordinates B hdet]
  change 0≤ cellCoordinates B v i-(⌊cellCoordinates B v i⌋ : ℚ) ∧ cellCoordinates B v i-(⌊cellCoordinates B v i⌋ : ℚ)< 1
  constructor
  · exact sub_nonneg.mpr (Int.floor_le _)
  · have h := Int.lt_floor_add_one (cellCoordinates B v i)
    linarith

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end P2MDyadicModule164

/- Helper module Solutions.RegevBridgeNativeDualQuotientGeometry. -/
section P2MDyadicModule165

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

/-- Exact ambient point for the integer remainder, before the public
fine-grid scale is applied. -/
def normalizedPoint {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : Fin n → ℤ) : IntegerBasis.Space (dimension:=n) :=
  realVec (fun row => (r row : ℚ)/(originalDenominator B : ℚ))

def residuePoint {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ) (r : Fin n → ℤ) : IntegerBasis.Space (dimension:=n) :=
  R⁻¹ • normalizedPoint B r

theorem residuePoint_eq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ) (r : Fin n → ℤ) :
    residuePoint B R r=(R*(originalDenominator B : ℝ))⁻¹ • intVecE r := by
  ext row
  simp only [residuePoint,normalizedPoint,realVec,intVecE,WithLp.ofLp_smul,WithLp.ofLp_toLp,
    Pi.smul_apply,smul_eq_mul,Rat.cast_div,Rat.cast_mul,Rat.cast_inv,Rat.cast_intCast,Rat.cast_natCast,mul_inv_rev,div_eq_mul_inv]
  ring

theorem normalized_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (r : Fin n → ℤ) (i : Fin n) :
    inner ℝ (normalizedPoint B r) (IntegerBasis.realBasis B hdet i)=(cellCoordinates B r i : ℝ) := by
  rw [←inputVectors_real B hdet i]
  change inner ℝ (realVec _) (realVec _)=_
  rw [←innerQ_real]
  apply congrArg (fun value : ℚ => (value : ℝ))
  simp only [innerQ,inputVectors,cellCoordinates,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
    Int.cast_sum,Int.cast_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- Full remainder vector decomposition in the original dual columns. -/
theorem normalizedPoint_decomposition {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (r : Fin n → ℤ) :
    normalizedPoint B r=∑ i,(cellCoordinates B r i : ℝ) • IntegerBasis.dualRealBasis B hdet i := by
  apply real_pairings_unique B hdet
  intro k
  rw [normalized_pairing B hdet,sum_inner]
  have hd (i : Fin n) : inner ℝ (IntegerBasis.dualRealBasis B hdet i) (IntegerBasis.realBasis B hdet k)=if k=i then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left IntegerBasis.inner_nondegenerate (IntegerBasis.realBasis B hdet) i k
  simp only [real_inner_smul_left]
  simp_rw [hd]
  simp

/-- The quotient's retained remainder lies in the actual dual fundamental
parallelotope divided by R, with a complete Euclidean norm bound. -/
theorem remainder_norm_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (R : ℝ) (hR : 0< R) (v : Fin n → ℤ) :
    ‖residuePoint B R (remainderVector B v)‖≤ (∑ i,‖IntegerBasis.dualRealBasis B hdet i‖)/R := by
  have hc := remainder_in_cell B hdet v
  have hs : ‖normalizedPoint B (remainderVector B v)‖≤∑ i,‖IntegerBasis.dualRealBasis B hdet i‖ := by
    rw [normalizedPoint_decomposition B hdet]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have hi0 : (0 : ℝ)≤ cellCoordinates B (remainderVector B v) i := by exact_mod_cast (hc i).1
    have hi1 : (cellCoordinates B (remainderVector B v) i : ℝ)≤1 := by exact_mod_cast (hc i).2.le
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hi0]
    nlinarith [norm_nonneg (IntegerBasis.dualRealBasis B hdet i)]
  rw [residuePoint,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  calc
    _ ≤ R⁻¹*(∑ i,‖IntegerBasis.dualRealBasis B hdet i‖) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hR.le)
    _ = _ := by ring

/-- Canonical pairs recover the same quotient under the native inverse,
so the two public programs form a bijection onto the retained cell. -/
theorem quotientVector_reconstruct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (z r : Fin n → ℤ) (hr : InFundamentalCell B r) :
    quotientVector B ((cleared B).mulVec z+r)=z := by
  have hd : (originalDenominator B : ℚ)≠0 := by exact_mod_cast (denominator_pos (RationalInverse.Native.inputRows B)).ne'
  have he : B.transpose.mulVec ((cleared B).mulVec z+r)=
      (originalDenominator B : ℤ) • z+B.transpose.mulVec r := by
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,transpose_mul_cleared B hdet]
    simp only [Matrix.smul_mulVec,Matrix.one_mulVec]
  funext i
  rw [quotientVector,he]
  have hy : (((originalDenominator B : ℤ) • z+B.transpose.mulVec r) i : ℚ)/(originalDenominator B : ℚ)=
      (z i : ℚ)+cellCoordinates B r i := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Int.cast_add,Int.cast_mul,Int.cast_natCast,cellCoordinates]
    field_simp
  rw [hy]
  apply Int.floor_eq_iff.mpr
  constructor
  · have h := (hr i).1
    linarith
  · have h := (hr i).2
    linarith

theorem remainderVector_reconstruct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (z r : Fin n → ℤ) (hr : InFundamentalCell B r) :
    remainderVector B ((cleared B).mulVec z+r)=r := by
  rw [remainderVector,quotientVector_reconstruct B hdet z r hr]
  abel

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end P2MDyadicModule165

/- Helper module Solutions.RegevBridgeNativeDualQuotientTransport. -/
section P2MDyadicModule166

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

theorem normalizedPoint_add {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) :
    normalizedPoint B (x+y)=normalizedPoint B x+normalizedPoint B y := by
  ext row
  simp [normalizedPoint,realVec,Int.cast_add,add_div]

theorem cellCoordinates_cleared {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (z : Fin n → ℤ) (i : Fin n) :
    cellCoordinates B ((cleared B).mulVec z) i=(z i : ℚ) := by
  have hd : (originalDenominator B : ℚ)≠0 := by exact_mod_cast (denominator_pos (RationalInverse.Native.inputRows B)).ne'
  rw [cellCoordinates,Matrix.mulVec_mulVec,transpose_mul_cleared B hdet]
  simp only [Matrix.smul_mulVec,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul,Int.cast_mul,Int.cast_natCast]
  field_simp

theorem normalizedPoint_cleared {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (z : Fin n → ℤ) :
    normalizedPoint B ((cleared B).mulVec z)=IntegerBasis.dualCoordinates B hdet z := by
  rw [normalizedPoint_decomposition B hdet,IntegerBasis.dualCoordinates_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [cellCoordinates_cleared B hdet]
  simp only [Rat.cast_intCast,Int.cast_smul_eq_zsmul]

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end P2MDyadicModule166

/- Helper module Solutions.RegevBridgeNativeDualQuotientEquiv. -/
section P2MDyadicModule167

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open RationalGramSchmidt RationalInverse RegevLWE.GaussConv

open GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

theorem residual_in_cell {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : Residual B) : InFundamentalCell B r.val := by
  intro i
  have hi := congrFun r.property i
  change ⌊cellCoordinates B r.val i⌋=(0 : ℤ) at hi
  simpa using Int.floor_eq_iff.mp hi

theorem remainder_quotient_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (v : Fin n → ℤ) :
    quotientVector B (remainderVector B v)=0 := by
  simpa only [Matrix.mulVec_zero,zero_add] using
    quotientVector_reconstruct B hdet 0 (remainderVector B v) (remainder_in_cell B hdet v)

def integerPointsEquiv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    (Fin n → ℤ) ≃ Residual B × (Fin n → ℤ) where
  toFun v := (⟨remainderVector B v,remainder_quotient_zero B hdet v⟩,quotientVector B v)
  invFun pair := (cleared B).mulVec pair.2+pair.1.val
  left_inv v := by unfold remainderVector;module
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      exact remainderVector_reconstruct B hdet pair.2 pair.1.val (residual_in_cell B pair.1)
    · exact quotientVector_reconstruct B hdet pair.2 pair.1.val (residual_in_cell B pair.1)

def Gamma {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (R : ℝ) (hR : 0< R) :
    Submodule ℤ (IntegerBasis.Space (dimension:=n)) :=
  GaussianLatticeTransport.imageLattice (dual (IntegerBasis.inputLattice B hdet)) (dilation R⁻¹ (inv_pos.mpr hR))

def gammaIntegerEquiv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (R : ℝ) (hR : 0< R) :
    (Fin n → ℤ) ≃ Gamma B hdet R hR :=
  (IntegerBasis.dualIntegerEquiv B hdet).toEquiv.trans
    (imageEquiv _ (dilation R⁻¹ (inv_pos.mpr hR)))

@[simp] theorem gammaIntegerEquiv_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (R : ℝ) (hR : 0< R) (z : Fin n → ℤ) :
    (gammaIntegerEquiv B hdet R hR z : IntegerBasis.Space (dimension:=n))=R⁻¹ • IntegerBasis.dualCoordinates B hdet z := rfl

def Ambient {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ) (hR : 0< R) :
    Submodule ℤ (IntegerBasis.Space (dimension:=n)) :=
  GaussianLatticeTransport.imageLattice (IntegerBasis.inputLattice (1 : Matrix (Fin n) (Fin n) ℤ) (by simp))
    (dilation (R*(originalDenominator B : ℝ))⁻¹ (by
      apply inv_pos.mpr
      exact mul_pos hR (by exact_mod_cast denominator_pos (RationalInverse.Native.inputRows B))))

def ambientIntegerEquiv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ) (hR : 0< R) :
    (Fin n → ℤ) ≃ Ambient B R hR :=
  ((IntegerBasis.integerBasis (1 : Matrix (Fin n) (Fin n) ℤ) (by simp)).equivFun.symm.toEquiv).trans
    (imageEquiv _ (dilation (R*(originalDenominator B : ℝ))⁻¹ (by
      apply inv_pos.mpr
      exact mul_pos hR (by exact_mod_cast denominator_pos (RationalInverse.Native.inputRows B)))))

theorem ambientIntegerEquiv_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ) (hR : 0< R) (v : Fin n → ℤ) :
    (ambientIntegerEquiv B R hR v : IntegerBasis.Space (dimension:=n))=residuePoint B R v := by
  change (R*(originalDenominator B : ℝ))⁻¹ •
    ((IntegerBasis.integerBasis (1 : Matrix (Fin n) (Fin n) ℤ) (by simp)).equivFun.symm v : IntegerBasis.Space (dimension:=n))=_
  rw [IntegerBasis.coefficient_point,residuePoint_eq]
  simp only [latVec,Matrix.one_mulVec,intVecE]

/-- The actual integer quotient gives an equivalence of the complete
ambient fine grid with retained residues and the actual scaled dual lattice. -/
def ambientCosetEquiv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (R : ℝ) (hR : 0< R) :
    Ambient B R hR ≃ Residual B × Gamma B hdet R hR :=
  (ambientIntegerEquiv B R hR).symm.trans ((integerPointsEquiv B hdet).trans
    (Equiv.prodCongr (Equiv.refl _) (gammaIntegerEquiv B hdet R hR)))

/-- The inverse pair has exactly gamma-point plus retained-residue
physical semantics, as required by complete Gaussian coset factorization. -/
theorem ambientCosetEquiv_symm_point {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (R : ℝ) (hR : 0< R) (r : Residual B) (g : Gamma B hdet R hR) :
    ((ambientCosetEquiv B hdet R hR).symm (r,g) : IntegerBasis.Space (dimension:=n))=
      (g : IntegerBasis.Space (dimension:=n))+residuePoint B R r.val := by
  let z := (gammaIntegerEquiv B hdet R hR).symm g
  change (ambientIntegerEquiv B R hR ((cleared B).mulVec z+r.val) : IntegerBasis.Space (dimension:=n))=_
  rw [ambientIntegerEquiv_apply,residuePoint,normalizedPoint_add,normalizedPoint_cleared B hdet,smul_add]
  have hg := congrArg (fun point : Gamma B hdet R hR => (point : IntegerBasis.Space (dimension:=n)))
    ((gammaIntegerEquiv B hdet R hR).apply_symm_apply g)
  rw [gammaIntegerEquiv_apply] at hg
  exact congrArg (fun point => point+R⁻¹ • normalizedPoint B r.val) hg

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end P2MDyadicModule167

/- Helper module Solutions.RegevBridgeLatticeGaussianTail. -/
section P2MDyadicModule168

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Actual Gaussian mass outside the specified Euclidean ball. -/
def gaussianTail (lattice : Submodule ℤ (Space (dimension:=dimension))) (width radius : ℝ) : ℝ :=
  ∑' point : lattice,if radius ≤ ‖(point : Space (dimension:=dimension))‖ then
    rho width (point : Space (dimension:=dimension)) else 0

/-- Comparing a Gaussian with its doubled width pays an explicit radial
exponential factor, point by point. -/
theorem rho_tail_point (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (point : Space (dimension:=dimension)) (hpoint : radius≤‖point‖) :
    rho width point ≤ Real.exp (-3*Real.pi*radius^2/(4*width^2))*rho (2*width) point := by
  unfold rho
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hnorm : radius^2 ≤ ‖point‖^2 := (sq_le_sq₀ hradius (norm_nonneg point)).mpr hpoint
  have hden : 0<4*width^2 := by positivity
  apply (mul_le_mul_iff_of_pos_right hden).mp
  field_simp
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hnorm)]

/-- An unconditional full lattice Gaussian tail bound, relative to its
actual normalizer. No smoothing hypothesis is required. -/
theorem gaussianTail_le (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius) :
    gaussianTail lattice width radius ≤
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*(2 : ℝ)^dimension*rhoCoset width lattice 0 := by
  classical
  let function : lattice → ℝ := fun point =>
    if radius ≤ ‖(point : Space (dimension:=dimension))‖ then rho width (point : Space (dimension:=dimension)) else 0
  have hs := summable_gaussian_lattice lattice width hwidth
  have hfiltered : Summable function := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro point
      dsimp only [function]
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    · intro point
      dsimp only [function]
      split_ifs
      · exact le_rfl
      · exact (Real.exp_pos _).le
  have hdoubled := summable_gaussian_lattice lattice (2*width) (by positivity)
  have hpointwise (point : lattice) : function point ≤
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*rho (2*width) (point : Space (dimension:=dimension)) := by
    dsimp only [function]
    split_ifs with hpoint
    · exact rho_tail_point width radius hwidth hradius (point : Space (dimension:=dimension)) hpoint
    · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hsumBound := hfiltered.tsum_le_tsum hpointwise (hdoubled.mul_left
    (Real.exp (-3*Real.pi*radius^2/(4*width^2))))
  have hsumExact : (∑' point : lattice,
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*rho (2*width) (point : Space (dimension:=dimension)))=
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*rhoCoset (2*width) lattice 0 := by
    rw [tsum_mul_left]
    simp only [rhoCoset,add_zero]
  have hfirst : gaussianTail lattice width radius ≤
      Real.exp (-3*Real.pi*radius^2/(4*width^2))*rhoCoset (2*width) lattice 0 :=
    hsumBound.trans_eq hsumExact
  exact hfirst.trans (by
    have hmass := rhoCoset_dilation_le lattice width 2 hwidth (by norm_num)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le)

/-- The explicit dimensional tail factor is exponentially small at the
usual sqrt(dimension)-times-width radius. -/
theorem radial_factor_le_quarter_pow :
    Real.exp (-3*Real.pi*(dimension : ℝ)/4)*(2 : ℝ)^dimension ≤ (1/4 : ℝ)^dimension := by
  have hexponent : -3*Real.pi/4 ≤ -(Real.log 2+Real.log 2+Real.log 2) := by
    linarith [Real.pi_gt_three,Real.log_two_lt_d9]
  have hbase : Real.exp (-3*Real.pi/4) ≤ (1/8 : ℝ) := by
    have h := Real.exp_le_exp.mpr hexponent
    simpa only [Real.exp_neg,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2),mul_one,one_div,show (2 : ℝ)*2*2=8 by norm_num] using h
  have hpower := pow_le_pow_left₀ (Real.exp_pos _).le hbase dimension
  have hexp : Real.exp (-3*Real.pi*(dimension : ℝ)/4)=Real.exp (-3*Real.pi/4)^dimension := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ ≤ (1/8 : ℝ)^dimension*(2 : ℝ)^dimension :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = (1/4 : ℝ)^dimension := by rw [←mul_pow];norm_num

/-- In particular, the actual relative outside mass is at most 4^-n when
the squared radius is at least n times the squared Gaussian width. -/
theorem gaussianTail_le_quarter_pow (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (hscale : (dimension : ℝ)*width^2 ≤ radius^2) :
    gaussianTail lattice width radius ≤ (1/4 : ℝ)^dimension*rhoCoset width lattice 0 := by
  have hmass : 0 ≤ rhoCoset width lattice 0 := tsum_nonneg (fun point => (Real.exp_pos _).le)
  have hexponent : -3*Real.pi*radius^2/(4*width^2) ≤ -3*Real.pi*(dimension : ℝ)/4 := by
    apply (div_le_iff₀ (by positivity : 0<4*width^2)).mpr
    have h := mul_le_mul_of_nonneg_left hscale (by positivity : 0≤3*Real.pi)
    nlinarith
  have hfactor := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent)
    (by positivity : (0 : ℝ)≤2^dimension)
  have hfinal := hfactor.trans (radial_factor_le_quarter_pow (dimension:=dimension))
  exact (gaussianTail_le lattice width radius hwidth hradius).trans
    (mul_le_mul_of_nonneg_right hfinal hmass)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule168

/- Helper module Solutions.RegevBridgePeriodizedTailBound. -/
section P2MDyadicModule169

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

theorem summable_filtered_nonnegative {Index : Type*} (weight : Index → ℝ)
    (hsummable : Summable weight) (hnonnegative : ∀ point,0≤weight point) (predicate : Index → Prop)
    [DecidablePred predicate] : Summable (fun point => if predicate point then weight point else 0) := by
  apply Summable.of_nonneg_of_le _ _ hsummable
  · intro point;split_ifs <;> simp [hnonnegative]
  · intro point;split_ifs <;> simp [hnonnegative]

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule169

/- Helper module Solutions.RegevBridgeSharpSmoothingParameters. -/
section P2MDyadicModule170

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

/-- A logarithmic smoothing factor. The harmless absolute constant four
keeps every geometric-tail denominator uniformly bounded below. -/
def shortSmoothingFactor (dimension : ℕ) (error : ℝ) : ℝ :=
  Real.sqrt (Real.log (4*(dimension : ℝ)*(1+1/error))/Real.pi)

theorem smoothing_log_arg_gt_one (dimension : ℕ) (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    1 < 4*(dimension : ℝ)*(1+1/error) := by
  have hdimensionReal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
  have hinverse : 0 < 1/error := one_div_pos.mpr herror
  nlinarith [mul_nonneg (show (0 : ℝ)≤dimension by positivity) hinverse.le]

theorem shortSmoothingFactor_pos (dimension : ℕ) (error : ℝ) (hdimension : 0 < dimension) (herror : 0 < error) :
    0 < shortSmoothingFactor dimension error := by
  apply Real.sqrt_pos.mpr
  exact div_pos (Real.log_pos (smoothing_log_arg_gt_one dimension error hdimension herror)) Real.pi_pos

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule170

/- Helper module Solutions.RegevBridgeNativeGaussianSmoothing. -/
section P2MDyadicModule171

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection IntegerBasis NativeDualQuotient

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem dual_dual_input (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    dual (dual (inputLattice basis hdet))=inputLattice basis hdet := by
  have hsymm : LinearMap.BilinForm.IsSymm (innerₗ (Space (dimension:=dimension))) := by
    constructor
    intro first second
    simpa only [innerₗ_apply_apply] using (real_inner_comm first second).symm
  exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis
    (innerₗ (Space (dimension:=dimension))) IntegerBasis.inner_nondegenerate hsymm (realBasis basis hdet)

instance nativeGamma_discrete (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (scale : ℝ) (hscale : 0 < scale) : DiscreteTopology (Gamma basis hdet scale hscale) := by
  unfold Gamma
  infer_instance

instance nativeGamma_full_rank (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (scale : ℝ) (hscale : 0 < scale) : IsZLattice ℝ (Gamma basis hdet scale hscale) := by
  unfold Gamma
  infer_instance

instance nativeAmbient_discrete (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (scale : ℝ) (hscale : 0 < scale) : DiscreteTopology (Ambient basis scale hscale) := by
  unfold Ambient
  infer_instance

instance nativeAmbient_full_rank (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (scale : ℝ) (hscale : 0 < scale) : IsZLattice ℝ (Ambient basis scale hscale) := by
  unfold Ambient
  infer_instance

def dualColumnBudget (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) : ℝ :=
  1+∑ index,‖dualRealBasis basis hdet index‖

theorem dualColumnBudget_pos (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    0 < dualColumnBudget basis hdet := by
  have hsum : 0 ≤ ∑ index,‖dualRealBasis basis hdet index‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  dsimp only [dualColumnBudget]
  linarith

/-- The actual scaled-dual fine lattice meets a public original-dual-column
smoothing budget. No efficiently chosen short basis is assumed. -/
theorem nativeGamma_smoothing_columnBudget
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (scale error : ℝ) (hscale : 0 < scale) (hdimension : 0 < dimension) (herror : 0 < error) :
    smoothingParam (Gamma basis hdet scale hscale) error ≤
      shortSmoothingFactor dimension error*dualColumnBudget basis hdet/scale := by
  let source := dual (inputLattice basis hdet)
  letI : DiscreteTopology (dual source) := by change DiscreteTopology (dual (dual (inputLattice basis hdet)));rw [dual_dual_input];infer_instance
  letI : IsZLattice ℝ (dual source) := by
    change IsZLattice ℝ (dual (dual (inputLattice basis hdet)))
    simpa only [dual_dual_input] using (inferInstance : IsZLattice ℝ (inputLattice basis hdet))
  let directions : Fin dimension → source := fun index =>
    ⟨dualRealBasis basis hdet index,by
      change dualRealBasis basis hdet index ∈ dual (inputLattice basis hdet)
      rw [dual_lattice_eq_span]
      exact Submodule.subset_span ⟨index,rfl⟩⟩
  have hindependent : LinearIndependent ℝ (fun index => (directions index : Space (dimension:=dimension))) :=
    (dualRealBasis basis hdet).linearIndependent
  have hbound (index : Fin dimension) : ‖(directions index : Space (dimension:=dimension))‖ ≤ dualColumnBudget basis hdet := by
    have h := Finset.single_le_sum (fun other (_ : other ∈ Finset.univ) => norm_nonneg (dualRealBasis basis hdet other)) (Finset.mem_univ index)
    change ‖dualRealBasis basis hdet index‖ ≤ _
    dsimp only [dualColumnBudget]
    linarith
  have hsource := InfoLossLAR.WorstCase.RegevSketch.smoothing_le_short_independent source directions hindependent (dualColumnBudget basis hdet) error
    hdimension (dualColumnBudget_pos basis hdet) herror hbound
  have hwidth := mul_pos (shortSmoothingFactor_pos dimension error hdimension herror) (dualColumnBudget_pos basis hdet)
  have h := dilation_smoothing_le source (scale⁻¹) (shortSmoothingFactor dimension error*dualColumnBudget basis hdet) error
    (inv_pos.mpr hscale) hwidth herror hsource
  simpa only [Gamma,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule171

/- Helper module Solutions.RegevBridgeHilbertReindex. -/
section P2MDyadicModule172

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

/-- An actual label bijection transports the complete countable amplitude
vector without discarding any label or changing any Hilbert norm. -/
def hilbertReindex {First Second : Type*} (equivalence : First ≃ Second) (value : Hilbert First) : Hilbert Second := by
  refine ⟨fun second => value (equivalence.symm second),?_⟩
  apply memℓp_gen
  have hs : Summable (fun first => ‖value first‖^2) := by
    simpa using (lp.memℓp value).summable (by norm_num)
  simpa only [Function.comp_def,ENNReal.toReal_ofNat,Real.rpow_two] using equivalence.symm.summable_iff.mpr hs

theorem hilbertReindex_apply {First Second : Type*} (equivalence : First ≃ Second) (value : Hilbert First) (second : Second) :
    hilbertReindex equivalence value second=value (equivalence.symm second) := rfl

theorem hilbertReindex_norm {First Second : Type*} (equivalence : First ≃ Second) (value : Hilbert First) :
    ‖hilbertReindex equivalence value‖=‖value‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hilbert_norm_sq,hilbert_norm_sq]
  exact equivalence.symm.tsum_eq (fun first => ‖value first‖^2)

/-- Full norm and amplitude preservation for any exact reversible quotient
encoding, irrespective of its number of represented lattice points. -/
def hilbertReindexIsometry {First Second : Type*} (equivalence : First ≃ Second) : Hilbert First ≃ₗᵢ[ℂ] Hilbert Second where
  toFun := hilbertReindex equivalence
  invFun := hilbertReindex equivalence.symm
  left_inv value := by ext first;simp only [hilbertReindex_apply,Equiv.symm_symm,Equiv.symm_apply_apply]
  right_inv value := by ext second;simp only [hilbertReindex_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  map_add' first second := by ext index;rfl
  map_smul' scalar value := by ext index;rfl
  norm_map' := hilbertReindex_norm equivalence

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule172

/- Helper module Solutions.RegevBridgeAmbientGaussianProduct. -/
section P2MDyadicModule173

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv NativeDualQuotient GaussianRandomizedRounding AFT.GaussianSource

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Actual ambient-grid Gaussian weights factor in the original integer
coordinate register. The coordinate width may be exponentially large. -/
theorem nativeAmbient_weight_product
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (scale width : ℝ)
    (hscale : 0 < scale) (hwidth : 0 < width) (word : Fin dimension → ℤ) :
    rho width (ambientIntegerEquiv basis scale hscale word : IntegerBasis.Space (dimension:=dimension))=
      finiteProductMass dimension (shiftedWeight (width*scale*(originalDenominator basis : ℝ)) 0) word := by
  have hD : (0 : ℝ) < originalDenominator basis := by exact_mod_cast denominator_pos (RationalInverse.Native.inputRows basis)
  rw [ambientIntegerEquiv_apply,residuePoint_eq,rho,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    EuclideanSpace.real_norm_sq_eq]
  dsimp only [finiteProductMass,shiftedWeight]
  rw [←Real.exp_sum]
  congr 1
  simp only [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro row _
  simp only [intVecE,WithLp.ofLp_toLp,sub_zero]
  field_simp

/-- Full normalization of the actual ambient Gaussian is the product of
the complete one-coordinate theta normalizers. -/
theorem nativeAmbient_normalizer_product
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (scale width : ℝ)
    (hscale : 0 < scale) (hwidth : 0 < width) :
    rhoCoset width (Ambient basis scale hscale) 0=
      (theta (width*scale*(originalDenominator basis : ℝ)) 0)^dimension := by
  have hD : (0 : ℝ) < originalDenominator basis := by exact_mod_cast denominator_pos (RationalInverse.Native.inputRows basis)
  have hs : 0 < width*scale*(originalDenominator basis : ℝ) := by positivity
  unfold rhoCoset
  rw [←(ambientIntegerEquiv basis scale hscale).tsum_eq]
  simp_rw [add_zero,nativeAmbient_weight_product basis scale width hscale hwidth]
  exact (finiteProductMass_hasSum dimension _ (fun _ => Real.exp_nonneg _)
    (summable_shiftedWeight _ 0 hs)).tsum_eq

/-- The exact center-zero product preparation is the actual ambient lattice
Gaussian pure state after the verified integer-coordinate bijection. -/
theorem nativeAmbient_product_state
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (scale width : ℝ)
    (hscale : 0 < scale) (hwidth : 0 < width) :
    hilbertReindex (ambientIntegerEquiv basis scale hscale)
      (integerGaussianProductState dimension (width*scale*(originalDenominator basis : ℝ)) (by
        have hD : (0 : ℝ) < originalDenominator basis := by exact_mod_cast denominator_pos (RationalInverse.Native.inputRows basis)
        positivity))=
      gaussianHilbertState (Ambient basis scale hscale) width hwidth 0 := by
  have hD : (0 : ℝ) < originalDenominator basis := by exact_mod_cast denominator_pos (RationalInverse.Native.inputRows basis)
  have hs : 0 < width*scale*(originalDenominator basis : ℝ) := by positivity
  ext point
  obtain ⟨word,rfl⟩ := (ambientIntegerEquiv basis scale hscale).surjective point
  rw [hilbertReindex_apply,Equiv.symm_apply_apply,gaussianHilbertState_apply]
  change (Real.sqrt (integerGaussianProductMass dimension _ _ word) : ℂ)=_
  apply Complex.ofReal_inj.mpr
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (gaussianAmplitude_nonneg _ _ _ _)).mp
  rw [Real.sq_sqrt (integerGaussianProductMass_nonnegative _ _ _ _),gaussianAmplitude_sq (Ambient basis scale hscale) width hwidth 0 _,add_zero,
    nativeAmbient_weight_product basis scale width hscale hwidth,nativeAmbient_normalizer_product basis scale width hscale hwidth]
  simp only [integerGaussianProductMass,finiteProductMass,roundingPMF_toReal,Finset.prod_div_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule173

/- Helper module Solutions.RegevBridgeHilbertProjection. -/
section P2MDyadicModule174

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

/-- Literal truncation in the complete countable Hilbert space. -/
def hilbertProject {Index : Type*} (event : Index → Prop) [DecidablePred event] (value : Hilbert Index) : Hilbert Index := by
  refine ⟨fun index => if event index then value index else 0,?_⟩
  apply memℓp_gen
  have hs : Summable (fun index => ‖value index‖^2) := by
    simpa using (lp.memℓp value).summable (by norm_num)
  have hfiltered : Summable (fun index => if event index then ‖value index‖^2 else 0) :=
    summable_filtered_nonnegative _ hs (fun index => sq_nonneg _) event
  have hterm (index : Index) : ‖(if event index then value index else 0)‖^2=
      (if event index then ‖value index‖^2 else 0) := by
    split_ifs <;> simp
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,hterm] using hfiltered

theorem hilbertProject_apply {Index : Type*} (event : Index → Prop) [DecidablePred event]
    (value : Hilbert Index) (index : Index) : hilbertProject event value index=(if event index then value index else 0) := rfl

/-- Full countable truncation has exactly its omitted Gaussian square mass
as squared Hilbert error. -/
theorem hilbertProject_error_sq {Index : Type*} (event : Index → Prop) [DecidablePred event] (value : Hilbert Index) :
    ‖value-hilbertProject event value‖^2=∑' index,if event index then 0 else ‖value index‖^2 := by
  rw [hilbert_norm_sq]
  apply tsum_congr
  intro index
  rw [lp.coeFn_sub,Pi.sub_apply,hilbertProject_apply]
  split_ifs <;> simp

/-- An actual finite cutoff can be compared to the complete normalized
pure state without losing or postselecting the omitted branch silently. -/
theorem normalized_hilbertProject_close {Index : Type*} (event : Index → Prop) [DecidablePred event]
    (value : Hilbert Index) (hvalue : ‖value‖=1) (hproject : hilbertProject event value≠0) (error : ℝ)
    (htail : (∑' index,if event index then 0 else ‖value index‖^2) ≤ error) :
    ‖value-CoherentProjection.normalized (hilbertProject event value)‖ ≤ 2*Real.sqrt error := by
  have herror : 0 ≤ error := (tsum_nonneg (fun index => by split_ifs;exact le_rfl;exact sq_nonneg _)).trans htail
  have hnorm : ‖value-hilbertProject event value‖ ≤ Real.sqrt error := by
    apply (Real.le_sqrt (norm_nonneg _) herror).mpr
    rw [hilbertProject_error_sq]
    exact htail
  exact (CoherentProjection.normalized_close value _ hvalue hproject).trans
    (mul_le_mul_of_nonneg_left hnorm (by norm_num))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule174

/- Helper module Solutions.RegevBridgeFiniteHilbertProjection. -/
section P2MDyadicModule175

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped Classical

noncomputable section

variable {FiniteIndex Index : Type*} [Fintype FiniteIndex]

/-- Literal finite-coordinate restriction and injective embedding equal
the actual full Hilbert projection, including all outside zeros. -/
theorem finiteEmbed_restrict (embedding : FiniteIndex ↪ Index) (value : Hilbert Index) :
    finiteEmbed embedding (finiteRestrict embedding value)=
      hilbertProject (fun index => index ∈ Set.range embedding) value := by
  classical
  ext index
  by_cases hindex : index ∈ Set.range embedding
  · obtain ⟨source,rfl⟩ := hindex
    rw [finiteEmbed_apply,hilbertProject_apply,if_pos ⟨source,rfl⟩]
    rfl
  · rw [finiteEmbed_apply_not_mem embedding _ index hindex,hilbertProject_apply,if_neg hindex]

theorem finiteEmbed_real_smul (embedding : FiniteIndex ↪ Index) (scalar : ℝ) (value : EuclideanSpace ℂ FiniteIndex) :
    finiteEmbed embedding (scalar • value)=scalar • finiteEmbed embedding value := by
  classical
  simp only [finiteEmbed,PiLp.smul_apply,lp.single_smul,Finset.smul_sum]

/-- Normalization commutes with the true finite-to-countable isometry. -/
theorem finiteEmbed_normalized (embedding : FiniteIndex ↪ Index) (value : EuclideanSpace ℂ FiniteIndex) :
    finiteEmbed embedding (CoherentProjection.normalized value)=
      CoherentProjection.normalized (finiteEmbed embedding value) := by
  rw [CoherentProjection.normalized,finiteEmbed_real_smul,CoherentProjection.normalized,finiteEmbed_norm]

/-- The normalized finite Gaussian restriction represents exactly the
normalized genuine complete-space projection. -/
theorem finiteEmbed_normalized_restrict (embedding : FiniteIndex ↪ Index) (value : Hilbert Index) :
    finiteEmbed embedding (CoherentProjection.normalized (finiteRestrict embedding value))=
      CoherentProjection.normalized (hilbertProject (fun index => index ∈ Set.range embedding) value) := by
  rw [finiteEmbed_normalized,finiteEmbed_restrict]

/-- Finite cutoff error is measured in the complete Hilbert space after
actual injective physical encoding, with no change in norm budget. -/
theorem finite_restriction_close (embedding : FiniteIndex ↪ Index) (value : Hilbert Index) (hvalue : ‖value‖=1)
    (hprojection : hilbertProject (fun index => index ∈ Set.range embedding) value≠0) (tail : ℝ)
    (htail : (∑' index,if index ∈ Set.range embedding then 0 else ‖value index‖^2) ≤ tail) :
    ‖value-finiteEmbed embedding (CoherentProjection.normalized (finiteRestrict embedding value))‖ ≤ 2*Real.sqrt tail := by
  rw [finiteEmbed_normalized_restrict]
  exact normalized_hilbertProject_close _ value hvalue hprojection tail htail

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule175

/- Helper module RectParallel. -/
section P2MDyadicModule176

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource

open QAlgorithms QAlgorithms.Complexity CoherentProjection CoherentComputeUncompute

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] {w : ℕ}

def embedding (e : I × J ↪ Bits w) (n : ℕ) :
    ((Fin n → I) × (Fin n → J)) ↪ Bits (CoherentParallelTrials.width w n) where
  toFun u := (CoherentParallelTrials.coordinates w n).symm (fun i => e (u.1 i,u.2 i))
  inj' := by
    rintro ⟨s,t⟩ ⟨v,y⟩ he
    have h := (CoherentParallelTrials.coordinates w n).symm.injective he
    exact Prod.ext (funext (fun i => congrArg Prod.fst (e.injective (congrFun h i))))
      (funext (fun i => congrArg Prod.snd (e.injective (congrFun h i))))

def pack (e : I × J ↪ Bits w) (ψ : EuclideanSpace ℂ I) (χ : EuclideanSpace ℂ J) :
    EuclideanSpace ℂ (Bits w) := WithLp.toLp 2 (basisEmbedding e (CoherentProjection.tensorState ψ χ))

theorem pack_norm (e : I × J ↪ Bits w) (ψ : EuclideanSpace ℂ I) (χ : EuclideanSpace ℂ J) :
    ‖pack e ψ χ‖ = ‖ψ‖ * ‖χ‖ := (basisEmbedding_norm _ _).trans (tensorState_norm _ _)

theorem unpack (e : I × J ↪ Bits w) (ψ : EuclideanSpace ℂ I) (χ : EuclideanSpace ℂ J)
    (n : ℕ) (z : Bits (CoherentParallelTrials.width w n)) :
    pack (embedding e n) (repeatState n ψ) (repeatState n χ) z =
      repeatState n (pack e ψ χ) (CoherentParallelTrials.coordinates w n z) := by
  classical
  by_cases hz : z ∈ Set.range (embedding e n)
  · obtain ⟨⟨v,y⟩,rfl⟩ := hz
    change basisEmbedding _ _ ((embedding e n) _) = _
    rw [basisEmbedding_at]
    simp only [embedding,Function.Embedding.coeFn_mk,Equiv.apply_symm_apply,repeatState,
      CoherentProjection.tensorState,pack,basisEmbedding_at,Finset.prod_mul_distrib]
  · change basisEmbedding _ _ _ = _
    rw [basisEmbedding_outside _ _ _ hz]
    have he : ∃ i,CoherentParallelTrials.coordinates w n z i ∉ Set.range e := by
      by_contra! h
      choose a ha using h
      apply hz
      refine ⟨(fun i => (a i).1,fun i => (a i).2),?_⟩
      apply (CoherentParallelTrials.coordinates w n).injective
      change (CoherentParallelTrials.coordinates w n) ((CoherentParallelTrials.coordinates w n).symm _) = _
      rw [Equiv.apply_symm_apply]
      funext i
      exact ha i
    obtain ⟨i,hi⟩ := he
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (basisEmbedding_outside e _ _ hi)).symm

theorem initial_basis (n : ℕ) (x : Bits w) :
    CoherentParallelTrials.initial (basis x) n =
      basis ((CoherentParallelTrials.coordinates w n).symm (fun _ => x)) := by
  funext y
  rw [CoherentParallelTrials.initial_product]
  have h := congrArg (fun f : EuclideanSpace ℂ (Fin n → Bits w) =>
    f (CoherentParallelTrials.coordinates w n y))
    (CoherentFirstSuccessNative.InitialNative.repeatState_basis n x)
  change _=basis (fun _ => x) (CoherentParallelTrials.coordinates w n y) at h
  apply h.trans
  simp only [basis,Equiv.eq_symm_apply]

theorem ran_norm (C : Layered w) (x : Bits w) :
    ‖(WithLp.toLp 2 (runLayered C (basis x)) : EuclideanSpace ℂ _)‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.norm_sq_eq]
  have h := runLayered_mass C (basis x)
  simpa [Complex.normSq_eq_norm_sq,basis] using h

theorem parallel (C : Layered w) (x : Bits w) (e : I × J ↪ Bits w)
    (ψ : EuclideanSpace ℂ I) (χ : EuclideanSpace ℂ J) (hψ : ‖ψ‖=1) (hχ : ‖χ‖=1)
    (err : ℝ) (h : ‖(WithLp.toLp 2 (runLayered C (basis x)) : EuclideanSpace ℂ _) - pack e ψ χ‖ ≤ err)
    (n : ℕ) :
    ‖(WithLp.toLp 2 (runLayered (CoherentParallelTrials.circuit C n)
      (basis ((CoherentParallelTrials.coordinates w n).symm (fun _ => x)))) : EuclideanSpace ℂ _) -
      pack (embedding e n) (repeatState n ψ) (repeatState n χ)‖ ≤ (n : ℝ)*err := by
  have hn := repeatState_error n _ _ (ran_norm C x) (by rw [pack_norm,hψ,hχ,one_mul]) err h
  rw [←initial_basis]
  refine le_trans (le_of_eq ?_) hn
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,PiLp.sub_apply]
  apply Fintype.sum_equiv (CoherentParallelTrials.coordinates w n)
  intro z
  rw [unpack,CoherentParallelTrials.circuit_product]
  rfl

end InfoLossLAR.WorstCase.RectangularSource

end

end P2MDyadicModule176

/- Helper module RectAnalytic. -/
section P2MDyadicModule177

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource

open GaussianRandomizedRounding GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent

open CoherentProjection GaussianPoissonSeries NativeDualQuotient RegevLWE.GaussConv AFT GaussianSource

abbrev Side (R : ℕ) := Fin (2*R+1)

def coord (R : ℕ) : Side R ↪ ℤ :=
  (windowPointEquiv 0 R).toEmbedding.trans (Function.Embedding.subtype _)

@[simp] theorem coord_apply (R : ℕ) (t : Side R) : coord R t = windowPoint 0 R t := rfl

def box (n R : ℕ) : (Fin n → Side R) ↪ (Fin n → ℤ) where
  toFun v i := coord R (v i)
  inj' _ _ h := funext (fun i => (coord R).injective (congrFun h i))

def boxAmbient {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (M : ℝ) (hM : 0<M) (R : ℕ) :=
  (box n R).trans (ambientIntegerEquiv B M hM).toEmbedding

def retained (s : ℝ) (hs : 0<s) (R : ℕ) : ℝ :=
  ∑ t : Side R,(roundingPMF s hs 0 (coord R t)).toReal

theorem retained_pos (s : ℝ) (hs : 0<s) (R : ℕ) : 0 < retained s hs R := by
  unfold retained
  simp_rw [roundingPMF_toReal]
  rw [←Finset.sum_div]
  simpa only [coord_apply,Rat.cast_zero] using div_pos (windowMass_pos s 0 R) (theta_pos s (0:ℚ) (by simpa using hs))

def window (s : ℝ) (R : ℕ) := finitePositiveState (windowLaw s 0 R)

theorem window_norm (s : ℝ) (R : ℕ) : ‖window s R‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.norm_sq_eq,one_pow]
  simp only [window,finitePositiveState,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt ((windowLaw s 0 R).nonneg _)]
  exact (windowLaw s 0 R).sum_one

theorem factor (s : ℝ) (hs : 0<s) (R : ℕ) (t : Side R) :
    integerGaussianState s hs 0 (coord R t) =
      (Real.sqrt (retained s hs R) : ℂ) * window s R t := by
  change (Real.sqrt _ : ℂ) = _ * (Real.sqrt ((windowLaw s 0 R).weight t) : ℂ)
  rw [windowLaw_eq_conditional s hs]
  simp only [Rat.cast_zero]
  simp only [retained,coord_apply] at *
  change (Real.sqrt _ : ℂ) = _ * (Real.sqrt (_ / retained s hs R) : ℂ)
  rw [Real.sqrt_div ENNReal.toReal_nonneg,←Complex.ofReal_mul]
  congr 1
  field_simp [(Real.sqrt_pos.mpr (retained_pos s hs R)).ne']
  rfl

theorem integer_restriction (n R : ℕ) (s : ℝ) (hs : 0<s) :
    finiteRestrict (box n R) (integerGaussianProductState n s hs) =
      (Real.sqrt (retained s hs R))^n • repeatState n (window s R) := by
  ext v
  change integerGaussianProductState n s hs (box n R v) = _
  rw [integerGaussianProductState_apply]
  change (∏ i,integerGaussianState s hs 0 (coord R (v i))) =
    (Real.sqrt (retained s hs R))^n • (∏ i,window s R (v i))
  simp only [factor,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Algebra.smul_def]
  simp

theorem normalize_multiple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0<c) (v : E) (hv : ‖v‖=1) : normalized (c • v)=v := by
  simp [normalized,norm_smul,Real.norm_eq_abs,abs_of_pos hc,hv,smul_smul,hc.ne']

theorem ambient_restriction {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (M s : ℝ)
    (hM : 0<M) (hs : 0<s) (R : ℕ) :
    normalized (finiteRestrict (boxAmbient B M hM R) (gaussianHilbertState (Ambient B M hM) s hs 0)) =
      repeatState n (window (s*M*(originalDenominator B:ℝ)) R) := by
  have hD : (0 : ℝ)<originalDenominator B := by exact_mod_cast denominator_pos (RationalInverse.Native.inputRows B)
  have hu : 0 < s*M*(originalDenominator B:ℝ) := by positivity
  have hre : finiteRestrict (boxAmbient B M hM R) (gaussianHilbertState (Ambient B M hM) s hs 0) =
      finiteRestrict (box n R) (integerGaussianProductState n _ hu) := by
    rw [←nativeAmbient_product_state B M s hM hs]
    ext v
    simp only [finiteRestrict,boxAmbient,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
      hilbertReindex_apply,Equiv.symm_apply_apply]
  rw [hre,integer_restriction,normalize_multiple (pow_pos (Real.sqrt_pos.mpr (retained_pos _ hu R)) _)]
  exact repeatState_normalized n _ (window_norm _ _)

end InfoLossLAR.WorstCase.RectangularSource

end

end P2MDyadicModule177

/- Helper module RectNative. -/
section P2MDyadicModule178

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource

open GaussianRandomizedRounding GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent

open GaussianPoissonSeries CoherentProjection CoherentComputeUncompute QAlgorithms QAlgorithms.Complexity

open GaussianRandomizedRounding.Wide.Coherent.Padding

open CoherentFirstSuccessNative CoherentRejection CoherentWeightedPreparation

open scoped BigOperators

def active (input : PointRequest) : Side (radius input) ↪ Ticket input :=
  Fin.castLEEmb (Nat.lt_size_self (intervalCount input)).le

def activeBits (input : PointRequest) (K : ℕ) (hK : Nat.size (intervalCount input) ≤ K) :
    Side (radius input) × Bits (K-Nat.size (intervalCount input)) ↪ Bits K :=
  ((active input).prodMap (Function.Embedding.refl _)).trans
    (capacityTicketEquiv input K hK).symm.toEmbedding

def suffix (l : ℕ) : EuclideanSpace ℂ (Bits l) := WithLp.toLp 2 (fun _ => coinAmplitude l)

theorem suffix_norm (l : ℕ) : ‖suffix l‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simp [EuclideanSpace.norm_sq_eq,suffix,coinAmplitude_mass]

theorem active_value (input : PointRequest) (hc : input.1.2=0) (s : ℝ) (t : Side (radius input)) :
    target (fun i : Ticket input => weight input s i.val) (active input t) = window s (radius input) t := by
  change ((Real.sqrt (weight input s t.val) / Real.sqrt (weightSum (fun i : Ticket input => weight input s i.val)) : ℝ) : ℂ) = _
  rw [weightSum,sum_weight]
  simp only [weight,if_pos (show t.val < intervalCount input from t.isLt)]
  simp only [window,finitePositiveState,windowLaw,AFT.FiniteDist.normalize]
  rw [Real.sqrt_div (show 0 ≤ AFT.GaussianSource.shiftedWeight s (0:ℚ) _ from Real.exp_nonneg _)]
  simp only [trueWindowMass,point_eq_windowPoint,hc]
  rfl

theorem capacity_window (input : PointRequest) (hc : input.1.2=0) (s : ℝ)
    (K : ℕ) (hK : Nat.size (intervalCount input) ≤ K) :
    WithLp.toLp 2 (target (capacityWeight input s K hK)) =
      pack (activeBits input K hK) (window s (radius input)) (suffix _) := by
  classical
  ext tape
  obtain ⟨⟨t,y⟩,rfl⟩ := (capacityTicketEquiv input K hK).symm.surjective tape
  rw [show (WithLp.toLp 2 (target (capacityWeight input s K hK)) : EuclideanSpace ℂ _)
    ((capacityTicketEquiv input K hK).symm (t,y)) =
    target (fun i : Ticket input => weight input s i.val) t * coinAmplitude _ from by
      rw [WithLp.ofLp_toLp,capacity_target_tensor,←capacityTicketEquiv_first,Equiv.apply_symm_apply]]
  by_cases ht : t.val < intervalCount input
  · let x : Side (radius input) := ⟨t.val,ht⟩
    have he : t=active input x := rfl
    rw [he,active_value input hc]
    change _=basisEmbedding _ _ (activeBits input K hK (x,y))
    rw [basisEmbedding_at]
    rfl
  · have ho : (capacityTicketEquiv input K hK).symm (t,y) ∉ Set.range (activeBits input K hK) := by
      rintro ⟨⟨v,b⟩,h⟩
      have he := (capacityTicketEquiv input K hK).symm.injective h
      exact ht ((congrArg (fun p : Ticket input × _ => p.1.val) he) ▸ v.isLt)
    change _=basisEmbedding _ _ _
    rw [basisEmbedding_outside _ _ _ ho]
    simp [target,weight,ht]

variable {I J H L W V : Type*} [Fintype I] [Fintype J] [Fintype H] [Fintype W]
  [Fintype V] [DecidableEq W] [DecidableEq V]

def joinEmbedding (e : I × J ↪ W) (f : W × H ↪ V) : I × (J × H) ↪ V :=
  (Equiv.prodAssoc I J H).symm.toEmbedding.trans ((e.prodMap (Function.Embedding.refl H)).trans f)

theorem joined (e : I × J ↪ W) (f : W × H ↪ V)
    (u : EuclideanSpace ℂ I) (v : EuclideanSpace ℂ J) (h : EuclideanSpace ℂ H) :
    basisEmbedding f (CoherentProjection.tensorState (WithLp.toLp 2 (basisEmbedding e (CoherentProjection.tensorState u v))) h) =
      basisEmbedding (joinEmbedding e f) (CoherentProjection.tensorState u (CoherentProjection.tensorState v h)) := by
  classical
  funext x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨⟨b,y⟩,rfl⟩ := hx
    rw [basisEmbedding_at]
    by_cases hb : b ∈ Set.range e
    · obtain ⟨⟨i,j⟩,rfl⟩ := hb
      change basisEmbedding e _ (e (i,j))*h y = basisEmbedding _ _ (joinEmbedding e f (i,(j,y)))
      rw [basisEmbedding_at,basisEmbedding_at]
      exact mul_assoc _ _ _
    · have ho : f (b,y) ∉ Set.range (joinEmbedding e f) := by
        rintro ⟨⟨i,j,k⟩,he⟩
        exact hb ⟨(i,j),congrArg Prod.fst (f.injective he)⟩
      change basisEmbedding e _ b*h y = _
      rw [basisEmbedding_outside e _ _ hb,basisEmbedding_outside _ _ _ ho,zero_mul]
  · have ho : x ∉ Set.range (joinEmbedding e f) := by
      rintro ⟨⟨i,j,k⟩,rfl⟩
      exact hx ⟨(e (i,j),k),rfl⟩
    rw [basisEmbedding_outside _ _ _ hx,basisEmbedding_outside _ _ _ ho]

theorem composeEmbed (e : I ↪ W) (f : W ↪ V) (u : I → ℂ) :
    basisEmbedding f (basisEmbedding e u) = basisEmbedding (e.trans f) u := by
  classical
  funext x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨b,rfl⟩ := hx
    rw [basisEmbedding_at]
    by_cases hb : b ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hb
      change basisEmbedding _ _ (e i)=basisEmbedding _ _ ((e.trans f) i)
      rw [basisEmbedding_at,basisEmbedding_at]
    · rw [basisEmbedding_outside _ _ _ hb,basisEmbedding_outside]
      rintro ⟨i,h⟩
      exact hb ⟨i,f.injective h⟩
  · rw [basisEmbedding_outside _ _ _ hx,basisEmbedding_outside]
    rintro ⟨i,rfl⟩
    exact hx ⟨e i,rfl⟩

end InfoLossLAR.WorstCase.RectangularSource

end

end P2MDyadicModule178

/- Helper module RectCircuit. -/
section P2MDyadicModule179

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource

open GaussianRandomizedRounding GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent

open GaussianPoissonSeries CoherentProjection CoherentComputeUncompute QAlgorithms QAlgorithms.Complexity

open GaussianRandomizedRounding.Wide.Coherent.Padding

open CoherentFirstSuccessNative CoherentRejection CoherentWeightedPreparation

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

variable (request : Str → PointRequest × List Unit) (hr : Poly request)

abbrev sourceWork (a : ℕ) (slots : List Unit) (K : ℕ) := Builder.Trial.workSize request hr a slots K

abbrev sourceWidth (a : ℕ) (slots : List Unit) (K m : ℕ) :=
  NativeWordLayout.width CoherentFirstSuccessNative.P m+(m+1)*sourceWork request hr a slots K+m*4

def selected (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K) (m : ℕ) :=
  joinEmbedding
    ((activeBits (request word).1 K hK).trans (Builder.Trial.workEmbedding request hr a slots word K))
    (abstractEmbedding (sourceWork request hr a slots K) m 4)

theorem prepared_eq (a : ℕ) (slots : List Unit) (word : Str)
    (hc : (request word).1.1.2=0) (s : ℝ) (K : ℕ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K) (m : ℕ)
    (χ : EuclideanSpace ℂ (Retained (Bits (sourceWork request hr a slots K)) (Bits 4) m)) :
    basisEmbedding (abstractEmbedding (sourceWork request hr a slots K) m 4)
      (CoherentProjection.tensorState (Builder.Trial.embeddedTarget request hr a slots word K s hK) χ) =
    pack (selected request hr a slots word K hK m)
      (window s (radius (request word).1)) (CoherentProjection.tensorState (suffix _) χ) := by
  have h := capacity_window (request word).1 hc s K hK
  have he : Builder.Trial.embeddedTarget request hr a slots word K s hK =
      WithLp.toLp 2 (basisEmbedding ((activeBits (request word).1 K hK).trans
        (Builder.Trial.workEmbedding request hr a slots word K))
        (CoherentProjection.tensorState (window s (radius (request word).1)) (suffix _))) := by
    change WithLp.toLp 2 (basisEmbedding _ (target _)) = _
    rw [← composeEmbed]
    exact congrArg (fun y : EuclideanSpace ℂ (Bits K) =>
      WithLp.toLp 2 (basisEmbedding (Builder.Trial.workEmbedding request hr a slots word K) y)) h
  rw [he]
  exact joined _ _ _ _ _

theorem exists_prepared :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ ∀ (slots : List Unit) (word : Str) (s : ℝ) (budget : List Unit),
    (request word).1.1.2=0 → 2*word.length+1 ≤ slots.length →
    ∀ (K : ℕ) (hK : Nat.size (intervalCount (request word).1) ≤ K),
    1 ≤ s → s^2=(variance (request word).1:ℝ) → 2 ≤ (request word).1.2.1.length →
    ∀ m : ℕ, m≠0 → ∀ n : ℕ,
      ∃ ξ : EuclideanSpace ℂ (Fin n → Bits (K - Nat.size (intervalCount (request word).1)) ×
        Retained (Bits (sourceWork request hr a slots K)) (Bits 4) m),
      ‖ξ‖=1 ∧
      ‖(WithLp.toLp 2 (runLayered
        (CoherentParallelTrials.circuit (Builder.Pipeline.circuit request hr a b slots word K budget m) n)
        (basis ((CoherentParallelTrials.coordinates (sourceWidth request hr a slots K m) n).symm
          (fun _ => Builder.Pipeline.basisInput request hr a slots word K m)))) : EuclideanSpace ℂ _) -
        pack (embedding (selected request hr a slots word K hK m) n) (repeatState n (window s (radius (request word).1))) ξ‖ ≤
      (n:ℝ)*((m:ℝ)*Builder.Trial.error request hr a slots word K budget+
        2*Real.exp (-(m:ℝ)/(112*((request word).1.2.1.length:ℝ)))) := by
  obtain ⟨a,b,ha,hb,h⟩ := Builder.Pipeline.exists_pure_from_basis request hr
  refine ⟨a,b,ha,hb,?_⟩
  intro slots word s budget hc hslots K hK hs hv hfactor m hm n
  obtain ⟨χ,hχ,herr⟩ := h slots word s budget hslots K hK hs hv hfactor m hm
  rw [prepared_eq request hr a slots word hc s K hK m χ] at herr
  have hj : ‖CoherentProjection.tensorState (suffix (K - Nat.size (intervalCount (request word).1))) χ‖=1 := by
    rw [tensorState_norm,suffix_norm,hχ,one_mul]
  exact ⟨_,repeatState_normalized n _ hj,parallel _ _ _ _ _ (window_norm _ _) hj _ herr n⟩

end InfoLossLAR.WorstCase.RectangularSource

end

end P2MDyadicModule179

/- Helper module Solutions.RegevBridgeNativeFixedBits. -/
section P2MDyadicModule180

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeFixedBits

open QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- The output length comes from a supplied unary buffer. Binary magnitudes
are never expanded into a unary number of steps. -/
def current (x : List Unit×ℕ) : Str := (Nat.bits x.2++x.1.map (fun _ => false)).take x.1.length

@[fun_prop] theorem current_poly : Poly current := by
  unfold current
  exact Poly.comp (g:=fun x : List Unit×ℕ => (Nat.bits x.2++x.1.map (fun _ => false),x.1.length)) parser_take_poly (by fun_prop)

@[simp] theorem current_length (ticks : List Unit) (value : ℕ) :
    (current (ticks,value)).length=ticks.length := by
  simp only [current,List.length_take,List.length_append,List.length_map]
  omega

theorem bitValue_bound (word : Str) : bitValue word<2^word.length := by
  induction word with
  | nil => simp [bitValue]
  | cons b tail ih => cases b <;> simp only [bitValue,Bool.toNat_false,Bool.toNat_true,List.length_cons,pow_succ] <;> omega

theorem bitValue_injective_length (left right : Str) (hlen : left.length=right.length)
    (hvalue : bitValue left=bitValue right) : left=right := by
  induction left generalizing right with
  | nil => simpa using hlen.symm
  | cons b tail ih =>
    cases right with
    | nil => simp at hlen
    | cons c rest =>
      have hl : tail.length=rest.length := by simpa using hlen
      cases b <;> cases c <;> simp only [bitValue,Bool.toNat_false,Bool.toNat_true] at hvalue
      · exact congrArg (List.cons false) (ih rest hl (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih rest hl (by omega))

theorem bitValue_false (n : ℕ) : bitValue (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,bitValue,Bool.toNat_false,ih,Nat.mul_zero,Nat.zero_add]

theorem bitValue_append_false (word : Str) (n : ℕ) : bitValue (word++List.replicate n false)=bitValue word := by
  induction word with
  | nil => exact bitValue_false n
  | cons b tail ih => simp only [List.cons_append,bitValue,ih]

theorem current_value (ticks : List Unit) (value : ℕ) (h : value<2^ticks.length) :
    bitValue (current (ticks,value))=value := by
  have hs : (Nat.bits value).length≤ticks.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr h
  simp only [current,List.take_append,List.take_of_length_le hs,List.map_const',List.take_replicate]
  rw [bitValue_append_false,bitValue_bits]

/-- Literal fixed-length binary tickets, including high false bits, are
recovered exactly from their integer value. -/
theorem current_recovers (word : Str) : current (word.map (fun _ => ()),bitValue word)=word := by
  apply bitValue_injective_length
  · simp
  · apply current_value
    simpa only [List.length_map] using bitValue_bound word

end InfoLossLAR.WorstCase.NativeFixedBits

end P2MDyadicModule180

/- Helper module Solutions.RegevBridgeCoherentInjectionEmitter. -/
section P2MDyadicModule181

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

variable {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g)

local instance : DecidableEq P.machine.Label := Classical.decEq _

local instance : DecidableEq P.machine.State := Classical.decEq _

def inverseWord (word : Str) : Str := (request P word).2.1.map (fun _ => true)

@[fun_prop] theorem inverseWord_poly : Poly (inverseWord P) := by unfold inverseWord;fun_prop

theorem inverseWord_exact (n : ℕ) : inverseWord P (unary n)=unary (outputSize P n) := by
  rw [inverseWord,request_unary]
  simp [unary,outputSize]

def workTicks (word : Str) : List Unit :=
  (generate P.machine.code P.machine.input P.machine.main P.machine.initial (request P word)).2.2.2.map (fun _ => ())++[()]

@[fun_prop] theorem workTicks_poly : Poly (workTicks P) := by unfold workTicks;fun_prop

theorem workTicks_length (n : ℕ) : (workTicks P (unary n)).length=forwardWork P n := by
  have h := machineWidth_eq P n
  unfold machineWidth at h
  have hn : (unary n).length=n := by simp [unary]
  rw [hn] at h
  unfold NativeWordLayout.width at h
  simp only [workTicks,List.length_append,List.length_map,List.length_singleton,forwardWork]
  omega

def outputTicks (word : Str) : List Unit := (request P word).2.1

@[fun_prop] theorem outputTicks_poly : Poly (outputTicks P) := by unfold outputTicks;fun_prop

theorem outputTicks_length (n : ℕ) : (outputTicks P (unary n)).length=outputSize P n := by
  simp [outputTicks,request_unary,outputSize]

def firstSlots (word : Str) : List Unit := word.map (fun _ => ())++workTicks P word++outputTicks P word

def secondSlots (word : Str) : List Unit :=
  (inverseWord P word).map (fun _ => ())++workTicks Q (inverseWord P word)++outputTicks Q (inverseWord P word)

def wholeSlots (word : Str) : List Unit :=
  outputTicks Q (inverseWord P word)++outputTicks P word++workTicks P word++workTicks Q (inverseWord P word)

@[fun_prop] theorem firstSlots_poly : Poly (firstSlots P) := by unfold firstSlots;fun_prop

@[fun_prop] theorem secondSlots_poly : Poly (secondSlots P Q) := by unfold secondSlots;fun_prop

@[fun_prop] theorem wholeSlots_poly : Poly (wholeSlots P Q) := by unfold wholeSlots;fun_prop

theorem firstSlots_length (n : ℕ) : (firstSlots P (unary n)).length=NativeWordLayout.width P n+capacity P n := by
  simp only [firstSlots,List.length_append,List.length_map,workTicks_length,outputTicks_length]
  simp [unary,NativeWordLayout.width,forwardWork,outputSize]

theorem secondSlots_length (n : ℕ) :
    (secondSlots P Q (unary n)).length=NativeWordLayout.width Q (outputSize P n)+capacity Q (outputSize P n) := by
  simp only [secondSlots,inverseWord_exact,List.length_append,List.length_map,workTicks_length,outputTicks_length]
  simp [unary,NativeWordLayout.width,forwardWork,outputSize]

theorem wholeSlots_length (n : ℕ) : (wholeSlots P Q (unary n)).length=totalWidth P Q n := by
  simp only [wholeSlots,List.length_append,inverseWord_exact,workTicks_length,outputTicks_length,totalWidth,width,originalSize,backwardWork,outputSize,forwardWork]

def firstAddress (word : Str) (i : ℕ) : ℕ :=
  if i<word.length then i
  else if i<word.length+(workTicks P word).length then
    (outputTicks Q (inverseWord P word)).length+(outputTicks P word).length+(i-word.length)
  else (outputTicks Q (inverseWord P word)).length+(i-(word.length+(workTicks P word).length))

def secondAddress (word : Str) (i : ℕ) : ℕ :=
  if i<(outputTicks P word).length then (outputTicks Q (inverseWord P word)).length+i
  else if i<(outputTicks P word).length+(workTicks Q (inverseWord P word)).length then
    (outputTicks Q (inverseWord P word)).length+(outputTicks P word).length+(workTicks P word).length+
      (i-(outputTicks P word).length)
  else i-((outputTicks P word).length+(workTicks Q (inverseWord P word)).length)

@[fun_prop] theorem firstAddress_poly : Poly (fun x : Str×ℕ => firstAddress P Q x.1 x.2) := by unfold firstAddress;fun_prop

@[fun_prop] theorem secondAddress_poly : Poly (fun x : Str×ℕ => secondAddress P Q x.1 x.2) := by unfold secondAddress;fun_prop

def firstLayout (word : Str) : List ℕ := (List.range (firstSlots P word).length).map (firstAddress P Q word)

def secondLayout (word : Str) : List ℕ := (List.range (secondSlots P Q word).length).map (secondAddress P Q word)

@[fun_prop] theorem firstLayout_poly : Poly (firstLayout P Q) := by
  unfold firstLayout
  apply Poly.list_map
  · exact firstAddress_poly P Q
  · exact Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=firstSlots P) Poly.list_indices (firstSlots_poly P)

@[fun_prop] theorem secondLayout_poly : Poly (secondLayout P Q) := by
  unfold secondLayout
  apply Poly.list_map
  · exact secondAddress_poly P Q
  · exact Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=secondSlots P Q) Poly.list_indices (secondSlots_poly P Q)

theorem firstAddress_exact (n : ℕ) (i : Fin (NativeWordLayout.width P n+capacity P n)) :
    firstAddress P Q (unary n) i.val=(firstWires P Q n i).val := by
  simp only [firstAddress,inverseWord_exact,outputTicks_length,workTicks_length]
  simp only [unary,List.length_replicate,firstWires,forwardWires,Function.Embedding.coeFn_mk]
  change (if i.val<n then i.val else if i.val<n+forwardWork P n then
    originalSize P Q n+outputSize P n+(i.val-n) else originalSize P Q n+(i.val-(n+forwardWork P n)))=_
  split_ifs <;> rfl

theorem secondAddress_exact (n : ℕ)
    (i : Fin (NativeWordLayout.width Q (outputSize P n)+capacity Q (outputSize P n))) :
    secondAddress P Q (unary n) i.val=(secondWires P Q n i).val := by
  simp only [secondAddress,inverseWord_exact,outputTicks_length,workTicks_length,
    secondWires,backwardWires,Function.Embedding.coeFn_mk,backwardWork,forwardWork,originalSize,outputSize]
  split_ifs <;> rfl

theorem firstLayout_exact (n : ℕ) : firstLayout P Q (unary n)=List.ofFn (fun i => (firstWires P Q n i).val) := by
  unfold firstLayout
  rw [firstSlots_length]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i<NativeWordLayout.width P n+capacity P n := by simpa using hi
    simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using firstAddress_exact P Q n ⟨i,hi'⟩

theorem secondLayout_exact (n : ℕ) : secondLayout P Q (unary n)=List.ofFn (fun i => (secondWires P Q n i).val) := by
  unfold secondLayout
  rw [secondSlots_length]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i<NativeWordLayout.width Q (outputSize P n)+capacity Q (outputSize P n) := by simpa using hi
    simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using secondAddress_exact P Q n ⟨i,hi'⟩

def emitted (word : Str) : List (List Str) :=
  relocatedWordLayers (wholeSlots P Q word,(firstLayout P Q word,CoherentClassicalOracle.publicLayers P word))++
    relocatedWordLayers (wholeSlots P Q word,(secondLayout P Q word,
      CoherentClassicalOracle.publicLayers Q (inverseWord P word)))

attribute [local irreducible] wholeSlots firstLayout secondLayout CoherentClassicalOracle.publicLayers inverseWord

@[fun_prop] theorem emitted_poly : Poly (emitted P Q) := by unfold emitted;fun_prop

theorem emitted_exact (n : ℕ) : emitted P Q (unary n)=(circuit P Q n).map (List.map encInstr) := by
  unfold emitted circuit firstCircuit secondCircuit
  rw [firstLayout_exact,secondLayout_exact,inverseWord_exact,CoherentClassicalOracle.publicLayers_exact,
    CoherentClassicalOracle.publicLayers_exact]
  rw [relocatedWordLayers_exact _ _ _ (by rw [wholeSlots_length]),
    relocatedWordLayers_exact _ _ _ (by rw [wholeSlots_length]),List.map_append]

end InfoLossLAR.WorstCase.CoherentInjection

end

end P2MDyadicModule181

/- Helper module Solutions.RegevBridgeNativeTicketInteger. -/
section P2MDyadicModule182

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.NativeTicketInteger

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2NativeAffineEncoding

open Integration9_9.LARPlatformEncoding

/-- A fixed public header precedes literal physical ticket bits. This is
the same unary header framing used by the actual padded Gaussian builder. -/
def input (header tape : Str) : Str := lengthToken header++header++tape

def split (word : Str) : Str×Str :=
  ((readUnary word).2.take (unarySlots word).length,
    (readUnary word).2.drop (unarySlots word).length)

@[fun_prop] theorem split_poly : Poly split := by
  have hu : Poly (fun word : Str => (readUnary word).2) := Poly.comp Poly.snd readUnary_poly
  have hn : Poly (fun word : Str => (unarySlots word).length) := Poly.comp Poly.list_length unarySlots_poly
  exact Poly.pair (Poly.comp parser_take_poly (Poly.pair hu hn))
    (Poly.comp parser_drop_poly (Poly.pair hu hn))

theorem split_input (header tape : Str) : split (input header tape)=(header,tape) := by
  simp only [split,input,List.append_assoc,lengthToken_eq,readUnary_append,unarySlots_append,
    List.length_replicate,List.take_left,List.drop_left]

@[fun_prop] theorem input_poly : Poly (fun x : Str×Str => input x.1 x.2) := by unfold input;fun_prop

variable (offset : Str → ℤ) (hoffset : Poly offset)

end InfoLossLAR.WorstCase.NativeTicketInteger

end P2MDyadicModule182

/- Helper module Solutions.RegevBridgeNativePaddedWords. -/
section P2MDyadicModule183

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativePaddedWords

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.LARPlatformEncoding (readBinaryList_append_mapped encL_length_pos serializeBinaryWords_map)

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem current_poly : Poly current := by
  have h := Poly.comp QMCNumericRuntime.parser_take_poly
    (show Poly (fun x : List Unit×Str => (x.2++x.1.map (fun _ => false),x.1.length)) by fun_prop)
  exact h

@[simp] theorem current_length (ticks : List Unit) (word : Str) : (current (ticks,word)).length=ticks.length := by
  simp only [current,List.length_take,List.length_append,List.length_map]
  omega

theorem current_eq (ticks : List Unit) (word : Str) (h : word.length≤ ticks.length) :
    current (ticks,word)=word++List.replicate (ticks.length-word.length) false := by
  simp only [current,List.take_append,List.take_of_length_le h,List.map_const',List.take_replicate]
  congr 2
  omega

theorem readVector_serialized (vector : List ℤ) (tail : Str) :
    readVector (serializeVector vector++tail)=(tail,vector) := by
  unfold readVector serializeVector
  rw [serializeBinaryWords_map]
  have h := readBinaryList_append_mapped readInteger encI id (fun z => by simp [encI]) readInteger_append vector tail
  simpa only [List.map_id] using h

theorem readMatrix_serialized (matrix : List (List ℤ)) (tail : Str) :
    readMatrix (serializeMatrix matrix++tail)=(tail,matrix) := by
  unfold readMatrix serializeMatrix
  rw [serializeBinaryWords_map]
  have hp (row : List ℤ) : 0<(serializeVector row).length := by
    rw [serializeVector,serializeBinaryWords_map]
    exact encL_length_pos encI row
  have h := readBinaryList_append_mapped readVector serializeVector id hp readVector_serialized matrix tail
  simpa only [List.map_id] using h

end InfoLossLAR.WorstCase.NativePaddedWords

end P2MDyadicModule183

/- Helper module Solutions.RegevBridgeNativeDualQuotientCodec. -/
section P2MDyadicModule184

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2200000

namespace InfoLossLAR.WorstCase.NativeDualQuotient.Codec

open QAlgorithms QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2PlatformSerialization

open Integration9_9.LARPlatformEncoding (readS readS_poly readS_append)

open NativePaddedWords (readVector_serialized readMatrix_serialized)

def input (matrix : List (List ℤ)) (vector : List ℤ) : Str := serialize (matrix,vector)

def forward (word : Str) : Str :=
  let b := readS word
  let v := readS b.1
  let result := NativeDualQuotient.current ((readMatrix b.2).2,(readVector v.2).2)
  lengthToken word++encS b.2++encS (serializeVector result.1)++encS (serializeVector result.2)

@[fun_prop] theorem forward_poly : Poly forward := by unfold forward;fun_prop

def inverse (word : Str) : Str :=
  let b := readS (readUnary word).2
  let z := readS b.1
  let r := readS z.1
  let point := NativeDualQuotient.reconstruct ((readMatrix b.2).2,((readVector z.2).2,(readVector r.2).2))
  NativePaddedWords.current (unarySlots word,encPair b.2 (serializeVector point))

@[fun_prop] theorem inverse_poly : Poly inverse := by
  have hu : Poly (fun word : Str => (readUnary word).2) := Poly.comp Poly.snd readUnary_poly
  have hb : Poly (fun word : Str => readS (readUnary word).2) := Poly.comp (f:=readS) (g:=fun word : Str => (readUnary word).2) readS_poly hu
  have hz : Poly (fun word : Str => readS (readS (readUnary word).2).1) := Poly.comp (f:=readS) (g:=fun word : Str => (readS (readUnary word).2).1) readS_poly (Poly.comp Poly.fst hb)
  have hr : Poly (fun word : Str => readS (readS (readS (readUnary word).2).1).1) := Poly.comp (f:=readS) (g:=fun word : Str => (readS (readS (readUnary word).2).1).1) readS_poly (Poly.comp Poly.fst hz)
  have hp : Poly (fun word : Str => NativeDualQuotient.reconstruct
      ((readMatrix (readS (readUnary word).2).2).2,
        ((readVector (readS (readS (readUnary word).2).1).2).2,
          (readVector (readS (readS (readS (readUnary word).2).1).1).2).2))) := by fun_prop
  have he : Poly (fun x : Str×Str => encPair x.1 x.2) := by fun_prop
  have ho := Poly.comp he (Poly.pair (Poly.comp Poly.snd hb) (Poly.comp serializeVector_poly hp))
  have hout := Poly.comp NativePaddedWords.current_poly (Poly.pair unarySlots_poly ho)
  exact hout

theorem forward_append (matrix : List (List ℤ)) (vector : List ℤ) (padding : Str) :
    forward (input matrix vector++padding)=
      lengthToken (input matrix vector++padding)++encS (serializeMatrix matrix)++
        encS (serializeVector (NativeDualQuotient.current (matrix,vector)).1)++
        encS (serializeVector (NativeDualQuotient.current (matrix,vector)).2) := by
  have hm : (readMatrix (serializeMatrix matrix)).2=matrix := by
    have h := readMatrix_serialized matrix []
    simpa only [List.append_nil] using congrArg Prod.snd h
  have hv : (readVector (serializeVector vector)).2=vector := by
    have h := readVector_serialized vector []
    simpa only [List.append_nil] using congrArg Prod.snd h
  simp only [forward,input,serialize,encPair,List.append_assoc,readS_append,hm,hv]

theorem inverse_forward_append (matrix : List (List ℤ)) (vector : List ℤ) (padding extra : Str) :
    inverse (forward (input matrix vector++padding)++extra)=
      NativePaddedWords.current (List.replicate (input matrix vector++padding).length (),
        input matrix (NativeDualQuotient.reconstruct (matrix,NativeDualQuotient.current (matrix,vector)))) := by
  have hm : (readMatrix (serializeMatrix matrix)).2=matrix := by
    have h := readMatrix_serialized matrix []
    simpa only [List.append_nil] using congrArg Prod.snd h
  have hv (v : List ℤ) : (readVector (serializeVector v)).2=v := by
    have h := readVector_serialized v []
    simpa only [List.append_nil] using congrArg Prod.snd h
  rw [forward_append]
  simp only [inverse,List.append_assoc,lengthToken_eq,readUnary_append,unarySlots_append,
    readS_append,hm,hv,input,serialize]

/-- On every valid integer basis the actual two native functions are
inverse on padded canonical inputs, including the public original word length.
The output keeps the basis plus the true quotient/remainder, never the old v. -/
theorem inverse_forward_padded {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (v : Fin n → ℤ) (ticks : List Unit)
    (hlen : (input (RationalInverse.Native.inputRows B) (List.ofFn v)).length≤ ticks.length)
    (extra : Str) :
    inverse (forward (NativePaddedWords.current
      (ticks,input (RationalInverse.Native.inputRows B) (List.ofFn v)))++extra)=
        NativePaddedWords.current (ticks,input (RationalInverse.Native.inputRows B) (List.ofFn v)) := by
  rw [NativePaddedWords.current_eq ticks _ hlen,inverse_forward_append,reconstruct_current B hdet]
  have hl : (input (RationalInverse.Native.inputRows B) (List.ofFn v)++
      List.replicate (ticks.length-(input (RationalInverse.Native.inputRows B) (List.ofFn v)).length) false).length=ticks.length := by
    simp only [List.length_append,List.length_replicate]
    omega
  rw [hl]
  have ht : List.replicate ticks.length ()=ticks := by
    symm
    exact List.eq_replicate_iff.mpr ⟨rfl,fun _ _ => Subsingleton.elim _ _⟩
  rw [ht,NativePaddedWords.current_eq ticks _ hlen]

noncomputable def forwardProgram : PolyProgram id id forward :=
  Integration9_9.LARCoinLayout.rawPolyProgram forward_poly

noncomputable def inverseProgram : PolyProgram id id inverse :=
  Integration9_9.LARCoinLayout.rawPolyProgram inverse_poly

theorem inverse_machine_output {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (v : Fin n → ℤ) (ticks : List Unit)
    (hlen : (input (RationalInverse.Native.inputRows B) (List.ofFn v)).length≤ ticks.length) :
    inverse (CoherentClassicalOracle.paddedOutput forwardProgram (NativePaddedWords.current
      (ticks,input (RationalInverse.Native.inputRows B) (List.ofFn v))))=
        NativePaddedWords.current (ticks,input (RationalInverse.Native.inputRows B) (List.ofFn v)) := by
  change inverse (TM2Boolean.PolyProgramCircuit.paddedOutput forwardProgram _)=_
  rw [TM2Boolean.PolyProgramCircuit.paddedOutput_eq_append]
  exact inverse_forward_padded B hdet v ticks hlen _

end InfoLossLAR.WorstCase.NativeDualQuotient.Codec

end P2MDyadicModule184

/- Helper module Solutions.RegevBridgeNativeDualQuotientCoherent. -/
section P2MDyadicModule185

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeDualQuotient.Codec

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.LARPlatformEncoding (readS readS_append)

open NativePaddedWords (readVector_serialized)

open scoped BigOperators

def vectorInWord (word : Str) : List ℤ := (readVector (readS (readS word).1).2).2

theorem vectorInWord_input (matrix : List (List ℤ)) (vector : List ℤ) (padding : Str) :
    vectorInWord (input matrix vector++padding)=vector := by
  have hv : (readVector (serializeVector vector)).2=vector := by
    have h := readVector_serialized vector []
    simpa only [List.append_nil] using congrArg Prod.snd h
  simp only [vectorInWord,input,serialize,encPair,List.append_assoc,readS_append,hv]

theorem padded_input_injective {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (v w : Fin n → ℤ)
    (hv : (input (RationalInverse.Native.inputRows B) (List.ofFn v)).length≤ ticks.length)
    (hw : (input (RationalInverse.Native.inputRows B) (List.ofFn w)).length≤ ticks.length)
    (he : NativePaddedWords.current (ticks,input (RationalInverse.Native.inputRows B) (List.ofFn v))=
      NativePaddedWords.current (ticks,input (RationalInverse.Native.inputRows B) (List.ofFn w))) : v=w := by
  have h := congrArg vectorInWord he
  rw [NativePaddedWords.current_eq ticks _ hv,NativePaddedWords.current_eq ticks _ hw,
    vectorInWord_input,vectorInWord_input] at h
  funext i
  have hh := congrArg (fun vs : List ℤ => vs[i.val]?.getD 0) h
  simpa only [List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some] using hh

variable {n : ℕ} {I : Type*} [Fintype I]

def words (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit) (vectors : I → Fin n → ℤ) (i : I) : Str :=
  NativePaddedWords.current (ticks,input (RationalInverse.Native.inputRows B) (List.ofFn (vectors i)))

theorem words_length (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit) (vectors : I → Fin n → ℤ) (i : I) :
    (words B ticks vectors i).length=ticks.length := NativePaddedWords.current_length _ _

theorem words_injective (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit) (vectors : I → Fin n → ℤ)
    (hi : Function.Injective vectors)
    (hfit : ∀ i,(input (RationalInverse.Native.inputRows B) (List.ofFn (vectors i))).length≤ ticks.length) :
    Function.Injective (words B ticks vectors) := by
  intro i j he
  exact hi (padded_input_injective B ticks _ _ (hfit i) (hfit j) he)

theorem words_inverse (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (ticks : List Unit) (vectors : I → Fin n → ℤ)
    (hfit : ∀ i,(input (RationalInverse.Native.inputRows B) (List.ofFn (vectors i))).length≤ ticks.length) (i : I) :
    inverse (CoherentClassicalOracle.paddedOutput forwardProgram (words B ticks vectors i))=words B ticks vectors i :=
  inverse_machine_output B hdet _ ticks (hfit i)

/-- The actual uniform native circuit realizes the quotient/remainder
change of coordinates on a whole finite Gaussian truncation at once. Every
old-vector and machine-work wire is zero at the output. -/
theorem actual_coherent_quotient (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (ticks : List Unit) (vectors : I → Fin n → ℤ) (hi : Function.Injective vectors)
    (hfit : ∀ i,(input (RationalInverse.Native.inputRows B) (List.ofFn (vectors i))).length≤ ticks.length)
    (ψ : I → ℂ) :
    runLayered (CoherentInjection.circuit forwardProgram inverseProgram ticks.length)
      (basisEmbedding (CoherentInjection.inputEncoding forwardProgram inverseProgram ticks.length
        (words B ticks vectors) (words_length B ticks vectors) (words_injective B ticks vectors hi hfit)) ψ)=
      basisEmbedding (CoherentInjection.outputEncoding forwardProgram inverseProgram ticks.length
        (words B ticks vectors) (words_length B ticks vectors) (words_injective B ticks vectors hi hfit)
        (words_inverse B hdet ticks vectors hfit)) ψ :=
  CoherentInjection.circuit_superposition _ _ _ _ _ _ _ _

end InfoLossLAR.WorstCase.NativeDualQuotient.Codec

end

end P2MDyadicModule185

/- Helper module RectCodec. -/
section P2MDyadicModule186

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

namespace InfoLossLAR.WorstCase.RectangularSource.Binary

open QAlgorithms.Complexity QMCNumericRuntime NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open NativeTicketInteger (input split)

@[local fun_prop] private theorem flatten_poly : Poly (List.flatten : List Str → Str) := ⟨PolyProgram.listFlatten encodeBool false⟩

attribute [local fun_prop] parser_take_poly parser_drop_poly

abbrev Config := (List (List ℤ) × List Unit) × ((ℕ × ℕ) × (List Unit × ℤ))

abbrev Context := Config × Str

abbrev Indexed := Context × ℕ

abbrev matrix (p : Config) := p.1.1

abbrev ticks (p : Config) := p.1.2

abbrev span (p : Config) := p.2.1.1

abbrev start (p : Config) := p.2.1.2

abbrev activeTicks (p : Config) := p.2.2.1

abbrev offset (p : Config) := p.2.2.2

def take (p : Str × ℕ) : Str := p.1.take p.2

def drop (p : Str × ℕ) : Str := p.1.drop p.2

@[fun_prop] theorem take_poly : Poly take := parser_take_poly

@[fun_prop] theorem drop_poly : Poly drop := parser_drop_poly

def slice (input : (Str×ℕ)×ℕ) := take (drop input.1,input.2)

@[fun_prop] theorem slice_poly : Poly slice := by
  unfold slice
  fun_prop

def row (p : Indexed) : Str := slice ((p.1.2,p.2*span p.1.1),span p.1.1)

@[fun_prop] theorem row_poly : Poly row := by unfold row;fun_prop

def low (p : Indexed) : Str := slice ((row p,start p.1.1),(activeTicks p.1.1).length)

@[fun_prop] theorem low_poly : Poly low := by unfold low;fun_prop

def rest (p : Indexed) : Str := take (row p,start p.1.1) ++ drop (row p,start p.1.1+(activeTicks p.1.1).length)

@[fun_prop] theorem rest_poly : Poly rest := by
  unfold rest
  fun_prop

def value (p : Indexed) : ℤ := offset p.1.1+(bitValue (low p):ℤ)

@[fun_prop] theorem value_poly : Poly value := by unfold value;fun_prop

def indices (p : Context) := List.range (matrix p.1).length

@[fun_prop] theorem indices_poly : Poly indices := by
  unfold indices
  exact Poly.comp (f:=fun xs : List (List ℤ) => List.range xs.length) (g:=fun p : Context => matrix p.1) Poly.list_indices (by fun_prop)

def values (p : Context) := (indices p).map (fun i => value (p,i))

@[fun_prop] theorem values_poly : Poly values := Poly.list_map value_poly indices_poly

def rests (p : Context) := ((indices p).map (fun i => rest (p,i))).flatten

@[fun_prop] theorem rests_poly : Poly rests := by
  unfold rests
  have hm : Poly (fun p : Context => (indices p).map (fun i => rest (p,i))) := Poly.list_map rest_poly indices_poly
  exact Poly.comp (f:=(List.flatten : List Str → Str)) (g:=fun p : Context => (indices p).map (fun i => rest (p,i))) flatten_poly hm

variable (controls : Str → Config) (hc : Poly controls)

def ctx (w : Str) : Context := (controls (split w).1,(split w).2)

include hc in
@[fun_prop] theorem ctx_poly : Poly (ctx controls) := Poly.pair (Poly.comp hc (Poly.comp Poly.fst NativeTicketInteger.split_poly)) (Poly.comp Poly.snd NativeTicketInteger.split_poly)

def padded (m : List (List ℤ)) (ts : List Unit) (v : List ℤ) := NativePaddedWords.current (ts,Codec.input m v)

@[fun_prop] theorem padded_poly : Poly (fun x : Config × List ℤ => padded (matrix x.1) (ticks x.1) x.2) := by
  unfold padded Codec.input
  fun_prop

def forward (w : Str) : Str :=
  let p := ctx controls w
  input (split w).1 (padded (matrix p.1) (ticks p.1) (values p) ++ rests p)

include hc in
@[fun_prop] theorem forward_poly : Poly (forward controls) := by
  unfold forward
  dsimp only
  have hctx := ctx_poly controls hc
  have hp : Poly (fun w => padded (matrix (ctx controls w).1) (ticks (ctx controls w).1) (values (ctx controls w))) :=
    Poly.comp (f:=fun x : Config × List ℤ => padded (matrix x.1) (ticks x.1) x.2)
      (g:=fun w => ((ctx controls w).1,values (ctx controls w))) padded_poly
      (Poly.pair (Poly.comp Poly.fst hctx) (Poly.comp values_poly hctx))
  exact Poly.comp NativeTicketInteger.input_poly (Poly.pair (Poly.comp Poly.fst NativeTicketInteger.split_poly)
    (Poly.comp Poly.list_append (Poly.pair hp (Poly.comp rests_poly hctx))))

def dataRow (p : Indexed) : Str :=
  let width := span p.1.1 - (activeTicks p.1.1).length
  slice ((p.1.2,(ticks p.1.1).length+p.2*width),width)

@[fun_prop] theorem dataRow_poly : Poly dataRow := by unfold dataRow;fun_prop

@[fun_prop] theorem vectorInWord_poly : Poly Codec.vectorInWord := by
  unfold Codec.vectorInWord
  fun_prop

def recover (p : Indexed) : Str :=
  let ints := Codec.vectorInWord p.1.2
  let d := dataRow p
  let bits := NativeFixedBits.current (activeTicks p.1.1,((ints[p.2]?.getD 0)-offset p.1.1).toNat)
  take (d,start p.1.1) ++ bits ++ drop (d,start p.1.1)

section
attribute [local irreducible] dataRow Codec.vectorInWord NativeFixedBits.current
@[fun_prop] theorem recover_poly : Poly recover := by
  unfold recover
  fun_prop
end

def inverse (w : Str) : Str :=
  let p := ctx controls w
  input (split w).1 (((indices p).map (fun i => recover (p,i))).flatten)

include hc in
@[fun_prop] theorem inverse_poly : Poly (inverse controls) := by
  have h : Poly (fun p : Context => (indices p).map (fun i => recover (p,i))) :=
    Poly.list_map recover_poly indices_poly
  unfold inverse
  exact Poly.comp NativeTicketInteger.input_poly (Poly.pair (Poly.comp Poly.fst NativeTicketInteger.split_poly)
    (Poly.comp flatten_poly (Poly.comp h (ctx_poly controls hc))))

end InfoLossLAR.WorstCase.RectangularSource.Binary

end P2MDyadicModule186

/- Helper module RectBlocks. -/
section P2MDyadicModule187

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RectangularSource

open QAlgorithms QAlgorithms.Complexity

def flattenBlocks {n : ℕ} (r : Fin n → Str) := (List.ofFn r).flatten

theorem get_block {n : ℕ} (width : ℕ) (r : Fin n → Str) (hlen : ∀ i,(r i).length=width)
    (padding : Str) (i : Fin n) :
    (((flattenBlocks r ++ padding).drop (i.val*width)).take width) = r i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [flattenBlocks,List.ofFn_succ,List.flatten_cons,List.append_assoc]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,Nat.zero_mul,List.drop_zero]
      exact List.take_left' (hlen 0)
    · simp only [Fin.val_succ,Nat.succ_mul]
      rw [add_comm (j.val*width) width,← List.drop_drop,List.drop_left' (hlen 0)]
      exact ih (fun j => r j.succ) (fun j => hlen j.succ) j

theorem map_range {α : Type*} {n : ℕ} (f : ℕ → α) (v : Fin n → α)
    (he : ∀ i,f i.val = v i) : (List.range n).map f = List.ofFn v := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa using he ⟨i,by simpa using hj⟩

theorem coordinate_blocks {n W : ℕ} (r : Fin n → Bits W) :
    List.ofFn ((CoherentParallelTrials.coordinates W n).symm r) =
      flattenBlocks (fun i => List.ofFn (r i)) := by
  induction n with
  | zero =>
    simp [flattenBlocks,CoherentParallelTrials.width]
  | succ n ih =>
    rw [flattenBlocks,List.ofFn_succ,List.flatten_cons]
    change List.ofFn (Fin.append (r 0) ((CoherentParallelTrials.coordinates W n).symm (fun i => r i.succ))) = _
    rw [List.ofFn_fin_append,ih]
    rfl

end InfoLossLAR.WorstCase.RectangularSource

end P2MDyadicModule187

/- Helper module RectCodecExact. -/
section P2MDyadicModule188

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RectangularSource.Binary

open QAlgorithms.Complexity QMCNumericRuntime NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeTicketInteger (input)

variable {n : ℕ}

abbrev pieces (pre low post : Fin n → Str) (i : Fin n) := pre i ++ low i ++ post i

structure Fits (c : Config) (pre a post : Fin n → Str) : Prop where
  count : (matrix c).length=n
  width : ∀ i,(pieces pre a post i).length=span c
  preLength : ∀ i,(pre i).length=start c
  active : ∀ i,(a i).length=(activeTicks c).length

theorem erased_width {c : Config} {pre a post : Fin n → Str} (h : Fits c pre a post)
    (i : Fin n) : (pre i ++ post i).length=span c-(activeTicks c).length := by
  have hw := h.width i
  have ha := h.active i
  simp only [pieces,List.length_append] at hw ⊢
  omega

theorem decode_row {c : Config} {pre a post : Fin n → Str} (h : Fits c pre a post)
    (i : Fin n) :
    let p := (c,flattenBlocks (pieces pre a post))
    low (p,i.val)=a i ∧ rest (p,i.val)=pre i ++ post i := by
  have hel : row ((c,flattenBlocks (pieces pre a post)),i.val) = pieces pre a post i := by
    simpa only [row,slice,take,drop,List.append_nil] using get_block (span c) (pieces pre a post) h.width [] i
  dsimp only
  rw [low,rest,hel]
  simp only [slice,take,drop,pieces]
  have hd : (pre i++a i++post i).drop (start c+(activeTicks c).length)=post i := by
    rw [← h.preLength i,← h.active i,← List.length_append,List.drop_left]
  rw [hd,List.append_assoc,List.drop_left' (h.preLength i),List.take_left' (h.active i),
    List.take_left' (h.preLength i)]
  exact ⟨rfl,rfl⟩

def numbers (c : Config) (a : Fin n → Str) := List.ofFn (fun i => offset c + (bitValue (a i):ℤ))

theorem summaries {c : Config} {pre a post : Fin n → Str} (h : Fits c pre a post) :
    let p := (c,flattenBlocks (pieces pre a post))
    values p = numbers c a ∧ rests p = flattenBlocks (fun i => pre i ++ post i) := by
  constructor
  · unfold values indices numbers
    dsimp only
    rw [h.count]
    exact map_range _ _ (fun i => congrArg (fun b : Str => offset c + (bitValue b:ℤ)) (decode_row h i).1)
  · unfold rests indices flattenBlocks
    dsimp only
    rw [h.count]
    exact congrArg List.flatten (map_range _ _ (fun i => (decode_row h i).2))

variable (controls : Str → Config) (hdr : Str)

theorem forward_exact {pre a post : Fin n → Str} (h : Fits (controls hdr) pre a post) :
    forward controls (input hdr (flattenBlocks (pieces pre a post))) =
      input hdr (padded (matrix (controls hdr)) (ticks (controls hdr)) (numbers (controls hdr) a) ++
        flattenBlocks (fun i => pre i ++ post i)) := by
  simp only [forward,ctx,NativeTicketInteger.split_input,(summaries h).1,(summaries h).2]

private theorem pad_vec (c : Config) (z : List ℤ) (extra : Str)
    (hfit : (Codec.input (matrix c) z).length≤(ticks c).length) :
    Codec.vectorInWord (padded (matrix c) (ticks c) z++extra)=z := by
  rw [padded,NativePaddedWords.current_eq _ _ hfit,List.append_assoc,Codec.vectorInWord_input]

theorem restore_row {c : Config} {pre a post : Fin n → Str} (h : Fits c pre a post)
    (hfit : (Codec.input (matrix c) (numbers c a)).length≤(ticks c).length) (padding : Str) (i : Fin n) :
    let out := padded (matrix c) (ticks c) (numbers c a) ++ flattenBlocks (fun i => pre i ++ post i) ++ padding
    recover ((c,out),i.val) = pieces pre a post i := by
  let z := numbers c a
  let q := padded (matrix c) (ticks c) z
  let v := fun i => pre i ++ post i
  have hq : q.length=(ticks c).length := NativePaddedWords.current_length _ _
  have hd : dataRow ((c,q ++ flattenBlocks v ++ padding),i.val) = pre i ++ post i := by
    change ((q ++ flattenBlocks v ++ padding).drop ((ticks c).length+i.val*(span c-(activeTicks c).length))).take _ = _
    rw [List.append_assoc,←List.drop_drop,List.drop_left' hq]
    exact get_block _ _ (erased_width h) padding i
  have hz : Codec.vectorInWord (q++flattenBlocks v++padding) = z := by
    rw [List.append_assoc]
    exact pad_vec _ _ _ hfit
  have hget : (z[i.val]?).getD 0 = offset c + (bitValue (a i):ℤ) := by
    simp only [z,numbers,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  have hactive : activeTicks c=(a i).map (fun _ => ()) := by
    apply List.ext_getElem
    · simp [h.active]
    · simp
  dsimp only
  change take (dataRow ((c,q++flattenBlocks v++padding),i.val),start c) ++
    NativeFixedBits.current (activeTicks c,((Codec.vectorInWord (q++flattenBlocks v++padding))[i.val]?.getD 0-offset c).toNat) ++
    drop (dataRow ((c,q++flattenBlocks v++padding),i.val),start c) = _
  rw [hd,hz,hget,add_sub_cancel_left,Int.toNat_natCast,hactive,NativeFixedBits.current_recovers]
  rw [take,drop,List.take_left' (h.preLength i),List.drop_left' (h.preLength i)]

theorem inverse_exact {pre a post : Fin n → Str} (h : Fits (controls hdr) pre a post)
    (hfit : (Codec.input (matrix (controls hdr)) (numbers (controls hdr) a)).length≤(ticks (controls hdr)).length)
    (padding : Str) :
    inverse controls (forward controls (input hdr (flattenBlocks (pieces pre a post))) ++ padding) =
      input hdr (flattenBlocks (pieces pre a post)) := by
  rw [forward_exact controls hdr h]
  rw [show ∀ s : Str,input hdr s++padding=input hdr (s++padding) from by intro s;simp [NativeTicketInteger.input,List.append_assoc]]
  simp only [inverse,ctx,NativeTicketInteger.split_input,indices,h.count]
  apply congrArg (input hdr)
  exact congrArg List.flatten (map_range _ _ (fun i => restore_row h hfit padding i))

end InfoLossLAR.WorstCase.RectangularSource.Binary

end P2MDyadicModule188

/- Helper module RectLayout. -/
section P2MDyadicModule189

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

namespace InfoLossLAR.WorstCase.RectangularSource

open GaussianRandomizedRounding GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent

open GaussianRandomizedRounding.Wide.Coherent.Padding NativeWordLayout

open CoherentFirstSuccessNative CoherentRejection CoherentControlledSwap

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

noncomputable section

theorem extension_word (word : Str) {N : ℕ} (h : word.length ≤ N) :
    List.ofFn (fun i : Fin N => TM2Boolean.wordExtension word i.val) =
      word ++ List.replicate (N-word.length) false := by
  apply List.ext_getElem
  · simp;omega
  · intro i hi hj
    simp only [List.getElem_ofFn]
    by_cases hw : i < word.length
    · rw [List.getElem_append_left hw,TM2Boolean.wordExtension_before _ _ hw]
    · rw [List.getElem_append_right (by omega),List.getElem_replicate,TM2Boolean.wordExtension_after _ _ (by omega)]

theorem assembled {b m : ℕ} (out : Bits b) (copies : Fin m → Bits b) :
    List.ofFn (assembleRows out copies) = List.ofFn out ++ flattenBlocks (fun i => List.ofFn (copies i)) := by
  rw [List.ofFn_mul]
  have hh : (fun i : Fin (m+1) => List.ofFn (fun j : Fin b =>
      assembleRows out copies ⟨i.val*b+j.val,by nlinarith [j.isLt,Nat.mul_le_mul_right b i.isLt]⟩)) =
      (fun i : Fin (m+1) => List.ofFn (Fin.cases out copies i)) := by
    funext i
    apply congrArg List.ofFn
    funext j
    have he : (⟨i.val*b+j.val,by nlinarith [j.isLt,Nat.mul_le_mul_right b i.isLt]⟩ : Fin ((m+1)*b))=rowWire i j := by
      apply Fin.ext
      change i.val*b+j.val=j.val+b*i.val
      ring
    rw [he]
    simp only [assembleRows,rowWire,Equiv.symm_apply_apply]
  rw [hh,List.ofFn_succ]
  simp [flattenBlocks]

def lowWord (q : PointRequest) (i : Side (radius q)) : Str :=
  List.ofFn ((proposalTicket q).symm (active q i))

theorem low_value (q : PointRequest) (i : Side (radius q)) : QMCNumericRuntime.bitValue (lowWord q i) = i.val := by
  rw [lowWord,proposalTicket_value,Equiv.apply_symm_apply]
  rfl

section
attribute [local irreducible] proposalTicket active intervalCount
theorem binary_split (q : PointRequest) (K : ℕ) (hK : Nat.size (intervalCount q) ≤ K)
    (i : Side (radius q)) (y : Bits (K-Nat.size (intervalCount q))) :
    List.ofFn (activeBits q K hK (i,y)) = lowWord q i ++ List.ofFn y := by
  have hj : ∀ (k l t : ℕ) (h : k=l+t) (x : Bits l) (z : Bits t),
      List.ofFn ((bitsCast h).symm (Fin.append x z)) = List.ofFn x ++ List.ofFn z := by
    intro k l t h x z
    subst k
    rw [←List.ofFn_fin_append]
    rfl
  exact hj K (Nat.size (intervalCount q)) (K-Nat.size (intervalCount q)) (by omega)
    ((proposalTicket q).symm (active q i)) y
end

variable (request : Str → PointRequest × List Unit) (hr : Poly request)

abbrev junk (a : ℕ) (slots : List Unit) (word : Str) (K m : ℕ) :=
  Bits (K-Nat.size (intervalCount (request word).1)) × Retained (Bits (sourceWork request hr a slots K)) (Bits 4) m

def beginning (a : ℕ) (slots : List Unit) (word : Str) (K m : ℕ) (y : junk request hr a slots word K m) : Str :=
  List.ofFn (CoherentFirstSuccessNative.initialWork m (List.ofFn y.2.1)) ++ lengthToken slots ++ Builder.paddedPublic slots word

def ending (a : ℕ) (slots : List Unit) (word : Str) (K m : ℕ) (y : junk request hr a slots word K m) : Str :=
  List.ofFn y.1 ++ List.replicate (sourceWork request hr a slots K-(2*slots.length+1+K)) false ++
    flattenBlocks (fun i => List.ofFn (y.2.2 i).1) ++ List.ofFn (packJunk (fun i => (y.2.2 i).2))

theorem physical_block (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K) (m : ℕ)
    (i : Side (radius (request word).1)) (y : junk request hr a slots word K m) :
    List.ofFn (selected request hr a slots word K hK m (i,y)) =
      beginning request hr a slots word K m y ++ lowWord (request word).1 i ++ ending request hr a slots word K m y := by
  let tape := activeBits (request word).1 K hK (i,y.1)
  have hfit : (Builder.encoded slots word tape).length ≤ sourceWork request hr a slots K := by
    rw [Builder.encoded_length]
    unfold sourceWork Builder.Trial.workSize NativeWordLayout.width
    omega
  have hwork : List.ofFn (Builder.Trial.workTicket request hr a slots word K tape) =
      Builder.encoded slots word tape ++ List.replicate (sourceWork request hr a slots K-(2*slots.length+1+K)) false := by
    rw [←Builder.encoded_length slots word tape]
    exact extension_word (Builder.encoded slots word tape) hfit
  change List.ofFn (Fin.append (Fin.append _ (assembleRows (Builder.Trial.workTicket request hr a slots word K tape)
      (fun i => (y.2.2 i).1))) _) = _
  simp only [List.ofFn_fin_append,assembled,hwork,Builder.encoded,Builder.rawInput,tape,binary_split,
    beginning,ending,List.append_assoc]
  rfl

end

end InfoLossLAR.WorstCase.RectangularSource

end P2MDyadicModule189

/- Helper module RectEncoded. -/
section P2MDyadicModule190

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.RectangularSource

open GaussianRandomizedRounding GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent

open GaussianRandomizedRounding.Wide.Coherent.Padding NativeWordLayout NativeDualQuotient

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Binary

noncomputable section

variable (request : Str → PointRequest × List Unit) (hr : Poly request)

variable (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (hK : Nat.size (intervalCount (request word).1) ≤ K) (m n : ℕ)

abbrev E := embedding (selected request hr a slots word K hK m) n

abbrev W := CoherentParallelTrials.width (sourceWidth request hr a slots K m) n

abbrev X := Fin n → Side (radius (request word).1)

abbrev Y := Fin n → junk request hr a slots word K m

def raw (hdr : Str) (v : X request word n × Y request hr a slots word K m n) :=
  NativeTicketInteger.input hdr (List.ofFn (E request hr a slots word K hK m n v))

def frame (c : Binary.Config) : Prop :=
  Binary.span c=sourceWidth request hr a slots K m ∧
  Binary.start c=NativeWordLayout.width CoherentFirstSuccessNative.P m+2*slots.length+1 ∧
  (Binary.activeTicks c).length=Nat.size (intervalCount (request word).1) ∧
  (Binary.matrix c).length=n ∧ Binary.offset c= -(radius (request word).1:ℤ)

def saved (y : Y request hr a slots word K m n) :=
  flattenBlocks (fun i => beginning request hr a slots word K m (y i) ++ ending request hr a slots word K m (y i))

def signed (x : X request word n) := List.ofFn ((box n (radius (request word).1)) x)

theorem low_signed (c : Binary.Config) (hc : frame request hr a slots word K m n c) (x : X request word n) :
    Binary.numbers c (fun i => lowWord (request word).1 (x i)) = signed request word n x := by
  apply congrArg List.ofFn
  funext i
  simp only [low_value,hc.2.2.2.2,box,Function.Embedding.coeFn_mk,coord_apply,windowPoint,AFT.RationalNumerics.centeredGaussianAnchor]
  norm_num
  ring

theorem raw_blocks (hdr : Str) (x : X request word n) (y : Y request hr a slots word K m n) :
    raw request hr a slots word K hK m n hdr (x,y) = NativeTicketInteger.input hdr
      (flattenBlocks (Binary.pieces (fun i => beginning request hr a slots word K m (y i))
        (fun i => lowWord (request word).1 (x i)) (fun i => ending request hr a slots word K m (y i)))) := by
  unfold raw
  rw [show E request hr a slots word K hK m n (x,y) = (CoherentParallelTrials.coordinates _ n).symm
    (fun i => selected request hr a slots word K hK m (x i,y i)) from rfl,coordinate_blocks]
  simp only [physical_block]

include hK in
theorem pieces_fit (c : Binary.Config) (hc : frame request hr a slots word K m n c)
    (x : X request word n) (y : Y request hr a slots word K m n) :
    Binary.Fits c (fun i => beginning request hr a slots word K m (y i)) (fun i => lowWord (request word).1 (x i))
      (fun i => ending request hr a slots word K m (y i)) := by
  refine ⟨hc.2.2.2.1,?_,?_,?_⟩
  · intro i
    rw [hc.1]
    exact (congrArg List.length (physical_block request hr a slots word K hK m (x i) (y i))).symm.trans List.length_ofFn
  · intro i
    simp only [beginning,List.length_append,List.length_ofFn,lengthToken,List.length_map,List.length_singleton,
      Builder.paddedPublic_length,hc.2.1]
    omega
  · intro i
    simp [lowWord,hc.2.2.1]

variable (controls : Str → Config) (hcontrols : Poly controls) (hdr : Str)

variable (hc : frame request hr a slots word K m n (controls hdr))

include hc in
theorem destination (x : X request word n) (y : Y request hr a slots word K m n) :
    Binary.forward controls (raw request hr a slots word K hK m n hdr (x,y)) =
      NativeTicketInteger.input hdr (Binary.padded (Binary.matrix (controls hdr)) (Binary.ticks (controls hdr)) (signed request word n x) ++
        saved request hr a slots word K m n y) := by
  rw [raw_blocks,Binary.forward_exact controls hdr (pieces_fit request hr a slots word K hK m n _ hc x y),
    low_signed request hr a slots word K m n _ hc x]
  rfl

end

end InfoLossLAR.WorstCase.RectangularSource

end P2MDyadicModule190

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingNativeInitial. -/
section P2MDyadicModule191

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.NativeInitial

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordLayout NativeWordCoherent

open CoherentComputeUncompute

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable (request : Str→PointRequest×List Unit) (hr : Poly request) (a : ℕ)

abbrev Input := List Unit×(List Unit×(List Unit×Str))

abbrev program := NativeWordCoherent.P (gateWord request a) (gateWord_poly request hr a) (wordBound request hr a)

def headerWord (x : Input) : Str := Preparation.builderHeader x.1 x.2.2.2++x.2.1.map (fun _ => false)

@[fun_prop] theorem headerWord_poly : Poly headerWord := by unfold headerWord;fun_prop

@[simp] theorem headerWord_length (x : Input) : (headerWord x).length=2*x.1.length+1+x.2.1.length := by
  simp only [headerWord,List.length_append,Preparation.builderHeader_length,List.length_map]

def clock (x : Input) : Str := (headerWord x).map (fun _ => true)

@[fun_prop] theorem clock_poly : Poly clock := by unfold clock;fun_prop

theorem clock_exact (x : Input) : clock x=unary (2*x.1.length+1+x.2.1.length) := by
  simp only [clock,List.map_const',headerWord_length,unary]

def workTicks (x : Input) : List Unit :=
  (NativeWordDescription.totalSlots (program request hr a) (clock x)).take
    (machineWidth (program request hr a) (clock x))

@[fun_prop] theorem workTicks_poly : Poly (workTicks request hr a) := by
  unfold workTicks
  exact Poly.comp (g:=fun x : Input =>
    (NativeWordDescription.totalSlots (program request hr a) (clock x),machineWidth (program request hr a) (clock x)))
    (f:=fun x : List Unit×ℕ => x.1.take x.2) QMCNumericRuntime.parser_take_poly (by fun_prop)

theorem workTicks_length (x : Input) :
    (workTicks request hr a x).length=Trial.workSize request hr a x.1 x.2.1.length := by
  unfold workTicks
  rw [clock_exact,machineWidth_eq,List.length_take]
  have h:=NativeWordDescription.totalSlots_bound (program request hr a) (2*x.1.length+1+x.2.1.length)
  exact Nat.min_eq_left (by omega)

def rowWord (x : Input) : Str :=
  (headerWord x++(workTicks request hr a x).map (fun _ => false)).take (workTicks request hr a x).length

@[fun_prop] theorem rowWord_poly : Poly (rowWord request hr a) := by
  unfold rowWord
  exact Poly.comp (g:=fun x : Input =>
    (headerWord x++(workTicks request hr a x).map (fun _ => false),(workTicks request hr a x).length))
    QMCNumericRuntime.parser_take_poly (by fun_prop)

theorem rowWord_ofFn (x : Input) : rowWord request hr a x=
    List.ofFn (fun i : Fin (workTicks request hr a x).length => wordExtension (headerWord x) i.val) := by
  apply List.ext_getElem
  · simp only [rowWord,List.length_take,List.length_append,List.length_map,List.length_ofFn]
    omega
  · intro i hi hj
    simp only [rowWord,List.getElem_take,List.getElem_ofFn]
    by_cases h : i<(headerWord x).length
    · rw [List.getElem_append_left h,wordExtension_before _ _ h]
    · rw [List.getElem_append_right (by omega),List.getElem_map,wordExtension_after _ _ (by omega)]

def placement (x : Input) : CoherentFirstSuccessNative.PlacementRequest :=
  ((x.2.2.1,workTicks request hr a x),List.replicate 4 ())

@[fun_prop] theorem placement_poly : Poly (placement request hr a) := by unfold placement;fun_prop

def format (x : Input) : Str :=
  CoherentFirstSuccessNative.InitialNative.format (placement request hr a x,rowWord request hr a x)

@[fun_prop] theorem format_poly : Poly (format request hr a) := by unfold format;fun_prop

theorem format_exact (x : Input) : format request hr a x=
    List.ofFn (CoherentFirstSuccessNative.copyEncoding (workTicks request hr a x).length x.2.2.1.length 4
      (fun _ => Fin.append (Fin.append (fun i => wordExtension (headerWord x) i.val)
        (fun _ : Fin 1 => false)) (fun _ : Fin 4 => false))) := by
  unfold format
  rw [rowWord_ofFn]
  exact CoherentFirstSuccessNative.InitialNative.format_copyEncoding (placement request hr a x) _

theorem format_basisInput (x : Input) : format request hr a x=
    List.ofFn (Pipeline.basisInput request hr a x.1 x.2.2.2 x.2.1.length x.2.2.1.length) := by
  rw [format_exact,workTicks_length]
  simp only [Pipeline.basisInput,Pipeline.initialBasis_append,headerWord,Trial.workTicket,
    NativeWordCoherent.initialWork,encoded,rawInput,Preparation.builderHeader,List.map_const',List.ofFn_const]
  rfl

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.NativeInitial

end

end P2MDyadicModule191

/- Helper module Solutions.AdvantageBridgeBodyDEmission. -/
section P2MDyadicModule192

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

theorem leftCircuit_instructionWords {n m : ℕ} (circuit : Layered n) :
    (leftCircuit (m := m) circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by
  have hg (gate : Instr n) : encInstr (leftInstruction (m := m) gate)=encInstr gate := by cases gate <;> rfl
  simp only [leftCircuit,List.map_map,Function.comp_def,hg]

theorem rightCircuit_instructionWords_congr {n : ℕ} (left right : ℕ) (he : left=right) (circuit : Layered n) :
    (rightCircuit (n := left) circuit).map (List.map encInstr)=
      (rightCircuit (n := right) circuit).map (List.map encInstr) := by cases he; rfl

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2PlatformSerialization

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule192

/- Helper module Solutions.RegevBridgeCoherentParallelEmitter. -/
section P2MDyadicModule193

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentParallelTrials

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

abbrev Request := List Unit×(Str×List (List Str))

/-- Supplied public unary slots bound both the number of repetitions and
the physical width. Offsets are computed by the existing total native emitter. -/
def emittedLayers (x : Request) : List (List Str) :=
  bundleCircuitWordLayers (x.1.map (fun _ => (x.2.1,([false],x.2.2))))

@[fun_prop] theorem emittedLayers_poly : Poly emittedLayers := by unfold emittedLayers;fun_prop

theorem emittedLayers_code {n : ℕ} (trial : Layered n) (m : ℕ) :
    emittedLayers (List.replicate m (), (unary n,trial.map (List.map encInstr)))=
      (circuit trial m).map (List.map encInstr) := by
  simp only [emittedLayers,List.map_replicate]
  induction m with
  | zero => rfl
  | succ m ih =>
    change bundleCircuitWordLayers
        (List.replicate (m+1) (unary n,([false],trial.map (List.map encInstr))))=
      (leftCircuit trial++rightCircuit (circuit trial m)).map (List.map encInstr)
    rw [List.replicate_succ,bundleCircuitWordLayers_cons]
    simp only [List.map_append,leftCircuit_instructionWords,shiftCircuitWords_zero]
    rw [ih,shiftCircuitWords_correct]
    have he : (unary n).length=n := by simp [unary]
    rw [rightCircuit_instructionWords_congr _ _ he]

end InfoLossLAR.WorstCase.CoherentParallelTrials

end P2MDyadicModule193

/- Helper module Solutions.RegevBridgeCoherentPipelineEmitter. -/
section P2MDyadicModule194

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordDescription NativeWordLayout

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

/-- Repetition/output/junk unary capacities, a global unary wire bound,
and an actual finite trial's instruction words. -/
abbrev PipelineRequest := PlacementRequest×(List Unit×List (List Str))

def parallelWords (x : PipelineRequest) : List (List Str) :=
  CoherentParallelTrials.emittedLayers
    (x.1.1.1,((trialTicks x.1).map (fun _ => true),x.2.2))

@[fun_prop] theorem parallelWords_poly : Poly parallelWords := by unfold parallelWords;fun_prop

private theorem unit_replicate (xs : List Unit) : xs=List.replicate xs.length () := by
  apply List.eq_replicate_iff.mpr
  exact ⟨rfl,fun _ _ => Subsingleton.elim _ _⟩

theorem parallelWords_code (x : PlacementRequest)
    (trial : Layered (x.1.2.length+1+x.2.length)) (ticks : List Unit) :
    parallelWords (x,(ticks,trial.map (List.map encInstr)))=
      (CoherentParallelTrials.circuit trial x.1.1.length).map (List.map encInstr) := by
  unfold parallelWords
  have hh : (trialTicks x).map (fun _ => true)=unary (x.1.2.length+1+x.2.length) := by
    simp only [List.map_const',trialTicks_length,unary]
  rw [hh]
  exact (congrArg (fun slots : List Unit => CoherentParallelTrials.emittedLayers
    (slots,(unary (x.1.2.length+1+x.2.length),trial.map (List.map encInstr))))
    (unit_replicate x.1.1)).trans (CoherentParallelTrials.emittedLayers_code trial x.1.1.length)

def pipelineWords (x : PipelineRequest) : List (List Str) :=
  relocatedWordLayers (x.2.1,(publicLayout x.1,parallelWords x))++publicLayers x.1.1

@[fun_prop] theorem pipelineWords_poly : Poly pipelineWords := by
  have hl : Poly (fun x : PipelineRequest => relocatedWordLayers (x.2.1,(publicLayout x.1,parallelWords x))) := by fun_prop
  have hr : Poly (fun x : PipelineRequest => publicLayers x.1.1) :=
    Poly.comp publicLayers_poly (by fun_prop)
  unfold pipelineWords
  exact Poly.comp Poly.list_append (Poly.pair hl hr)

theorem pipelineWords_code (x : PlacementRequest)
    (trial : Layered (x.1.2.length+1+x.2.length)) (ticks : List Unit)
    (ht : width P x.1.1.length+(x.1.1.length+1)*x.1.2.length+x.1.1.length*x.2.length≤ticks.length) :
    pipelineWords (x,(ticks,trial.map (List.map encInstr)))=
      (pipelineCircuit x.1.2.length x.1.1.length x.2.length trial).map (List.map encInstr) := by
  unfold pipelineWords
  rw [publicLayout_exact,parallelWords_code,relocatedWordLayers_exact _ _ ticks ht,publicLayers_code]
  simp only [pipelineCircuit,List.map_append,parallelPreparation,fullCircuit,leftCircuit_instructionWords]

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule194

/- Helper module RectEmit. -/
section P2MDyadicModule195

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource.Emit

open QAlgorithms QAlgorithms.Complexity

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent.Padding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

open CoherentFirstSuccessNative NativeWordLayout NativeWordDescription TM2Boolean.RPN FiniteGateTransport

open GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

abbrev U := NativeInitial.Input

variable (request : Str → PointRequest × List Unit) (hr : Poly request) (a b : ℕ) (q : Polynomial ℕ)

def hadamards (x : U) := (Preparation.ticketPositions (x.1,x.2.1)).map
  (fun i => [encNat 0 ++ boundedNat ((NativeInitial.clock x).map (fun _ => ())) i])

@[fun_prop] theorem hadamards_poly : Poly hadamards := by unfold hadamards;fun_prop

theorem hadamards_code (x : U) :
    hadamards x =
      (Pipeline.proposalCircuit request hr a x.1 x.2.2.2 x.2.1.length).map (List.map encInstr) := by
  unfold hadamards Preparation.ticketPositions Pipeline.proposalCircuit Pipeline.fixedProposalCircuit
  rw [coinCircuit_direct]
  simp only [relocateCircuit,List.map_ofFn,Function.comp_def,List.map_cons,List.map_nil,relocateInstr,encInstr]
  rw [List.map_map]
  apply map_range
  intro i
  simp only [Function.comp_apply,Pipeline.fixedTicketWires,Function.Embedding.coeFn_mk,Fin.val_mk]
  have hi : 2*x.1.length+1+i.val ≤ ((NativeInitial.clock x).map (fun _ => ())).length := by
    rw [NativeInitial.clock_exact,List.length_map,unary,List.length_replicate]
    omega
  rw [boundedNat_eq _ _ hi]

def rawTrial (x : U) := hadamards x ++ NativeWordDescription.layerWords (gateWord request a) (gateWord_poly request hr a)
  (wordBound request hr a) q b (NativeInitial.clock x)

@[fun_prop] theorem rawTrial_poly : Poly (rawTrial request hr a b q) := by
  unfold rawTrial
  exact Poly.comp Poly.list_append (Poly.pair hadamards_poly
    (Poly.comp (NativeWordDescription.layerWords_poly _ _ _ _ _) NativeInitial.clock_poly))

def budget (x : U) : List Unit := List.replicate (q.eval (2*x.1.length+1+x.2.1.length)) ()

theorem trial_code (x : U) : rawTrial request hr a b q x =
    (Pipeline.trialCircuit request hr a b x.1 x.2.2.2 x.2.1.length (budget q x)).map (List.map encInstr) := by
  rw [rawTrial,hadamards_code request hr a,NativeInitial.clock_exact,NativeWordDescription.layerWords_code]
  exact (List.map_append ..).symm

def slots (x : U) := (NativeInitial.format request hr a x).map (fun _ => ())

@[fun_prop] theorem slots_poly : Poly (slots request hr a) := by unfold slots;fun_prop

theorem slots_length (x : U) : (slots request hr a x).length =
    sourceWidth request hr a x.1 x.2.1.length x.2.2.1.length := by
  simp only [slots,List.length_map,NativeInitial.format_basisInput,List.length_ofFn]

def one (x : U) := pipelineWords (NativeInitial.placement request hr a x,
  (slots request hr a x, rawTrial request hr a b q x))

@[fun_prop] theorem one_poly : Poly (one request hr a b q) := by unfold one;fun_prop

private theorem unit_eq (x : List Unit) : x=List.replicate x.length () :=
  List.eq_replicate_iff.mpr ⟨rfl,fun _ _ => Subsingleton.elim _ _⟩

private theorem pipeline_of_lengths (tries work junk cap : List Unit) (w k : ℕ)
    (hw : work.length=w) (hk : junk.length=k)
    (hcap : width CoherentFirstSuccessNative.P tries.length+(tries.length+1)*w+tries.length*k≤cap.length)
    (trial : Layered (w+1+k)) :
    pipelineWords (((tries,work),junk),(cap,trial.map (List.map encInstr))) =
      (pipelineCircuit w tries.length k trial).map (List.map encInstr) := by
  subst w k
  exact pipelineWords_code ((tries,work),junk) trial cap hcap

theorem one_code (x : U) : one request hr a b q x =
    (Pipeline.circuit request hr a b x.1 x.2.2.2 x.2.1.length (budget q x) x.2.2.1.length).map (List.map encInstr) := by
  unfold one NativeInitial.placement
  rw [trial_code]
  exact pipeline_of_lengths x.2.2.1 (NativeInitial.workTicks request hr a x) (List.replicate 4 ())
    (slots request hr a x) (sourceWork request hr a x.1 x.2.1.length) 4 (NativeInitial.workTicks_length _ _ _ _) (List.length_replicate)
    (slots_length request hr a x).symm.le _

abbrev Input := U × List Unit

def many (x : Input) := CoherentParallelTrials.emittedLayers (x.2,((slots request hr a x.1).map (fun _ => true),
  one request hr a b q x.1))

@[fun_prop] theorem many_poly : Poly (many request hr a b q) := by unfold many;fun_prop

theorem many_code (x : U) (ns : List Unit) :
    many request hr a b q (x,ns) =
      (CoherentParallelTrials.circuit (Pipeline.circuit request hr a b x.1 x.2.2.2 x.2.1.length (budget q x)
        x.2.2.1.length) ns.length).map (List.map encInstr) := by
  unfold many
  rw [one_code]
  have hs : (slots request hr a x).map (fun _ => true) = unary (sourceWidth request hr a x.1 x.2.1.length x.2.2.1.length) := by
    simp only [List.map_const',slots_length,unary]
  rw [hs]
  refine Eq.trans ?_ (CoherentParallelTrials.emittedLayers_code _ ns.length)
  exact congrArg (fun ts : List Unit => CoherentParallelTrials.emittedLayers
    (ts,(unary (sourceWidth request hr a x.1 x.2.1.length x.2.2.1.length),
      (Pipeline.circuit request hr a b x.1 x.2.2.2 x.2.1.length (budget q x) x.2.2.1.length).map (List.map encInstr)))) (unit_eq ns)

def initial (x : Input) := x.2.flatMap (fun _ => NativeInitial.format request hr a x.1)

@[fun_prop] theorem initial_poly : Poly (initial request hr a) := by unfold initial;fun_prop

theorem initial_code (x : U) (ns : List Unit) :
    initial request hr a (x,ns) = List.ofFn ((CoherentParallelTrials.coordinates
      (sourceWidth request hr a x.1 x.2.1.length x.2.2.1.length) ns.length).symm
      (fun _ => Pipeline.basisInput request hr a x.1 x.2.2.2 x.2.1.length x.2.2.1.length)) := by
  rw [coordinate_blocks]
  simp [initial,flattenBlocks,NativeInitial.format_basisInput,List.flatMap_def]

end InfoLossLAR.WorstCase.RectangularSource.Emit

end

end P2MDyadicModule195

/- Helper module Solutions.RegevBridgeQuantumXorError. -/
section P2MDyadicModule196

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

noncomputable section

namespace InfoLossLAR.WorstCase.QuantumXorOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute ControlledNativeGates

variable {W k : ℕ}

theorem run_error {n : ℕ} (U : Layered n) (φ ψ : QState n) :
    stateNorm (runLayered U φ-runLayered U ψ)=stateNorm (φ-ψ) := by
  rw [←runLayeredLinearMap_apply,←runLayeredLinearMap_apply,←map_sub,runLayeredLinearMap_apply]
  exact (circuitIsometry U).norm_map (WithLp.toLp 2 (φ-ψ))

end InfoLossLAR.WorstCase.QuantumXorOracle

end

end P2MDyadicModule196

/- Helper module Solutions.RegevBridgeGaussianCosetNormalization. -/
section P2MDyadicModule197

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ} {Label : Type*}

/-- Every exact ambient-to-coset bijection accounts for the whole Gaussian
normalizer, including all source points in all residues. -/
theorem gaussian_coset_normalizers
    (ambient coarse : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology ambient] [IsZLattice ℝ ambient]
    (shifts : Label → Space (dimension:=dimension)) (equivalence : ambient ≃ Label×coarse)
    (hcoordinates : ∀ pair : Label×coarse,
      ((equivalence.symm pair : ambient) : Space (dimension:=dimension))=(pair.2 : Space (dimension:=dimension))+shifts pair.1)
    (width : ℝ) (hwidth : 0 < width) :
    Summable (fun label => rhoCoset width coarse (shifts label)) ∧
      (∑' label,rhoCoset width coarse (shifts label))=rhoCoset width ambient 0 := by
  have hs := summable_gaussian_lattice ambient width hwidth
  have hpairs : Summable (fun pair : Label×coarse =>
      rho width ((pair.2 : Space (dimension:=dimension))+shifts pair.1)) := by
    have h := equivalence.symm.summable_iff.mpr hs
    simpa only [Function.comp_def,hcoordinates] using h
  have hreindex := equivalence.symm.tsum_eq (fun point : ambient => rho width (point : Space (dimension:=dimension)))
  simp only [hcoordinates] at hreindex
  rw [hpairs.tsum_prod] at hreindex
  refine ⟨hpairs.prod,?_⟩
  simpa only [rhoCoset,add_zero] using hreindex

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule197

/- Helper module Solutions.RegevBridgeGaussianCosetJunk. -/
section P2MDyadicModule198

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ} {Label : Type*}

/-- The actual positive coherent residue amplitude is fixed by the true
Gaussian mass of each actual coset, including its complete normalizer. -/
def gaussianCosetJunk
    (ambient coarse : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology ambient] [IsZLattice ℝ ambient] [DiscreteTopology coarse] [IsZLattice ℝ coarse]
    (shifts : Label → Space (dimension:=dimension)) (equivalence : ambient ≃ Label×coarse)
    (hcoordinates : ∀ pair : Label×coarse,
      ((equivalence.symm pair : ambient) : Space (dimension:=dimension))=(pair.2 : Space (dimension:=dimension))+shifts pair.1)
    (width : ℝ) (hwidth : 0 < width) : Hilbert Label := by
  refine ⟨fun label => (Real.sqrt (rhoCoset width coarse (shifts label)/rhoCoset width ambient 0) : ℂ),?_⟩
  apply memℓp_gen
  have hs := (gaussian_coset_normalizers ambient coarse shifts equivalence hcoordinates width hwidth).1
  have hnonnegative (label : Label) : 0 ≤ rhoCoset width coarse (shifts label)/rhoCoset width ambient 0 :=
    div_nonneg (rhoCoset_pos coarse width hwidth _).le (rhoCoset_zero_pos ambient width hwidth).le
  have hterm (label : Label) : ‖(Real.sqrt (rhoCoset width coarse (shifts label)/rhoCoset width ambient 0) : ℂ)‖^2=
      rhoCoset width coarse (shifts label)/rhoCoset width ambient 0 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hnonnegative label)]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,hterm] using hs.div_const (rhoCoset width ambient 0)

theorem gaussianCosetJunk_apply
    (ambient coarse : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology ambient] [IsZLattice ℝ ambient] [DiscreteTopology coarse] [IsZLattice ℝ coarse]
    (shifts : Label → Space (dimension:=dimension)) (equivalence : ambient ≃ Label×coarse)
    (hcoordinates : ∀ pair : Label×coarse,
      ((equivalence.symm pair : ambient) : Space (dimension:=dimension))=(pair.2 : Space (dimension:=dimension))+shifts pair.1)
    (width : ℝ) (hwidth : 0 < width) (label : Label) :
    gaussianCosetJunk ambient coarse shifts equivalence hcoordinates width hwidth label=
      (Real.sqrt (rhoCoset width coarse (shifts label)/rhoCoset width ambient 0) : ℂ) := rfl

theorem gaussianCosetJunk_norm
    (ambient coarse : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology ambient] [IsZLattice ℝ ambient] [DiscreteTopology coarse] [IsZLattice ℝ coarse]
    (shifts : Label → Space (dimension:=dimension)) (equivalence : ambient ≃ Label×coarse)
    (hcoordinates : ∀ pair : Label×coarse,
      ((equivalence.symm pair : ambient) : Space (dimension:=dimension))=(pair.2 : Space (dimension:=dimension))+shifts pair.1)
    (width : ℝ) (hwidth : 0 < width) :
    ‖gaussianCosetJunk ambient coarse shifts equivalence hcoordinates width hwidth‖=1 := by
  have hs := (gaussian_coset_normalizers ambient coarse shifts equivalence hcoordinates width hwidth).2
  have hterm (label : Label) :
      ‖gaussianCosetJunk ambient coarse shifts equivalence hcoordinates width hwidth label‖^2=
        rhoCoset width coarse (shifts label)/rhoCoset width ambient 0 := by
    rw [gaussianCosetJunk_apply,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_nonneg (rhoCoset_pos coarse width hwidth _).le (rhoCoset_zero_pos ambient width hwidth).le)]
  have hnorm : ‖gaussianCosetJunk ambient coarse shifts equivalence hcoordinates width hwidth‖^2=1 := by
    rw [hilbert_norm_sq]
    simp only [hterm]
    rw [tsum_div_const,hs,div_self (rhoCoset_zero_pos ambient width hwidth).ne']
  nlinarith [norm_nonneg (gaussianCosetJunk ambient coarse shifts equivalence hcoordinates width hwidth)]

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule198

/- Helper module Solutions.RegevBridgeCoherentHilbertFibers. -/
section P2MDyadicModule199

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

theorem lp_two_norm_sq {Index : Type*} {Carrier : Index → Type*}
    [∀ index,NormedAddCommGroup (Carrier index)] (value : lp Carrier 2) :
    ‖value‖^2=∑' index,‖value index‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p:=(2 : ENNReal)) (by norm_num) value

variable {Label Carrier : Type*} [NormedAddCommGroup Carrier] [NormedSpace ℂ Carrier]

/-- Every label and its amplitude are retained. The conditional pure
states may depend arbitrarily on the label. -/
def coherentFiberState (junk : Hilbert Label) (branches : Label → Carrier)
    (hbranches : ∀ label,‖branches label‖=1) : lp (fun _ : Label => Carrier) 2 := by
  refine ⟨fun label => junk label • branches label,?_⟩
  apply memℓp_gen
  have hs : Summable (fun label => ‖junk label‖^2) := by
    simpa using (lp.memℓp junk).summable (by norm_num)
  simpa [norm_smul,hbranches] using hs

theorem coherentFiberState_apply (junk : Hilbert Label) (branches : Label → Carrier)
    (hbranches : ∀ label,‖branches label‖=1) (label : Label) :
    coherentFiberState junk branches hbranches label=junk label • branches label := rfl

/-- Uniform conditional amplitude bounds control the entire coherent
state, retaining the complete label distribution and all its phases. -/
theorem coherentFiberState_distance
    (junk : Hilbert Label) (hjunk : ‖junk‖=1) (branches : Label → Carrier)
    (hbranches : ∀ label,‖branches label‖=1) (target : Carrier) (htarget : ‖target‖=1)
    (error : ℝ) (herror : 0 ≤ error) (hclose : ∀ label,‖branches label-target‖ ≤ error) :
    ‖coherentFiberState junk branches hbranches-
      coherentFiberState junk (fun _ => target) (fun _ => htarget)‖ ≤ error := by
  apply (sq_le_sq₀ (norm_nonneg _) herror).mp
  rw [lp_two_norm_sq]
  have hjunkSummable : Summable (fun label => ‖junk label‖^2) := by
    simpa using (lp.memℓp junk).summable (by norm_num)
  have hsource : Summable (fun label => ‖(coherentFiberState junk branches hbranches-
      coherentFiberState junk (fun _ => target) (fun _ => htarget)) label‖^2) := by
    simpa using (lp.memℓp (coherentFiberState junk branches hbranches-
      coherentFiberState junk (fun _ => target) (fun _ => htarget))).summable (by norm_num)
  have hpoint (label : Label) : ‖(coherentFiberState junk branches hbranches-
      coherentFiberState junk (fun _ => target) (fun _ => htarget)) label‖^2 ≤ ‖junk label‖^2*error^2 := by
    rw [lp.coeFn_sub,Pi.sub_apply,coherentFiberState_apply,coherentFiberState_apply,←smul_sub,norm_smul,mul_pow]
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) herror).mpr (hclose label)) (sq_nonneg _)
  have h := hsource.tsum_le_tsum hpoint (hjunkSummable.mul_right (error^2))
  rw [tsum_mul_right,←hilbert_norm_sq,hjunk,one_pow,one_mul] at h
  exact h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule199

/- Helper module Solutions.RegevBridgeHilbertFlatten. -/
section P2MDyadicModule200

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- Flatten the complete coherent label/main registers by their literal
coordinate pair. Every register and every amplitude remains represented. -/
def hilbertFlatten {Label Index : Type*} (value : lp (fun _ : Label => Hilbert Index) 2) : Hilbert (Label×Index) := by
  classical
  refine ⟨fun pair => value pair.1 pair.2,?_⟩
  apply memℓp_gen' (C:=‖value‖^2)
  intro selected
  let labels := selected.image Prod.fst
  let indices := selected.image Prod.snd
  have hsubset : selected ⊆ labels×ˢindices := by
    intro pair hpair
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨pair,hpair,rfl⟩,Finset.mem_image.mpr ⟨pair,hpair,rfl⟩⟩
  have hsum : (∑ pair ∈ selected,‖value pair.1 pair.2‖^2) ≤
      ∑ label ∈ labels,∑ index ∈ indices,‖value label index‖^2 := by
    have hrectangle := Finset.sum_product labels indices (fun pair : Label×Index => ‖value pair.1 pair.2‖^2)
    have hboundRectangle : (∑ pair ∈ selected,‖value pair.1 pair.2‖^2) ≤
        ∑ pair ∈ labels×ˢindices,‖value pair.1 pair.2‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun pair _ _ => sq_nonneg _)
    exact hboundRectangle.trans_eq hrectangle
  have hinner (label : Label) : (∑ index ∈ indices,‖value label index‖^2) ≤ ‖value label‖^2 := by
    simpa using lp.sum_rpow_le_norm_rpow (p:=(2 : ENNReal)) (by norm_num) (value label) indices
  have houter : (∑ label ∈ labels,‖value label‖^2) ≤ ‖value‖^2 := by
    simpa using lp.sum_rpow_le_norm_rpow (p:=(2 : ENNReal)) (by norm_num) value labels
  have hbound := hsum.trans ((Finset.sum_le_sum (fun label (_ : label ∈ labels) => hinner label)).trans houter)
  simpa using hbound

theorem hilbertFlatten_apply {Label Index : Type*} (value : lp (fun _ : Label => Hilbert Index) 2) (pair : Label×Index) :
    hilbertFlatten value pair=value pair.1 pair.2 := rfl

/-- The full flattening preserves the actual infinite Hilbert norm. -/
theorem hilbertFlatten_norm {Label Index : Type*} (value : lp (fun _ : Label => Hilbert Index) 2) :
    ‖hilbertFlatten value‖=‖value‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hilbert_norm_sq,lp_two_norm_sq]
  have hs : Summable (fun pair : Label×Index => ‖hilbertFlatten value pair‖^2) := by
    simpa using (lp.memℓp (hilbertFlatten value)).summable (by norm_num)
  rw [hs.tsum_prod]
  simp only [hilbertFlatten_apply,←hilbert_norm_sq]

def hilbertFlattenIsometry {Label Index : Type*} :
    lp (fun _ : Label => Hilbert Index) 2 →ₗᵢ[ℂ] Hilbert (Label×Index) where
  toFun := hilbertFlatten
  map_add' first second := by ext pair;rfl
  map_smul' scalar value := by ext pair;rfl
  norm_map' := hilbertFlatten_norm

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule200

/- Helper module Solutions.RegevBridgeGaussianCosetFactorization. -/
section P2MDyadicModule201

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ} {Label : Type*}

/-- The genuine ambient Gaussian amplitude decomposes exactly into the
normalized Gaussian on its actual lattice coset and its genuine residue
amplitude. All factors are positive, fixing the coherent phase. -/
theorem gaussianCoset_amplitude_factor
    (ambient coarse : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology ambient] [IsZLattice ℝ ambient] [DiscreteTopology coarse] [IsZLattice ℝ coarse]
    (shifts : Label → Space (dimension:=dimension)) (equivalence : ambient ≃ Label×coarse)
    (hcoordinates : ∀ pair : Label×coarse,
      ((equivalence.symm pair : ambient) : Space (dimension:=dimension))=(pair.2 : Space (dimension:=dimension))+shifts pair.1)
    (width : ℝ) (hwidth : 0 < width) (pair : Label×coarse) :
    gaussianAmplitude ambient width 0 (equivalence.symm pair)=
      Real.sqrt (rhoCoset width coarse (shifts pair.1)/rhoCoset width ambient 0)*
        gaussianAmplitude coarse width (shifts pair.1) pair.2 := by
  have hcoarse := rhoCoset_pos coarse width hwidth (shifts pair.1)
  have hambient := rhoCoset_zero_pos ambient width hwidth
  unfold gaussianAmplitude
  rw [add_zero,hcoordinates,Real.sqrt_div hcoarse.le]
  field_simp [(Real.sqrt_pos.mpr hcoarse).ne',(Real.sqrt_pos.mpr hambient).ne']

/-- Exact complete Hilbert-space coset factorization after the actual
reversible coordinate bijection. The conditional Gaussian is allowed to
depend on the retained residue; no junk independence is asserted. -/
theorem gaussianCoset_state_factorization
    (ambient coarse : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology ambient] [IsZLattice ℝ ambient] [DiscreteTopology coarse] [IsZLattice ℝ coarse]
    (shifts : Label → Space (dimension:=dimension)) (equivalence : ambient ≃ Label×coarse)
    (hcoordinates : ∀ pair : Label×coarse,
      ((equivalence.symm pair : ambient) : Space (dimension:=dimension))=(pair.2 : Space (dimension:=dimension))+shifts pair.1)
    (width : ℝ) (hwidth : 0 < width) :
    hilbertReindex equivalence (gaussianHilbertState ambient width hwidth 0)=
      hilbertFlatten (coherentFiberState (gaussianCosetJunk ambient coarse shifts equivalence hcoordinates width hwidth)
        (fun label => gaussianHilbertState coarse width hwidth (shifts label))
        (fun label => gaussianHilbertState_norm coarse width hwidth (shifts label))) := by
  ext pair
  change (gaussianAmplitude ambient width 0 (equivalence.symm pair) : ℂ)=
    (Real.sqrt (rhoCoset width coarse (shifts pair.1)/rhoCoset width ambient 0) : ℂ)*
      (gaussianAmplitude coarse width (shifts pair.1) pair.2 : ℂ)
  rw [←Complex.ofReal_mul]
  exact congrArg Complex.ofReal (gaussianCoset_amplitude_factor ambient coarse shifts equivalence hcoordinates width hwidth pair)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule201

/- Helper module Solutions.RegevBridgeGaussianShiftAffinity. -/
section P2MDyadicModule202

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- The actual midpoint norm identity on arbitrary Euclidean lattice
points, retaining both the full shift and its half. -/
theorem gaussian_midpoint_norm (point shift : Space (dimension:=dimension)) :
    ‖point‖^2+‖point+shift‖^2=2*‖point+(1/2 : ℝ) • shift‖^2+‖shift‖^2/2 := by
  rw [norm_add_sq_real,norm_add_sq_real,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,real_inner_smul_right]
  ring

/-- The literal product of the two positive normalized amplitudes is a
constant times the genuine midpoint-shift Gaussian, point by point. -/
theorem gaussianAmplitude_product (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) (point : lattice) :
    gaussianAmplitude lattice width 0 point*gaussianAmplitude lattice width shift point=
      (Real.exp (-Real.pi*‖shift‖^2/(4*width^2))*
        rho width ((point : Space (dimension:=dimension))+(1/2 : ℝ) • shift))/
        (Real.sqrt (rhoCoset width lattice 0)*Real.sqrt (rhoCoset width lattice shift)) := by
  by_cases hwidth : width=0
  · simp [hwidth,gaussianAmplitude,rho,mul_comm]
  unfold gaussianAmplitude rho
  rw [add_zero,div_mul_div_comm,←Real.exp_add,←Real.exp_add]
  congr 2
  have h := gaussian_midpoint_norm (point : Space (dimension:=dimension)) shift
  field_simp [hwidth]
  nlinarith

/-- The exact full infinite-lattice affinity of two genuine positive
Gaussian amplitude states. This is an amplitude identity, not a TV claim. -/
theorem gaussianAmplitude_affinity (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) :
    Summable (fun point : lattice => gaussianAmplitude lattice width 0 point*gaussianAmplitude lattice width shift point) ∧
      (∑' point : lattice,gaussianAmplitude lattice width 0 point*gaussianAmplitude lattice width shift point)=
      (Real.exp (-Real.pi*‖shift‖^2/(4*width^2))*rhoCoset width lattice ((1/2 : ℝ) • shift))/
        (Real.sqrt (rhoCoset width lattice 0)*Real.sqrt (rhoCoset width lattice shift)) := by
  simp_rw [gaussianAmplitude_product]
  refine ⟨((summable_gaussian_coset lattice width hwidth ((1/2 : ℝ) • shift)).mul_left _).div_const _,?_⟩
  rw [tsum_div_const,tsum_mul_left]
  rfl

/-- The exact full squared distance is twice one minus this affinity,
with all infinite summability obligations explicitly discharged. -/
theorem gaussianAmplitude_distance_sq (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) :
    Summable (fun point : lattice => (gaussianAmplitude lattice width 0 point-gaussianAmplitude lattice width shift point)^2) ∧
      (∑' point : lattice,(gaussianAmplitude lattice width 0 point-gaussianAmplitude lattice width shift point)^2)=
        2-2*(Real.exp (-Real.pi*‖shift‖^2/(4*width^2))*rhoCoset width lattice ((1/2 : ℝ) • shift))/
          (Real.sqrt (rhoCoset width lattice 0)*Real.sqrt (rhoCoset width lattice shift)) := by
  have hzero := gaussianAmplitude_square_sum lattice width hwidth 0
  have hshift := gaussianAmplitude_square_sum lattice width hwidth shift
  have haffinity := gaussianAmplitude_affinity lattice width hwidth shift
  have hformula (point : lattice) :
      (gaussianAmplitude lattice width 0 point-gaussianAmplitude lattice width shift point)^2=
      (gaussianAmplitude lattice width 0 point)^2+(gaussianAmplitude lattice width shift point)^2-
        2*(gaussianAmplitude lattice width 0 point*gaussianAmplitude lattice width shift point) := by ring
  simp_rw [hformula]
  refine ⟨(hzero.1.add hshift.1).sub (haffinity.1.mul_left 2),?_⟩
  rw [(hzero.1.add hshift.1).tsum_sub (haffinity.1.mul_left 2),hzero.1.tsum_add hshift.1,
    tsum_mul_left,hzero.2,hshift.2,haffinity.2]
  ring

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule202

/- Helper module Solutions.RegevBridgeGaussianShiftNumerics. -/
section P2MDyadicModule203

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

/-- True normalizer bounds convert a midpoint Gaussian mass into the
required positive-amplitude affinity bound. -/
theorem midpoint_affinity_lower (base first second midpoint error factor : ℝ)
    (hbase : 0 < base) (hfirst : 0 < first) (hsecond : 0 < second)
    (herror : 0 ≤ error) (herrorOne : error < 1) (hfactor : 0 ≤ factor)
    (hfirstUpper : first ≤ (1+error)*base) (hsecondUpper : second ≤ (1+error)*base)
    (hmidpointLower : (1-error)*base ≤ midpoint) :
    factor*(1-error)/(1+error) ≤ factor*midpoint/(Real.sqrt first*Real.sqrt second) := by
  have hdenominator : 0 < Real.sqrt first*Real.sqrt second := by positivity
  have hupperPositive : 0 < (1+error)*base := by positivity
  have hproduct : first*second ≤ ((1+error)*base)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfirstUpper) (sub_nonneg.mpr hsecondUpper)]
  have hdenominatorUpper : Real.sqrt first*Real.sqrt second ≤ (1+error)*base := by
    apply (sq_le_sq₀ hdenominator.le hupperPositive.le).mp
    rw [mul_pow,Real.sq_sqrt hfirst.le,Real.sq_sqrt hsecond.le]
    exact hproduct
  have hlowNonnegative : 0 ≤ factor*((1-error)*base) := by positivity
  have hfirstBound := div_le_div_of_nonneg_left hlowNonnegative hdenominator hdenominatorUpper
  have hsecondBound := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmidpointLower hfactor) hdenominator.le
  have hequal : factor*(1-error)/(1+error)=factor*((1-error)*base)/((1+error)*base) := by
    field_simp [hbase.ne',ne_of_gt (show 0 < 1+error by positivity)]
  rw [hequal]
  exact hfirstBound.trans hsecondBound

/-- The exact exponential and normalizer distortions give a direct
quadratic-shift plus smoothing error for the squared pure-state distance. -/
theorem affinity_error_numeric (error shiftError affinity : ℝ)
    (herror : 0 ≤ error) (hshift : 0 ≤ shiftError)
    (haffinity : Real.exp (-shiftError)*(1-error)/(1+error) ≤ affinity) :
    2-2*affinity ≤ 4*error+2*shiftError := by
  have hfactorUpper : Real.exp (-shiftError) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hfactorLower : 1-shiftError ≤ Real.exp (-shiftError) := by linarith [Real.add_one_le_exp (-shiftError)]
  have hratio : Real.exp (-shiftError)-2*error ≤ Real.exp (-shiftError)*(1-error)/(1+error) := by
    apply (le_div_iff₀ (by positivity : 0 < 1+error)).mpr
    nlinarith [mul_nonneg herror (show 0 ≤ 1+error-Real.exp (-shiftError) by linarith)]
  linarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule203

/- Helper module Solutions.RegevBridgeGaussianShiftStability. -/
section P2MDyadicModule204

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- Uniform shift stability of the complete actual positive Gaussian
amplitudes. The conclusion is the squared Hilbert distance itself; no
classical total-variation estimate is substituted for coherent control. -/
theorem gaussianAmplitude_shift_square_bound
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width error : ℝ) (hwidth : 0 < width) (herror : 0 < error) (herrorOne : error < 1)
    (hsmoothing : smoothingParam lattice error ≤ width) (shift : Space (dimension:=dimension)) :
    (∑' point : lattice,(gaussianAmplitude lattice width 0 point-gaussianAmplitude lattice width shift point)^2) ≤
      4*error+Real.pi*‖shift‖^2/(2*width^2) := by
  let base := width^dimension*(ZLattice.covolume lattice)⁻¹
  have hbase : 0 < base := mul_pos (pow_pos hwidth dimension)
    (inv_pos.mpr (ZLattice.covolume_pos lattice MeasureTheory.volume))
  have hzero := claim_3_8 lattice (0 : Space (dimension:=dimension)) herror hwidth hsmoothing
  have hshift := claim_3_8 lattice shift herror hwidth hsmoothing
  have hmid := claim_3_8 lattice ((1/2 : ℝ) • shift) herror hwidth hsmoothing
  have hzeroUpper : rhoCoset width lattice 0 ≤ (1+error)*base := by
    have h := (abs_le.mp hzero).2
    dsimp only [base]
    linarith
  have hshiftUpper : rhoCoset width lattice shift ≤ (1+error)*base := by
    have h := (abs_le.mp hshift).2
    dsimp only [base]
    linarith
  have hmidLower : (1-error)*base ≤ rhoCoset width lattice ((1/2 : ℝ) • shift) := by
    have h := (abs_le.mp hmid).1
    dsimp only [base]
    linarith
  let shiftError := Real.pi*‖shift‖^2/(4*width^2)
  have hshiftError : 0 ≤ shiftError := by dsimp only [shiftError];positivity
  have haffinity := midpoint_affinity_lower base (rhoCoset width lattice 0) (rhoCoset width lattice shift)
    (rhoCoset width lattice ((1/2 : ℝ) • shift)) error (Real.exp (-shiftError)) hbase
    (rhoCoset_pos lattice width hwidth 0) (rhoCoset_pos lattice width hwidth shift) herror.le herrorOne
    (Real.exp_pos _).le hzeroUpper hshiftUpper hmidLower
  have h := affinity_error_numeric error shiftError _ herror.le hshiftError haffinity
  rw [(gaussianAmplitude_distance_sq lattice width hwidth shift).2]
  have hequal : -Real.pi*‖shift‖^2/(4*width^2)= -shiftError := by dsimp only [shiftError];ring
  rw [hequal]
  have hright : 4*error+2*shiftError=4*error+Real.pi*‖shift‖^2/(2*width^2) := by
    dsimp only [shiftError]
    ring
  simpa only [mul_div_assoc] using h.trans_eq hright

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule204

/- Helper module Solutions.RegevBridgeGaussianHilbertShift. -/
section P2MDyadicModule205

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

theorem gaussianHilbertState_shift_sq
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width error : ℝ) (hwidth : 0 < width) (herror : 0 < error) (herrorOne : error < 1)
    (hsmoothing : smoothingParam lattice error ≤ width) (shift : Space (dimension:=dimension)) :
    ‖gaussianHilbertState lattice width hwidth 0-gaussianHilbertState lattice width hwidth shift‖^2 ≤
      4*error+Real.pi*‖shift‖^2/(2*width^2) := by
  rw [hilbert_norm_sq]
  have hpoint (point : lattice) :
      ‖(gaussianHilbertState lattice width hwidth 0-gaussianHilbertState lattice width hwidth shift) point‖^2=
        (gaussianAmplitude lattice width 0 point-gaussianAmplitude lattice width shift point)^2 := by
    rw [lp.coeFn_sub,Pi.sub_apply,gaussianHilbertState_apply,gaussianHilbertState_apply,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp only [hpoint]
  exact gaussianAmplitude_shift_square_bound lattice width error hwidth herror herrorOne hsmoothing shift

/-- Uniform full Hilbert-space shift stability of the actual Gaussian
unit vector, with its genuine lattice normalizers and complete tails. -/
theorem gaussianHilbertState_shift_norm
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width error : ℝ) (hwidth : 0 < width) (herror : 0 < error) (herrorOne : error < 1)
    (hsmoothing : smoothingParam lattice error ≤ width) (shift : Space (dimension:=dimension)) :
    ‖gaussianHilbertState lattice width hwidth 0-gaussianHilbertState lattice width hwidth shift‖ ≤
      Real.sqrt (4*error+Real.pi*‖shift‖^2/(2*width^2)) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  exact gaussianHilbertState_shift_sq lattice width error hwidth herror herrorOne hsmoothing shift

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule205

/- Helper module Solutions.RegevBridgeCoherentGaussianShifts. -/
section P2MDyadicModule206

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ} {Label : Type*}

/-- Retain every residue label with its complete coherent junk amplitude.
Uniform true shifted-Gaussian stability then produces a single pure
centered Gaussian tensor the same junk, with a full-state norm bound. -/
theorem coherentGaussianShifts_close
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width error radius : ℝ) (hwidth : 0 < width) (herror : 0 < error) (herrorOne : error < 1) (hradius : 0 ≤ radius)
    (hsmoothing : smoothingParam lattice error ≤ width)
    (junk : Hilbert Label) (hjunk : ‖junk‖=1) (shifts : Label → Space (dimension:=dimension))
    (hshifts : ∀ label,‖shifts label‖ ≤ radius) :
    ‖coherentFiberState junk (fun label => gaussianHilbertState lattice width hwidth (shifts label))
        (fun label => gaussianHilbertState_norm lattice width hwidth (shifts label))-
      coherentFiberState junk (fun _ => gaussianHilbertState lattice width hwidth 0)
        (fun _ => gaussianHilbertState_norm lattice width hwidth 0)‖ ≤
      Real.sqrt (4*error+Real.pi*radius^2/(2*width^2)) := by
  apply coherentFiberState_distance junk hjunk _
    (fun label => gaussianHilbertState_norm lattice width hwidth (shifts label))
    (gaussianHilbertState lattice width hwidth 0) (gaussianHilbertState_norm lattice width hwidth 0)
    _ (Real.sqrt_nonneg _)
  intro label
  rw [norm_sub_rev]
  apply (gaussianHilbertState_shift_norm lattice width error hwidth herror herrorOne hsmoothing (shifts label)).trans
  apply Real.sqrt_le_sqrt
  have hnorm := (sq_le_sq₀ (norm_nonneg (shifts label)) hradius).mpr (hshifts label)
  gcongr

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule206

/- Helper module Solutions.RegevBridgeGaussianCosetPure. -/
section P2MDyadicModule207

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ} {Label : Type*}

/-- The complete actual ambient Gaussian, after exact reversible quotient
encoding, is close to one centered coarse-lattice Gaussian tensor its
actual coherent residue junk. No residue measurement is required. -/
theorem gaussianCoset_centered_close
    (ambient coarse : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology ambient] [IsZLattice ℝ ambient] [DiscreteTopology coarse] [IsZLattice ℝ coarse]
    (shifts : Label → Space (dimension:=dimension)) (equivalence : ambient ≃ Label×coarse)
    (hcoordinates : ∀ pair : Label×coarse,
      ((equivalence.symm pair : ambient) : Space (dimension:=dimension))=(pair.2 : Space (dimension:=dimension))+shifts pair.1)
    (width error radius : ℝ) (hwidth : 0 < width) (herror : 0 < error) (herrorOne : error < 1) (hradius : 0 ≤ radius)
    (hsmoothing : smoothingParam coarse error ≤ width) (hshifts : ∀ label,‖shifts label‖ ≤ radius) :
    ∃ junk : Hilbert Label,‖junk‖=1 ∧
      ‖hilbertReindex equivalence (gaussianHilbertState ambient width hwidth 0)-
        hilbertFlatten (coherentFiberState junk (fun _ => gaussianHilbertState coarse width hwidth 0)
          (fun _ => gaussianHilbertState_norm coarse width hwidth 0))‖ ≤
        Real.sqrt (4*error+Real.pi*radius^2/(2*width^2)) := by
  let junk := gaussianCosetJunk ambient coarse shifts equivalence hcoordinates width hwidth
  have hjunk : ‖junk‖=1 := gaussianCosetJunk_norm ambient coarse shifts equivalence hcoordinates width hwidth
  refine ⟨junk,hjunk,?_⟩
  rw [gaussianCoset_state_factorization ambient coarse shifts equivalence hcoordinates width hwidth]
  have hclose := coherentGaussianShifts_close coarse width error radius hwidth herror herrorOne hradius hsmoothing junk hjunk shifts hshifts
  have hisometry := (hilbertFlattenIsometry (Label:=Label) (Index:=coarse)).isometry.dist_eq
    (coherentFiberState junk (fun label => gaussianHilbertState coarse width hwidth (shifts label))
      (fun label => gaussianHilbertState_norm coarse width hwidth (shifts label)))
    (coherentFiberState junk (fun _ => gaussianHilbertState coarse width hwidth 0)
      (fun _ => gaussianHilbertState_norm coarse width hwidth 0))
  simp only [dist_eq_norm] at hisometry
  exact hisometry.le.trans hclose

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule207

/- Helper module Solutions.RegevBridgeNativeGaussianCosetPure. -/
section P2MDyadicModule208

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv NativeDualQuotient

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

def nativeResidualShift (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (scale : ℝ) :
    Residual basis → Space (dimension:=dimension) := fun residue => residuePoint basis scale residue.val

theorem nativeResidualShift_bound (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (scale : ℝ) (hscale : 0 < scale) (residue : Residual basis) :
    ‖nativeResidualShift basis scale residue‖ ≤ dualColumnBudget basis hdet/scale := by
  have hremainder : remainderVector basis residue.val=residue.val := by
    rw [remainderVector,residue.property,Matrix.mulVec_zero,sub_zero]
  have h := remainder_norm_bound basis hdet scale hscale residue.val
  rw [hremainder] at h
  change ‖residuePoint basis scale residue.val‖ ≤ _
  exact h.trans (div_le_div_of_nonneg_right (by dsimp only [dualColumnBudget];linarith) hscale.le)

/-- The native quotient's actual ambient grid yields the actual scaled
dual lattice centered Gaussian and a retained unit residue state. All
coordinate semantics and shift bounds come from the verified programs. -/
theorem native_ambient_gaussian_pure
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (scale width error : ℝ) (hscale : 0 < scale) (hwidth : 0 < width) (herror : 0 < error) (herrorOne : error < 1)
    (hdimension : 0 < dimension)
    (hpublic : shortSmoothingFactor dimension error*dualColumnBudget basis hdet/scale ≤ width) :
    ∃ junk : Hilbert (Residual basis),‖junk‖=1 ∧
      ‖hilbertReindex (ambientCosetEquiv basis hdet scale hscale)
          (gaussianHilbertState (Ambient basis scale hscale) width hwidth 0)-
        hilbertFlatten (coherentFiberState junk
          (fun _ => gaussianHilbertState (Gamma basis hdet scale hscale) width hwidth 0)
          (fun _ => gaussianHilbertState_norm (Gamma basis hdet scale hscale) width hwidth 0))‖ ≤
        Real.sqrt (4*error+Real.pi*(dualColumnBudget basis hdet/scale)^2/(2*width^2)) := by
  have hsmoothing := (nativeGamma_smoothing_columnBudget basis hdet scale error hscale hdimension herror).trans hpublic
  exact gaussianCoset_centered_close (Ambient basis scale hscale) (Gamma basis hdet scale hscale)
    (nativeResidualShift basis scale) (ambientCosetEquiv basis hdet scale hscale)
    (fun pair => ambientCosetEquiv_symm_point basis hdet scale hscale pair.1 pair.2)
    width error (dualColumnBudget basis hdet/scale) hwidth herror herrorOne
    (div_nonneg (dualColumnBudget_pos basis hdet).le hscale.le) hsmoothing
    (nativeResidualShift_bound basis hdet scale hscale)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule208

/- Helper module ShortFourier. -/
section P2MDyadicModule209

set_option autoImplicit false

set_option maxHeartbeats 950000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection CoherentComputeUncompute GaussianProjection.CosetGeometry

open GaussianProjection GaussianLatticeTransport NativeDualQuotient

noncomputable section

variable {n M : ℕ} [NeZero M]

def putColor {I J : Type} [Fintype I] [Fintype J] [DecidableEq J] (emb : I ↪ J)
    (v : EuclideanSpace ℂ I) : EuclideanSpace ℂ J := WithLp.toLp 2 (basisEmbedding emb v.ofLp)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule209

/- Helper module GammaTruncate. -/
section P2MDyadicModule210

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedVariables false

set_option maxHeartbeats 1050000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection GaussianProjection

open NativeDualQuotient

noncomputable section

variable {n M : ℕ} [NeZero M]

theorem in_fine_range (L : Submodule ℤ (PointSpace n)) (R : ℝ) (p : fineLattice L M) :
    p ∈ Set.range (fineEmbedding L M R) ↔ ‖(p : PointSpace n)‖ < R := by
  constructor
  · rintro ⟨z,rfl⟩
    exact z.property
  · obtain ⟨z,rfl⟩ := (fineMap L M).surjective p
    intro h
    exact ⟨⟨z,h⟩,rfl⟩

theorem gamma_short {L : Submodule ℤ (PointSpace n)} [DiscreteTopology L] [IsZLattice ℝ L]
    (u R : ℝ) (hu : 0<u) (hR : 0<R) (hscale : (n:ℝ)*u^2 ≤ R^2) [Fintype (Retained L M R)] :
    let emb := fineEmbedding L M R
    let g := gaussianHilbertState (fineLattice L M) u hu 0
    (‖g-finiteEmbed emb (normalized (finiteRestrict emb g))‖ ≤ 2*Real.sqrt ((1/4:ℝ)^n)) ∧
    ‖finiteEmbed emb (normalized (finiteRestrict emb g))‖ = 1 := by
  classical
  let G := fineLattice L M
  let g := gaussianHilbertState G u hu 0
  let emb := fineEmbedding L M R
  have hmass : 0 < rhoCoset u G 0 := rhoCoset_zero_pos G u hu
  have hzero : (0 : G) ∈ Set.range emb := (in_fine_range L R 0).2 (by simpa using hR)
  have hpoint : g 0 ≠ 0 := by
    rw [show g 0 = (gaussianAmplitude G u 0 0 : ℂ) from rfl]
    exact Complex.ofReal_ne_zero.mpr (show gaussianAmplitude G u 0 0 ≠ 0 from (div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr hmass)).ne')
  have hproject (d : DecidablePred (fun index : G => index ∈ Set.range emb)) : @hilbertProject _ (fun index => index ∈ Set.range emb) d g ≠ 0 := by
    intro he
    have hh := congrArg (fun v : Hilbert G => v 0) he
    rw [hilbertProject_apply,if_pos hzero] at hh
    exact hpoint hh
  have ht (d : DecidablePred (fun index : G => index ∈ Set.range emb)) : (∑' p : G, @ite ℝ (p ∈ Set.range emb) (d p) 0 (‖g p‖^2)) ≤ (1/4 : ℝ)^n := by
    calc
      _ = gaussianTail G u R / rhoCoset u G 0 := by
        rw [gaussianTail,←tsum_div_const]
        apply tsum_congr
        intro p
        split
        · rename_i h
          simp only [if_neg (not_le.mpr ((in_fine_range L R p).1 h)),zero_div]
        · rename_i h
          rw [if_pos (le_of_not_gt (mt (in_fine_range L R p).2 h))]
          change ‖(gaussianAmplitude G u 0 p : ℂ)‖^2 = _
          rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,gaussianAmplitude_sq G u hu,add_zero]
      _ ≤ _ := (div_le_iff₀ hmass).mpr (gaussianTail_le_quarter_pow G u R hu hR.le hscale)
  refine ⟨finite_restriction_close emb g (gaussianHilbertState_norm G u hu 0) (hproject _) _ (ht _),?_⟩
  rw [finiteEmbed_normalized_restrict]
  exact normalized_norm _ (hproject _)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule210

/- Helper module NativeShortSource. -/
section P2MDyadicModule211

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection GaussianProjection NativeDualQuotient

noncomputable section

variable {n M : ℕ} [NeZero M]

private theorem modulus_pos (m : ℕ) [NeZero m] : 0 < (m:ℝ) := by exact_mod_cast NeZero.pos m

private abbrev nativeFineEquiv (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (M : ℕ) [NeZero M] :
    Ambient B M (modulus_pos M) ≃ Residual B × fineLattice (dual (IntegerBasis.inputLattice B hB)) M :=
  ambientCosetEquiv B hB M (modulus_pos M)

abbrev flatProduct {I J : Type} (j : Hilbert J) (v : Hilbert I) (hv : ‖v‖=1) : Hilbert (J×I) :=
  hilbertFlatten (coherentFiberState j (fun _ => v) (fun _ => hv))

theorem product_error {I J : Type} (j : Hilbert J) (hj : ‖j‖=1) (u v : Hilbert I) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖flatProduct j u hu-flatProduct j v hv‖ ≤ ‖u-v‖ := by
  have hiso := (hilbertFlattenIsometry (Label:=J) (Index:=I)).isometry.dist_eq
    (coherentFiberState j (fun _ => u) (fun _ => hu)) (coherentFiberState j (fun _ => v) (fun _ => hv))
  rw [dist_eq_norm,dist_eq_norm] at hiso
  exact hiso.le.trans (coherentFiberState_distance j hj (fun _ => u) (fun _ => hu) v hv _ (norm_nonneg _) (fun _ => le_rfl))

/-- The real reversible ambient quotient applied to the finite rectangle
state, interpreted on its output coordinates, is close to the normalized
short fine dual Gaussian times a unit residual. The omitted rectangular tail
or finite preparation error is counted before the quotient. -/
theorem rectangular_to_short (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (s R e δ : ℝ) (hs : 0<s) (hR : 0<R) (he : 0<e) (he' : e<1) (hn : 0<n)
    (hscale : (n:ℝ)*(s/Real.sqrt 2)^2 ≤ R^2)
    (hpublic : shortSmoothingFactor n e*dualColumnBudget B hB/(M:ℝ) ≤ s/Real.sqrt 2)
    [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) M R)]
    (prepared : Hilbert (Ambient B M (modulus_pos M)))
    (hprepared : ‖prepared-gaussianHilbertState (Ambient B M (modulus_pos M))
      (s/Real.sqrt 2) (by positivity) 0‖ ≤ δ) :
    let L := dual (IntegerBasis.inputLattice B hB)
    let g := gaussianHilbertState (fineLattice L M) (s/Real.sqrt 2) (by positivity) 0
    let trunc := finiteEmbed (fineEmbedding L M R) (normalized (finiteRestrict (fineEmbedding L M R) g))
    ∃ j : Hilbert (Residual B), ‖j‖=1 ∧ ∃ ht : ‖trunc‖=1,
      ‖hilbertReindex (nativeFineEquiv B hB M) prepared-flatProduct j trunc ht‖ ≤
        δ + Real.sqrt (4*e+Real.pi*(dualColumnBudget B hB/(M:ℝ))^2/(2*(s/Real.sqrt 2)^2)) + 2*Real.sqrt ((1/4:ℝ)^n) := by
  let L := dual (IntegerBasis.inputLattice B hB)
  let hM : 0 < (M : ℝ) := by exact_mod_cast NeZero.pos M
  let u := s/Real.sqrt 2
  have hu : 0<u := by dsimp only [u]; positivity
  let g := gaussianHilbertState (fineLattice L M) u hu 0
  let ambient := gaussianHilbertState (Ambient B M hM) u hu 0
  let equiv := nativeFineEquiv B hB M
  let trunc := finiteEmbed (fineEmbedding L M R) (normalized (finiteRestrict (fineEmbedding L M R) g))
  obtain ⟨junk,hjunk,hcenter⟩ := native_ambient_gaussian_pure B hB M u e hM hu he he' hn hpublic
  obtain ⟨hclose,ht⟩ := gamma_short (L:=L) (M:=M) u R hu hR hscale
  have hg : ‖g‖=1 := gaussianHilbertState_norm _ _ _ _
  change ‖hilbertReindex equiv ambient - flatProduct junk g hg‖ ≤ _ at hcenter
  refine ⟨junk,hjunk,ht,?_⟩
  have hprep := (hilbertReindexIsometry equiv).isometry.dist_eq prepared ambient
  rw [dist_eq_norm,dist_eq_norm] at hprep
  exact (norm_sub_le_norm_sub_add_norm_sub _ (hilbertReindex equiv ambient) _).trans
    ((add_le_add (hprep.le.trans hprepared) ((norm_sub_le_norm_sub_add_norm_sub _ (flatProduct junk g hg) _).trans
      (add_le_add hcenter ((product_error junk hjunk g trunc hg ht).trans hclose)))).trans (le_of_eq (add_assoc _ _ _).symm))

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule211

/- Helper module NativeTransfer. -/
section P2MDyadicModule212

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection GaussianProjection NativeDualQuotient

open CoherentComputeUncompute QAlgorithms QAlgorithms.Complexity ControlledNativeGates

noncomputable section

variable {n M : ℕ} [NeZero M]

/-- Relabeling a finite physical register embedded in the full mathematical
Hilbert space agrees exactly with applying that relabeling to its codewords. -/
theorem reindex_embed {I J K : Type} [Fintype I] (e : I ↪ J) (f : J ≃ K) (v : EuclideanSpace ℂ I) :
    hilbertReindex f (finiteEmbed e v) = finiteEmbed (e.trans f.toEmbedding) v := by
  ext k
  rw [hilbertReindex_apply]
  by_cases hk : k ∈ Set.range (e.trans f.toEmbedding)
  · obtain ⟨i,rfl⟩ := hk
    change finiteEmbed e v (f.symm (f (e i))) = _
    rw [f.symm_apply_apply,finiteEmbed_apply,finiteEmbed_apply]
  · rw [finiteEmbed_apply_not_mem (e.trans f.toEmbedding) v k hk]
    apply finiteEmbed_apply_not_mem
    rintro ⟨i,hi⟩
    exact hk ⟨i, (congrArg f hi).trans (f.apply_symm_apply k)⟩

theorem embed_restrict_of_support {I J : Type} [Fintype I] (e : I ↪ J) (v : Hilbert J)
    (hv : ∀ j, j ∉ Set.range e → v j = 0) : finiteEmbed e (finiteRestrict e v) = v := by
  ext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i,rfl⟩ := hj
    rw [finiteEmbed_apply]; rfl
  · rw [finiteEmbed_apply_not_mem _ _ _ hj,hv _ hj]

theorem physical_countable_distance {I J K : Type} [Fintype I] [Fintype K] [DecidableEq K]
    (c : I ↪ K) (e : I ↪ J) (v w : EuclideanSpace ℂ I) :
    ‖putColor c v-putColor c w‖ = ‖finiteEmbed e v-finiteEmbed e w‖ := by
  have hc := basisEmbedding_error c v.ofLp w.ofLp
  have he := (finiteEmbedIsometry e).isometry.dist_eq v w
  rw [dist_eq_norm,dist_eq_norm] at he
  exact hc.trans he.symm

/-- Full-space estimate for the actual, uniform, reversible quotient gates
on an arbitrary finite ambient box. The output comparison retains every
residue with its actual original-basis quotient and uses the same code for
both finite states. -/
theorem actual_quotient_transfer {I A J : Type} [Fintype I]
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (ticks : List Unit) (z : I ↪ (Fin n → ℤ))
    (hfit : ∀ i,(Codec.input (RationalInverse.Native.inputRows B) (List.ofFn (z i))).length ≤ ticks.length)
    (ambient : I ↪ A) (split : A ≃ J) (v : EuclideanSpace ℂ I) (goal : Hilbert J)
    (hcover : ∀ j, j ∉ Set.range (ambient.trans split.toEmbedding) → goal j = 0)
    (δ : ℝ) (hδ : ‖hilbertReindex split (finiteEmbed ambient v)-goal‖ ≤ δ) :
    let fw := Codec.forwardProgram
    let bw := Codec.inverseProgram
    let words := Codec.words B ticks z
    let hin := CoherentInjection.inputEncoding fw bw ticks.length words (Codec.words_length B ticks z)
      (Codec.words_injective B ticks z z.injective hfit)
    let hout := CoherentInjection.outputEncoding fw bw ticks.length words (Codec.words_length B ticks z)
      (Codec.words_injective B ticks z z.injective hfit) (Codec.words_inverse B hB ticks z hfit)
    let U := CoherentInjection.circuit fw bw ticks.length
    ∀ (actual : QState (CoherentInjection.totalWidth fw bw ticks.length)) (ε : ℝ),
      stateNorm (actual - basisEmbedding hin v.ofLp) ≤ ε →
      stateNorm (runLayered U actual - basisEmbedding hout (finiteRestrict (ambient.trans split.toEmbedding) goal).ofLp) ≤ ε+δ := by
  dsimp only
  intro actual ε hε
  let U := CoherentInjection.circuit Codec.forwardProgram Codec.inverseProgram ticks.length
  let hin := CoherentInjection.inputEncoding Codec.forwardProgram Codec.inverseProgram ticks.length
    (Codec.words B ticks z) (Codec.words_length B ticks z) (Codec.words_injective B ticks z z.injective hfit)
  let hout := CoherentInjection.outputEncoding Codec.forwardProgram Codec.inverseProgram ticks.length
    (Codec.words B ticks z) (Codec.words_length B ticks z) (Codec.words_injective B ticks z z.injective hfit)
    (Codec.words_inverse B hB ticks z hfit)
  have result : runLayered U (basisEmbedding hin v.ofLp) = basisEmbedding hout v.ofLp :=
    Codec.actual_coherent_quotient B hB ticks z z.injective hfit v.ofLp
  let outEmbedding := ambient.trans split.toEmbedding
  let w := finiteRestrict outEmbedding goal
  change stateNorm (runLayered U actual - basisEmbedding hout w.ofLp) ≤ ε + δ
  have ha : stateNorm (runLayered U actual - basisEmbedding hout v.ofLp) ≤ ε := by
    rw [←result,QuantumXorOracle.run_error]
    exact hε
  have hb : stateNorm (basisEmbedding hout v.ofLp - basisEmbedding hout w.ofLp) ≤ δ := by
    change ‖putColor hout v-putColor hout w‖ ≤ δ
    rw [physical_countable_distance hout outEmbedding v w]
    change ‖finiteEmbed outEmbedding v - finiteEmbed outEmbedding (finiteRestrict outEmbedding goal)‖ ≤ δ
    rw [embed_restrict_of_support outEmbedding goal hcover,←reindex_embed]
    exact hδ
  exact (norm_sub_le_norm_sub_add_norm_sub (WithLp.toLp 2 (runLayered U actual))
    (WithLp.toLp 2 (basisEmbedding hout v.ofLp)) (WithLp.toLp 2 (basisEmbedding hout w.ofLp))).trans (add_le_add ha hb)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule212

/- Helper module FiniteSupport. -/
section P2MDyadicModule213

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection GaussianProjection NativeDualQuotient

open RationalGramSchmidt

noncomputable section

variable {n M : ℕ} [NeZero M]

/-- Complete finite index set for the actual rectangle together with every
point of the retained Fourier product, including every original residue. -/
def sourceSupport {I P A J K : Type} [Fintype I] [Fintype P] [Fintype J] [DecidableEq A]
    (actual : I ↪ A) (split : A ≃ J × K) (retained : P ↪ K) : Finset A :=
  Finset.univ.image actual ∪ Finset.univ.image (fun t : J × P => split.symm (t.1,retained t.2))

theorem short_product_supported {I P A J K : Type} [Fintype I] [Fintype P] [Fintype J] [DecidableEq A]
    (actual : I ↪ A) (split : A ≃ J × K) (retained : P ↪ K) (j : Hilbert J) (v : EuclideanSpace ℂ P)
    (hv : ‖finiteEmbed retained v‖ = 1) (x : J × K)
    (hx : ¬ ∃ a ∈ sourceSupport actual split retained, split a = x) :
    flatProduct j (finiteEmbed retained v) hv x = 0 := by
  have hk : x.2 ∉ Set.range retained := by
    rintro ⟨p,hp⟩
    apply hx
    refine ⟨split.symm (x.1,retained p),Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x.1,p),Finset.mem_univ _,rfl⟩),?_⟩
    rw [split.apply_symm_apply,hp]
  change j x.1*finiteEmbed retained v x.2=0
  rw [finiteEmbed_apply_not_mem retained v x.2 hk,mul_zero]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule213

/- Helper module NativeSupport. -/
section P2MDyadicModule214

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection GaussianProjection NativeDualQuotient RationalGramSchmidt

noncomputable section

variable {n M : ℕ} [NeZero M]

abbrev integerSplit (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (M : ℕ) [NeZero M] :=
  (ambientIntegerEquiv B M (by exact_mod_cast NeZero.pos M)).trans (ambientCosetEquiv B hB M (by exact_mod_cast NeZero.pos M))

theorem inverse_point_fit (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (R : ℝ) (res : Residual B) (p : Retained (dual (IntegerBasis.inputLattice B hB)) M R) (i : Fin n) :
    |(integerSplit B hB M).symm (res,fineEmbedding _ M R p) i| ≤
      ⌈(originalDenominator B : ℝ)*((M:ℝ)*R+dualColumnBudget B hB)⌉ := by
  let D := (originalDenominator B : ℝ)
  have hD : 0<D := by dsimp [D]; exact_mod_cast denominator_pos (RationalInverse.Native.inputRows B)
  have hM : 0<(M:ℝ) := by exact_mod_cast NeZero.pos M
  let g := fineEmbedding _ M R p
  let z := (integerSplit B hB M).symm (res,g)
  let y := (ambientCosetEquiv B hB M hM).symm (res,g)
  have heq : (ambientIntegerEquiv B M hM) z = y := by exact Equiv.apply_symm_apply _ _
  have hgeom := ambientCosetEquiv_symm_point B hB M hM res g
  change (y : PointSpace n) = _ at hgeom
  rw [←heq,ambientIntegerEquiv_apply, residuePoint_eq] at hgeom
  have hr := nativeResidualShift_bound B hB M hM res
  change ‖residuePoint B M res.val‖ ≤ _ at hr
  have hg : ‖(g : PointSpace n)‖ < R := p.property
  have hratio : ((M:ℝ)*D)⁻¹*‖intVecE z‖ ≤ R+dualColumnBudget B hB/(M:ℝ) := by
    rw [←abs_of_pos (inv_pos.mpr (mul_pos hM hD)),←Real.norm_eq_abs,←norm_smul]
    change ‖((M:ℝ)*(originalDenominator B:ℝ))⁻¹ • intVecE z‖ ≤ _
    rw [hgeom]
    exact (norm_add_le _ _).trans (add_le_add hg.le hr)
  have hz : ‖intVecE z‖ ≤ D * ((M:ℝ)*R+dualColumnBudget B hB) := by
    calc
      _ = ((M:ℝ)*D) * (((M:ℝ)*D)⁻¹*‖intVecE z‖) := by field_simp
      _ ≤ ((M:ℝ)*D) * (R+dualColumnBudget B hB/(M:ℝ)) := mul_le_mul_of_nonneg_left hratio (mul_pos hM hD).le
      _ = _ := by field_simp
  have hi := PiLp.norm_apply_le (p:=2) (intVecE z) i
  change ‖(z i:ℝ)‖ ≤ _ at hi
  rw [Real.norm_eq_abs] at hi
  have hh := (hi.trans hz).trans (Int.le_ceil _)
  exact_mod_cast hh

theorem support_fit {I : Type} [Fintype I] (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (R : ℝ) [Fintype (Residual B)] [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) M R)]
    (src : I ↪ (Fin n → ℤ)) (C : ℤ) (hc : ∀ x i, |src x i| ≤ C) (z : Fin n → ℤ)
    (hz : z ∈ sourceSupport src (integerSplit B hB M) (fineEmbedding _ M R)) (i : Fin n) :
    |z i| ≤ max C ⌈(originalDenominator B : ℝ)*((M:ℝ)*R+dualColumnBudget B hB)⌉ := by
  rcases Finset.mem_union.mp hz with h|h
  · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp h
    exact (hc x i).trans (le_max_left _ _)
  · obtain ⟨⟨res,p⟩,_,rfl⟩ := Finset.mem_image.mp h
    exact (inverse_point_fit B hB R res p i).trans (le_max_right _ _)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule214

/- Helper module SupportEmbedding. -/
section P2MDyadicModule215

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open GaussianPoissonSeries CoherentComputeUncompute

noncomputable section

theorem basis_comp {I J K : Type} [Fintype I] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (e : I ↪ J) (f : J ↪ K) (v : I → ℂ) :
    basisEmbedding f (basisEmbedding e v) = basisEmbedding (e.trans f) v := by
  funext k
  by_cases hk : k ∈ Set.range f
  · obtain ⟨j,rfl⟩ := hk
    rw [basisEmbedding_at]
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hj
      exact (basisEmbedding_at e v i).trans (basisEmbedding_at (e.trans f) v i).symm
    · rw [basisEmbedding_outside e v j hj,basisEmbedding_outside (e.trans f) v]
      rintro ⟨i,hi⟩
      exact hj ⟨i,f.injective hi⟩
  · rw [basisEmbedding_outside f _ k hk,basisEmbedding_outside (e.trans f) v]
    rintro ⟨i,rfl⟩
    exact hk ⟨e i,rfl⟩

theorem finite_comp {I J K : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (e : I ↪ J) (f : J ↪ K) (v : EuclideanSpace ℂ I) :
    finiteEmbed f (putColor e v) = finiteEmbed (e.trans f) v := by
  ext k
  by_cases hk : k ∈ Set.range f
  · obtain ⟨j,rfl⟩ := hk
    rw [finiteEmbed_apply]
    change basisEmbedding e v.ofLp j = _
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hj
      exact (basisEmbedding_at e v.ofLp i).trans (finiteEmbed_apply (e.trans f) v i).symm
    · rw [basisEmbedding_outside e v.ofLp j hj,finiteEmbed_apply_not_mem]
      rintro ⟨i,hi⟩
      exact hj ⟨i,f.injective hi⟩
  · rw [finiteEmbed_apply_not_mem f _ k hk,finiteEmbed_apply_not_mem]
    rintro ⟨i,rfl⟩
    exact hk ⟨e i,rfl⟩

variable {I P A J K : Type} [Fintype I] [Fintype P] [Fintype J] [DecidableEq A]
  (src : I ↪ A) (split : A ≃ J × K) (keep : P ↪ K)

def sourceInjection : I ↪ ↥(sourceSupport src split keep) where
  toFun i := ⟨src i,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
  inj' _ _ h := src.injective (congrArg Subtype.val h)

def targetInjection : J × P ↪ ↥(sourceSupport src split keep) where
  toFun t := ⟨split.symm (t.1,keep t.2),Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)⟩
  inj' _ _ h := by
    have hh := split.symm.injective (congrArg Subtype.val h)
    exact Prod.ext (congrArg (fun x : J × K => x.1) hh) (keep.injective (congrArg (fun x : J × K => x.2) hh))

def supportVals : ↥(sourceSupport src split keep) ↪ A := Function.Embedding.subtype _

theorem support_factor (j : Hilbert J) (v : EuclideanSpace ℂ P) (hv : ‖finiteEmbed keep v‖=1) :
    (finiteRestrict ((supportVals src split keep).trans split.toEmbedding) (flatProduct j (finiteEmbed keep v) hv)).ofLp =
    basisEmbedding (targetInjection src split keep) (fun t => j t.1 * v t.2) := by
  funext a
  by_cases ha : a ∈ Set.range (targetInjection src split keep)
  · obtain ⟨⟨r,p⟩,rfl⟩ := ha
    rw [basisEmbedding_at]
    change j (split (split.symm (r,keep p))).1 * finiteEmbed keep v (split (split.symm (r,keep p))).2=_
    rw [split.apply_symm_apply,finiteEmbed_apply]
  · rw [basisEmbedding_outside _ _ a ha]
    change j (split a.val).1 * finiteEmbed keep v (split a.val).2 = 0
    rw [finiteEmbed_apply_not_mem,mul_zero]
    rintro ⟨p,hp⟩
    apply ha
    refine ⟨((split a.val).1,p),Subtype.ext ?_⟩
    change split.symm (_,keep p) = _
    rw [hp,Prod.mk.eta,split.symm_apply_apply]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule215

/- Helper module Solutions.RegevBridgeNativeFixedResidue. -/
section P2MDyadicModule216

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeFixedResidue

open QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeBodyKernel

/-- A binary power of two is constructed in a number of steps controlled
by the public unary bit capacity, never by the value of the modulus. -/
def modulus (ticks : List Unit) : ℕ := bitValue (ticks.map (fun _ => false)++[true])

@[fun_prop] theorem modulus_poly : Poly modulus := by unfold modulus;fun_prop

theorem modulus_eq (ticks : List Unit) : modulus ticks=2^ticks.length := by
  induction ticks with
  | nil => simp [modulus,bitValue]
  | cons u ticks ih =>
    simp only [modulus,List.map_cons,List.cons_append,bitValue,Bool.toNat_false,zero_add] at *
    rw [ih,List.length_cons,pow_succ,Nat.mul_comm]

theorem modulus_pos (ticks : List Unit) : 0 <  modulus ticks := by rw [modulus_eq];positivity

def current (x : List Unit×ℤ) : Str := NativeFixedBits.current (x.1,emodNatural (x.2,modulus x.1))

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

end InfoLossLAR.WorstCase.NativeFixedResidue

end P2MDyadicModule216

/- Helper module IntegerDivision. -/
section P2MDyadicModule217

set_option autoImplicit false

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace InfoLossLAR.WorstCase.NativeLLL

@[fun_prop] theorem intNatAbs_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩

@[fun_prop] theorem natQuotient_poly : Poly (fun t : ℕ × ℕ => t.1 / t.2) :=
  ⟨PolyProgram.natDiv⟩

/-- Floor division by a natural denominator, using binary natural division
and sign-magnitude conversion. The zero-divisor convention matches Int.ediv. -/
def intDivNat (t : ℤ × ℕ) : ℤ :=
  if t.2 = 0 then 0
  else if t.1 < 0 then -(((t.1.natAbs - 1) / t.2 : ℕ) : ℤ) - 1
  else ((t.1.natAbs / t.2 : ℕ) : ℤ)

@[fun_prop] theorem intDivNat_poly : Poly intDivNat := by
  unfold intDivNat
  fun_prop

theorem intDivNat_eq (a : ℤ) (b : ℕ) : intDivNat (a, b) = a / (b : ℤ) := by
  by_cases hb : b = 0
  · subst b
    simp [intDivNat]
  cases a with
  | ofNat a =>
      simp [intDivNat, hb, Int.natCast_ediv]
  | negSucc a =>
      have hpos : 0 < (b : ℤ) := by omega
      simp [intDivNat, hb, Int.negSucc_ediv a hpos, Int.natCast_ediv]
      change -((a : ℤ) / b) - 1 = -1 + -((a : ℤ) / b)
      ring

end InfoLossLAR.WorstCase.NativeLLL

end P2MDyadicModule217

/- Helper module ResidueBlocks. -/
section P2MDyadicModule218

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Consecutive little-endian words, one per row of the original basis. -/
def blocks (t : List Unit × List ℤ) : Str :=
  t.2.flatMap fun z => NativeFixedResidue.current (t.1,z)

@[fun_prop] theorem blocks_poly : Poly blocks := by unfold blocks; fun_prop

def chunk (input : (List Unit × Str) × ℕ) : ℕ :=
  bitValue ((input.1.2.drop (input.2*input.1.1.length)).take input.1.1.length)

@[fun_prop] theorem chunk_poly : Poly chunk := by
  have hd := Poly.comp parser_drop_poly (show Poly (fun x : (List Unit × Str) × ℕ =>
    (x.1.2,x.2*x.1.1.length)) by fun_prop)
  have hb : Poly (fun x : (List Unit × Str) × ℕ => x.1.1.length) := by fun_prop
  have hv := Poly.comp bitValue_poly (Poly.comp parser_take_poly (Poly.pair hd hb))
  exact hv

def answers (input : List Unit × List ℤ) : List ℤ :=
  input.2.map fun z => -NativeLLL.intDivNat (z,NativeFixedResidue.modulus input.1)

@[fun_prop] theorem answers_poly : Poly answers := by unfold answers; fun_prop

def restore (t : (List Unit × Str) × List ℤ) : List ℤ :=
  (List.range t.2.length).map fun i =>
    (chunk (t.1,i) : ℤ) - (NativeFixedResidue.modulus t.1.1 : ℤ) * (t.2[i]?.getD 0)

@[fun_prop] theorem restore_poly : Poly restore := by
  have hi : Poly (fun t : (List Unit × Str) × List ℤ => List.range t.2.length) :=
    Poly.comp (f:=fun t : List ℤ => List.range t.length) Poly.list_indices Poly.snd
  unfold restore
  exact Poly.list_map (by fun_prop) hi

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule218

/- Helper module QueryWord. -/
section P2MDyadicModule219

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2PlatformSerialization

open Integration9_9.LARPlatformEncoding (serializeBinaryWords_map)

open Integration9_9.LARPlatformEncoding (serializeBinaryWords)

open GaussianRandomizedRounding.Wide.Coherent (rationalCode)

open scoped BigOperators

def points (u : (List (List ℤ) × List Unit) × List ℤ) : List ℚ :=
  let M := NativeFixedResidue.modulus u.1.2
  let p := u.2.map fun z => (Integration9_9.TM2NativeBodyKernel.emodNatural (z,M) : ℚ)
  (RationalInverse.Native.current u.1.1).map fun row =>
    (M : ℚ)⁻¹ * RationalGramSchmidt.Native.dot (row,p)

@[fun_prop] theorem points_poly : Poly points := by
  unfold points
  fun_prop

def res (M : ℕ) (a : ℤ) : ℤ := a % (M : ℤ)

noncomputable def queryPoint {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (M : ℕ) (z : Fin n → ℤ) : Fin n → ℚ :=
  (M : ℚ)⁻¹ • ((Int.castRingHom ℚ).mapMatrix B).transpose⁻¹.mulVec (fun i => (res M (z i) : ℚ))

theorem points_value {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (b : List Unit) (z : Fin n → ℤ) :
    points ((RationalInverse.Native.inputRows B,b),List.ofFn z)
      = List.ofFn (queryPoint B (NativeFixedResidue.modulus b) z) := by
  let M := NativeFixedResidue.modulus b
  have hp : (0:ℤ)<M := by exact_mod_cast NativeFixedResidue.modulus_pos b
  have he (a : ℤ) : (Integration9_9.TM2NativeBodyKernel.emodNatural (a,M) : ℚ) = (res M a : ℚ) := by
    rw [Integration9_9.TM2NativeBodyKernel.emodNatural_eq,← Int.cast_natCast (R:=ℚ),Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne')]
    rfl
  have hd := RationalInverse.Native.current_inverse_transpose B hB
  rw [RationalInverse.Native.current_correct_dual B hB] at hd
  have hmat : (Int.castRingHom ℚ).mapMatrix B = (fun row col => (B row col : ℚ)) := by ext; rfl
  have hij (i j : Fin n) : RationalInverse.dualVector B j i =
      (((Int.castRingHom ℚ).mapMatrix B).transpose⁻¹) i j := by
    rw [hmat]
    have hij := congrFun (congrFun hd i) j
    simpa only [RationalInverse.Native.decodeMatrix,List.getElem?_ofFn,i.isLt,j.isLt,↓reduceDIte,Option.getD_some] using hij
  unfold points
  rw [RationalInverse.Native.current_correct_dual B hB]
  change _ = List.ofFn (queryPoint B M z)
  simp only [← List.ofFn_comp']
  congr 1
  funext i
  change (M:ℚ)⁻¹ * RationalGramSchmidt.Native.dot
      (List.ofFn (fun j => RationalInverse.dualVector B j i),List.ofFn (fun j => (Integration9_9.TM2NativeBodyKernel.emodNatural (z j,M) : ℚ))) = _
  simp_rw [he]
  rw [RationalGramSchmidt.Native.dot_ofFn]
  simp only [queryPoint,Pi.smul_apply,smul_eq_mul,RationalGramSchmidt.innerQ,Matrix.mulVec,dotProduct,hij]

def serializePoints (q : List ℚ) : Str := serializeBinaryWords (q.map rationalCode)

@[fun_prop] theorem serializePoints_poly : Poly serializePoints := by unfold serializePoints; fun_prop

def body (x : ((Str × Str) × (Str × Str)) × List ℚ) : Str :=
  encPair x.1.1.1 (encPair x.1.1.2 (encPair x.1.2.1 (encPair x.1.2.2 (serializePoints x.2))))

@[fun_prop] theorem body_poly : Poly body := by unfold body; fun_prop

theorem serializePoints_ofFn {n : ℕ} (q : Fin n → ℚ) :
    serializePoints (List.ofFn q)=encVec encQ q := by
  change serializeBinaryWords ((List.ofFn q).map encQ) = _
  exact serializeBinaryWords_map _ _

theorem serializeMatrix_eq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    serializeMatrix (RationalInverse.Native.inputRows B)=encMat encI B := by
  have hv (v : Fin n → ℤ) : serializeVector (List.ofFn v)=encVec encI v := by
    simp only [serializeVector,serializeBinaryWords_map,encVec]
  simp only [serializeMatrix,RationalInverse.Native.inputRows,List.map_ofFn,Function.comp_def,hv]
  simpa only [List.map_ofFn,Function.comp_def,encMat] using serializeBinaryWords_map (encVec encI) (List.ofFn B)

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule219

/- Helper module Layout. -/
section P2MDyadicModule220

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 12000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2NativeAffineEmitter

open Integration9_9.LARPlatformEncoding (readS readS_poly readS_append)

@[fun_prop] theorem header_poly : Poly header := by unfold header; fun_prop

def skipU (w : Str) : Str := (readUnary w).2

@[fun_prop] theorem skipU_poly : Poly skipU := by
  have h := Poly.comp (f:=Prod.snd) (g:=readUnary) Poly.snd readUnary_poly
  exact h

def skipS (w : Str) : Str := (readS w).1

@[fun_prop] theorem skipS_poly : Poly skipS := by
  have h := Poly.comp (f:=Prod.fst) (g:=readS) Poly.fst readS_poly
  exact h

def firstS (w : Str) : Str := (readS w).2

@[fun_prop] theorem firstS_poly : Poly firstS := by
  have h := Poly.comp (f:=Prod.snd) (g:=readS) Poly.snd readS_poly
  exact h

def vec (w : Str) : List ℤ := (readVector w).2

@[fun_prop] theorem vec_poly : Poly vec := by
  have h := Poly.comp (f:=Prod.snd) (g:=readVector) Poly.snd readVector_poly
  exact h

def setup (w : Str) : Config :=
  let k := skipU w
  let l := skipU k
  let r := skipU l
  let p := skipS r
  ((unarySlots w,unarySlots k,unarySlots l),(firstS r,firstS p,firstS (skipS p)))

@[fun_prop] theorem setup_poly : Poly setup := by unfold setup; dsimp only; fun_prop

theorem units_exact (s : List Unit) : List.replicate s.length ()=s := by
  symm
  exact List.eq_replicate_iff.mpr ⟨rfl,fun _ _ => Subsingleton.elim _ _⟩

theorem setup_header (p : Config) : setup (header p)=p := by
  rcases p with ⟨⟨b,k,l⟩,R,prec,rows⟩
  simp only [setup,skipU,skipS,firstS,header,List.append_assoc,lengthToken_eq,unarySlots_append,readUnary_append,units_exact,
    readS_append,show (readS (encS rows)).2=rows by simpa using congrArg Prod.snd (readS_append rows [])]

@[fun_prop] theorem pack_poly : Poly pack := by unfold pack; fun_prop

def unpack (w : Str) : Source :=
  let B := skipU (skipS w)
  let z := skipS B
  let r := skipS z
  (((firstS w,unarySlots (skipS w)),(firstS B,firstS r)),vec (firstS z))

@[fun_prop] theorem unpack_poly : Poly unpack := by unfold unpack; dsimp only; fun_prop

theorem vector_read (s : List ℤ) : (readVector (serializeVector s)).2=s := by
  simpa using congrArg Prod.snd (NativePaddedWords.readVector_serialized s [])

theorem unpack_pack (s : Source) (tail : Str) : unpack (pack s ++ tail)=s := by
  rcases s with ⟨⟨⟨h,t⟩,B,r⟩,z⟩
  simp only [unpack,skipU,skipS,firstS,vec,pack,List.append_assoc,lengthToken_eq,readS_append,readUnary_append,unarySlots_append,units_exact,vector_read]

def request (v : (Config × Str) × List ℤ) : Str :=
  let c := v.1.1
  let mat := v.1.2
  encS (body (((mat,c.2.1),c.2.2),points (((readMatrix mat).2,c.1.1),v.2)))

@[fun_prop] theorem request_poly : Poly request := by unfold request; fun_prop

/-- Fixed register boundaries depend on widths and dimension only. The last word carries
the preserved residual and may vary in length. -/
def outHead (x : List Unit × Source) : Str :=
  lengthToken x.1 ++ encS x.2.1.1.1 ++ lengthToken x.2.1.1.2 ++ encS x.2.1.2.1 ++ lengthToken x.2.2

@[fun_prop] theorem outHead_poly : Poly outHead := by unfold outHead; fun_prop

def emit (x : List Unit × Source) : Str :=
  let s := x.2
  let c := setup s.1.1.1
  outHead x ++ blocks (c.1.1,s.2) ++
    NativePaddedWords.current (c.1.2.1,serializeVector (answers (c.1.1,s.2))) ++
    NativePaddedWords.current (c.1.2.2,request ((c,s.1.2.1),s.2)) ++ encS s.1.2.2

@[fun_prop] theorem emit_poly : Poly emit := by unfold emit; fun_prop

def ticks (w : Str) : List Unit := w.map fun _ => ()

@[fun_prop] theorem ticks_poly : Poly ticks := by unfold ticks;fun_prop

def forward (w : Str) : Str := emit (ticks w,unpack w)

@[fun_prop] theorem forward_poly : Poly forward := by unfold forward; fun_prop

def cut (x : ℕ × Str) : Str × Str := (x.2.take x.1,x.2.drop x.1)

@[fun_prop] theorem cut_poly : Poly cut :=
  Poly.pair (Poly.comp parser_take_poly (Poly.pair Poly.snd Poly.fst))
    (Poly.comp parser_drop_poly (Poly.pair Poly.snd Poly.fst))

def takeWord (x : ℕ × Str) : Str := (cut x).1

@[fun_prop] theorem takeWord_poly : Poly takeWord := by
  have h := Poly.comp (f:=Prod.fst) (g:=cut) Poly.fst cut_poly
  exact h

def dropWord (x : ℕ × Str) : Str := (cut x).2

@[fun_prop] theorem dropWord_poly : Poly dropWord := by
  have h := Poly.comp (f:=Prod.snd) (g:=cut) Poly.snd cut_poly
  exact h

def inverse (out : Str) : Str :=
  let h := skipU out
  let B := skipU (skipS h)
  let dim := skipS B
  let n := (unarySlots dim).length
  let c := setup (firstS h)
  let p := (n*c.1.1.length,skipU dim)
  let a := (c.1.2.1.length,dropWord p)
  let r := firstS (dropWord (c.1.2.2.length,dropWord a))
  let z := restore ((c.1.1,takeWord p),vec (takeWord a))
  NativePaddedWords.current (unarySlots out,pack (((firstS h,unarySlots (skipS h)),(firstS B,r)),z))

@[fun_prop] theorem inverse_poly : Poly inverse := by unfold inverse; dsimp only; fun_prop

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule220

/- Helper module Realize. -/
section P2MDyadicModule221

set_option autoImplicit false

set_option maxHeartbeats 2200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2NativeAffineEmitter

open CoherentComputeUncompute

noncomputable def forwardProgram : PolyProgram id id forward :=
  Integration9_9.LARCoinLayout.rawPolyProgram forward_poly

noncomputable def inverseProgram : PolyProgram id id inverse :=
  Integration9_9.LARCoinLayout.rawPolyProgram inverse_poly

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule221

/- Helper module RectangularQuotient. -/
section P2MDyadicModule222

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection GaussianProjection NativeDualQuotient

open CoherentComputeUncompute QAlgorithms QAlgorithms.Complexity ControlledNativeGates

noncomputable section

variable {n M : ℕ} [NeZero M]

abbrev nativeIn {I : Type} [Fintype I] (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit) (z : I ↪ (Fin n → ℤ))
    (hf : ∀ i,(Codec.input (RationalInverse.Native.inputRows B) (List.ofFn (z i))).length ≤ ticks.length) :=
  CoherentInjection.inputEncoding Codec.forwardProgram Codec.inverseProgram ticks.length (Codec.words B ticks z)
    (Codec.words_length B ticks z) (Codec.words_injective B ticks z z.injective hf)

abbrev nativeOut {I : Type} [Fintype I] (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (ticks : List Unit) (z : I ↪ (Fin n → ℤ))
    (hf : ∀ i,(Codec.input (RationalInverse.Native.inputRows B) (List.ofFn (z i))).length ≤ ticks.length) :=
  CoherentInjection.outputEncoding Codec.forwardProgram Codec.inverseProgram ticks.length (Codec.words B ticks z)
    (Codec.words_length B ticks z) (Codec.words_injective B ticks z z.injective hf) (Codec.words_inverse B hB ticks z hf)

/-- The genuine native quotient circuit transports finite rectangular source
amplitudes to an explicitly encoded product on every original residue and
every retained short point. Physical encoding widths must cover the verified
integer coordinate bound of `support_fit`. -/
theorem rectangular_quotient {I : Type} [Fintype I]
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (hM : 0<(M:ℝ))
    (s R e δ : ℝ) (hs : 0<s) (hR : 0<R) (he : 0<e) (he' : e<1) (hn : 0<n)
    (hscale : (n:ℝ)*(s/Real.sqrt 2)^2 ≤ R^2)
    (hpublic : shortSmoothingFactor n e*dualColumnBudget B hB/(M:ℝ) ≤ s/Real.sqrt 2)
    [Fintype (Residual B)] [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) M R)]
    (src : I ↪ (Fin n → ℤ)) (v : EuclideanSpace ℂ I)
    (hprepared : ‖finiteEmbed (src.trans (ambientIntegerEquiv B M hM).toEmbedding) v
      -gaussianHilbertState (Ambient B M hM) (s/Real.sqrt 2) (by positivity) 0‖ ≤ δ)
    (ticks : List Unit) :
    let split := integerSplit B hB M
    let L := dual (IntegerBasis.inputLattice B hB)
    let keep := fineEmbedding L M R
    let z := supportVals src split keep
    let target := normalized (finiteRestrict keep (gaussianHilbertState (fineLattice L M) (s/Real.sqrt 2) (by positivity) 0))
    ∀ hf : ∀ i,(Codec.input (RationalInverse.Native.inputRows B) (List.ofFn (z i))).length ≤ ticks.length,
    ∃ j : Hilbert (Residual B), ‖j‖ = 1 ∧
    ∀ (actual : QState (CoherentInjection.totalWidth Codec.forwardProgram Codec.inverseProgram ticks.length)) (ε : ℝ),
      stateNorm (actual - basisEmbedding ((sourceInjection src split keep).trans (nativeIn B ticks z hf)) v.ofLp) ≤ ε →
      stateNorm (runLayered (CoherentInjection.circuit Codec.forwardProgram Codec.inverseProgram ticks.length) actual -
        basisEmbedding ((targetInjection src split keep).trans (nativeOut B hB ticks z hf)) (fun p => j p.1*target p.2)) ≤
        ε + (δ + Real.sqrt (4*e+Real.pi*(dualColumnBudget B hB/(M:ℝ))^2/(2*(s/Real.sqrt 2)^2)) + 2*Real.sqrt ((1/4:ℝ)^n)) := by
  let split := integerSplit B hB M
  let L := dual (IntegerBasis.inputLattice B hB)
  let keep := fineEmbedding L M R
  let z := supportVals src split keep
  let target := normalized (finiteRestrict keep (gaussianHilbertState (fineLattice L M) (s/Real.sqrt 2) (by positivity) 0))
  let v' := putColor (sourceInjection src split keep) v
  dsimp only
  intro hf
  obtain ⟨j,hj,ht,hd⟩ := rectangular_to_short B hB s R e δ hs hR he he' hn hscale hpublic _ hprepared
  let goal := flatProduct j (finiteEmbed keep target) ht
  have ha : hilbertReindex split (finiteEmbed z v') =
      hilbertReindex (ambientCosetEquiv B hB M hM) (finiteEmbed (src.trans (ambientIntegerEquiv B M hM).toEmbedding) v) := by
    rw [show finiteEmbed z v' = finiteEmbed ((sourceInjection src split keep).trans z) v from finite_comp _ _ _,reindex_embed,reindex_embed]
    rfl
  have cover (x) (hx : x ∉ Set.range (z.trans split.toEmbedding)) : goal x=0 := by
    apply short_product_supported src split keep j target ht x
    rintro ⟨a,h,heq⟩
    exact hx ⟨⟨a,h⟩,heq⟩
  refine ⟨j,hj,?_⟩
  intro actual ε hε
  have hinit : stateNorm (actual - basisEmbedding (nativeIn B ticks z hf) v'.ofLp) ≤ ε := by
    change stateNorm (actual - basisEmbedding _ (basisEmbedding _ v.ofLp)) ≤ _
    rw [basis_comp]
    exact hε
  have h := actual_quotient_transfer B hB ticks z hf z split v' goal cover _ (ha ▸ hd) actual ε hinit
  dsimp only at h
  rw [support_factor src split keep j target ht,basis_comp] at h
  exact h

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule222

/- Helper module ShortQuery. -/
section P2MDyadicModule223

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries GaussianProjection NativeDualQuotient IntegerBasis

noncomputable section

variable {n M : ℕ} [NeZero M]

theorem quotient_coordinate (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℝ)
    (p : Retained (dual (inputLattice B hB)) M R) (res : Residual B) :
    let z := (integerSplit B hB M).symm (res,fineEmbedding _ M R p)
    remainderVector B z = res.val ∧ quotientVector B z = shortCoordinate B hB R p := by
  let g := fineEmbedding _ M R p
  let z := (integerSplit B hB M).symm (res,g)
  have hh := (integerSplit B hB M).apply_symm_apply (res,g)
  change integerSplit B hB M z = _ at hh
  have hd : integerSplit B hB M z = ((integerPointsEquiv B hB z).1,
      gammaIntegerEquiv B hB M (by exact_mod_cast NeZero.pos M) ((integerPointsEquiv B hB z).2)) := by
    dsimp [integerSplit,ambientCosetEquiv]
    simp [Prod.map]
  rw [hd] at hh
  constructor
  · exact congrArg (fun t : Residual B × fineLattice (dual (inputLattice B hB)) M => t.1.val) hh
  · have hq := congrArg (fun t : Residual B × fineLattice (dual (inputLattice B hB)) M => t.2) hh
    change fineMap _ M ((dualIntegerEquiv B hB) (quotientVector B z)) = fineMap _ M p.val at hq
    exact (dualIntegerEquiv B hB).injective ((fineMap _ M).injective hq |>.trans ((dualIntegerEquiv B hB).apply_symm_apply p.val).symm)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule223

/- Helper module CodecMatch. -/
section P2MDyadicModule224

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1550000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity NativeQFTPlanCompile GridReadout.Axis FineCodec

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open QMCNumericRuntime OAI.MetricKMedian.Binary

open RegevLWE.GaussConv GaussianPoissonSeries IntegerBasis

noncomputable section

variable {n m : ℕ}

theorem physical_request (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt k l : List Unit)
    (R : ℚ) (prec : ℕ) (pool : Fin m → Fin n → ℤ) (z : Fin n → ℤ) :
    request ((queryConfig bt k l R prec pool,encMat encI B),List.ofFn z) =
    encS (poolBDDInput B R prec pool (FineGridDecoding.input B (2^bt.length) (FineGridDecoding.residue (2^bt.length) z))) := by
  have hm : (readMatrix (encMat encI B)).2 = RationalInverse.Native.inputRows B := by
    rw [←serializeMatrix_eq]
    simpa using congrArg Prod.snd (NativePaddedWords.readMatrix_serialized (RationalInverse.Native.inputRows B) [])
  simp only [request,queryConfig,hm,points_value B hB,NativeFixedResidue.modulus_eq,serializePoints_ofFn,body,poolBDDInput]
  rfl

theorem physical_answer (bt : List Unit) (z : Fin n → ℤ) :
    serializeVector (answers (bt,List.ofFn z)) = encVec encI (FineGridDecoding.answer (2^bt.length) z) := by
  have ha : answers (bt,List.ofFn z)=List.ofFn (FineGridDecoding.answer (2^bt.length) z) := by
    simp only [answers,List.map_ofFn,Function.comp_def,NativeLLL.intDivNat_eq,NativeFixedResidue.modulus_eq]
    rfl
  rw [ha]
  simp only [serializeVector,Integration9_9.LARPlatformEncoding.serializeBinaryWords_map,encVec]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule224

/- Helper module TapeFrame. -/
section P2MDyadicModule225

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity CoherentInjection PaddedDecoder FineCodec

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

noncomputable section

theorem dataBits_tape {X Y A B : ℕ} (x : Bits X) (y : Bits Y) :
    List.ofFn (dataBits (a:=A) (b:=B) x y) =
    List.ofFn x ++ List.ofFn y ++ List.replicate (A+B) false := by
  have he : dataBits (a:=A) (b:=B) x y =
      Fin.append (Fin.append (Fin.append x y) (fun _ : Fin A => false)) (fun _ : Fin B => false) := by
    funext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          simp only [Fin.append_left]
          exact dataBits_old x y i
        | right i =>
          simp only [Fin.append_left,Fin.append_right]
          exact dataBits_fresh x y i
      | right i =>
        simp only [Fin.append_left,Fin.append_right]
        apply dataBits_work
        change X + Y ≤ X+Y+i.val
        omega
    | right i =>
      simp only [Fin.append_right]
      apply dataBits_work
      change X + Y ≤ X+Y+A+i.val
      omega
  rw [he]
  simp only [List.ofFn_fin_append,List.ofFn_const,List.append_assoc,List.replicate_add]

theorem finalBits_tape {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g) (w : Str) :
    List.ofFn (CoherentInjection.finalBits P Q w) =
      List.replicate (originalSize P Q w.length) false ++ f w ++
      List.replicate (outputSize P w.length-(f w).length+forwardWork P w.length+backwardWork P Q w.length) false := by
  rw [CoherentInjection.finalBits,dataBits_tape,List.ofFn_const]
  have he : List.ofFn (outputBits P w) = paddedOutput P w := rfl
  rw [he,paddedOutput_eq_append]
  simp [List.replicate_add,List.append_assoc]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule225

/- Helper module RectArena. -/
section P2MDyadicModule226

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

namespace InfoLossLAR.WorstCase.RectangularSource.Arena

open NativeDualQuotient GaussianRandomizedRounding.Wide.Coherent.Padding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic QAlgorithms QAlgorithms.Complexity

open Integration9_9.TM2PlatformSerialization RegevSearch.PhysicalFourier

open NativeTicketInteger (input split)

noncomputable section

abbrev QWidth (k : ℕ) := CoherentInjection.totalWidth Codec.forwardProgram Codec.inverseProgram k

def quotientSlots (ticks : List Unit) := CoherentInjection.wholeSlots Codec.forwardProgram Codec.inverseProgram (ticks.map fun _ => true)

@[fun_prop] theorem quotientSlots_poly : Poly quotientSlots := by unfold quotientSlots;fun_prop

theorem quotientSlots_length (ticks : List Unit) : (quotientSlots ticks).length=QWidth ticks.length := by
  rw [quotientSlots,List.map_const']
  exact CoherentInjection.wholeSlots_length _ _ _

def blanks (ts : List Unit) := (quotientSlots ts).map (fun _ => false) |>.drop ts.length

@[fun_prop] theorem blanks_poly : Poly blanks := by
  unfold blanks
  exact Poly.comp (f:=fun v : Str×ℕ => v.1.drop v.2) (g:=fun ts : List Unit => ((quotientSlots ts).map (fun _ => false),ts.length))
    Binary.drop_poly (by fun_prop)

theorem blanks_exact (ts : List Unit) : blanks ts = List.replicate (QWidth ts.length-ts.length) false := by
  rw [blanks,List.map_const',List.drop_replicate,quotientSlots_length]

theorem ticks_le (ts : List Unit) : ts.length≤QWidth ts.length := by
  have h := CoherentInjection.originalSize_ge Codec.forwardProgram Codec.inverseProgram ts.length
  unfold QWidth CoherentInjection.totalWidth CoherentInjection.width
  omega

variable (controls : Str→Binary.Config) (hc : Poly controls)

def insert (w : Str) : Str :=
  let p := split w
  let ts := Binary.ticks (controls p.1)
  input p.1 ((Binary.take (p.2,ts.length)++blanks ts)++Binary.drop (p.2,ts.length))

include hc in
@[fun_prop] theorem insert_poly : Poly (insert controls) := by
  unfold insert
  fun_prop

def strip (w : Str) : Str :=
  let p := split w
  let ts := Binary.ticks (controls p.1)
  input p.1 (Binary.take (p.2,ts.length)++Binary.drop (p.2,(quotientSlots ts).length))

include hc in
@[fun_prop] theorem strip_poly : Poly (strip controls) := by
  unfold strip
  fun_prop

def fw := insert controls ∘ Binary.forward controls

def bw := Binary.inverse controls ∘ strip controls

include hc in
@[fun_prop] theorem fw_poly : Poly (fw controls) := by unfold fw;exact Poly.comp (f:=insert controls) (g:=Binary.forward controls) (insert_poly controls hc) (Binary.forward_poly controls hc)

include hc in
@[fun_prop] theorem bw_poly : Poly (bw controls) := by unfold bw;exact Poly.comp (f:=Binary.inverse controls) (g:=strip controls) (Binary.inverse_poly controls hc) (strip_poly controls hc)

def P := Integration9_9.LARCoinLayout.rawPolyProgram (fw_poly controls hc)

def Q := Integration9_9.LARCoinLayout.rawPolyProgram (bw_poly controls hc)

theorem inserted (hdr q r : Str) (he : q.length=(Binary.ticks (controls hdr)).length) :
    insert controls (input hdr (q++r))=input hdr ((q++blanks (Binary.ticks (controls hdr)))++r) := by
  simp only [insert,Binary.take,Binary.drop,NativeTicketInteger.split_input,List.take_left' he,List.drop_left' he]

theorem stripped (hdr q r pad : Str) (he : q.length=(Binary.ticks (controls hdr)).length) :
    strip controls (input hdr ((q++blanks (Binary.ticks (controls hdr)))++r)++pad)=input hdr (q++r)++pad := by
  let ts := Binary.ticks (controls hdr)
  have hb : (q++blanks ts).length=(quotientSlots ts).length := by
    rw [List.length_append,blanks_exact,List.length_replicate,quotientSlots_length,he]
    have hh := ticks_le ts
    change ts.length+(_-ts.length)=_
    omega
  have hi (h t e : Str) : input h t++e=input h (t++e) := by simp only [NativeTicketInteger.input,List.append_assoc]
  rw [hi,hi,strip,NativeTicketInteger.split_input]
  apply congrArg (input hdr)
  change (((q++blanks ts)++r)++pad).take ts.length++(((q++blanks ts)++r)++pad).drop (quotientSlots ts).length=(q++r)++pad
  rw [List.append_assoc (q++blanks ts),List.drop_left' hb,List.append_assoc q,List.take_left' he,List.append_assoc]

theorem recover {n : ℕ} (hdr : Str) {pre a post : Fin n→Str} (h : Binary.Fits (controls hdr) pre a post)
    (hf : (Codec.input (Binary.matrix (controls hdr)) (Binary.numbers (controls hdr) a)).length≤(Binary.ticks (controls hdr)).length)
    (pad : Str) :
    bw controls (fw controls (input hdr (flattenBlocks (Binary.pieces pre a post)))++pad)=input hdr (flattenBlocks (Binary.pieces pre a post)) := by
  let ts := Binary.ticks (controls hdr)
  let q := Binary.padded (Binary.matrix (controls hdr)) ts (Binary.numbers (controls hdr) a)
  let r := flattenBlocks (fun i => pre i++post i)
  let w := input hdr (flattenBlocks (Binary.pieces pre a post))
  have he : q.length=ts.length := NativePaddedWords.current_length _ _
  have hfwd : Binary.forward controls w=input hdr (q++r) := Binary.forward_exact controls hdr h
  have hback : Binary.inverse controls (Binary.forward controls w++pad)=w := Binary.inverse_exact controls hdr h hf pad
  change Binary.inverse controls (strip controls (insert controls (Binary.forward controls w)++pad))=w
  rw [hfwd,inserted controls hdr q r he,stripped controls hdr q r pad he,←hfwd]
  exact hback

theorem input_bits (q : Str) {t : ℕ} (ht : q.length=t) :
    List.ofFn (CoherentInjection.inputBitsAt Codec.forwardProgram Codec.inverseProgram t q)=q++List.replicate (QWidth t-t) false := by
  rw [CoherentInjection.inputBitsAt,dataBits_tape,extension_word q (ht ▸ CoherentInjection.originalSize_ge Codec.forwardProgram Codec.inverseProgram t)]
  simp only [List.ofFn_const,List.append_assoc,← List.replicate_add,ht]
  congr 2
  have hh := CoherentInjection.originalSize_ge Codec.forwardProgram Codec.inverseProgram t
  unfold QWidth CoherentInjection.totalWidth CoherentInjection.width
  omega

end

end InfoLossLAR.WorstCase.RectangularSource.Arena

end P2MDyadicModule226

/- Helper module RectFramed. -/
section P2MDyadicModule227

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Arena

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary CoherentComputeUncompute CoherentInjection

open FiniteGateTransport RegevSearch.StageRegisters RegevSearch.PhysicalFourier

open NativeTicketInteger (input split)

open Integration9_9.TM2PlatformSerialization

noncomputable section

theorem input_tape {f g : Str→Str} (p : PolyProgram id id f) (q : PolyProgram id id g) {t : ℕ} (s : Str) (hs : s.length=t) :
    List.ofFn (inputBitsAt p q t s)=s++List.replicate (totalWidth p q t-t) false := by
  have ho := originalSize_ge p q t
  rw [inputBitsAt,dataBits_tape,extension_word s (by omega)]
  simp only [List.ofFn_const,List.append_assoc,←List.replicate_add,hs]
  congr 2
  unfold totalWidth width
  omega

variable {f g : Str→Str} (p : PolyProgram id id f) (q : PolyProgram id id g)

def headerPart (hdr : Str) := lengthToken hdr++hdr

def before (hdr : Str) (k : ℕ) := (headerPart hdr).length+k

theorem len (hdr : Str) {k : ℕ} (x : Bits k) : (input hdr (List.ofFn x)).length=before hdr k := by
  simp only [NativeTicketInteger.input,List.length_append,List.length_ofFn,headerPart,before]

def frameBits (hdr : Str) (k : ℕ) : Bits k ↪ Bits (totalWidth p q (before hdr k)) :=
  inputEncoding p q _ (fun x => input hdr (List.ofFn x)) (len hdr)
    (fun x y h => List.ofFn_inj.mp (congrArg Prod.snd (by simpa only [NativeTicketInteger.split_input] using congrArg split h)))

theorem frame_tape (hdr : Str) {k : ℕ} (x : Bits k) :
    List.ofFn (frameBits p q hdr k x)=headerPart hdr++List.ofFn x++
      List.replicate (totalWidth p q (before hdr k)-before hdr k) false := by
  simpa only [frameBits,inputEncoding,Function.Embedding.coeFn_mk,NativeTicketInteger.input,headerPart] using
    input_tape p q (input hdr (List.ofFn x)) (len hdr x)

theorem bound (hdr : Str) (k : ℕ) : (headerPart hdr).length+k≤totalWidth p q (before hdr k) := by
  have he := len hdr (fun _ : Fin k => false)
  have ht := originalSize_ge p q (before hdr k)
  change before hdr k≤_
  unfold totalWidth width
  omega

abbrev prepW (hdr : Str) (k : ℕ) := Window.wires (headerPart hdr).length (bound p q hdr k)

theorem framed_attach (hdr : Str) (k : ℕ) (v : QState k) :
    basisEmbedding (frameBits p q hdr k) v=attach (prepW p q hdr k) v
      (basis ((wireBitsEquiv (prepW p q hdr k) (frameBits p q hdr k (fun _ => false))).2)) := by
  let w := prepW p q hdr k
  let F := frameBits p q hdr k
  let o := (wireBitsEquiv w (F (fun _ => false))).2
  have inside (x : Bits k) : (wireBitsEquiv w (F x)).1=x := Window.inside _ _ _ _ rfl _ _ (frame_tape p q hdr x)
  have outside (x : Bits k) : (wireBitsEquiv w (F x)).2=o :=
    Window.outside _ _ _ _ rfl _ _ _ _ (frame_tape p q hdr x) (frame_tape p q hdr _)
  funext z
  change basisEmbedding F v z=v ((wireBitsEquiv w z).1)*basis o ((wireBitsEquiv w z).2)
  by_cases hz : (wireBitsEquiv w z).2=o
  · have he : F (wireBitsEquiv w z).1=z := (wireBitsEquiv w).injective
      (Prod.ext (inside _) ((outside _).trans hz.symm))
    conv_lhs => rw [←he,basisEmbedding_at]
    simp only [basis,if_pos hz,mul_one]
  · have he : z ∉ Set.range F := by rintro ⟨i,rfl⟩;exact hz (outside i)
    simp only [basisEmbedding_outside F _ _ he,basis,if_neg hz,mul_zero]

theorem run_source (hdr : Str) {k : ℕ} (c : Layered k) (b : Bits k) :
    runLayered (relocateCircuit (prepW p q hdr k) c) (basis (frameBits p q hdr k b)) =
      basisEmbedding (frameBits p q hdr k) (runLayered c (basis b)) := by
  have h : basisEmbedding (frameBits p q hdr k) (basis b)=basis (frameBits p q hdr k b) := by
    funext y
    by_cases hy : y∈Set.range (frameBits p q hdr k)
    · obtain ⟨a,rfl⟩ := hy
      simp [basisEmbedding_at,basis,(frameBits p q hdr k).injective.eq_iff]
    · rw [basisEmbedding_outside _ _ _ hy]
      simp [basis,show y≠frameBits p q hdr k b from fun hh => hy ⟨b,hh.symm⟩]
  rw [←h,framed_attach,framed_attach,run_attach]

end

end InfoLossLAR.WorstCase.RectangularSource.Arena

end P2MDyadicModule227

/- Helper module RectLoaded. -/
section P2MDyadicModule228

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.Arena

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary CoherentComputeUncompute CoherentInjection

open ControlledNativeGates FiniteGateTransport RegevSearch.StageRegisters RegevSearch.PhysicalFourier

open NativeTicketInteger (input split)

noncomputable section

variable {f g : Str→Str} (p : PolyProgram id id f) (q : PolyProgram id id g)

variable {I Y : Type} [Fintype I] [Fintype Y] {k t : ℕ}

def wRaw (hdr : Str) (e : I×Y ↪ Bits k) (xy : I×Y) := input hdr (List.ofFn (e xy))

theorem wRaw_len (hdr : Str) (e : I×Y ↪ Bits k) (xy) : (wRaw hdr e xy).length=before hdr k := len hdr _

theorem wRaw_inj (hdr : Str) (e : I×Y ↪ Bits k) : Function.Injective (wRaw hdr e) := by
  intro i j he
  apply e.injective
  apply List.ofFn_inj.mp
  have ht := congrArg split he
  simpa only [wRaw,NativeTicketInteger.split_input,Prod.mk.injEq,true_and] using ht

def leftWord (hdr : Str) (k : ℕ) := List.replicate (originalSize p q (before hdr k)) false++headerPart hdr

def rightWord (hdr : Str) (k t : ℕ) (r : Str) :=
  r++List.replicate (outputSize p (before hdr k)-((headerPart hdr).length+t+r.length)+forwardWork p (before hdr k)+backwardWork p q (before hdr k)) false

theorem final_tape (hdr : Str) (e : I×Y ↪ Bits k) (mid : I→Bits t) (tail : Y→Str)
    (dest : ∀ i y,f (wRaw hdr e (i,y))=input hdr (List.ofFn (mid i)++tail y)) (i : I) (y : Y) :
    List.ofFn (finalBitsAt p q (before hdr k) (wRaw hdr e (i,y)))=
      leftWord p q hdr k++List.ofFn (mid i)++rightWord p q hdr k t (tail y) := by
  let ww := wRaw hdr e (i,y)
  have hl : ww.length=before hdr k := wRaw_len .. 
  have hh := finalBits_tape p q ww
  change List.ofFn (finalBitsAt p q ww.length ww)=_ at hh
  rw [hl] at hh
  rw [hh,show f ww=_ from dest i y]
  simp only [NativeTicketInteger.input,headerPart,leftWord,rightWord,List.length_append,List.length_ofFn,List.append_assoc]
  congr 6 <;> omega

theorem fits (hdr : Str) (e : I×Y ↪ Bits k) (mid : I→Bits t) (tail : Y→Str)
    (dest : ∀ i y,f (wRaw hdr e (i,y))=input hdr (List.ofFn (mid i)++tail y)) (i : I) (y : Y) :
      (leftWord p q hdr k).length+t ≤ totalWidth p q (before hdr k) := by
  have he := congrArg List.length (final_tape p q hdr e mid tail dest i y)
  simp only [List.length_ofFn,List.length_append] at he
  omega

abbrev after (hdr : Str) (e : I×Y ↪ Bits k)
    (inv : ∀ u,g (CoherentClassicalOracle.paddedOutput p (wRaw hdr e u))=wRaw hdr e u) :=
  outputEncoding p q (before hdr k) _ (wRaw_len hdr e) (wRaw_inj hdr e) inv

theorem serializer (hdr : Str) (e : I×Y ↪ Bits k)
    (inv : ∀ v,g (CoherentClassicalOracle.paddedOutput p (wRaw hdr e v))=wRaw hdr e v) (ψ : I×Y→ℂ) :
    runLayered (circuit p q (before hdr k)) (basisEmbedding (frameBits p q hdr k) (basisEmbedding e ψ))=
      basisEmbedding (after p q hdr e inv) ψ := by
  rw [basis_comp]
  exact circuit_superposition p q (before hdr k) (wRaw hdr e) (wRaw_len hdr e) (wRaw_inj hdr e) inv ψ

theorem composed (hdr : Str) (e : I×Y ↪ Bits k) (mid : I↪Bits t) (tail : Y→Str)
    (inv : ∀ v,g (CoherentClassicalOracle.paddedOutput p (wRaw hdr e v))=wRaw hdr e v)
    (dest : ∀ i y,f (wRaw hdr e (i,y))=input hdr (List.ofFn (mid i)++tail y))
    (i₀ : I) (y₀ : Y) (c : Layered k) (b : Bits k) (ψ : I→ℂ) (ξ : EuclideanSpace ℂ Y) (norm : ‖ξ‖=1)
    {ε : ℝ} (hp : stateNorm (runLayered c (basis b)-basisEmbedding e (fun u => ψ u.1*ξ u.2))≤ε) :
    let w := Window.wires (leftWord p q hdr k).length (fits p q hdr e mid tail dest i₀ y₀)
    ∃ junk : OutsideBits w→ℂ, (∑ z,‖junk z‖^2)=1 ∧
      stateNorm (runLayered (circuit p q (before hdr k))
        (runLayered (relocateCircuit (prepW p q hdr k) c) (basis (frameBits p q hdr k b)))-
        attach w (basisEmbedding mid ψ) junk)≤ε := by
  intro w
  let F := after p q hdr e inv
  have ht (i y) : List.ofFn (F (i,y))=leftWord p q hdr k++List.ofFn (mid i)++rightWord p q hdr k t (tail y) :=
    final_tape p q hdr e mid tail dest i y
  have hi (i y) : (wireBitsEquiv w (F (i,y))).1=mid i := Window.inside _ _ _ _ rfl _ _ (ht i y)
  have ho (i y) : (wireBitsEquiv w (F (i,y))).2=(wireBitsEquiv w (F (i₀,y))).2 :=
    Window.outside _ _ _ _ rfl _ _ _ _ (ht i y) (ht i₀ y)
  obtain ⟨junk,hj,heq⟩ := Window.fixed_exterior w F mid i₀ hi ho ψ ξ norm
  refine ⟨junk,hj,?_⟩
  rw [←heq,←serializer p q hdr e inv,run_source p q hdr c b]
  let C := circuit p q (before hdr k)
  let A := basisEmbedding (frameBits p q hdr k)
  let φ := runLayered c (basis b)
  let θ := basisEmbedding e (fun u => ψ u.1*ξ u.2)
  change stateNorm (runLayered C (A φ)-runLayered C (A θ))≤ε
  have hd : stateNorm (runLayered C (A φ)-runLayered C (A θ))=stateNorm (A φ-A θ) :=
    (show ‖(circuitIsometry C) (WithLp.toLp 2 (A φ))-(circuitIsometry C) (WithLp.toLp 2 (A θ))‖=_ from
      by rw [←map_sub,(circuitIsometry C).norm_map];rfl)
  rw [hd]
  exact (basisEmbedding_error _ _ _).le.trans hp

end

end InfoLossLAR.WorstCase.RectangularSource.Arena

end P2MDyadicModule228

/- Helper module RectTail. -/
section P2MDyadicModule229

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource

open GaussianRandomizedRounding GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent

open CoherentProjection GaussianPoissonSeries NativeDualQuotient RegevLWE.GaussConv AFT GaussianSource

theorem complementary_sq {I J : Type*} [Fintype J] (e : J ↪ I) (g : Hilbert I) (hg : ‖g‖=1) :
    (∑' i,if i ∈ Set.range e then 0 else ‖g i‖^2) = 1 - ‖finiteRestrict e g‖^2 := by
  let E := fun i => i ∈ Set.range e
  have hs : Summable (fun i => ‖g i‖^2) := by
    simpa using (lp.memℓp g).summable (by norm_num)
  have ha := summable_filtered_nonnegative _ hs (fun i => sq_nonneg _) E
  have hb := summable_filtered_nonnegative _ hs (fun i => sq_nonneg _) (fun i => ¬E i)
  have hpair := ha.tsum_add hb
  have hsplit : (fun i => (if E i then ‖g i‖^2 else 0) + if ¬E i then ‖g i‖^2 else 0) =
      fun i => ‖g i‖^2 := by funext i;by_cases h : E i <;> simp [h]
  rw [hsplit,←hilbert_norm_sq,hg,one_pow] at hpair
  have he : (∑' i,if E i then ‖g i‖^2 else 0) = ‖finiteRestrict e g‖^2 := by
    rw [←finiteEmbed_norm e (finiteRestrict e g),finiteEmbed_restrict,hilbert_norm_sq]
    apply tsum_congr
    intro i
    rw [hilbertProject_apply]
    change _=‖if E i then _ else _‖^2
    split_ifs <;> simp
  rw [he] at hpair
  simpa only [ite_not,E] using (eq_sub_of_add_eq' hpair.symm :
    (∑' i,if ¬E i then ‖g i‖^2 else 0) = 1-‖finiteRestrict e g‖^2)

theorem drop_one (s : ℝ) (hs : 1 ≤ s) (R : ℕ) :
    0 ≤ 1-retained s (zero_lt_one.trans_le hs) R ∧
    1-retained s (zero_lt_one.trans_le hs) R ≤ tailEnvelope s R := by
  have he := outsideWindowMass_eq 1 s (zero_lt_one.trans_le hs) 0 R
  rw [retainedResidue_sum] at he
  have he' : outsideWindowMass s (zero_lt_one.trans_le hs) 0 R = 1 - retained s (zero_lt_one.trans_le hs) R := by
    simpa only [retained,coord_apply,Rat.cast_zero] using he
  rw [←he']
  exact ⟨tsum_nonneg (fun i => by split_ifs <;> positivity),outsideWindowMass_le _ hs _ _⟩

theorem drop_many {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (n : ℕ) :
    1-a^n ≤ (n:ℝ)*(1-a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    have h := mul_le_mul_of_nonneg_right (pow_le_one₀ ha ha' (n:=n)) (sub_nonneg.mpr ha')
    linarith

theorem rectangular_close {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (M s : ℝ)
    (hM : 0<M) (hs : 0 < s) (input : PointRequest)
    (hw : 1 ≤ s*M*(originalDenominator B:ℝ))
    (hv : (s*M*(originalDenominator B:ℝ))^2=(variance input : ℝ)) :
    let e := boxAmbient B M hM (radius input)
    let g := gaussianHilbertState (Ambient B M hM) s hs 0
    ‖finiteEmbed e (repeatState n (window (s*M*(originalDenominator B:ℝ)) (radius input))) - g‖ ≤
      2*Real.sqrt ((n:ℝ)*(6*Real.exp (-Real.pi*(input.2.1.length:ℝ)^2/2))) := by
  let u := s*M*(originalDenominator B:ℝ)
  have hu : 0<u := zero_lt_one.trans_le hw
  let R := radius input
  let e := boxAmbient B M hM R
  let g := gaussianHilbertState (Ambient B M hM) s hs 0
  let v := repeatState n (window u R)
  have hvn : ‖v‖=1 := repeatState_normalized n _ (window_norm u R)
  have hsc : finiteRestrict e g = (Real.sqrt (retained u hu R))^n • v := by
    rw [←integer_restriction]
    ext j
    simp only [e,g,u,finiteRestrict,boxAmbient,← nativeAmbient_product_state B M s hM hs,
      Function.Embedding.trans_apply,Equiv.toEmbedding_apply,hilbertReindex_apply,Equiv.symm_apply_apply]
  have hr := retained_pos u hu R
  have hcoef := pow_pos (Real.sqrt_pos.mpr hr) n
  have hnorm : ‖finiteRestrict e g‖ = (Real.sqrt (retained u hu R))^n := by
    rw [hsc,norm_smul,hvn,mul_one,Real.norm_eq_abs,abs_of_pos hcoef]
  have hn (d : DecidablePred (fun i => i ∈ Set.range e)) :
      @hilbertProject _ (fun i => i ∈ Set.range e) d g ≠ 0 := by
    intro hz
    have hzero : finiteRestrict e g = 0 := by
      ext j
      have hp := congrArg (fun V : Hilbert _ => V (e j)) hz
      rw [hilbertProject_apply,if_pos ⟨j,rfl⟩] at hp
      exact hp
    rw [hzero,norm_zero] at hnorm
    linarith
  have htail (d : DecidablePred (fun i => i ∈ Set.range e)) :
      (∑' i, @ite ℝ (i ∈ Set.range e) (d i) 0 (‖g i‖^2)) = 1 - (retained u hu R)^n := by
    calc
      _ = 1 - ‖finiteRestrict e g‖^2 := by
        refine Eq.trans ?_ (complementary_sq e g (gaussianHilbertState_norm _ _ _ _))
        apply tsum_congr
        intro i
        by_cases h : i ∈ Set.range e <;> simp [h]
      _ = _ := by rw [hnorm,←pow_mul,mul_comm n 2,pow_mul,Real.sq_sqrt hr.le]
  have hd := drop_one u hw R
  have hl := ((drop_many hr.le (by linarith [hd.1]) n).trans (mul_le_mul_of_nonneg_left
    (hd.2.trans (scaled_tail_bound input u hw hv)) (Nat.cast_nonneg n)))
  have hclose := finite_restriction_close e g (gaussianHilbertState_norm _ _ _ _) (hn _) _ ((htail _).le.trans hl)
  rw [ambient_restriction] at hclose
  exact (norm_sub_rev _ _).le.trans hclose

end InfoLossLAR.WorstCase.RectangularSource

end

end P2MDyadicModule229

/- Helper module RectPort. -/
section P2MDyadicModule230

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.Arena

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeDualQuotient CoherentComputeUncompute CoherentProjection FiniteGateTransport ControlledNativeGates

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent GaussianRandomizedRounding.Wide.Coherent.Padding

open RegevSearch.PhysicalFourier RegevSearch.StageRegisters

noncomputable section

variable (request : Str→PointRequest × List Unit) (hr : Poly request)

variable (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (hK : Nat.size (intervalCount (request word).1)≤K) (m n : ℕ)

variable (controls : Str→Binary.Config) (hctrl : Poly controls) (hdr : Str)

variable (cf : frame request hr a slots word K m n (controls hdr))

abbrev ticks := Binary.ticks (controls hdr)

abbrev boxE := box n (radius (request word).1)

abbrev rawE := E request hr a slots word K hK m n

variable (B : Matrix (Fin n) (Fin n) ℤ) (hm : Binary.matrix (controls hdr)=RationalInverse.Native.inputRows B)

abbrev Fits := ∀ x,(Codec.input (RationalInverse.Native.inputRows B) (List.ofFn (boxE request word n x))).length≤(ticks controls hdr).length

abbrev inBox (hf : Fits request word n controls hdr B) := nativeIn B (ticks controls hdr) (boxE request word n) hf

include cf hm in
theorem dest (hf : Fits request word n controls hdr B) (i y) :
    fw controls (wRaw hdr (rawE request hr a slots word K hK m n) (i,y)) =
      NativeTicketInteger.input hdr (List.ofFn (inBox request word n controls hdr B hf i)++saved request hr a slots word K m n y) := by
  let ts := ticks controls hdr
  let qword := Codec.words B ts (boxE request word n) i
  let rest := saved request hr a slots word K m n y
  have hl : qword.length=ts.length := Codec.words_length B ts _ i
  have hd : Binary.forward controls (wRaw hdr (rawE request hr a slots word K hK m n) (i,y))=NativeTicketInteger.input hdr (qword++rest) := by
    have h := destination request hr a slots word K hK m n controls hdr cf i y
    rw [hm] at h
    exact h
  have hq : List.ofFn (inBox request word n controls hdr B hf i)=qword++blanks ts := by
    rw [blanks_exact]
    exact input_bits qword hl
  rw [hq]
  exact (congrArg (insert controls) hd).trans (inserted controls hdr qword rest hl)

include cf hm in
theorem inv (hf : Fits request word n controls hdr B) (v) :
    bw controls (CoherentClassicalOracle.paddedOutput (P controls hctrl)
      (wRaw hdr (rawE request hr a slots word K hK m n) v))=wRaw hdr (rawE request hr a slots word K hK m n) v := by
  rcases v with ⟨i,y⟩
  change bw controls (TM2Boolean.PolyProgramCircuit.paddedOutput (P controls hctrl)
    (raw request hr a slots word K hK m n hdr (i,y)))=raw request hr a slots word K hK m n hdr (i,y)
  rw [TM2Boolean.PolyProgramCircuit.paddedOutput_eq_append,raw_blocks]
  apply recover
  · exact pieces_fit request hr a slots word K hK m n _ cf i y
  · rw [low_signed request hr a slots word K m n _ cf i,hm]
    exact hf i

abbrev first (i : X request word n) (y : Y request hr a slots word K m n)
    (hf : Fits request word n controls hdr B) := Window.wires
      (leftWord (P controls hctrl) (Q controls hctrl) hdr (W request hr a slots K m n)).length
      (fits (P controls hctrl) (Q controls hctrl) hdr (rawE request hr a slots word K hK m n)
        (inBox request word n controls hdr B hf) (saved request hr a slots word K m n)
        (dest request hr a slots word K hK m n controls hdr cf B hm hf) i y)

abbrev full (hdr : Str) (C : Layered (W request hr a slots K m n)) :=
  relocateCircuit (prepW (P controls hctrl) (Q controls hctrl) hdr (W request hr a slots K m n)) C++
    CoherentInjection.circuit (P controls hctrl) (Q controls hctrl) (before hdr (W request hr a slots K m n))

theorem port (hf : Fits request word n controls hdr B)
    (i : X request word n) (y : Y request hr a slots word K m n)
    (C : Layered (W request hr a slots K m n)) (b : Bits (W request hr a slots K m n))
    (ψ : X request word n →ℂ) (ξ : EuclideanSpace ℂ (Y request hr a slots word K m n)) (hξ : ‖ξ‖=1)
    (ε : ℝ) (herr : stateNorm (runLayered C (basis b)-
      basisEmbedding (rawE request hr a slots word K hK m n) (fun u => ψ u.1*ξ u.2))≤ε) :
    let wire := first request hr a slots word K hK m n controls hctrl hdr cf B hm i y hf
    ∃ junk : OutsideBits wire→ℂ, (∑ z,‖junk z‖^2)=1 ∧
      stateNorm (runLayered (full request hr a slots K m n controls hctrl hdr C)
        (basis (frameBits (P controls hctrl) (Q controls hctrl) hdr _ b))-
        attach wire (basisEmbedding (inBox request word n controls hdr B hf) ψ) junk)≤ε := by
  dsimp only
  simp only [full,runLayered,List.foldl_append]
  exact composed (P controls hctrl) (Q controls hctrl) hdr _ (inBox request word n controls hdr B hf)
    (saved request hr a slots word K m n) (inv request hr a slots word K hK m n controls hctrl hdr cf B hm hf)
    (dest request hr a slots word K hK m n controls hdr cf B hm hf) i y C b ψ ξ hξ herr

end

end InfoLossLAR.WorstCase.RectangularSource.Arena

end P2MDyadicModule230

/- Helper module RectFrontEmit. -/
section P2MDyadicModule231

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

namespace InfoLossLAR.WorstCase.RectangularSource.FrontEmit

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent.Padding

open FiniteGateTransport NativeDualQuotient NativeWordLayout Integration9_9.TM2PlatformSerialization

open Arena

noncomputable section

variable (request : Str→PointRequest × List Unit) (hr : Poly request) (a b : ℕ) (q : Polynomial ℕ)

variable (controls : Str→Binary.Config) (hc : Poly controls)

attribute [local irreducible] P Q Codec.forwardProgram Codec.inverseProgram

abbrev Inp := Str × Emit.Input

def dataBits (v : Inp) := Emit.initial request hr a v.2

@[fun_prop] theorem dataBits_poly : Poly (dataBits request hr a) := by unfold dataBits;fun_prop

def initial (v : Inp) := NativeTicketInteger.input v.1 (dataBits request hr a v)

@[fun_prop] theorem initial_poly : Poly (initial request hr a) := by unfold initial;fun_prop

def clock (v : Inp) := (initial request hr a v).map (fun _ => true)

@[fun_prop] theorem clock_poly : Poly (clock request hr a) := by unfold clock;fun_prop

def arenaSlots (v : Inp) := CoherentInjection.wholeSlots (P controls hc) (Q controls hc) (clock request hr a v)

@[fun_prop] theorem arenaSlots_poly : Poly (arenaSlots request hr a controls hc) := by unfold arenaSlots;fun_prop

def prepOff (v : Inp) := (lengthToken v.1++v.1).length

@[fun_prop] theorem prepOff_poly : Poly prepOff := by unfold prepOff;fun_prop

def quotientOff (v : Inp) :=
  (CoherentInjection.outputTicks (Q controls hc) (CoherentInjection.inverseWord (P controls hc) (clock request hr a v))).length+prepOff v

@[fun_prop] theorem quotientOff_poly : Poly (quotientOff request hr a controls hc) := by unfold quotientOff;fun_prop

def stageOne (v : Inp) := Window.emit ((arenaSlots request hr a controls hc v,prepOff v),(dataBits request hr a v).map (fun _ => ()),Emit.many request hr a b q v.2)

@[fun_prop] theorem one_poly : Poly (stageOne request hr a b q controls hc) := by unfold stageOne;fun_prop

def stageTwo (v : Inp) := CoherentInjection.emitted (P controls hc) (Q controls hc) (clock request hr a v)

@[fun_prop] theorem two_poly : Poly (stageTwo request hr a controls hc) := Poly.comp (f:=CoherentInjection.emitted (P controls hc) (Q controls hc)) (g:=clock request hr a) (CoherentInjection.emitted_poly _ _) (clock_poly request hr a)

def stageThree (v : Inp) := Window.emit ((arenaSlots request hr a controls hc v,quotientOff request hr a controls hc v),quotientSlots (Binary.ticks (controls v.1)),CoherentInjection.emitted Codec.forwardProgram Codec.inverseProgram ((Binary.ticks (controls v.1)).map (fun _ => true)))

@[fun_prop] theorem three_poly : Poly (stageThree request hr a controls hc) := by unfold stageThree;fun_prop

def stage (v : Inp) : List (List Str) :=
  stageOne request hr a b q controls hc v++stageTwo request hr a controls hc v++stageThree request hr a controls hc v

@[fun_prop] theorem stage_poly : Poly (stage request hr a b q controls hc) := by
  let A := stageOne request hr a b q controls hc
  let B := stageTwo request hr a controls hc
  let C := stageThree request hr a controls hc
  have app {α : Type} [Coding α] [Inhabited α] {x y : Inp→List α} (hx : Poly x) (hy : Poly y) : Poly (fun v => x v++y v) :=
    Poly.comp (f:=fun z : List α ×List α => z.1++z.2) (g:=fun v => (x v,y v)) Poly.list_append (Poly.pair hx hy)
  exact app (x:=fun v => A v++B v) (y:=C) (app (x:=A) (y:=B) (one_poly _ _ _ _ _ _ _) (two_poly _ _ _ _ _)) (three_poly _ _ _ _ _)

def extent (v : Inp) := (dataBits request hr a v).length

theorem clock_eq (v : Inp) : clock request hr a v=unary (before v.1 (extent request hr a v)) := by
  simp only [clock,List.map_const',initial,NativeTicketInteger.input,List.length_append,before,headerPart,extent,unary]

theorem arenaSlots_eq (v : Inp) : (arenaSlots request hr a controls hc v).length=
    CoherentInjection.totalWidth (P controls hc) (Q controls hc) (before v.1 (extent request hr a v)) := by
  rw [arenaSlots,clock_eq,CoherentInjection.wholeSlots_length]

theorem quotientOff_eq (v : Inp) : quotientOff request hr a controls hc v=
    (leftWord (P controls hc) (Q controls hc) v.1 (extent request hr a v)).length := by
  rw [quotientOff,clock_eq,CoherentInjection.inverseWord_exact,CoherentInjection.outputTicks_length]
  simp only [leftWord,List.length_append,List.length_replicate,prepOff,headerPart]

theorem relocate_by_length {N k : ℕ} (cap ks : List Unit) (hc : N ≤ cap.length) (hk : ks.length=k)
    (off : ℕ) (h : off+k ≤ N) (c : Layered k) :
    Window.emit ((cap,off),ks,c.map (List.map encInstr))=(relocateCircuit (Window.wires off h) c).map (List.map encInstr) := by
  subst k
  exact Window.emit_exact cap hc off ks h c

end

end InfoLossLAR.WorstCase.RectangularSource.FrontEmit

end P2MDyadicModule231

/- Helper module RectFit. -/
section P2MDyadicModule232

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RectangularSource.WordBudget

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic QAlgorithms.Complexity

open Integration9_9.TM2NativeAffineEmitter

open Integration9_9.LARPlatformEncoding (serializeBinaryWords)

open NativeDualQuotient GaussianPoissonSeries RegevSearch.PhysicalFourier

open GaussianRandomizedRounding.Wide

theorem binary_length (n : ℕ) : (encB n).length=2*n.bits.length+1 := by
  simp [encB,List.length_flatMap,List.sum_replicate,Nat.mul_comm]

theorem signed_mono (z : ℤ) (b : ℕ) (h : z.natAbs ≤ b) : (encI z).length ≤ (encI (b:ℤ)).length := by
  simp only [encI,List.length_cons,binary_length,Int.natAbs_natCast]
  have hh := NatBinary.length_mono h;omega

theorem vec_mono {n : ℕ} (v : Fin n→ℤ) (b : ℕ) (hb : ∀ i,(v i).natAbs ≤ b) :
    (serializeVector (List.ofFn v)).length ≤ (serializeVector (List.replicate n (b:ℤ))).length := by
  simp only [serializeVector,serializeBinaryWords,List.length_append,List.length_map,List.length_ofFn,List.length_replicate]
  apply Nat.add_le_add_left
  rw [List.length_flatten,List.length_flatten,List.map_map,List.map_map]
  simp only [List.map_ofFn,List.map_replicate,List.sum_ofFn,List.sum_replicate]
  calc
    _ ≤ ∑ _i : Fin n,(encI (b:ℤ)).length := Finset.sum_le_sum (fun i _ => signed_mono _ _ (hb i))
    _ = _ := by simp

theorem encS_mono {u v : Str} (h : u.length ≤ v.length) : (encS u).length ≤ (encS v).length := by
  simp only [encS,List.length_append,binary_length]
  have hl := NatBinary.length_mono h
  omega

abbrev Input := List (List ℤ) × ℕ

def tape (x : Input) := (Codec.input x.1 (x.1.map (fun _ => (x.2:ℤ)))).map (fun _ => ())

@[fun_prop] theorem tape_poly : Poly tape := by unfold tape Codec.input;fun_prop

theorem fit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (b : ℕ) (v : Fin n→ℤ) (hv : ∀ i, (v i).natAbs≤b) :
    (Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)).length ≤ (tape (RationalInverse.Native.inputRows B,b)).length := by
  have hz := encS_mono (vec_mono v b hv)
  simp only [tape,List.length_map,Codec.input,serialize,encPair,List.map_const',
    show (RationalInverse.Native.inputRows B).length=n from List.length_ofFn,List.length_append,List.length_replicate]
  omega

theorem source_box {n R : ℕ} (x : Fin n → Side R) (i : Fin n) : |box n R x i| ≤ (R:ℤ) := by
  simp only [box,Function.Embedding.coeFn_mk,coord_apply,GaussianRandomizedRounding.windowPoint,AFT.RationalNumerics.centeredGaussianAnchor]
  have hx := (x i).isLt
  norm_num
  apply abs_le.mpr
  constructor <;> omega

theorem joint_fit {n M Rb : ℕ} [NeZero M] (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℝ)
    [Fintype (Residual B)] [Fintype (Retained (RegevLWE.GaussConv.dual (IntegerBasis.inputLattice B hB)) M R)]
    (limit : ℕ) (hbox : Rb ≤ limit)
    (hshort : (originalDenominator B : ℝ)*((M:ℝ)*R+dualColumnBudget B hB) ≤ (limit:ℝ)) :
    let z := supportVals (box n Rb) (integerSplit B hB M) (fineEmbedding _ M R)
    ∀ u,(Codec.input (RationalInverse.Native.inputRows B) (List.ofFn (z u))).length ≤ (tape (RationalInverse.Native.inputRows B,limit)).length := by
  intro z u
  apply fit
  intro i
  have hh := support_fit B hB R (box n Rb) (Rb:ℤ) source_box u.val u.property i
  have hb : (Rb:ℤ) ≤ (limit:ℤ) := by exact_mod_cast hbox
  have hc : ⌈(originalDenominator B : ℝ)*((M:ℝ)*R+dualColumnBudget B hB)⌉ ≤ (limit:ℤ) :=
    Int.ceil_le.mpr (by exact_mod_cast hshort)
  have hi := hh.trans (max_le hb hc)
  change (u.val i).natAbs ≤ limit
  exact_mod_cast (show (↑(u.val i).natAbs:ℤ)≤(limit:ℤ) by simpa only [Int.natCast_natAbs] using hi)

end InfoLossLAR.WorstCase.RectangularSource.WordBudget

end P2MDyadicModule232

/- Helper module Solutions.RegevBridgeNativeGaussianBudget. -/
section P2MDyadicModule233

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv RationalInverse RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

noncomputable section

/-- A canonical rational height bound controls its real magnitude without
assuming any bound on an unreduced input numerator or denominator. -/
theorem rationalHeight_real_abs (value : ℚ) (bits : ℕ) (h : HeightBound value bits) :
    |(value : ℝ)| ≤ (2 : ℝ)^bits := by
  have hden : (1 : ℝ) ≤ value.den := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr value.den_nz)
  have hnum : |(value.num : ℝ)| ≤ (2 : ℝ)^bits := by
    have hh : (value.num.natAbs : ℝ) ≤ (2 : ℝ)^bits := by exact_mod_cast h.1
    have heq : (value.num.natAbs : ℝ)=|(value.num : ℝ)| := by
      have ht := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs value.num)
      simpa only [Int.cast_natCast,Int.cast_abs] using ht
    rwa [heq] at hh
  rw [Rat.cast_def,abs_div,show |(value.den : ℝ)|=(value.den : ℝ) from abs_of_pos (by exact_mod_cast value.den_pos)]
  apply (div_le_iff₀ (by exact_mod_cast value.den_pos : (0 : ℝ) < value.den)).mpr
  exact hnum.trans (le_mul_of_one_le_right (by positivity) hden)

/-- The actual original dual columns admit a binary input-height bound;
no efficiently short basis or shortest-vector information is assumed. -/
theorem dualColumn_norm_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (bits : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^bits)
    (column : Fin dimension) :
    ‖IntegerBasis.dualRealBasis basis hdet column‖ ≤
      ((dimension : ℝ)+1)*(2 : ℝ)^(dualHeight dimension bits) := by
  rw [←dualVector_real basis hdet column]
  have hpoint (row : Fin dimension) : |(dualVector basis column row : ℝ)| ≤ (2 : ℝ)^(dualHeight dimension bits) :=
    rationalHeight_real_abs _ _ (dualVector_height basis bits hentries column row)
  have hsum : ‖realVec (dualVector basis column)‖^2 ≤
      (dimension : ℝ)*((2 : ℝ)^(dualHeight dimension bits))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _row : Fin dimension,((2 : ℝ)^(dualHeight dimension bits))^2 := by
        apply Finset.sum_le_sum
        intro row _
        change ((dualVector basis column row : ℚ) : ℝ)^2 ≤ _
        rw [←sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hpoint row)
      _ = _ := by simp
  have hn : (0 : ℝ) ≤ dimension := Nat.cast_nonneg _
  have hc : (0 : ℝ) < (2 : ℝ)^(dualHeight dimension bits) := by positivity
  have hsquare : (dimension : ℝ) ≤ ((dimension : ℝ)+1)^2 := by nlinarith [sq_nonneg (dimension : ℝ)]
  have hlarge := mul_le_mul_of_nonneg_right hsquare (sq_nonneg ((2 : ℝ)^(dualHeight dimension bits)))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow] using hsum.trans hlarge

/-- The smoothing and coherent residual-shift budget has a bound whose
binary exponent is polynomial in the original dimension and input height. -/
theorem dualColumnBudget_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (bits : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^bits) :
    dualColumnBudget basis hdet ≤
      1+(dimension : ℝ)*((dimension : ℝ)+1)*(2 : ℝ)^(dualHeight dimension bits) := by
  dsimp only [dualColumnBudget]
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin dimension)))
    (fun column _ => dualColumn_norm_height basis hdet bits hentries column)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  linarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule233

/- Helper module Solutions.RegevBridgeNativeGaussianDyadicBudget. -/
section P2MDyadicModule234

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RationalInverse

open scoped BigOperators

noncomputable section

theorem dualColumnBudget_dyadic {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (bits : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^bits) :
    dualColumnBudget basis hdet ≤ (2 : ℝ)^(dualColumnBudgetBits dimension bits) := by
  have hn : (dimension : ℝ) ≤ (2 : ℝ)^dimension := by exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hn' : (dimension : ℝ)+1 ≤ (2 : ℝ)^(dimension+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension+1)).le
  have hproduct := mul_le_mul hn hn' (by positivity) (by positivity)
  have hp : (dimension : ℝ)*((dimension : ℝ)+1)*(2 : ℝ)^(dualHeight dimension bits) ≤
      (2 : ℝ)^(dualHeight dimension bits+2*dimension+1) := by
    calc
      _ ≤ ((2 : ℝ)^dimension*(2 : ℝ)^(dimension+1))*(2 : ℝ)^(dualHeight dimension bits) :=
        mul_le_mul_of_nonneg_right hproduct (by positivity)
      _ = _ := by
        rw [←pow_add,←pow_add]
        congr 1
        omega
  have hpower : (1 : ℝ) ≤ (2 : ℝ)^(dualHeight dimension bits+2*dimension+1) := one_le_pow₀ (by norm_num)
  have h := dualColumnBudget_height basis hdet bits hentries
  dsimp only [dualColumnBudgetBits]
  rw [show dualHeight dimension bits+2*dimension+2=(dualHeight dimension bits+2*dimension+1)+1 by omega,pow_succ]
  linarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule234

/- Helper module GridBudget. -/
section P2MDyadicModule235

set_option autoImplicit false

set_option maxHeartbeats 900000

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

open GaussianPoissonSeries RationalInverse GridReadout

noncomputable section

def eps (d : ℕ) : ℝ := 1/(2:ℝ)^(2*d+4)

theorem factor (n d : ℕ) (hn : 0 < n) : shortSmoothingFactor n (eps d) ≤ (2:ℝ)^(n+2*d+8) := by
  let X : ℝ := 4*(n:ℝ)*(1+1/(eps d))
  have he : 0<eps d := by unfold eps; positivity
  have hx : 1 < X := smoothing_log_arg_gt_one n (eps d) hn he
  have hlog : Real.log X / Real.pi ≤ X^2 := by
    have hp : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hlog : Real.log X ≤ X := (Real.log_le_sub_one_of_pos (zero_lt_one.trans hx)).trans (by linarith)
    exact (div_le_self (Real.log_nonneg hx.le) hp).trans (hlog.trans (by nlinarith [sq_nonneg (X-1)]))
  have hfac : shortSmoothingFactor n (eps d) ≤ X := Real.sqrt_le_iff.mpr ⟨(zero_lt_one.trans hx).le,hlog⟩
  have hd : (1:ℝ) ≤ 2^(2*d+4) := one_le_pow₀ (by norm_num)
  have hn' : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hval : 1+1/(eps d) ≤ 2*(2:ℝ)^(2*d+4) := by simp only [eps,one_div,inv_inv];linarith
  apply hfac.trans
  calc
    X ≤ 4*(2:ℝ)^n*(2*(2:ℝ)^(2*d+4)) := mul_le_mul (by gcongr) hval (by positivity) (by positivity)
    _ ≤ (2:ℝ)^(n+2*d+8) := by
      simp only [pow_add]
      norm_num
      nlinarith [mul_pos (by positivity : (0:ℝ)<2^n) (by positivity : (0:ℝ)<2^(2*d))]

private theorem ratio_bound {n H K d : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (hb : ∀ i j, |B i j| ≤ (2:ℤ)^H) :
    dualColumnBudget B hB/(2:ℝ)^(bits n H K d) ≤ (1/((2:ℝ)^(K+1)*(2:ℝ)^(n+2*d+8)*(2:ℝ)^(d+2))) := by
  let a := dualColumnBudgetBits n H
  have he : a+(K+1)+(n+2*d+8)+(d+2) ≤ bits n H K d := le_max_right _ _
  have hM := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) he
  have hD := dualColumnBudget_dyadic B hB H hb
  calc
    _ ≤ (2:ℝ)^a / (2:ℝ)^(a+(K+1)+(n+2*d+8)+(d+2)) :=
      div_le_div₀ (by positivity) hD (by positivity) hM
    _ = _ := by simp only [pow_add]; field_simp

theorem relative {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (r : ℝ) (hr : 0 < r) (H K d : ℕ) (hn : 0<n)
    (hb : ∀ i j, |B i j| ≤ (2:ℤ)^H) (hrK : r ≤ (2:ℝ)^K) :
    let u := 1/(2*r)
    let M := (2:ℝ)^(bits n H K d)
    shortSmoothingFactor n (eps d)*dualColumnBudget B hB / M ≤ u ∧
      dualColumnBudget B hB/M ≤ u*delta d/2 ∧ 1 ≤ u*M := by
  dsimp only
  let x : ℝ := 2^(K+1)
  let y : ℝ := 2^(n+2*d+8)
  let z : ℝ := 2^(d+2)
  let M : ℝ := 2^(bits n H K d)
  have hx : 0 < x := by dsimp [x];positivity
  have hy : 1 ≤ y := one_le_pow₀ (by norm_num)
  have hz : 1 ≤ z := one_le_pow₀ (by norm_num)
  have hbase : 2*r≤x := by dsimp [x];rw [pow_succ];linarith
  have hq : dualColumnBudget B hB/M ≤ 1/(x*y*z) := ratio_bound B hB hb
  have hq' : dualColumnBudget B hB/M ≤ 1/(x*y) := hq.trans (one_div_le_one_div_of_le
    (mul_pos hx (zero_lt_one.trans_le hy)) (le_mul_of_one_le_right (by positivity) hz))
  have hF : shortSmoothingFactor n (eps d) ≤ y := factor n d hn
  have hfirst : shortSmoothingFactor n (eps d)*(dualColumnBudget B hB/M) ≤ 1/x := by
    calc
      _ ≤ y*(1/(x*y)) := mul_le_mul hF hq' (div_nonneg (dualColumnBudget_pos _ _).le (by dsimp [M]; positivity)) (zero_le_one.trans hy)
      _ = _ := by field_simp
  have hcong : (1/x:ℝ) ≤ 1/(2*r) := one_div_le_one_div_of_le (by positivity) hbase
  refine ⟨by rw [mul_div_assoc];exact hfirst.trans hcong, ?_, ?_⟩
  · have hprod : x*(2*(2:ℝ)^d) ≤ x*y*z := by
      have h2 : 2*(2:ℝ)^d ≤ z := by dsimp [z];rw [pow_add];norm_num;nlinarith [show (0:ℝ)<2^d by positivity]
      calc
        _ ≤ x*z := mul_le_mul_of_nonneg_left h2 hx.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hx.le hy) (zero_le_one.trans hz)
    calc
      _ ≤ 1/(x*(2*2^d)) := hq.trans (one_div_le_one_div_of_le (by positivity) hprod)
      _ = (1/x)*delta d/2 := by unfold delta;ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcong (by unfold delta; positivity)) (by norm_num)
  · have hsize : K+1 ≤ bits n H K d := (by omega : K+1≤dualColumnBudgetBits n H+(K+1)+(n+2*d+8)+(d+2)).trans (le_max_right _ _)
    have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hsize
    rw [one_div,inv_mul_eq_div]
    exact (one_le_div (by positivity)).mpr (hbase.trans hpow)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end P2MDyadicModule235

/- Helper module GridProgram. -/
section P2MDyadicModule236

set_option autoImplicit false

set_option maxHeartbeats 1800000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic AFT.RationalNumerics

open GaussianPoissonSeries RationalInverse RationalGramSchmidt.Native GridReadout

@[fun_prop] theorem gridCount_poly : Poly gridCount := by
  unfold gridCount bits gridBits dualColumnBudgetBits dualHeight
  simp only [Nat.max_def]
  fun_prop

@[fun_prop] theorem slots_poly : Poly slots := by unfold slots;fun_prop

@[fun_prop] theorem capacity_poly : Poly capacity := by unfold capacity;fun_prop

@[fun_prop] theorem gridTape_poly : Poly gridTape := by
  exact Poly.comp (f:=fun x : List Unit × ℕ => x.1.take x.2) (g:=fun s => (capacity s,gridCount s)) ⟨PolyProgram.listTake Automatic.enc ()⟩ (by fun_prop)

theorem tape_length (s : Setup) : (gridTape s).length = gridCount s := by
  let n := s.1.length
  let H := (integerMatrixTicks s.1).length
  let K := (rationalTicks s.2.1).length
  let d := s.2.2.length
  let L := (slots s).length
  have hL : L=n+H+K+d+1 := by simp [L,n,H,K,d,slots,Nat.add_assoc]
  have hc : (capacity s).length=L*(L*64) := by
    simp [capacity,L,List.sum_replicate,List.length_flatMap,Nat.mul_comm]
  have hprod := Nat.mul_le_mul (show n+H≤L by omega) (show n≤L by omega)
  change (List.take _ _).length=_
  rw [List.length_take,min_eq_left]
  rw [hc]
  change bits n H K d ≤ L*(L*64)
  unfold bits gridBits dualColumnBudgetBits dualHeight
  have hf : L*(L*64) = 64*(L*L) := by ring
  have hL2 : L≤L*L := by simpa using Nat.mul_le_mul_left L (show 1≤L by omega)
  rw [hf]
  apply max_le <;> omega

theorem ratio_heights (r : ℚ) (hr : 0<r) :
    (r : ℝ) ≤ (2:ℝ)^(rationalTicks r).length ∧
    1/(r : ℝ) ≤ (2:ℝ)^(rationalTicks r).length := by
  let K := (rationalTicks r).length
  have hnr : r.num.natAbs.bits.length ≤ K := by
    simp [K,rationalTicks,List.length_flatMap]; omega
  have hdr : r.den.bits.length ≤ K := by
    simp [K,rationalTicks,List.length_flatMap]; omega
  have hn := (NatBinary.le_two_pow_length r.num.natAbs).trans (Nat.pow_le_pow_right (by decide : 1≤2) hnr)
  have hd := (NatBinary.le_two_pow_length r.den).trans (Nat.pow_le_pow_right (by decide : 1≤2) hdr)
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hden : (1:ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hnum : 0 < r.num := (Rat.num_pos).mpr hr
  have hnum' : (1:ℝ) ≤ r.num := by exact_mod_cast hnum
  have hn' : (r.num : ℝ) ≤ (2:ℝ)^K := by
    have hn'' := (Nat.cast_le (α:=ℤ)).mpr hn
    simp only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs,abs_of_pos hnum] at hn''
    exact_mod_cast hn''
  have hd' : (r.den : ℝ) ≤ (2:ℝ)^K := by exact_mod_cast hd
  constructor
  · rw [Rat.cast_def]
    exact (div_le_self (by positivity) hden).trans hn'
  · rw [Rat.cast_def,one_div,inv_div]
    exact (div_le_self (by positivity) hnum').trans hd'

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end P2MDyadicModule236

/- Helper module GridError. -/
section P2MDyadicModule237

set_option autoImplicit false

set_option maxHeartbeats 800000

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

open GaussianPoissonSeries NativeDualQuotient

open scoped BigOperators

noncomputable section

theorem delta_pos (d : ℕ) : 0 < delta d := by unfold delta; positivity

theorem eps_pos (d : ℕ) : 0 < eps d := by unfold eps; positivity

theorem eps_eq (d : ℕ) : eps d = (delta d)^2/16 := by
  have he : 2*d+4=d+d+4 := by omega
  rw [eps,delta,he,pow_add,pow_add];ring

theorem eps_lt_one (d : ℕ) : eps d < 1 := by
  unfold eps
  apply (div_lt_iff₀ (by positivity)).mpr
  simpa using (one_lt_pow₀ (a:=(2 : ℝ)) (n:=2*d+4) (by norm_num) (by omega))

theorem coset_error (D M u : ℝ) (hD : 0 ≤ D) (hM : 0 < M) (hu : 0<u) (d : ℕ)
    (hd : D/M ≤ u*delta d/2) :
    Real.sqrt (4*eps d+Real.pi*(D/M)^2/(2*u^2)) ≤ delta d := by
  apply Real.sqrt_le_iff.mpr ⟨(delta_pos d).le,?_⟩
  have hsq := pow_le_pow_left₀ (div_nonneg hD hM.le) hd 2
  have hπ : Real.pi*(D/M)^2 ≤ 4*(D/M)^2 :=
    mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg _)
  have hterm : Real.pi*(D/M)^2/(2*u^2) ≤ (delta d)^2/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hπ,hsq]
  rw [eps_eq]
  nlinarith only [hterm,sq_nonneg (delta d)]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end P2MDyadicModule237

/- Helper module RectSettings. -/
section P2MDyadicModule238

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1700000

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource.Settings

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic QAlgorithms.Complexity

open NativeDualQuotient GaussianPoissonSeries RegevSearch.PhysicalGrid GaussianRandomizedRounding.Wide

open Integration9_9.TM2NativeFiniteDraw RationalGramSchmidt.Native

open scoped BigOperators

def times (x : List Unit×List Unit) := x.1.flatMap fun _ => x.2

@[fun_prop] theorem times_poly : Poly times := by unfold times;fun_prop

theorem times_len (a b : List Unit) : (times (a,b)).length=a.length*b.length := by
  simp [times,List.length_flatMap,List.sum_replicate]

@[fun_prop] theorem base_poly : Poly base := by unfold base;fun_prop

def baseSq (p : Settings) := times (base p,base p)

@[fun_prop] theorem baseSq_poly : Poly baseSq := by unfold baseSq;fun_prop

def factor (p : Settings) := times (List.replicate 8 (),baseSq p)

@[fun_prop] theorem factor_poly : Poly factor := by unfold factor;fun_prop

def tries (p : Settings) := times (List.replicate 448 (),times (factor p,baseSq p))

@[fun_prop] theorem tries_poly : Poly tries := by unfold tries;fun_prop

def accuracy (p : Settings) := times (List.replicate 32 (),times (baseSq p,tries p))

@[fun_prop] theorem accuracy_poly : Poly accuracy := by unfold accuracy;fun_prop

def modulus (p : Settings) := dyadicPower (gridTape p.1)

@[fun_prop] theorem modulus_poly : Poly modulus := by unfold modulus;fun_prop

def wide (p : Settings) : ℚ := (modulus p : ℚ)*(denominator p.1.1 : ℚ)/(2*p.1.2.1)

@[fun_prop] theorem wide_poly : Poly wide := by unfold wide;fun_prop

def pointRequest (p : Settings) : PointRequest×List Unit :=
  (((wide p*wide p,0),factor p,accuracy p++accuracy p),accuracy p)

@[fun_prop] theorem pointRequest_poly : Poly pointRequest := by unfold pointRequest;fun_prop

@[local fun_prop] theorem ratDen : Poly Rat.den := ⟨PolyProgram.ratDen⟩

def limit (p : Settings) := max (radius (pointRequest p).1)
  (denominator p.1.1 * (modulus p * ((p.1.1.length+1)*(p.1.2.1.den+1))+modulus p))

@[fun_prop] theorem limit_poly : Poly limit := by unfold limit;simp only [Nat.max_def];fun_prop

def wordTicks (p : Settings) := WordBudget.tape (p.1.1,limit p)

@[fun_prop] theorem wordTicks_poly : Poly wordTicks := by unfold wordTicks;fun_prop

theorem result_width {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (r : ℚ) (hr : 0<r)
    (d : ℕ) (p : List Unit) (hn : 0<n) :
    let v := atBasis B r d p
    let u := 1/(2*(r:ℝ))
    1 ≤ u*(modulus v:ℝ)*(originalDenominator B:ℝ) ∧
      (u*(modulus v:ℝ)*(originalDenominator B:ℝ))^2=(variance (pointRequest v).1:ℝ) ∧
      dualColumnBudget B hB ≤ (modulus v:ℝ) := by
  intro v u
  let H := (integerMatrixTicks (RationalInverse.Native.inputRows B)).length
  let K := (rationalTicks r).length
  have hg : (modulus v : ℝ)=(2:ℝ)^(bits n H K d) := by
    simp only [modulus,dyadicPower,atBasis,v,tape_length,gridCount,setup,RationalInverse.Native.inputRows,List.length_ofFn,List.length_replicate]
    push_cast
    rfl
  have hr' : 0<(r:ℝ) := by exact_mod_cast hr
  have hW := (relative B hB (r:ℝ) hr' H K d hn (RationalInverse.Native.inputRows_entry_height B) (ratio_heights r hr).1).2.2
  rw [←hg] at hW
  have hval : (wide v:ℝ)=u*(modulus v:ℝ)*(originalDenominator B:ℝ) := by
    simp only [wide,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
    change _*(originalDenominator B:ℝ)/(2*(r:ℝ))=_
    dsimp [u];ring
  have hD : 1 ≤ (originalDenominator B:ℝ) := by exact_mod_cast denominator_pos (RationalInverse.Native.inputRows B)
  have h1 : 1 ≤ u*(modulus v:ℝ)*(originalDenominator B:ℝ) := by nlinarith
  have hsq : (1:ℚ)≤wide v*wide v := by
    have h : (1:ℝ)≤((wide v*wide v:ℚ):ℝ) := by rw [Rat.cast_mul,hval];nlinarith
    exact_mod_cast h
  refine ⟨h1,?_,?_⟩
  · rw [pointRequest,variance,if_pos hsq,Rat.cast_mul,hval];ring
  · rw [hg]
    exact (dualColumnBudget_dyadic B hB H (RationalInverse.Native.inputRows_entry_height B)).trans
      (pow_le_pow_right₀ (by norm_num) (by unfold bits;exact (by omega : dualColumnBudgetBits n H≤dualColumnBudgetBits n H+(K+1)+(n+2*d+8)+(d+2)).trans (le_max_right _ _)))

theorem cutoff_fit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (hr : 0<r)
    (d : ℕ) (p : List Unit) (hn : 0<n) (R : ℝ) (hc : R ≤ (n+1:ℕ)*(r.den+1:ℕ)) :
    let v := atBasis B r d p
    radius (pointRequest v).1 ≤ limit v ∧
    (originalDenominator B:ℝ)*((modulus v:ℝ)*R+dualColumnBudget B hB) ≤ (limit v:ℝ) := by
  intro v
  have hD := (result_width B hB r hr d p hn).2.2
  let c := (n+1)*(r.den+1)
  have hc' : R ≤ (c:ℝ) := by exact_mod_cast hc
  have hh : denominator v.1.1 * (modulus v*c+modulus v) ≤ limit v := by
    have hn : v.1.1.length=n := List.length_ofFn
    unfold limit
    rw [hn]
    exact le_max_right _ _
  refine ⟨le_max_left _ _,?_⟩
  push_cast at hc
  calc _ ≤ (originalDenominator B:ℝ)*((modulus v:ℝ)*(c:ℝ)+(modulus v:ℝ)) := by gcongr
       _ ≤ _ := by exact_mod_cast hh

end InfoLossLAR.WorstCase.RectangularSource.Settings

end

end P2MDyadicModule238

/- Helper module RectPublic. -/
section P2MDyadicModule239

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent.Padding

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2PlatformSerialization NativeTicketInteger

open Integration9_9.LARPlatformEncoding (readB readB_append)

open Settings

noncomputable section

@[local fun_prop] theorem codeRat : Poly encQ := by
  have hn : Poly Rat.num := ⟨PolyProgram.ratNum⟩
  have hd : Poly Rat.den := ⟨PolyProgram.ratDen⟩
  unfold encQ;fun_prop

def pad (t : List Unit) : Str := t.map fun _ => true

def unpad (s : Str) : List Unit := s.map fun _ => ()

@[fun_prop] theorem pad_poly : Poly pad := by unfold pad;fun_prop

@[fun_prop] theorem unpad_poly : Poly unpad := by unfold unpad;fun_prop

theorem unpad_pad (t : List Unit) : unpad (pad t)=t := by
  simp only [unpad,pad,List.map_const',List.length_replicate,List.map_replicate]
  exact (List.eq_replicate_iff.mpr ⟨rfl, fun _ _ => Subsingleton.elim _ _⟩).symm

def pair (x : Str×Str) := input x.1 x.2

@[fun_prop] theorem pair_poly : Poly pair := NativeTicketInteger.input_poly

theorem split_pair (x y : Str) : split (pair (x,y))=(x,y) := split_input _ _

def aHead (s : Str) := (split s).1

def aTail (s : Str) := (split s).2

@[fun_prop] theorem aHead_poly : Poly aHead := Poly.comp (g:=split) (f:=Prod.fst) Poly.fst split_poly

@[fun_prop] theorem aTail_poly : Poly aTail := Poly.comp (g:=split) (f:=Prod.snd) Poly.snd split_poly

def ratRead (s : Str) := mkRat (readInteger s).2 (readB (readInteger s).1).2

@[fun_prop] theorem ratRead_poly : Poly ratRead := by unfold ratRead;fun_prop

theorem ratRead_code (r : ℚ) : ratRead (encQ r)=r := by
  have h := readB_append r.den ([] : Str)
  rw [List.append_nil] at h
  simp only [ratRead,encQ,readInteger_append,h,Rat.mkRat_self]

def packRequest (p : PointRequest×List Unit) := pair (encQ p.1.1.1,pair (pad p.1.2.1,pair (pad p.1.2.2,pad p.2)))

@[fun_prop] theorem packRequest_poly : Poly packRequest := by unfold packRequest;fun_prop

def request (s : Str) : PointRequest×List Unit :=
  (((ratRead (aHead s),0),unpad (aHead (aTail s)),unpad (aHead (aTail (aTail s)))),unpad (aTail (aTail (aTail s))))

@[fun_prop] theorem request_poly : Poly request := by unfold request;fun_prop

theorem request_code (p : PointRequest×List Unit) (h : p.1.1.2=0) : request (packRequest p)=p := by
  rcases p with ⟨⟨⟨x,c⟩,f,p⟩,q⟩
  change c=0 at h
  subst c
  simp only [request,packRequest,aHead,aTail,split_pair,ratRead_code,unpad_pad]

def readNat (s : Str) := (readB s).2

@[fun_prop] theorem readNat_poly : Poly readNat := by unfold readNat;fun_prop

theorem readNat_enc (x : ℕ) : readNat (encB x)=x := by
  have h := readB_append x ([] : Str)
  simpa only [List.append_nil,readNat] using congrArg Prod.snd h

def readInt (s : Str) := (readInteger s).2

@[fun_prop] theorem readInt_poly : Poly readInt := by unfold readInt;fun_prop

theorem readInt_enc (x : ℤ) : readInt (encI x)=x := by
  have h := readInteger_append x ([] : Str)
  simpa only [List.append_nil,readInt] using congrArg Prod.snd h

def readRows (s : Str) := (readMatrix s).2

@[fun_prop] theorem readRows_poly : Poly readRows := by unfold readRows;fun_prop

theorem readRows_enc (B : List (List ℤ)) : readRows (serializeMatrix B)=B := by
  have h := NativePaddedWords.readMatrix_serialized B []
  simpa only [List.append_nil,readRows] using congrArg Prod.snd h

def packControl (c : Binary.Config) := pair (serializeMatrix (Binary.matrix c),pair (pad (Binary.ticks c),pair (encB (Binary.span c),
  pair (encB (Binary.start c),pair (pad (Binary.activeTicks c),encI (Binary.offset c))))))

@[fun_prop] theorem packControl_poly : Poly packControl := by unfold packControl;fun_prop

def controller (s : Str) : Binary.Config :=
  let x := aTail s
  let y := aTail x
  let z := aTail y
  let t := aTail z
  ((readRows (aHead s),unpad (aHead x)),(readNat (aHead y),readNat (aHead z)),unpad (aHead t),readInt (aTail t))

@[fun_prop] theorem controller_poly : Poly controller := by unfold controller;fun_prop

theorem controller_code (c : Binary.Config) : controller (packControl c)=c := by
  simp only [controller,packControl,aHead,aTail,split_pair,unpad_pad,readNat_enc,readInt_enc,readRows_enc]

def word (p : Settings.Settings) := packRequest (pointRequest p)

@[fun_prop] theorem word_poly : Poly word := by unfold word;fun_prop

theorem word_eq (p : Settings.Settings) : request (word p)=pointRequest p := request_code _ rfl

def slots (p : Settings.Settings) := unpad (word p++word p++[true])

@[fun_prop] theorem slots_poly : Poly slots := by unfold slots;fun_prop

theorem slots_len (p : Settings.Settings) : (slots p).length=2*(word p).length+1 := by simp [slots,unpad];omega

def active (p : Settings.Settings) := (Nat.bits (intervalCount (pointRequest p).1)).map fun _ => ()

@[fun_prop] theorem active_poly : Poly active := by
  have hn : Poly Nat.bits := ⟨BooleanLists.packProgram.recode Nat.bits (fun _ => rfl) (fun _ => rfl)⟩
  unfold active;fun_prop

theorem active_length (p : Settings.Settings) : (active p).length=Nat.size (intervalCount (request (word p)).1) := by
  simp [active,word_eq,Nat.size_eq_bits_len]

def nativeInput (p : Settings.Settings) : Emit.U := (slots p,active p,tries p,word p)

@[fun_prop] theorem nativeInput_poly : Poly nativeInput := by unfold nativeInput;fun_prop

def ns (p : Settings.Settings) := p.1.1.map fun _ => ()

@[fun_prop] theorem ns_poly : Poly ns := by unfold ns;fun_prop

def config (a : ℕ) (p : Settings.Settings) : Binary.Config :=
  ((p.1.1,wordTicks p),((Emit.slots request request_poly a (nativeInput p)).length,
    NativeWordLayout.machineWidth CoherentFirstSuccessNative.P (pad (tries p))+2*(slots p).length+1),active p,-(radius (pointRequest p).1:ℤ))

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule239

/- Helper module RectAccuracy. -/
section P2MDyadicModule240

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource.Settings

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent GaussianRandomizedRounding.Wide.Coherent.Padding

theorem base_len (p : Settings) : (base p).length=p.1.1.length+p.2.length+4 := by simp [base,Nat.add_assoc]

theorem base_four (p : Settings) : 4≤(base p).length := by rw [base_len];omega

theorem lengths (p : Settings) :
    (factor p).length=8*(base p).length^2 ∧
    (tries p).length=448*(factor p).length*(base p).length^2 ∧
    (accuracy p).length=32*(base p).length^2*(tries p).length := by
  simp only [factor,tries,accuracy,baseSq,times_len,List.length_replicate]
  constructor
  · ring
  · constructor <;> ring

theorem real_lengths (p : Settings) :
    ((factor p).length:ℝ)=8*(base p).length^2 ∧
    ((tries p).length:ℝ)=448*(factor p).length*(base p).length^2 ∧
    ((accuracy p).length:ℝ)=32*(base p).length^2*(tries p).length := by exact_mod_cast lengths p

theorem exp_decay (x a : ℝ) (ha : 0<a) (h : a≤x+1) : Real.exp (-x)≤1/a := by
  rw [Real.exp_neg,←one_div]
  exact one_div_le_one_div_of_le ha (h.trans (Real.add_one_le_exp x))

theorem window_error (p : Settings) :
    2*Real.sqrt ((p.1.1.length:ℝ)*(6*Real.exp (-Real.pi*((pointRequest p).1.2.1.length:ℝ)^2/2)))≤
      1/((base p).length:ℝ) := by
  let L : ℝ := (base p).length
  have hL : 4≤L := by dsimp [L];exact_mod_cast base_four p
  have h := (real_lengths p).1
  have hn : (p.1.1.length:ℝ)≤L := by dsimp [L];exact_mod_cast (by rw [base_len];omega : p.1.1.length≤(base p).length)
  change 2*Real.sqrt (_*(6*Real.exp (-Real.pi*((factor p).length:ℝ)^2/2)))≤1/L
  have hx : 24*L^3 ≤ Real.pi*((factor p).length:ℝ)^2/2+1 := by
    change ((factor p).length:ℝ)=8*L^2 at h
    rw [h];have hp := Real.pi_gt_three; nlinarith [sq_nonneg (L^2),mul_nonneg (show 0≤L^3 by positivity) (show 0≤L-1 by linarith),mul_nonneg (show 0≤Real.pi-3 by linarith) (show 0≤L^4 by positivity)]
  have he := exp_decay (Real.pi*((factor p).length:ℝ)^2/2) (24*L^3) (by positivity) hx
  rw [show -Real.pi*((factor p).length:ℝ)^2/2= -(Real.pi*((factor p).length:ℝ)^2/2) by ring]
  have hlocal : (p.1.1.length:ℝ)*(6*Real.exp (-(Real.pi*((factor p).length:ℝ)^2/2)))≤(1/(2*L))^2 := by
    calc _ ≤ L*(6*(1/(24*L^3))) := by gcongr
         _ = _ := by field_simp;ring
  have hrt := Real.sqrt_le_iff.mpr ⟨(by positivity : 0≤1/(2*L)),hlocal⟩
  linarith [show 2*(1/(2*L))=1/L by ring]

theorem rejection_error (p : Settings) :
    (p.1.1.length:ℝ)*(2*Real.exp (-((tries p).length:ℝ)/(112*((factor p).length:ℝ))))≤1/(2*(base p).length) := by
  let L : ℝ := (base p).length
  have hL : 4≤L := by dsimp [L];exact_mod_cast base_four p
  obtain ⟨hf,hm,_⟩ := real_lengths p
  have hn : (p.1.1.length:ℝ)≤L := by dsimp [L];exact_mod_cast (by rw [base_len];omega : p.1.1.length≤(base p).length)
  change ((factor p).length:ℝ)=8*L^2 at hf
  have hfpos : 0<((factor p).length:ℝ) := by rw [hf];positivity
  have he : -((tries p).length:ℝ)/(112*((factor p).length:ℝ))= -(4*L^2) := by
    rw [hm];field_simp [ne_of_gt hfpos];dsimp [L];ring
  rw [he]
  calc _ ≤ L*(2*(1/(4*L^2))) := by
         gcongr
         exact exp_decay _ _ (by positivity) (by linarith)
       _ = _ := by change _=1/(2*L);field_simp;ring

theorem point_error (a : ℕ) (ha : 0<a) :
    2*Real.sqrt (1/(2:ℝ)^(a+a)) ≤ 2/a := by
  have hp := (Nat.lt_two_pow_self (n:=a)).le
  have hr : (a:ℝ)≤2^a := by exact_mod_cast hp
  have he : 1/(2:ℝ)^(a+a)=(1/(2:ℝ)^a)^2 := by rw [pow_add];ring
  rw [he,Real.sqrt_sq (by positivity)]
  exact (mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by exact_mod_cast ha) hr) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

open Polynomial in
def interpreterBudget (bound : Polynomial ℕ) : Polynomial ℕ := 180*bound*(Polynomial.X+1)

theorem gate_error (p : Settings) (bound : Polynomial ℕ) (clock : ℕ) (hc : (accuracy p).length ≤ clock) :
    180*((bound.eval clock : ℕ):ℝ)/((((interpreterBudget bound).eval clock : ℕ):ℝ)+1) ≤ 1/((accuracy p).length:ℝ) := by
  obtain ⟨hf,hm,ha⟩ := lengths p
  have hL := base_four p
  have hapos : 0<(accuracy p).length := by rw [ha,hm,hf];positivity
  have ha' : 0<((accuracy p).length:ℝ) := by exact_mod_cast hapos
  simp only [interpreterBudget,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_add,Polynomial.eval_one]
  push_cast
  rw [div_le_div_iff₀ (by positivity) ha']
  have he : ((accuracy p).length:ℝ)≤clock := by exact_mod_cast hc
  nlinarith [mul_nonneg (show 0≤((bound.eval clock : ℕ):ℝ) by positivity) (sub_nonneg.mpr he)]

end InfoLossLAR.WorstCase.RectangularSource.Settings

end

end P2MDyadicModule240

/- Helper module RectConfigure. -/
section P2MDyadicModule241

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1700000

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent GaussianRandomizedRounding.Wide.Coherent.Padding

open Integration9_9.TM2PlatformSerialization Settings

noncomputable section

@[fun_prop] theorem config_poly (a : ℕ) : Poly (config a) := by unfold config;fun_prop

def header (a : ℕ) (p : Settings.Settings) := packControl (config a p)

@[fun_prop] theorem header_poly (a : ℕ) : Poly (header a) := by unfold header;fun_prop

def plan (a : ℕ) (p : Settings.Settings) : FrontEmit.Inp := (header a p,nativeInput p,ns p)

@[fun_prop] theorem plan_poly (a : ℕ) : Poly (plan a) := by unfold plan;fun_prop

theorem frame_valid (a : ℕ) (p : Settings.Settings) :
    frame request request_poly a (slots p) (word p) (active p).length (tries p).length p.1.1.length (controller (header a p)) := by
  rw [header,controller_code]
  unfold frame
  dsimp only [config,Binary.span,Binary.start,Binary.activeTicks,Binary.matrix,Binary.offset]
  have hh := Emit.slots_length request request_poly a (nativeInput p)
  dsimp only [nativeInput] at hh
  refine ⟨hh,?_,active_length p,rfl,?_⟩
  · have he : pad (tries p)=unary (tries p).length := List.map_const' ..
    simp only [config,Binary.start,he,NativeWordLayout.machineWidth_eq]
  · simp only [config,Binary.offset,word_eq]

theorem config_matrix (a : ℕ) (p : Settings.Settings) :
    Binary.matrix (controller (header a p))=p.1.1 := by rw [header,controller_code];rfl

theorem config_ticks (a : ℕ) (p : Settings.Settings) :
    Binary.ticks (controller (header a p))=wordTicks p :=
  by
    change Binary.ticks (controller (packControl (config a p))) = wordTicks p
    calc
      _ = Binary.ticks (config a p) := congrArg Binary.ticks (controller_code (config a p))
      _ = _ := by dsimp only [Binary.ticks,config]

theorem word_large (p : Settings.Settings) : (accuracy p).length ≤ (word p).length := by
  simp only [word,packRequest,pair,NativeTicketInteger.input,pointRequest,List.length_append,pad,List.length_map];omega

theorem trial_positive (p : Settings.Settings) : 0<(tries p).length := by
  obtain ⟨hf,hm,_⟩ := lengths p
  rw [hm,hf];have h := base_four p;positivity

theorem factor_two (p : Settings.Settings) : 2≤(request (word p)).1.2.1.length := by
  rw [word_eq];change 2≤(Settings.factor p).length
  rw [(lengths p).1];have h := base_four p;nlinarith

abbrev sched (a : ℕ) := interpreterBudget (Builder.wordBound request request_poly a)

abbrev budget (a : ℕ) (p : Settings.Settings) := Emit.budget (sched a) (nativeInput p)

theorem preparation_error (a : ℕ) (p : Settings.Settings) :
    (p.1.1.length:ℝ)*((tries p).length*Builder.Trial.error request request_poly a (slots p) (word p) (active p).length (budget a p)+
      2*Real.exp (-(tries p).length/(112*((request (word p)).1.2.1.length:ℝ))))≤1/(base p).length := by
  let L : ℝ := (base p).length
  let M : ℝ := (tries p).length
  let N : ℝ := p.1.1.length
  let A : ℝ := (accuracy p).length
  let clock := 2*(slots p).length+1+(active p).length
  have hT := trial_positive p
  have hM : 0<M := by dsimp only [M];exact_mod_cast hT
  have hL : 4≤L := by dsimp only [L];exact_mod_cast base_four p
  have hN : N≤L := by dsimp only [N,L];exact_mod_cast (show p.1.1.length≤(base p).length by rw [base_len];omega)
  have hN0 : 0≤N := Nat.cast_nonneg _
  have hA : A=32*L^2*M := (real_lengths p).2.2
  have hAP : 0<A := by rw [hA];positivity
  have hnat : 0<(accuracy p).length := by exact_mod_cast (show (0:ℝ)<(accuracy p).length from hAP)
  have hclock : (accuracy p).length≤clock := by dsimp [clock];rw [slots_len];have hw:=word_large p;omega
  have hg := gate_error p (Builder.wordBound request request_poly a) clock hclock
  have hv := point_error _ hnat
  have hb : (budget a p).length=((sched a).eval clock) := List.length_replicate
  have hs : Builder.Trial.error request request_poly a (slots p) (word p) (active p).length (budget a p)≤8/A := by
    rw [Builder.Trial.error,hb,word_eq]
    change 180*(↑((Builder.wordBound request request_poly a).eval clock):ℝ)/(_+1)+
      (5/(A+1)+2*Real.sqrt (1/(2:ℝ)^(accuracy p++accuracy p).length))≤8/A
    rw [List.length_append]
    have h5 : 5/(A+1)≤5/A := div_le_div_of_nonneg_left (by norm_num) hAP (by linarith)
    change _≤1/A at hg
    change _≤2/A at hv
    linarith [show 1/A+5/A+2/A=8/A by ring]
  have hrej := rejection_error p
  rw [word_eq]
  change N*(M*Builder.Trial.error request request_poly a (slots p) (word p) (active p).length (budget a p)+
    2*Real.exp (-M/(112*((Settings.factor p).length:ℝ))))≤1/L
  have hp : N*M*(8/A)≤1/(2*L) := by
    rw [hA,←mul_div_assoc,div_le_div_iff₀] <;> try positivity
    nlinarith [mul_nonneg (show 0≤(L-N) from sub_nonneg.mpr hN) hM.le,mul_nonneg (show 0≤L^2-L*N by nlinarith [mul_nonneg (sub_nonneg.mpr hN) (by linarith : 0≤L)]) hM.le]
  rw [mul_add]
  have step1 : N*(M*Builder.Trial.error request request_poly a (slots p) (word p) (active p).length (budget a p)) ≤ 1/(2*L) := by
    calc _ ≤ N*(M*(8/A)) := by gcongr
         _ ≤ _ := by rw [←mul_assoc];exact hp
  linarith [show 1/(2*L)+1/(2*L)=1/L by ring]

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule241

/- Helper module RectJoined. -/
section P2MDyadicModule242

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Arena

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent GaussianRandomizedRounding.Wide.Coherent.Padding

open RegevLWE.GaussConv GaussianPoissonSeries NativeDualQuotient GaussianProjection CoherentComputeUncompute CoherentProjection

open FiniteGateTransport ControlledNativeGates RegevSearch.PhysicalFourier RegevSearch.StageRegisters

noncomputable section

variable (request : Str→PointRequest × List Unit) (hr : Poly request)

variable (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (hK : Nat.size (intervalCount (request word).1) ≤ K) (m n : ℕ)

variable (controls : Str→Binary.Config) (hctrl : Poly controls) (hdr : Str)

variable (cf : frame request hr a slots word K m n (controls hdr))

variable (B : Matrix (Fin n) (Fin n) ℤ) (hm : Binary.matrix (controls hdr)=RationalInverse.Native.inputRows B)

abbrev prepCircuit (b : ℕ) (budget : List Unit) := CoherentParallelTrials.circuit
    (Builder.Pipeline.circuit request hr a b slots word K budget m) n

abbrev basisSeed := (CoherentParallelTrials.coordinates (sourceWidth request hr a slots K m) n).symm
    (fun _ => Builder.Pipeline.basisInput request hr a slots word K m)

abbrev preparedVector (s : ℝ) := repeatState n (window s (radius (request word).1))

def outsideUnit {k N : ℕ} (w : Fin k ↪ Fin N) (side : OutsideBits w → ℂ) : Prop := (∑ v, ‖side v‖^2)=1

def quotientResult {N k : ℕ} {J F : Type} [Fintype J] [Fintype F] (w : Fin k ↪ Fin N)
    (A : QState N) (f : J×F ↪ Bits k) (goal : F→ℂ) (ε : ℝ) : Prop :=
  ∃ j : Hilbert J, ‖j‖=1 ∧ ∃ side : OutsideBits w→ℂ, outsideUnit w side ∧
    stateNorm (A-attach w (basisEmbedding f (fun u => j u.1*goal u.2)) side) ≤ ε

theorem run_app {n : ℕ} (c d : Layered n) (x : QState n) : runLayered (c++d) x = runLayered d (runLayered c x) := by simp only [runLayered,List.foldl_append]

attribute [local irreducible] P Q Codec.forwardProgram Codec.inverseProgram

theorem joined {M : ℕ} [NeZero M] (hB : B.det ≠ 0) (hM : 0<(M:ℝ)) (s R e : ℝ) (hs : 0<s) (hR : 0<R) (he : 0<e)
    (he' : e<1) (hn : 0<n) (hscale : (n:ℝ)*(s/Real.sqrt 2)^2 ≤ R^2)
    (hpublic : shortSmoothingFactor n e*dualColumnBudget B hB/(M:ℝ) ≤ s/Real.sqrt 2)
    (hw : 1 ≤ s/Real.sqrt 2 * (M:ℝ) * (originalDenominator B:ℝ))
    (hv : (s/Real.sqrt 2 * (M:ℝ) * (originalDenominator B:ℝ))^2=(variance (request word).1:ℝ))
    [Fintype (Residual B)] [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) M R)]
    (b : ℕ) (budget : List Unit) (ε : ℝ) (i : X request word n) (y : Y request hr a slots word K m n)
    (hsrc : ∃ ξ : EuclideanSpace ℂ (Y request hr a slots word K m n), ‖ξ‖=1 ∧
      stateNorm (runLayered (prepCircuit request hr a slots word K m n b budget) (basis (basisSeed request hr a slots word K m n))-
        basisEmbedding (rawE request hr a slots word K hK m n)
          (fun v => preparedVector request word n (s/Real.sqrt 2 * (M:ℝ) * (originalDenominator B:ℝ)) v.1*ξ v.2)) ≤ ε) :
    let src := boxE request word n
    let sp := integerSplit B hB M
    let keep := fineEmbedding (dual (IntegerBasis.inputLattice B hB)) M R
    let z := supportVals src sp keep
    let target := normalized (finiteRestrict keep (gaussianHilbertState (fineLattice (dual (IntegerBasis.inputLattice B hB)) M)
      (s/Real.sqrt 2) (by positivity) 0))
    ∀ hf : ∀ x,(Codec.input (RationalInverse.Native.inputRows B) (List.ofFn (z x))).length ≤ (ticks controls hdr).length,
    let boxfit : Fits request word n controls hdr B := fun x => hf (sourceInjection src sp keep x)
    let w := first request hr a slots word K hK m n controls hctrl hdr cf B hm i y boxfit
    let C := full request hr a slots K m n controls hctrl hdr (prepCircuit request hr a slots word K m n b budget)++
      relocateCircuit w (CoherentInjection.circuit Codec.forwardProgram Codec.inverseProgram (ticks controls hdr).length)
    quotientResult w (runLayered C (basis (frameBits (P controls hctrl) (Q controls hctrl) hdr _ (basisSeed request hr a slots word K m n))))
      ((targetInjection src sp keep).trans (nativeOut B hB (ticks controls hdr) z hf)) target.ofLp
      (ε+(2*Real.sqrt ((n:ℝ)*(6*Real.exp (-Real.pi*((request word).1.2.1.length:ℝ)^2/2)))+
          Real.sqrt (4*e+Real.pi*(dualColumnBudget B hB/(M:ℝ))^2/(2*(s/Real.sqrt 2)^2))+2*Real.sqrt ((1/4:ℝ)^n))) := by
  intro src sp keep z target hf fb w C
  let u := s/Real.sqrt 2 * (M:ℝ) * (originalDenominator B:ℝ)
  let ψ := preparedVector request word n u
  obtain ⟨ξ,hξ,hp⟩ := hsrc
  obtain ⟨junk,hj,hnear⟩ := port request hr a slots word K hK m n controls hctrl hdr cf B hm fb i y
    _ _ ψ ξ hξ ε hp
  have ht := rectangular_close B M (s/Real.sqrt 2) hM (by positivity) (request word).1 hw hv
  have hsrc' : ‖finiteEmbed (src.trans (ambientIntegerEquiv B M hM).toEmbedding) ψ -
      gaussianHilbertState (Ambient B M hM) (s/Real.sqrt 2) (by positivity) 0‖ ≤ 
      2*Real.sqrt ((n:ℝ)*(6*Real.exp (-Real.pi*((request word).1.2.1.length:ℝ)^2/2))) := ht
  obtain ⟨j,hjNorm,hlocal⟩ := rectangular_quotient B hB hM s R e _ hs hR he he' hn hscale hpublic
    src ψ hsrc' (ticks controls hdr) hf
  let initial := basisEmbedding (inBox request word n controls hdr B fb) ψ.ofLp
  let goal := basisEmbedding ((targetInjection src sp keep).trans (nativeOut B hB (ticks controls hdr) z hf)) (fun u => j u.1*target u.2)
  have heq : initial=basisEmbedding ((sourceInjection src sp keep).trans (nativeIn B (ticks controls hdr) z hf)) ψ.ofLp := by rfl
  specialize hlocal initial 0 (by rw [←heq,sub_self];exact le_of_eq (norm_zero : ‖(0 : EuclideanSpace ℂ _)‖=0))
  rw [zero_add] at hlocal
  refine ⟨j,hjNorm,junk,hj,?_⟩
  let G := CoherentInjection.circuit Codec.forwardProgram Codec.inverseProgram (ticks controls hdr).length
  let A := runLayered (full request hr a slots K m n controls hctrl hdr (prepCircuit request hr a slots word K m n b budget))
       (basis (frameBits (P controls hctrl) (Q controls hctrl) hdr _ (basisSeed request hr a slots word K m n)))
  have result := propagate w G initial goal junk hj A ε _ hnear hlocal
  dsimp only [C]
  rw [run_app]
  exact result

end

end InfoLossLAR.WorstCase.RectangularSource.Arena

end P2MDyadicModule242

/- Helper module RectSourceReady. -/
section P2MDyadicModule243

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent GaussianRandomizedRounding.Wide.Coherent.Padding

open RegevLWE.GaussConv GaussianPoissonSeries NativeDualQuotient CoherentComputeUncompute ControlledNativeGates RegevSearch.PhysicalFourier RegevSearch.StageRegisters

open Settings Arena

noncomputable section

abbrev K (p : Settings.Settings) := (active p).length

abbrev m (p : Settings.Settings) := (tries p).length

abbrev kOk (p : Settings.Settings) : Nat.size (intervalCount (request (word p)).1) ≤ K p := (active_length p).ge

abbrev srcE (a n : ℕ) (p : Settings.Settings) := rawE request request_poly a (slots p) (word p) (K p) (kOk p) (m p) n

abbrev srcB (a n : ℕ) (p : Settings.Settings) := basisSeed request request_poly a (slots p) (word p) (K p) (m p) n

abbrev srcC (a b n : ℕ) (p : Settings.Settings) := prepCircuit request request_poly a (slots p) (word p) (K p) (m p) n b (budget a p)

abbrev vec (p : Settings.Settings) (n : ℕ) (s : ℝ) := preparedVector request (word p) n s

abbrev noise (a n : ℕ) (p : Settings.Settings) := Y request request_poly a (slots p) (word p) (K p) (m p) n

def Prepared (a b : ℕ) : Prop := ∀ (p : Settings.Settings) (n : ℕ), p.1.1.length=n →
  ∀ s : ℝ, 1 ≤ s → s^2=(variance (request (word p)).1:ℝ) →
    ∃ ξ : EuclideanSpace ℂ (noise a n p), ‖ξ‖=1 ∧
      stateNorm (runLayered (srcC a b n p) (basis (srcB a n p))-
        basisEmbedding (srcE a n p) (fun v => vec p n s v.1*ξ v.2)) ≤ 1/(base p).length

theorem real_source : ∃ a b : ℕ, 0<a ∧ 0<b ∧ Prepared a b := by
  obtain ⟨a,b,ha,hb,h⟩ := exists_prepared request request_poly
  refine ⟨a,b,ha,hb,?_⟩
  intro p n hn s hs hv
  have hc : (request (word p)).1.1.2=0 := by rw [word_eq];rfl
  have hlen : 2*(word p).length+1≤(slots p).length := (slots_len p).ge
  obtain ⟨ξ,hξ,hp⟩ := h (slots p) (word p) s (budget a p) hc hlen _ (kOk p) hs hv (factor_two p) _ (Nat.ne_of_gt (trial_positive p)) n
  refine ⟨ξ,hξ,hp.trans ?_⟩
  rw [←hn]
  exact preparation_error a p

theorem controls_emit (a b : ℕ) :
    Poly (fun p : Settings.Settings => FrontEmit.stage request request_poly a b (sched a) controller controller_poly (plan a p)) :=
  Poly.comp (f:=FrontEmit.stage request request_poly a b (sched a) controller controller_poly) (g:=plan a)
    (FrontEmit.stage_poly _ _ _ _ _ _ _) (plan_poly _)

theorem basisDim (p : Settings.Settings) : (ns p).length=p.1.1.length := List.length_map _

theorem natural_modulus (p : Settings.Settings) : 0 < modulus p := Nat.pow_pos (by decide)

instance (p : Settings.Settings) : NeZero (modulus p) := ⟨Nat.ne_of_gt (natural_modulus p)⟩

theorem actualFit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (hr : 0<r) (d : ℕ) (precision : List Unit)
    (hn : 0<n) (a : ℕ) (R : ℝ) (hR : R ≤ (n+1:ℕ)*(r.den+1:ℕ))
    [Fintype (Residual B)] [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) (modulus (atBasis B r d precision)) R)] :
    let p := atBasis B r d precision
    let z := supportVals (boxE request (word p) n) (integerSplit B hB (modulus p)) (fineEmbedding _ (modulus p) R)
    ∀ u,(Codec.input (RationalInverse.Native.inputRows B) (List.ofFn (z u))).length ≤ (ticks controller (header a p)).length := by
  intro p z u
  rw [ticks,config_ticks]
  obtain ⟨hb,hc⟩ := cutoff_fit B hB r hr d precision hn R hR
  apply WordBudget.joint_fit B hB R (limit p) _ hc u
  rw [word_eq]
  exact hb

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule243

/- Helper module RectOperational. -/
section P2MDyadicModule244

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent GaussianRandomizedRounding.Wide.Coherent.Padding

open RegevLWE.GaussConv GaussianPoissonSeries NativeDualQuotient GaussianProjection CoherentProjection CoherentComputeUncompute

open FiniteGateTransport ControlledNativeGates RegevSearch.PhysicalFourier RegevSearch.StageRegisters

open Settings Arena RegevSearch.PhysicalGrid

noncomputable section

attribute [local irreducible] P Q Codec.forwardProgram Codec.inverseProgram

abbrev pWidth (a n : ℕ) (p : Settings.Settings) := W request request_poly a (slots p) (K p) (m p) n

abbrev pA (a n : ℕ) (p : Settings.Settings) := CoherentInjection.totalWidth (P controller controller_poly) (Q controller controller_poly) (before (header a p) (pWidth a n p))

abbrev pOff (a n : ℕ) (p : Settings.Settings) := (leftWord (P controller controller_poly) (Q controller controller_poly) (header a p) (pWidth a n p)).length

abbrev pTicks (a : ℕ) (p : Settings.Settings) := ticks controller (header a p)

abbrev seed (a n : ℕ) (p : Settings.Settings) := frameBits (P controller controller_poly) (Q controller controller_poly) (header a p) _ (srcB a n p)

abbrev circuit (a b n : ℕ) (p : Settings.Settings) (h : pOff a n p+QWidth (pTicks a p).length ≤ pA a n p) :=
  full request request_poly a (slots p) (K p) (m p) n controller controller_poly (header a p) (srcC a b n p)++
  relocateCircuit (Window.wires (pOff a n p) h) (CoherentInjection.circuit Codec.forwardProgram Codec.inverseProgram (pTicks a p).length)

theorem physics_pos {r : ℚ} (hr : 0<r) : 0<physics r := by
  unfold physics
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  positivity

theorem physics_width (r : ℚ) (hr : 0<r) : physics r/Real.sqrt 2=1/(2*(r:ℝ)) := by
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  unfold physics
  field_simp
  nlinarith

theorem gridMargin {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (hr : 0<r) (d : ℕ) (prec : List Unit)
    (hn : 0<n) :
    let p := atBasis B r d prec
    let u := physics r/Real.sqrt 2
    shortSmoothingFactor n (eps d)*dualColumnBudget B hB/(modulus p:ℝ) ≤ u ∧
    Real.sqrt (4*eps d+Real.pi*(dualColumnBudget B hB/(modulus p:ℝ))^2/(2*u^2)) ≤ delta d := by
  intro p u
  let H := (RationalGramSchmidt.Native.integerMatrixTicks (RationalInverse.Native.inputRows B)).length
  let K := (RationalGramSchmidt.Native.rationalTicks r).length
  have hg : (modulus p : ℝ)=(2:ℝ)^(bits n H K d) := by
    simp only [modulus,Integration9_9.TM2NativeFiniteDraw.dyadicPower,atBasis,p,tape_length,gridCount,setup,RationalInverse.Native.inputRows,List.length_ofFn,List.length_replicate]
    push_cast;rfl
  have rr : (0:ℝ)<r := by exact_mod_cast hr
  have hh := relative B hB (r:ℝ) rr H K d hn (RationalInverse.Native.inputRows_entry_height B) (ratio_heights r hr).1
  dsimp only at hh
  rw [←hg,←physics_width r hr] at hh
  have hu : 0<u := div_pos (physics_pos hr) (Real.sqrt_pos.mpr (by norm_num))
  refine ⟨hh.1,coset_error _ _ u (dualColumnBudget_pos B hB).le (by exact_mod_cast natural_modulus p) hu d hh.2.1⟩

theorem stage {a b : ℕ} (proven : Prepared a b) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (r : ℚ) (hr : 0<r) (d : ℕ) (prec : List Unit) (R : ℝ) (hR : 0<R) (hn : 0<n)
    (hscale : (n:ℝ)*(physics r/Real.sqrt 2)^2 ≤ R^2) (hcap : R ≤ (n+1:ℕ)*(r.den+1:ℕ))
    [Fintype (Residual B)] [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) (modulus (atBasis B r d prec)) R)] :
    let p := atBasis B r d prec
    let src := boxE request (word p) n
    let sp := integerSplit B hB (modulus p)
    let keep := fineEmbedding (dual (IntegerBasis.inputLattice B hB)) (modulus p) R
    let z := supportVals src sp keep
    let target := normalized (finiteRestrict keep (gaussianHilbertState (fineLattice (dual (IntegerBasis.inputLattice B hB)) (modulus p))
      (physics r/Real.sqrt 2) (div_pos (physics_pos hr) (Real.sqrt_pos.mpr (by norm_num))) 0))
    let hf := actualFit B hB r hr d prec hn a R hcap
    ∃ found : pOff a n p+QWidth (pTicks a p).length ≤ pA a n p,
      quotientResult (Window.wires (pOff a n p) found) (runLayered (circuit a b n p found) (basis (seed a n p)))
        ((targetInjection src sp keep).trans (nativeOut B hB (pTicks a p) z hf)) target.ofLp (gap p d n) := by
  intro p src sp keep z target hf
  have hlen : p.1.1.length=n := List.length_ofFn
  have fr : frame request request_poly a (slots p) (word p) (K p) (m p) n (controller (header a p)) := by
    rw [←hlen];exact frame_valid _ _
  have hm : Binary.matrix (controller (header a p))=RationalInverse.Native.inputRows B := config_matrix a p
  have hu := (result_width B hB r hr d prec hn)
  rw [←physics_width r hr] at hu
  have hvar : (physics r/Real.sqrt 2 * (modulus p:ℝ) * (originalDenominator B:ℝ))^2=(variance (request (word p)).1:ℝ) := by
    rw [word_eq];exact hu.2.1
  let i : X request (word p) n := fun _ => 0
  let y : noise a n p := fun _ => (0,(fun _ => false),fun _ => (0,0))
  have hy : 0<(modulus p:ℝ) := by exact_mod_cast natural_modulus p
  obtain ⟨hmarg,hcoset⟩ := gridMargin B hB r hr d prec hn
  have hsrc := proven p n hlen _ hu.1 hvar
  let fb : Fits request (word p) n controller (header a p) B := fun x => hf (sourceInjection src sp keep x)
  let found := fits (P controller controller_poly) (Q controller controller_poly) (header a p) (srcE a n p) (inBox request (word p) n controller (header a p) B fb)
    (saved request request_poly a (slots p) (word p) (K p) (m p) n)
    (dest request request_poly a (slots p) (word p) (K p) (kOk p) (m p) n controller (header a p) fr B hm fb) i y
  refine ⟨found,?_⟩
  have h := Arena.joined request request_poly a (slots p) (word p) (K p) (kOk p) (m p) n controller controller_poly (header a p) fr B hm
    hB hy (physics r) R (eps d) (physics_pos hr) hR (eps_pos d) (eps_lt_one d) hn hscale hmarg hu.1 hvar b (budget a p) _ i y hsrc hf
  obtain ⟨j,hj,side,hs,hnear⟩ := h
  refine ⟨j,hj,side,hs,hnear.trans ?_⟩
  have hw := window_error p
  rw [hlen] at hw
  rw [word_eq]
  unfold gap
  have he : 2/((base p).length:ℝ)=1/(base p).length + 1/(base p).length := by ring
  rw [he]
  linarith only [hw,hcoset]

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule244

/- Helper module PoolTape. -/
section P2MDyadicModule245

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1150000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime FineCodec

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

abbrev OldTable := (List Unit × List Unit) × Str

def readSlots (v : OldTable) : List Str :=
  (List.range v.1.1.length).map (fun i => (v.2.drop (i*v.1.2.length)).take v.1.2.length)

@[fun_prop] theorem readSlots_poly : Poly readSlots := by
  unfold readSlots
  apply Poly.list_map
  · change Poly (fun p : OldTable × ℕ => (p.1.2.drop (p.2*p.1.1.2.length)).take p.1.1.2.length)
    have hd := Poly.comp (f:=fun z : Str × ℕ => z.1.drop z.2)
      (g:=fun p : OldTable × ℕ => (p.1.2,p.2*p.1.1.2.length)) parser_drop_poly (by fun_prop)
    exact Poly.comp parser_take_poly (Poly.pair hd (by fun_prop))
  · exact Poly.comp (f:=fun l : List Unit => List.range l.length) (g:=fun v : OldTable => v.1.1) Poly.list_indices (by fun_prop)

def encodedPool (v : OldTable) : Str := serializeMatrix ((readSlots v).map fun r => (readVector r).2)

@[fun_prop] theorem encodedPool_poly : Poly encodedPool := by unfold encodedPool;fun_prop

def setupFromPool (v : ((List Unit × List Unit × List Unit) × (Str × Str)) × OldTable) : Config :=
  (v.1.1,(v.1.2.1,v.1.2.2,encodedPool v.2))

@[fun_prop] theorem setupFromPool_poly : Poly setupFromPool := by unfold setupFromPool;fun_prop

theorem slotCorrect {n : ℕ} (count width : List Unit) (tape : Str) (p : Fin count.length → Fin n → ℤ)
    (h : ∀ i, encVec encI (p i) <+: (tape.drop (i.val*width.length)).take width.length) :
    encodedPool ((count,width),tape) = encVec (encVec encI) p := by
  have rows : (readSlots ((count,width),tape)).map (fun r => (readVector r).2) = List.ofFn (fun i => List.ofFn (p i)) := by
    apply List.ext_getElem
    · simp [readSlots]
    · intro i hl hr
      have hi : i<count.length := by simpa using hr
      obtain ⟨tail,hey⟩ := h ⟨i,hi⟩
      simp only [readSlots,List.getElem_map,List.getElem_range,List.getElem_ofFn]
      rw [←hey,readVector_append]
  rw [encodedPool,rows]
  have hv (z : Fin n → ℤ) : serializeVector (List.ofFn z)=encVec encI z := by
    simp only [serializeVector,Integration9_9.LARPlatformEncoding.serializeBinaryWords_map,encVec]
  simp only [serializeMatrix,List.map_ofFn,Function.comp_def,hv,encVec]
  simpa only [List.map_ofFn,Function.comp_def,encVec] using Integration9_9.LARPlatformEncoding.serializeBinaryWords_map (encVec encI) (List.ofFn p)

theorem confCorrect {n : ℕ} (bt k l count width : List Unit) (R : ℚ) (prec : ℕ) (tape : Str)
    (p : Fin count.length → Fin n → ℤ)
    (h : ∀ i, encVec encI (p i) <+: (tape.drop (i.val*width.length)).take width.length) :
    setupFromPool (((bt,k,l),(encQ R,unary prec)),((count,width),tape)) = queryConfig bt k l R prec p := by
  change (_,(_,_,encodedPool ((count,width),tape)))=_
  rw [slotCorrect count width tape p h]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule245

/- Helper module RawStage. -/
section P2MDyadicModule246

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity PaddedDecoder FineCodec NativeDualQuotient IntegerBasis

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open RegevLWE.GaussConv

noncomputable section

variable {n m M : ℕ} [NeZero M]

theorem quotient_word (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (c : Config) (ticks : List Unit)
    (v : Fin n → ℤ) (hf : (Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)).length ≤ ticks.length) :
    encS (header c) ++ Codec.forward (NativePaddedWords.current (ticks,Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v))) =
    pack (fineSource B c ticks (remainderVector B v) (quotientVector B v)) := by
  rw [NativePaddedWords.current_eq ticks _ hf,Codec.forward_append,current_ofFn B hB,FineCodec.serializeMatrix_eq]
  let w := Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)
  have hl : w.length+(ticks.length-w.length)=ticks.length := by change w.length≤ticks.length at hf;omega
  simp only [fineSource,pack,lengthToken_eq,List.length_append,List.length_replicate,List.append_assoc]
  rw [show (Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)).length + (ticks.length - (Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)).length)=ticks.length from hl]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule246

/- Helper module FineSizes. -/
section P2MDyadicModule247

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1700000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineSizes

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeDualQuotient RegevSearch RegevSearch.PhysicalFourier RegevSearch.FineCodec IntegerBasis

open Integration9_9.TM2NativeAffineEmitter RegevLWE.GaussConv GaussianPoissonSeries

open TM2Boolean.PolyProgramCircuit

noncomputable section

def answerAt (w : Str) := let s := FineCodec.unpack w; serializeVector (answers ((setup s.1.1.1).1.1,s.2))

def requestAt (w : Str) := let s := FineCodec.unpack w; FineCodec.request ((setup s.1.1.1,s.1.2.1),s.2)

@[fun_prop] theorem answerAt_poly : Poly answerAt := by unfold answerAt;fun_prop

@[fun_prop] theorem requestAt_poly : Poly requestAt := by unfold requestAt;fun_prop

def AP := Integration9_9.LARCoinLayout.rawPolyProgram answerAt_poly

def RP := Integration9_9.LARCoinLayout.rawPolyProgram requestAt_poly

attribute [local irreducible] AP RP Codec.forwardProgram Codec.inverseProgram

def head (c : Config) := encS (header c)

@[fun_prop] theorem head_poly : Poly head := by unfold head;fun_prop

def workspace (v : Config×List Unit) := (head v.1).map (fun _ => ())++CoherentInjection.outputTicks Codec.forwardProgram (Public.pad v.2)

@[fun_prop] theorem workspace_poly : Poly workspace := by unfold workspace;fun_prop

theorem workspace_len (c : Config) (t : List Unit) :
    (workspace (c,t)).length=(head c).length+CoherentInjection.outputSize Codec.forwardProgram t.length := by
  rw [workspace,List.length_append,List.length_map,show Public.pad t=unary t.length from List.map_const' ..,CoherentInjection.outputTicks_length]

def k (v : Config×List Unit) := CoherentInjection.outputTicks AP (Public.pad (workspace v))

def l (v : Config×List Unit) := k v++CoherentInjection.outputTicks RP (Public.pad (workspace v))

@[fun_prop] theorem k_poly : Poly k := by unfold k;fun_prop

@[fun_prop] theorem l_poly : Poly l := by unfold l;fun_prop

theorem k_le_l (v : Config×List Unit) : (k v).length≤(l v).length := by simp [l]

theorem program_fits {f : Str→Str} (p : PolyProgram id id f) (w : Str) :
    (f w).length ≤ capacity p w.length := by
  exact (actualOutput_length_lt_capacity p w).le

variable {n M : ℕ} [NeZero M]

theorem actual_frame (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (c : Config) (t : List Unit)
    (v : Fin n → ℤ) (hf : (Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)).length ≤ t.length) :
    let old := NativePaddedWords.current (t,Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v))
    let src := fineSource B c t (remainderVector B v) (quotientVector B v)
    (FineCodec.pack src).length≤(workspace (c,t)).length ∧
    head c++CoherentClassicalOracle.paddedOutput Codec.forwardProgram old=
      NativePaddedWords.current (workspace (c,t),FineCodec.pack src) := by
  intro old src
  have ho : old.length=t.length := NativePaddedWords.current_length _ _
  have hword : head c++Codec.forward old=FineCodec.pack src := quotient_word B hB c t v hf
  have hF := program_fits Codec.forwardProgram old
  change (Codec.forward old).length≤capacity Codec.forwardProgram old.length at hF
  rw [ho] at hF
  have hlen := congrArg List.length hword
  simp only [List.length_append] at hlen
  have hfit : (FineCodec.pack src).length≤(workspace (c,t)).length := by rw [workspace_len];unfold CoherentInjection.outputSize;omega
  refine ⟨hfit,?_⟩
  rw [NativePaddedWords.current_eq _ _ hfit]
  change head c++paddedOutput Codec.forwardProgram old=_
  rw [paddedOutput_eq_append,←List.append_assoc,hword,workspace_len,ho]
  apply congrArg (List.append (FineCodec.pack src))
  apply congrArg (fun k : ℕ => List.replicate k false)
  unfold CoherentInjection.outputSize
  omega

theorem widths {m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt t : List Unit) (R : ℚ)
    (prec : ℕ) (pool : Fin m → Fin n → ℤ) (v : Fin n → ℤ)
    (hf : (Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)).length ≤ t.length) :
    let c := queryConfig bt [] [] R prec pool
    let z := quotientVector B v
    (encVec encI (FineGridDecoding.answer (2^bt.length) z)).length ≤ (k (c,t)).length ∧
    (encS (poolBDDInput B R prec pool (FineGridDecoding.input B (2^bt.length) (FineGridDecoding.residue (2^bt.length) z)))).length ≤ (l (c,t)).length := by
  intro c z
  let old := NativePaddedWords.current (t,Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v))
  let w := head c++CoherentClassicalOracle.paddedOutput Codec.forwardProgram old
  let src := fineSource B c t (remainderVector B v) z
  have h := actual_frame B hB c t v hf
  have hw : w=NativePaddedWords.current (workspace (c,t),FineCodec.pack src) := h.2
  have hl : w.length=(workspace (c,t)).length := hw ▸ NativePaddedWords.current_length _ _
  have hu : FineCodec.unpack w=src := by rw [hw,NativePaddedWords.current_eq _ _ h.1,unpack_pack]
  have hA : answerAt w=encVec encI (FineGridDecoding.answer (2^bt.length) z) := by
    rw [answerAt,hu];change serializeVector (answers ((setup (header c)).1.1,List.ofFn z))=_;rw [setup_header];apply physical_answer
  have hR : requestAt w=encS (poolBDDInput B R prec pool (FineGridDecoding.input B (2^bt.length) (FineGridDecoding.residue (2^bt.length) z))) := by
    rw [requestAt,hu];change FineCodec.request ((setup (header c),encMat encI B),List.ofFn z)=_;rw [setup_header];exact physical_request B hB bt [] [] R prec pool z
  have hp : Public.pad (workspace (c,t))=unary (workspace (c,t)).length := List.map_const' ..
  have ha := program_fits AP w
  have hr := program_fits RP w
  rw [hA,hl] at ha
  rw [hR,hl] at hr
  refine ⟨?_,?_⟩
  · rw [k,hp,CoherentInjection.outputTicks_length];exact ha
  · rw [l,List.length_append,hp,CoherentInjection.outputTicks_length];exact hr.trans (Nat.le_add_left ..)

end

end InfoLossLAR.WorstCase.RectangularSource.FineSizes

end P2MDyadicModule247

/- Helper module StageLabels. -/
section P2MDyadicModule248

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FineCodec IntegerBasis PaddedDecoder SharedPoolCoherence

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open RegevLWE.GaussConv

noncomputable section

variable {n m : ℕ}

theorem toBits_tape (w : Str) : List.ofFn (QAlgorithms.Complexity.toBits w) = w := List.ofFn_get w

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule248

/- Helper module FineReady. -/
section P2MDyadicModule249

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2200000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineSizes

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeDualQuotient RegevSearch RegevSearch.PhysicalFourier RegevSearch.FineCodec IntegerBasis

open Integration9_9.TM2NativeAffineEmitter RegevLWE.GaussConv GaussianPoissonSeries

noncomputable section

abbrev Data := ((List Unit × Str × Str) × OldTable) × List Unit

def dummy (v : Data) := setupFromPool (((v.1.1.1,[],[]),v.1.1.2),v.1.2)

def cfg (v : Data) := setupFromPool (((v.1.1.1,k (dummy v,v.2),l (dummy v,v.2)),v.1.1.2),v.1.2)

def stage (v : Data) := workspace (cfg v,v.2)

@[fun_prop] theorem dummy_poly : Poly dummy := by unfold dummy;fun_prop

@[fun_prop] theorem cfg_poly : Poly cfg := by unfold cfg;fun_prop

@[fun_prop] theorem stage_poly : Poly stage := by unfold stage;fun_prop

theorem ready {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt t count slots : List Unit) (R : ℚ) (hR : 0<R)
    (pr : ℕ) (tape : Str) (pool : Fin count.length → Fin n → ℤ)
    (hr : ∀ i,encVec encI (pool i) <+: (tape.drop (i.val*slots.length)).take slots.length)
    (cut : ℝ) (hcut : cut≤(famσ n:ℝ)/(2*(R:ℝ)))
    (fit : ∀ (res : Residual B) (p : StageI B hB bt.length cut),
      let v := (integerSplit B hB (2^bt.length)).symm (res,fineEmbedding _ (2^bt.length) cut p)
      (Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)).length≤t.length) :
    let x : Data := (((bt,encQ R,unary pr),((count,slots),tape)),t)
    let A := k (dummy x,t)
    let L := l (dummy x,t)
    let S := stage x
    cfg x=queryConfig bt A L R pr pool ∧ A.length≤L.length ∧
    (∀ res p,(FineCodec.pack (frameCode B hB bt A L S t R pr pool cut res p)).length≤S.length) ∧
    (∀ p : StageI B hB bt.length cut,(encVec encI (promisedShort B hB R hR cut hcut p).answer).length≤A.length) ∧
    (∀ p : StageI B hB bt.length cut,(encS (SharedPoolCoherence.word pr pool (promisedShort B hB R hR cut hcut p))).length≤L.length) := by
  intro x A L S
  have hd : dummy x=queryConfig bt [] [] R pr pool := confCorrect bt [] [] count slots R pr tape pool hr
  have hc : cfg x=queryConfig bt A L R pr pool := confCorrect bt A L count slots R pr tape pool hr
  refine ⟨hc,k_le_l _,?_,?_,?_⟩
  · intro res p
    let v := (integerSplit B hB (2^bt.length)).symm (res,fineEmbedding _ (2^bt.length) cut p)
    have h := (actual_frame B hB (cfg x) t v (fit res p)).1
    have ch := quotient_coordinate B hB cut p res
    change remainderVector B v=_ ∧ quotientVector B v=_ at ch
    rw [ch.1,ch.2,hc] at h
    change _≤(workspace (cfg x,t)).length
    rw [hc]
    exact h
  · intro p
    let res := (integerPointsEquiv B hB 0).1
    let v := (integerSplit B hB (2^bt.length)).symm (res,fineEmbedding _ (2^bt.length) cut p)
    have h := (widths B hB bt t R pr pool v (fit res p)).1
    have hq : quotientVector B v=shortCoordinate B hB cut p := (quotient_coordinate B hB cut p res).2
    rw [hq,←hd] at h
    exact h
  · intro p
    let res := (integerPointsEquiv B hB 0).1
    let v := (integerSplit B hB (2^bt.length)).symm (res,fineEmbedding _ (2^bt.length) cut p)
    have h := (widths B hB bt t R pr pool v (fit res p)).2
    have hq : quotientVector B v=shortCoordinate B hB cut p := (quotient_coordinate B hB cut p res).2
    rw [hq,←hd] at h
    exact h

end

end InfoLossLAR.WorstCase.RectangularSource.FineSizes

end P2MDyadicModule249

/- Helper module FineWires. -/
section P2MDyadicModule250

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1100000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

structure Plan where
  N : ℕ
  F : ℕ
  H : ℕ
  O : ℕ
  S : ℕ
  oldBound : S+O≤N
  fineBound : H+O≤F

variable (p : Plan)

def chosen (s o i : ℕ) : Bool := decide (s≤ i ∧ i<s+o)

def addr (s o h f i : ℕ) := if chosen s o i then h+(i-s) else f+i

def old : Fin p.N ↪ Fin (p.F+p.N) where
  toFun i := ⟨addr p.S p.O p.H p.F i.val,by
    have := p.fineBound
    unfold addr chosen
    split <;> simp_all <;> omega⟩
  inj' i j eq := by
    have hh:=congrArg Fin.val eq
    change addr _ _ _ _ _ = addr _ _ _ _ _ at hh
    have := p.fineBound
    simp only [addr,chosen,decide_eq_true_eq] at hh
    split at hh <;> split at hh <;> apply Fin.ext <;> omega

def front (hdr : Bits p.H) (x : Bits p.N) : Bits p.F := fun i =>
  if h : i.val<p.H then hdr ⟨i,h⟩ else if t : i.val<p.H+p.O then
    x ⟨p.S+(i.val-p.H),by have:=p.oldBound;omega⟩ else false

def back (x : Bits p.N) : Bits p.N := fun i => if chosen p.S p.O i then false else x i

def tape (hdr : Bits p.H) (x : Bits p.N) := Fin.append (front p hdr x) (back p x)

theorem selected (hdr : Bits p.H) (x : Bits p.N) :
    (wireBitsEquiv (old p) (tape p hdr x)).1=x := by
  funext i
  change tape p hdr x (old p i)=_
  by_cases pick : p.S≤ i.val ∧ i.val<p.S+p.O
  · have hb : p.H+(i.val-p.S)<p.F := by have:=p.fineBound;omega
    let j : Fin p.F := ⟨_,hb⟩
    have he : old p i=Fin.castAdd p.N j := by
      apply Fin.ext
      simp [old,addr,chosen,pick,j]
    rw [he,tape,Fin.append_left]
    simp only [front,j,dif_neg (by omega : ¬p.H+(i.val-p.S)<p.H),dif_pos (by omega : p.H+(i.val-p.S)<p.H+p.O)]
    apply congrArg x
    apply Fin.ext
    dsimp
    omega
  · have he : old p i=Fin.natAdd p.F i := by apply Fin.ext; simp [old,addr,chosen,pick]
    rw [he,tape,Fin.append_right]
    simp [back,chosen,pick]

def code (hdr : Bits p.H) : Bits p.N ↪ Bits (p.F+p.N) where
  toFun := tape p hdr
  inj' x y e := by simpa only [selected] using congrArg (fun z => (wireBitsEquiv (old p) z).1) e

theorem exterior (hdr : Bits p.H) (x y : Bits p.N) :
    (wireBitsEquiv (old p) (tape p hdr x)).2=(wireBitsEquiv (old p) (tape p hdr y)).2 := by
  funext r
  obtain ⟨r,hr⟩:=r
  change tape p hdr x r=tape p hdr y r
  induction r using Fin.addCases with
  | left i =>
    rw [tape,tape,Fin.append_left,Fin.append_left]
    unfold front
    split <;> try rfl
    split <;> try rfl
    rename_i hh
    exfalso
    apply hr
    let j : Fin p.N := ⟨p.S+(i.val-p.H),by have:=p.oldBound;omega⟩
    use j
    apply Fin.ext
    have hp : p.S≤j.val ∧ j.val<p.S+p.O := by dsimp [j];omega
    simp [old,addr,chosen,hp,j]
    omega
  | right i =>
    rw [tape,tape,Fin.append_right,Fin.append_right]
    unfold back
    split <;> try rfl
    rename_i h
    exfalso
    apply hr
    use i
    apply Fin.ext
    simp [old,addr,h]

theorem framed (hdr : Bits p.H) (v : QState p.N) :
    basisEmbedding (code p hdr) v=attach (old p) v (basis ((wireBitsEquiv (old p) (tape p hdr (0:Bits p.N))).2)) := by
  let w := old p
  let c := code p hdr
  let side := (wireBitsEquiv w (tape p hdr (0:Bits p.N))).2
  funext z
  change basisEmbedding c v z=v ((wireBitsEquiv w z).1)*basis side ((wireBitsEquiv w z).2)
  by_cases hz : (wireBitsEquiv w z).2=side
  · have he : c (wireBitsEquiv w z).1=z := (wireBitsEquiv w).injective (Prod.ext (selected _ _ _) ((exterior _ _ _ _).trans hz.symm))
    conv_lhs => rw [←he,basisEmbedding_at]
    simp only [basis,if_pos hz,mul_one]
  · have he : z∉ Set.range c := by rintro ⟨i,rfl⟩; exact hz (exterior _ _ _ _)
    simp only [basisEmbedding_outside c _ _ he,basis,if_neg hz,mul_zero]

theorem run (hdr : Bits p.H) (c : Layered p.N) (seed : Bits p.N) :
    runLayered (relocateCircuit (old p) c) (basis (tape p hdr seed)) =
    basisEmbedding (code p hdr) (runLayered c (basis seed)) := by
  have he : basisEmbedding (code p hdr) (basis seed)=basis (tape p hdr seed) := by
    funext z
    by_cases hz : z∈Set.range (code p hdr)
    · obtain ⟨i,rfl⟩:=hz
      change basisEmbedding _ _ _ = basis (code p hdr seed) _
      simp [basisEmbedding_at,basis,(code p hdr).injective.eq_iff]
    · rw [basisEmbedding_outside _ _ _ hz]
      simp [basis,show z≠tape p hdr seed from fun h => hz ⟨seed,h.symm⟩]
  rw [←he,framed,framed,run_attach]

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end P2MDyadicModule250

/- Helper module FineTransfer. -/
section P2MDyadicModule251

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1100000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open ControlledNativeGates QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport RegevSearch.PhysicalFourier

noncomputable section

variable {I : Type} [Fintype I] {Q : ℕ} (p : Plan)

def first : Fin p.F ↪ Fin (p.F+p.N) where
  toFun := Fin.castAdd p.N
  inj' _ _ h := Fin.ext (congrArg (fun t : Fin (p.F+p.N) => t.val) h)

def merge (w : Fin Q ↪ Fin p.N) (q : I ↪ Bits Q) : I×OutsideBits w ↪ Bits p.N where
  toFun t := (wireBitsEquiv w).symm (q t.1,t.2)
  inj' i j h := by
    have hh := (wireBitsEquiv w).symm.injective h
    exact Prod.ext (q.injective (congrArg Prod.fst hh)) (congrArg (fun t : Bits Q × OutsideBits w => t.2) hh)

theorem merge_eq (w : Fin Q ↪ Fin p.N) (q : I ↪ Bits Q) (v : I→ℂ) (u : OutsideBits w→ℂ) :
    basisEmbedding (merge p w q) (fun t => v t.1*u t.2)=attach w (basisEmbedding q v) u := by
  have h := Window.tensor_attach w (merge p w q) q (Function.Embedding.refl _)
    (fun i j => (wireBitsEquiv w).apply_symm_apply (q i,j)) v u
  have he : basisEmbedding (Function.Embedding.refl _) u=u := by funext z;exact basisEmbedding_at _ _ z
  rw [he] at h
  exact h

theorem first_part (hdr : Bits p.H) (x : Bits p.N) : (wireBitsEquiv (first p) (tape p hdr x)).1=front p hdr x := by
  funext i
  exact Fin.append_left _ _ i

theorem second_part (hdr : Bits p.H) (x y : Bits p.N) (h : back p x=back p y) :
    (wireBitsEquiv (first p) (tape p hdr x)).2=(wireBitsEquiv (first p) (tape p hdr y)).2 := by
  funext r
  obtain ⟨r,hr⟩:=r
  change tape p hdr x r=tape p hdr y r
  induction r using Fin.addCases with
  | left i => exact (hr ⟨i,rfl⟩).elim
  | right i => simpa only [tape,Fin.append_right] using congrFun h i

theorem handoff (w : Fin Q↪Fin p.N) (q : I↪Bits Q) (i₀ : I) (hdr : Bits p.H) (g : I→Bits p.F)
    (hf : ∀ i j,front p hdr (merge p w q (i,j))=g i)
    (hb : ∀ i j,back p (merge p w q (i,j))=back p (merge p w q (i₀,j)))
    (c : Layered p.N) (seed : Bits p.N) (v : I→ℂ) (u : OutsideBits w→ℂ) (hu : Arena.outsideUnit w u)
    (ε : ℝ) (h : stateNorm (runLayered c (basis seed)-attach w (basisEmbedding q v) u)≤ε) :
    ∃ t : OutsideBits (first p)→ℂ, Arena.outsideUnit (first p) t ∧
    stateNorm (runLayered (relocateCircuit (old p) c) (basis (tape p hdr seed))-
      attach (first p) (∑ i,v i • basis (g i)) t)≤ε := by
  let e := (merge p w q).trans (code p hdr)
  have ha (i : I) (j : OutsideBits w) : (wireBitsEquiv (first p) (e (i,j))).1=g i :=
    (first_part p hdr _).trans (hf i j)
  have hd (i : I) (j : OutsideBits w) : (wireBitsEquiv (first p) (e (i,j))).2=(wireBitsEquiv (first p) (e (i₀,j))).2 :=
    second_part p hdr _ _ (hb i j)
  let j₀ : OutsideBits w := fun _ => false
  let b : I↪Bits p.F := ⟨g,fun i l h => congrArg Prod.fst (e.injective ((wireBitsEquiv (first p)).injective
    (Prod.ext ((ha i j₀).trans (h.trans (ha l j₀).symm)) ((hd i j₀).trans (hd l j₀).symm))))⟩
  let u' : EuclideanSpace ℂ (OutsideBits w) := WithLp.toLp 2 u
  have hn : ‖u'‖=1 := by
    have hh := EuclideanSpace.norm_sq_eq u'
    change ‖u'‖^2=∑ i,‖u i‖^2 at hh
    rw [show (∑ i,‖u i‖^2)=1 from hu] at hh
    nlinarith [norm_nonneg u']
  obtain ⟨t,ht,he⟩:=Window.fixed_exterior (first p) e b i₀ ha hd v u' hn
  refine ⟨t,ht,?_⟩
  change stateNorm (_-attach (first p) (basisEmbedding b v) t)≤ε
  rw [run,←he]
  have hr := merge_eq p w q v u
  rw [←hr] at h
  have hc := basisEmbedding_error (code p hdr) (runLayered c (basis seed)) (basisEmbedding (merge p w q) (fun s => v s.1*u s.2))
  rw [basis_comp] at hc
  exact hc.le.trans h

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end P2MDyadicModule251

/- Helper module FineFields. -/
section P2MDyadicModule252

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open OAI.MetricKMedian.Binary QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport RegevSearch.PhysicalFourier

noncomputable section

variable {I : Type} [Fintype I] {Q : ℕ} (p : Plan)

section

variable (off o : ℕ) (hQ : off+Q≤p.N) (ho : o+p.O≤Q) (hS : p.S=off+o)
  (q : I↪Bits Q) (d : I→Bits p.O)
  (fixed tail : Str) (hlen : fixed.length=o)
  (ht : ∀ i,List.ofFn (q i)=fixed++List.ofFn (d i)++tail)

include ho hS hlen ht in
theorem mid_at (i : I) (j : OutsideBits (Window.wires off hQ)) (k : Fin p.O) :
    merge p (Window.wires off hQ) q (i,j) ⟨p.S+k.val,by have:=p.oldBound;omega⟩= d i k := by
  let w := Window.wires off hQ
  let v := Window.wires o ho
  let x := merge p w q (i,j)
  have h1 : (wireBitsEquiv w x).1=q i := congrArg Prod.fst ((wireBitsEquiv w).apply_symm_apply (q i,j))
  have h2 : (wireBitsEquiv v (q i)).1=d i := Window.inside o ho fixed tail hlen _ _ (ht i)
  have he : w (v k)=⟨p.S+k.val,by have:=p.oldBound;omega⟩ := by
    apply Fin.ext
    change off+(o+k.val)=p.S+k.val
    omega
  rw [←he]
  exact (congrFun h1 (v k)).trans (congrFun h2 k)

include ho hS hlen ht in
theorem spectator (i i₀ : I) (j : OutsideBits (Window.wires off hQ)) :
    back p (merge p (Window.wires off hQ) q (i,j))=back p (merge p (Window.wires off hQ) q (i₀,j)) := by
  let w := Window.wires off hQ
  let v := Window.wires o ho
  let x (l : I) := merge p w q (l,j)
  have select (l : I) : wireBitsEquiv w (x l)=(q l,j) := (wireBitsEquiv w).apply_symm_apply _
  funext k
  unfold back
  split <;> try rfl
  rename_i hno
  by_cases hp : k∈Set.range w
  · obtain ⟨s,rfl⟩:=hp
    have hs : s∉Set.range v := by
      rintro ⟨r,rfl⟩
      apply hno
      simp only [chosen,decide_eq_true_eq]
      change p.S≤off+(o+r.val) ∧ off+(o+r.val)<p.S+p.O
      omega
    let s' : {s : Fin Q // s∉Set.range v} := ⟨s,hs⟩
    have he := Window.outside o ho fixed tail hlen (q i) (q i₀) (d i) (d i₀) (ht i) (ht i₀)
    exact (congrFun (congrArg Prod.fst (select i)) s).trans ((congrFun he s').trans (congrFun (congrArg Prod.fst (select i₀)) s).symm)
  · let k' : {k : Fin p.N // k∉Set.range w} := ⟨k,hp⟩
    exact (congrFun (congrArg Prod.snd (select i)) k').trans (congrFun (congrArg Prod.snd (select i₀)) k').symm

include ho hS hlen ht in
theorem front_field (i : I) (j : OutsideBits (Window.wires off hQ)) (hdr : Bits p.H) :
    front p hdr (merge p (Window.wires off hQ) q (i,j))=
    fun k => TM2Boolean.wordExtension (List.ofFn hdr++List.ofFn (d i)) k.val := by
  funext k
  unfold front TM2Boolean.wordExtension
  split
  · rename_i hh
    rw [List.getElem?_append_left (by simpa using hh)]
    simp [List.getElem?_ofFn,hh]
  · rename_i hh
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hh)]
    simp only [List.length_ofFn,List.getElem?_ofFn]
    split
    · rename_i hi
      have hb : k.val-p.H<p.O := by omega
      simp only [hb,↓reduceDIte,Option.getD_some]
      exact mid_at p off o hQ ho hS q d fixed tail hlen ht i j ⟨_,hb⟩
    · rename_i hi
      have hb : ¬k.val-p.H<p.O := by omega
      simp [hb]

end

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end P2MDyadicModule252

/- Helper module FineHandoff. -/
section P2MDyadicModule253

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport RegevSearch.PhysicalFourier

open OAI.MetricKMedian.Binary NativeDualQuotient RegevSearch.FineCodec CoherentInjection ControlledNativeGates

noncomputable section

attribute [local irreducible] Codec.forwardProgram Codec.inverseProgram RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram

abbrev qWidth (t : List Unit) := totalWidth Codec.forwardProgram Codec.inverseProgram t.length

abbrev qOrig (t : List Unit) := originalSize Codec.forwardProgram Codec.inverseProgram t.length

abbrev qOut (t : List Unit) := outputSize Codec.forwardProgram t.length

abbrev fWidth (c : Config) (t : List Unit) := totalWidth RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram (FineSizes.workspace (c,t)).length

theorem pad_bits {f : Str→Str} (P : PolyProgram id id f) (t : ℕ) (w : Str) (hw : w.length=t) :
    List.ofFn (fun i : Fin (outputSize P t) => TM2Boolean.wordExtension (f w) i.val) = CoherentClassicalOracle.paddedOutput P w := by
  subst t
  rfl

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end P2MDyadicModule253

/- Helper module FirstTensor. -/
section P2MDyadicModule254

set_option autoImplicit false

set_option maxHeartbeats 950000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open ControlledNativeGates QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport

noncomputable section

def backIndex (p : Plan) : Fin p.N ≃ {i : Fin (p.F+p.N) // i ∉ Set.range (first p)} where
  toFun i := ⟨Fin.natAdd p.F i,by
    rintro ⟨j,h⟩
    have hh := congrArg Fin.val h
    change j.val=p.F+i.val at hh
    omega⟩
  invFun t := ⟨t.1.val-p.F,by
    have h := t.1.isLt
    have hh : p.F≤t.1.val := by
      by_contra! hl
      exact t.2 ⟨⟨t.1.val,hl⟩,Fin.ext rfl⟩
    omega⟩
  left_inv i := by apply Fin.ext;dsimp;omega
  right_inv t := by
    apply Subtype.ext;apply Fin.ext
    have h : p.F≤t.1.val := by
      by_contra! hl
      apply t.2
      exact ⟨⟨t.1.val,hl⟩,Fin.ext rfl⟩
    dsimp
    omega

def backStates (p : Plan) : Bits p.N ≃ OutsideBits (first p) := Equiv.arrowCongr (backIndex p) (Equiv.refl Bool)

theorem first_tensor (p : Plan) (v : QState p.F) (j : OutsideBits (first p)→ℂ) (hj : ∑ i,‖j i‖^2=1) :
    ∃ ξ : QState p.N, stateNorm ξ=1 ∧ attach (first p) v j=tensorState v ξ := by
  let e := backStates p
  let ξ : QState p.N := fun x => j (e x)
  refine ⟨ξ,?_,?_⟩
  · have he := e.sum_comp (fun i => ‖j i‖^2)
    have hn := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 ξ : EuclideanSpace ℂ (Bits p.N))
    change (stateNorm ξ)^2=∑ i,‖j (e i)‖^2 at hn
    rw [he,hj] at hn
    have h0 : 0 ≤ stateNorm ξ := norm_nonneg _
    nlinarith
  · funext x
    change _ * j ((wireBitsEquiv (first p) x).2) = _ * j (e (rightRegister x))
    congr 2
    funext a
    obtain ⟨i,rfl⟩ := (backIndex p).surjective a
    change x (Fin.natAdd p.F i)=x (Fin.natAdd p.F ((backIndex p).symm ((backIndex p) i)))
    rw [Equiv.symm_apply_apply]

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end P2MDyadicModule254

/- Helper module FineEmitter. -/
section P2MDyadicModule255

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWireEmit

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport FineWires RegevSearch.PhysicalFourier

noncomputable section

abbrev Spec := ((ℕ×ℕ)×Str) × (List Unit×List Unit)

abbrev H (v : Spec) := v.1.2.length

abbrev S (v : Spec) := v.1.1.1

abbrev O (v : Spec) := v.1.1.2

abbrev F (v : Spec) := v.2.1.length

abbrev N (v : Spec) := v.2.2.length

def addresses (v : Spec) := (List.range (N v)).map (fun i => addr (S v) (O v) (H v) (F v) i)

@[fun_prop] theorem addresses_poly : Poly addresses := by
  unfold addresses
  apply Poly.list_map
  · unfold addr chosen; fun_prop
  · exact Poly.comp (f:= fun l : List Unit => List.range l.length) (g:=fun v : Spec => v.2.2) Poly.list_indices (by fun_prop)

def gates (v : Spec×List (List Str)) := relocatedWordLayers (v.1.2.1++v.1.2.2,addresses v.1,v.2)

@[fun_prop] theorem gates_poly : Poly gates := by unfold gates;fun_prop

def read (v : Str×ℕ) := v.1.getD v.2 false

@[fun_prop] theorem read_poly : Poly read := Poly.list_getD_comp false Poly.fst Poly.snd

def frontBit (v : (Spec×Str)×ℕ) :=
  if v.2<H v.1.1 then read (v.1.1.1.2,v.2) else if v.2<H v.1.1+O v.1.1 then read (v.1.2,S v.1.1+(v.2-H v.1.1)) else false

def backBit (v : (Spec×Str)×ℕ) := if chosen (S v.1.1) (O v.1.1) v.2 then false else read (v.1.2,v.2)

@[fun_prop] theorem frontBit_poly : Poly frontBit := by unfold frontBit;fun_prop

@[fun_prop] theorem backBit_poly : Poly backBit := by unfold backBit chosen;fun_prop

def seed (v : Spec×Str) :=
  (List.range (F v.1)).map (fun i =>frontBit (v,i)) ++ (List.range (N v.1)).map (fun i =>backBit (v,i))

@[fun_prop] theorem seed_poly : Poly seed := by
  have ha := Poly.list_map (f:=fun (v : Spec×Str) (i : ℕ) => frontBit (v,i)) frontBit_poly (Poly.comp (f:=fun l : List Unit => List.range l.length) (g:=fun v : Spec×Str => v.1.2.1) Poly.list_indices (by fun_prop))
  have hb := Poly.list_map (f:=fun (v : Spec×Str) (i : ℕ) => backBit (v,i)) backBit_poly (Poly.comp (f:=fun l : List Unit => List.range l.length) (g:=fun v : Spec×Str => v.1.2.2) Poly.list_indices (by fun_prop))
  exact Poly.comp (f:=fun p : Str×Str => p.1++p.2) (g:=fun v : Spec×Str => ((List.range (F v.1)).map (fun i =>frontBit (v,i)),(List.range (N v.1)).map (fun i =>backBit (v,i)))) Poly.list_append (Poly.pair ha hb)

def make (v : Spec) (hs : S v+O v≤N v) (hf : H v+O v≤F v) : Plan := ⟨N v,F v,H v,O v,S v,hs,hf⟩

theorem gate_exact (v : Spec) (hs : S v+O v≤N v) (hf : H v+O v≤F v) (C : Layered (N v)) :
    gates (v,C.map (List.map encInstr))=(relocateCircuit (old (make v hs hf)) C).map (List.map encInstr) := by
  have ha : addresses v=List.ofFn (fun i => ((old (make v hs hf)) i).val) := by
    apply List.ext_getElem <;> simp [addresses,old,make]
  rw [gates,ha]
  exact relocatedWordLayers_exact _ _ _ (by simp [make])

theorem seed_exact (v : Spec) (hs : S v+O v≤N v) (hf : H v+O v≤F v) (x : Bits (N v)) :
    seed (v,List.ofFn x)=List.ofFn (tape (make v hs hf) (toBits v.1.2) x) := by
  rw [seed,tape,List.ofFn_fin_append]
  apply congrArg₂ List.append
  · apply List.ext_getElem
    · simp [make]
    · intro i h₁ h₂
      have hF : i<F v := by simpa using h₁
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,frontBit,front,make]
      by_cases hh : i<H v
      · simp [hh,read,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hh,toBits]
      · by_cases ho : i<H v+O v
        · have hi : S v+(i-H v)<N v := by omega
          simp [hh,ho,read,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi]
        · simp [hh,ho]
  · apply List.ext_getElem
    · simp [make]
    · intro i h₁ h₂
      have hi : i<N v := by simpa using h₁
      simp [backBit,back,make,read,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi]

end

end InfoLossLAR.WorstCase.RectangularSource.FineWireEmit

end P2MDyadicModule255

/- Helper module SeedWrite. -/
section P2MDyadicModule256

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.SeedWrite

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open ControlledNativeCode CoherentComputeUncompute RegevSearch.PhysicalFourier

noncomputable section

def flips {n : ℕ} (b : Bits n) := (List.finRange n).filter b

def circuit {n : ℕ} (b : Bits n) := compileReversible ((flips b).map ReversibleGate.flip)

theorem bits {n : ℕ} (zs : List (Fin n)) (hz : zs.Nodup) (b : Bits n) (i : Fin n) :
    (reversibleAction (zs.map ReversibleGate.flip) b) i=if i∈zs then !(b i) else b i := by
  induction zs generalizing b with
  | nil =>simp [reversibleAction]
  | cons a zs ih =>
    obtain ⟨ha,hn⟩:=List.nodup_cons.mp hz
    simp only [List.map_cons,reversibleAction,Equiv.trans_apply,ReversibleGate.equiv_apply,ReversibleGate.act,ih hn]
    by_cases he : i=a
    · subst i;simp [ha]
    · simp [he,Function.update_of_ne he]

theorem from_zero {n : ℕ} (b : Bits n) : runLayered (circuit b) (basis (0:Bits n))=basis b := by
  rw [circuit,CoherentXorCopy.compile_basis]
  apply congrArg basis
  funext i
  rw [bits (flips b) ((List.nodup_finRange n).filter b) (0:Bits n) i]
  cases hi : b i <;> simp [flips,hi] <;> rfl

def code (s : Str) : List GateCode := (List.range s.length).flatMap (fun i => if FineWireEmit.read (s,i) then [(3,i,0)] else [])

@[fun_prop] theorem code_poly : Poly code := by
  unfold code
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.list_indices

theorem code_exact {n : ℕ} (b : Bits n) : code (List.ofFn b)=codeList (circuit b) := by
  rw [code,List.length_ofFn,show List.range n=(List.finRange n).map Fin.val by simp,List.flatMap_map]
  have general (l : List (Fin n)) : l.flatMap (fun i => if FineWireEmit.read (List.ofFn b,i.val) then [(3,i.val,0)] else []) =
      codeList (compileReversible ((l.filter b).map ReversibleGate.flip)) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      have ha : FineWireEmit.read (List.ofFn b,a.val)=b a := by simp [FineWireEmit.read,List.getD_eq_getElem?_getD]
      cases hh : b a <;>
        simp [ha,hh,codeList,compileReversible,ReversibleGate.compile,encodeInstr] at ih ⊢ <;> exact ih
  exact general _

def flatten (v : List (List Str)) : List GateCode := v.flatten.map FiniteGateTransport.readGateCode

@[fun_prop] theorem flatten_poly : Poly flatten := by
  have hl : Poly (List.flatten : List (List Str)→List Str) := ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  unfold flatten;fun_prop

theorem flatten_exact {n : ℕ} (c : Layered n) : flatten (c.map (List.map encInstr))=codeList c := by
  simp only [flatten,codeList,List.map_flatten,List.map_map,Function.comp_def,FiniteGateTransport.readGateCode_exact]

end

end InfoLossLAR.WorstCase.RectangularSource.SeedWrite

end P2MDyadicModule256

/- Helper module BootstrapSize. -/
section P2MDyadicModule257

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 6500000

set_option maxRecDepth 12000

set_option linter.unusedVariables false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute CoherentDecoder FiniteGateTransport ControlledNativeGates

open RegevSearch RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid NativeDualQuotient IntegerBasis GaussianPoissonSeries RegevLWE.GaussConv

open SharedPoolCoherence Settings

noncomputable section

theorem bootstrapSize {n : ℕ} (a : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (hr : 0<r)
    (d : ℕ) (acc : List Unit) (cut : ℝ) (hn : 0<n) (hcap : cut ≤ (n+1:ℕ)*(r.den+1:ℕ))
    [Fintype (Residual B)] [Fintype (StageI B hB (gridTape (atBasis B r d acc).1).length cut)] :
    let p := atBasis B r d acc
    let bt := gridTape p.1
    let t := pTicks a p
    ∀ (res : Residual B) (pt : StageI B hB bt.length cut),
      let v := (integerSplit B hB (2^bt.length)).symm (res,fineEmbedding _ (2^bt.length) cut pt)
      (Codec.input (RationalInverse.Native.inputRows B) (List.ofFn v)).length ≤ t.length := by
  intro p bt t res pt
  let src := Arena.boxE Public.request (Public.word p) n
  let sp := integerSplit B hB (modulus p)
  let keep := fineEmbedding (dual (inputLattice B hB)) (modulus p) cut
  let z := targetInjection src sp keep (res,pt)
  exact actualFit B hB r hr d acc hn a cut hcap z

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule257

/- Helper module CellData. -/
section P2MDyadicModule258

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1100000

namespace InfoLossLAR.WorstCase.RectangularSource.Cell

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeDualQuotient RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid RegevSearch.FineCodec RegevSearch

open Settings Public

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2PlatformSerialization

open GaussianRandomizedRounding.Wide.Coherent (rationalCode)

noncomputable section

def nt (v : Input) := v.1.1.1.map fun _ => ()

def parameters (v : Input) : Settings.Settings := ((v.1.1.1,v.1.1.2.1.2,nt v),v.1.1.2.2.2.1)

def oldTable (v : Input) : OldTable := (v.1.2,v.2.1)

def bt (v : Input) := gridTape (parameters v).1

def ticks (a : ℕ) (v : Input) := Binary.ticks (controller (Public.header a (parameters v)))

def fields (a : ℕ) (v : Input) : FineSizes.Data :=
  (((bt v,rationalCode v.1.1.2.1.1,Public.pad v.1.1.2.2.2.2),oldTable v),ticks a v)

def answer (a : ℕ) (v : Input) := FineSizes.k (FineSizes.dummy (fields a v),ticks a v)

def query (a : ℕ) (v : Input) := FineSizes.l (FineSizes.dummy (fields a v),ticks a v)

def config (a : ℕ) (v : Input) := FineSizes.cfg (fields a v)

def fineStageTicks (a : ℕ) (v : Input) := FineSizes.stage (fields a v)

def front (a : ℕ) (v : Input) := (parameters v,config a v)

@[fun_prop] theorem nt_poly : Poly nt := by unfold nt;fun_prop

@[fun_prop] theorem parameters_poly : Poly parameters := by unfold parameters;fun_prop

@[fun_prop] theorem oldTable_poly : Poly oldTable := by unfold oldTable;fun_prop

@[fun_prop] theorem bt_poly : Poly bt := by unfold bt;fun_prop

@[fun_prop] theorem ticks_poly (a : ℕ) : Poly (ticks a) := by unfold ticks;fun_prop

@[fun_prop] theorem fields_poly (a : ℕ) : Poly (fields a) := by unfold fields;fun_prop

@[fun_prop] theorem answer_poly (a : ℕ) : Poly (answer a) := by unfold answer;fun_prop

@[fun_prop] theorem query_poly (a : ℕ) : Poly (query a) := by unfold query;fun_prop

@[fun_prop] theorem config_poly (a : ℕ) : Poly (config a) := by unfold config;fun_prop

@[fun_prop] theorem fineStageTicks_poly (a : ℕ) : Poly (fineStageTicks a) := by unfold fineStageTicks;fun_prop

@[fun_prop] theorem front_poly (a : ℕ) : Poly (front a) := by unfold front;fun_prop

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end P2MDyadicModule258

/- Helper module RectStageCode. -/
section P2MDyadicModule259

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2600000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport NativeDualQuotient Settings Arena

noncomputable section

attribute [local irreducible] P Q Codec.forwardProgram Codec.inverseProgram

def nativeGates (a b : ℕ) (p : Settings.Settings) := FrontEmit.stage request request_poly a b (sched a) controller controller_poly (plan a p)

@[fun_prop] theorem nativeGates_poly (a b : ℕ) : Poly (nativeGates a b) := controls_emit a b

def nativeArena (a : ℕ) (p : Settings.Settings) := FrontEmit.arenaSlots request request_poly a controller controller_poly (plan a p)

@[fun_prop] theorem nativeArena_poly (a : ℕ) : Poly (nativeArena a) := by unfold nativeArena;fun_prop

def rawSeed (a : ℕ) (p : Settings.Settings) := FrontEmit.initial request request_poly a (plan a p)

@[fun_prop] theorem rawSeed_poly (a : ℕ) : Poly (rawSeed a) := by unfold rawSeed;fun_prop

def nativeSeed (a : ℕ) (p : Settings.Settings) := rawSeed a p++((nativeArena a p).drop (rawSeed a p).length).map (fun _ => false)

@[fun_prop] theorem nativeSeed_poly (a : ℕ) : Poly (nativeSeed a) := by
  have hpad : Poly (fun v : Str×List Unit => v.1++(v.2.drop v.1.length).map (fun _ => false)) := by
    have hd : Poly (fun v : Str×List Unit => v.2.drop v.1.length) :=
      Poly.comp (f:=fun z : List Unit×ℕ => z.1.drop z.2) (g:=fun v : Str×List Unit => (v.2,v.1.length)) QMCNumericRuntime.parser_drop_poly (by fun_prop)
    fun_prop
  exact Poly.comp (f:=fun v : Str×List Unit => v.1++(v.2.drop v.1.length).map (fun _ => false)) (g:=fun p : Settings.Settings => (rawSeed a p,nativeArena a p))
    hpad (Poly.pair (rawSeed_poly a) (nativeArena_poly a))

theorem rawData (a n : ℕ) (p : Settings.Settings) (hn : (ns p).length=n) :
    FrontEmit.dataBits request request_poly a (plan a p)=List.ofFn (srcB a n p) := by
  subst n
  exact Emit.initial_code request request_poly a (nativeInput p) (ns p)

theorem rawGates (a b n : ℕ) (p : Settings.Settings) (hn : (ns p).length=n) :
    Emit.many request request_poly a b (sched a) (plan a p).2=(srcC a b n p).map (List.map encInstr) := by
  subst n
  exact Emit.many_code request request_poly a b (sched a) (nativeInput p) (ns p)

theorem rawExtent (a n : ℕ) (p : Settings.Settings) (hn : (ns p).length=n) :
    FrontEmit.extent request request_poly a (plan a p)=pWidth a n p := by
  exact (congrArg List.length (rawData a n p hn)).trans List.length_ofFn

theorem arenaLen (a n : ℕ) (p : Settings.Settings) (hn : (ns p).length=n) : (nativeArena a p).length=pA a n p := by
  rw [nativeArena,FrontEmit.arenaSlots_eq,rawExtent a n p hn]
  rfl

theorem seedCode (a n : ℕ) (p : Settings.Settings) (hn : (ns p).length=n) :
    nativeSeed a p=List.ofFn (seed a n p) := by
  have hu : rawSeed a p=NativeTicketInteger.input (header a p) (List.ofFn (srcB a n p)) :=
    congrArg (NativeTicketInteger.input (header a p)) (rawData a n p hn)
  rw [nativeSeed,List.map_const',List.length_drop,arenaLen a n p hn,hu]
  have hl := len (header a p) (srcB a n p)
  rw [hl]
  exact (input_tape (P controller controller_poly) (Q controller controller_poly) _ hl).symm

theorem nativeCode (a b n : ℕ) (p : Settings.Settings) (hn : (ns p).length=n)
    (fit : pOff a n p+QWidth (pTicks a p).length ≤ pA a n p) :
    nativeGates a b p=(circuit a b n p fit).map (List.map encInstr) := by
  let v:=plan a p
  have he:=rawExtent a n p hn
  have hR:=rawGates a b n p hn
  have ht:=FrontEmit.clock_eq request request_poly a v
  change FrontEmit.clock request request_poly a (plan a p)=_ at ht
  rw [he] at ht
  have hA:=arenaLen a n p hn
  have hO:=FrontEmit.quotientOff_eq request request_poly a controller controller_poly (plan a p)
  rw [he] at hO
  let ks:=(FrontEmit.dataBits request request_poly a v).map (fun _=>())
  have hk : ks.length=pWidth a n p := (List.length_map _).trans he
  have wb : FrontEmit.prepOff v+pWidth a n p≤pA a n p := bound (P controller controller_poly) (Q controller controller_poly) (header a p) (pWidth a n p)
  have htq : (pTicks a p).map (fun _ =>true)=unary (pTicks a p).length := List.map_const' ..
  change FrontEmit.stage request request_poly a b (sched a) controller controller_poly (plan a p)=_
  rw [FrontEmit.stage,FrontEmit.stageOne,FrontEmit.stageTwo,FrontEmit.stageThree,hR,ht,CoherentInjection.emitted_exact,hO]
  change (Window.emit ((nativeArena a p,FrontEmit.prepOff v),ks,(srcC a b n p).map (List.map encInstr))++
    (CoherentInjection.circuit (P controller controller_poly) (Q controller controller_poly) (before (header a p) (pWidth a n p))).map (List.map encInstr))++
    Window.emit ((nativeArena a p,pOff a n p),quotientSlots (pTicks a p),CoherentInjection.emitted Codec.forwardProgram Codec.inverseProgram ((pTicks a p).map (fun _=>true)))=_
  rw [htq,CoherentInjection.emitted_exact,
      FrontEmit.relocate_by_length (nativeArena a p) ks hA.ge hk _ wb,
      FrontEmit.relocate_by_length (nativeArena a p) (quotientSlots (pTicks a p)) hA.ge (quotientSlots_length _) _ fit]
  simp only [circuit,full,List.map_append]
  rfl

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule259

/- Helper module FineWireLengths. -/
section P2MDyadicModule260

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWireEmit

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary FineWires FiniteGateTransport RegevSearch.PhysicalFourier

noncomputable section

theorem gates_at (v : Spec) (p : Plan) (hn : N v=p.N) (hf : F v=p.F) (hh : H v=p.H) (ho : O v=p.O) (hs : S v=p.S)
    (C : Layered p.N) : gates (v,C.map (List.map encInstr))=(relocateCircuit (old p) C).map (List.map encInstr) := by
  cases p with
  | mk n f h o s b₁ b₂ =>
    dsimp only at hn hf hh ho hs
    subst n;subst f;subst h;subst o;subst s
    exact gate_exact _ _ _ _

theorem seed_at (v : Spec) (p : Plan) (hn : N v=p.N) (hf : F v=p.F) (hh : H v=p.H) (ho : O v=p.O) (hs : S v=p.S)
    (hdr : Bits p.H) (he : List.ofFn hdr=v.1.2) (x : Bits p.N) : seed (v,List.ofFn x)=List.ofFn (tape p hdr x) := by
  cases p with
  | mk n f h o s b₁ b₂ =>
    dsimp only at hn hf hh ho hs
    subst n;subst f;subst h;subst o;subst s
    have hc : hdr=toBits v.1.2 := List.ofFn_inj.mp (he.trans (toBits_tape _).symm)
    rw [hc]
    exact seed_exact _ _ _ _

end

end InfoLossLAR.WorstCase.RectangularSource.FineWireEmit

end P2MDyadicModule260

/- Helper module FrontCode. -/
section P2MDyadicModule261

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

namespace InfoLossLAR.WorstCase.RectangularSource.FrontCode

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic FiniteGateTransport

open NativeDualQuotient RegevSearch.FineCodec RegevSearch.PhysicalFourier CoherentInjection

open Settings Public

noncomputable section

attribute [local irreducible] Codec.forwardProgram Codec.inverseProgram RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram Arena.P Arena.Q

abbrev Input := Settings.Settings × Config

def ticks (a : ℕ) (p : Settings.Settings) := Binary.ticks (controller (header a p))

@[fun_prop] theorem ticks_poly (a : ℕ) : Poly (ticks a) := by unfold ticks;fun_prop

def offset (a : ℕ) (p : Settings.Settings) := FrontEmit.quotientOff request request_poly a controller controller_poly (plan a p)

@[fun_prop] theorem offset_poly (a : ℕ) : Poly (offset a) := by unfold offset;fun_prop

def spec (a : ℕ) (v : Input) : FineWireEmit.Spec :=
  let c:=v.2
  let raw:=pad (ticks a v.1)
  let orig:=(outputTicks Codec.inverseProgram (inverseWord Codec.forwardProgram raw)).length
  let O:=(outputTicks Codec.forwardProgram raw).length
  let S:=FineSizes.workspace (c,ticks a v.1)
  (((offset a v.1+orig,O),FineSizes.head c),(wholeSlots RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram (pad S),nativeArena a v.1))

section polynomials

attribute [local irreducible] ticks offset nativeArena FineSizes.workspace FineSizes.head

@[fun_prop] theorem spec_poly (a : ℕ) : Poly (spec a) := by
  unfold spec
  dsimp only
  repeat' apply Poly.pair
  all_goals fun_prop

end polynomials

theorem parts (a n : ℕ) (p : Settings.Settings) (hn : (ns p).length=n) (c : Config) :
    let s:=spec a (p,c)
    FineWireEmit.N s=pA a n p ∧ FineWireEmit.F s=FineWires.fWidth c (pTicks a p) ∧
      FineWireEmit.O s=FineWires.qOut (pTicks a p) ∧ FineWireEmit.S s=pOff a n p+FineWires.qOrig (pTicks a p) := by
  intro s
  have tp : pad (ticks a p)=unary (pTicks a p).length := List.map_const' ..
  have ts : pad (FineSizes.workspace (c,ticks a p))=unary (FineSizes.workspace (c,pTicks a p)).length := List.map_const' ..
  refine ⟨arenaLen a n p hn,?_,?_,?_⟩
  · change (wholeSlots _ _ (pad (FineSizes.workspace (c,ticks a p)))).length=_
    rw [ts,wholeSlots_length]
  · change (outputTicks _ (pad (ticks a p))).length=_
    rw [tp,outputTicks_length]
  · change offset a p+(outputTicks _ (inverseWord _ (pad (ticks a p)))).length=_
    rw [tp,inverseWord_exact,outputTicks_length,offset,FrontEmit.quotientOff_eq,rawExtent a n p hn]
    rfl

end

end InfoLossLAR.WorstCase.RectangularSource.FrontCode

end P2MDyadicModule261

/- Helper module CellFacts. -/
section P2MDyadicModule262

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

namespace InfoLossLAR.WorstCase.RectangularSource.Cell

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid RegevSearch.FineCodec RegevSearch CoherentInjection

open NativeDualQuotient IntegerBasis RectangularSource.Settings RectangularSource.Public

noncomputable section

section

variable (nt₀ copies acc oracle count width : List Unit) (B : Matrix (Fin nt₀.length) (Fin nt₀.length) ℤ)
  (R r : ℚ) (tape advice : Str)

include nt₀

theorem rect_dimension : nt (encoded nt₀ copies acc oracle count width B R r tape advice)=nt₀ := by
  apply List.ext_getElem
  · simp [nt,encoded,receipt,RationalInverse.Native.inputRows]
  · intro i _ _;exact Subsingleton.elim _ _

theorem rect_settings : parameters (encoded nt₀ copies acc oracle count width B R r tape advice)=atBasis B r nt₀.length acc := by
  change ((_,_,nt _),acc)=_
  rw [rect_dimension]
  have hh : nt₀=List.replicate nt₀.length () := List.eq_replicate_iff.mpr ⟨rfl,fun _ _=>Subsingleton.elim _ _⟩
  exact congrArg (fun v : List Unit => ((RationalInverse.Native.inputRows B,r,v),acc)) hh

theorem rect_fields (a : ℕ) :
    let v:=encoded nt₀ copies acc oracle count width B R r tape advice
    let p:=atBasis B r nt₀.length acc
    fields a v=(((gridTape p.1,encQ R,unary oracle.length),((count,width),tape)),pTicks a p) := by
  intro v p
  have hs : parameters v=p := rect_settings _ _ _ _ _ _ _ _ _ _ _
  have hq : pad oracle=unary oracle.length := List.map_const' ..
  change (((gridTape (parameters v).1,_,pad oracle),((count,width),tape)),Binary.ticks (controller (Public.header a (parameters v))))=_
  rw [hs,hq]
  rfl

end

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end P2MDyadicModule262

/- Helper module RawFrontWire. -/
section P2MDyadicModule263

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport RegevSearch.PhysicalFourier

open OAI.MetricKMedian.Binary NativeDualQuotient RegevSearch.FineCodec CoherentInjection ControlledNativeGates

noncomputable section

attribute [local irreducible] Codec.forwardProgram Codec.inverseProgram RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram

def rawPlan (F : ℕ) (c : Config) (t : List Unit) (N off : ℕ) (hQ : off+qWidth t≤N) (hF : (FineSizes.workspace (c,t)).length≤F) : Plan where
  N:=N
  F:=F
  H:=(FineSizes.head c).length
  O:=qOut t
  S:=off+qOrig t
  oldBound:=by unfold qWidth totalWidth width at hQ;unfold qOrig qOut;omega
  fineBound:=by rw [←FineSizes.workspace_len];exact hF

section
attribute [local irreducible] FineSizes.head FineSizes.workspace
theorem raw_quotient {I : Type} [Fintype I] (c : Config) (t : List Unit) (N off : ℕ) (hQ : off+qWidth t≤N) (F : ℕ) (hF : (FineSizes.workspace (c,t)).length≤F)
    (i₀ : I) (q : I ↪ Bits (qWidth t)) (src : I→Source) (words : I→Str)
    (hw : ∀ i,(words i).length=t.length)
    (hq : ∀ i,q i=finalBitsAt Codec.forwardProgram Codec.inverseProgram t.length (words i))
    (hframe : ∀ i,FineSizes.head c++CoherentClassicalOracle.paddedOutput Codec.forwardProgram (words i)=stagedWord (FineSizes.workspace (c,t)) (src i))
    (C : Layered N) (seed : Bits N) (v : I→ℂ) (u : OutsideBits (Window.wires off hQ)→ℂ)
    (hu : Arena.outsideUnit _ u) (ε : ℝ)
    (he : stateNorm (runLayered C (basis seed)-attach (Window.wires off hQ) (basisEmbedding q v) u)≤ε) :
    let p:=rawPlan F c t N off hQ hF
    ∃ side : OutsideBits (first p)→ℂ, Arena.outsideUnit (first p) side ∧
    stateNorm (runLayered (relocateCircuit (old p) C) (basis (tape p (toBits (FineSizes.head c)) seed))-
      attach (first p) (rawState F (FineSizes.workspace (c,t)) src v) side)≤ε := by
  intro p
  let H := FineSizes.head c
  let hdr : Bits p.H := toBits H
  let St := FineSizes.workspace (c,t)
  let d (i : I) : Bits p.O := fun k => TM2Boolean.wordExtension (Codec.forward (words i)) k.val
  let fixed := List.replicate (qOrig t) false
  let tail := List.replicate (forwardWork Codec.forwardProgram t.length+backwardWork Codec.forwardProgram Codec.inverseProgram t.length) false
  have ho : qOrig t+p.O≤qWidth t := by change qOrig t+qOut t≤_;unfold qWidth qOrig qOut totalWidth width;omega
  have hs : p.S=off+qOrig t := rfl
  have hl : fixed.length=qOrig t := List.length_replicate
  have ht (i : I) : List.ofFn (q i)=fixed++List.ofFn (d i)++tail := by
    rw [hq,finalBitsAt,dataBits_tape,List.ofFn_const]
    rfl
  let fine (i : I) : Bits F := fun k=> TM2Boolean.wordExtension (stagedWord St (src i)) k.val
  have ff (i : I) (j : OutsideBits (Window.wires off hQ)) : front p hdr (merge p (Window.wires off hQ) q (i,j))=fine i := by
    rw [front_field p off (qOrig t) hQ ho hs q d fixed tail hl ht i j hdr]
    have hhead : List.ofFn hdr=H := toBits_tape _
    have hseg : List.ofFn (d i)=CoherentClassicalOracle.paddedOutput Codec.forwardProgram (words i) := pad_bits _ _ _ (hw i)
    rw [hhead,hseg]
    change (fun k : Fin p.F => TM2Boolean.wordExtension (FineSizes.head c++_) k.val)=_
    rw [hframe i]
    rfl
  exact handoff p _ q i₀ hdr fine ff (fun i j=>spectator p off _ hQ ho hs q d fixed tail hl ht i i₀ j) C seed v u hu ε he
end

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end P2MDyadicModule263

/- Helper module RawFrontEmit. -/
section P2MDyadicModule264

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1700000

namespace InfoLossLAR.WorstCase.RectangularSource.RawFront

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CoherentComputeUncompute NativeDualQuotient RegevSearch.FineCodec FiniteGateTransport RegevSearch.PhysicalFourier

open Public Settings

noncomputable section

def description (a : ℕ) (v : Cell.Input) : Spec :=
  ((Cell.ticks a v, Cell.answer a v),(Cell.query a v, Cell.fineStageTicks a v), nativeArena a (Cell.parameters v))

@[fun_prop] theorem description_poly (a : ℕ) : Poly (description a) := by unfold description;fun_prop

def ports (a : ℕ) (v : FrontCode.Input×List Unit) : FineWireEmit.Spec :=
  let s:=FrontCode.spec a v.1
  (s.1,v.2,s.2.2)

@[fun_prop] theorem ports_poly (a : ℕ) : Poly (ports a) := by unfold ports;fun_prop

def write (a b : ℕ) (v : FrontCode.Input×List Unit) :=
  SeedWrite.code (FineWireEmit.seed (ports a v,nativeSeed a v.1.1)) ++
   SeedWrite.flatten (FineWireEmit.gates (ports a v,nativeGates a b v.1.1))

@[fun_prop] theorem write_poly (a b : ℕ) : Poly (write a b) := by unfold write;fun_prop

def emitter (a b : ℕ) (v : Cell.Input×List Unit) := write a b (Cell.front a v.1,v.2)

@[fun_prop] theorem emitter_poly (a b : ℕ) : Poly (emitter a b) := by unfold emitter;fun_prop

section
attribute [local irreducible] FineSizes.head FineSizes.workspace Codec.forwardProgram Codec.inverseProgram
theorem write_exact (a b n : ℕ) (p : Settings.Settings) (hn : (ns p).length=n) (c : Config)
    (wf : List Unit) (fit : pOff a n p+Arena.QWidth (pTicks a p).length≤pA a n p)
    (width : (FineSizes.workspace (c,pTicks a p)).length≤wf.length) :
    let v:=FineWires.rawPlan wf.length c (pTicks a p) (pA a n p) (pOff a n p) fit width
    let C:=relocateCircuit (FineWires.old v) (Public.circuit a b n p fit)
    let init:=FineWires.tape v (toBits (FineSizes.head c)) (Public.seed a n p)
    write a b ((p,c),wf)=codeList (SeedWrite.circuit init++C) := by
  intro v C init
  obtain ⟨n₁,_,o₁,s₁⟩:=FrontCode.parts a n p hn c
  let sp:=ports a ((p,c),wf)
  have hs: FineWireEmit.seed (sp,nativeSeed a p)=List.ofFn init := by
    rw [seedCode a n p hn]
    exact FineWireEmit.seed_at sp v n₁ rfl rfl o₁ s₁ (toBits (FineSizes.head c)) (toBits_tape (FineSizes.head c)) (Public.seed a n p)
  have hg : SeedWrite.flatten (FineWireEmit.gates (sp,nativeGates a b p))=codeList C := by
    rw [nativeCode a b n p hn fit]
    change SeedWrite.flatten (FineWireEmit.gates (sp,_))=codeList (relocateCircuit (FineWires.old v) (Public.circuit a b n p fit))
    rw [FineWireEmit.gates_at sp v n₁ rfl rfl o₁ s₁ (Public.circuit a b n p fit)]
    exact SeedWrite.flatten_exact _
  change SeedWrite.code _++_=_
  rw [hs,hg,SeedWrite.code_exact];simp [codeList]
end

end

end InfoLossLAR.WorstCase.RectangularSource.RawFront

end P2MDyadicModule264

/- Helper module RawFrontLink. -/
section P2MDyadicModule265

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity NativeDualQuotient GaussianProjection CoherentProjection CoherentComputeUncompute ControlledNativeGates

open RegevLWE.GaussConv GaussianPoissonSeries FiniteGateTransport RegevSearch.PhysicalFourier RegevSearch.StageRegisters RegevSearch.PhysicalGrid

open Settings Arena

noncomputable section

attribute [local irreducible] Codec.forwardProgram Codec.inverseProgram RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram

def rawLayer (F : ℕ) (c : RegevSearch.FineCodec.Config) (t : List Unit) (N off : ℕ)
    (fit : off+FineWires.qWidth t≤N) (width : (FineSizes.workspace (c,t)).length≤F) (C : Layered N) (seed : Bits N) :
    Layered (F+N) :=
  let v:=FineWires.rawPlan F c t N off fit width
  SeedWrite.circuit (FineWires.tape v (toBits (FineSizes.head c)) seed) ++ relocateCircuit (FineWires.old v) C

def rawReady {J I : Type} [Fintype J] [Fintype I] (F : ℕ) (c : RegevSearch.FineCodec.Config) (t : List Unit)
    (N off : ℕ) (fit : off+FineWires.qWidth t≤N) (width : (FineSizes.workspace (c,t)).length≤F)
    (C : Layered N) (seed : Bits N) (src : J×I→RegevSearch.FineCodec.Source) (tar : I→ℂ) (ε : ℝ) : Prop :=
  ∃ j : Hilbert J, ‖j‖=1 ∧ ∃ y : QState N, stateNorm y=1 ∧
    stateNorm (runLayered (rawLayer F c t N off fit width C seed) (basis (0:Bits (F+N)))-
      tensorState (FineWires.rawState F (FineSizes.workspace (c,t)) src (fun i=> j i.1*tar i.2)) y)≤ε

section
attribute [local irreducible] FineSizes.head FineSizes.workspace
theorem finishRaw {I : Type} [Fintype I] (c : RegevSearch.FineCodec.Config) (t : List Unit)
    (N off : ℕ) (found : off+FineWires.qWidth t≤N) (F : ℕ) (width : (FineSizes.workspace (c,t)).length≤F)
    (i₀ : I) (q : I ↪ Bits (FineWires.qWidth t)) (src : I→RegevSearch.FineCodec.Source) (words : I→Str)
    (hw : ∀ i,(words i).length=t.length)
    (hq : ∀ i,q i=CoherentInjection.finalBitsAt Codec.forwardProgram Codec.inverseProgram t.length (words i))
    (hframe : ∀ i,FineSizes.head c++CoherentClassicalOracle.paddedOutput Codec.forwardProgram (words i)=stagedWord (FineSizes.workspace (c,t)) (src i))
    (C : Layered N) (seed : Bits N) (v : I→ℂ) (u : OutsideBits (Window.wires off found)→ℂ)
    (hu : outsideUnit _ u) (ε : ℝ) (near : stateNorm (runLayered C (basis seed)-attach (Window.wires off found) (basisEmbedding q v) u)≤ε) :
    ∃ y : QState N, stateNorm y=1 ∧ stateNorm (runLayered (rawLayer F c t N off found width C seed) (basis 0)-
      tensorState (FineWires.rawState F (FineSizes.workspace (c,t)) src v) y)≤ε := by
  let plan := FineWires.rawPlan F c t N off found width
  let ψ:=FineWires.rawState F (FineSizes.workspace (c,t)) src v
  obtain ⟨side,hside,hstate⟩:=FineWires.raw_quotient c t N off found F width i₀ q src words hw hq hframe C seed v u hu ε near
  obtain ⟨y,hy,eq⟩:=FineWires.first_tensor plan ψ side hside
  refine ⟨y,hy,?_⟩
  have ce : runLayered (rawLayer F c t N off found width C seed) (basis 0) =
      runLayered (relocateCircuit (FineWires.old plan) C) (basis (FineWires.tape plan (toBits (FineSizes.head c)) seed)) := by
    unfold rawLayer
    simp only [runLayered,List.foldl_append]
    exact congrArg (fun v => runLayered (relocateCircuit (FineWires.old plan) C) v) (SeedWrite.from_zero _)
  exact (congrArg₂ (fun a b => stateNorm (a-b)) ce eq.symm).le.trans hstate
end

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule265

/- Helper module RawFrontStage. -/
section P2MDyadicModule266

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity NativeDualQuotient GaussianProjection CoherentProjection CoherentComputeUncompute ControlledNativeGates

open RegevLWE.GaussConv GaussianPoissonSeries FiniteGateTransport RegevSearch.PhysicalFourier RegevSearch.StageRegisters RegevSearch.PhysicalGrid

open Settings Arena

noncomputable section

attribute [local irreducible] Codec.forwardProgram Codec.inverseProgram RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram

attribute [local irreducible] FineSizes.head FineSizes.workspace P Q CoherentInjection.width

theorem prepareRaw {a b : ℕ} (proven : Prepared a b) {n m₀ : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (r : ℚ) (hr : 0<r) (d : ℕ) (prec : List Unit) (cut : ℝ) (hc : 0<cut) (hn : 0<n)
    (hscale : (n:ℝ)*(physics r/Real.sqrt 2)^2 ≤ cut^2) (hcap : cut ≤ (n+1:ℕ)*(r.den+1:ℕ))
    [Fintype (Residual B)] [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) (modulus (atBasis B r d prec)) cut)]
    (k l : List Unit) (R : ℚ) (pr : ℕ) (pool : Fin m₀→Fin n→ℤ) (F : ℕ) :
    let p := atBasis B r d prec
    let bt := gridTape p.1
    let tt := pTicks a p
    let c := queryConfig bt k l R pr pool
    let S := FineSizes.workspace (c,tt)
    let target := normalized (finiteRestrict (fineEmbedding (dual (IntegerBasis.inputLattice B hB)) (modulus p) cut)
      (gaussianHilbertState (fineLattice (dual (IntegerBasis.inputLattice B hB)) (modulus p))
      (physics r/Real.sqrt 2) (div_pos (physics_pos hr) (Real.sqrt_pos.mpr (by norm_num))) 0))
    let src (i : Residual B × StageI B hB bt.length cut) := frameCode B hB bt k l S tt R pr pool cut i.1 i.2
    ∀ width : S.length≤F, ∃ found : pOff a n p+QWidth tt.length ≤ pA a n p,
    rawReady F c tt (pA a n p) (pOff a n p) found width (circuit a b n p found) (seed a n p) src target.ofLp (gap p d n) := by
  intro p bt tt c S target src width
  let box := boxE request (word p) n
  let sp := integerSplit B hB (modulus p)
  let keep := fineEmbedding (dual (IntegerBasis.inputLattice B hB)) (modulus p) cut
  let z := supportVals box sp keep
  let hf := actualFit B hB r hr d prec hn a cut hcap
  let targetE := targetInjection box sp keep
  let q := targetE.trans (nativeOut B hB tt z hf)
  let words (i : Residual B × StageI B hB bt.length cut) := Codec.words B tt z (targetE i)
  obtain ⟨found,j,hj,side,hs,hnear⟩ := stage proven B hB r hr d prec cut hc hn hscale hcap
  refine ⟨found,j,hj,?_⟩
  let i₀ : Residual B × StageI B hB bt.length cut := ((integerPointsEquiv B hB 0).1,⟨0,by simpa [fineGridPoint] using hc⟩)
  have hw (i : Residual B × StageI B hB bt.length cut) : (words i).length=tt.length :=
    Codec.words_length B tt z (targetE i)
  have hf' (i : Residual B × StageI B hB bt.length cut) :
    FineSizes.head c++CoherentClassicalOracle.paddedOutput Codec.forwardProgram (words i)=stagedWord S (src i) := by
    let v := z (targetE i)
    have h := (FineSizes.actual_frame B hB c tt v (hf (targetE i))).2
    have hm := quotient_coordinate B hB cut i.2 i.1
    change remainderVector B v=i.1.val ∧ quotientVector B v=shortCoordinate B hB cut i.2 at hm
    rw [hm.1,hm.2] at h
    exact h
  exact finishRaw c tt (pA a n p) (pOff a n p) found F width i₀ q src words hw (fun _ => rfl) hf'
    (circuit a b n p found) (seed a n p) (fun i => j i.1*target i.2) side hs (gap p d n) hnear

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule266

/- Helper module RawFrontFacade. -/
section P2MDyadicModule267

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 3000000

set_option maxRecDepth 12000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.RawFront

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianPoissonSeries FiniteGateTransport RegevSearch RegevSearch.PhysicalGrid RegevSearch.PhysicalFourier

open SharedPoolCoherence CoherentComputeUncompute CoherentProjection NativeDualQuotient RegevLWE.GaussConv IntegerBasis

open ControlledNativeCode ControlledNativeGates Settings Public

noncomputable section

attribute [local irreducible] FineSizes.workspace FineSizes.k FineSizes.l Arena.P Arena.Q FineWires.rawState

theorem certify {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt : List Unit) (R r : ℚ) (hr : 0<r)
    (pr : ℕ) (pool : Fin m→Fin n→ℤ) (cut : ℝ) (t k l s old wf : List Unit) (ε : ℝ) (codes : List GateCode)
    [Fintype (Residual B)] [Fintype (StageI B hB bt.length cut)]
    (N : ℕ) (eq : old.length=N) (G : Layered (wf.length+N)) (gcode : codeList G=codes)
    (near :
      let u:=taper B hB bt.length (r:ℝ) cut (by exact_mod_cast hr)
      let src (z : Residual B × StageI B hB bt.length cut) := frameCode B hB bt k l s t R pr pool cut z.1 z.2
      ∃ j : Hilbert (Residual B), ‖j‖=1 ∧ ∃ side : QState N, stateNorm side=1 ∧
      stateNorm (runLayered G (basis 0)-tensorState (FineWires.rawState wf.length s src (fun z => j z.1*u z.2)) side) ≤ ε) :
    preparedState B hB bt R r hr pr pool cut ((t,k),(l,s),old) ε wf codes := by
  subst N
  exact ⟨G,gcode,near⟩

theorem _root_.solution :
    ∃ describe : Cell.Input→Spec, Poly describe ∧ ∃ emit : Cell.Input×List Unit→List GateCode, Poly emit ∧ frontContract describe emit := by
  obtain ⟨a,b,_,_,proven⟩:=real_source
  refine ⟨description a,description_poly a,emitter a b,emitter_poly a b,?_⟩
  intro nt copies acc oracle count width B hB hn R r hR hr cut hc hscale hcap hcut tape advice pool table v p bt _ _
  let n:=nt.length
  let old:OldTable:=((count,width),tape)
  let t:=pTicks a p
  let data:FineSizes.Data:=(((bt,encQ R,unary oracle.length),old),t)
  let k:=FineSizes.k (FineSizes.dummy data,t)
  let l:=FineSizes.l (FineSizes.dummy data,t)
  let c:=FineSizes.cfg data
  let s:=FineSizes.workspace (c,t)
  let N:=pA a n p
  let junk:=nativeArena a p
  have hp : Cell.parameters v=p:=Cell.rect_settings .. 
  have hd : Cell.fields a v=data:=Cell.rect_fields ..
  have ht : Cell.ticks a v=t:=congrArg (fun p => pTicks a p) hp
  have hfront : Cell.front a v=(p,c):= by
    change (Cell.parameters v,FineSizes.cfg (Cell.fields a v))=(p,c)
    rw [hp,hd]
  have hdesc : description a v=((t,k),(l,s),junk):= by
    simp only [description,Cell.answer,Cell.query,Cell.fineStageTicks,ht,hd,hp,FineSizes.stage,data,k,l,s,c,junk]
  have hdim : (ns p).length=n:=(basisDim _).trans List.length_ofFn
  have hN : junk.length=N:=arenaLen a n p hdim
  obtain ⟨conf,k_le,frame,ans,que⟩:=FineSizes.ready B hB bt t count width R hR oracle.length tape pool table cut hcut
    (bootstrapSize a B hB r hr n acc cut hn hcap)
  change c=queryConfig bt k l R oracle.length pool at conf
  let promise (z : Spec) : Prop := fits B hB bt R hR oracle.length pool cut hcut z ∧
    ∀ wf : List Unit, z.2.1.2.length ≤ wf.length →
      preparedState B hB bt R r hr oracle.length pool cut z (gap p n n) wf (emitter a b (v,wf))
  change promise (description a v)
  apply (congrArg promise hdesc).mpr
  constructor
  · dsimp only [fits]
    simpa only [k,l,data,old,c,s,FineSizes.stage] using (And.intro k_le (And.intro frame (And.intro ans que)))
  
  intro wf width_ok
  change s.length ≤ wf.length at width_ok
  have small : (n:ℝ)*(physics r/Real.sqrt 2)^2 ≤ cut^2 := by
    apply le_trans _ hscale
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ (div_pos (physics_pos hr) (Real.sqrt_pos.mpr (by norm_num))).le
    exact div_le_self (physics_pos hr).le (Real.one_le_sqrt.mpr (by norm_num))
  let good (cfg : FineCodec.Config) : Prop :=
    ∀ hw : (FineSizes.workspace (cfg,t)).length ≤ wf.length,
      ∃ found : pOff a n p+Arena.QWidth t.length ≤ N,
      let labels (z : Residual B × StageI B hB bt.length cut) := frameCode B hB bt k l (FineSizes.workspace (cfg,t)) t R oracle.length pool cut z.1 z.2
      rawReady wf.length cfg t N (pOff a n p) found hw (circuit a b n p found) (seed a n p) labels
        (taper B hB bt.length (r:ℝ) cut (by exact_mod_cast hr)).ofLp (gap p n n)
  have prod : good (queryConfig bt k l R oracle.length pool):=
    prepareRaw proven B hB r hr n acc cut hc hn small hcap k l R oracle.length pool wf.length
  have near : good c:=(congrArg good conf).mpr prod
  obtain ⟨found,hrun⟩:=near width_ok
  let G:=rawLayer wf.length c t N (pOff a n p) found width_ok (circuit a b n p found) (seed a n p)
  have gc : codeList G=emitter a b (v,wf) := by
    unfold emitter
    rw [hfront]
    dsimp only [G]
    unfold rawLayer
    exact (write_exact a b n p hdim c wf found width_ok).symm
  exact certify B hB bt R r hr oracle.length pool cut t k l s junk wf (gap p n n) _ N hN G gc hrun

end

end InfoLossLAR.WorstCase.RectangularSource.RawFront

end P2MDyadicModule267
