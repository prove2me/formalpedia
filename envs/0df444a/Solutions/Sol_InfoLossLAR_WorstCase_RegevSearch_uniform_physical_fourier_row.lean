-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.uniform_physical_fourier_row
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:14:24.362489+00:00
-- url     : https://prove2.me/submissions/9dc9d0de-c34d-405f-adfa-da7ccba1e537

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_01
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_07
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_08
import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_02
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_04
import Definitions.Def_InfoLossLAR_NativeSparsePrefix_02
import Definitions.Def_InfoLossLAR_ReciprocallyScaledGaussianSource
import Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD
import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_ReversibleStringInjection
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
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_ShorAlgorithms_QFT_BitStrings
import Mathlib
import Theorems.Thm_InfoLossLAR_WorstCase_CoherentInjection_circuit_basis_at
import Theorems.Thm_InfoLossLAR_WorstCase_RationalInverse_Native_current_correct
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_PhysicalFourier_oracle_in_serialized_order
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_PhysicalFourier_signed_qft_joint
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_compile_signed_register_readout
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_finite_grid_fourier_gaussian_event_bound
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_uniform_rectangular_gaussian_preparation
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral

set_option linter.all false

namespace AFT
end AFT

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace GridReadout
end GridReadout

namespace GridReadout.Axis
end GridReadout.Axis

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

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

namespace InfoLossLAR.WorstCase.CoherentPublicPreparation
end InfoLossLAR.WorstCase.CoherentPublicPreparation

namespace InfoLossLAR.WorstCase.CoherentRejection
end InfoLossLAR.WorstCase.CoherentRejection

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

namespace InfoLossLAR.WorstCase.FiniteGateTransport
end InfoLossLAR.WorstCase.FiniteGateTransport

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier
end InfoLossLAR.WorstCase.FiniteLatticeFourier

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

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.rationalCode
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.rationalCode

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

namespace InfoLossLAR.WorstCase.NativeDualQuotient
end InfoLossLAR.WorstCase.NativeDualQuotient

namespace InfoLossLAR.WorstCase.NativeQFTPlan
end InfoLossLAR.WorstCase.NativeQFTPlan

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile
end InfoLossLAR.WorstCase.NativeQFTPlanCompile

namespace InfoLossLAR.WorstCase.NativeTicketInteger
end InfoLossLAR.WorstCase.NativeTicketInteger

namespace InfoLossLAR.WorstCase.NativeWordCoherent
end InfoLossLAR.WorstCase.NativeWordCoherent

namespace InfoLossLAR.WorstCase.NativeWordDescription
end InfoLossLAR.WorstCase.NativeWordDescription

namespace InfoLossLAR.WorstCase.NativeWordLayout
end InfoLossLAR.WorstCase.NativeWordLayout

namespace InfoLossLAR.WorstCase.QuantumXorOracle
end InfoLossLAR.WorstCase.QuantumXorOracle

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

namespace InfoLossLAR.WorstCase.RationalInverse
end InfoLossLAR.WorstCase.RationalInverse

namespace InfoLossLAR.WorstCase.RectangularSource
end InfoLossLAR.WorstCase.RectangularSource

namespace InfoLossLAR.WorstCase.RectangularSource.Arena
end InfoLossLAR.WorstCase.RectangularSource.Arena

namespace InfoLossLAR.WorstCase.RectangularSource.Public
end InfoLossLAR.WorstCase.RectangularSource.Public

namespace InfoLossLAR.WorstCase.RectangularSource.Settings
end InfoLossLAR.WorstCase.RectangularSource.Settings

namespace InfoLossLAR.WorstCase.RegevSearch
end InfoLossLAR.WorstCase.RegevSearch

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages
end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer
end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec
end InfoLossLAR.WorstCase.RegevSearch.FineCodec

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration
end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder
end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier
end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid
end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

namespace InfoLossLAR.WorstCase.RegevSearch.StageRegisters
end InfoLossLAR.WorstCase.RegevSearch.StageRegisters

namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch

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

namespace Integration9_9.LARPlatformEncoding.readBinaryList_append_mapped
end Integration9_9.LARPlatformEncoding.readBinaryList_append_mapped

namespace Integration9_9.LARPlatformEncoding.readS
end Integration9_9.LARPlatformEncoding.readS

namespace Integration9_9.LARPlatformEncoding.readS_rest_length
end Integration9_9.LARPlatformEncoding.readS_rest_length

namespace Integration9_9.LARPlatformEncoding.serializeBinaryWords
end Integration9_9.LARPlatformEncoding.serializeBinaryWords

namespace Integration9_9.LARRankOneMachine
end Integration9_9.LARRankOneMachine

namespace Integration9_9.LoadedBatch.PostComposition
end Integration9_9.LoadedBatch.PostComposition

namespace Integration9_9.TM2NativeAffineEmitter
end Integration9_9.TM2NativeAffineEmitter

namespace Integration9_9.TM2NativeAffineEncoding
end Integration9_9.TM2NativeAffineEncoding

namespace Integration9_9.TM2NativeBodyKernel
end Integration9_9.TM2NativeBodyKernel

namespace Integration9_9.TM2NativeBodyKernel.emodNatural_eq
end Integration9_9.TM2NativeBodyKernel.emodNatural_eq

namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength

namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization

namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget

namespace Integration9_9.TM2StockLists
end Integration9_9.TM2StockLists

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

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

/- Helper module Solutions.RegevBridgeInverseCircuit. -/
section P2MDyadicModule0

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

end P2MDyadicModule0

/- Helper module Solutions.RegevBridgeCoherentComputeUncompute. -/
section P2MDyadicModule1

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

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeCoherentBasisEmbedding. -/
section P2MDyadicModule2

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

@[simp] theorem wireBitsEquiv_fst {k n : ℕ} (w : Fin k ↪ Fin n) (y : Bits n) :
    (wireBitsEquiv w y).1=y ∘ w := rfl

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeToffoli. -/
section P2MDyadicModule4

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

end P2MDyadicModule4

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule5

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

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeInverseUniform. -/
section P2MDyadicModule6

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

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
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

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeReversibleUniform. -/
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

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule9

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

end P2MDyadicModule9

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule10

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

private theorem leftLayer_tensor {n m : ℕ} (layer : List (Instr n)) (first : QState n) (second : QState m) :
    runLayer (layer.map leftInstruction) (tensorState first second)=tensorState (runLayer layer first) second := by
  induction layer generalizing first with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [leftInstruction_tensor]
    exact ih (gate.apply first)

theorem leftCircuit_tensor {n m : ℕ} (circuit : Layered n) (first : QState n) (second : QState m) :
    runLayered (leftCircuit circuit) (tensorState first second)=tensorState (runLayered circuit first) second := by
  induction circuit generalizing first with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [leftCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [leftLayer_tensor]
    exact ih (runLayer layer first)

end InfoLossLAR.WorstCase

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeCircuitRelocation. -/
section P2MDyadicModule11

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

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeInitializedRelocation. -/
section P2MDyadicModule12

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

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgeCircuitInitializedEmbedding. -/
section P2MDyadicModule13

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

def initializedWireEmbedding {k n : ℕ} (w : Fin k ↪ Fin n) (outside : OutsideBits w) : Bits k ↪ Bits n where
  toFun x := (wireBitsEquiv w).symm (x,outside)
  inj' := by intro x y he;exact congrArg Prod.fst ((wireBitsEquiv w).symm.injective he)

theorem initializedWires_eq_embedding {k n : ℕ} (w : Fin k ↪ Fin n)
    (outside : OutsideBits w) (ψ : QState k) :
    initializedWires w outside ψ=basisEmbedding (initializedWireEmbedding w outside) ψ := by
  classical
  funext x
  obtain ⟨p,rfl⟩ := (wireBitsEquiv w).symm.surjective x
  by_cases h : p.2=outside
  · rcases p with ⟨bits,other⟩
    dsimp at h
    subst other
    change initializedWires w outside ψ _=basisEmbedding (initializedWireEmbedding w outside) ψ (initializedWireEmbedding w outside bits)
    rw [basisEmbedding_at]
    simp [initializedWires,unsplitState,basis]
  · have hn : (wireBitsEquiv w).symm p∉Set.range (initializedWireEmbedding w outside) := by
      rintro ⟨y,hy⟩
      have hh: (y,outside)=p := (wireBitsEquiv w).symm.injective hy
      exact h (congrArg Prod.snd hh).symm
    rw [basisEmbedding_outside _ _ _ hn]
    simp [initializedWires,unsplitState,basis,h]

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

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeCircuitRelocationBasis. -/
section P2MDyadicModule14

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

end InfoLossLAR.WorstCase.FiniteGateTransport

end

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeFiniteGateNativeAlgebra. -/
section P2MDyadicModule15

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

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeFiniteGateNativeBounds. -/
section P2MDyadicModule16

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

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeFiniteGateNativeMatrix. -/
section P2MDyadicModule17

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

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeFiniteGateNativeMatrixBounds. -/
section P2MDyadicModule18

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

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeFiniteGateNativeEnumeration. -/
section P2MDyadicModule19

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

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeFiniteGateNativeGates. -/
section P2MDyadicModule20

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

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeFiniteGateNativeResourceBounds. -/
section P2MDyadicModule21

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

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeFiniteGateNativeWord. -/
section P2MDyadicModule22

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

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeFiniteGateNativeBounded. -/
section P2MDyadicModule23

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

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeFiniteGateNativeWordPoly. -/
section P2MDyadicModule24

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

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeFiniteGateNativePredicate. -/
section P2MDyadicModule25

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

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeFiniteGateNativeCompiler. -/
section P2MDyadicModule26

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

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeFiniteGateNativeGuarantee. -/
section P2MDyadicModule27

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

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeNativePhaseTaylor. -/
section P2MDyadicModule28

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

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeNativePhaseGates. -/
section P2MDyadicModule29

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

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeControlledNativeCode. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledNativeCode

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def localTable : List GateCode := alphabet.map (fun letter => encodeInstr letter.toInstr)

def localCode (code : ℕ) : GateCode := localTable[code]?.getD (0,0,0)

theorem localCode_eq (code : ℕ) :
    localCode code=encodeInstr (FiniteGateNativeEnumeration.letterOfCode code).toInstr := by
  unfold localCode localTable FiniteGateNativeEnumeration.letterOfCode
  rw [List.getElem?_map]
  cases alphabet[code]? <;> rfl

@[fun_prop] theorem localCode_poly : Poly localCode := by
  exact Poly.list_getD_comp (0,0,0) (Automatic.Poly.const localTable) Poly.identity

abbrev Layout := ℕ×ℕ×ℕ

def address (layout : Layout) (wire : ℕ) : ℕ :=
  if wire=0 then layout.1 else if wire=1 then layout.2.1 else layout.2.2

def relocateCode (layout : Layout) (gate : GateCode) : GateCode :=
  (gate.1,address layout gate.2.1,if gate.1=4 then address layout gate.2.2 else 0)

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

end InfoLossLAR.WorstCase.ControlledNativeCode

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeBooleanUniform. -/
section P2MDyadicModule31

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

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule32

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

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule33

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

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule34

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

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule35

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

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule36

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

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeBooleanSize. -/
section P2MDyadicModule37

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

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule38

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

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeBooleanRPN. -/
section P2MDyadicModule39

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

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeBooleanRPNRun. -/
section P2MDyadicModule40

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
  exact step_poly.program.listFold (0,0) (20*(2*X+4)^2) (by
    intro tokens s pre suf he
    simp only [eval_mul, eval_ofNat, eval_pow, eval_add, eval_X]
    change (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2
    exact run_partial_bound tokens s pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeBooleanCodePoly. -/
section P2MDyadicModule41

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

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeTM2CodeFamily. -/
section P2MDyadicModule42

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

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeTM2CodeTransition. -/
section P2MDyadicModule43

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

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeTM2CodeEnumeration. -/
section P2MDyadicModule44

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

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule45

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

end P2MDyadicModule45

/- Helper module Solutions.RegevBridgeTM2Size. -/
section P2MDyadicModule46

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

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule47

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

end P2MDyadicModule47

/- Helper module Solutions.RegevBridgeTM2CodeRegisters. -/
section P2MDyadicModule48

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

end P2MDyadicModule48

/- Helper module Solutions.RegevBridgeBooleanRPNBounds. -/
section P2MDyadicModule49

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

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeTM2CodeStep. -/
section P2MDyadicModule50

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

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeTM2CodeLoop. -/
section P2MDyadicModule51

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

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule52

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

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeTM2CodeGenerate. -/
section P2MDyadicModule53

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

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeBooleanNodeSerialization. -/
section P2MDyadicModule54

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

end P2MDyadicModule54

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule55

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

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule56

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

end P2MDyadicModule56

/- Helper module Solutions.RegevBridgeTM2CodeDescription. -/
section P2MDyadicModule57

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

end P2MDyadicModule57

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule58

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

end P2MDyadicModule58

/- Helper module Solutions.RegevBridgeTM2PolyUniform. -/
section P2MDyadicModule59

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

end P2MDyadicModule59

/- Helper module Solutions.AdvantageBridgeQueryQuantum. -/
section P2MDyadicModule60

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

end P2MDyadicModule60

/- Helper module Solutions.AdvantageBridgeQueryMetadata. -/
section P2MDyadicModule61

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

end P2MDyadicModule61

/- Helper module Solutions.RegevBridgeTM2MultiOutput. -/
section P2MDyadicModule62

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

end P2MDyadicModule62

/- Helper module Solutions.RegevBridgeNativeWordLayout. -/
section P2MDyadicModule63

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

/-- Exact width of the entire generated reversible machine, including its
old input, all work/output wires, and the reserved guard wire. -/
def machineWidth (word : Str) : ℕ :=
  word.length+(generate P.machine.code P.machine.input P.machine.main P.machine.initial (request P word)).2.2.2.length+1

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

attribute [local irreducible] machineWidth

end InfoLossLAR.WorstCase.NativeWordLayout

end

end P2MDyadicModule63

/- Helper module Solutions.RegevBridgeNativeWordCoherentCompute. -/
section P2MDyadicModule64

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

end P2MDyadicModule64

/- Helper module Solutions.RegevBridgeNativeWordLift. -/
section P2MDyadicModule65

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

end P2MDyadicModule65

/- Helper module Solutions.RegevBridgeNativeWordSerializer. -/
section P2MDyadicModule66

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

variable (words : Str → List ℕ) (hw : Poly words) (p q : Polynomial ℕ)

end InfoLossLAR.WorstCase.NativeWordDescription

end

end P2MDyadicModule66

/- Helper module Solutions.RegevBridgeCircuitRelocationNative. -/
section P2MDyadicModule67

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

end P2MDyadicModule67

/- Helper module Solutions.RegevBridgeCircuitRelocationWords. -/
section P2MDyadicModule68

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

end P2MDyadicModule68

/- Helper module Solutions.RegevBridgeGaussianPoissonSeries. -/
section P2MDyadicModule69

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

end P2MDyadicModule69

/- Helper module Solutions.RegevBridgeLatticeGaussianSummable. -/
section P2MDyadicModule70

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

end P2MDyadicModule70

/- Helper module Solutions.RegevBridgeLatticeGaussianCosetSummable. -/
section P2MDyadicModule71

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

end P2MDyadicModule71

/- Helper module Solutions.RegevBridgeGaussianLatticeTransport. -/
section P2MDyadicModule72

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- The image parametrization also preserves the literal lattice variable. -/
def latticeEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    lattice ≃ₗ[ℤ] imageLattice lattice transform :=
  ZLattice.comap_equiv ℝ lattice transform.symm.toLinearEquiv

/-- Exact primal-coset reindexing, before any Gaussian approximation. -/
theorem rhoCoset_image (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (width : ℝ) (shift : Space (dimension := dimension)) :
    rhoCoset width (imageLattice lattice transform) (transform shift) =
      ∑' value : lattice, rho width (transform ((value : Space (dimension := dimension)) + shift)) := by
  unfold rhoCoset
  have reindex := (latticeEquiv lattice transform).toEquiv.tsum_eq
    (fun value : imageLattice lattice transform =>
      rho width ((value : Space (dimension := dimension)) + transform shift))
  change (∑' value : lattice, rho width
    (transform (value : Space (dimension := dimension)) + transform shift)) = _ at reindex
  simpa only [map_add] using reindex.symm

end

end InfoLossLAR.WorstCase.GaussianLatticeTransport

end P2MDyadicModule72

/- Helper module Solutions.RegevBridgeGaussianLatticeScaling. -/
section P2MDyadicModule73

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem rho_dilation_inverse (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width)
    (value : ScalingSpace (dimension:=dimension)) :
    rho width ((dilation factor hfactor).symm value)=rho (factor*width) value := by
  unfold rho
  rw [dilation_symm_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hfactor)]
  congr 1
  field_simp [hfactor.ne',hwidth.ne']

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule73

/- Helper module Solutions.RegevBridgeGaussianCosetGeometry. -/
section P2MDyadicModule74

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Public coefficients and the hidden secret live in the same fixed
input basis; zero secret coordinates are allowed. -/
def publicCoordinates {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (value : lattice) : Index → ZMod q :=
  fun index => (basis.equivFun value index : ZMod q)

theorem publicCoordinates_lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) :
    publicCoordinates q lattice basis (lift q lattice basis color)=color := by
  funext index
  unfold publicCoordinates lift
  rw [LinearEquiv.apply_symm_apply]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

theorem modulusLattice_le (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) :
    modulusLattice q lattice ≤ lattice := by
  intro value membership
  obtain ⟨original,horiginal,rfl⟩ := (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) value).mp membership
  have h := lattice.smul_mem (q : ℤ) horiginal
  simpa only [←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast] using h

/-- The actual point in the coset qL+u, viewed back in L. -/
def sample (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (shift : lattice) (value : modulusLattice q lattice) : lattice :=
  ⟨(value : Space (dimension:=dimension))+(shift : Space (dimension:=dimension)),
    lattice.add_mem (modulusLattice_le q lattice value.property) shift.property⟩

theorem publicCoordinates_add {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (first second : lattice) :
    publicCoordinates q lattice basis (first+second)=publicCoordinates q lattice basis first+publicCoordinates q lattice basis second := by
  funext index
  simp only [publicCoordinates,map_add,Pi.add_apply,Int.cast_add]

theorem publicCoordinates_sub {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (first second : lattice) :
    publicCoordinates q lattice basis (first-second)=publicCoordinates q lattice basis first-publicCoordinates q lattice basis second := by
  funext index
  simp only [publicCoordinates,map_sub,Pi.sub_apply,Int.cast_sub]

/-- The zero public-coefficient fiber is exactly the actual q-dilate. -/
theorem publicCoordinates_zero_iff {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (value : lattice) :
    publicCoordinates q lattice basis value=0 ↔ (value : Space (dimension:=dimension)) ∈ modulusLattice q lattice := by
  constructor
  · intro hzero
    have hdiv (index : Index) : (q : ℤ) ∣ basis.equivFun value index :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by simpa only [publicCoordinates,Pi.zero_apply] using congrFun hzero index)
    let original := basis.equivFun.symm (fun index => basis.equivFun value index/(q : ℤ))
    have he : (q : ℤ) • original=value := by
      apply basis.equivFun.injective
      rw [map_smul]
      funext index
      simp only [original,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]
      exact Int.mul_ediv_cancel' (hdiv index)
    apply (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mpr
    refine ⟨(original : Space (dimension:=dimension)),original.property,?_⟩
    have h := congrArg (fun point : lattice => (point : Space (dimension:=dimension))) he
    simpa only [Submodule.coe_smul,←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast] using h
  · intro membership
    obtain ⟨original,horiginal,heq⟩ :=
      (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mp membership
    let originalPoint : lattice := ⟨original,horiginal⟩
    have he : value=(q : ℤ) • originalPoint := by
      apply Subtype.ext
      change (value : Space (dimension:=dimension))=(q : ℤ) • original
      rw [←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast]
      exact heq.symm
    rw [he]
    funext index
    simp [publicCoordinates,Pi.smul_apply]

theorem publicCoordinates_sample {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (shift : lattice) (value : modulusLattice q lattice) :
    publicCoordinates q lattice basis (sample q lattice shift value)=publicCoordinates q lattice basis shift := by
  let original : lattice := ⟨(value : Space (dimension:=dimension)),modulusLattice_le q lattice value.property⟩
  have hz : publicCoordinates q lattice basis original=0 :=
    (publicCoordinates_zero_iff q lattice basis original).mpr value.property
  change publicCoordinates q lattice basis (original+shift)=publicCoordinates q lattice basis shift
  rw [publicCoordinates_add,hz,zero_add]

theorem publicCoordinates_fiber {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (color : Index → ZMod q) (value : lattice) :
    publicCoordinates q lattice basis value=color ↔
      ((value-lift q lattice basis color : lattice) : Space (dimension:=dimension)) ∈ modulusLattice q lattice := by
  rw [←publicCoordinates_zero_iff q lattice basis (value-lift q lattice basis color),
    publicCoordinates_sub,publicCoordinates_lift,sub_eq_zero]

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule74

/- Helper module Solutions.RegevBridgeGaussianFiniteFourier. -/
section P2MDyadicModule75

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

end P2MDyadicModule75

/- Helper module Solutions.RegevBridgeLatticeGaussianMass. -/
section P2MDyadicModule76

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

end P2MDyadicModule76

/- Helper module Solutions.RegevBridgeLatticeGaussianCosetMax. -/
section P2MDyadicModule77

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped BigOperators FourierTransform

noncomputable section

variable {dimension : ℕ}

theorem rhoCoset_nonneg (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) : 0≤rhoCoset width lattice shift :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

theorem norm_periodizedGaussian (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) :
    ‖periodizedGaussian lattice width shift‖=rhoCoset width lattice shift := by
  rw [periodized_eq_rhoCoset,Complex.norm_real,Real.norm_of_nonneg (rhoCoset_nonneg lattice width shift)]

/-- Among all translates, the genuine Gaussian mass on a lattice is
maximized at the unshifted lattice, by the full positive Poisson series. -/
theorem rhoCoset_shift_le_zero (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) (shift : Space (dimension:=dimension)) :
    rhoCoset width lattice shift≤rhoCoset width lattice 0 := by
  have hs : Summable (fun frequency : dual lattice =>
      ((width : ℂ)^dimension*(rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)) := by
    simpa only [mul_assoc] using (summable_dual_series lattice width hwidth shift).mul_left ((width : ℂ)^dimension)
  have hpoint (frequency : dual lattice) :
      ‖((width : ℂ)^dimension*(rho (1/width) (frequency : Space (dimension:=dimension)) : ℂ))*
        (𝐞 (inner ℝ shift (frequency : Space (dimension:=dimension))) : ℂ)‖=
      width^dimension*rho (1/width) (frequency : Space (dimension:=dimension)) := by
    rw [norm_mul,norm_mul,Circle.norm_coe,mul_one,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg hwidth.le,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ rho (1/width) (frequency : Space (dimension:=dimension)) from (Real.exp_pos _).le)]
  have hbound := norm_tsum_le_tsum_norm hs.norm
  simp only [hpoint,tsum_mul_left] at hbound
  have hpoisson := congrArg norm (periodized_poisson lattice width hwidth shift)
  rw [norm_periodizedGaussian,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (ZLattice.covolume_pos lattice MeasureTheory.volume).le] at hpoisson
  rw [hpoisson,rhoCoset_zero_poisson lattice width hwidth]
  have h := mul_le_mul_of_nonneg_left hbound
    (inv_nonneg.mpr (ZLattice.covolume_pos lattice MeasureTheory.volume).le)
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule77

/- Helper module Solutions.RegevBridgeGaussianShiftAmplitude. -/
section P2MDyadicModule78

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

end P2MDyadicModule78

/- Helper module Solutions.RegevBridgeGaussianHilbertState. -/
section P2MDyadicModule79

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

end P2MDyadicModule79

/- Helper module Solutions.RegevBridgeGaussianCosetPartition. -/
section P2MDyadicModule80

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators Classical

noncomputable section

variable {dimension : ℕ} {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- Exact partition of L by its actual input-basis residue vector. -/
def partitionEquiv (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) : lattice ≃ (Index → ZMod q) × modulusLattice q lattice where
  toFun value :=
    let color := publicCoordinates q lattice basis value
    (color,⟨((value-lift q lattice basis color : lattice) : Space (dimension:=dimension)),
      (publicCoordinates_fiber q lattice basis color value).mp rfl⟩)
  invFun pair := sample q lattice (lift q lattice basis pair.1) pair.2
  left_inv value := by
    apply Subtype.ext
    change ((value : Space (dimension:=dimension))-(lift q lattice basis (publicCoordinates q lattice basis value) : Space (dimension:=dimension)))+
      (lift q lattice basis (publicCoordinates q lattice basis value) : Space (dimension:=dimension))=(value : Space (dimension:=dimension))
    abel
  right_inv pair := by
    rcases pair with ⟨color,value⟩
    have hc := (publicCoordinates_sample q lattice basis (lift q lattice basis color) value).trans
      (publicCoordinates_lift q lattice basis color)
    apply Prod.ext
    · exact hc
    · apply Subtype.ext
      change ((sample q lattice (lift q lattice basis color) value : Space (dimension:=dimension))-
        (lift q lattice basis (publicCoordinates q lattice basis (sample q lattice (lift q lattice basis color) value)) : Space (dimension:=dimension)))=
        (value : Space (dimension:=dimension))
      rw [hc]
      change ((value : Space (dimension:=dimension))+(lift q lattice basis color : Space (dimension:=dimension)))-
        (lift q lattice basis color : Space (dimension:=dimension))=(value : Space (dimension:=dimension))
      abel

omit [DecidableEq Index] in
theorem partitionEquiv_public_symm (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) (pair : (Index → ZMod q) × modulusLattice q lattice) :
    publicCoordinates q lattice basis ((partitionEquiv q lattice basis).symm pair)=pair.1 := by
  exact congrArg Prod.fst ((partitionEquiv q lattice basis).apply_symm_apply pair)

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule80

/- Helper module Solutions.RegevBridgeWideGaussianScale. -/
section P2MDyadicModule81

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteDraw

open scoped BigOperators

@[fun_prop] theorem naturalBits_poly : Poly Nat.bits := ⟨PolyProgram.natAsList⟩

@[fun_prop] theorem signedAbsolute_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule81

/- Helper module Solutions.RegevBridgeRationalGramSchmidt. -/
section P2MDyadicModule82

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

end P2MDyadicModule82

/- Helper module Solutions.AdvantageBridgeBundleEmitter. -/
section P2MDyadicModule83

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

end InfoLossLAR.WorstCase

end P2MDyadicModule83

/- Helper module Solutions.AdvantageBridgeBodyDEmission. -/
section P2MDyadicModule84

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

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2PlatformSerialization

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule84

/- Helper module Solutions.RegevBridgeRationalGramSchmidtNative. -/
section P2MDyadicModule85

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

end P2MDyadicModule85

/- Helper module Solutions.RegevBridgeRationalGramSchmidtInput. -/
section P2MDyadicModule86

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

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule86

/- Helper module Solutions.RegevBridgeRationalInverseAlgebra. -/
section P2MDyadicModule87

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

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule87

/- Helper module Solutions.RegevBridgeRationalInverseNative. -/
section P2MDyadicModule88

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

end P2MDyadicModule88

/- Helper module Solutions.RegevBridgeRationalInverseRefinement. -/
section P2MDyadicModule89

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

end P2MDyadicModule89

/- Helper module Solutions.RegevBridgeNativeDual. -/
section P2MDyadicModule90

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
private theorem nativeDualRows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (h : B.det≠0) :
    current (inputRows B)=List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => dualVector B j i)) := by
  exact current_correct B h

theorem current_inverse_transpose {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    decodeMatrix n (current (inputRows B))=(Matrix.transpose (fun row col => (B row col : ℚ)))⁻¹ := by
  have hd : decodeMatrix n (current (inputRows B))=(fun row col => dualVector B col row) := by
    ext row col
    simp only [decodeMatrix,nativeDualRows B hdet,List.getElem?_ofFn,row.isLt,col.isLt,
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

end P2MDyadicModule90

/- Helper module Solutions.RegevBridgeNativeFixedBits. -/
section P2MDyadicModule91

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

end InfoLossLAR.WorstCase.NativeFixedBits

end P2MDyadicModule91

/- Helper module Solutions.RegevBridgeCoherentInjectionLayout. -/
section P2MDyadicModule92

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms.Complexity FiniteGateTransport

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

end P2MDyadicModule92

/- Helper module Solutions.RegevBridgeCoherentXorCopy. -/
section P2MDyadicModule93

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

end P2MDyadicModule93

/- Helper module Solutions.RegevBridgeCoherentClassicalOracle. -/
section P2MDyadicModule94

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

end P2MDyadicModule94

/- Helper module Solutions.RegevBridgeCoherentClassicalOracleNative. -/
section P2MDyadicModule95

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

end P2MDyadicModule95

/- Helper module Solutions.RegevBridgeCoherentClassicalOracleBasis. -/
section P2MDyadicModule96

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

variable {f : Str → Str} (P : PolyProgram id id f)

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

/-- A native inverse function can erase an old padded input after the
forward result has been retained. This is the Boolean identity used by the
second actual clean circuit, including every high padding bit. -/
theorem maskedData_erases (word original : Str) (h : f word=original) :
    maskedData P word (fun i : Fin (capacity P word.length) => wordExtension original i.val)=
      (fun _ => false) := by
  funext i
  simp [maskedData,h]

end InfoLossLAR.WorstCase.CoherentClassicalOracle

end

end P2MDyadicModule96

/- Helper module Solutions.RegevBridgeCoherentInjectionOracle. -/
section P2MDyadicModule97

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

theorem originalSize_ge (n : ℕ) : n ≤ originalSize P Q n := by
  simp only [originalSize,outputSize,capacity]
  omega

def outputBits (word : Str) : Bits (outputSize P word.length) := fun i => wordExtension (f word) i.val

def finalBits (word : Str) : Bits (totalWidth P Q word.length) :=
  dataBits (fun _ => false) (outputBits P word)

end InfoLossLAR.WorstCase.CoherentInjection

end

end P2MDyadicModule97

/- Helper module Solutions.RegevBridgeCoherentInjectionEmitter. -/
section P2MDyadicModule98

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

end P2MDyadicModule98

/- Helper module Solutions.RegevBridgeNativePaddedWords. -/
section P2MDyadicModule99

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

end P2MDyadicModule99

/- Helper module Solutions.RegevBridgeNativeFixedResidue. -/
section P2MDyadicModule100

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

@[simp] theorem current_length (ticks : List Unit) (value : ℤ) :
    (current (ticks,value)).length=ticks.length := NativeFixedBits.current_length _ _

theorem residue_lt (ticks : List Unit) (value : ℤ) : emodNatural (value,modulus ticks ) <  modulus ticks := by
  rw [emodNatural_eq]
  have hp : (0 : ℤ ) <  modulus ticks := by exact_mod_cast modulus_pos ticks
  have hn := Int.emod_nonneg value (ne_of_gt hp)
  have hl := Int.emod_lt_of_pos value hp
  have he := Int.toNat_of_nonneg hn
  omega

theorem current_value (ticks : List Unit) (value : ℤ) :
    bitValue (current (ticks,value))=(value%(modulus ticks : ℤ)).toNat := by
  rw [current,NativeFixedBits.current_value]
  · exact emodNatural_eq _ _
  · rw [←modulus_eq];exact residue_lt ticks value

end InfoLossLAR.WorstCase.NativeFixedResidue

end P2MDyadicModule100

/- Helper module QueryWord. -/
section P2MDyadicModule101

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
  rw [RationalInverse.Native.nativeDualRows B hB] at hd
  have hmat : (Int.castRingHom ℚ).mapMatrix B = (fun row col => (B row col : ℚ)) := by ext; rfl
  have hij (i j : Fin n) : RationalInverse.dualVector B j i =
      (((Int.castRingHom ℚ).mapMatrix B).transpose⁻¹) i j := by
    rw [hmat]
    have hij := congrFun (congrFun hd i) j
    simpa only [RationalInverse.Native.decodeMatrix,List.getElem?_ofFn,i.isLt,j.isLt,↓reduceDIte,Option.getD_some] using hij
  unfold points
  rw [RationalInverse.Native.current_correct B hB]
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

end P2MDyadicModule101

/- Helper module Solutions.RegevBridgeNativeDualClearing. -/
section P2MDyadicModule102

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

theorem cleared_cast {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (row col : Fin n) :
    (cleared B row col : ℚ)=(originalDenominator B : ℚ)*dualVector B col row := by
  apply scaled_num_cast
  rw [RationalInverse.Native.current_correct B hdet]
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

end P2MDyadicModule102

/- Helper module Solutions.RegevBridgeNativeDualQuotientSemantics. -/
section P2MDyadicModule103

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

def remainderVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) : Fin n → ℤ :=
  v-(cleared B).mulVec (quotientVector B v)

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

end P2MDyadicModule103

/- Helper module Solutions.RegevBridgeNativeDualQuotientGeometry. -/
section P2MDyadicModule104

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

end P2MDyadicModule104

/- Helper module IntegerDivision. -/
section P2MDyadicModule105

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

end P2MDyadicModule105

/- Helper module ResidueBlocks. -/
section P2MDyadicModule106

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

theorem blocks_length (b : List Unit) (z : List ℤ) : (blocks (b,z)).length=z.length*b.length := by
  induction z with
  | nil => simp [blocks]
  | cons u z ih =>
    change ((NativeFixedResidue.current (b,u)) ++ blocks (b,z)).length = _
    simp [ih,Nat.add_mul,Nat.add_comm]

def chunk (input : (List Unit × Str) × ℕ) : ℕ :=
  bitValue ((input.1.2.drop (input.2*input.1.1.length)).take input.1.1.length)

@[fun_prop] theorem chunk_poly : Poly chunk := by
  have hd := Poly.comp parser_drop_poly (show Poly (fun x : (List Unit × Str) × ℕ =>
    (x.1.2,x.2*x.1.1.length)) by fun_prop)
  have hb : Poly (fun x : (List Unit × Str) × ℕ => x.1.1.length) := by fun_prop
  have hv := Poly.comp bitValue_poly (Poly.comp parser_take_poly (Poly.pair hd hb))
  exact hv

theorem chunk_blocks (b : List Unit) (z : List ℤ) (tail : Str) (i : ℕ) (hi : i<z.length) :
    chunk ((b,blocks (b,z) ++ tail),i) = (z[i] % (NativeFixedResidue.modulus b : ℤ)).toNat := by
  induction z generalizing i with
  | nil => simp at hi
  | cons u z ih =>
    cases i with
    | zero =>
      change bitValue ((((NativeFixedResidue.current (b,u) ++ blocks (b,z)) ++ tail).drop (0*b.length)).take b.length) = _
      simp only [Nat.zero_mul,List.drop_zero,List.append_assoc,List.take_left' (NativeFixedResidue.current_length b u)]
      exact NativeFixedResidue.current_value b u
    | succ i =>
      have hd : (((NativeFixedResidue.current (b,u) ++ blocks (b,z)) ++ tail).drop ((i+1)*b.length)) =
          (blocks (b,z) ++ tail).drop (i*b.length) := by
        rw [List.append_assoc,List.drop_append,NativeFixedResidue.current_length,Nat.add_mul,Nat.one_mul]
        simp [List.drop_eq_nil_of_le (by simp : (NativeFixedResidue.current (b,u)).length ≤ i*b.length+b.length)]
      exact (congrArg (fun t : Str => bitValue (t.take b.length)) hd).trans (ih i (by simpa using hi))

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

theorem restore_blocks (b : List Unit) (z : List ℤ) (tail : Str) :
    restore ((b,blocks (b,z) ++ tail),answers (b,z))=z := by
  apply List.ext_getElem
  · simp [restore,answers]
  · intro i hleft hi
    simp only [restore,List.getElem_map,List.getElem_range]
    rw [chunk_blocks b z tail i hi]
    have hp : (0:ℤ)<NativeFixedResidue.modulus b := by exact_mod_cast NativeFixedResidue.modulus_pos b
    have hden := Int.emod_nonneg (z[i]) hp.ne'
    rw [Int.toNat_of_nonneg hden]
    simp only [answers,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some,
      NativeLLL.intDivNat_eq,mul_neg,sub_neg_eq_add]
    exact Int.emod_add_mul_ediv _ _

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule106

/- Helper module Layout. -/
section P2MDyadicModule107

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

theorem ticks_length (w : Str) : (ticks w).length=w.length := by simp [ticks]

def forward (w : Str) : Str := emit (ticks w,unpack w)

@[fun_prop] theorem forward_poly : Poly forward := by unfold forward; fun_prop

def cut (x : ℕ × Str) : Str × Str := (x.2.take x.1,x.2.drop x.1)

@[fun_prop] theorem cut_poly : Poly cut :=
  Poly.pair (Poly.comp parser_take_poly (Poly.pair Poly.snd Poly.fst))
    (Poly.comp parser_drop_poly (Poly.pair Poly.snd Poly.fst))

theorem cut_append (a r : Str) (k : ℕ) (hk : a.length=k) : cut (k,a++r)=(a,r) := by
  rw [←hk];simp only [cut,List.take_left,List.drop_left]

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

end P2MDyadicModule107

/- Helper module Solutions.RegevBridgeDualIntegerBasis. -/
section P2MDyadicModule108

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem dualIntegerBasis_repr (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (point : dual (inputLattice basis hdet)) (index : Fin dimension) :
    (dualIntegerBasis basis hdet).repr point index=
      pairing (inputLattice basis hdet) point (integerBasis basis hdet index) := by
  simp only [dualIntegerBasis,Module.Basis.map_repr]
  rfl

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule108

/- Helper module Solutions.RegevBridgeNativeDualQuotientEquiv. -/
section P2MDyadicModule109

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

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end P2MDyadicModule109

/- Helper module Solutions.RegevBridgeLatticeGaussianTail. -/
section P2MDyadicModule110

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

end P2MDyadicModule110

/- Helper module Solutions.RegevBridgePeriodizedTailBound. -/
section P2MDyadicModule111

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- Full nonnegative fiber sums on an arbitrary finite quotient. -/
def fiberMass {Index Color : Type*} [DecidableEq Color]
    (quotient : Index → Color) (weight : Index → ℝ) (color : Color) : ℝ :=
  ∑' point,if quotient point=color then weight point else 0

theorem summable_filtered_nonnegative {Index : Type*} (weight : Index → ℝ)
    (hsummable : Summable weight) (hnonnegative : ∀ point,0≤weight point) (predicate : Index → Prop)
    [DecidablePred predicate] : Summable (fun point => if predicate point then weight point else 0) := by
  apply Summable.of_nonneg_of_le _ _ hsummable
  · intro point;split_ifs <;> simp [hnonnegative]
  · intro point;split_ifs <;> simp [hnonnegative]

/-- Exact complete mass accounting across the finite quotient. -/
theorem sum_fiberMass {Index Color : Type*} [Fintype Color] [DecidableEq Color]
    (quotient : Index → Color) (weight : Index → ℝ)
    (hsummable : Summable weight) (hnonnegative : ∀ point,0≤weight point) :
    (∑ color,fiberMass quotient weight color)=∑' point,weight point := by
  classical
  have hfiltered (color : Color) : Summable (fun point => if quotient point=color then weight point else 0) :=
    summable_filtered_nonnegative weight hsummable hnonnegative _
  unfold fiberMass
  rw [←Summable.tsum_finsetSum (fun color (_ : color ∈ Finset.univ) => hfiltered color)]
  apply tsum_congr
  intro point
  simp

/-- The full periodized tail has a dimension-free l2-square bound. This
uses its complete fiber maximum, so a fine-grid cardinality never enters. -/
theorem fiber_square_sum_le {Index Color : Type*} [Fintype Color] [DecidableEq Color]
    (quotient : Index → Color) (weight : Index → ℝ)
    (hsummable : Summable weight) (hnonnegative : ∀ point,0≤weight point)
    (bound : ℝ) (hbound : ∀ color,fiberMass quotient weight color ≤ bound) :
    (∑ color,(fiberMass quotient weight color)^2) ≤ bound*∑' point,weight point := by
  calc
    _ ≤ ∑ color,bound*fiberMass quotient weight color := by
      apply Finset.sum_le_sum
      intro color _
      have hnonneg : 0≤fiberMass quotient weight color := by
        apply tsum_nonneg
        intro point
        split_ifs <;> simp [hnonnegative]
      nlinarith [hbound color]
    _ = bound*∑' point,weight point := by
      rw [←Finset.mul_sum,sum_fiberMass quotient weight hsummable hnonnegative]

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule111

/- Helper module Solutions.RegevBridgeLatticeGaussianSeparation. -/
section P2MDyadicModule112

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- A separated lattice has only its zero Gaussian mass inside the ball. -/
theorem rhoCoset_eq_one_add_tail
    (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius : ℝ) (hwidth : 0<width) (hradius : 0<radius)
    (hseparation : ∀ point : lattice,point≠0 → radius ≤ ‖(point : Space (dimension:=dimension))‖) :
    rhoCoset width lattice 0=1+gaussianTail lattice width radius := by
  classical
  have hs := summable_gaussian_lattice lattice width hwidth
  have h := hs.tsum_eq_add_tsum_ite (0 : lattice)
  have hzero : rho width ((0 : lattice) : Space (dimension:=dimension))=1 := by simp [rho]
  rw [hzero] at h
  have htail : (∑' point : lattice,if point=0 then 0 else rho width (point : Space (dimension:=dimension)))=
      gaussianTail lattice width radius := by
    unfold gaussianTail
    apply tsum_congr
    intro point
    by_cases hpoint : point=0
    · subst point
      simp only [ite_true,ZeroMemClass.coe_zero,norm_zero,not_le.mpr hradius,ite_false]
    · simp only [hpoint,ite_false,hseparation point hpoint,ite_true]
  rw [htail] at h
  simpa only [rhoCoset,add_zero] using h

/-- Small relative Gaussian tail on a separated lattice bounds its entire
unshifted mass by the reciprocal remaining fraction. -/
theorem rhoCoset_separated_le (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius error : ℝ) (hwidth : 0<width) (hradius : 0<radius) (herror : error<1)
    (hseparation : ∀ point : lattice,point≠0 → radius ≤ ‖(point : Space (dimension:=dimension))‖)
    (htail : gaussianTail lattice width radius ≤ error*rhoCoset width lattice 0) :
    rhoCoset width lattice 0 ≤ 1/(1-error) := by
  have hequal := rhoCoset_eq_one_add_tail lattice width radius hwidth hradius hseparation
  apply (le_div_iff₀ (by linarith : 0<1-error)).mpr
  nlinarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule112

/- Helper module Solutions.RegevBridgeNativeGaussianSmoothing. -/
section P2MDyadicModule113

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection IntegerBasis NativeDualQuotient

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

def dualColumnBudget (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) : ℝ :=
  1+∑ index,‖dualRealBasis basis hdet index‖

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule113

/- Helper module Solutions.RegevBridgeLatticeResidueFiber. -/
section P2MDyadicModule114

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ} {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- The complete coefficient residue fiber is exactly one genuine
modulus-lattice coset, for every absolutely summable complex function. -/
theorem tsum_residue_fiber (modulus : ℕ) [NeZero modulus]
    (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) (function : lattice → ℂ) (hsummable : Summable function)
    (target : Index → ZMod modulus) :
    (∑' point : lattice,if publicCoordinates modulus lattice basis point=target then function point else 0)=
      ∑' point : modulusLattice modulus lattice,function (sample modulus lattice (lift modulus lattice basis target) point) := by
  classical
  let filtered : lattice → ℂ := fun point =>
    if publicCoordinates modulus lattice basis point=target then function point else 0
  have hfiltered : Summable filtered := by
    apply Summable.of_norm_bounded hsummable.norm
    intro point
    dsimp only [filtered]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (function point)
  let equivalence := partitionEquiv modulus lattice basis
  have hpairs : Summable (filtered ∘ equivalence.symm) := equivalence.symm.summable_iff.mpr hfiltered
  change Summable (fun pair => filtered (equivalence.symm pair)) at hpairs
  have hreindex := equivalence.symm.tsum_eq filtered
  rw [hpairs.tsum_prod,tsum_fintype] at hreindex
  change (∑' point : lattice,filtered point)=_
  rw [←hreindex]
  have hinner (color : Index → ZMod modulus) :
      (∑' point : modulusLattice modulus lattice,filtered (equivalence.symm (color,point)))=
      if color=target then
        ∑' point : modulusLattice modulus lattice,function (sample modulus lattice (lift modulus lattice basis color) point) else 0 := by
    dsimp only [filtered]
    simp_rw [show ∀ point : modulusLattice modulus lattice,
      publicCoordinates modulus lattice basis (equivalence.symm (color,point))=color from
      fun point => partitionEquiv_public_symm modulus lattice basis (color,point)]
    by_cases hcolor : color=target
    · simp only [hcolor,ite_true]
      rfl
    · simp only [hcolor,ite_false,tsum_zero]
  simp_rw [hinner]
  simp

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule114

/- Helper module Solutions.RegevBridgeLatticeResidueFiberReal. -/
section P2MDyadicModule115

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

noncomputable section

variable {dimension : ℕ} {Index : Type*} [Fintype Index] [DecidableEq Index]

theorem tsum_residue_fiber_real (modulus : ℕ) [NeZero modulus]
    (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) (function : lattice → ℝ) (hsummable : Summable function)
    (target : Index → ZMod modulus) :
    (∑' point : lattice,if publicCoordinates modulus lattice basis point=target then function point else 0)=
      ∑' point : modulusLattice modulus lattice,function (sample modulus lattice (lift modulus lattice basis target) point) := by
  classical
  have h := tsum_residue_fiber modulus lattice basis (fun point => (function point : ℂ))
    (Complex.summable_ofReal.mpr hsummable) target
  have hfirst (point : lattice) : (if publicCoordinates modulus lattice basis point=target then (function point : ℂ) else 0)=
      ((if publicCoordinates modulus lattice basis point=target then function point else 0 : ℝ) : ℂ) := by split_ifs <;> rfl
  simp only [hfirst,←Complex.ofReal_tsum] at h
  exact Complex.ofReal_injective h

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule115

/- Helper module Solutions.RegevBridgeFineGridGaussian. -/
section P2MDyadicModule116

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

def fineGridWeight (width : ℝ) (point : Space (dimension:=dimension)) : ℝ :=
  rho width (fineGridPoint (modulus:=modulus) point)

theorem fineGridWeight_eq_rho (width : ℝ) (hwidth : 0<width) (point : Space (dimension:=dimension)) :
    fineGridWeight (modulus:=modulus) width point=rho ((modulus : ℝ)*width) point := by
  exact rho_dilation_inverse (modulus : ℝ) width (by exact_mod_cast NeZero.pos modulus) hwidth point

theorem summable_fineGridWeight (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    Summable (fun point : lattice => fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension))) := by
  simp_rw [fineGridWeight_eq_rho width hwidth]
  exact summable_gaussian_lattice lattice ((modulus : ℝ)*width)
    (mul_pos (by exact_mod_cast NeZero.pos modulus) hwidth)

theorem rhoCoset_dilation_scale (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width) (shift : Space (dimension:=dimension)) :
    rhoCoset (factor*width) (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) (factor • shift)=
      rhoCoset width lattice shift := by
  rw [show factor • shift=dilation factor hfactor shift from rfl,rhoCoset_image]
  unfold rhoCoset
  apply tsum_congr
  intro point
  have h := rho_dilation_inverse factor width hfactor hwidth (dilation factor hfactor
    ((point : Space (dimension:=dimension))+shift))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h.symm

/-- Every actual fine-grid quotient fiber is the actual coarse-lattice
Gaussian coset mass at its canonical fine-grid representative. -/
theorem fineGrid_fiberMass
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width : ℝ) (hwidth : 0<width)
    (color : Fin dimension → ZMod modulus) :
    fiberMass (publicCoordinates modulus lattice basis)
      (fun point : lattice => fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension))) color=
      rhoCoset width lattice (FiniteLatticeFourier.gridPoint modulus lattice basis color) := by
  let hmodulus : 0<(modulus : ℝ) := Nat.cast_pos.mpr (NeZero.pos modulus)
  unfold fiberMass
  simp_rw [fineGridWeight_eq_rho width hwidth]
  rw [tsum_residue_fiber_real modulus lattice basis
    (fun point : lattice => rho ((modulus : ℝ)*width) (point : Space (dimension:=dimension)))
    (summable_gaussian_lattice lattice ((modulus : ℝ)*width) (mul_pos hmodulus hwidth)) color]
  change rhoCoset ((modulus : ℝ)*width) (modulusLattice modulus lattice)
    (GaussianProjection.CosetGeometry.lift modulus lattice basis color : Space (dimension:=dimension))=_
  have hshift : (GaussianProjection.CosetGeometry.lift modulus lattice basis color : Space (dimension:=dimension))=
      (modulus : ℝ) • FiniteLatticeFourier.gridPoint modulus lattice basis color := by
    rw [FiniteLatticeFourier.gridPoint,smul_smul,mul_inv_cancel₀ hmodulus.ne',one_smul]
  rw [hshift]
  exact rhoCoset_dilation_scale lattice (modulus : ℝ) width hmodulus hwidth _

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule116

/- Helper module Solutions.RegevBridgePeriodizedTruncation. -/
section P2MDyadicModule117

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- Exact full quotient amplitude minus the truncated amplitude is the
sum over all omitted points in that same fiber. -/
theorem fiberMass_sub_truncated {Index Color : Type*} [DecidableEq Color]
    (quotient : Index → Color) (weight : Index → ℝ)
    (hsummable : Summable weight) (hnonnegative : ∀ point,0≤weight point)
    (keep : Index → Prop) [DecidablePred keep] (color : Color) :
    fiberMass quotient weight color-
      fiberMass quotient (fun point => if keep point then weight point else 0) color=
      fiberMass quotient (fun point => if keep point then 0 else weight point) color := by
  have hfiltered := summable_filtered_nonnegative weight hsummable hnonnegative
    (fun point => quotient point=color)
  have htruncated := summable_filtered_nonnegative weight hsummable hnonnegative
    (fun point => quotient point=color ∧ keep point)
  have hterm (point : Index) :
      (if quotient point=color then weight point else 0)-
        (if quotient point=color then if keep point then weight point else 0 else 0)=
      if quotient point=color then if keep point then 0 else weight point else 0 := by
    split_ifs <;> ring
  have hsecond : Summable (fun point => if quotient point=color then if keep point then weight point else 0 else 0) := by
    simpa only [ite_and] using htruncated
  unfold fiberMass
  rw [←hfiltered.tsum_sub hsecond]
  apply tsum_congr
  exact hterm

/-- The complete quotient l2-square truncation error is bounded by a
uniform fiber mass times the entire omitted mass. -/
theorem periodized_truncation_square_le {Index Color : Type*} [Fintype Color] [DecidableEq Color]
    (quotient : Index → Color) (weight : Index → ℝ)
    (hsummable : Summable weight) (hnonnegative : ∀ point,0≤weight point)
    (keep : Index → Prop) [DecidablePred keep] (bound : ℝ)
    (hbound : ∀ color,fiberMass quotient weight color ≤ bound) :
    (∑ color,(fiberMass quotient weight color-
      fiberMass quotient (fun point => if keep point then weight point else 0) color)^2) ≤
      bound*∑' point,if keep point then 0 else weight point := by
  have htail : Summable (fun point => if keep point then 0 else weight point) := by
    simpa only [ite_not] using summable_filtered_nonnegative weight hsummable hnonnegative (fun point => ¬keep point)
  have htailNonnegative (point : Index) : 0≤(if keep point then 0 else weight point) := by
    split_ifs <;> simp [hnonnegative]
  have htailBound (color : Color) :
      fiberMass quotient (fun point => if keep point then 0 else weight point) color ≤ bound := by
    apply le_trans _ (hbound color)
    unfold fiberMass
    have hfirst := summable_filtered_nonnegative _ htail htailNonnegative (fun point => quotient point=color)
    have hsecond := summable_filtered_nonnegative _ hsummable hnonnegative (fun point => quotient point=color)
    apply hfirst.tsum_le_tsum _ hsecond
    intro point
    split_ifs <;> simp [hnonnegative]
  simp_rw [fiberMass_sub_truncated quotient weight hsummable hnonnegative keep]
  exact fiber_square_sum_le quotient _ htail htailNonnegative bound htailBound

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule117

/- Helper module Solutions.RegevBridgeFineGridGaussianTail. -/
section P2MDyadicModule118

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

theorem norm_fineGridPoint (point : Space (dimension:=dimension)) :
    ‖fineGridPoint (modulus:=modulus) point‖=‖point‖/(modulus : ℝ) := by
  have hmodulus : 0<(modulus : ℝ) := by exact_mod_cast NeZero.pos modulus
  rw [fineGridPoint,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hmodulus),div_eq_mul_inv,mul_comm]

/-- Fine-grid radial tail accounting is exactly the original input
lattice radial Gaussian tail at the rescaled width and radius. -/
theorem fineGrid_tail_eq (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width radius : ℝ) (hwidth : 0<width) :
    (∑' point : lattice,if ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius then 0
      else fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension)))=
      gaussianTail lattice ((modulus : ℝ)*width) ((modulus : ℝ)*radius) := by
  classical
  have hmodulus : 0<(modulus : ℝ) := by exact_mod_cast NeZero.pos modulus
  unfold gaussianTail
  apply tsum_congr
  intro point
  rw [norm_fineGridPoint,fineGridWeight_eq_rho width hwidth]
  have hcondition : ¬(‖(point : Space (dimension:=dimension))‖/(modulus : ℝ)<radius) ↔
      (modulus : ℝ)*radius ≤ ‖(point : Space (dimension:=dimension))‖ := by
    rw [not_lt,le_div_iff₀ hmodulus,mul_comm]
  split_ifs <;> simp_all

/-- The complete squared-amplitude error of periodizing the true fine
lattice Gaussian is controlled by a coarse-lattice mass and the full fine
Gaussian normalizer. There is no quotient-cardinality error factor. -/
theorem fineGrid_periodized_truncation_square_le
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (hscale : (dimension : ℝ)*width^2 ≤ radius^2) :
    (∑ color : Fin dimension → ZMod modulus,
      (rhoCoset width lattice (FiniteLatticeFourier.gridPoint modulus lattice basis color)-
        fiberMass (publicCoordinates modulus lattice basis)
          (fun point : lattice => if ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius then
            fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension)) else 0) color)^2) ≤
      rhoCoset width lattice 0*((1/4 : ℝ)^dimension*rhoCoset ((modulus : ℝ)*width) lattice 0) := by
  classical
  have hmodulus : 0<(modulus : ℝ) := by exact_mod_cast NeZero.pos modulus
  let weight : lattice → ℝ := fun point => fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension))
  let keep : lattice → Prop := fun point => ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius
  have hs := summable_fineGridWeight (modulus:=modulus) lattice width hwidth
  have hnonnegative (point : lattice) : 0≤weight point := (Real.exp_pos _).le
  have hbound (color : Fin dimension → ZMod modulus) :
      fiberMass (publicCoordinates modulus lattice basis) weight color ≤ rhoCoset width lattice 0 := by
    rw [fineGrid_fiberMass lattice basis width hwidth]
    exact rhoCoset_shift_le_zero lattice width hwidth _
  have hfirst := periodized_truncation_square_le (publicCoordinates modulus lattice basis) weight hs hnonnegative
    keep (rhoCoset width lattice 0) hbound
  dsimp only [weight] at hfirst
  simp_rw [fineGrid_fiberMass lattice basis width hwidth] at hfirst
  have htail : (∑' point : lattice,if keep point then 0 else weight point) ≤
      (1/4 : ℝ)^dimension*rhoCoset ((modulus : ℝ)*width) lattice 0 := by
    rw [show (fun point : lattice => if keep point then 0 else weight point)=
      (fun point : lattice => if ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius then 0
        else fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension))) from rfl,
      fineGrid_tail_eq lattice width radius hwidth]
    apply gaussianTail_le_quarter_pow lattice ((modulus : ℝ)*width) ((modulus : ℝ)*radius)
      (mul_pos hmodulus hwidth) (mul_nonneg hmodulus.le hradius)
    have h := mul_le_mul_of_nonneg_left hscale (sq_nonneg (modulus : ℝ))
    nlinarith
  exact hfirst.trans (mul_le_mul_of_nonneg_left htail (rhoCoset_nonneg lattice width 0))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule118

/- Helper module Solutions.RegevBridgeFineGridInjectivity. -/
section P2MDyadicModule119

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- A coarse lattice separated by twice the truncation radius makes the
actual quotient encoding injective on every retained fine lattice point. -/
theorem fineGrid_quotient_injective
    (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (radius : ℝ)
    (hseparation : ∀ point : lattice,point≠0 → 2*radius ≤ ‖(point : Space (dimension:=dimension))‖) :
    Set.InjOn (publicCoordinates modulus lattice basis)
      {point : lattice | ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius} := by
  intro first hfirst second hsecond hequal
  change ‖fineGridPoint (modulus:=modulus) (first : Space (dimension:=dimension))‖<radius at hfirst
  change ‖fineGridPoint (modulus:=modulus) (second : Space (dimension:=dimension))‖<radius at hsecond
  have hmodulus : 0<(modulus : ℝ) := Nat.cast_pos.mpr (NeZero.pos modulus)
  have hzero : publicCoordinates modulus lattice basis (first-second)=0 := by
    rw [publicCoordinates_sub,hequal,sub_self]
  have hmem := (publicCoordinates_zero_iff modulus lattice basis (first-second)).mp hzero
  obtain ⟨coarse,hcoarse,hscale⟩ := (mem_dilated_lattice lattice (modulus : ℝ) hmodulus _).mp hmem
  have hdifference : fineGridPoint (modulus:=modulus) (first : Space (dimension:=dimension))-
      fineGridPoint (modulus:=modulus) (second : Space (dimension:=dimension))=coarse := by
    rw [fineGridPoint,fineGridPoint,←smul_sub]
    change (modulus : ℝ)⁻¹ • ((first-second : lattice) : Space (dimension:=dimension))=coarse
    rw [←hscale,smul_smul,inv_mul_cancel₀ hmodulus.ne',one_smul]
  have hshort : ‖coarse‖<2*radius := by
    rw [←hdifference]
    have hnorm := norm_sub_le (fineGridPoint (modulus:=modulus) (first : Space (dimension:=dimension)))
      (fineGridPoint (modulus:=modulus) (second : Space (dimension:=dimension)))
    exact hnorm.trans_lt (by change _<2*radius;linarith)
  have hcoarseZero : coarse=0 := by
    by_contra hne
    have hsep := hseparation ⟨coarse,hcoarse⟩ (by intro h;exact hne (congrArg Subtype.val h))
    exact (not_lt_of_ge hsep) hshort
  apply Subtype.ext
  have hinjective : Function.Injective (fun point : Space (dimension:=dimension) =>
      fineGridPoint (modulus:=modulus) point) := by
    intro first second h
    have hscaled := congrArg (fun point : Space (dimension:=dimension) => (modulus : ℝ) • point) h
    simpa only [fineGridPoint,smul_smul,mul_inv_cancel₀ hmodulus.ne',one_smul] using hscaled
  exact hinjective (sub_eq_zero.mp (hdifference.trans hcoarseZero))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule119

/- Helper module Solutions.RegevBridgeFineGridSquareMass. -/
section P2MDyadicModule120

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- Squaring a real Gaussian amplitude changes the Regev width by sqrt2,
with the same Euclidean point and pi convention. -/
theorem rho_square (width : ℝ) (point : Space (dimension:=dimension)) :
    (rho width point)^2=rho (width/Real.sqrt 2) point := by
  by_cases hwidth : width=0
  · simp [hwidth,rho]
  unfold rho
  rw [←Real.exp_nat_mul]
  congr 1
  have hroot : Real.sqrt 2 ^2=(2 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [div_pow,hroot]
  field_simp
  ring

theorem summable_fineGridWeight_square
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) :
    Summable (fun point : lattice => (fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension)))^2) := by
  have hequal (point : lattice) :
      (fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension)))^2=
      fineGridWeight (modulus:=modulus) (width/Real.sqrt 2) (point : Space (dimension:=dimension)) := rho_square _ _
  simp_rw [hequal]
  exact summable_fineGridWeight lattice (width/Real.sqrt 2) (by positivity)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule120

/- Helper module Solutions.RegevBridgeTruncatedFiberNorm. -/
section P2MDyadicModule121

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- When truncation makes the quotient injective, every retained fiber
contains at most one amplitude, so its squared amplitude is its fiber
sum of squared amplitudes. -/
theorem truncated_fiber_square {Index Color : Type*} [DecidableEq Color]
    (quotient : Index → Color) (weight : Index → ℝ) (keep : Index → Prop) [DecidablePred keep]
    (hinjective : Set.InjOn quotient {point | keep point}) (color : Color) :
    (fiberMass quotient (fun point => if keep point then weight point else 0) color)^2=
      fiberMass quotient (fun point => if keep point then (weight point)^2 else 0) color := by
  classical
  by_cases hexists : ∃ point,keep point ∧ quotient point=color
  · obtain ⟨point,hkeep,hcolor⟩ := hexists
    have honly (other : Index) (hne : other≠point) : ¬(keep other ∧ quotient other=color) := by
      rintro ⟨hotherKeep,hotherColor⟩
      exact hne (hinjective hotherKeep hkeep (hotherColor.trans hcolor.symm))
    have hvalue : fiberMass quotient (fun point => if keep point then weight point else 0) color=weight point := by
      unfold fiberMass
      rw [tsum_eq_single point]
      · simp only [hcolor,hkeep,ite_true]
      · intro other hne
        have hnot := honly other hne
        split_ifs <;> simp_all
    have hsquare : fiberMass quotient (fun point => if keep point then (weight point)^2 else 0) color=(weight point)^2 := by
      unfold fiberMass
      rw [tsum_eq_single point]
      · simp only [hcolor,hkeep,ite_true]
      · intro other hne
        have hnot := honly other hne
        split_ifs <;> simp_all
    rw [hvalue,hsquare]
  · have hnot (point : Index) : ¬(keep point ∧ quotient point=color) := by
      exact fun h => hexists ⟨point,h⟩
    have hfirst (point : Index) : (if quotient point=color then if keep point then weight point else 0 else 0)=0 := by
      have h := hnot point
      split_ifs <;> simp_all
    have hsecond (point : Index) : (if quotient point=color then if keep point then (weight point)^2 else 0 else 0)=0 := by
      have h := hnot point
      split_ifs <;> simp_all
    simp only [fiberMass,hfirst,hsecond,tsum_zero,zero_pow (by norm_num : (2 : ℕ)≠0)]

/-- The full retained l2-square norm equals the complete retained square
mass when the quotient is injective on all retained source points. -/
theorem sum_truncated_fiber_square {Index Color : Type*} [Fintype Color] [DecidableEq Color]
    (quotient : Index → Color) (weight : Index → ℝ) (keep : Index → Prop) [DecidablePred keep]
    (hinjective : Set.InjOn quotient {point | keep point})
    (hsquare : Summable (fun point => (weight point)^2)) :
    (∑ color,(fiberMass quotient (fun point => if keep point then weight point else 0) color)^2)=
      ∑' point,if keep point then (weight point)^2 else 0 := by
  simp_rw [truncated_fiber_square quotient weight keep hinjective]
  have hnonnegative (point : Index) : 0≤(weight point)^2 := sq_nonneg _
  have htruncated := summable_filtered_nonnegative _ hsquare hnonnegative keep
  apply sum_fiberMass quotient _ htruncated
  intro point
  split_ifs <;> positivity

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule121

/- Helper module Solutions.RegevBridgeFineGridTruncatedNorm. -/
section P2MDyadicModule122

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

def truncatedAmplitude (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width radius : ℝ) (color : Fin dimension → ZMod modulus) : ℝ :=
  fiberMass (publicCoordinates modulus lattice basis)
    (fun point : lattice => if ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius then
      fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension)) else 0) color

def truncatedState (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width radius : ℝ) :
    EuclideanSpace ℂ (Fin dimension → ZMod modulus) :=
  WithLp.toLp 2 (fun color => (truncatedAmplitude (modulus:=modulus) lattice basis width radius color : ℂ))

theorem truncatedState_norm_sq
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width radius : ℝ) (hwidth : 0<width)
    (hseparation : ∀ point : lattice,point≠0 → 2*radius ≤ ‖(point : Space (dimension:=dimension))‖) :
    ‖truncatedState (modulus:=modulus) lattice basis width radius‖^2=
      ∑' point : lattice,if ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius then
        (fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension)))^2 else 0 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [truncatedState,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact sum_truncated_fiber_square (publicCoordinates modulus lattice basis)
    (fun point : lattice => fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension))) _
    (fineGrid_quotient_injective lattice basis radius hseparation)
    (summable_fineGridWeight_square lattice width hwidth)

/-- The complete retained square mass has the expected lower bound in
terms of the true fine Gaussian normalizer at width w/sqrt2. -/
theorem truncatedState_norm_sq_lower
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (hscale : (dimension : ℝ)*width^2 ≤ radius^2)
    (hseparation : ∀ point : lattice,point≠0 → 2*radius ≤ ‖(point : Space (dimension:=dimension))‖) :
    (1-(1/4 : ℝ)^dimension)*rhoCoset ((modulus : ℝ)*(width/Real.sqrt 2)) lattice 0 ≤
      ‖truncatedState (modulus:=modulus) lattice basis width radius‖^2 := by
  classical
  let weight : lattice → ℝ := fun point =>
    (fineGridWeight (modulus:=modulus) width (point : Space (dimension:=dimension)))^2
  let keep : lattice → Prop := fun point =>
    ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius
  have hs : Summable weight := summable_fineGridWeight_square lattice width hwidth
  have hn (point : lattice) : 0≤weight point := sq_nonneg _
  have hfirst := summable_filtered_nonnegative weight hs hn keep
  have hsecond : Summable (fun point => if keep point then 0 else weight point) := by
    simpa only [ite_not] using summable_filtered_nonnegative weight hs hn (fun point => ¬keep point)
  have hsum := hfirst.tsum_add hsecond
  have hterms (point : lattice) :
      (if keep point then weight point else 0)+(if keep point then 0 else weight point)=weight point := by split_ifs <;> simp
  simp only [hterms] at hsum
  have hsquare (point : lattice) : weight point=
      fineGridWeight (modulus:=modulus) (width/Real.sqrt 2) (point : Space (dimension:=dimension)) := rho_square _ _
  have htotal : (∑' point : lattice,weight point)=rhoCoset ((modulus : ℝ)*(width/Real.sqrt 2)) lattice 0 := by
    simp_rw [hsquare,fineGridWeight_eq_rho (width/Real.sqrt 2) (by positivity)]
    simp only [rhoCoset,add_zero]
  have htail : (∑' point : lattice,if keep point then 0 else weight point) ≤
      (1/4 : ℝ)^dimension*rhoCoset ((modulus : ℝ)*(width/Real.sqrt 2)) lattice 0 := by
    simp_rw [hsquare]
    change (∑' point : lattice,if ‖fineGridPoint (modulus:=modulus) (point : Space (dimension:=dimension))‖<radius then 0 else
      fineGridWeight (modulus:=modulus) (width/Real.sqrt 2) (point : Space (dimension:=dimension))) ≤ _
    rw [fineGrid_tail_eq lattice (width/Real.sqrt 2) radius (by positivity)]
    have hmodulus : 0<(modulus : ℝ) := by exact_mod_cast NeZero.pos modulus
    apply gaussianTail_le_quarter_pow lattice ((modulus : ℝ)*(width/Real.sqrt 2)) ((modulus : ℝ)*radius)
      (by positivity) (mul_nonneg hmodulus.le hradius)
    have hroot : Real.sqrt 2 ^2=(2 : ℝ) := Real.sq_sqrt (by norm_num)
    rw [mul_pow,div_pow,hroot,mul_pow]
    have h := mul_le_mul_of_nonneg_left hscale (sq_nonneg (modulus : ℝ))
    have hn : (0 : ℝ) ≤ dimension := Nat.cast_nonneg dimension
    nlinarith [mul_nonneg hn (sq_nonneg width)]
  rw [truncatedState_norm_sq lattice basis width radius hwidth hseparation]
  change _≤∑' point : lattice,if keep point then weight point else 0
  rw [htotal] at hsum
  nlinarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule122

/- Helper module Solutions.RegevBridgeCoherentProjection. -/
section P2MDyadicModule123

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

end InfoLossLAR.WorstCase.CoherentProjection

end P2MDyadicModule123

/- Helper module Solutions.RegevBridgeGaussianPureComparison. -/
section P2MDyadicModule124

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open CoherentProjection

noncomputable section

theorem normalized_smul_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (scalar : ℝ) (hscalar : 0<scalar) (value : E) : normalized (scalar • value)=normalized value := by
  rw [normalized,normalized,norm_smul,Real.norm_eq_abs,abs_of_pos hscalar,smul_smul,mul_inv_rev,
    mul_assoc,inv_mul_cancel₀ hscalar.ne',mul_one]

/-- Comparing arbitrary unnormalized amplitude vectors costs at most
 twice their relative error, measured against the first true norm. -/
theorem normalized_pair_distance_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (first second : E) (hfirst : first≠0) (hsecond : second≠0) :
    ‖normalized first-normalized second‖ ≤ 2*‖first-second‖/‖first‖ := by
  have hscalar : 0<‖first‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hfirst)
  have h := normalized_close (normalized first) (‖first‖⁻¹ • second)
    (normalized_norm first hfirst) (smul_ne_zero hscalar.ne' hsecond)
  rw [normalized_smul_pos _ hscalar second] at h
  have hequal : ‖normalized first-‖first‖⁻¹ • second‖=‖first-second‖/‖first‖ := by
    rw [normalized,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hscalar,div_eq_mul_inv,mul_comm]
  rw [hequal] at h
  simpa only [mul_div_assoc] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule124

/- Helper module Solutions.RegevBridgeFiniteGaussianStates. -/
section P2MDyadicModule125

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- A true squared Hilbert-space bound for the complete complex Gaussian
amplitude vectors on the finite quotient. -/
theorem periodizedState_truncatedState_sq_le
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (hscale : (dimension : ℝ)*width^2 ≤ radius^2) :
    ‖periodizedState (modulus:=modulus) lattice basis width-
      truncatedState (modulus:=modulus) lattice basis width radius‖^2 ≤
      rhoCoset width lattice 0*((1/4 : ℝ)^dimension*rhoCoset ((modulus : ℝ)*width) lattice 0) := by
  rw [EuclideanSpace.norm_sq_eq]
  have hpoint (color : Fin dimension → ZMod modulus) :
      ‖(periodizedState (modulus:=modulus) lattice basis width-
        truncatedState (modulus:=modulus) lattice basis width radius) color‖^2=
      (rhoCoset width lattice (FiniteLatticeFourier.gridPoint modulus lattice basis color)-
        truncatedAmplitude (modulus:=modulus) lattice basis width radius color)^2 := by
    change ‖((rhoCoset width lattice (FiniteLatticeFourier.gridPoint modulus lattice basis color) : ℂ)-
      (truncatedAmplitude (modulus:=modulus) lattice basis width radius color : ℂ))‖^2=_
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp only [hpoint]
  exact fineGrid_periodized_truncation_square_le lattice basis width radius hwidth hradius hscale

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule125

/- Helper module Solutions.RegevBridgeFineGridNormalization. -/
section P2MDyadicModule126

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

theorem quarter_pow_le_quarter (hdimension : 0 < dimension) : (1/4 : ℝ)^dimension  ≤  1/4 := by
  cases dimension with
  | zero => omega
  | succ dimension =>
    rw [pow_succ]
    have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (1/4 : ℝ) ≤ 1) (n:=dimension)
    nlinarith

/-- Under the actual coarse-lattice separation condition, every periodized
Gaussian coset has mass at most 4/3. -/
theorem separated_rhoCoset_le_four_thirds
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width radius : ℝ) (hwidth : 0 < width) (hradius : 0 < radius) (hdimension : 0 < dimension)
    (hscale : (dimension : ℝ)*width^2  ≤  radius^2)
    (hseparation : ∀ point : lattice,point≠0 → 2*radius  ≤  ‖(point : Space (dimension:=dimension))‖) :
    rhoCoset width lattice 0  ≤  4/3 := by
  have hquarter := quarter_pow_le_quarter hdimension
  have htail := gaussianTail_le_quarter_pow lattice width radius hwidth hradius.le hscale
  have hsep (point : lattice) (hne : point≠0) : radius  ≤  ‖(point : Space (dimension:=dimension))‖ := by
    exact (by linarith : radius ≤ 2*radius).trans (hseparation point hne)
  have h := rhoCoset_separated_le lattice width radius ((1/4 : ℝ)^dimension) hwidth hradius
    (by linarith) hsep htail
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < 1-(1/4 : ℝ)^dimension)).mpr
  linarith

/-- The true fine Gaussian normalizer for amplitudes is at most 2^n times
the true normalizer for their squares. -/
theorem fine_mass_le_two_pow_square_mass
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) :
    rhoCoset ((modulus : ℝ)*width) lattice 0  ≤ 
      (2 : ℝ)^dimension*rhoCoset ((modulus : ℝ)*(width/Real.sqrt 2)) lattice 0 := by
  have hmodulus : 0 < (modulus : ℝ) := by exact_mod_cast NeZero.pos modulus
  have hroot : 0 < Real.sqrt 2 := by positivity
  have hrootOne : (1 : ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  have hrootTwo : Real.sqrt 2 ≤ (2 : ℝ) := by apply Real.sqrt_le_iff.mpr;norm_num
  have h := rhoCoset_dilation_le lattice ((modulus : ℝ)*(width/Real.sqrt 2)) (Real.sqrt 2) (by positivity) hrootOne
  have hequal : Real.sqrt 2*((modulus : ℝ)*(width/Real.sqrt 2))=(modulus : ℝ)*width := by field_simp [hroot.ne']
  rw [hequal] at h
  have hpow := pow_le_pow_left₀ hroot.le hrootTwo dimension
  exact h.trans (mul_le_mul_of_nonneg_right hpow (rhoCoset_nonneg _ _ _))

/-- All true normalizers cancel in the relative squared Hilbert-space
truncation error, leaving a concrete exponentially small factor. -/
theorem fineGrid_relative_square_error
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width radius : ℝ) (hwidth : 0 < width) (hradius : 0 < radius)
    (hdimension : 0 < dimension) (hscale : (dimension : ℝ)*width^2  ≤  radius^2)
    (hseparation : ∀ point : lattice,point≠0 → 2*radius  ≤  ‖(point : Space (dimension:=dimension))‖) :
    ‖periodizedState (modulus:=modulus) lattice basis width-truncatedState (modulus:=modulus) lattice basis width radius‖^2  ≤ 
      (2*(1/2 : ℝ)^dimension)*‖truncatedState (modulus:=modulus) lattice basis width radius‖^2 := by
  let mass := rhoCoset ((modulus : ℝ)*(width/Real.sqrt 2)) lattice 0
  have hmass : 0 ≤ mass := rhoCoset_nonneg _ _ _
  have herror := periodizedState_truncatedState_sq_le (modulus:=modulus) lattice basis width radius hwidth hradius.le hscale
  have hcoarse := separated_rhoCoset_le_four_thirds lattice width radius hwidth hradius hdimension hscale hseparation
  have hfine := fine_mass_le_two_pow_square_mass (modulus:=modulus) lattice width hwidth
  have hlower := truncatedState_norm_sq_lower (modulus:=modulus) lattice basis width radius hwidth hradius.le hscale hseparation
  have hquarter := quarter_pow_le_quarter hdimension
  have hsmall : (3/4 : ℝ)*mass  ≤  ‖truncatedState (modulus:=modulus) lattice basis width radius‖^2 := by
    have h := mul_le_mul_of_nonneg_right (show (3/4 : ℝ) ≤ 1-(1/4 : ℝ)^dimension by linarith) hmass
    exact h.trans hlower
  have hfirst : ‖periodizedState (modulus:=modulus) lattice basis width-truncatedState (modulus:=modulus) lattice basis width radius‖^2  ≤ 
      (4/3 : ℝ)*((1/4 : ℝ)^dimension*((2 : ℝ)^dimension*mass)) := by
    apply herror.trans
    have h1 : rhoCoset width lattice 0*((1/4 : ℝ)^dimension*rhoCoset ((modulus : ℝ)*width) lattice 0) ≤
        (4/3 : ℝ)*((1/4 : ℝ)^dimension*rhoCoset ((modulus : ℝ)*width) lattice 0) :=
      mul_le_mul_of_nonneg_right hcoarse
        (mul_nonneg (pow_nonneg (by norm_num) dimension)
          (rhoCoset_nonneg lattice ((modulus : ℝ)*width) 0))
    have h2 : (4/3 : ℝ)*((1/4 : ℝ)^dimension*rhoCoset ((modulus : ℝ)*width) lattice 0) ≤
        (4/3 : ℝ)*((1/4 : ℝ)^dimension*((2 : ℝ)^dimension*mass)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfine (by positivity)) (by norm_num)
    exact h1.trans h2
  have hequal : (4/3 : ℝ)*((1/4 : ℝ)^dimension*((2 : ℝ)^dimension*mass))=
      (4/3 : ℝ)*(1/2 : ℝ)^dimension*mass := by
    rw [←mul_assoc ((1/4 : ℝ)^dimension),←mul_pow]
    norm_num
    ring
  rw [hequal] at hfirst
  have hscaled := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 2*(1/2 : ℝ)^dimension)
  nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) dimension) hmass]

/-- The normalized actual finite quotient Gaussian and its true truncated
pure state are exponentially close, uniformly in the fine-grid modulus. -/
theorem normalized_periodized_truncated_close
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width radius : ℝ) (hwidth : 0 < width) (hradius : 0 < radius)
    (hdimension : 0 < dimension) (hscale : (dimension : ℝ)*width^2 ≤ radius^2)
    (hseparation : ∀ point : lattice,point≠0 → 2*radius ≤ ‖(point : Space (dimension:=dimension))‖) :
    ‖CoherentProjection.normalized (periodizedState (modulus:=modulus) lattice basis width)-
      CoherentProjection.normalized (truncatedState (modulus:=modulus) lattice basis width radius)‖ ≤
      2*Real.sqrt (2*(1/2 : ℝ)^dimension) := by
  have hmodulus : 0 < (modulus : ℝ) := by exact_mod_cast NeZero.pos modulus
  have hmass := rhoCoset_zero_pos lattice ((modulus : ℝ)*(width/Real.sqrt 2)) (by positivity)
  have hquarter := quarter_pow_le_quarter hdimension
  have hnormLower := truncatedState_norm_sq_lower (modulus:=modulus) lattice basis width radius hwidth hradius.le hscale hseparation
  have hnormPositive : 0 < ‖truncatedState (modulus:=modulus) lattice basis width radius‖ := by
    have hpositive : 0 < (1-(1/4 : ℝ)^dimension)*rhoCoset ((modulus : ℝ)*(width/Real.sqrt 2)) lattice 0 :=
      mul_pos (by linarith) hmass
    have hnormSquare : 0 < ‖truncatedState (modulus:=modulus) lattice basis width radius‖^2 :=
      hpositive.trans_le hnormLower
    nlinarith [norm_nonneg (truncatedState (modulus:=modulus) lattice basis width radius)]
  have htruncated : truncatedState (modulus:=modulus) lattice basis width radius≠0 := norm_pos_iff.mp hnormPositive
  have hperiodized : periodizedState (modulus:=modulus) lattice basis width≠0 := by
    have hpositive : 0 < rhoCoset width lattice (FiniteLatticeFourier.gridPoint modulus lattice basis (0 : Fin dimension → ZMod modulus)) := by
      have h := (summable_gaussian_coset lattice width hwidth
        (FiniteLatticeFourier.gridPoint modulus lattice basis (0 : Fin dimension → ZMod modulus))).tsum_pos
        (fun _ => (Real.exp_pos _).le) (0 : lattice) (Real.exp_pos _)
      exact h
    intro hzero
    have hvalue := congrArg (fun vector : EuclideanSpace ℂ (Fin dimension → ZMod modulus) => vector 0) hzero
    change (rhoCoset width lattice (FiniteLatticeFourier.gridPoint modulus lattice basis (0 : Fin dimension → ZMod modulus)) : ℂ)=0 at hvalue
    exact (ne_of_gt hpositive) (Complex.ofReal_injective (by simpa using hvalue))
  have hsquare := fineGrid_relative_square_error (modulus:=modulus) lattice basis width radius hwidth hradius hdimension hscale hseparation
  have hradical : 0 ≤ 2*(1/2 : ℝ)^dimension := by positivity
  have hrelative : ‖periodizedState (modulus:=modulus) lattice basis width-truncatedState (modulus:=modulus) lattice basis width radius‖ ≤
      Real.sqrt (2*(1/2 : ℝ)^dimension)*‖truncatedState (modulus:=modulus) lattice basis width radius‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hnormPositive.le)).mp
    rw [mul_pow,Real.sq_sqrt hradical]
    exact hsquare
  have h := normalized_pair_distance_le (truncatedState (modulus:=modulus) lattice basis width radius)
    (periodizedState (modulus:=modulus) lattice basis width) htruncated hperiodized
  rw [norm_sub_rev, norm_sub_rev (truncatedState (modulus:=modulus) lattice basis width radius)
    (periodizedState (modulus:=modulus) lattice basis width)] at h
  apply h.trans
  apply (div_le_iff₀ hnormPositive).mpr
  nlinarith

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule126

/- Helper module Solutions.RegevBridgeHybridMeasurement. -/
section P2MDyadicModule127

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentDecoder

open scoped BigOperators

noncomputable section

/-- Retain the amplitudes in a final classical measurement event. -/
def retainEvent {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : EuclideanSpace ℂ α :=
  open Classical in WithLp.toLp 2 (fun value => if event value then state value else 0)

theorem bornEvent_eq_norm_sq {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : bornEvent event state=‖retainEvent event state‖^2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  unfold bornEvent retainEvent
  apply Finset.sum_congr rfl
  intro value _
  split_ifs <;> simp_all

theorem retainEvent_norm_le {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : ‖retainEvent event state‖ ≤ ‖state‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro value _
  change ‖(if event value then state value else 0 : ℂ)‖^2 ≤ ‖state value‖^2
  split_ifs <;> simp_all

theorem retainEvent_sub {α : Type*} [Fintype α] (event : α → Prop)
    (first second : EuclideanSpace ℂ α) :
    retainEvent event (first-second)=retainEvent event first-retainEvent event second := by
  classical
  ext value
  change (if event value then first value-second value else 0)=
    (if event value then first value else 0)-(if event value then second value else 0)
  split_ifs <;> simp

/-- Final classical measurement contracts coherent error. This estimate uses
the full amplitudes and does not replace correlated garbage with independent
output bits. -/
theorem bornEvent_error_le {α : Type*} [Fintype α] (event : α → Prop)
    (first second : EuclideanSpace ℂ α) :
    |bornEvent event first-bornEvent event second| ≤ ‖first-second‖*(‖first‖+‖second‖) := by
  rw [bornEvent_eq_norm_sq,bornEvent_eq_norm_sq]
  have hdiff : |‖retainEvent event first‖-‖retainEvent event second‖| ≤ ‖first-second‖ := by
    apply (abs_norm_sub_norm_le _ _).trans
    rw [←retainEvent_sub]
    exact retainEvent_norm_le event _
  have hsum := add_le_add (retainEvent_norm_le event first) (retainEvent_norm_le event second)
  calc
    _ = |‖retainEvent event first‖-‖retainEvent event second‖| *
        (‖retainEvent event first‖+‖retainEvent event second‖) := by
      rw [←abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),←abs_mul]
      congr 1
      ring
    _ ≤ _ := mul_le_mul hdiff hsum (by positivity) (norm_nonneg _)

end

end InfoLossLAR.WorstCase.CoherentDecoder

end P2MDyadicModule127

/- Helper module Cofactor. -/
section P2MDyadicModule128

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout

open InfoLossLAR.WorstCase IntegerBasis

noncomputable section

variable {n M : ℕ} [NeZero M]

def cofactorSum (B : Matrix (Fin n) (Fin n) ℤ) : ℕ := ∑ i, ∑ j, (B.adjugate i j).natAbs

end

end GridReadout

end P2MDyadicModule128

/- Helper module Solutions.RegevBridgeLoadedBatchPostFrame. -/
section P2MDyadicModule129

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch.PostComposition

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2StockLists Integration9_9.TM2PlatformSerialization

open QMCNumericRuntime

@[fun_prop] theorem readWireWord_poly : Poly readWireWord := by
  exact Poly.pair (Poly.comp Poly.snd readUnary_poly) (Poly.comp Poly.fst readUnary_poly)

theorem readWireWord_rest_length (word : Str) : (readWireWord word).1.length ≤ word.length := by
  simp only [readWireWord,readUnary,List.length_drop]
  omega

theorem readWireWord_append (n : ℕ) (suffix : Str) :
    readWireWord (encNat n++suffix)=(suffix,encNat n) := by
  simp only [readWireWord,readUnary_append]

@[fun_prop] theorem readWireWords_poly : Poly readWireWords :=
  readList_poly readWireWord readWireWord_poly readWireWord_rest_length

theorem readWireWords_append (wires : List ℕ) (suffix : Str) :
    readWireWords (encStr (wires.map encNat)++suffix)=(suffix,wires.map encNat) :=
  readList_append_mapped readWireWord encNat encNat readWireWord_append wires suffix

theorem multi_encoding (F : MFamily) (n : ℕ) : F.encAt n=encNat (F.anc n)++
    encStr (((List.ofFn (F.outW n)).map Fin.val).map encNat)++encCirc (F.circ n) := by
  unfold MFamily.encAt
  simp only [bind_pure_comp]
  change encNat (F.anc n)++encStr (((List.ofFn (F.outW n)).map Fin.val).map encNat)++encCirc (F.circ n)=_
  rfl

@[fun_prop] theorem readFrame_poly : Poly readFrame := by unfold readFrame;fun_prop

theorem readFrame_correct (F : MFamily) (n : ℕ) :
    readFrame (unary n,F.encAt n)=
      (unary (oldWidth F n),
        ((List.ofFn (F.outW n)).map (fun wire => encNat wire.val),(F.circ n).map (List.map encInstr))) := by
  unfold readFrame
  rw [multi_encoding]
  simp only [List.append_assoc,readUnary_append,unaryPayload_encNat]
  rw [readWireWords_append]
  have hc := readCircuitLayers_append (F.circ n) []
  simp only [List.append_nil] at hc
  rw [hc,List.map_map]
  simp only [oldWidth,unary,List.replicate_add,List.append_assoc,List.replicate_one,Function.comp_def]

variable {f : Str → Str} (P : PolyProgram id id f)

end Integration9_9.LoadedBatch.PostComposition

end

end P2MDyadicModule129

/- Helper module Solutions.RegevBridgeQuantumXorGoodState. -/
section P2MDyadicModule130

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

noncomputable section

namespace InfoLossLAR.WorstCase.QuantumXorOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute

open ControlledNativeGates

open scoped BigOperators

variable {W k : ℕ}

def appendEmbedding (data : Bits k) : Bits W ↪ Bits (W+k) where
  toFun w := Fin.append w data
  inj' := by intro w v he;exact (CoherentXorCopy.append_eq_iff _ _ _ _).mp he |>.1

def attach (data : Bits k) : QState W →ₗ[ℂ] QState (W+k) := basisEmbedding (appendEmbedding data)

theorem attach_tensor (data : Bits k) (η : QState W) : attach data η=tensorState η (basis data) := by
  classical
  funext x
  obtain ⟨⟨w,d⟩,rfl⟩ := (qubitsAppendEquiv W k).symm.surjective x
  change attach data η (Fin.append w d)=tensorState η (basis data) (Fin.append w d)
  by_cases hd : d=data
  · subst d
    change basisEmbedding (appendEmbedding data) η (appendEmbedding data w)=_
    rw [basisEmbedding_at]
    have hl : leftRegister (Fin.append w data)=w := by funext i;exact Fin.append_left w data i
    have hr : rightRegister (Fin.append w data)=data := by funext i;exact Fin.append_right w data i
    rw [tensorState,hl,hr]
    simp [basis]
  · have ho : Fin.append w d∉Set.range (appendEmbedding data) := by
      rintro ⟨z,hz⟩
      have hh := (CoherentXorCopy.append_eq_iff _ _ _ _).mp hz
      exact hd hh.2.symm
    rw [attach,basisEmbedding_outside _ _ _ ho]
    have hl : leftRegister (Fin.append w d)=w := by funext i;exact Fin.append_left w d i
    have hr : rightRegister (Fin.append w d)=d := by funext i;exact Fin.append_right w d i
    rw [tensorState,hl,hr]
    simp [basis,hd]

theorem attach_norm (data : Bits k) (η : QState W) : stateNorm (attach data η)=stateNorm η :=
  basisEmbedding_norm _ _

theorem attach_error (data : Bits k) (η ζ : QState W) :
    stateNorm (attach data η-attach data ζ)=stateNorm (η-ζ) := by rw [←map_sub,attach_norm]

end InfoLossLAR.WorstCase.QuantumXorOracle

end

end P2MDyadicModule130

/- Helper module Solutions.RegevBridgeQuantumXorError. -/
section P2MDyadicModule131

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

end P2MDyadicModule131

/- Helper module FullSpaceBorn. -/
section P2MDyadicModule132

set_option autoImplicit false

set_option maxHeartbeats 1200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

open QAlgorithms QAlgorithms.Complexity QuantumXorOracle ControlledNativeGates CoherentDecoder

noncomputable section

theorem born_after {N : ℕ} (V : Layered N) (u v : QState N) (hu : stateNorm u=1) (hv : stateNorm v=1)
    (E : Bits N → Prop) :
    |bornEvent E (WithLp.toLp 2 (runLayered V u)) - bornEvent E (WithLp.toLp 2 (runLayered V v))| ≤ 2*stateNorm (u-v) := by
  apply (bornEvent_error_le E _ _).trans
  change stateNorm (runLayered V u - runLayered V v) * (stateNorm (runLayered V u)+stateNorm (runLayered V v)) ≤ _
  rw [run_error,show stateNorm (runLayered V u) = stateNorm u from (circuitIsometry V).norm_map _,
    show stateNorm (runLayered V v) = stateNorm v from (circuitIsometry V).norm_map _,hu,hv]
  linarith

end

end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

end P2MDyadicModule132

/- Helper module Solutions.RegevBridgeHilbertProjection. -/
section P2MDyadicModule133

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

end P2MDyadicModule133

/- Helper module Solutions.RegevBridgeNativeGaussianCosetPure. -/
section P2MDyadicModule134

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

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule134

/- Helper module Solutions.RegevBridgeFiniteHilbertEmbedding. -/
section P2MDyadicModule135

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

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule135

/- Helper module Solutions.RegevBridgeFiniteHilbertProjection. -/
section P2MDyadicModule136

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

end P2MDyadicModule136

/- Helper module ShortFourier. -/
section P2MDyadicModule137

set_option autoImplicit false

set_option maxHeartbeats 950000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection CoherentComputeUncompute GaussianProjection.CosetGeometry

open GaussianProjection GaussianLatticeTransport NativeDualQuotient

noncomputable section

variable {n M : ℕ} [NeZero M]

abbrev Color (n M : ℕ) := Fin n → ZMod M

def colorEmbedding (L : Submodule ℤ (PointSpace n)) (b : Module.Basis (Fin n) ℤ L) (R : ℝ)
    (hs : Separated L R) : Retained L M R ↪ Color n M where
  toFun p := publicCoordinates M L b p.val
  inj' := fun p q h => Subtype.ext (fineGrid_quotient_injective L b R hs p.property q.property h)

@[instance_reducible] def shortFintype (L : Submodule ℤ (PointSpace n)) (b : Module.Basis (Fin n) ℤ L) (R : ℝ) (hs : Separated L R) :
    Fintype (Retained L M R) := Fintype.ofInjective (colorEmbedding L b R hs) (colorEmbedding L b R hs).injective

theorem truncate_embed (L : Submodule ℤ (PointSpace n)) (b : Module.Basis (Fin n) ℤ L) (s R : ℝ)
    (hs : Separated L R) [Fintype (Retained L M R)] :
    (WithLp.toLp 2 (basisEmbedding (colorEmbedding (M:=M) L b R hs) (fun z =>
      (fineGridWeight (modulus:=M) s (z.val : PointSpace n) : ℂ))) : EuclideanSpace ℂ _) =
      truncatedState (modulus:=M) L b s R := by
  classical
  ext c
  let keep (p : L) := ‖fineGridPoint (modulus:=M) (p : PointSpace n)‖ < R
  let f := publicCoordinates M L b
  let emb := colorEmbedding (M:=M) L b R hs
  by_cases hc : c ∈ Set.range emb
  · obtain ⟨z,rfl⟩ := hc
    change basisEmbedding emb _ (emb z) = (truncatedAmplitude L b s R (emb z) : ℂ)
    rw [basisEmbedding_at]
    apply congrArg ((↑) : ℝ → ℂ)
    symm
    unfold truncatedAmplitude fiberMass
    rw [tsum_eq_single z.val]
    · rw [if_pos (show publicCoordinates M L b z.val = emb z from rfl)]
      exact if_pos z.property
    · intro p hp
      by_cases hr : keep p
      · have hne : f p ≠ emb z := fun he => hp (fineGrid_quotient_injective L b R hs hr z.property he)
        change (if f p = emb z then _ else 0) = 0
        rw [if_neg hne]
      · simp only [keep] at hr
        simp [hr]
  · change basisEmbedding emb _ c = (truncatedAmplitude L b s R c : ℂ)
    rw [basisEmbedding_outside emb _ c hc]
    have h0 : truncatedAmplitude L b s R c=0 := by
      unfold truncatedAmplitude fiberMass
      trans ∑' _p : L, (0 : ℝ)
      · apply tsum_congr
        intro p
        by_cases hr : keep p
        · have hne : f p ≠ c := fun he => hc ⟨⟨p,hr⟩,he⟩
          change (if f p = c then _ else 0) = 0
          rw [if_neg hne]
        · simp only [keep] at hr
          simp [hr]
      · simp
    simp [h0]

/-- Restricting the centered Gaussian on the scaled lattice gives precisely
the short Fourier amplitudes, including their common normalization factor. -/
theorem gamma_restrict (L : Submodule ℤ (PointSpace n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (s R : ℝ) (hs : 0<s) [Fintype (Retained L M R)] :
    finiteRestrict (fineEmbedding L M R) (gaussianHilbertState (fineLattice L M) (s/Real.sqrt 2) (by positivity) 0) =
    (Real.sqrt (rhoCoset (s/Real.sqrt 2) (fineLattice L M) 0))⁻¹ •
      (WithLp.toLp 2 (fun p : Retained L M R => (fineGridWeight (modulus:=M) s (p.val : PointSpace n) : ℂ)) : EuclideanSpace ℂ _) := by
  have hw : 2*(s/Real.sqrt 2)^2=s^2 := by rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
  ext p
  change (gaussianAmplitude (fineLattice L M) (s/Real.sqrt 2) 0 (fineEmbedding L M R p) : ℂ) = _
  rw [gaussianAmplitude,add_zero,hw]
  rw [show ((fineEmbedding L M R p : fineLattice L M) : PointSpace n) = fineGridPoint (modulus:=M) (p.val : PointSpace n) from rfl]
  simp only [fineGridWeight,rho,WithLp.ofLp_smul,WithLp.ofLp_toLp,Pi.smul_apply,
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_div]
  ring

def putColor {I J : Type} [Fintype I] [Fintype J] [DecidableEq J] (emb : I ↪ J)
    (v : EuclideanSpace ℂ I) : EuclideanSpace ℂ J := WithLp.toLp 2 (basisEmbedding emb v.ofLp)

theorem putColor_normalized {I J : Type} [Fintype I] [Fintype J] [DecidableEq J] (emb : I ↪ J)
    (v : EuclideanSpace ℂ I) : putColor emb (normalized v) = normalized (putColor emb v) := by
  have hn : ‖putColor emb v‖ = ‖v‖ := basisEmbedding_norm emb v.ofLp
  unfold normalized
  rw [hn]
  ext j
  change basisEmbedding emb (((‖v‖⁻¹ : ℝ) : ℂ) • v.ofLp) j = _
  rw [map_smul]
  rfl

theorem short_gamma_to_fourier (L : Submodule ℤ (PointSpace n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin n) ℤ L) (s R : ℝ) (hs : 0<s) (hsep : Separated L R) [Fintype (Retained L M R)] :
    putColor (colorEmbedding L b R hsep) (normalized (finiteRestrict (fineEmbedding L M R)
      (gaussianHilbertState (fineLattice L M) (s/Real.sqrt 2) (by positivity) 0))) =
    normalized (truncatedState (modulus:=M) L b s R) := by
  rw [gamma_restrict L s R hs,normalized_smul_pos _ (inv_pos.mpr (Real.sqrt_pos.mpr
    (rhoCoset_zero_pos (fineLattice L M) (s/Real.sqrt 2) (by positivity)))),putColor_normalized]
  exact congrArg normalized (truncate_embed L b s R hsep)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule137

/- Helper module GammaTruncate. -/
section P2MDyadicModule138

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

end P2MDyadicModule138

/- Helper module FiniteSupport. -/
section P2MDyadicModule139

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection GaussianProjection NativeDualQuotient

open RationalGramSchmidt

noncomputable section

variable {n M : ℕ} [NeZero M]

abbrev residualCap (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) : ℤ :=
  ⌈(originalDenominator B : ℝ)*dualColumnBudget B hB⌉

theorem residual_fit (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : Residual B) (i : Fin n) :
    |r.val i| ≤ residualCap B hB := by
  let D := (originalDenominator B : ℝ)
  have hD : 0<D := by dsimp [D]; exact_mod_cast denominator_pos (RationalInverse.Native.inputRows B)
  have hbound := nativeResidualShift_bound B hB 1 zero_lt_one r
  change ‖residuePoint B 1 r.val‖ ≤ _ at hbound
  rw [residuePoint_eq,one_mul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hD),div_one] at hbound
  have hf : ‖intVecE r.val‖ ≤ D*dualColumnBudget B hB := by
    change D⁻¹ * _ ≤ _ at hbound
    calc
      _ = D*(D⁻¹*‖intVecE r.val‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound hD.le
  have hi := PiLp.norm_apply_le (p:=2) (intVecE r.val) i
  change ‖(r.val i : ℝ)‖ ≤ _ at hi
  rw [Real.norm_eq_abs] at hi
  have hh := (hi.trans hf).trans (Int.le_ceil _)
  exact_mod_cast hh

def residualEmbedding (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) :
    Residual B ↪ (Fin n → ↥(Finset.Icc (-residualCap B hB) (residualCap B hB))) where
  toFun r i := ⟨r.val i,by simpa only [Finset.mem_Icc,←abs_le] using residual_fit B hB r i⟩
  inj' := by intro r s h; apply Subtype.ext; funext i; exact congrArg Subtype.val (congrFun h i)

@[instance_reducible] def residualFintype (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) : Fintype (Residual B) :=
  Fintype.ofInjective (residualEmbedding B hB) (residualEmbedding B hB).injective

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule139

/- Helper module SupportEmbedding. -/
section P2MDyadicModule140

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

variable {I P A J K : Type} [Fintype I] [Fintype P] [Fintype J] [DecidableEq A]
  (src : I ↪ A) (split : A ≃ J × K) (keep : P ↪ K)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule140

/- Helper module SparseOracle. -/
section P2MDyadicModule141

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1350000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

open CoherentComputeUncompute QAlgorithms QAlgorithms.Complexity QuantumXorOracle ControlledNativeGates

noncomputable section

variable {n l k a r : ℕ} {I : Type} [Fintype I]

theorem attached_basis {W : ℕ} (x : Bits W) (d : Bits k) :
    attach d (basis x) = basis (Fin.append x d) := by
  rw [attach_tensor]
  funext y
  obtain ⟨⟨z,t⟩,rfl⟩ := (qubitsAppendEquiv W k).symm.surjective y
  change (if (qubitsAppendEquiv W k ((qubitsAppendEquiv W k).symm (z,t))).1=x then 1 else 0)*
      (if (qubitsAppendEquiv W k ((qubitsAppendEquiv W k).symm (z,t))).2=d then 1 else 0) =
      if (qubitsAppendEquiv W k).symm (z,t)=(qubitsAppendEquiv W k).symm (x,d) then 1 else 0
  simp only [Equiv.apply_symm_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq]
  split_ifs <;> simp_all

end

end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

end P2MDyadicModule141

/- Helper module ShortQuery. -/
section P2MDyadicModule142

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries GaussianProjection NativeDualQuotient IntegerBasis

noncomputable section

variable {n M : ℕ} [NeZero M]

theorem coordinate_color (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℝ)
    (sep : Separated (dual (inputLattice B hB)) R) (p : Retained (dual (inputLattice B hB)) M R) :
    colorEmbedding _ (dualIntegerBasis B hB) _ sep p = fun i => (shortCoordinate B hB R p i : ZMod M) := by
  funext i
  change ((dualIntegerBasis B hB).repr p.val i : ZMod M) = _
  rw [dualIntegerBasis_repr]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule142

/- Helper module PoolMarginal. -/
section P2MDyadicModule143

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1450000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity SharedPoolCoherence CoherentProjection GaussianPoissonSeries GaussianProjection

open RegevLWE.GaussConv RegevSketch

noncomputable section

variable {n m : ℕ}

theorem failure_junk {T I : Type} [Fintype T] [Fintype I] (C : MFamily)
    (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (prec : ℕ) (pool : Fin m → Fin n → ℤ)
    (q : I → Query B R) (j : T → ℂ) (v : I → ℂ) (hj : ∑ t, ‖j t‖^2=1) :
    failureMass C prec pool (fun t : T × I => q t.2) (fun t => j t.1*v t.2) =
      failureMass C prec pool q v := by
  unfold failureMass
  simp only [Fintype.sum_prod_type,norm_mul,mul_pow,mul_assoc,←Finset.mul_sum,←Finset.sum_mul,hj,one_mul]

theorem residual_mass {R : Type} [Fintype R] (j : Hilbert R) (hj : ‖j‖=1) : ∑ r, ‖j r‖^2=1 := by
  have h := hilbert_norm_sq j
  simpa only [hj,one_pow,tsum_fintype] using h.symm

theorem short_mass {B : Matrix (Fin n) (Fin n) ℤ} (hB : B.det≠0) (M : ℕ) [NeZero M]
    (s R : ℝ) (hs : 0<s) (hR : 0<R) (hscale : (n:ℝ)*(s/Real.sqrt 2)^2 ≤ R^2)
    [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) M R)] :
    let L := dual (IntegerBasis.inputLattice B hB)
    let keep := fineEmbedding L M R
    let target := normalized (finiteRestrict keep (gaussianHilbertState (fineLattice L M) (s/Real.sqrt 2) (by positivity) 0))
    ∑ p, ‖target p‖^2 = 1 := by
  let L := dual (IntegerBasis.inputLattice B hB)
  let keep := fineEmbedding L M R
  have hu : 0<s/Real.sqrt 2 := by positivity
  let t := normalized (finiteRestrict keep (gaussianHilbertState (fineLattice L M) (s/Real.sqrt 2) hu 0))
  have h := (gamma_short (L:=L) (M:=M) (s/Real.sqrt 2) R hu hR hscale).2
  change ‖finiteEmbed keep t‖=1 at h
  rw [finiteEmbed_norm] at h
  change ∑ p, ‖t p‖^2=1
  rw [←EuclideanSpace.norm_sq_eq t,h,one_pow]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule143

/- Helper module OracleTable. -/
section P2MDyadicModule144

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.OracleTable

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2PlatformSerialization Integration9_9.TM2StockLists QMCNumericRuntime

open Integration9_9.LARPlatformEncoding (readS_poly readS_rest_length readBinaryList_poly)

noncomputable section

@[fun_prop] theorem unpack_poly : Poly unpack := readBinaryList_poly _ readS_poly readS_rest_length

@[fun_prop] theorem lookup_poly : Poly lookup := by unfold lookup;fun_prop

end

end InfoLossLAR.WorstCase.RegevSearch.OracleTable

end P2MDyadicModule144

/- Helper module Solutions.RegevBridgeNativeQFTPlan. -/
section P2MDyadicModule145

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeQFTPlan

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

@[fun_prop] theorem hCode_poly : Poly hCode := by unfold hCode emptyRequest;fun_prop

@[fun_prop] theorem cnotCode_poly : Poly (fun x : ℕ × ℕ => cnotCode x.1 x.2) := by
  unfold cnotCode emptyRequest
  fun_prop

@[fun_prop] theorem phaseCode_poly : Poly (fun x : ℕ × NativePhaseTaylor.QFTRequest => phaseCode x.1 x.2) := by
  unfold phaseCode
  fun_prop

@[fun_prop] theorem request_poly : Poly (fun x : Input × (ℕ × Bool) => request x.1 x.2.1 x.2.2) := by
  have ht : Poly (fun x : Input × (ℕ × Bool) => x.1.1.take x.2.1) :=
    Poly.comp (f := fun x : List Unit × ℕ => x.1.take x.2)
      (g := fun x : Input × (ℕ × Bool) => (x.1.1,x.2.1)) parser_take_poly (by fun_prop)
  unfold request
  fun_prop

@[fun_prop] theorem interaction_poly : Poly interaction := by unfold interaction;fun_prop

@[fun_prop] theorem indices_poly : Poly indices := by
  have hr : Poly (fun input : Input => List.range input.1.length) :=
    Poly.comp (f := fun ticks : List Unit => List.range ticks.length) (g := fun input : Input => input.1)
      Poly.list_indices (by fun_prop)
  unfold indices
  exact Poly.comp parser_reverse_poly hr

@[fun_prop] theorem rowPlan_poly : Poly rowPlan := by unfold rowPlan;fun_prop

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

end InfoLossLAR.WorstCase.NativeQFTPlan

end P2MDyadicModule145

/- Helper module Solutions.RegevBridgeNativeQFTPlanCompile. -/
section P2MDyadicModule146

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeQFTPlan FiniteGateTransport FiniteGateNative

@[fun_prop] theorem automaticInput_poly : Poly automaticInput := by unfold automaticInput;fun_prop

theorem compileCode_poly (a : ℕ) : Poly (compileCode a) := by
  have hw : Poly (fun x : List Unit × NativeQFTPlan.Instruction =>
      NativePhaseGates.automatic a (automaticInput x)) := Poly.comp (NativePhaseGates.automatic_poly a) automaticInput_poly
  unfold compileCode
  fun_prop

@[fun_prop] theorem plan_poly : Poly plan := by
  unfold plan
  exact Poly.comp NativeQFTPlan.current_poly (by fun_prop)

theorem current_poly (a : ℕ) : Poly (current a) := by
  have hcode : Poly (fun x : Input × NativeQFTPlan.Instruction => compileCode a (x.1.2,x.2)) :=
    Poly.comp (compileCode_poly a) (by fun_prop)
  unfold current
  exact Poly.list_map hcode plan_poly

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end P2MDyadicModule146

/- Helper module AxisFourier. -/
section P2MDyadicModule147

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

noncomputable section

variable {b : ℕ}

theorem binary_cast (x : Bits b) : binary b x = ((ShorAlgorithms.QFT.bitsVal (finBits x) : ℕ) : ZMod (2^b)) := by
  let z := finFunctionFinEquiv (finBits x)
  have hval : z.val=ShorAlgorithms.QFT.bitsVal (finBits x) := by
    simp [z,ShorAlgorithms.QFT.bitsVal,Nat.mul_comm]
  rw [←hval]
  change (ZMod.finEquiv (2^b)) z = (z.val : ZMod (2^b))
  have hcoe (m : ℕ) [NeZero m] (k : Fin m) : (ZMod.finEquiv m) k = (k.val : ZMod m) := by
    cases m with
    | zero => exact Fin.elim0 k
    | succ m => exact (Fin.cast_val_eq_self k).symm
  exact hcoe _ _

end

end GridReadout.Axis

end P2MDyadicModule147

/- Helper module GridNorm. -/
section P2MDyadicModule148

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

noncomputable section

variable {n b : ℕ}

def rowsEquiv (b n : ℕ) : Bits (n*b) ≃ Rows b n where
  toFun y i k := y (finProdFinEquiv (i,k))
  invFun v p := v (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  left_inv y := by funext i; exact congrArg y (finProdFinEquiv.apply_symm_apply i)
  right_inv v := by funext i k; simp

def layout (b n : ℕ) : Bits (n*b+2) ≃ Rows b n × Bits 2 := (qubitsAppendEquiv (n*b) 2).trans
  ((rowsEquiv b n).prodCongr (Equiv.refl _))

theorem liftBorn (E : Rows b n → Prop) (v : Rows b n → ℂ) :
    bornEvent (fun y => E (rows y)) (WithLp.toLp 2 (liftRows v)) = bornEvent E (WithLp.toLp 2 v) := by
  unfold bornEvent
  trans ∑ p : Rows b n × Bits 2, if E p.1 then ‖(if p.2=0 then v p.1 else 0:ℂ)‖^2 else 0
  · apply Fintype.sum_equiv (layout b n)
    intro x; rfl
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : E x
  · simp [he,apply_ite]
  · simp [he]

theorem liftNorm (v : Rows b n → ℂ) :
    ‖(WithLp.toLp 2 (liftRows v) : EuclideanSpace ℂ _)‖ = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ _)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [bornEvent,if_true,EuclideanSpace.norm_sq_eq] using liftBorn (fun _ => True) v

end

end GridReadout.Axis

end P2MDyadicModule148

/- Helper module Outcome. -/
section P2MDyadicModule149

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

open CoherentProjection GaussianPoissonSeries FiniteLatticeFourier IntegerBasis RegevLWE.GaussConv

noncomputable section

variable {n b : ℕ}

theorem reindex_norm {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (v : EuclideanSpace ℂ Y) :
    ‖reindex e v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem normalized_reindex {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (v : EuclideanSpace ℂ Y) :
    normalized (reindex e v) = reindex e (normalized v) := by
  unfold normalized
  rw [reindex_norm]
  rfl

end

end GridReadout.Axis

end P2MDyadicModule149

/- Helper module SignedProgram. -/
section P2MDyadicModule150

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 QMCNumericRuntime

noncomputable section

theorem tape_value {b : ℕ} (t : Bits b) :
    bitValue (List.ofFn t) = ShorAlgorithms.QFT.bitsVal (finBits t) := by
  induction b with
  | zero => simp [bitValue,ShorAlgorithms.QFT.bitsVal]
  | succ b ih =>
    simp only [List.ofFn_succ,bitValue,ShorAlgorithms.QFT.bitsVal,Fin.sum_univ_succ,Fin.val_zero,pow_zero,one_mul,Fin.val_succ]
    rw [ih]
    unfold ShorAlgorithms.QFT.bitsVal
    rw [Finset.mul_sum]
    congr 1
    · cases h:t 0 <;> simp [finBits,h]
    · apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      change 2 * (2 ^ i.val * (finBits t i.succ).val) = _
      ring

end

end GridReadout.Axis

end P2MDyadicModule150

/- Helper module Modulus. -/
section P2MDyadicModule151

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout

open InfoLossLAR.WorstCase RegevSearch

variable {n : ℕ}

theorem cofactor_height (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hB : ∀ i j, |B i j| ≤ (2:ℤ)^H) :
    cofactorSum B ≤ 2^(2*n+(n+H)*n) := by
  have h (i j : Fin n) : (B.adjugate i j).natAbs ≤ 2^((n+H)*n) := by
    have ha : |B.adjugate i j| ≤ (2:ℤ)^((n+H)*n) := by
      rw [Matrix.adjugate_apply]
      apply RationalInverse.determinant_binary_bound _ H
      intro a b
      rw [Matrix.updateRow_apply]
      split_ifs
      · simp only [Pi.single_apply]
        split_ifs <;> simp
        exact one_le_pow₀ (by norm_num : (1:ℤ)≤2)
      · exact hB _ _
    have h' : ((B.adjugate i j).natAbs : ℤ) ≤ (2:ℤ)^((n+H)*n) := by simpa only [Int.natCast_natAbs] using ha
    exact_mod_cast h'
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, 2^((n+H)*n) := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = n*(n*2^((n+H)*n)) := by simp
    _ ≤ 2^n*(2^n*2^((n+H)*n)) :=
      Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le)
    _ = 2^(2*n+(n+H)*n) := by rw [←mul_assoc,←pow_add,←pow_add]; congr 1; omega

theorem dyadic_adequate (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (H K : ℕ)
    (hB : ∀ i j, |B i j| ≤ (2:ℤ)^H) (hr : ⌈r⌉₊ ≤ 2^K) :
    gridAdequate B r (2^(gridBits n H K)) := by
  let A := 2*n+(n+H)*n
  have hA : cofactorSum B+1 ≤ 2^(A+1) := by
    have h := cofactor_height B H hB
    change cofactorSum B ≤ 2^A at h
    rw [pow_succ]; have := Nat.one_le_pow A 2 (by decide); omega
  have hK : ⌈r⌉₊ + 1 ≤ 2^(K+1) := by rw [pow_succ]; have := Nat.one_le_pow K 2 (by decide); omega
  change 4*(cofactorSum B+1)*(n+1)*(⌈r⌉₊+1) ≤ (2:ℕ)^(2+(A+1)+n+(K+1))
  calc
    _ ≤ 2^2 * 2^(A+1) * 2^n * 2^(K+1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hA) Nat.lt_two_pow_self) hK
    _ = _ := by simp only [pow_add]

end GridReadout

end P2MDyadicModule151

/- Helper module QFTJunk. -/
section P2MDyadicModule152

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity CoherentDecoder ControlledNativeGates

open NativeQFTPlanCompile GridReadout.Axis

noncomputable section

theorem marginal_product {w c : ℕ} (u : QState w) (j : QState c) (hj : stateNorm j = 1) (E : Bits w → Prop) :
    bornEvent (fun p : Bits (w+c) => E (leftRegister p)) (WithLp.toLp 2 (tensorState u j)) =
      bornEvent E (WithLp.toLp 2 u) := by
  have hn : (∑ v, ‖j v‖^2)=1 := by
    have he := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 j : EuclideanSpace ℂ (Bits c))
    simpa only [show ‖(WithLp.toLp 2 j : EuclideanSpace ℂ (Bits c))‖=1 from hj,one_pow] using he.symm
  unfold bornEvent
  trans ∑ xy : Bits w × Bits c, if E xy.1 then ‖u xy.1 * j xy.2‖^2 else 0
  · apply Fintype.sum_equiv (qubitsAppendEquiv w c); intro _; rfl
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  by_cases he : E v
  · simp only [if_pos he,norm_mul,mul_pow,←Finset.mul_sum,hn,mul_one]
  · simp [he]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule152

/- Helper module ShortReadout. -/
section P2MDyadicModule153

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1150000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity CoherentDecoder ControlledNativeGates NativeQFTPlanCompile GridReadout.Axis

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection GaussianProjection IntegerBasis

noncomputable section

variable {n b : ℕ}

def framedColor (v : EuclideanSpace ℂ (Color n (2^b))) : QState (n*b+2) :=
  liftRows (reindex (rowInput b n) v).ofLp

theorem framedColor_norm (v : EuclideanSpace ℂ (Color n (2^b))) :
    stateNorm (framedColor v) = ‖v‖ :=
  (liftNorm _).trans (reindex_norm _ _)

theorem framedColor_error (v w : EuclideanSpace ℂ (Color n (2^b))) :
    stateNorm (framedColor v - framedColor w) = ‖v-w‖ := by
  rw [←framedColor_norm (v-w)]
  congr 1
  funext y
  by_cases hy : anc n b y = 0 <;> simp [framedColor,liftRows,hy,reindex]

theorem truncated_ne (L : Submodule ℤ (PointSpace n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (bs : Module.Basis (Fin n) ℤ L) (s R : ℝ) (hs : 0<s) (hR : 0<R) (hn : 0<n)
    (hscale : (n:ℝ)*s^2 ≤ R^2) (hsep : Separated L R) :
    truncatedState (modulus:=2^b) L bs s R ≠ 0 := by
  have hlow := truncatedState_norm_sq_lower (modulus:=2^b) L bs s R hs hR.le hscale hsep
  have hm := rhoCoset_zero_pos L (((2^b:ℕ):ℝ)*(s/Real.sqrt 2)) (by positivity)
  have hq := quarter_pow_le_quarter hn
  have hp : 0 < (1-(1/4:ℝ)^n)*rhoCoset (((2^b:ℕ):ℝ)*(s/Real.sqrt 2)) L 0 := mul_pos (by linarith) hm
  intro h
  rw [h,norm_zero,zero_pow (by decide),] at hlow
  exact (not_lt_of_ge hlow) hp

theorem short_frame_distance
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (r R : ℝ) (hr : 0<r) (hR : 0<R) (hn : 0<n)
    (hscale : (n:ℝ)*(1/(Real.sqrt 2*r))^2 ≤ R^2) (hsep : Separated (dual (inputLattice B hB)) R) :
    let t := normalized (truncatedState (modulus:=2^b) (dual (inputLattice B hB)) (dualIntegerBasis B hB) (1/(Real.sqrt 2*r)) R)
    stateNorm (framedColor t)=1 ∧
    stateNorm (framedColor t-liftRows (inputState (dualInput (b:=b) B hB r)).ofLp) ≤ 2*Real.sqrt (2*(1/2:ℝ)^n) := by
  dsimp only
  constructor
  · rw [framedColor_norm,normalized_norm _ (truncated_ne _ _ _ _ (by positivity) hR hn hscale hsep)]
  · rw [GridReadout.Axis.inputState,normalized_reindex]
    change stateNorm (framedColor _-framedColor _) ≤ _
    rw [framedColor_error,norm_sub_rev]
    exact normalized_periodized_truncated_close _ _ _ _ (by positivity) hR hn hscale hsep

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule153

/- Helper module ErasedLayout. -/
section P2MDyadicModule154

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open CoherentComputeUncompute QAlgorithms QAlgorithms.Complexity CoherentDecoder ControlledNativeGates GridReadout.Axis

open RegevLWE.GaussConv GaussianPoissonSeries NativeDualQuotient

noncomputable section

variable {n b w γ : ℕ}

def framedBits (n b : ℕ) : Color n (2^b) ↪ Bits (n*b+2) where
  toFun c := (layout b n).symm ((rowInput b n).symm c,0)
  inj' _ _ h := (rowInput b n).symm.injective (congrArg Prod.fst ((layout b n).symm.injective h))

theorem framed_embed (v : EuclideanSpace ℂ (Color n (2^b))) :
    basisEmbedding (framedBits n b) v.ofLp = framedColor v := by
  funext x
  let c := rowInput b n (rows x)
  have hx : layout b n x=(rows x, anc n b x) := rfl
  by_cases h : anc n b x=0
  · have he : framedBits n b c=x := by
      apply (layout b n).injective
      change (layout b n) ((layout b n).symm (_,0)) = _
      rw [Equiv.apply_symm_apply,hx,h,Equiv.symm_apply_apply]
    rw [←he,basisEmbedding_at,he]
    simp [framedColor,liftRows,h,reindex,c]
  · have hn : x ∉ Set.range (framedBits n b) := by
      rintro ⟨z,hz⟩
      have := congrArg (fun t : Bits (n*b+2) => (layout b n t).2) hz
      change ((layout b n) ((layout b n).symm (_,0))).2 = anc n b x at this
      rw [Equiv.apply_symm_apply] at this
      exact h this.symm
    rw [basisEmbedding_outside _ _ x hn]
    simp [framedColor,liftRows,h]

def erasedBits {P J : Type} (data : P ↪ Bits w) (junk : J ↪ Bits γ) : J×P ↪ Bits (w+γ) where
  toFun t := (qubitsAppendEquiv w γ).symm (data t.2,junk t.1)
  inj' _ _ h := by
    have hh := (qubitsAppendEquiv w γ).symm.injective h
    exact Prod.ext (junk.injective (congrArg (fun p : Bits w × Bits γ => p.2) hh))
      (data.injective (congrArg (fun p : Bits w × Bits γ => p.1) hh))

theorem erased_tensor {P J : Type} [Fintype P] [Fintype J] (data : P ↪ Bits w) (junk : J ↪ Bits γ)
    (v : P → ℂ) (j : J → ℂ) :
    basisEmbedding (erasedBits data junk) (fun t => j t.1*v t.2) =
    tensorState (basisEmbedding data v) (basisEmbedding junk j) := by
  funext x
  obtain ⟨⟨c,y⟩,rfl⟩ := (qubitsAppendEquiv w γ).symm.surjective x
  let a := @qubitsAppendEquiv w γ
  change basisEmbedding (erasedBits data junk) _ (a.symm (c,y)) =
    basisEmbedding data v (a (a.symm (c,y))).1 * basisEmbedding junk j (a (a.symm (c,y))).2
  rw [a.apply_symm_apply]
  by_cases hc : c ∈ Set.range data
  · obtain ⟨p,rfl⟩ := hc
    by_cases hy : y ∈ Set.range junk
    · obtain ⟨r,rfl⟩ := hy
      rw [basisEmbedding_at data,basisEmbedding_at junk,←mul_comm]
      exact basisEmbedding_at (erasedBits data junk) _ (r,p)
    · rw [basisEmbedding_outside junk _ _ hy,mul_zero,basisEmbedding_outside]
      rintro ⟨t,e⟩
      exact hy ⟨t.1,congrArg (fun z : Bits w × Bits γ => z.2) (a.symm.injective e)⟩
  · rw [basisEmbedding_outside data _ _ hc,zero_mul,basisEmbedding_outside]
    rintro ⟨t,e⟩
    exact hc ⟨t.2,congrArg (fun z : Bits w × Bits γ => z.1) (a.symm.injective e)⟩

theorem erased_short_tensor {J : Type} [Fintype J] (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (s R : ℝ)
    (hs : 0<s) (hsep : Separated (dual (IntegerBasis.inputLattice B hB)) R)
    [Fintype (Retained (dual (IntegerBasis.inputLattice B hB)) (2^b) R)] (je : J ↪ Bits γ) (j : J → ℂ) :
    let L := dual (IntegerBasis.inputLattice B hB)
    let bs := IntegerBasis.dualIntegerBasis B hB
    let c := colorEmbedding (M:=2^b) L bs R hsep
    let v := CoherentProjection.normalized (finiteRestrict (fineEmbedding L (2^b) R)
      (gaussianHilbertState (fineLattice L (2^b)) (s/Real.sqrt 2) (by positivity) 0))
    basisEmbedding (erasedBits (c.trans (framedBits n b)) je) (fun t => j t.1*v t.2) =
    tensorState (framedColor (CoherentProjection.normalized (truncatedState (modulus:=2^b) L bs s R))) (basisEmbedding je j) := by
  dsimp only
  rw [erased_tensor,←basis_comp]
  rw [←short_gamma_to_fourier _ _ _ _ hs hsep,←framed_embed]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule154

/- Helper module SignedShortReadout. -/
section P2MDyadicModule155

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity CoherentDecoder ControlledNativeGates NativeQFTPlanCompile GridReadout.Axis

open RegevLWE.GaussConv GaussianPoissonSeries CoherentComputeUncompute IntegerBasis

noncomputable section

/-- The actual signed QFT maps the cleanly erased finite Gaussian reference
to the coefficient PMF, up to an explicit finite-grid, tail, and gate error.
The input discrepancy and every entangled garbage wire are accounted for. -/
theorem signed_short_readout : ∃ a : ℕ, 0<a ∧ ∀ (nt : List Unit) (x : Input) (γ : ℕ)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (hB : B.det≠0) (r R : ℝ) (hr : 0<r) (hR : 0<R)
    (hn : 0<nt.length) (hadequate : gridAdequate B r (2^x.1.length))
    (hscale : (nt.length:ℝ)*(1/(Real.sqrt 2*r))^2 ≤ R^2)
    (hsep : Separated (dual (inputLattice B hB)) R)
    (k : ℕ) (_hk : precision nt.length x.1.length k ≤ x.2.length)
    [Fintype (Retained (dual (inputLattice B hB)) (2^x.1.length) R)]
    (J : Type) [Fintype J] (je : J ↪ Bits γ) (j : J → ℂ) (_hj : ∑ t, ‖j t‖^2 = 1)
    (actual : QState (nt.length*x.1.length+2+γ)) (_ha : stateNorm actual = 1),
    let L := dual (inputLattice B hB)
    let s := 1/(Real.sqrt 2*r)
    let c := colorEmbedding (M:=2^x.1.length) L (dualIntegerBasis B hB) R hsep
    let target := CoherentProjection.normalized (finiteRestrict (fineEmbedding L (2^x.1.length) R)
      (gaussianHilbertState (fineLattice L (2^x.1.length)) (s/Real.sqrt 2) (by dsimp [s]; positivity) 0))
    let ideal := basisEmbedding (erasedBits (c.trans (framedBits nt.length x.1.length)) je) (fun t => j t.1*target t.2)
    let U := circuit a x (List.finRange nt.length)
    let u := WithLp.toLp 2 (runLayered (leftCircuit (m:=γ) U) actual)
    let emit := fun p : Bits (nt.length*x.1.length+2+γ) => encodeSlices (nt,x.1,List.ofFn (leftRegister p : Bits (nt.length*x.1.length+2)))
    bornEvent (fun p => ∃ z : Fin nt.length → ℤ, encVec encI z <+: emit p) u = 1 ∧
    ∀ T : Finset (Fin nt.length → ℤ),
      |bornEvent (fun p => ∃ z ∈ T, encVec encI z <+: emit p) u - ∑ z ∈ T, RegevSketch.coefficientMass B r z| ≤
      2*stateNorm (actual-ideal) + 4*Real.sqrt (2*(1/2:ℝ)^nt.length) + 1/(4*((k:ℝ)+1))+GridReadout.gridError nt.length := by
  obtain ⟨a,ha,h⟩ := signed_qft_joint
  refine ⟨a,ha,?_⟩
  intro nt x γ B hB r R hr hR hn had hscale hsep k hk _ J _ je j hj actual hactual
  dsimp only
  rw [erased_short_tensor B hB _ _ (by positivity) hsep je j]
  let L := dual (inputLattice B hB)
  let frame := framedColor (CoherentProjection.normalized (truncatedState (modulus:=2^x.1.length)
    L (dualIntegerBasis B hB) (1/(Real.sqrt 2*r)) R))
  have hshort := short_frame_distance (b:=x.1.length) B hB r R hr hR hn hscale hsep
  have hnorm : stateNorm (basisEmbedding je j)=1 := by
    have hmass := basisEmbedding_mass je j
    rw [hj,←EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (basisEmbedding je j) : EuclideanSpace ℂ _)] at hmass
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (hmass.trans (one_pow 2).symm)
  have result := h nt x γ B hB r hr k hk frame hshort.1 _ hnorm actual hactual
  refine ⟨result.1,?_⟩
  intro T
  have hbound := InfoLossLAR.WorstCase.RegevSearch.finite_grid_fourier_gaussian_event_bound B hB r hr hn had T
  apply (abs_sub_le _ (fourierEvent B r (2^x.1.length) T) _).trans
  apply add_le_add _ hbound
  apply (result.2 T).trans
  have hs := hshort.2
  change stateNorm (frame - _) ≤ _ at hs
  change 2*stateNorm (actual-tensorState frame (basisEmbedding je j)) + 2*stateNorm (frame-_) + _ ≤
    2*stateNorm (actual-tensorState frame (basisEmbedding je j)) + _ + _
  linarith

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule155

/- Helper module Realize. -/
section P2MDyadicModule156

set_option autoImplicit false

set_option maxHeartbeats 2200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2NativeAffineEmitter

open Integration9_9.LARPlatformEncoding (readS_append)

open CoherentComputeUncompute

theorem inverse_emitted (s : Source) (width : List Unit) (tail : Str)
    (hfit : (serializeVector (answers ((setup s.1.1.1).1.1,s.2))).length ≤ (setup s.1.1.1).1.2.1.length) :
    inverse (emit (width,s) ++ tail)=NativePaddedWords.current (width,pack s) := by
  rcases s with ⟨⟨⟨h,t⟩,B,r⟩,z⟩
  let c := setup h
  let a := answers (c.1.1,z)
  let q := request ((c,B),z)
  let words := blocks (c.1.1,z)
  have ha : (readVector (NativePaddedWords.current (c.1.2.1,serializeVector a))).2=a := by
    rw [NativePaddedWords.current_eq _ _ hfit]
    exact congrArg Prod.snd (NativePaddedWords.readVector_serialized a _)
  have hr : restore ((c.1.1,words),a)=z := by simpa [words,a] using restore_blocks c.1.1 z []
  dsimp only [inverse,skipU,skipS,firstS,vec,takeWord,dropWord,emit,outHead]
  simp only [List.append_assoc,lengthToken_eq,unarySlots_append,readUnary_append,readS_append,
    units_exact,List.length_replicate]
  change NativePaddedWords.current (width,pack (((h,t),(B,_)),_))=_
  rw [cut_append _ _ _ (blocks_length c.1.1 z)]
  dsimp only
  rw [cut_append _ _ _ (NativePaddedWords.current_length c.1.2.1 (serializeVector a))]
  dsimp only
  rw [cut_append _ _ _ (NativePaddedWords.current_length c.1.2.2 q)]
  dsimp only
  rw [ha,hr,readS_append]

theorem forward_padded (s : Source) (width : List Unit) (hwidth : (pack s).length≤width.length) :
    forward (NativePaddedWords.current (width,pack s))=emit (width,s) := by
  unfold forward
  have ht : ticks (NativePaddedWords.current (width,pack s))=width := by
    rw [←units_exact (ticks _),ticks_length,NativePaddedWords.current_length,units_exact]
  rw [ht,NativePaddedWords.current_eq _ _ hwidth,unpack_pack]

noncomputable def forwardProgram : PolyProgram id id forward :=
  Integration9_9.LARCoinLayout.rawPolyProgram forward_poly

noncomputable def inverseProgram : PolyProgram id id inverse :=
  Integration9_9.LARCoinLayout.rawPolyProgram inverse_poly

theorem left_inverse (s : Source) (width : List Unit)
    (hwidth : (pack s).length≤width.length)
    (hfit : (serializeVector (answers ((setup s.1.1.1).1.1,s.2))).length ≤ (setup s.1.1.1).1.2.1.length) :
    inverse (CoherentClassicalOracle.paddedOutput forwardProgram (NativePaddedWords.current (width,pack s))) =
      NativePaddedWords.current (width,pack s) := by
  change inverse (TM2Boolean.PolyProgramCircuit.paddedOutput forwardProgram _)=_
  rw [TM2Boolean.PolyProgramCircuit.paddedOutput_eq_append,forward_padded s width hwidth]
  exact inverse_emitted s width _ hfit

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule156

/- Helper module CodecMatch. -/
section P2MDyadicModule157

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

theorem row_bits_match (bt : List Unit) (z : ℤ) :
    List.ofFn ((binary bt.length).symm (z : ZMod (2^bt.length))) = NativeFixedResidue.current (bt,z) := by
  let t := (binary bt.length).symm (z : ZMod (2^bt.length))
  apply NativeFixedBits.bitValue_injective_length
  · simp
  · rw [NativeFixedResidue.current_value,NativeFixedResidue.modulus_eq]
    have he := binary_cast t
    have he' : binary bt.length t = (z : ZMod (2^bt.length)) := Equiv.apply_symm_apply _ _
    rw [he',←tape_value] at he
    have hm : 0 < (2^bt.length:ℕ) := pow_pos (by decide) _
    have hlt : bitValue (List.ofFn t) < 2^bt.length := by simpa using NativeFixedBits.bitValue_bound (List.ofFn t)
    have hh := congrArg ZMod.val he
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt hlt] at hh
    rw [←ZMod.val_intCast,Int.toNat_natCast]
    exact hh.symm

theorem physical_rows (bt : List Unit) (z : Fin n → ℤ) :
    List.ofFn (framedBits n bt.length (fun i => (z i : ZMod (2^bt.length)))) =
      blocks (bt,List.ofFn z) ++ [false,false] := by
  let data := fun i : Fin n => (binary bt.length).symm (z i : ZMod (2^bt.length))
  let row := (rowsEquiv bt.length n).symm data
  change List.ofFn (Fin.append row (fun _ : Fin 2 => false)) = _
  rw [List.ofFn_fin_append,show List.ofFn (fun _ : Fin 2 => false) = [false,false] from rfl]
  apply congrArg (fun w : Str => w ++ [false,false])
  rw [List.ofFn_mul,blocks,List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [←row_bits_match]
  apply congrArg List.ofFn
  funext j
  let idx := finProdFinEquiv (i,j)
  have he : (⟨i.val*bt.length+j.val,by nlinarith [j.isLt,Nat.mul_le_mul_right bt.length i.isLt]⟩ : Fin (n*bt.length)) = idx := by
    apply Fin.ext
    change i.val*bt.length+j.val=j.val+bt.length*i.val
    ring
  rw [he]
  change data (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = _
  rw [Equiv.symm_apply_apply]

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

end P2MDyadicModule157

/- Helper module OraclePlacement. -/
section P2MDyadicModule158

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute

noncomputable section

def relabel {p N : ℕ} (e : Fin p ≃ Fin N) (v : QState p) : QState N := v ∘ wirePull e

theorem relabel_error {p N : ℕ} (e : Fin p ≃ Fin N) (v w : QState p) :
    stateNorm (relabel e v-relabel e w)=stateNorm (v-w) :=
  GridReadout.Axis.reindex_norm (wirePull e) (WithLp.toLp 2 (v-w))

theorem relabel_emb {p N : ℕ} {I : Type} [Fintype I] (e : Fin p ≃ Fin N) (f : I ↪ Bits p) (v : I→ℂ) :
    relabel e (basisEmbedding f v) = basisEmbedding (f.trans (wirePull e).symm.toEmbedding) v := by
  funext x
  obtain ⟨t,rfl⟩ := (wirePull e).symm.surjective x
  change basisEmbedding f v ((wirePull e) ((wirePull e).symm t))=_
  rw [Equiv.apply_symm_apply]
  by_cases ht : t ∈ Set.range f
  · obtain ⟨i,rfl⟩ := ht
    exact (basisEmbedding_at f v i).trans (basisEmbedding_at (f.trans (wirePull e).symm.toEmbedding) v i).symm
  · rw [basisEmbedding_outside f v t ht,basisEmbedding_outside]
    rintro ⟨i,h⟩
    exact ht ⟨i,(wirePull e).symm.injective h⟩

theorem relabel_run {p N : ℕ} (e : Fin p ≃ Fin N) (U : Layered p) (v : QState p) :
    runLayered (relocateCircuit e.toEmbedding U) (relabel e v) = relabel e (runLayered U v) := by
  funext x
  let w := e.toEmbedding
  let t := wireBitsEquiv w x
  have he := congrFun (relocateCircuit_split w U (relabel e v)) t
  have hy : (fun y => splitState w (relabel e v) (y,t.2))=v := by
    funext y
    change v (((wireBitsEquiv w).symm (y,t.2)) ∘ e)=v y
    apply congrArg v
    exact congrArg Prod.fst ((wireBitsEquiv w).apply_symm_apply (y,t.2))
  rw [hy] at he
  change runLayered (relocateCircuit w U) (relabel e v) ((wireBitsEquiv w).symm ((wireBitsEquiv w) x))= runLayered U v t.1 at he
  rw [Equiv.symm_apply_apply] at he
  exact he

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule158

/- Helper module SerializedOracle. -/
section P2MDyadicModule159

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic ControlledNativeCode

noncomputable section

variable {H K L J A : ℕ}

def serializedBits (front : Bits H) (d : Bits K) (x : Bits L) (rear : Bits J) (work : Bits A) :
    Bits (H+K+L+J+A) := Fin.append (Fin.append (Fin.append (Fin.append front d) x) rear) work

theorem sampled_bits (front : Bits H) (d : Bits K) (x : Bits L) (rear : Bits J) (work : Bits A) :
    wirePull (oraclePerm H K L J A) (serializedBits front d x rear work) =
    Fin.append (Fin.append (Fin.append x work) d) (Fin.append front rear) := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        have h : (oraclePerm H K L J A) (((i.castAdd A).castAdd K).castAdd (H+J)) =
            ((i.natAdd (H+K)).castAdd J).castAdd A := by
          apply Fin.ext;simp [oraclePerm,i.isLt]
        change serializedBits _ _ _ _ _ ((oraclePerm H K L J A) _) = _
        simp only [h,serializedBits,Fin.append_left,Fin.append_right]
      | right i =>
        have h : (oraclePerm H K L J A) (((i.natAdd L).castAdd K).castAdd (H+J)) = i.natAdd (H+K+L+J) := by
          apply Fin.ext;simp only [oraclePerm,Equiv.coe_fn_mk,Fin.val_castAdd,Fin.val_natAdd];split_ifs <;> omega
        change serializedBits _ _ _ _ _ ((oraclePerm H K L J A) _) = _
        simp only [h,serializedBits,Fin.append_left,Fin.append_right]
    | right i =>
      have h : (oraclePerm H K L J A) ((i.natAdd (L+A)).castAdd (H+J)) =
          (((i.natAdd H).castAdd L).castAdd J).castAdd A := by
        apply Fin.ext;simp only [oraclePerm,Equiv.coe_fn_mk,Fin.val_castAdd,Fin.val_natAdd];split_ifs <;> omega
      change serializedBits _ _ _ _ _ ((oraclePerm H K L J A) _) = _
      simp only [h,serializedBits,Fin.append_left,Fin.append_right]
  | right i =>
    induction i using Fin.addCases with
    | left i =>
      have h : (oraclePerm H K L J A) ((i.castAdd J).natAdd (L+A+K)) =
          (((i.castAdd K).castAdd L).castAdd J).castAdd A := by
        apply Fin.ext;simp only [oraclePerm,Equiv.coe_fn_mk,Fin.val_castAdd,Fin.val_natAdd];split_ifs <;> omega
      change serializedBits _ _ _ _ _ ((oraclePerm H K L J A) _) = _
      simp only [h,serializedBits,Fin.append_left,Fin.append_right]
    | right i =>
      have h : (oraclePerm H K L J A) ((i.natAdd H).natAdd (L+A+K)) =
          (i.natAdd (H+K+L)).castAdd A := by
        apply Fin.ext;simp only [oraclePerm,Equiv.coe_fn_mk,Fin.val_castAdd,Fin.val_natAdd];split_ifs <;> omega
      change serializedBits _ _ _ _ _ ((oraclePerm H K L J A) _) = _
      simp only [h,serializedBits,Fin.append_left,Fin.append_right]

abbrev WireSpec := (ℕ × ℕ) × ℕ × ℕ × ℕ

def locate (s : WireSpec × ℕ) := Id.run do
  let ⟨((h,k),l,j,a),i⟩ := s
  return if i<l then h+k+i else if i<l+a then h+k+l+j+(i-l)
    else if i<l+a+k then h+(i-(l+a)) else if i<l+a+k+h then i-(l+a+k)
    else h+k+l+(i-(l+a+k+h))

@[fun_prop] theorem locate_poly : Poly locate := by unfold locate;dsimp;fun_prop

def positioned (v : WireSpec × GateCode) : GateCode :=
  (v.2.1,locate (v.1,v.2.2.1),if v.2.1=4 then locate (v.1,v.2.2.2) else 0)

@[fun_prop] theorem positioned_poly : Poly positioned := by unfold positioned;fun_prop

theorem positioned_exact (g : Instr (L+A+K+(H+J))) :
    positioned (((H,K),L,J,A),encodeInstr g) =
    encodeInstr (relocateInstr (oraclePerm H K L J A).toEmbedding g) := by
  cases g <;> rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule159

/- Helper module RunSerialized. -/
section P2MDyadicModule160

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute QuantumXorOracle

open PaddedDecoder SharedPoolCoherence

noncomputable section

variable {H K L J A : ℕ}

theorem emittedBasis_at {I : Type} (h : I → Bits H) (j : I → Bits J) (hi : Function.Injective (fun i => (h i,j i)))
    (x : I → Bits L) (d : I → Bits K) (i : I) :
    emittedBasis (A:=A) h j hi x d i = serializedBits (h i) (d i) (x i) (j i) 0 := by
  apply (wirePull (oraclePerm H K L J (A+1))).injective
  simp only [emittedBasis,Function.Embedding.trans_apply,Equiv.toEmbedding_apply]
  rw [Equiv.apply_symm_apply,sampled_bits]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule160

/- Helper module PositionedQFT. -/
section P2MDyadicModule161

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute CoherentDecoder

open NativeQFTPlanCompile GridReadout.Axis

open RegevLWE.GaussConv GaussianPoissonSeries IntegerBasis

noncomputable section

abbrev qftPerm (P D J : ℕ) : Fin (D+2+(P+J)) ≃ Fin (P+D+J+2) := oraclePerm P 0 D J 2

def rowBits {n b : ℕ} (c : Color n (2^b)) : Bits (n*b) :=
  (rowsEquiv b n).symm ((rowInput b n).symm c)

def headerJunk {P J : ℕ} {T : Type} (header : Bits P) (junk : T ↪ Bits J) : T ↪ Bits (P+J) where
  toFun t := Fin.append header (junk t)
  inj' t u h := by
    change (qubitsAppendEquiv P J).symm (header,junk t)=(qubitsAppendEquiv P J).symm (header,junk u) at h
    exact junk.injective (congrArg (fun z : Bits P × Bits J => z.2) ((qubitsAppendEquiv P J).symm.injective h))

def cleanOutput {n b P J : ℕ} {T I : Type} (header : Bits P) (junk : T ↪ Bits J) (c : I ↪ Color n (2^b)) :=
  (erasedBits (c.trans (framedBits n b)) (headerJunk header junk)).trans (wirePull (qftPerm P (n*b) J)).symm.toEmbedding

theorem cleanOutput_at {n b P J : ℕ} {T I : Type} (head : Bits P) (j : T ↪ Bits J) (c : I ↪ Color n (2^b)) (t : T × I) :
    cleanOutput head j c t = Fin.append (Fin.append (Fin.append head (rowBits (c t.2))) (j t.1)) (0:Bits 2) := by
  let e := qftPerm P (n*b) J
  have hhead : Fin.append head (0:Bits 0) = head := by
    funext i
    exact Fin.append_left head (0:Bits 0) i
  have he := sampled_bits head (0:Bits 0) (rowBits (c t.2)) (j t.1) (0:Bits 2)
  rw [serializedBits,hhead] at he
  apply (wirePull e).injective
  simp only [cleanOutput,Function.Embedding.trans_apply,Equiv.toEmbedding_apply]
  rw [Equiv.apply_symm_apply]
  apply Eq.trans _ he.symm
  change Fin.append (Fin.append (rowBits (c t.2)) 0) (Fin.append head (j t.1))=
    Fin.append (Fin.append (Fin.append (rowBits (c t.2)) 0) (0:Bits 0)) (Fin.append head (j t.1))
  congr 1
  funext i
  exact (Fin.append_left _ (0:Bits 0) i).symm

theorem born_wire_relabel {W N : ℕ} (e : Fin W ≃ Fin N) (v : QState W) (E : Bits W → Prop) :
    bornEvent (fun p => E (wirePull e p)) (WithLp.toLp 2 (relabel e v))=bornEvent E (WithLp.toLp 2 v) :=
  Fintype.sum_equiv (wirePull e) _ _ (fun _ => rfl)

theorem positioned_short_readout : ∃ a : ℕ, 0<a ∧ ∀ (nt : List Unit) (x : Input) (P J : ℕ)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (hB : B.det≠0) (r R : ℝ) (hr : 0<r) (hR : 0<R)
    (hn : 0<nt.length) (had : gridAdequate B r (2^x.1.length))
    (hscale : (nt.length:ℝ)*(1/(Real.sqrt 2*r))^2 ≤ R^2) (hsep : Separated (dual (inputLattice B hB)) R)
    (k : ℕ) (hk : precision nt.length x.1.length k ≤ x.2.length)
    [Fintype (Retained (dual (inputLattice B hB)) (2^x.1.length) R)]
    (T : Type) [Fintype T] (head : Bits P) (je : T ↪ Bits J) (j : T → ℂ) (_hj : ∑ t, ‖j t‖^2 = 1)
    (actual : QState (P+(nt.length*x.1.length)+J+2)) (_ha : stateNorm actual=1),
    let L := dual (inputLattice B hB)
    let s := 1/(Real.sqrt 2*r)
    let c := colorEmbedding (M:=2^x.1.length) L (dualIntegerBasis B hB) R hsep
    let target := CoherentProjection.normalized (finiteRestrict (fineEmbedding L (2^x.1.length) R)
      (gaussianHilbertState (fineLattice L (2^x.1.length)) (s/Real.sqrt 2) (by dsimp [s]; positivity) 0))
    let ideal := basisEmbedding (cleanOutput head je c) (fun t => j t.1*target t.2)
    let e := qftPerm P (nt.length*x.1.length) J
    let U := relocateCircuit e.toEmbedding (leftCircuit (m:=P+J) (circuit a x (List.finRange nt.length)))
    let u := WithLp.toLp 2 (runLayered U actual)
    let emit (p : Bits (P+(nt.length*x.1.length)+J+2)) := encodeSlices (nt,x.1,
      List.ofFn (leftRegister (wirePull e p) : Bits (nt.length*x.1.length+2)))
    bornEvent (fun p => ∃ z : Fin nt.length → ℤ, encVec encI z <+: emit p) u = 1 ∧
    ∀ S : Finset (Fin nt.length → ℤ),
      |bornEvent (fun p => ∃ z ∈ S, encVec encI z <+: emit p) u - ∑ z ∈ S, RegevSketch.coefficientMass B r z| ≤
      2*stateNorm (actual-ideal) + 4*Real.sqrt (2*(1/2:ℝ)^nt.length) + 1/(4*((k:ℝ)+1))+GridReadout.gridError nt.length := by
  obtain ⟨a,ha,h⟩ := signed_short_readout
  refine ⟨a,ha,?_⟩
  intro nt x P J B hB r R hr hR hn had hscale hsep k hk _ T _ head je j hj actual hactual
  dsimp only
  let e := qftPerm P (nt.length*x.1.length) J
  let v := relabel e.symm actual
  have hv : relabel e v=actual := by
    funext i
    change actual ((i ∘ e) ∘ e.symm)=actual i
    congr 1
    funext t;simp
  have hnorm : stateNorm v=1 :=
    (reindex_norm (wirePull e.symm) (WithLp.toLp 2 actual)).trans hactual
  have he := h nt x (P+J) B hB r R hr hR hn had hscale hsep k hk T (headerJunk head je) j hj v hnorm
  rw [←hv,relabel_run]
  constructor
  · exact (born_wire_relabel e _ _).trans he.1
  · intro S
    unfold cleanOutput
    rw [←relabel_emb,relabel_error]
    convert he.2 S using 2
    apply congrArg (fun z : ℝ => z - _)
    exact born_wire_relabel e _ (fun p => ∃ z ∈ S, encVec encI z <+: encodeSlices (nt,x.1,List.ofFn (leftRegister p : Bits (nt.length*x.1.length+2))))

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule161

/- Helper module TapeFrame. -/
section P2MDyadicModule162

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

theorem prefix_tape_padded (b : List Unit) (word : Str) :
    List.ofFn (prefixBits b.length word)=NativePaddedWords.current (b,word) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ _
    have hi : i<b.length := by simpa using h₁
    simp only [prefixBits,List.getElem_ofFn,NativePaddedWords.current,List.getElem_take]
    by_cases hw : i<word.length
    · simp [hw,List.getElem_append_left]
    · have hg : word.length ≤ i := by omega
      simp [List.getElem?_eq_none hg,List.getElem_append_right hg]

theorem finalBits_tape {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g) (w : Str) :
    List.ofFn (CoherentInjection.finalBits P Q w) =
      List.replicate (originalSize P Q w.length) false ++ f w ++
      List.replicate (outputSize P w.length-(f w).length+forwardWork P w.length+backwardWork P Q w.length) false := by
  rw [CoherentInjection.finalBits,dataBits_tape,List.ofFn_const]
  have he : List.ofFn (outputBits P w) = paddedOutput P w := rfl
  rw [he,paddedOutput_eq_append]
  simp [List.replicate_add,List.append_assoc]

/-- The true emitted qubits of the reversible forward/inverse codec consist
of the literal public header, row-major residue bits, signed answer, framed
query, retained residual and zeros on every unused machine wire. -/
theorem codec_final_tape (src : Source) (width : List Unit) (hfit : (pack src).length ≤ width.length) :
    let w := NativePaddedWords.current (width,pack src)
    let c := setup src.1.1.1
    let E := emit (width,src)
    List.ofFn (CoherentInjection.finalBits FineCodec.forwardProgram FineCodec.inverseProgram w) =
    List.replicate (originalSize FineCodec.forwardProgram FineCodec.inverseProgram width.length) false ++
      outHead (width,src) ++ blocks (c.1.1,src.2) ++
      NativePaddedWords.current (c.1.2.1,serializeVector (answers (c.1.1,src.2))) ++
      NativePaddedWords.current (c.1.2.2,request ((c,src.1.2.1),src.2)) ++ encS src.1.2.2 ++
      List.replicate (outputSize FineCodec.forwardProgram width.length-E.length+
        forwardWork FineCodec.forwardProgram width.length+backwardWork FineCodec.forwardProgram FineCodec.inverseProgram width.length) false := by
  dsimp only
  rw [finalBits_tape,NativePaddedWords.current_length,forward_padded src width hfit]
  simp only [emit,List.append_assoc]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule162

/- Helper module PhysicalReadout. -/
section P2MDyadicModule163

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1450000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity GridReadout.Axis CoherentDecoder ControlledNativeGates QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

def signedSlice (u : (List Unit × List Unit) × ℕ × Str) : Str :=
  encodeSlices (u.1.1,u.1.2,u.2.2.drop u.2.1)

theorem rowSlices_tail (nt bt : List Unit) (w tail : Str) (hw : nt.length*bt.length ≤ w.length) :
    rowSlices (nt,bt,w++tail) = rowSlices (nt,bt,w) := by
  unfold rowSlices
  dsimp only
  apply List.map_congr_left
  intro i hi
  have hi' : i<nt.length := List.mem_range.mp hi
  have bound := Nat.mul_le_mul_right bt.length (Nat.succ_le_of_lt hi')
  rw [Nat.succ_mul] at bound
  rw [List.drop_append,List.take_append_of_le_length (by simp;omega)]

theorem signedSlice_exact (nt bt : List Unit) (P J : ℕ) (p : Bits (P+nt.length*bt.length+J+2)) :
    signedSlice ((nt,bt),P,List.ofFn p) =
    encodeSlices (nt,bt,List.ofFn (leftRegister (wirePull (qftPerm P (nt.length*bt.length) J) p) :
      Bits (nt.length*bt.length+2))) := by
  obtain ⟨⟨q,aux⟩,rfl⟩ := (qubitsAppendEquiv (P+nt.length*bt.length+J) 2).symm.surjective p
  obtain ⟨⟨q,tail⟩,rfl⟩ := (qubitsAppendEquiv (P+nt.length*bt.length) J).symm.surjective q
  obtain ⟨⟨head,data⟩,rfl⟩ := (qubitsAppendEquiv P (nt.length*bt.length)).symm.surjective q
  have hhead : Fin.append head (0:Bits 0) = head := funext (Fin.append_left head (0:Bits 0))
  have he := sampled_bits head (0:Bits 0) data tail aux
  rw [serializedBits,hhead] at he
  change signedSlice ((nt,bt),P,List.ofFn (Fin.append (Fin.append (Fin.append head data) tail) aux)) =
    encodeSlices (nt,bt,List.ofFn (leftRegister (wirePull (oraclePerm P 0 (nt.length*bt.length) J 2) (Fin.append (Fin.append (Fin.append head data) tail) aux)) : Bits (nt.length*bt.length+2)))
  rw [he]
  have hl : leftRegister (Fin.append (Fin.append (Fin.append data aux) (0:Bits 0)) (Fin.append head tail))=Fin.append data aux := by
    funext i
    change Fin.append _ _ (Fin.castAdd _ i) = _
    exact (Fin.append_left _ _ i).trans (Fin.append_left _ _ i)
  rw [hl]
  simp only [signedSlice,List.ofFn_fin_append,List.append_assoc,List.drop_left' (show (List.ofFn head).length=P from List.length_ofFn)]
  unfold encodeSlices
  rw [rowSlices_tail nt bt (List.ofFn data) _ (by simp),rowSlices_tail nt bt (List.ofFn data) _ (by simp)]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule163

/- Helper module SignedRecipe. -/
section P2MDyadicModule164

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit TM2Boolean.CodeGenerator NativeWordLayout

open Integration9_9.TM2PlatformSerialization

open scoped Classical BigOperators

noncomputable section

abbrev Raw := Sizes × ((List Unit×ℕ) × List GateCode)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end P2MDyadicModule164

/- Helper module GridBudget. -/
section P2MDyadicModule165

set_option autoImplicit false

set_option maxHeartbeats 900000

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

open GaussianPoissonSeries RationalInverse GridReadout

noncomputable section

theorem adequate {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (H K d : ℕ)
    (hB : ∀ i j, |B i j| ≤ (2:ℤ)^H) (hr : r ≤ (2:ℝ)^K) :
    gridAdequate B r (2^(bits n H K d)) := by
  have hc : ⌈r⌉₊ ≤ 2^K := Nat.ceil_le.mpr (by exact_mod_cast hr)
  exact (dyadic_adequate B r H K hB hc).trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end P2MDyadicModule165

/- Helper module GridProgram. -/
section P2MDyadicModule166

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

theorem gridTape_adequate {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (d : ℕ) (hr : 0<r) :
    gridAdequate B (r:ℝ) (2^(gridTape (setup B r d)).length) := by
  rw [tape_length]
  simpa only [gridCount,setup,Native.inputRows,List.length_ofFn,List.length_replicate] using
    adequate B (r:ℝ) (integerMatrixTicks (Native.inputRows B)).length (rationalTicks r).length d
      (Native.inputRows_entry_height B) (ratio_heights r hr).1

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end P2MDyadicModule166

/- Helper module Solutions.RegevBridgeCoherentPublicPreparation. -/
section P2MDyadicModule167

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentPublicPreparation

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentComputeUncompute

open NativeWordCoherent NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

variable {f : Str→Str} (P : PolyProgram id id f)

theorem initializedWires_basis {k n : ℕ} (w : Fin k↪Fin n) (x : Bits n) :
    initializedWires w (wireBitsEquiv w x).2 (basis (wireBitsEquiv w x).1)=basis x := by
  funext y
  have he : y=x ↔ (wireBitsEquiv w y).1=(wireBitsEquiv w x).1 ∧
      (wireBitsEquiv w y).2=(wireBitsEquiv w x).2 := by
    rw [←(wireBitsEquiv w).injective.eq_iff,Prod.mk.injEq]
  change (if (wireBitsEquiv w y).1=(wireBitsEquiv w x).1 then (1 : ℂ) else 0)*
    (if (wireBitsEquiv w y).2=(wireBitsEquiv w x).2 then 1 else 0)=if y=x then 1 else 0
  split_ifs <;> simp_all

end InfoLossLAR.WorstCase.CoherentPublicPreparation

end

end P2MDyadicModule167

/- Helper module RectLayout. -/
section P2MDyadicModule168

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



end

end InfoLossLAR.WorstCase.RectangularSource

end P2MDyadicModule168

/- Helper module RectFramed. -/
section P2MDyadicModule169

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Arena

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary CoherentComputeUncompute CoherentInjection

open FiniteGateTransport RegevSearch.StageRegisters RegevSearch.PhysicalFourier

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

end

end InfoLossLAR.WorstCase.RectangularSource.Arena

end P2MDyadicModule169

/- Helper module GridError. -/
section P2MDyadicModule170

set_option autoImplicit false

set_option maxHeartbeats 800000

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

open GaussianPoissonSeries NativeDualQuotient

open scoped BigOperators

noncomputable section

theorem delta_pos (d : ℕ) : 0 < delta d := by unfold delta; positivity

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end P2MDyadicModule170

/- Helper module RectSettings. -/
section P2MDyadicModule171

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

end InfoLossLAR.WorstCase.RectangularSource.Settings

end

end P2MDyadicModule171

/- Helper module RectPublic. -/
section P2MDyadicModule172

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent.Padding

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2PlatformSerialization NativeTicketInteger

open Settings

noncomputable section

def pad (t : List Unit) : Str := t.map fun _ => true

@[fun_prop] theorem pad_poly : Poly pad := by unfold pad;fun_prop

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule172

/- Helper module RectOperational. -/
section P2MDyadicModule173

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

theorem physics_pos {r : ℚ} (hr : 0<r) : 0<physics r := by
  unfold physics
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  positivity

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule173

/- Helper module PoolTape. -/
section P2MDyadicModule174

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

end P2MDyadicModule174

/- Helper module EraseQuery. -/
section P2MDyadicModule175

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeBodyKernel (emodNatural_eq)

open Integration9_9.TM2PlatformSerialization

open Integration9_9.LARPlatformEncoding (readS_append)

open CoherentComputeUncompute TM2Boolean.PolyProgramCircuit

def digits (x : (List Unit × List Unit) × Str) : List ℤ :=
  (List.range x.1.1.length).map fun i => (chunk ((x.1.2,x.2),i) : ℤ)

@[fun_prop] theorem digits_poly : Poly digits := by
  have hi : Poly (fun x : (List Unit × List Unit) × Str => List.range x.1.1.length) :=
    Poly.comp (f:=fun t : List Unit => List.range t.length) Poly.list_indices (by fun_prop)
  unfold digits
  exact Poly.list_map (by fun_prop) hi

theorem digits_blocks (n b : List Unit) (z : List ℤ) (hn : n.length=z.length) :
    digits ((n,b),blocks (b,z)) = z.map (fun a => a % (NativeFixedResidue.modulus b : ℤ)) := by
  apply List.ext_getElem
  · simp [digits,hn]
  · intro i h₁ h₂
    have hi : i<z.length := by simpa using h₂
    simp only [digits,List.getElem_map,List.getElem_range]
    have hp : (0:ℤ)<NativeFixedResidue.modulus b := by exact_mod_cast NativeFixedResidue.modulus_pos b
    rw [show chunk ((b,blocks (b,z)),i) = (z[i]%(NativeFixedResidue.modulus b:ℤ)).toNat by simpa using chunk_blocks b z [] i hi,
      Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne')]

theorem request_residues (c : Config) (B : Str) (z : List ℤ) :
    request ((c,B),z.map (fun a => a%(NativeFixedResidue.modulus c.1.1 : ℤ)))=request ((c,B),z) := by
  simp only [request,points,List.map_map,Function.comp_def,emodNatural_eq,Int.emod_emod]

/-- The input is the literal contiguous public header and residue register. -/
def queryLabel (width : List Unit) (s : Source) : Str :=
  outHead (width,s) ++ blocks ((setup s.1.1.1).1.1,s.2)

def queryFromLabel (w : Str) : Str :=
  let h := skipU w
  let B := skipU (skipS h)
  let dim := skipS B
  let c := setup (firstS h)
  let p := digits ((unarySlots dim,c.1.1),skipU dim)
  NativePaddedWords.current (c.1.2.2,request ((c,firstS B),p))

@[fun_prop] theorem queryFromLabel_poly : Poly queryFromLabel := by unfold queryFromLabel; dsimp only; fun_prop

theorem queryFromLabel_exact (width : List Unit) (s : Source) :
    queryFromLabel (queryLabel width s) =
      NativePaddedWords.current ((setup s.1.1.1).1.2.2,request ((setup s.1.1.1,s.1.2.1),s.2)) := by
  unfold queryFromLabel queryLabel outHead
  dsimp only [skipU,skipS,firstS]
  simp only [List.append_assoc,lengthToken_eq,readUnary_append,unarySlots_append,readS_append]
  rw [digits_blocks _ _ _ (List.length_replicate),request_residues]

noncomputable def queryProgram : PolyProgram id id queryFromLabel :=
  Integration9_9.LARCoinLayout.rawPolyProgram queryFromLabel_poly

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule175

/- Helper module RawStage. -/
section P2MDyadicModule176

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

theorem fine_head (B : Matrix (Fin n) (Fin n) ℤ) (c : Config) (stage ticks : List Unit) (r z : Fin n → ℤ) :
    outHead (stage,fineSource B c ticks r z) =
      lengthToken stage ++ encS (header c) ++ lengthToken ticks ++ encS (encMat encI B) ++ encNat n := by
  simp only [fineSource,outHead,lengthToken_eq,List.length_ofFn]

theorem fine_tape (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt k l stage ticks : List Unit)
    (R : ℚ) (prec : ℕ) (pool : Fin m → Fin n → ℤ) (res z : Fin n → ℤ) :
    let c := queryConfig bt k l R prec pool
    let src := fineSource B c ticks res z
    let Q := poolBDDInput B R prec pool (FineGridDecoding.input B (2^bt.length) (FineGridDecoding.residue (2^bt.length) z))
    emit (stage,src) =
      (lengthToken stage ++ encS (header c) ++ lengthToken ticks ++ encS (encMat encI B) ++ encNat n) ++
      blocks (bt,List.ofFn z) ++ NativePaddedWords.current (k,encVec encI (FineGridDecoding.answer (2^bt.length) z)) ++
      NativePaddedWords.current (l,encS Q) ++ encS (serializeVector (List.ofFn res)) := by
  dsimp only
  rw [emit,fine_head]
  simp only [fineSource,setup_header,physical_answer,queryConfig]
  rw [←physical_request B hB bt k l R prec pool z]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule176

/- Helper module MoveErase. -/
section P2MDyadicModule177

set_option autoImplicit false

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open RegevSearch.PhysicalFourier CoherentPublicPreparation

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open ControlledNativeCode

noncomputable section

abbrev Arena (E W K L J A M D : ℕ) := E+W+K+L+J+A+(M+D)

/-- The copy-and-uncompute machine reads the public prefix and residue register, and
targets the framed query. Fresh wires hold its work and the zero suffix of its output. -/
def eraserWires (E W K L J A M D : ℕ) : Fin ((W+M)+(L+D)) ↪ Fin (Arena E W K L J A M D) where
  toFun i := ⟨if i.val < W then E+i.val else if i.val < W+M then E+W+K+L+J+A+(i.val-W)
    else if i.val < W+M+L then E+W+K+(i.val-(W+M)) else E+W+K+L+J+A+M+(i.val-(W+M+L)), by
    unfold Arena; split_ifs <;> omega⟩
  inj' := by intro i j h; have e := congrArg Fin.val h; apply Fin.ext; dsimp only at e; split_ifs at e <;> omega

variable {E W K L J A M D : ℕ}

def arenaBits (p : Bits E) (w : Bits W) (k : Bits K) (q : Bits L) (r : Bits J) (a : Bits A)
    (m : Bits M) (d : Bits D) : Bits (Arena E W K L J A M D) :=
  Fin.append (serializedBits (Fin.append p w) k q r a) (Fin.append m d)

theorem eraser_selected (p : Bits E) (w : Bits W) (k : Bits K) (q : Bits L) (r : Bits J)
    (a : Bits A) (m : Bits M) (d : Bits D) :
    (wireBitsEquiv (eraserWires E W K L J A M D) (arenaBits p w k q r a m d)).1 =
      Fin.append (Fin.append w m) (Fin.append q d) := by
  funext i
  simp only [wireBitsEquiv_fst,Function.comp_apply]
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      have h : eraserWires E W K L J A M D ((i.castAdd M).castAdd (L+D)) =
        (((((i.natAdd E).castAdd K).castAdd L).castAdd J).castAdd A).castAdd (M+D) := by
        apply Fin.ext; simp only [eraserWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]; split_ifs <;> omega
      rw [h]; simp only [arenaBits,serializedBits,Fin.append_left,Fin.append_right]
    | right i =>
      have h : eraserWires E W K L J A M D ((i.natAdd W).castAdd (L+D)) =
        (i.castAdd D).natAdd (E+W+K+L+J+A) := by
        apply Fin.ext; simp only [eraserWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]; split_ifs <;> omega
      rw [h]; simp only [arenaBits,serializedBits,Fin.append_left,Fin.append_right]
  | right i =>
    induction i using Fin.addCases with
    | left i =>
      have h : eraserWires E W K L J A M D ((i.castAdd D).natAdd (W+M)) =
        (((i.natAdd (E+W+K)).castAdd J).castAdd A).castAdd (M+D) := by
        apply Fin.ext; simp only [eraserWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]; split_ifs <;> omega
      rw [h]; simp only [arenaBits,serializedBits,Fin.append_left,Fin.append_right]
    | right i =>
      have h : eraserWires E W K L J A M D ((i.natAdd L).natAdd (W+M)) =
        (i.natAdd M).natAdd (E+W+K+L+J+A) := by
        apply Fin.ext; simp only [eraserWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]; split_ifs <;> omega
      rw [h]; simp only [arenaBits,serializedBits,Fin.append_left,Fin.append_right]

theorem eraser_outside (p : Bits E) (w : Bits W) (k : Bits K) (q q' : Bits L) (r : Bits J)
    (a : Bits A) (m : Bits M) (d : Bits D) :
    (wireBitsEquiv (eraserWires E W K L J A M D) (arenaBits p w k q r a m d)).2 =
    (wireBitsEquiv (eraserWires E W K L J A M D) (arenaBits p w k q' r a m d)).2 := by
  funext u
  rcases u with ⟨i,hi⟩
  change arenaBits p w k q r a m d i = arenaBits p w k q' r a m d i
  unfold arenaBits serializedBits Arena at *
  induction i using Fin.addCases with
  | right i => simp
  | left i =>
    simp only [Fin.append_left]
    induction i using Fin.addCases with
    | right i => simp
    | left i =>
      simp only [Fin.append_left]
      induction i using Fin.addCases with
      | right i => simp
      | left i =>
        simp only [Fin.append_left]
        induction i using Fin.addCases with
        | left i => simp
        | right i =>
          exfalso
          apply hi
          refine ⟨(i.castAdd D).natAdd (W+M),?_⟩
          apply Fin.ext; simp only [eraserWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]; split_ifs <;> omega

theorem relocated_erasure (U : Layered ((W+M)+(L+D))) (p : Bits E) (w : Bits W) (k : Bits K)
    (q : Bits L) (r : Bits J) (a : Bits A) (m : Bits M) (d : Bits D)
    (hU : runLayered U (basis (Fin.append (Fin.append w m) (Fin.append q d))) =
      basis (Fin.append (Fin.append w m) (Fin.append (0 : Bits L) d))) :
    runLayered (relocateCircuit (eraserWires E W K L J A M D) U) (basis (arenaBits p w k q r a m d)) =
      basis (arenaBits p w k 0 r a m d) := by
  let e := eraserWires E W K L J A M D
  rw [←CoherentPublicPreparation.initializedWires_basis e (arenaBits p w k q r a m d),
    relocateCircuit_initialized,eraser_selected,hU,eraser_outside p w k q 0 r a m d,
    ←eraser_selected p w k 0 r a m d,CoherentPublicPreparation.initializedWires_basis]

end

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule177

/- Helper module PlacedErase. -/
section P2MDyadicModule178

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open ControlledNativeCode TM2Boolean.PolyProgramCircuit NativeWordLayout

noncomputable section

abbrev machineSpace (W : ℕ) := (compiled queryProgram W).ops.length + 1

abbrev EraseSpec := ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)

def eraseAddress (v : EraseSpec × ℕ) : ℕ :=
  let ⟨⟨⟨e,w⟩,k,l⟩,⟨j,a⟩,m⟩ := v.1
  let i := v.2
  if i < w then e+i else if i < w+m then e+w+k+l+j+a+(i-w)
    else if i < w+m+l then e+w+k+(i-(w+m)) else e+w+k+l+j+a+m+(i-(w+m+l))

@[fun_prop] theorem eraseAddress_poly : Poly eraseAddress := by unfold eraseAddress;dsimp;fun_prop

def eraseGate (v : EraseSpec × GateCode) : GateCode :=
  (v.2.1,eraseAddress (v.1,v.2.2.1),if v.2.1=4 then eraseAddress (v.1,v.2.2.2) else 0)

@[fun_prop] theorem eraseGate_poly : Poly eraseGate := by unfold eraseGate;fun_prop

theorem eraseGate_exact {E W K L J A M D : ℕ} (g : Instr ((W+M)+(L+D))) :
    eraseGate ((((E,W),(K,L)),((J,A),M)),encodeInstr g) =
      encodeInstr (relocateInstr (eraserWires E W K L J A M D) g) := by
  cases g <;> rfl

end

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule178

/- Helper module CleanArena. -/
section P2MDyadicModule179

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity QuantumXorOracle ControlledNativeGates CoherentComputeUncompute FineCodec

def castBits {n m : ℕ} (h : n=m) (x : Bits n) : Bits m := h ▸ x

def castState {n m : ℕ} (h : n=m) (v : QState n) : QState m := h ▸ v

theorem castBits_list {n m : ℕ} (h : n=m) (x : Bits n) : List.ofFn (castBits h x)=List.ofFn x := by subst m;rfl

theorem castState_basis {n m : ℕ} (h : n=m) (x : Bits n) : castState h (basis x)=basis (castBits h x) := by subst m;rfl

theorem castState_error {n m : ℕ} (h : n=m) (u v : QState n) :
    stateNorm (castState h u-castState h v)=stateNorm (u-v) := by subst m;rfl

def transported {n m : ℕ} {I : Type} (h : n=m) (f : I ↪ Bits n) : I ↪ Bits m :=
  h ▸ f

abbrev rearSize (K L J A M D : ℕ) := K+L+J+A+M+D

def rearBits {K L J A M D : ℕ} (r : Bits J) : Bits (rearSize K L J A M D) :=
  Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (0:Bits K) (0:Bits L)) r) (0:Bits A)) (0:Bits M)) (0:Bits D)

def retainedRear {K L J A M D : ℕ} {T : Type} (j : T ↪ Bits J) : T ↪ Bits (rearSize K L J A M D) where
  toFun i := rearBits (j i)
  inj' t u h := by
    apply j.injective
    funext x
    have hi := congrFun h (((((x.natAdd (K+L)).castAdd A).castAdd M).castAdd D))
    simpa only [rearBits,Fin.append_left,Fin.append_right] using hi

theorem arenaSize (E H d K L J A M D : ℕ) :
    Arena E (H+d) K L J A M D+2=(E+H)+d+rearSize K L J A M D+2 := by unfold Arena rearSize;omega

theorem cleaned_arena_eq {n b E H K L J A M D : ℕ} {T I : Type}
    (pre : Bits E) (head : Bits H) (j : T ↪ Bits J) (c : I ↪ Color n (2^b)) (t : T×I) :
    castBits (arenaSize E H (n*b) K L J A M D)
      (Fin.append (arenaBits pre (Fin.append head (rowBits (c t.2))) (0:Bits K) (0:Bits L) (j t.1)
        (0:Bits A) (0:Bits M) (0:Bits D)) (0:Bits 2)) =
    cleanOutput (Fin.append pre head) (retainedRear (K:=K) (L:=L) (A:=A) (M:=M) (D:=D) j) c t := by
  apply List.ofFn_inj.mp
  rw [castBits_list,cleanOutput_at]
  simp only [arenaBits,serializedBits,retainedRear,Function.Embedding.coeFn_mk,rearBits,List.ofFn_fin_append,List.append_assoc]

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule179

/- Helper module StageLabels. -/
section P2MDyadicModule180

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

def commonHead (B : Matrix (Fin n) (Fin n) ℤ) (c : Config) (stage ticks : List Unit) :=
  lengthToken stage ++ encS (header c) ++ lengthToken ticks ++ encS (encMat encI B) ++ encNat n

theorem rowTape (bt : List Unit) (z : Fin n → ℤ) :
    List.ofFn (rowBits (b:=bt.length) (fun i => (z i : ZMod (2^bt.length)))) = blocks (bt,List.ofFn z) := by
  have h := physical_rows bt z
  change List.ofFn (Fin.append (rowBits (fun i => (z i : ZMod (2^bt.length)))) (0:Bits 2)) = _ at h
  rw [List.ofFn_fin_append,show List.ofFn (0:Bits 2)=[false,false] from rfl] at h
  exact List.append_cancel_right h

theorem queryLabel_match (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (bt k l stage ticks : List Unit)
    (R : ℚ) (prec : ℕ) (pool : Fin m → Fin n → ℤ) (cut : ℝ) (sep : Separated (dual (inputLattice B hB)) cut)
    (res : Fin n → ℤ) (p : Retained (dual (inputLattice B hB)) (2^bt.length) cut) :
    let c := queryConfig bt k l R prec pool
    let src := fineSource B c ticks res (shortCoordinate B hB cut p)
    let color := colorEmbedding _ (dualIntegerBasis B hB) _ sep p
    queryLabel stage src = List.ofFn (Fin.append (toBits (commonHead B c stage ticks)) (rowBits color)) := by
  dsimp only
  rw [queryLabel,fine_head,coordinate_color,List.ofFn_fin_append,rowTape bt _]
  simp only [toBits_tape,fineSource,setup_header,commonHead]
  rfl

theorem canonical_uncompute (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (bt k l stage ticks : List Unit)
    (R : ℚ) (hR : 0<R) (prec : ℕ) (pool : Fin m → Fin n → ℤ) (cut : ℝ)
    (hcut : cut ≤ (famσ n:ℝ)/(2*(R:ℝ))) (sep : Separated (dual (inputLattice B hB)) cut)
    (p : Retained (dual (inputLattice B hB)) (2^bt.length) cut) :
    let c := queryConfig bt k l R prec pool
    let color := colorEmbedding _ (dualIntegerBasis B hB) _ sep p
    let w := Fin.append (toBits (commonHead B c stage ticks)) (rowBits color)
    let q := promisedShort B hB R hR cut hcut p
    queryFromLabel (List.ofFn w) = List.ofFn (prefixBits l.length (encS (word prec pool q))) := by
  dsimp only
  rw [←queryLabel_match B hB bt k l stage ticks R prec pool cut sep (0:Fin n→ℤ) p,queryFromLabel_exact,prefix_tape_padded]
  simp only [fineSource,setup_header]
  let z := shortCoordinate B hB cut p
  change NativePaddedWords.current (l,request ((queryConfig bt k l R prec pool,encMat encI B),List.ofFn z)) = _
  rw [physical_request B hB bt k l R prec pool z]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule180

/- Helper module UniformErase. -/
section P2MDyadicModule181

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary TM2Boolean.PolyProgramCircuit NativeWordLayout

open scoped BigOperators Classical

noncomputable section

def castCapacity {B C T : ℕ} (h : C=T) (U : Layered (B+C)) : Layered (B+T) := h ▸ U

theorem extend_ofFn {L : ℕ} (q : Bits L) (D : ℕ) :
    (fun i : Fin (L+D) => TM2Boolean.wordExtension (List.ofFn q) i.val) = Fin.append q (0:Bits D) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [TM2Boolean.wordExtension,i.isLt]
  | right i => simp [TM2Boolean.wordExtension]; rfl

theorem oracle_at (W : ℕ) (w : Str) (hw : w.length=W) {L : ℕ} (x : Bits L) (hq : queryFromLabel w=List.ofFn x) :
    runLayered (CoherentClassicalOracle.fullCircuit queryProgram W)
      (basis (Fin.append (CoherentClassicalOracle.initialWork queryProgram W w)
        (fun i : Fin (capacity queryProgram W) => TM2Boolean.wordExtension (List.ofFn x) i.val))) =
      basis (Fin.append (CoherentClassicalOracle.initialWork queryProgram W w) (0:Bits (capacity queryProgram W))) := by
  subst W
  rw [CoherentClassicalOracle.fullCircuit_basis,CoherentClassicalOracle.maskedData_erases queryProgram _ _ hq]
  rfl

theorem cast_bits {B C D L : ℕ} (h : C=L+D) (U : Layered (B+C)) (w : Bits B) (x : Bits L)
    (hU : runLayered U (basis (Fin.append w (fun i : Fin C => TM2Boolean.wordExtension (List.ofFn x) i.val))) =
      basis (Fin.append w (0:Bits C))) :
    runLayered (castCapacity h U) (basis (Fin.append w (Fin.append x (0:Bits D)))) =
      basis (Fin.append w (Fin.append (0:Bits L) (0:Bits D))) := by
  subst C
  rw [extend_ofFn x D] at hU
  have hz : (0:Bits (L+D))=Fin.append (0:Bits L) (0:Bits D) := by funext i;induction i using Fin.addCases <;> simp
  exact hU.trans (congrArg (fun t : Bits (L+D) => basis (Fin.append w t)) hz)

def uniformEraser (E W K L J A D : ℕ) (hc : capacity queryProgram W = L+D) :
    Layered (Arena E W K L J A (machineSpace W) D) :=
  relocateCircuit (eraserWires E W K L J A (machineSpace W) D)
    (castCapacity (B:=W+machineSpace W) hc (CoherentClassicalOracle.fullCircuit queryProgram W))

theorem uniform_erase_basis {E W K L J A D : ℕ} (hc : capacity queryProgram W=L+D)
    (front : Bits E) (w : Bits W) (signed : Bits K) (x : Bits L) (rear : Bits J) (work : Bits A)
    (hq : queryFromLabel (List.ofFn w)=List.ofFn x) :
    runLayered (uniformEraser E W K L J A D hc)
      (basis (arenaBits front w signed x rear work (0:Bits (machineSpace W)) (0:Bits D))) =
      basis (arenaBits front w signed (0:Bits L) rear work (0:Bits (machineSpace W)) (0:Bits D)) := by
  apply relocated_erasure
  apply cast_bits
  have H := oracle_at W (List.ofFn w) List.length_ofFn x hq
  have hh : CoherentClassicalOracle.initialWork queryProgram W (List.ofFn w) =
      Fin.append w (0:Bits (machineSpace W)) := by
    exact extend_ofFn w _
  rwa [hh] at H

theorem uniform_erase_sum {I : Type*} [Fintype I] {E W K L J A D : ℕ} (hc : capacity queryProgram W=L+D)
    (front : I → Bits E) (w : I → Bits W) (signed : I → Bits K) (x : I → Bits L)
    (rear : I → Bits J) (work : I → Bits A) (a : I → ℂ)
    (hq : ∀ i, queryFromLabel (List.ofFn (w i))=List.ofFn (x i)) :
    runLayered (uniformEraser E W K L J A D hc)
      (∑ i, a i • basis (arenaBits (front i) (w i) (signed i) (x i) (rear i) (work i) (0:Bits (machineSpace W)) (0:Bits D))) =
      ∑ i, a i • basis (arenaBits (front i) (w i) (signed i) (0:Bits L) (rear i) (work i) (0:Bits (machineSpace W)) (0:Bits D)) := by
  rw [←runLayeredLinearMap_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,runLayeredLinearMap_apply,uniform_erase_basis hc _ _ _ _ _ _ (hq i)]

end

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule181

/- Helper module ErasureTransfer. -/
section P2MDyadicModule182

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentComputeUncompute QuantumXorOracle ControlledNativeGates

open FineCodec PaddedDecoder TM2Boolean.PolyProgramCircuit

noncomputable section

variable {n b E H K L J A D : ℕ} {T I : Type} [Fintype T] [Fintype I]

def tags (pre : Bits E) (head : Bits H) (c : I ↪ Color n (2^b)) (t : I) : Bits (E+(H+n*b)) :=
  Fin.append pre (Fin.append head (rowBits (c t)))

theorem tags_injective (pre : Bits E) (head : Bits H) (c : I ↪ Color n (2^b)) : Function.Injective (tags pre head c) := by
  intro i j h
  have h1 := (CoherentXorCopy.append_eq_iff _ _ _ _).mp h
  have h2 := (CoherentXorCopy.append_eq_iff _ _ _ _).mp h1.2
  exact c.injective ((GridReadout.Axis.rowInput b n).symm.injective ((GridReadout.Axis.rowsEquiv b n).symm.injective h2.2))

theorem tagPair_injective (pre : Bits E) (head : Bits H) (c : I ↪ Color n (2^b)) (r : T ↪ Bits J) :
    Function.Injective (fun t : T×I => (tags pre head c t.2,r t.1)) := by
  intro p q h
  exact Prod.ext (r.injective (congrArg (fun a : Bits (E+(H+n*b)) × Bits J => a.2) h))
    ((tags_injective pre head c) (congrArg (fun a : Bits (E+(H+n*b)) × Bits J => a.1) h))

abbrev taggedBasis (A K L : ℕ) (pre : Bits E) (head : Bits H) (c : I ↪ Color n (2^b)) (r : T ↪ Bits J)
    (x : I → Bits L) (d : I → Bits K) :=
  emittedBasis (A:=A) (fun t : T×I => tags pre head c t.2) (fun t => r t.1) (tagPair_injective pre head c r)
    (fun t => x t.2) (fun t => d t.2)

def afterErasure (E H n b K L J A D : ℕ) (hc : capacity queryProgram (H+n*b)=L+D)
    (v : QState ((E+(H+n*b))+K+L+J+(A+1))) :
    QState ((E+H)+(n*b)+rearSize K L J (A+1) (machineSpace (H+n*b)) D+2) :=
  castState (arenaSize E H (n*b) K L J (A+1) (machineSpace (H+n*b)) D)
    (attach (0:Bits 2) (runLayered (uniformEraser E (H+n*b) K L J (A+1) D hc) (attach
      (Fin.append (0:Bits (machineSpace (H+n*b))) (0:Bits D)) v)))

theorem afterErasure_error (hc : capacity queryProgram (H+n*b)=L+D) (u v : QState ((E+(H+n*b))+K+L+J+(A+1))) :
    stateNorm (afterErasure E H n b K L J A D hc u-afterErasure E H n b K L J A D hc v)=stateNorm (u-v) := by
  rw [afterErasure,afterErasure,castState_error,attach_error,run_error,attach_error]

theorem afterErasure_norm (hc : capacity queryProgram (H+n*b)=L+D) (v : QState ((E+(H+n*b))+K+L+J+(A+1))) :
    stateNorm (afterErasure E H n b K L J A D hc v)=stateNorm v := by
  have hn {s t : ℕ} (h : s=t) (v : QState s) : stateNorm (castState h v)=stateNorm v := by subst t;rfl
  rw [afterErasure,hn,attach_norm,show ∀ {m : ℕ} (U : Layered m) (v : QState m),stateNorm (runLayered U v)=stateNorm v from fun U v => (circuitIsometry U).norm_map _,attach_norm]

theorem afterErasure_exact (hc : capacity queryProgram (H+n*b)=L+D)
    (pre : Bits E) (head : Bits H) (c : I ↪ Color n (2^b)) (r : T ↪ Bits J) (x : I → Bits L)
    (hq : ∀ i, queryFromLabel (List.ofFn (Fin.append head (rowBits (c i))))=List.ofFn (x i)) (v : T×I → ℂ) :
    afterErasure E H n b K L J A D hc (basisEmbedding (taggedBasis A K L pre head c r x (fun _ => 0)) v) =
    basisEmbedding (cleanOutput (Fin.append pre head) (retainedRear (K:=K) (L:=L) (A:=A+1) (M:=machineSpace (H+n*b)) (D:=D) r) c) v := by
  let z := Fin.append (0:Bits (machineSpace (H+n*b))) (0:Bits D)
  let M := machineSpace (H+n*b)
  let W := H+n*b
  let e := taggedBasis A K L pre head c r x (fun _ => 0)
  let em := e.trans (appendEmbedding z)
  have hmid : attach z (basisEmbedding e v)=basisEmbedding em v := basis_comp _ _ _
  have hm (t : T×I) : em t=arenaBits pre (Fin.append head (rowBits (c t.2))) (0:Bits K) (x t.2) (r t.1) (0:Bits (A+1)) (0:Bits M) (0:Bits D) := by
    change Fin.append (taggedBasis A K L pre head c r x (fun _ => 0) t) z = _
    rw [taggedBasis,emittedBasis_at]
    rfl
  let ex := uniform_erase_sum hc (fun _ : T×I => pre) (fun t => Fin.append head (rowBits (c t.2))) (fun _ => (0:Bits K))
    (fun t => x t.2) (fun t => r t.1) (fun _ => (0:Bits (A+1))) v (fun t => hq t.2)
  let hj := arenaSize E H (n*b) K L J (A+1) M D
  let ie := cleanOutput (Fin.append pre head) (retainedRear (K:=K) (L:=L) (A:=A+1) (M:=M) (D:=D) r) c
  change castState hj (attach (0:Bits 2) (runLayered (uniformEraser E W K L J (A+1) D hc) (attach z (basisEmbedding e v))))=basisEmbedding ie v
  rw [hmid]
  unfold basisEmbedding
  dsimp only [LinearMap.coe_mk,AddHom.coe_mk]
  simp only [hm]
  rw [ex,map_sum]
  have cast_lin {u w : ℕ} (h : u=w) (xs : T×I → QState u) : castState h (∑ t,xs t) = ∑ t,castState h (xs t) := by subst w;rfl
  have cast_mul {u w : ℕ} (h : u=w) (a : ℂ) (v : QState u) : castState h (a • v)=a • castState h v := by subst w;rfl
  rw [cast_lin]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul,cast_mul]
  congr 1
  have ha {s k : ℕ} (d : Bits k) (b : Bits s) : attach d (basis b)=basis (Fin.append b d) := by
    exact PaddedDecoder.attached_basis _ _
  rw [ha,castState_basis,cleaned_arena_eq]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule182

/- Helper module CodecPhysicalFrame. -/
section P2MDyadicModule183

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FineCodec PaddedDecoder CoherentInjection IntegerBasis

open NativeDualQuotient (Residual)

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open Integration9_9.LARPlatformEncoding (readS readS_append)

open TM2Boolean TM2Boolean.PolyProgramCircuit RegevLWE.GaussConv

noncomputable section

abbrev codecOld (s : ℕ) := originalSize FineCodec.forwardProgram FineCodec.inverseProgram s

abbrev codecCap (s : ℕ) := outputSize FineCodec.forwardProgram s

abbrev codecWork (s : ℕ) := forwardWork FineCodec.forwardProgram s + backwardWork FineCodec.forwardProgram FineCodec.inverseProgram s

def fixedPart (H n b K L : ℕ) := H+n*b+K+L

def middleTail (s fix : ℕ) := codecCap s-fix+codecWork s

def resCode {n : ℕ} (r : Fin n → ℤ) := encS (serializeVector (List.ofFn r))

theorem prefix_tape_eq {J : ℕ} (w : Str) (h : w.length≤J) :
    List.ofFn (prefixBits J w)=w++List.replicate (J-w.length) false := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_append,List.length_replicate];omega
  · intro i hi hj
    simp only [List.getElem_ofFn,prefixBits]
    by_cases hl : i<w.length
    · simp [hl,List.getElem_append_left]
    · have hn : w.length ≤ i := by omega
      simp [hn,List.getElem?_eq_none,List.getElem_append_right]

theorem residual_code_inj {n J : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (fit : ∀ r : Residual B, (resCode r.val).length ≤ J) :
    Function.Injective (fun r : Residual B => prefixBits J (resCode r.val)) := by
  intro r t he
  let slots := List.replicate J ()
  have output (r : Residual B) :
      (readS (List.ofFn (prefixBits J (resCode r.val)))).2=serializeVector (List.ofFn r.val) := by
    rw [prefix_tape_eq _ (fit r),resCode,readS_append]
  have hv := congrArg (fun w : Bits J => (readVector (readS (List.ofFn w)).2).2) he
  rw [output r,output t,vector_read,vector_read] at hv
  exact Subtype.ext (List.ofFn_inj.mp hv)

theorem rootFrameSize (E Cap A B H C K L F : ℕ) (h : H+C+K+L ≤ Cap) :
    CoherentInjection.width E Cap A B+(F+1)=(E+(H+C))+K+L+(Cap-(H+C+K+L)+(A+B))+(F+1) := by
  unfold CoherentInjection.width
  omega

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule183

/- Helper module MachineFrame. -/
section P2MDyadicModule184

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FineCodec PaddedDecoder CoherentInjection IntegerBasis

open NativeDualQuotient (Residual)

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open TM2Boolean TM2Boolean.PolyProgramCircuit RegevLWE.GaussConv SharedPoolCoherence

noncomputable section

variable {n m : ℕ}

theorem machine_lengths (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt k l stage ticks : List Unit) (R : ℚ) (prec : ℕ)
    (pool : Fin m → Fin n → ℤ) (cut : ℝ) (res : Residual B) (p : Retained (dual (inputLattice B hB)) (2^bt.length) cut)
    (hfit : (pack (frameCode B hB bt k l stage ticks R prec pool cut res p)).length ≤ stage.length) :
    let src := frameCode B hB bt k l stage ticks R prec pool cut res p
    let H := (commonHead B (queryConfig bt k l R prec pool) stage ticks).length
    let fixed := fixedPart H n bt.length k.length l.length
    (emit (stage,src)).length = fixed+(resCode res.val).length ∧ fixed+(resCode res.val).length ≤ codecCap stage.length := by
  let src := frameCode B hB bt k l stage ticks R prec pool cut res p
  let w := NativePaddedWords.current (stage,pack src)
  have he := fine_tape B hB bt k l stage ticks R prec pool res.val (shortCoordinate B hB cut p)
  have hf : (emit (stage,src)).length =
    fixedPart (commonHead B (queryConfig bt k l R prec pool) stage ticks).length n bt.length k.length l.length + (resCode res.val).length := by
    rw [show emit (stage,src)=_ from he]
    simp only [List.length_append,blocks_length,List.length_ofFn,NativePaddedWords.current_length,fixedPart,resCode,commonHead]
  refine ⟨hf,?_⟩
  have hc := actualOutput_length_lt_capacity FineCodec.forwardProgram w
  change (FineCodec.forward w).length < _ at hc
  rw [show FineCodec.forward w = emit (stage,src) from forward_padded src stage hfit,
    show w.length=stage.length from NativePaddedWords.current_length _ _,hf] at hc
  exact hc.le

theorem machine_output (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt k l stage ticks : List Unit)
    (R : ℚ) (hR : 0<R) (prec : ℕ) (pool : Fin m → Fin n → ℤ) (cut : ℝ) (hcut : cut ≤ (famσ n:ℝ)/(2*(R:ℝ)))
    (sep : Separated (dual (inputLattice B hB)) cut) (res : Residual B) (p : Retained (dual (inputLattice B hB)) (2^bt.length) cut)
    (F : ℕ) (hfit : (pack (frameCode B hB bt k l stage ticks R prec pool cut res p)).length ≤ stage.length) :
    let src := frameCode B hB bt k l stage ticks R prec pool cut res p
    let w := NativePaddedWords.current (stage,pack src)
    let head := commonHead B (queryConfig bt k l R prec pool) stage ticks
    let fixed := fixedPart head.length n bt.length k.length l.length
    let hlen := machine_lengths B hB bt k l stage ticks R prec pool cut res p hfit
    let e := rootFrameSize (codecOld stage.length) (codecCap stage.length) (forwardWork FineCodec.forwardProgram stage.length)
      (backwardWork FineCodec.forwardProgram FineCodec.inverseProgram stage.length)
      head.length (n*bt.length) k.length l.length F (by exact (Nat.le_add_right _ _).trans hlen.2)
    let c := colorEmbedding (M:=2^bt.length) _ (dualIntegerBasis B hB) _ sep
    let q := promisedShort B hB R hR cut hcut p
    castBits e (Fin.append (finalBitsAt FineCodec.forwardProgram FineCodec.inverseProgram stage.length w) (0:Bits (F+1))) =
      serializedBits (tags (0:Bits (codecOld stage.length)) (toBits head) c p)
        (prefixBits k.length (encVec encI q.answer)) (prefixBits l.length (encS (word prec pool q)))
        (prefixBits (middleTail stage.length fixed) (resCode res.val)) (0:Bits (F+1)) := by
  let src := frameCode B hB bt k l stage ticks R prec pool cut res p
  let w := NativePaddedWords.current (stage,pack src)
  let head := commonHead B (queryConfig bt k l R prec pool) stage ticks
  let fixed := fixedPart head.length n bt.length k.length l.length
  have hcap := machine_lengths B hB bt k l stage ticks R prec pool cut res p hfit
  dsimp only at hcap
  have hrear : (resCode res.val).length ≤ middleTail stage.length fixed := by
    have h' : fixed+(resCode res.val).length ≤ codecCap stage.length := hcap.2
    unfold middleTail;omega
  have hfinal : List.ofFn (finalBitsAt FineCodec.forwardProgram FineCodec.inverseProgram stage.length w) =
      List.ofFn (CoherentInjection.finalBits FineCodec.forwardProgram FineCodec.inverseProgram w) := by
    generalize hh : stage.length=W
    have hw : w.length=W := (NativePaddedWords.current_length _ _).trans hh
    subst W
    have he (W : ℕ) (h : w.length=W) : List.ofFn (finalBitsAt FineCodec.forwardProgram FineCodec.inverseProgram W w) =
        List.ofFn (CoherentInjection.finalBits FineCodec.forwardProgram FineCodec.inverseProgram w) := by subst W;rfl
    exact he _ hw
  apply List.ofFn_inj.mp
  rw [castBits_list,List.ofFn_fin_append,hfinal,codec_final_tape src stage hfit]
  dsimp only [src,frameCode]
  simp only [serializedBits,tags,List.ofFn_fin_append,List.ofFn_const,toBits_tape,coordinate_color,rowTape bt]
  rw [fine_head]
  dsimp only [src,frameCode] at hcap
  rw [hcap.1,prefix_tape_padded k,prefix_tape_padded l,prefix_tape_eq (resCode res.val) hrear]
  simp only [fineSource,setup_header,physical_answer]
  rw [physical_request B hB bt k l R prec pool (shortCoordinate B hB cut p)]
  simp only [List.append_assoc]
  have heq : codecCap stage.length-(fixed+(resCode res.val).length)+forwardWork FineCodec.forwardProgram stage.length+
      backwardWork FineCodec.forwardProgram FineCodec.inverseProgram stage.length =
      middleTail stage.length fixed-(resCode res.val).length := by
    have hh : fixed+(resCode res.val).length≤codecCap stage.length := hcap.2
    unfold middleTail codecWork;omega
  rw [show outputSize FineCodec.forwardProgram stage.length-
      (fixed+(resCode res.val).length)+forwardWork FineCodec.forwardProgram stage.length+
      backwardWork FineCodec.forwardProgram FineCodec.inverseProgram stage.length = _ from heq]
  have hz (s : ℕ) : List.ofFn (0:Bits s)=List.replicate s false := List.ofFn_const s false
  simp only [commonHead,List.append_assoc,hz]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule184

/- Helper module StageKernel. -/
section P2MDyadicModule185

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000

set_option maxHeartbeats 2400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute QuantumXorOracle

open FineCodec PaddedDecoder TM2Boolean.PolyProgramCircuit SharedPoolCoherence GridReadout.Axis NativeQFTPlanCompile

open IntegerBasis RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection CoherentDecoder

noncomputable section

/-- Every physical gate and every complete tape register between the first
coherent BDD call and the final signed coefficient readout. The comparison
is against the genuine current-lattice coefficient PMF. The countable pool
averaging is performed separately on the exposed, pool-independent failure
amplitudes, even when the independent source junk varies by pool. -/
theorem single_physical_stage (C : MFamily) (hC : IsMQPT C) :
    ∃ F : MFamily, IsMQPT F ∧ ∃ width : ∀ l, l ≤ F.outLen l, ∃ a : ℕ, 0<a ∧
    ∀ (nt : List Unit) (x : Input) (m E J : ℕ)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (hB : B.det≠0) (r cut : ℝ) (hr : 0<r) (hc : 0<cut)
    (hn : 0<nt.length) (hg : gridAdequate B r (2^x.1.length))
    (hs : (nt.length:ℝ)*(1/(Real.sqrt 2*r))^2 ≤ cut^2) (sep : Separated (StageL B hB) cut)
    (R : ℚ) (hR : 0<R) (hcut : cut ≤ (famσ nt.length:ℝ)/(2*(R:ℝ)))
    (budget : ℕ) (hk : precision nt.length x.1.length budget ≤ x.2.length)
    (prec : ℕ) (pool : Fin m → Fin nt.length → ℤ)
    (k l stage ticks : List Unit) (hkl : k.length ≤ l.length)
    [Fintype (StageI B hB x.1.length cut)]
    (hfits : ∀ p : StageI B hB x.1.length cut, (encS (word prec pool (promisedShort B hB R hR cut hcut p))).length ≤ l.length)
    (T : Type) [Fintype T] [Nonempty T] (pre : Bits E) (je : T ↪ Bits J) (j : T → ℂ) (hj : ∑ t,‖j t‖^2=1),
    let head := toBits (commonHead B (queryConfig x.1 k l R prec pool) stage ticks)
    let H := (commonHead B (queryConfig x.1 k l R prec pool) stage ticks).length
    let c := colorEmbedding (M:=2^x.1.length) _ (dualIntegerBasis B hB) _ sep
    let q (p : StageI B hB x.1.length cut) := promisedShort B hB R hR cut hcut p
    let u := taper B hB x.1.length r cut hr
    let data (p : StageI B hB x.1.length cut) := prefixBits k.length (encVec encI (q p).answer)
    let req (p : StageI B hB x.1.length cut) := prefixBits l.length (encS (word prec pool (q p)))
    let W := H+nt.length*x.1.length
    let D := capacity queryProgram W-l.length
    ∃ hcap : capacity queryProgram W=l.length+D,
    let ide := basisEmbedding (taggedBasis (F.anc l.length) k.length l.length pre head c je req data)
      (fun p => j p.1*u p.2)
    let O := relocateCircuit (oraclePerm (E+W) k.length l.length J (F.anc l.length+1)).toEmbedding
      (leftCircuit (m:=E+W+J) (QuantumXorOracle.circuit (F.circ l.length) (controls F l.length k.length (hkl.trans (width l.length)))))
    let S := rearSize k.length l.length J (F.anc l.length+1) (machineSpace W) D
    let Q := relocateCircuit (qftPerm (E+H) (nt.length*x.1.length) S).toEmbedding
      (leftCircuit (m:=E+H+S) (GridReadout.Axis.circuit a x (List.finRange nt.length)))
    ∀ (v : QState ((E+W)+k.length+l.length+J+(F.anc l.length+1))) (_hv : stateNorm v=1),
    let mid := afterErasure E H nt.length x.1.length k.length l.length J (F.anc l.length) D hcap (runLayered O v)
    let out := WithLp.toLp 2 (runLayered Q mid)
    let read (p : Bits ((E+H)+nt.length*x.1.length+S+2)) := signedSlice ((nt,x.1),E+H,List.ofFn p)
    bornEvent (fun p => ∃ z : Fin nt.length→ℤ, encVec encI z <+: read p) out = 1 ∧
    ∀ event : Finset (Fin nt.length→ℤ),
      |bornEvent (fun p => ∃ z ∈ event, encVec encI z <+: read p) out -
        ∑ z ∈ event, RegevSketch.coefficientMass B r z| ≤
      2*stateNorm (v-ide)+4*Real.sqrt (failureMass C prec pool q u.ofLp)+4*Real.sqrt (2*(1/2:ℝ)^nt.length)+
        1/(4*((budget:ℝ)+1))+GridReadout.gridError nt.length := by
  obtain ⟨F,hF,width,ho⟩ := oracle_in_serialized_order C hC
  obtain ⟨a,ha,hread⟩ := positioned_short_readout
  refine ⟨F,hF,width,a,ha,?_⟩
  intro nt x m E J B hB r cut hr hc hn hg hs sep R hR hcut budget hk prec pool k l stage ticks hkl _ hfits T _ _ pre je j hj
  let n := nt.length
  let b := x.1.length
  let I := StageI B hB b cut
  let pzero : I := ⟨0,by simpa [GaussianPoissonSeries.fineGridPoint] using hc⟩
  letI : Nonempty I := ⟨pzero⟩
  let head := toBits (commonHead B (queryConfig x.1 k l R prec pool) stage ticks)
  let H := (commonHead B (queryConfig x.1 k l R prec pool) stage ticks).length
  let W := H+n*b
  let D := capacity queryProgram W-l.length
  let c := colorEmbedding (M:=2^b) _ (dualIntegerBasis B hB) _ sep
  let q (p : I) := promisedShort B hB R hR cut hcut p
  let req (i : I) := prefixBits l.length (encS (word prec pool (q i)))
  let u := taper B hB b r cut hr
  let amp (t : T×I) := j t.1*u t.2
  let tag (i : I) := Fin.append head (rowBits (c i))
  have hx (i : I) : queryFromLabel (List.ofFn (tag i))=List.ofFn (req i) := canonical_uncompute B hB _ _ _ _ _ R hR prec pool cut hcut sep i
  have cap : capacity queryProgram W = l.length+D := by
    have h := actualOutput_length_lt_capacity queryProgram (List.ofFn (tag pzero))
    rw [hx pzero,List.length_ofFn,List.length_ofFn] at h
    change l.length<capacity queryProgram W at h
    dsimp only [D];omega
  dsimp only
  refine ⟨cap,?_⟩
  intro v hv
  have hframe (i : I) : ∃ pad : Str, List.ofFn (req i)=encS (word prec pool (q i))++pad := by
    refine ⟨_,(prefix_tape_padded l _).trans (NativePaddedWords.current_eq l _ (hfits i))⟩
  let O := relocateCircuit (oraclePerm (E+W) k.length l.length J (F.anc l.length+1)).toEmbedding
    (leftCircuit (m:=E+W+J) (QuantumXorOracle.circuit (F.circ l.length) (controls F l.length k.length (hkl.trans (width l.length)))))
  let mid := afterErasure E H n b k.length l.length J (F.anc l.length) D cap (runLayered O v)
  let clean := cleanOutput (Fin.append pre head) (retainedRear (K:=k.length) (L:=l.length) (A:=F.anc l.length+1) (M:=machineSpace W) (D:=D) je) c
  let d (i : I) := prefixBits k.length (encVec encI (q i).answer)
  let input := basisEmbedding (taggedBasis (F.anc l.length) k.length l.length pre head c je req d) amp
  let empty := basisEmbedding (taggedBasis (F.anc l.length) k.length l.length pre head c je req (fun _ => 0)) amp
  have hO := ho hkl B R prec pool (T×I) (fun t => tags pre head c t.2) (fun t => je t.1)
    (tagPair_injective pre head c je) (fun t => q t.2) amp (fun t => req t.2) (fun t => hframe t.2) v
  change stateNorm (runLayered O v-empty) ≤ stateNorm (v-input)+2*Real.sqrt
    (failureMass C prec pool (fun t : T×I => q t.2) (fun t => j t.1*u t.2)) at hO
  rw [failure_junk C B R prec pool q j u.ofLp hj] at hO
  have hE := afterErasure_exact (A:=F.anc l.length) (K:=k.length) cap pre head c je req hx amp
  change afterErasure E H n b k.length l.length J (F.anc l.length) D cap empty = basisEmbedding clean amp at hE
  have hmid : stateNorm (mid-basisEmbedding clean amp) ≤ stateNorm (v-input)+2*Real.sqrt (failureMass C prec pool q u.ofLp) := by
    rw [←hE,show mid=afterErasure E H n b k.length l.length J (F.anc l.length) D cap (runLayered O v) from rfl,afterErasure_error]
    exact hO
  have hm : stateNorm mid=1 := (afterErasure_norm cap _).trans (((circuitIsometry O).norm_map _).trans hv)
  let S := rearSize k.length l.length J (F.anc l.length+1) (machineSpace W) D
  have read := hread nt x (E+H) S B hB r cut hr hc hn hg hs sep budget hk T (Fin.append pre head)
    (retainedRear (K:=k.length) (L:=l.length) (A:=F.anc l.length+1) (M:=machineSpace W) (D:=D) je) j hj mid hm
  dsimp only at read ⊢
  simp only [signedSlice_exact] at *
  refine ⟨read.1, fun ev => (read.2 ev).trans ?_⟩
  change 2*stateNorm (mid-basisEmbedding clean amp)+_+_+_ ≤ 2*stateNorm (v-input)+4*Real.sqrt (failureMass C prec pool q u.ofLp)+_+_+_
  linarith

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule185

/- Helper module MachineStep. -/
section P2MDyadicModule186

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2300000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity IntegerBasis PaddedDecoder CoherentComputeUncompute CoherentInjection

open FineCodec

open NativeDualQuotient (Residual)

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2PlatformSerialization

open TM2Boolean TM2Boolean.PolyProgramCircuit QuantumXorOracle ControlledNativeGates

noncomputable section

variable {n m : ℕ}

attribute [local irreducible] FineCodec.forwardProgram FineCodec.inverseProgram

def beforeMachine {I : Type} [Fintype I] (s : List Unit) (q : I → Source) (a : I → ℂ) :=
  ∑ i, a i • basis (inputBitsAt FineCodec.forwardProgram FineCodec.inverseProgram s.length (stagedWord s (q i)))

def machineRun {N : ℕ} (s : List Unit) (F : ℕ)
    (e : totalWidth FineCodec.forwardProgram FineCodec.inverseProgram s.length+(F+1)=N)
    (v : QState (totalWidth FineCodec.forwardProgram FineCodec.inverseProgram s.length)) :=
  castState e (attach (0:Bits (F+1)) (runLayered (circuit FineCodec.forwardProgram FineCodec.inverseProgram s.length) v))

theorem machineRun_error {N : ℕ} (s : List Unit) (F : ℕ)
    (e : totalWidth FineCodec.forwardProgram FineCodec.inverseProgram s.length+(F+1)=N) (u v) :
    stateNorm (machineRun s F e u-machineRun s F e v)=stateNorm (u-v) := by
  rw [machineRun,machineRun,castState_error,attach_error,run_error]

theorem machineRun_sum {I : Type} [Fintype I] {N : ℕ} (s : List Unit) (F : ℕ)
    (e : totalWidth FineCodec.forwardProgram FineCodec.inverseProgram s.length+(F+1)=N)
    (q : I → Source) (a : I → ℂ) (labels : I ↪ Bits N)
    (hf : ∀ i,(pack (q i)).length≤ s.length)
    (hs : ∀ i,(serializeVector (answers ((setup (q i).1.1.1).1.1,(q i).2))).length ≤ (setup (q i).1.1.1).1.2.1.length)
    (he : ∀ i,castBits e (Fin.append (finalBitsAt FineCodec.forwardProgram FineCodec.inverseProgram s.length (stagedWord s (q i))) (0:Bits (F+1)))=labels i) :
    machineRun s F e (beforeMachine s q a)=basisEmbedding labels a := by
  subst N
  change attach (0:Bits (F+1)) (runLayered (circuit _ _ s.length) (∑ i,a i • basis _))=∑ i,a i • basis _
  rw [←runLayeredLinearMap_apply,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := circuit_basis_at FineCodec.forwardProgram FineCodec.inverseProgram s.length (stagedWord s (q i))
    (NativePaddedWords.current_length _ _) (FineCodec.left_inverse _ _ (hf i) (hs i))
  rw [map_smul,map_smul,runLayeredLinearMap_apply,hi,PaddedDecoder.attached_basis]
  exact congrArg (fun t => a i • basis t) (he i)

theorem machine_stage (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt k l stage ticks : List Unit)
    (R : ℚ) (hR : 0<R) (prec : ℕ) (pool : Fin m → Fin n → ℤ) (cut : ℝ) (hc : 0<cut)
    (hcut : cut≤(famσ n:ℝ)/(2*(R:ℝ))) (sep : Separated (StageL B hB) cut)
    [Fintype (Residual B)] [Fintype (StageI B hB bt.length cut)]
    (F : ℕ) (hf : ∀ res p,(pack (frameCode B hB bt k l stage ticks R prec pool cut res p)).length≤ stage.length)
    (hA : ∀ p : StageI B hB bt.length cut, (encVec encI (promisedShort B hB R hR cut hcut p).answer).length≤ k.length) :
    let I := StageI B hB bt.length cut
    let src (t : Residual B×I) := frameCode B hB bt k l stage ticks R prec pool cut t.1 t.2
    let head := commonHead B (queryConfig bt k l R prec pool) stage ticks
    let W := head.length+n*bt.length
    let fixed := fixedPart head.length n bt.length k.length l.length
    let J := middleTail stage.length fixed
    let E := codecOld stage.length
    let c := colorEmbedding (M:=2^bt.length) _ (dualIntegerBasis B hB) _ sep
    let q (p : I) := promisedShort B hB R hR cut hcut p
    ∃ e : totalWidth FineCodec.forwardProgram FineCodec.inverseProgram stage.length+(F+1)=(E+W)+k.length+l.length+J+(F+1),
    ∃ je : Residual B ↪ Bits J,
    ∀ (a : Residual B×I→ℂ) (v : QState (totalWidth FineCodec.forwardProgram FineCodec.inverseProgram stage.length)),
      stateNorm (machineRun stage F e v-basisEmbedding (taggedBasis F k.length l.length (0:Bits E) (toBits head) c je
        (fun p => prefixBits l.length (encS (SharedPoolCoherence.word prec pool (q p))))
        (fun p => prefixBits k.length (encVec encI (q p).answer))) a) =
      stateNorm (v-beforeMachine stage src a) := by
  intro I src head W fixed J E c q
  let pz : I := ⟨0, by simpa [GaussianPoissonSeries.fineGridPoint] using hc⟩
  have hl (r : Residual B) : fixed+(resCode r.val).length≤codecCap stage.length :=
    (machine_lengths B hB bt k l stage ticks R prec pool cut r pz (hf r pz)).2
  let rz : Residual B := (NativeDualQuotient.integerPointsEquiv B hB 0).1
  have hfix : fixed≤codecCap stage.length := (Nat.le_add_right _ _).trans (hl rz)
  let e : totalWidth FineCodec.forwardProgram FineCodec.inverseProgram stage.length+(F+1)=(E+W)+k.length+l.length+J+(F+1) := rootFrameSize E (codecCap stage.length) (forwardWork FineCodec.forwardProgram stage.length)
    (backwardWork FineCodec.forwardProgram FineCodec.inverseProgram stage.length) head.length (n*bt.length) k.length l.length F hfix
  have hr (r : Residual B) : (resCode r.val).length ≤ J := by
    have hh := hl r
    change codecCap stage.length-fixed+codecWork stage.length ≥ _
    omega
  let je : Residual B ↪ Bits J := ⟨fun t => prefixBits J (resCode t.val),residual_code_inj hr⟩
  refine ⟨e,je,?_⟩
  intro a v
  have hscode (t : Residual B×I) : (serializeVector (answers ((setup (src t).1.1.1).1.1,(src t).2))).length ≤ (setup (src t).1.1.1).1.2.1.length := by
    simp only [src,frameCode,fineSource,setup_header,queryConfig,physical_answer]
    exact hA t.2
  let lb := taggedBasis F k.length l.length (0:Bits E) (toBits head) c je
        (fun p => prefixBits l.length (encS (SharedPoolCoherence.word prec pool (q p))))
        (fun p => prefixBits k.length (encVec encI (q p).answer))
  have he (t : Residual B×I) : castBits e (Fin.append (finalBitsAt FineCodec.forwardProgram FineCodec.inverseProgram stage.length (stagedWord stage (src t))) (0:Bits (F+1)))=lb t := by
    dsimp only [lb,taggedBasis]
    rw [emittedBasis_at]
    have h := machine_output B hB bt k l stage ticks R hR prec pool cut hcut sep t.1 t.2 F (hf t.1 t.2)
    dsimp only at h
    simpa only [e,src,stagedWord,je,Function.Embedding.coeFn_mk,head,q,c,E,fixed,J,W] using h
  change stateNorm (machineRun stage F e v-basisEmbedding lb a)=_
  rw [←machineRun_sum stage F e src a lb (fun t => hf t.1 t.2) hscode he,machineRun_error]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule186

/- Helper module FourierEmit. -/
section P2MDyadicModule187

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1550000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity ControlledNativeGates FiniteGateTransport ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeQFTPlanCompile

def blockActions (v : ℕ × Block) : List GateCode :=
  let n := v.1
  let b := v.2
  let i := b.2.1
  let j := b.2.2.1
  if b.1=0 then if i<n then [(0,i,0)] else []
  else if b.1=1 then if i<n then b.2.2.2.map (fun code => relocateCode (i,n,n+1) (localCode code)) else []
  else if b.1=2 then if i<n then if j<n then if i=j then [] else [(4,i,j)] else [] else [] else []

@[fun_prop] theorem blockActions_poly : Poly blockActions := by
  have hphase : Poly (fun v : ℕ × Block => v.2.2.2.2.map (fun j => relocateCode (v.2.2.1,v.1,v.1+1) (localCode j))) := by
    apply Poly.list_map
    · exact Poly.comp relocateCode_poly (Poly.pair (by fun_prop) (Poly.comp localCode_poly Poly.snd))
    · fun_prop
  unfold blockActions
  dsimp only
  fun_prop

theorem blockActions_eq (n : ℕ) (b : Block) :
    blockActions (n,b) = (instructions (physicalBlock n b)).map encodeInstr := by
  unfold physicalBlock blockActions
  dsimp only
  split_ifs <;> try rfl
  all_goals try omega
  rename_i hi
  simp only [instructions,FiniteGateNativeEnumeration.interpreted,List.map_map]
  apply List.map_congr_left
  intro c _
  let w := freshPhaseWires (⟨b.2.1,hi⟩ : Fin n)
  have he : ((w 0).val,(w 1).val,(w 2).val)=(b.2.1,n,n+1) := by rfl
  exact (congrArg (relocateCode (b.2.1,n,n+1)) (localCode_eq c)).trans (he ▸ relocateCode_encode w _)

def singleAxis (a : ℕ) (x : NativeQFTPlanCompile.Input) : List GateCode :=
  (current a x).flatMap (fun b => blockActions (x.1.length,b))

@[fun_prop] theorem singleAxis_poly (a : ℕ) : Poly (singleAxis a) := by
  unfold singleAxis
  have h := current_poly a
  fun_prop

theorem singleAxis_exact (a : ℕ) (x : NativeQFTPlanCompile.Input) :
    singleAxis a x=(instructions (physicalWord a x)).map encodeInstr := by
  simp only [singleAxis,physicalWord,instructions,List.map_flatMap,blockActions_eq,List.map_map]

def rowAddress (v : (ℕ × ℕ × ℕ) × ℕ) :=
  let b := v.1.1
  let n := v.1.2.1
  let i := v.1.2.2
  if v.2<b then i*b+v.2 else n*b+(v.2-b)

@[fun_prop] theorem rowAddress_poly : Poly rowAddress := by unfold rowAddress;fun_prop

def rowGate (v : (ℕ × ℕ × ℕ) × GateCode) : GateCode :=
  (v.2.1,rowAddress (v.1,v.2.2.1),if v.2.1=4 then rowAddress (v.1,v.2.2.2) else 0)

@[fun_prop] theorem rowGate_poly : Poly rowGate := by unfold rowGate;fun_prop

theorem rowAddress_eq {n b : ℕ} (i : Fin n) (j : Fin (b+2)) :
    rowAddress ((b,n,i.val),j.val)=(GridReadout.Axis.wires b i j).val := by
  induction j using Fin.addCases with
  | left j =>
    simp [rowAddress,GridReadout.Axis.wires,GridReadout.Axis.dataWire,Fin.append_left,j.isLt,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  | right j =>
    simp [rowAddress,GridReadout.Axis.wires,GridReadout.Axis.auxWire,Fin.append_right]

theorem rowGate_eq {n b : ℕ} (i : Fin n) (g : Letter (b+2)) :
    rowGate ((b,n,i.val),encodeInstr g.toInstr) = encodeInstr (g.relocate (GridReadout.Axis.wires b i)).toInstr := by
  cases g <;> simp [rowGate,encodeInstr,Letter.toInstr,Letter.relocate,rowAddress_eq]

def allRows (a : ℕ) (v : List Unit × NativeQFTPlanCompile.Input) : List GateCode :=
  (List.range v.1.length).flatMap (fun i =>
    (singleAxis a v.2).map (fun g => rowGate ((v.2.1.length,v.1.length,i),g)))

@[fun_prop] theorem allRows_poly (a : ℕ) : Poly (allRows a) := by
  unfold allRows
  have hr := Poly.comp (f:=fun xs : List Unit => List.range xs.length)
    (g:=fun v : List Unit × NativeQFTPlanCompile.Input => v.1) Poly.list_indices Poly.fst
  fun_prop

theorem allRows_exact (a : ℕ) (nt : List Unit) (x : NativeQFTPlanCompile.Input) :
    allRows a (nt,x) = (GridReadout.Axis.circuit a x (List.finRange nt.length)).flatten.map encodeInstr := by
  rw [allRows,show List.range nt.length=(List.finRange nt.length).map Fin.val by simp]
  simp only [List.flatMap_map,GridReadout.Axis.circuit,←List.flatMap_def,List.map_flatMap,singleAxis_exact,instructions,
    GridReadout.Axis.word,List.map_map,Function.comp_def,rowGate_eq]

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule187

/- Helper module Solutions.RegevBridgeQuantumXorNative. -/
section P2MDyadicModule188

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.QuantumXorOracle.Native

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode NativeWordDescription NativeWordLayout

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

variable (layers : Str → List (List Str)) (hlayers : Poly layers)
  (slots : Str → List Unit) (hslots : Poly slots)
  (positions : Str → List ℕ) (hpositions : Poly positions)

def wholeSlots (word : Str) : List Unit := slots word++(positions word).map (fun _ => ())

def copyCodes (word : Str) : List GateCode :=
  (List.range (positions word).length).map (fun i =>
    (4,(positions word)[i]?.getD 0,(slots word).length+i))

def copyWords (word : Str) : List (List Str) :=
  (copyCodes slots positions word).map (fun code => [gateWord (wholeSlots slots positions word) code])

def emitted (word : Str) : List (List Str) :=
  layers word++copyWords slots positions word++inverseCircuitWords (layers word)

variable {W k : ℕ → ℕ} (U : (n : ℕ) → Layered (W n))
  (controls : (n : ℕ) → Fin (k n) → Fin (W n))
  (hlayers_exact : ∀ n,layers (unary n)=(U n).map (List.map encInstr))
  (hslots_exact : ∀ n,(slots (unary n)).length=W n)
  (hpositions_exact : ∀ n,positions (unary n)=List.ofFn (fun i => (controls n i).val))

include hslots_exact hpositions_exact in
theorem wholeSlots_exact (n : ℕ) : (wholeSlots slots positions (unary n)).length=W n+k n := by
  simp only [wholeSlots,List.length_append,List.length_map,hslots_exact,hpositions_exact,List.length_ofFn]

include hslots_exact hpositions_exact in
theorem copyCodes_exact (n : ℕ) : copyCodes slots positions (unary n)=
    (List.finRange (k n)).map (fun i => encodeInstr
      (.cnot ((controls n i).castAdd (k n)) (Fin.natAdd (W n) i)
        (by intro h;have hv:=congrArg Fin.val h;dsimp at hv;have hi:=(controls n i).isLt;omega))) := by
  unfold copyCodes
  rw [hpositions_exact,hslots_exact]
  simp only [List.length_ofFn]
  have hr : List.range (k n)=(List.finRange (k n)).map Fin.val := by simp
  rw [hr,List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,List.getElem?_ofFn,i.isLt,dif_pos,Option.getD_some,
    encodeInstr,Fin.val_castAdd,Fin.val_natAdd]

include hslots_exact hpositions_exact in
theorem copyWords_exact (n : ℕ) : copyWords slots positions (unary n)=
    (CoherentXorCopy.circuit (controls n)).map (List.map encInstr) := by
  unfold copyWords
  rw [copyCodes_exact slots positions controls hslots_exact hpositions_exact]
  have hwidth : W n+k n ≤ (wholeSlots slots positions (unary n)).length := by
    rw [wholeSlots_exact slots positions controls hslots_exact hpositions_exact]
  simp only [List.map_map,Function.comp_def,gateWord_encode _ _ hwidth]
  simp [CoherentXorCopy.circuit,compileReversible,CoherentXorCopy.gate,ReversibleGate.compile,
    List.map_flatMap,List.flatMap_map,Function.comp_def]
  rw [List.map_eq_flatMap]

include hlayers_exact hslots_exact hpositions_exact in
theorem emitted_exact (n : ℕ) : emitted layers slots positions (unary n)=
    (QuantumXorOracle.circuit (U n) (controls n)).map (List.map encInstr) := by
  unfold emitted QuantumXorOracle.circuit
  rw [hlayers_exact,copyWords_exact slots positions controls hslots_exact hpositions_exact,
    inverseCircuitWords_correct]
  simp only [List.map_append,leftCircuit_instructionWords]

end InfoLossLAR.WorstCase.QuantumXorOracle.Native

end

end P2MDyadicModule188

/- Helper module OracleEmit. -/
section P2MDyadicModule189

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode ControlledNativeGates QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LoadedBatch.PostComposition Integration9_9.TM2PlatformSerialization

open NativeWordDescription PaddedDecoder

noncomputable section

abbrev CallInfo := (List Unit × List Unit) × Str

def oldFrame (v : CallInfo) := readFrame (v.1.1.map (fun _ => true),v.2)

@[fun_prop] theorem oldFrame_poly : Poly oldFrame := by unfold oldFrame;fun_prop

def ancSlots (v : CallInfo) : List Unit := (oldFrame v).1.map (fun _ => ())

@[fun_prop] theorem ancSlots_poly : Poly ancSlots := by unfold ancSlots;fun_prop

def useWires (v : CallInfo) : List ℕ :=
  ((oldFrame v).2.1.take v.1.2.length).map inputWidth

@[fun_prop] theorem useWires_poly : Poly useWires := by
  unfold useWires
  have ht := Poly.comp (f:=fun a : List Str × ℕ => a.1.take a.2) (g:=fun v : CallInfo => ((oldFrame v).2.1,v.1.2.length))
    (Integration9_9.TM2NativeFiniteDraw.take_poly (α:=Str)) (by fun_prop)
  fun_prop

def callWords (v : CallInfo) : List (List Str) :=
  let layers := (oldFrame v).2.2
  let gs := useWires v
  let work := ancSlots v
  let all := work ++ gs.map (fun _ => ())
  let copy := (List.range gs.length).map (fun i =>
    [gateWord all (4,gs[i]?.getD 0,work.length+i)])
  layers++copy++inverseCircuitWords layers

@[fun_prop] theorem callWords_poly : Poly callWords := by
  unfold callWords
  dsimp only
  have hr := Poly.comp (f:=fun s : List ℕ => List.range s.length) (g:=useWires) Poly.list_indices useWires_poly
  have hcopy : Poly (fun v : CallInfo => (List.range (useWires v).length).map (fun i =>
    [gateWord (ancSlots v ++ (useWires v).map (fun _ => ())) (4,(useWires v)[i]?.getD 0,(ancSlots v).length+i)])) := by
    apply Poly.list_map
    · have hget := Poly.list_getD_comp 0 (Poly.comp useWires_poly Poly.fst) Poly.snd
      fun_prop
    · exact hr
  fun_prop

def callCodes (v : CallInfo) : List GateCode := (callWords v).flatten.map readGateCode

@[fun_prop] theorem callCodes_poly : Poly callCodes := by
  unfold callCodes
  have hf : Poly (List.flatten : List (List Str) → List Str) := ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem parser_correct (F : MFamily) (l k : List Unit) :
    oldFrame ((l,k),F.encAt l.length)=
      (unary (Integration9_9.LoadedBatch.PostComposition.oldWidth F l.length),
        ((List.ofFn (F.outW l.length)).map (fun p => encNat p.val),(F.circ l.length).map (List.map encInstr))) := by
  unfold oldFrame
  simpa [unary] using readFrame_correct F l.length

theorem position_correct (F : MFamily) (l k : List Unit) (hf : k.length ≤ F.outLen l.length) :
    useWires ((l,k),F.encAt l.length)=List.ofFn (fun i => (controls F l.length k.length hf i).val) := by
  rw [useWires,parser_correct]
  apply List.ext_getElem
  · simp [hf]
  · intro i hl hr
    simp only [List.getElem_map,List.getElem_take,List.getElem_ofFn]
    have he (t : ℕ) : inputWidth (encNat t)=t := by simpa [encNat] using inputWidth_prefix t []
    rw [he]
    rfl

theorem callCodes_exact (F : MFamily) (l k : List Unit) (hf : k.length ≤ F.outLen l.length) :
    callCodes ((l,k),F.encAt l.length) =
      (QuantumXorOracle.circuit (F.circ l.length) (controls F l.length k.length hf)).flatten.map encodeInstr := by
  let v : CallInfo := ((l,k),F.encAt l.length)
  let layers (_ : Str) := (oldFrame v).2.2
  let slots (_ : Str) := ancSlots v
  let uses (_ : Str) := useWires v
  have hw (t : ℕ) : (slots (unary t)).length=l.length+(F.anc l.length+1) := by
    simp [slots,ancSlots,v,parser_correct,unary,Integration9_9.LoadedBatch.PostComposition.oldWidth]
  have hl (t : ℕ) : layers (unary t)=(F.circ l.length).map (List.map encInstr) := by
    simp [layers,v,parser_correct]
  have hu (t : ℕ) : uses (unary t)=List.ofFn (fun i => (controls F l.length k.length hf i).val) := position_correct F l k hf
  have he := QuantumXorOracle.Native.emitted_exact layers slots uses (fun _ => F.circ l.length)
    (fun _ => controls F l.length k.length hf) hl hw hu 0
  have hwords : callWords v = (QuantumXorOracle.circuit (F.circ l.length) (controls F l.length k.length hf)).map (List.map encInstr) := by
    rw [←he]
    simp only [QuantumXorOracle.Native.emitted,QuantumXorOracle.Native.copyWords,QuantumXorOracle.Native.copyCodes,QuantumXorOracle.Native.wholeSlots,callWords,slots,uses,layers,List.map_map,Function.comp_def]
  change (callWords v).flatten.map readGateCode = _
  rw [hwords]
  simp only [List.map_flatten,List.map_map,Function.comp_def,readGateCode_exact]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule189

/- Helper module StageEmit. -/
section P2MDyadicModule190

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates ControlledNativeCode

open FineCodec PaddedDecoder TM2Boolean.PolyProgramCircuit NativeQFTPlanCompile

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization NativeWordDescription

noncomputable section

theorem leftCode {n : ℕ} (m : ℕ) (i : Instr n) : encodeInstr (leftInstruction (m:=m) i)=encodeInstr i := by cases i <;> rfl

theorem leftCodeList {n : ℕ} (m : ℕ) (c : Layered n) : codeList (leftCircuit (m:=m) c)=codeList c := by
  simp [codeList,leftCircuit,List.map_flatten,List.map_map,Function.comp_def,leftCode]

theorem placedCodes (h k l j a : ℕ) (U : Layered (l+a+k)) :
    (codeList U).map (fun g => positioned (((h,k),l,j,a),g)) =
      codeList (relocateCircuit (oraclePerm h k l j a).toEmbedding (leftCircuit (m:=h+j) U)) := by
  rw [←leftCodeList (h+j) U]
  let V := leftCircuit (m:=h+j) U
  change (codeList V).map _=codeList (relocateCircuit _ V)
  simp only [codeList,List.map_map,Function.comp_def,positioned_exact,relocateCircuit,List.map_flatten]

def eraseWords (w : List Unit) : List GateCode :=
  (CoherentClassicalOracle.publicLayers queryProgram (w.map (fun _ => true))).flatten.map readGateCode

@[fun_prop] theorem eraseWords_poly : Poly eraseWords := by
  unfold eraseWords
  have hf : Poly (List.flatten : List (List Str) → List Str) := ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  have ho := CoherentClassicalOracle.publicLayers_poly queryProgram
  fun_prop

theorem eraseWords_eq (w : List Unit) :
    eraseWords w=codeList (CoherentClassicalOracle.fullCircuit queryProgram w.length) := by
  rw [eraseWords,show w.map (fun _ => true)=unary w.length by simp [unary],CoherentClassicalOracle.publicLayers_exact]
  simp only [codeList,List.map_flatten,List.map_map,Function.comp_def,readGateCode_exact]

theorem castCodes {s u v : ℕ} (h : u=v) (C : Layered (s+u)) : codeList (castCapacity h C)=codeList C := by subst v;rfl

theorem eraseCodes_eq (E K L J A D : ℕ) (w : List Unit) (hc : capacity queryProgram w.length=L+D) :
    (eraseWords w).map (fun g => eraseGate ((((E,w.length),(K,L)),((J,A),machineSpace w.length)),g)) =
      codeList (uniformEraser E w.length K L J A D hc) := by
  rw [eraseWords_eq,←castCodes (s:=w.length+machineSpace w.length) hc]
  unfold uniformEraser
  simp only [codeList,List.map_map,Function.comp_def,eraseGate_exact,relocateCircuit,List.map_flatten]

abbrev EmitterInput := (List Unit × NativeQFTPlanCompile.Input) × CallInfo × (List Unit × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)

/-- Metadata is ordered as (dimension, precision request), framed BDD call,
(unary query-cleanup input width, protected prefix size, header size), and
(residual size, BDD work size, cleanup work size, extra cleanup output size). -/
def stageCodes (a : ℕ) (v : EmitterInput) : List GateCode :=
  let ⟨nt,x⟩ := v.1
  let call := v.2.1
  let ⟨wt,E,H⟩ := v.2.2.1
  let ⟨J,A,M,D⟩ := v.2.2.2
  let K := call.1.2.length
  let L := call.1.1.length
  let W := wt.length
  let data := nt.length*x.1.length
  let S := rearSize K L J A M D
  (callCodes call).map (fun g => positioned (((E+W,K),L,J,A),g))++
  (eraseWords wt).map (fun g => eraseGate ((((E,W),(K,L)),((J,A),M)),g))++
  (allRows a (nt,x)).map (fun g => positioned (((E+H,0),data,S,2),g))

@[fun_prop] theorem stageCodes_poly (a : ℕ) : Poly (stageCodes a) := by
  unfold stageCodes
  dsimp only
  have app (f g : EmitterInput → List GateCode) (hf : Poly f) (hg : Poly g) : Poly (fun x => f x ++ g x) :=
    Poly.comp Poly.list_append (Poly.pair hf hg)
  apply app
  · apply app
    · apply Poly.list_map
      · apply Poly.comp positioned_poly
        exact Poly.pair (by fun_prop) Poly.snd
      · exact Poly.comp callCodes_poly (by fun_prop)
    · apply Poly.list_map
      · apply Poly.comp eraseGate_poly
        exact Poly.pair (by fun_prop) Poly.snd
      · exact Poly.comp eraseWords_poly (by fun_prop)
  · apply Poly.list_map
    · apply Poly.comp positioned_poly
      exact Poly.pair (by unfold rearSize;fun_prop) Poly.snd
    · exact Poly.comp (allRows_poly a) (by fun_prop)

theorem stageCodes_exact (a : ℕ) (nt : List Unit) (x : NativeQFTPlanCompile.Input) (F : MFamily) (l k wt : List Unit)
    (E H J D : ℕ)
    (hf : k.length≤F.outLen l.length) (hc : capacity queryProgram wt.length=l.length+D) :
    let W := wt.length
    let A := F.anc l.length+1
    let M := machineSpace W
    let S := rearSize k.length l.length J A M D
    let O := relocateCircuit (oraclePerm (E+W) k.length l.length J A).toEmbedding
      (leftCircuit (m:=E+W+J) (QuantumXorOracle.circuit (F.circ l.length) (controls F l.length k.length hf)))
    let X := uniformEraser E W k.length l.length J A D hc
    let Q := relocateCircuit (qftPerm (E+H) (nt.length*x.1.length) S).toEmbedding
      (leftCircuit (m:=E+H+S) (GridReadout.Axis.circuit a x (List.finRange nt.length)))
    stageCodes a ((nt,x),((l,k),F.encAt l.length),(wt,E,H),(J,A,M,D))=codeList O++codeList X++codeList Q := by
  dsimp only
  unfold stageCodes
  dsimp only
  rw [callCodes_exact F l k hf,eraseCodes_eq E k.length l.length J (F.anc l.length+1) D wt hc,allRows_exact]
  change (codeList _).map _ ++ _ ++ (codeList _).map _ = _
  rw [placedCodes,placedCodes]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule190

/- Helper module CodesAt. -/
section P2MDyadicModule191

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates ControlledNativeCode

open FineCodec PaddedDecoder TM2Boolean.PolyProgramCircuit NativeQFTPlanCompile

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization NativeWordDescription

noncomputable section

theorem stageCodes_at (a : ℕ) (nt : List Unit) (x : NativeQFTPlanCompile.Input) (F : MFamily) (l k wt : List Unit)
    (E H J D W : ℕ) (hw : wt.length=W)
    (hf : k.length≤F.outLen l.length) (hc : capacity queryProgram W=l.length+D) :
    let A := F.anc l.length+1
    let M := machineSpace W
    let S := rearSize k.length l.length J A M D
    let O := relocateCircuit (oraclePerm (E+W) k.length l.length J A).toEmbedding
      (leftCircuit (m:=E+W+J) (QuantumXorOracle.circuit (F.circ l.length) (controls F l.length k.length hf)))
    let X := uniformEraser E W k.length l.length J A D hc
    let Q := relocateCircuit (qftPerm (E+H) (nt.length*x.1.length) S).toEmbedding
      (leftCircuit (m:=E+H+S) (GridReadout.Axis.circuit a x (List.finRange nt.length)))
    stageCodes a ((nt,x),((l,k),F.encAt l.length),(wt,E,H),(J,A,M,D))=codeList O++codeList X++codeList Q := by
  subst W
  exact stageCodes_exact a nt x F l k wt E H J D hf hc

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule191

/- Helper module StageExecute. -/
section P2MDyadicModule192

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates QuantumXorOracle

noncomputable section

def castCircuit {n m : ℕ} (e : n=m) (C : Layered n) : Layered m := e ▸ C

theorem castCircuit_codes {n m : ℕ} (e : n=m) (C : Layered n) : codeList (castCircuit e C)=codeList C := by subst m;rfl

theorem castCircuit_run {n m : ℕ} (e : n=m) (C : Layered n) (v : QState n) :
    runLayered (castCircuit e C) (castState e v)=castState e (runLayered C v) := by subst m;rfl

theorem run_concat {n : ℕ} (C D : Layered n) (v : QState n) :
    runLayered (C++D) v=runLayered D (runLayered C v) := by simp only [runLayered,List.foldl_append]

theorem codes_concat {n : ℕ} (C D : Layered n) : codeList (C++D)=codeList C++codeList D := by simp [codeList]

theorem left_layered_ground {n k : ℕ} (C : Layered n) (z : Bits k) (v : QState n) :
    runLayered (leftCircuit (m:=k) C) (attach z v)=attach z (runLayered C v) := by
  simp only [attach_tensor,leftCircuit_tensor]

def onArena {n k d N : ℕ} (e : (n+k)+d=N) (O : Layered n) (X : Layered (n+k)) (Q : Layered N) :=
  castCircuit e (leftCircuit (m:=d) (leftCircuit (m:=k) O++X))++Q

theorem arena_codes {n k d N : ℕ} (e : (n+k)+d=N) (O : Layered n) (X : Layered (n+k)) (Q : Layered N) :
    codeList (onArena e O X Q)=codeList O++codeList X++codeList Q := by
  simp only [onArena,codes_concat,castCircuit_codes,leftCodeList]

theorem arena_runs {n k d N : ℕ} (e : (n+k)+d=N) (O : Layered n) (X : Layered (n+k)) (Q : Layered N)
    (v : QState n) (z : Bits k) (y : Bits d) :
    runLayered (onArena e O X Q) (castState e (attach y (attach z v))) =
    runLayered Q (castState e (attach y (runLayered X (attach z (runLayered O v))))) := by
  simp only [onArena,run_concat,castCircuit_run,left_layered_ground]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule192

/- Helper module GroundTape. -/
section P2MDyadicModule193

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute QuantumXorOracle

noncomputable section

def padWire {s N : ℕ} (h : s≤N) : Bits s ↪ Bits N :=
  transported (Nat.add_sub_of_le h) (appendEmbedding (0:Bits (N-s)))

theorem padWire_at {s N : ℕ} (h : s≤N) (v : Bits s) :
    List.ofFn (padWire h v)=List.ofFn v++List.replicate (N-s) false := by
  have hz {w u : ℕ} (hc : w=u) (e : Bits s ↪ Bits w) (b : Bits s) :
        (transported hc e) b=castBits hc (e b) := by subst u;rfl
  rw [padWire,hz,castBits_list]
  simp only [appendEmbedding,Function.Embedding.coeFn_mk,List.ofFn_fin_append]
  exact congrArg (List.append (List.ofFn v)) (List.ofFn_const (N-s) false)

def castLinear {s N : ℕ} (h : s=N) : QState s →ₗ[ℂ] QState N := h ▸ LinearMap.id

theorem castLinear_at {s N : ℕ} (h : s=N) (v : QState s) : castLinear h v=castState h v := by subst N;rfl

theorem on_basis_all {s N : ℕ} (f : QState s →ₗ[ℂ] QState N) (e : Bits s ↪ Bits N)
    (he : ∀ b,f (basis b)=basis (e b)) (v : QState s) : f v=basisEmbedding e v := by
  have hv : v=∑ b,v b • basis b := by
    funext b
    simp [Finset.sum_apply,basis,Pi.smul_apply,smul_eq_mul]
  rw [hv,map_sum]
  simp only [map_smul,he]
  rw [←hv]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule193

/- Helper module StageReady. -/
section P2MDyadicModule194

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FineCodec CoherentInjection PaddedDecoder ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

noncomputable section

attribute [local irreducible] FineCodec.forwardProgram FineCodec.inverseProgram FineCodec.queryProgram

abbrev NativeStageInfo := (List Unit × NativeQFTPlanCompile.Input) × (Config × Str) × (List Unit × List Unit) × Str

def headOf (v : NativeStageInfo) : Str :=
  lengthToken v.2.2.1.1 ++ encS (header v.2.1.1) ++ lengthToken v.2.2.1.2 ++ encS v.2.1.2 ++ lengthToken v.1.1

@[fun_prop] theorem headOf_poly : Poly headOf := by unfold headOf;fun_prop

def cleanupTicks (v : NativeStageInfo) := (headOf v).map (fun _ => ())++v.1.1.flatMap (fun _ => v.1.2.1)

@[fun_prop] theorem cleanupTicks_poly : Poly cleanupTicks := by unfold cleanupTicks;fun_prop

def callInfoOf (v : NativeStageInfo) : CallInfo := ((v.2.1.1.1.2.2,v.2.1.1.1.2.1),v.2.2.2)

@[fun_prop] theorem callInfoOf_poly : Poly callInfoOf := by unfold callInfoOf;fun_prop

def boolTicks (t : List Unit) : Str := t.map (fun _ => true)

@[fun_prop] theorem boolTicks_poly : Poly boolTicks := by unfold boolTicks;fun_prop

theorem boolTicks_eq (t : List Unit) : boolTicks t=unary t.length := by simp [boolTicks,unary]

def codecLayout (t : List Unit) : ℕ × ℕ × ℕ :=
  let s := boolTicks t
  let b := inverseWord FineCodec.forwardProgram s
  ((outputTicks FineCodec.inverseProgram b).length,(outputTicks FineCodec.forwardProgram s).length,
    (workTicks FineCodec.forwardProgram s).length+(workTicks FineCodec.inverseProgram b).length)

@[fun_prop] theorem codecLayout_poly : Poly codecLayout := by unfold codecLayout;dsimp only;fun_prop

theorem codecLayout_exact (t : List Unit) : codecLayout t=(codecOld t.length,codecCap t.length,codecWork t.length) := by
  simp only [codecLayout,boolTicks_eq,inverseWord_exact,outputTicks_length,workTicks_length]

def cleanupLayout (t : List Unit) : ℕ × ℕ :=
  ((workTicks queryProgram (boolTicks t)).length,(outputTicks queryProgram (boolTicks t)).length)

theorem cleanupLayout_exact (t : List Unit) : cleanupLayout t=(machineSpace t.length,TM2Boolean.PolyProgramCircuit.capacity queryProgram t.length) := by
  simp only [cleanupLayout,boolTicks_eq,workTicks_length,outputTicks_length]

def workOf (v : CallInfo) := (ancSlots v).length - v.1.1.length

@[fun_prop] theorem workOf_poly : Poly workOf := by unfold workOf;fun_prop

theorem workOf_exact (F : MFamily) (l k : List Unit) : workOf ((l,k),F.encAt l.length)=F.anc l.length+1 := by
  simp [workOf,ancSlots,parser_correct,unary,Integration9_9.LoadedBatch.PostComposition.oldWidth]

def stageMeta (v : NativeStageInfo) : EmitterInput :=
  let h := (headOf v).length
  let w := cleanupTicks v
  let cl := codecLayout v.2.2.1.1
  let m := cleanupLayout w
  let call := callInfoOf v
  let k := call.1.2.length
  let l := call.1.1.length
  let j := cl.2.1-(w.length+k+l)+cl.2.2
  (v.1,call,(w,cl.1,h),(j,workOf call,m.1,m.2-l))

@[fun_prop] theorem stageMeta_poly : Poly stageMeta := by unfold stageMeta;dsimp only;fun_prop

def programFor (a : ℕ) (v : NativeStageInfo) := stageCodes a (stageMeta v)

@[fun_prop] theorem programFor_poly (a : ℕ) : Poly (programFor a) := by unfold programFor;exact Poly.comp (f:=stageCodes a) (g:=stageMeta) (stageCodes_poly a) stageMeta_poly

theorem headerOf_eq {m : ℕ} (F : MFamily) (nt : List Unit) (x : NativeQFTPlanCompile.Input)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ)
    (k l s t : List Unit) (R : ℚ) (prec : ℕ) (pool : Fin m→Fin nt.length→ℤ) :
    let c := queryConfig x.1 k l R prec pool
    headOf ((nt,x),(c,encMat encI B),(s,t),F.encAt l.length)=commonHead B c s t := by
  simp only [headOf,commonHead,lengthToken_eq]

theorem cleanupTicks_size (v : NativeStageInfo) :
    (cleanupTicks v).length=(headOf v).length+v.1.1.length*v.1.2.1.length := by
  simp [cleanupTicks]

theorem stageMeta_exact {m : ℕ} (F : MFamily) (nt : List Unit) (x : NativeQFTPlanCompile.Input)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ)
    (k l s t : List Unit) (R : ℚ) (prec : ℕ) (pool : Fin m→Fin nt.length→ℤ) :
    let c := queryConfig x.1 k l R prec pool
    let v : NativeStageInfo := ((nt,x),(c,encMat encI B),(s,t),F.encAt l.length)
    let H := (commonHead B c s t).length
    let w := cleanupTicks v
    let W := H+nt.length*x.1.length
    let G := TM2Boolean.PolyProgramCircuit.capacity queryProgram W-l.length
    stageMeta v=((nt,x),((l,k),F.encAt l.length),(w,codecOld s.length,H),
      (middleTail s.length (fixedPart H nt.length x.1.length k.length l.length),F.anc l.length+1,machineSpace W,G)) := by
  dsimp only
  rw [stageMeta]
  simp only [codecLayout_exact,cleanupLayout_exact,cleanupTicks_size,headerOf_eq,middleTail,fixedPart]
  simp only [callInfoOf,queryConfig,workOf_exact]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule194

/- Helper module EndGates. -/
section P2MDyadicModule195

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentInjection ControlledNativeCode QuantumXorOracle

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization FineCodec NativeWordDescription

noncomputable section

attribute [local irreducible] FineCodec.forwardProgram FineCodec.inverseProgram FineCodec.queryProgram

abbrev fineSize (s : List Unit) := totalWidth FineCodec.forwardProgram FineCodec.inverseProgram s.length

abbrev fineCirc (s : List Unit) := circuit FineCodec.forwardProgram FineCodec.inverseProgram s.length

def fineCodes (t : List Unit) := (CoherentInjection.emitted FineCodec.forwardProgram FineCodec.inverseProgram (boolTicks t)).flatten.map readGateCode

@[fun_prop] theorem fineCodes_poly : Poly fineCodes := by
  unfold fineCodes
  have hf : Poly (List.flatten : List (List Str) → List Str) := ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  have he := CoherentInjection.emitted_poly FineCodec.forwardProgram FineCodec.inverseProgram
  fun_prop

theorem fineCodes_eq (t : List Unit) : fineCodes t=codeList (fineCirc t) := by
  rw [fineCodes,boolTicks_eq,CoherentInjection.emitted_exact]
  simp only [codeList,List.map_flatten,List.map_map,Function.comp_def,readGateCode_exact]

attribute [local irreducible] fineCodes programFor

def allStageCodes (a : ℕ) (v : NativeStageInfo) := fineCodes v.2.2.1.1++programFor a v

@[fun_prop] theorem allStageCodes_poly (a : ℕ) : Poly (allStageCodes a) := by
  unfold allStageCodes
  have hp : Poly (fun v : NativeStageInfo => v.2.2.1.1) := Poly.comp Poly.fst (Poly.comp Poly.fst (Poly.comp Poly.snd Poly.snd))
  have hpre : Poly (fun v : NativeStageInfo => fineCodes v.2.2.1.1) := Poly.comp (f:=fineCodes) (g:=fun v : NativeStageInfo => v.2.2.1.1) fineCodes_poly hp
  exact Poly.comp (f:=fun x : List GateCode × List GateCode => x.1++x.2)
    (g:=fun v : NativeStageInfo => (fineCodes v.2.2.1.1,programFor a v)) Poly.list_append (Poly.pair hpre (programFor_poly a))

def fullLocal {n k d N : ℕ} (s : List Unit) (F : ℕ) (h : fineSize s+(F+1)=n) (e : (n+k)+d=N)
    (O : Layered n) (X : Layered (n+k)) (Q : Layered N) : Layered N :=
  onArena e (castCircuit h (leftCircuit (m:=F+1) (fineCirc s))++O) X Q

def groundLocal {n k d N : ℕ} (s : List Unit) (F : ℕ) (h : fineSize s+(F+1)=n) (e : (n+k)+d=N)
    (z : Bits k) (y : Bits d) (v : QState (fineSize s)) : QState N :=
  castState e (attach y (attach z (castState h (attach (0:Bits (F+1)) v))))

theorem fullLocal_codes {n k d N : ℕ} (s : List Unit) (F : ℕ) (h : fineSize s+(F+1)=n) (e : (n+k)+d=N)
    (O : Layered n) (X : Layered (n+k)) (Q : Layered N) :
    codeList (fullLocal s F h e O X Q)=fineCodes s++(codeList O++codeList X++codeList Q) := by
  simp only [fullLocal,arena_codes,codes_concat,castCircuit_codes,leftCodeList,fineCodes_eq,List.append_assoc]

theorem fullLocal_runs {n k d N : ℕ} (s : List Unit) (F : ℕ) (h : fineSize s+(F+1)=n) (e : (n+k)+d=N)
    (O : Layered n) (X : Layered (n+k)) (Q : Layered N) (z : Bits k) (y : Bits d) (v : QState (fineSize s)) :
    runLayered (fullLocal s F h e O X Q) (groundLocal s F h e z y v) =
      runLayered Q (castState e (attach y (runLayered X (attach z (runLayered O (machineRun s F h v)))))) := by
  simp only [fullLocal,groundLocal,arena_runs,run_concat,castCircuit_run,left_layered_ground,machineRun,fineCirc]

theorem machineRun_unit {N : ℕ} (s : List Unit) (F : ℕ) (e : fineSize s+(F+1)=N) (v : QState (fineSize s))
    (hv : stateNorm v=1) : stateNorm (machineRun s F e v)=1 := by
  subst N
  change stateNorm (attach (0:Bits (F+1)) (runLayered (fineCirc s) v))=1
  rw [attach_norm,show stateNorm (runLayered (fineCirc s) v)=stateNorm v from (circuitIsometry _).norm_map _,hv]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule195

/- Helper module CanonicalGround. -/
section P2MDyadicModule196

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1250000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity QuantumXorOracle CoherentComputeUncompute

noncomputable section

theorem pad_ground {N A E M D : ℕ} (s : List Unit) (F : ℕ)
    (h : fineSize s+(F+1)=A) (e : (A+(M+D))+2=E) (w : E=N)
    (v : QState (fineSize s)) :
    castState w (groundLocal s F h e (Fin.append (0:Bits M) (0:Bits D)) (0:Bits 2) v) =
      basisEmbedding (padWire (show fineSize s ≤ N by omega)) v := by
  let T := (castLinear w).comp ((castLinear e).comp ((attach (0:Bits 2)).comp
    ((attach (Fin.append (0:Bits M) (0:Bits D))).comp ((castLinear h).comp (attach (0:Bits (F+1)))))))
  have teq : T v=castState w (groundLocal s F h e (Fin.append (0:Bits M) (0:Bits D)) (0:Bits 2) v) := by
    simp only [T,LinearMap.coe_comp,Function.comp_apply,castLinear_at,groundLocal]
  rw [←teq]
  apply on_basis_all T _ _ v
  intro x
  simp only [T,LinearMap.coe_comp,Function.comp_apply,castLinear_at,PaddedDecoder.attached_basis,castState_basis]
  apply congrArg basis
  apply List.ofFn_inj.mp
  have zero (t : ℕ) : List.ofFn (0:Bits t)=List.replicate t false := List.ofFn_const _ _
  rw [padWire_at]
  simp only [castBits_list,List.ofFn_fin_append,zero,List.append_assoc]
  have len : N-fineSize s=F+1+M+D+2 := by omega
  rw [len]
  simp only [List.replicate_add,List.append_assoc]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule196

/- Helper module RawProgram. -/
section P2MDyadicModule197

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FineCodec CoherentInjection PaddedDecoder ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

noncomputable section

attribute [local irreducible] FineCodec.forwardProgram FineCodec.inverseProgram queryProgram

abbrev FromPoolInput := (List Unit × NativeQFTPlanCompile.Input) × (Str × Str × Str) × ((List Unit × List Unit) × (List Unit × List Unit)) × OldTable × Str

def withPool (v : FromPoolInput) : NativeStageInfo :=
  let ⟨(nt,x),(mat,r,prec),((s,t),(k,l)),rows,desc⟩ := v
  ((nt,x),(setupFromPool (((x.1,k,l),(r,prec)),rows),mat),(s,t),desc)

@[fun_prop] theorem withPool_poly : Poly withPool := by unfold withPool;fun_prop

theorem withPool_exact (nt : List Unit) (x : NativeQFTPlanCompile.Input) (mat : Str) (r : ℚ) (prec : ℕ)
    (s t k l count width : List Unit) (tape desc : Str) (pool : Fin count.length→Fin nt.length→ℤ)
    (h : ∀ i, encVec encI (pool i) <+: (tape.drop (i.val*width.length)).take width.length) :
    withPool ((nt,x),(mat,encQ r,unary prec),((s,t),(k,l)),((count,width),tape),desc)=
      ((nt,x),(queryConfig x.1 k l r prec pool,mat),(s,t),desc) := by
  dsimp only [withPool]
  rw [confCorrect x.1 k l count width r prec tape pool h]

/-- The active slice starts after public original-input and header words. -/
def readStart (v : NativeStageInfo) := (stageMeta v).2.2.1.2.1+(stageMeta v).2.2.1.2.2

@[fun_prop] theorem readStart_poly : Poly readStart := by unfold readStart;fun_prop

def activeWidth (v : NativeStageInfo) :=
  let met := stageMeta v
  let ⟨nt,x⟩ := met.1
  let call := met.2.1
  let ⟨_,E,H⟩ := met.2.2.1
  let ⟨J,A,M,D⟩ := met.2.2.2
  (E+H)+nt.length*x.1.length+rearSize call.1.2.length call.1.1.length J A M D+2

@[fun_prop] theorem activeWidth_poly : Poly activeWidth := by unfold activeWidth rearSize;dsimp only;fun_prop

def arenaTicks (v : NativeStageInfo) : List Unit :=
  let call := callInfoOf v
  let w := cleanupTicks v
  wholeSlots FineCodec.forwardProgram FineCodec.inverseProgram (boolTicks v.2.2.1.1)++
    (ancSlots call).drop call.1.1.length++workTicks queryProgram (boolTicks w)++
    (outputTicks queryProgram (boolTicks w)).drop call.1.1.length++[(),()]

@[fun_prop] theorem arenaTicks_poly : Poly arenaTicks := by
  unfold arenaTicks
  dsimp only
  have drop : Poly (fun v : List Unit × ℕ => v.1.drop v.2) := ⟨PolyProgram.listDrop Automatic.enc ()⟩
  have ha : Poly (fun v : NativeStageInfo => (ancSlots (callInfoOf v)).drop (callInfoOf v).1.1.length) :=
    Poly.comp drop (Poly.pair (Poly.comp ancSlots_poly callInfoOf_poly) (by fun_prop))
  have hb : Poly (fun v : NativeStageInfo => (outputTicks queryProgram (boolTicks (cleanupTicks v))).drop (callInfoOf v).1.1.length) :=
    Poly.comp drop (Poly.pair (by fun_prop) (by fun_prop))
  fun_prop

theorem arenaTicks_exact (v : NativeStageInfo) :
    (arenaTicks v).length = totalWidth FineCodec.forwardProgram FineCodec.inverseProgram v.2.2.1.1.length+
    workOf (callInfoOf v)+machineSpace (cleanupTicks v).length+
    (TM2Boolean.PolyProgramCircuit.capacity queryProgram (cleanupTicks v).length-(callInfoOf v).1.1.length)+2 := by
  simp only [arenaTicks,List.length_append,List.length_drop,List.length_cons,List.length_nil,boolTicks_eq,wholeSlots_length,
    workTicks_length,outputTicks_length,workOf]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule197

/- Helper module CompleteReadout. -/
section P2MDyadicModule198

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2600000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity CoherentInjection QuantumXorOracle FiniteGateTransport ControlledNativeGates

open IntegerBasis FineCodec GaussianPoissonSeries SharedPoolCoherence NativeQFTPlanCompile PaddedDecoder TM2Boolean.PolyProgramCircuit

open NativeDualQuotient (Residual)

open CoherentComputeUncompute CoherentDecoder GridReadout.Axis

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

attribute [local irreducible] allStageCodes programFor withPool stageCodes activeWidth readStart machineRun beforeMachine

abbrev stageInput (a : ℕ) (v : FromPoolInput) := allStageCodes a (withPool v)

/-- A single raw gate generator, shared for every history. On the occupied
part of the fine-codec input the comparison is a sum over all residuals and
short dual points. The conclusion measures the complete physical output
state of one actual finite register from the native codec through BDD and QFT. -/
theorem coherent_step (C : MFamily) (hC : IsMQPT C) :
    ∃ F : MFamily, IsMQPT F ∧ ∃ a : ℕ, 0<a ∧
    ∀ (nt : List Unit) (x : NativeQFTPlanCompile.Input) (count pw : List Unit) (tape : Str)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (hB : B.det≠0) (r cut : ℝ) (hr : 0<r) (hc : 0<cut)
    (hn : 0<nt.length) (hg : gridAdequate B r (2^x.1.length))
    (hs : (nt.length:ℝ)*(1/(Real.sqrt 2*r))^2 ≤ cut^2) (sep : Separated (StageL B hB) cut)
    (R : ℚ) (hR : 0<R) (hcut : cut ≤ (famσ nt.length:ℝ)/(2*(R:ℝ)))
    (budget : ℕ) (hk : precision nt.length x.1.length budget ≤ x.2.length)
    (prec : ℕ) (pool : Fin count.length→Fin nt.length→ℤ)
    (table : ∀ i, encVec encI (pool i) <+: (tape.drop (i.val*pw.length)).take pw.length)
    (k l s t : List Unit) (hkl : k.length≤ l.length)
    [Fintype (Residual B)] [Fintype (StageI B hB x.1.length cut)]
    (hf : ∀ res p,(pack (frameCode B hB x.1 k l s t R prec pool cut res p)).length ≤ s.length)
    (hA : ∀ p : StageI B hB x.1.length cut,(encVec encI (promisedShort B hB R hR cut hcut p).answer).length≤ k.length)
    (hL : ∀ p : StageI B hB x.1.length cut,(encS (word prec pool (promisedShort B hB R hR cut hcut p))).length≤ l.length),
    let inp : FromPoolInput := ((nt,x),(encMat encI B,encQ R,unary prec),((s,t),(k,l)),((count,pw),tape),F.encAt l.length)
    let info := withPool inp
    let N := activeWidth info
    let q (p : StageI B hB x.1.length cut) := promisedShort B hB R hR cut hcut p
    let g := taper B hB x.1.length r cut hr
    let src (z : Residual B×StageI B hB x.1.length cut) := frameCode B hB x.1 k l s t R prec pool cut z.1 z.2
    ∃ U : Layered N, codeList U = stageInput a inp ∧
    ∃ hwidth : fineSize s ≤ N,
    ∀ (j : Hilbert (Residual B)) (_hj : ‖j‖=1) (v : QState (fineSize s)) (_hv : stateNorm v=1),
    let out := WithLp.toLp 2 (runLayered U (basisEmbedding (padWire hwidth) v))
    let read (p : Bits N) := signedSlice ((nt,x.1),readStart info,List.ofFn p)
    bornEvent (fun p => ∃ z : Fin nt.length→ℤ, encVec encI z <+: read p) out = 1 ∧
    ∀ event : Finset (Fin nt.length→ℤ),
      |bornEvent (fun p => ∃ z ∈ event, encVec encI z <+: read p) out - ∑ z ∈ event, RegevSketch.coefficientMass B r z| ≤
      2*stateNorm (v-beforeMachine s src (fun z => j z.1*g z.2))+4*Real.sqrt (failureMass C prec pool q g.ofLp)+
        4*Real.sqrt (2*(1/2:ℝ)^nt.length)+1/(4*((budget:ℝ)+1))+GridReadout.gridError nt.length := by
  obtain ⟨F,hF,width,a,ha,step⟩ := single_physical_stage C hC
  refine ⟨F,hF,a,ha,?_⟩
  intro nt x count pw tape B hB r cut hr hc hn hg hs sep R hR hcut budget hk prec pool table k l s t hkl _ _ hf hA hL
  intro inp info N q g src
  let conf := queryConfig x.1 k l R prec pool
  let known : NativeStageInfo := ((nt,x),(conf,encMat encI B),(s,t),F.encAt l.length)
  have hinfo : info=known := withPool_exact nt x _ R prec s t k l count pw tape _ pool table
  let n := nt.length
  let b := x.1.length
  let head := commonHead B conf s t
  let H := head.length
  let W := H+n*b
  let E := codecOld s.length
  let A := F.anc l.length+1
  let J := middleTail s.length (fixedPart H n b k.length l.length)
  let M := machineSpace W
  let D := capacity queryProgram W-l.length
  let S := rearSize k.length l.length J A M D
  let wt := cleanupTicks known
  have hh0 : headOf known=head := headerOf_eq F nt x B k l s t R prec pool
  have wtLen : wt.length=W := by rw [show wt=cleanupTicks known from rfl,cleanupTicks_size,hh0]
  have hm : stageMeta known=((nt,x),((l,k),F.encAt l.length),(wt,E,H),(J,A,M,D)) := stageMeta_exact _ _ _ B k l s t R prec pool
  have hnW : N=(E+H)+n*b+S+2 := by change activeWidth info=_;rw [hinfo,activeWidth,hm]
  have readpos : readStart info=E+H := by rw [hinfo,readStart,hm]
  have hRI : Nonempty (Residual B) := ⟨(NativeDualQuotient.integerPointsEquiv B hB 0).1⟩
  let : Nonempty (Residual B) := hRI
  obtain ⟨h,je,hnear⟩ := machine_stage B hB x.1 k l s t R hR prec pool cut hc hcut sep (F.anc l.length) hf hA
  let core := step nt x count.length E J B hB r cut hr hc hn hg hs sep R hR hcut budget hk prec pool k l s t hkl hL
    (Residual B) (0:Bits E) je
  let r0 := Classical.choice hRI
  let one (i : Residual B) : ℂ := if i=r0 then 1 else 0
  have normOne : ∑ i, ‖one i‖^2=1 := by
    rw [Finset.sum_eq_single r0]
    · simp [one]
    · intro i _ hi;simp [one,hi]
    · simp
  obtain ⟨cap,_⟩ := core one normOne
  let O := relocateCircuit (oraclePerm (E+W) k.length l.length J A).toEmbedding (leftCircuit (m:=E+W+J)
    (QuantumXorOracle.circuit (F.circ l.length) (controls F l.length k.length (hkl.trans (width _)))))
  let X := uniformEraser E W k.length l.length J A D cap
  let Q := relocateCircuit (qftPerm (E+H) (n*b) S).toEmbedding (leftCircuit (m:=E+H+S) (GridReadout.Axis.circuit a x (List.finRange n)))
  let e := arenaSize E H (n*b) k.length l.length J A M D
  let U := fullLocal s (F.anc l.length) h e O X Q
  let bdd0 := Fin.append (0:Bits M) (0:Bits D)
  let init := groundLocal s (F.anc l.length) h e bdd0 (0:Bits 2)
  have ne : (E+W)+k.length+l.length+J+A+(M+D)+2=(E+H)+n*b+S+2 := e
  have fwidth : fineSize s+A=(E+W)+k.length+l.length+J+A := h
  have htape : fineSize s ≤ N := by omega
  refine ⟨castCircuit hnW.symm U,?_,htape,?_⟩
  · rw [castCircuit_codes]
    change codeList (fullLocal s (F.anc l.length) h e O X Q)=_
    rw [fullLocal_codes]
    change fineCodes s++(codeList O++codeList X++codeList Q)=allStageCodes a (withPool inp)
    rw [show withPool inp=known from hinfo,allStageCodes]
    congr 1
    rw [programFor,hm]
    exact (stageCodes_at a nt x F l k wt E H J D W wtLen (hkl.trans (width _)) cap).symm
  · intro j hj v hv
    obtain ⟨_,he⟩ := core j (residual_mass _ hj)
    specialize he (machineRun s (F.anc l.length) h v) (machineRun_unit s _ h v hv)
    dsimp only at he ⊢
    have run := fullLocal_runs s (F.anc l.length) h e O X Q bdd0 (0:Bits 2) v
    have near := hnear (fun z => j z.1*g z.2) v
    have pad := pad_ground s (F.anc l.length) h e hnW.symm v
    change castState hnW.symm (init v) = basisEmbedding (padWire htape) v at pad
    rw [←pad,show runLayered (castCircuit hnW.symm U) (castState hnW.symm (init v))=castState hnW.symm (runLayered U (init v)) from castCircuit_run _ _ _,run]
    rw [←near]
    rw [readpos]
    have measure {w z : ℕ} (h : w=z) (u : QState w) (E : Str→Prop) :
        bornEvent (fun p => E (List.ofFn p)) (WithLp.toLp 2 (castState h u))=
        bornEvent (fun p => E (List.ofFn p)) (WithLp.toLp 2 u) := by subst z;rfl
    constructor
    · exact (measure _ _ (fun bits => ∃ z : Fin n→ℤ, encVec encI z <+: signedSlice ((nt,x.1),E+H,bits))).trans he.1
    · intro ev
      rw [measure _ _ (fun bits => ∃ z ∈ ev, encVec encI z <+: signedSlice ((nt,x.1),E+H,bits))]
      exact he.2 ev

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule198

/- Helper module ExpandArena. -/
section P2MDyadicModule199

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1550000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentComputeUncompute ControlledNativeCode ControlledNativeGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

variable {f n : ℕ} (h : f≤n) (j : ℕ)

def growWires : Fin (f+j) ↪ Fin (n+j) where
  toFun i := ⟨if i.val<f then i.val else n+(i.val-f),by split_ifs <;> omega⟩
  inj' i k eq := by
    have he := congrArg Fin.val eq
    dsimp only at he
    apply Fin.ext
    split_ifs at he <;> omega

def growTape (b : Bits (f+j)) : Bits (n+j) := Fin.append (padWire h (leftRegister b)) (rightRegister b : Bits j)

theorem padBit (b : Bits f) (i : Fin n) :
    padWire h b i = if hi : i.val<f then b ⟨i.val,hi⟩ else false := by
  have he := padWire_at h b
  have hi : i.val<(List.ofFn b++List.replicate (n-f) false).length := by simp;omega
  have hs : (List.ofFn (padWire h b))[i.val]'(by simpa using i.isLt)=_ :=
    List.getElem_of_eq he _
  by_cases hh : i.val<f
  · simpa [List.getElem_append_left,hh] using hs
  · have hcut : (List.ofFn b).length ≤ i.val := by simpa using Nat.le_of_not_gt hh
    rw [List.getElem_append_right hcut] at hs
    simpa [hh] using hs

theorem grow_left (i : Fin f) : growWires h j (i.castAdd j)=Fin.castAdd j (i.castLE h) := by
  apply Fin.ext;simp [growWires,i.isLt]

theorem grow_right (i : Fin j) : growWires h j (i.natAdd f)=i.natAdd n := by
  apply Fin.ext;simp [growWires]

theorem select_grown (b : Bits (f+j)) : (wireBitsEquiv (growWires h j) (growTape h j b)).1=b := by
  funext i
  change growTape h j b (growWires h j i)=b i
  induction i using Fin.addCases with
  | left i => simp [grow_left,growTape,padBit,i.isLt,leftRegister]
  | right i => simp [grow_right,growTape,rightRegister]

theorem exterior_grown (b : Bits (f+j)) : (wireBitsEquiv (growWires h j) (growTape h j b)).2=0 := by
  funext i
  obtain ⟨i,hi⟩:=i
  change growTape h j b i=false
  induction i using Fin.addCases with
  | left i =>
    have hi' : ¬ i.val<f := by
      intro w
      apply hi
      refine ⟨Fin.castAdd j (⟨_,w⟩:Fin f),?_⟩
      rw [grow_left];rfl
    simp [growTape,padBit,hi']
  | right i =>
    exact False.elim (hi ⟨i.natAdd f,grow_right h j i⟩)

def growEmbed : Bits (f+j) ↪ Bits (n+j) where
  toFun := growTape h j
  inj' x y e := by simpa only [select_grown] using congrArg (fun y => (wireBitsEquiv (growWires h j) y).1) e

theorem growSemantic (S : Layered (f+j)) (seed : Bits (f+j)) :
    runLayered (relocateCircuit (growWires h j) S) (basis (growTape h j seed))=
    basisEmbedding (growEmbed h j) (runLayered S (basis seed)) := by
  let w:=growWires h j
  have de : growEmbed h j=initializedWireEmbedding w 0 := by
    apply Function.Embedding.ext
    intro b
    change growTape h j b=(wireBitsEquiv w).symm (b,0)
    apply (wireBitsEquiv w).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (select_grown _ _ b) (exterior_grown _ _ b)
  rw [de,←initializedWires_eq_embedding,←relocateCircuit_initialized,initializedWires_basis]
  congr 2
  exact congrFun (congrArg DFunLike.coe de) seed

theorem growTensor (v : QState f) (y : QState j) :
    basisEmbedding (growEmbed h j) (tensorState v y)=tensorState (basisEmbedding (padWire h) v) y := by
  funext x
  obtain ⟨⟨a,b⟩,rfl⟩ := (qubitsAppendEquiv n j).symm.surjective x
  change basisEmbedding (growEmbed h j) (tensorState v y) (Fin.append a b) = basisEmbedding (padWire h) v (leftRegister (Fin.append a b))*y (rightRegister (Fin.append a b))
  have lr : leftRegister (Fin.append a b)=a := funext (Fin.append_left a b)
  have rr : rightRegister (Fin.append a b)=b := funext (Fin.append_right a b)
  rw [lr,rr]
  change basisEmbedding (growEmbed h j) (tensorState v y) (Fin.append a b) = basisEmbedding (padWire h) v a*y b
  by_cases ha : a∈Set.range (padWire h)
  · obtain ⟨i,rfl⟩ := ha
    have he : growEmbed h j (Fin.append i b)=Fin.append (padWire h i) b := by
      change Fin.append (padWire h (leftRegister (Fin.append i b))) (rightRegister (Fin.append i b))=_
      rw [show leftRegister (Fin.append i b)=i from funext (Fin.append_left i b),show rightRegister (Fin.append i b)=b from funext (Fin.append_right i b)]
    rw [←he,basisEmbedding_at,basisEmbedding_at]
    change v (leftRegister (Fin.append i b))*y (rightRegister (Fin.append i b))=_
    rw [show leftRegister (Fin.append i b)=i from funext (Fin.append_left i b),show rightRegister (Fin.append i b)=b from funext (Fin.append_right i b)]
  · rw [basisEmbedding_outside (padWire h) v a ha,zero_mul,basisEmbedding_outside]
    rintro ⟨i,hi⟩
    apply ha
    refine ⟨leftRegister i,?_⟩
    change Fin.append (padWire h (leftRegister i)) (rightRegister i : Bits j)=Fin.append a b at hi
    exact (CoherentXorCopy.append_eq_iff _ _ _ _).mp hi |>.1

def growAddr (v : (ℕ × ℕ) × ℕ) := if v.2 < v.1.1 then v.2 else v.1.2+(v.2-v.1.1)

@[fun_prop] theorem growAddr_poly : Poly growAddr := by unfold growAddr;fun_prop

def growGate (v : (ℕ × ℕ) × GateCode) : GateCode :=
  (v.2.1,growAddr (v.1,v.2.2.1),if v.2.1=4 then growAddr (v.1,v.2.2.2) else 0)

@[fun_prop] theorem growGate_poly : Poly growGate := by unfold growGate;fun_prop

theorem growGate_eq (x : Instr (f+j)) : growGate ((f,n),encodeInstr x)=encodeInstr (relocateInstr (growWires h j) x) := by cases x <;> rfl

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule199

/- Helper module CellWidth. -/
section P2MDyadicModule200

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1100000

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity CoherentInjection FineCodec OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

def ticksUpper (v : NativeStageInfo) := arenaTicks v++cleanupTicks v++(callInfoOf v).1.1++(callInfoOf v).1.2

@[fun_prop] theorem ticksUpper_poly : Poly ticksUpper := by unfold ticksUpper;fun_prop

def stageTicks (v : NativeStageInfo) := (ticksUpper v).take (activeWidth v)

@[fun_prop] theorem stageTicks_poly : Poly stageTicks := Poly.comp (f:=fun z : List Unit×ℕ => z.1.take z.2)
  (g:=fun v => (ticksUpper v,activeWidth v)) QMCNumericRuntime.parser_take_poly (Poly.pair ticksUpper_poly activeWidth_poly)

theorem stageTicks_exact (v : NativeStageInfo) : (stageTicks v).length=activeWidth v := by
  rw [stageTicks,List.length_take,Nat.min_eq_left]
  unfold ticksUpper
  simp only [List.length_append,arenaTicks_exact,cleanupTicks_size]
  simp only [activeWidth,stageMeta,codecLayout_exact,cleanupLayout_exact,rearSize,cleanupTicks_size,
    totalWidth,width,codecOld,codecCap,codecWork]
  omega

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule200

/- Helper module CellData. -/
section P2MDyadicModule201

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1100000

namespace InfoLossLAR.WorstCase.RectangularSource.Cell

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeDualQuotient RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid RegevSearch.FineCodec RegevSearch

open Settings Public

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2PlatformSerialization

noncomputable section

def nt (v : Input) := v.1.1.1.map fun _ => ()

def parameters (v : Input) : Settings.Settings := ((v.1.1.1,v.1.1.2.1.2,nt v),v.1.1.2.2.2.1)

def oldTable (v : Input) : OldTable := (v.1.2,v.2.1)

def bt (v : Input) := gridTape (parameters v).1

def qftAllowance (v : Input) :=
  times (List.replicate 200 (),times (nt v,times (bt v,times (bt v++[()],v.1.1.2.2.2.1++[()]))))

def qftRequest (v : Input) : NativeQFTPlanCompile.Input := (bt v,qftAllowance v)

def schedule (v : Input) := (nt v,bt v)

@[fun_prop] theorem nt_poly : Poly nt := by unfold nt;fun_prop

@[fun_prop] theorem oldTable_poly : Poly oldTable := by unfold oldTable;fun_prop

@[fun_prop] theorem bt_poly : Poly bt := by unfold bt;fun_prop

@[fun_prop] theorem qftAllowance_poly : Poly qftAllowance := by unfold qftAllowance;fun_prop

@[fun_prop] theorem qftRequest_poly : Poly qftRequest := by unfold qftRequest;fun_prop

@[fun_prop] theorem schedule_poly : Poly schedule := by unfold schedule;fun_prop

theorem qftAllowance_size (v : Input) : (qftAllowance v).length = GridReadout.Axis.precision (nt v).length (bt v).length v.1.1.2.2.2.1.length := by
  simp only [qftAllowance,times_len,List.length_replicate,List.length_append,List.length_singleton,GridReadout.Axis.precision]
  ring

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end P2MDyadicModule201

/- Helper module MachineUnit. -/
section P2MDyadicModule202

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FineCodec PaddedDecoder CoherentComputeUncompute ControlledNativeGates QuantumXorOracle

open IntegerBasis RegevLWE.GaussConv GaussianPoissonSeries

open NativeDualQuotient (Residual)

noncomputable section

attribute [local irreducible] FineCodec.forwardProgram FineCodec.inverseProgram FineCodec.queryProgram

theorem source_product_unit {n : ℕ} {I T : Type} [Fintype I] [Fintype T] (j : T→ℂ) (u : I→ℂ)
    (hj : ∑ i, ‖j i‖^2=1) (hu : ∑ i, ‖u i‖^2=1) (e : T×I ↪ Bits n) :
    stateNorm (basisEmbedding e (fun z => j z.1*u z.2))=1 := by
  rw [stateNorm,basisEmbedding_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simp only [EuclideanSpace.norm_sq_eq,one_pow,Fintype.sum_prod_type,norm_mul,mul_pow,←Finset.mul_sum,hu,mul_one,hj]

theorem machine_unit {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt k l s t : List Unit)
    (R : ℚ) (hR : 0<R) (prec : ℕ) (pool : Fin m→Fin n→ℤ) (r cut : ℝ) (hr : 0<r) (hc : 0<cut)
    (hcut : cut ≤ (famσ n:ℝ)/(2*(R:ℝ))) (sep : Separated (StageL B hB) cut)
    [Fintype (Residual B)] [Fintype (StageI B hB bt.length cut)]
    (hf : ∀ res p, (pack (frameCode B hB bt k l s t R prec pool cut res p)).length ≤ s.length)
    (hA : ∀ p : StageI B hB bt.length cut,(encVec encI (promisedShort B hB R hR cut hcut p).answer).length ≤ k.length)
    (hs : (n:ℝ)*(1/(Real.sqrt 2*r))^2 ≤ cut^2)
    (j : Hilbert (Residual B)) (hj : ‖j‖=1) :
    let src (z : Residual B×StageI B hB bt.length cut) := frameCode B hB bt k l s t R prec pool cut z.1 z.2
    let u := taper B hB bt.length r cut hr
    stateNorm (beforeMachine s src (fun z => j z.1*u z.2))=1 := by
  intro src u
  obtain ⟨h,je,he⟩:=machine_stage B hB bt k l s t R hR prec pool cut hc hcut sep 0 hf hA
  let v := beforeMachine s src (fun z => j z.1*u z.2)
  specialize he (fun z => j z.1*u z.2) v
  have hv : stateNorm (v-v)=0 := by simp [stateNorm]
  rw [show stateNorm (v-beforeMachine s src (fun z => j z.1*u z.2)) =0 from hv] at he
  have flat {a : ℕ} (x y : QState a) (he : stateNorm (x-y)=0) : x=y := by
    have hz : (WithLp.toLp 2 (x-y) : EuclideanSpace ℂ (Bits a))=0 := norm_eq_zero.mp he
    exact sub_eq_zero.mp (congrArg WithLp.ofLp hz)
  have hey := congrArg stateNorm (flat _ _ he)
  have hnorm {N : ℕ} (H : CoherentInjection.totalWidth FineCodec.forwardProgram FineCodec.inverseProgram s.length+(0+1)=N) :
      stateNorm (machineRun s 0 H v)=stateNorm v := by
    subst N
    change stateNorm (attach _ (runLayered _ v))=_
    rw [attach_norm];exact (circuitIsometry _).norm_map _
  rw [hnorm] at hey
  have hwidth : (n:ℝ)*((1/(Real.sqrt 2*r))/Real.sqrt 2)^2 ≤ cut^2 := by
    apply le_trans _ hs
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    apply pow_le_pow_left₀ (by positivity) _
    exact div_le_self (by positivity) (Real.one_le_sqrt.mpr (by norm_num))
  have hu := short_mass hB (2^bt.length) (1/(Real.sqrt 2*r)) cut (by positivity) hc hwidth
  exact hey.trans (source_product_unit _ _ (residual_mass j hj) hu _)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule202

/- Helper module AnalyticRow. -/
section P2MDyadicModule203

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 850000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms.Complexity GaussianIteration CoherentDecoder PhysicalFourier IntegerBasis GaussianPoissonSeries

open SharedPoolCoherence RegevLWE.GaussConv RectangularSource RectangularSource.Settings RectangularSource.Public

open PhysicalGrid

noncomputable def oneAnalysis {n : ℕ} (C : MFamily) (P : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (R r : ℚ) (hR : 0<R) (hr : 0<r) (acc : List Unit) (cut : ℝ) (hc : 0<cut)
    (hcut : cut≤(famσ n:ℝ)/(2*(R:ℝ))) (hscale : (n:ℝ)*(physics r)^2 ≤ cut^2)
    [Fintype (StageI B hB (gridTape (atBasis B r n acc).1).length cut)] : AnalysisData C P B R acc.length where
  grid := (gridTape (setup B R n)).length
  covers := gridTape_adequate B R n hR
  I := StageI B hB (gridTape (atBasis B r n acc).1).length cut
  inst := inferInstance
  inhabited := ⟨⟨0,by simpa [fineGridPoint] using hc⟩⟩
  query := promisedShort B hB R hR cut hcut
  amp := (taper B hB _ (r:ℝ) cut (by exact_mod_cast hr)).ofLp
  norm := by
    apply short_mass hB _ _ cut (physics_pos hr) hc
    apply le_trans _ hscale
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ (div_pos (physics_pos hr) (Real.sqrt_pos.mpr (by norm_num))).le
    exact div_le_self (physics_pos hr).le (Real.one_le_sqrt.mpr (by norm_num))
  prep := gap (atBasis B r n acc) n n
  prep_nonneg := by unfold gap;positivity [delta_pos n]
  L := (base (atBasis B r n acc)).length
  length_ge := by simp [base,atBasis];omega
  source := le_rfl

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule203

/- Helper module FineFields. -/
section P2MDyadicModule204

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open OAI.MetricKMedian.Binary QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport RegevSearch.PhysicalFourier

noncomputable section

theorem input_extension {f g : Str→Str} (P : PolyProgram id id f) (R : PolyProgram id id g) (w : Str) (l : ℕ) (hw : w.length=l) :
    CoherentInjection.inputBitsAt P R l w = fun k => TM2Boolean.wordExtension w k.val := by
  subst l
  apply List.ofFn_inj.mp
  rw [Arena.input_tape _ _ _ rfl]
  symm
  apply extension_word
  have := CoherentInjection.originalSize_ge P R w.length
  unfold CoherentInjection.totalWidth CoherentInjection.width
  omega

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end P2MDyadicModule204

/- Helper module SeedWrite. -/
section P2MDyadicModule205

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

end

end InfoLossLAR.WorstCase.RectangularSource.SeedWrite

end P2MDyadicModule205

/- Helper module JoinedEvent. -/
section P2MDyadicModule206

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1550000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport ControlledNativeCode ControlledNativeGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CoherentDecoder PaddedDecoder

noncomputable section

variable {f n j : ℕ} (h : f≤n)

def wholeCell (S : Layered (f+j)) (U : Layered n) := relocateCircuit (growWires h j) S++leftCircuit (m:=j) U

def wholeCodes (v : (ℕ × ℕ) × List GateCode × List GateCode) := v.2.1.map (fun g => growGate (v.1,g))++v.2.2

@[fun_prop] theorem wholeCodes_poly : Poly wholeCodes := by unfold wholeCodes;fun_prop

theorem wholeCodes_exact (S : Layered (f+j)) (U : Layered n) :
    wholeCodes ((f,n),codeList S,codeList U)=codeList (wholeCell h S U) := by
  simp only [wholeCodes,wholeCell,codes_concat,leftCodeList]
  congr 1
  simp only [codeList,List.map_map,Function.comp_def,growGate_eq (h:=h) (j:=j),relocateCircuit,List.map_flatten]

theorem tensorNorm {k d : ℕ} (v : QState k) (t : QState d) :
    stateNorm (tensorState v t)=stateNorm v*stateNorm t := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simp only [stateNorm,mul_pow,EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ p : Bits k × Bits d, ‖v p.1*t p.2‖^2 :=
      Fintype.sum_equiv (qubitsAppendEquiv k d) _ _ (fun _ => rfl)
    _ = _ := by simp only [Fintype.sum_prod_type,norm_mul,mul_pow,←Finset.mul_sum,←Finset.sum_mul]

theorem gateSeedNorm {k : ℕ} (S : Layered k) (s : Bits k) : stateNorm (runLayered S (basis s))=1 := by
  rw [show stateNorm (runLayered S (basis s))=stateNorm (basis s) from (circuitIsometry S).norm_map (WithLp.toLp 2 (basis s))]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  change ‖(WithLp.toLp 2 (basis s) : EuclideanSpace ℂ (Bits k))‖^2=1^2
  rw [EuclideanSpace.norm_sq_eq,Finset.sum_eq_single s]
  · simp [basis]
  · intro i _ hi;simp [basis,hi]
  · simp

theorem joined_event (S : Layered (f+j)) (seed : Bits (f+j)) (U : Layered n)
    (v : QState f) (sv : stateNorm v=1) (t : QState j) (st : stateNorm t=1) (ε : ℝ)
    (hs : stateNorm (runLayered S (basis seed)-tensorState v t)≤ε)
    (E : Bits n→Prop) (target δ : ℝ)
    (hu : |bornEvent E (WithLp.toLp 2 (runLayered U (basisEmbedding (padWire h) v)))-target|≤δ) :
    |bornEvent (fun z => E (leftRegister z)) (WithLp.toLp 2 (runLayered (wholeCell h S U) (basis (growTape h j seed))))-target|≤2*ε+δ := by
  let A:=basisEmbedding (growEmbed h j) (runLayered S (basis seed))
  let T:=basisEmbedding (growEmbed h j) (tensorState v t)
  have na : stateNorm A=1 := (basisEmbedding_norm _ _).trans (gateSeedNorm S seed)
  have nt : stateNorm T=1 := by
    calc _ = stateNorm (tensorState v t) := basisEmbedding_norm _ _
         _ = 1 := by rw [tensorNorm,sv,st,one_mul]
  have dist : stateNorm (A-T)≤ε := (basisEmbedding_error _ _ _).le.trans hs
  have step := born_after (leftCircuit (m:=j) U) A T na nt (fun z => E (leftRegister z))
  have rhs : bornEvent (fun z => E (leftRegister z)) (WithLp.toLp 2 (runLayered (leftCircuit (m:=j) U) T))=
      bornEvent E (WithLp.toLp 2 (runLayered U (basisEmbedding (padWire h) v))) := by
    dsimp only [T]
    rw [growTensor,leftCircuit_tensor,marginal_product _ _ st]
  rw [rhs] at step
  rw [wholeCell,run_concat,growSemantic]
  exact (abs_sub_le _ _ _).trans (add_le_add (step.trans (by linarith)) hu)

theorem read_tail (nt bt : List Unit) (o : ℕ) (hold : o+nt.length*bt.length≤n) (x : Bits (n+j)) :
    signedSlice ((nt,bt),o,List.ofFn x)=signedSlice ((nt,bt),o,List.ofFn (leftRegister x : Bits n)) := by
  obtain ⟨⟨p,t⟩,rfl⟩ := (qubitsAppendEquiv n j).symm.surjective x
  change signedSlice ((nt,bt),o,List.ofFn (Fin.append p t))=signedSlice ((nt,bt),o,List.ofFn (leftRegister (Fin.append p t) : Bits n))
  rw [show leftRegister (Fin.append p t)=p from funext (Fin.append_left p t),List.ofFn_fin_append]
  unfold signedSlice GridReadout.Axis.encodeSlices
  rw [List.drop_append,List.length_ofFn,Nat.sub_eq_zero_of_le (by omega : o≤n),List.drop_zero,
    rowSlices_tail nt bt ((List.ofFn p).drop o) (List.ofFn t) (by simp;omega)]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule206

/- Helper module CellZero. -/
section P2MDyadicModule207

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport RegevSearch.PhysicalFourier

noncomputable section

theorem empty_grow {f n j : ℕ} (h : f≤n) : growTape h j (0:Bits (f+j))=0 := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    rw [growTape,Fin.append_left,padBit]
    split <;> rfl
  | right i => exact Fin.append_right _ _ i

theorem start_zero {f n j : ℕ} (h : f≤n) (S : Layered (f+j)) (seed : Bits (f+j)) (U : Layered n) :
    runLayered (wholeCell h (SeedWrite.circuit seed++S) U) (basis (0:Bits (n+j)))=
    runLayered (wholeCell h S U) (basis (growTape h j seed)) := by
  rw [←empty_grow h,wholeCell,wholeCell,run_concat,run_concat,growSemantic,growSemantic,run_concat,SeedWrite.from_zero]

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule207

/- Helper module StageLayout. -/
section P2MDyadicModule208

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

theorem room_for_read (v : NativeStageInfo) : readStart v+v.1.1.length*v.1.2.1.length ≤ activeWidth v := by
  have h : v.1=(stageMeta v).1 := rfl
  rw [readStart,activeWidth,h]
  dsimp only
  exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ 2)

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule208

/- Helper module CellFacts. -/
section P2MDyadicModule209

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

end

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end P2MDyadicModule209

/- Helper module CellResult. -/
section P2MDyadicModule210

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.Cell

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute CoherentDecoder ControlledNativeCode

open RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid RegevSearch.FineCodec RegevSearch CoherentInjection

open NativeDualQuotient IntegerBasis Settings Public

noncomputable section

def eventLaw {n N : ℕ} (C : Layered N) (nt bt : List Unit) (off : ℕ) (mass : (Fin n→ℤ)→ℝ) (ε : ℝ) : Prop :=
  ∀ s : Finset (Fin n→ℤ),
    |bornEvent (fun y => ∃ z∈s, encVec encI z <+: signedSlice ((nt,bt),off,List.ofFn y))
      (WithLp.toLp 2 (runLayered C (basis (0:Bits N))))-∑z∈s,mass z|≤ε

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end P2MDyadicModule210

/- Helper module CellAssumptions. -/
section P2MDyadicModule211

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2600000

set_option maxRecDepth 12000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.Cell

open QAlgorithms QAlgorithms.Complexity RegevLWE.GaussConv GaussianPoissonSeries NativeDualQuotient IntegerBasis

open RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid RegevSearch SharedPoolCoherence Settings Public

noncomputable section

def error {n m : ℕ} (C : MFamily) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (R r : ℚ) (hR : 0<R) (hr : 0<r) (acc : List Unit) (cut : ℝ) (hcut : cut≤(famσ n:ℝ)/(2*(R:ℝ)))
    (pr : ℕ) (pool : Fin m→Fin n→ℤ)
    [Fintype (StageI B hB (gridTape (atBasis B r n acc).1).length cut)] : ℝ :=
  let p:=atBasis B r n acc
  let b:=(gridTape p.1).length
  let q (i : StageI B hB b cut) := promisedShort B hB R hR cut hcut i
  let u:=taper B hB b (r:ℝ) cut (by exact_mod_cast hr)
  2*gap p n n+(4*Real.sqrt (failureMass C pr pool q u.ofLp)+4*Real.sqrt (2*(1/2:ℝ)^n)+1/(4*((acc.length:ℝ)+1))+GridReadout.gridError n)

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end P2MDyadicModule211

/- Helper module RawAdapter. -/
section P2MDyadicModule212

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity RectangularSource RectangularSource.Settings RectangularSource.Public

open PhysicalGrid PhysicalFourier NativeDualQuotient GaussianIteration CoherentDecoder

noncomputable section

theorem cost_eq {n : ℕ} (C : MFamily) (P : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (R r : ℚ) (hR : 0<R) (hr : 0<r) (acc : List Unit) (pr : List Unit) (cut : ℝ) (hc : 0<cut)
    (hcut : cut≤(famσ n:ℝ)/(2*(R:ℝ))) (hscale : (n:ℝ)*(physics r)^2 ≤ cut^2)
    [Fintype (StageI B hB (gridTape (atBasis B r n acc).1).length cut)] (z : Rows n (P.eval n))
    (hp : pr.length=poolBDDPrecision (((P+1)+(P+1)).eval n) acc.length) :
    Cell.error C B hB R r hR hr acc cut hcut pr.length z = (oneAnalysis C P B hB R r hR hr acc cut hc hcut hscale).cost z := by
  rw [hp]
  unfold Cell.error AnalysisData.cost oneAnalysis
  dsimp only
  ring

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule212

/- Helper module InterpretedRow. -/
section P2MDyadicModule213

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 950000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.RawBackend

open QAlgorithms QAlgorithms.Complexity RectangularSource RegevSearch.PhysicalFourier GaussianIteration AdaptiveStages

open ControlledNativeCode OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

theorem interpreted (f : Str→SignedSlot.Raw) (hf : Poly f) :
    ∃ (G : MFamily) (desc : Str→Str), Poly desc ∧ (∀ n,desc (unary n)=G.encAt n) ∧ IsMQPT G ∧
      ∀ (w : Str) (v : SignedSlot.Raw), f w=v → ∀ (nt bt : List Unit) (n : ℕ), nt.length=n →
      v.1=(nt,bt) → ∀ (c : Layered v.2.1.1.length), codeList c=v.2.2 →
      ∀ (mass : Vec n→ℝ) (ε : ℝ), Cell.eventLaw c nt bt v.2.1.2 mass ε →
      v.2.1.2+nt.length*bt.length≤v.2.1.1.length → ∀ S : ℕ, (SignedSlot.slot (nt,bt)).length≤S →
      outputProb G w (SignedSlot.canon n S)=1 ∧
        ∀ T : Finset (Vec n), |finiteMass ((measuredWord G w).map (SignedSlot.decodeWord n)) T-∑z∈T,mass z|≤ε := by
  obtain ⟨G,desc,hdesc,uniform,qpt,law⟩ := compile_signed_register_readout f hf
  refine ⟨G,desc,hdesc,uniform,qpt,?_⟩
  intro w v hw nt bt n hd hg c hc mass ε event readFit S slotFit
  subst n
  have h:= law w v hw (nt,bt) hg v.2.1.2 rfl c
  obtain ⟨canon,read⟩:=h (by
    refine hc.symm.trans ?_
    change c.flatten.map encodeInstr=_
    congr 1
    funext g
    cases g <;>rfl) readFit
  refine ⟨canon S slotFit,?_⟩
  intro T
  rw [read]
  convert event T using 1
  congr 2
  simp only [CoherentDecoder.bornEvent,signedSlice,Pi.zero_def]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

end

end InfoLossLAR.WorstCase.RegevSearch.RawBackend

end P2MDyadicModule213

/- Helper module JoinedMeasured. -/
section P2MDyadicModule214

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 420000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity RegevSearch.PhysicalFourier CoherentComputeUncompute FiniteGateTransport ControlledNativeGates

open ControlledNativeCode CoherentDecoder

noncomputable section

def basicOut {w : ℕ} (G : Layered w) := WithLp.toLp 2 (runLayered G (basis (0:Bits w)))

def signedEv (nt bt : List Unit) (o : ℕ) (ev : Finset (Fin nt.length→ℤ)) {w : ℕ} (x : Bits w) :=
  ∃ z∈ev, encVec encI z <+: signedSlice ((nt,bt),o,List.ofFn x)

theorem join_measured {f n j : ℕ} (hw : f≤n) (S : Layered (f+j)) (σ : Bits (f+j)) (U : Layered n)
    (gates : List GateCode) (hU : codeList U=gates) (v : QState f) (hv : stateNorm v=1)
    (y : QState j) (hy : stateNorm y=1) (ε δ : ℝ)
    (hp : stateNorm (runLayered S (basis σ)-tensorState v y)≤ε)
    (nt bt : List Unit) (o : ℕ) (hroom : o+nt.length*bt.length≤n) (μ : (Fin nt.length→ℤ)→ℝ)
    (hb : ∀ ev,|bornEvent (signedEv nt bt o ev) (WithLp.toLp 2 (runLayered U (basisEmbedding (padWire hw) v)))-∑ z∈ev, μ z|≤δ) :
    ∃ G : Layered (n+j), codeList G=wholeCodes ((f,n),codeList (SeedWrite.circuit σ++S),gates) ∧
    ∀ ev, |bornEvent (signedEv nt bt o ev) (basicOut G)-∑ z∈ev,μ z|≤2*ε+δ := by
  refine ⟨wholeCell hw (SeedWrite.circuit σ++S) U,?_,?_⟩
  · rw [←wholeCodes_exact hw (SeedWrite.circuit σ++S) U,hU]
  · intro ev
    have result:=joined_event hw S σ U v hv y hy ε hp (signedEv nt bt o ev) _ δ (hb ev)
    have ep : (signedEv nt bt o ev : Bits (n+j)→Prop)=(fun x => signedEv nt bt o ev (leftRegister x : Bits n)) := by
      funext x;unfold signedEv;rw [read_tail nt bt o hroom]
    rw [ep,basicOut,start_zero]
    exact result

theorem remove_self {f : ℕ} (v : QState f) {a b c d X : ℝ} (h : X≤2*stateNorm (v-v)+a+b+c+d) : X≤a+b+c+d := by
  simpa [stateNorm] using h

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end P2MDyadicModule214

/- Helper module RawFrontWire. -/
section P2MDyadicModule215

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute RegevSearch.StageRegisters FiniteGateTransport RegevSearch.PhysicalFourier

open OAI.MetricKMedian.Binary NativeDualQuotient RegevSearch.FineCodec CoherentInjection ControlledNativeGates

noncomputable section

attribute [local irreducible] RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram

theorem raw_machine {I : Type} [Fintype I] (s : List Unit) (src : I→Source) (v : I→ℂ) :
    rawState (CoherentInjection.totalWidth RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram s.length) s src v=beforeMachine s src v := by
  unfold rawState beforeMachine
  apply Finset.sum_congr rfl
  intro i _
  unfold stagedWord
  rw [input_extension RegevSearch.FineCodec.forwardProgram RegevSearch.FineCodec.inverseProgram _ s.length (NativePaddedWords.current_length _ _)]

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end P2MDyadicModule215

/- Helper module RawBackend. -/
section P2MDyadicModule216

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.RawBackend

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RectangularSource RectangularSource.RawFront RectangularSource.Settings RectangularSource.Public

open PhysicalFourier PhysicalGrid NativeDualQuotient IntegerBasis CoherentInjection

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2PlatformSerialization ControlledNativeCode

open GaussianRandomizedRounding.Wide.Coherent (rationalCode)

open AdaptiveStages

noncomputable section

attribute [local irreducible] FineCodec.forwardProgram FineCodec.inverseProgram FineCodec.queryProgram

def clear (v : Cell.Input) : Cell.Input := (v.1,v.2.1,[])

def query (spec : Cell.Input→Spec) (v : Cell.Input) := (spec (clear v)).2.1.1

def fineWord (s : List Unit) := wholeSlots FineCodec.forwardProgram FineCodec.inverseProgram (boolTicks s)

def call (spec : Cell.Input→Spec) (v : Cell.Input) : FromPoolInput :=
  let x:=spec (clear v)
  ((Cell.nt v,Cell.qftRequest v),
    (serializeMatrix v.1.1.1,rationalCode v.1.1.2.1.1,RectangularSource.Public.pad v.1.1.2.2.2.2),
    ((x.2.1.2,x.1.1),(x.1.2,x.2.1.1)),Cell.oldTable v,OracleTable.lookup (v.2.2,(query spec v).length))

def wires (spec : Cell.Input→Spec) (v : Cell.Input) :=
  stageTicks (withPool (call spec v)) ++ (spec (clear v)).2.2

def codes (spec : Cell.Input→Spec) (emit : Cell.Input×List Unit→List GateCode) (qa : ℕ) (v : Cell.Input) :=
  let x:=spec (clear v)
  let c:=call spec v
  let wf:=fineWord x.2.1.2
  wholeCodes ((wf.length,activeWidth (withPool c)),emit (clear v,wf),stageInput qa c)

def describe (spec : Cell.Input→Spec) (emit : Cell.Input×List Unit→List GateCode) (qa : ℕ) (v : Cell.Input) : SignedSlot.Raw :=
  (Cell.schedule v,((wires spec v,readStart (withPool (call spec v))),codes spec emit qa v))

@[fun_prop] theorem clear_poly : Poly clear := by unfold clear;fun_prop

@[fun_prop] theorem query_poly {spec : Cell.Input→Spec} (h : Poly spec) : Poly (query spec) := by unfold query;fun_prop

@[fun_prop] theorem fineWord_poly : Poly fineWord := by unfold fineWord;fun_prop

@[fun_prop] theorem call_poly {spec : Cell.Input→Spec} (h : Poly spec) : Poly (call spec) := by unfold call;fun_prop

@[fun_prop] theorem wires_poly {spec : Cell.Input→Spec} (h : Poly spec) : Poly (wires spec) := by unfold wires;fun_prop

@[fun_prop] theorem codes_poly {spec : Cell.Input→Spec} (hm : Poly spec) {emit : Cell.Input×List Unit→List GateCode} (he : Poly emit)
    (qa : ℕ) : Poly (codes spec emit qa) := by unfold codes;fun_prop

@[fun_prop] theorem describe_poly {spec : Cell.Input→Spec} (hm : Poly spec) {emit : Cell.Input×List Unit→List GateCode} (he : Poly emit)
    (qa : ℕ) : Poly (describe spec emit qa) := by unfold describe;fun_prop

theorem fineWord_exact (s : List Unit) : (fineWord s).length=fineSize s := by
  rw [fineWord,boolTicks_eq,wholeSlots_length]

theorem fineWord_fits (s : List Unit) : s.length≤(fineWord s).length := by
  rw [fineWord_exact]
  have h:=CoherentInjection.originalSize_ge FineCodec.forwardProgram FineCodec.inverseProgram s.length
  unfold fineSize CoherentInjection.totalWidth CoherentInjection.width
  omega

theorem independent (spec : Cell.Input→Spec) : TableIndependent (query spec) := fun _ _ _ _=>rfl

theorem wires_size (spec : Cell.Input→Spec) (v : Cell.Input) :
    (wires spec v).length=activeWidth (withPool (call spec v))+(spec (clear v)).2.2.length := by
  rw [wires,List.length_append,stageTicks_exact]

theorem read_fits (spec : Cell.Input→Spec) (v : Cell.Input) :
    readStart (withPool (call spec v))+(Cell.nt v).length*(Cell.bt v).length≤(wires spec v).length := by
  have h := room_for_read (withPool (call spec v))
  change readStart (withPool (call spec v))+(Cell.nt v).length*(Cell.bt v).length≤activeWidth (withPool (call spec v)) at h
  rw [wires_size]
  exact h.trans (Nat.le_add_right ..)

theorem call_exact {F : MFamily} (spec : Cell.Input→Spec) (nt copies acc oracle count width : List Unit)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (R r : ℚ) (tape advice : Str) :
    let v:=Cell.encoded nt copies acc oracle count width B R r tape advice
    let x:=spec (clear v)
    let p:=atBasis B r nt.length acc
    let bt:=gridTape p.1
    let ft:=Cell.qftAllowance v
    (OracleTable.lookup (advice,(query spec v).length)=F.encAt (query spec v).length) →
    call spec v=((nt,(bt,ft)),(encMat encI B,encQ R,unary oracle.length),((x.2.1.2,x.1.1),(x.1.2,x.2.1.1)),((count,width),tape),F.encAt x.2.1.1.length) ∧
    Cell.schedule v=(nt,bt) ∧ GridReadout.Axis.precision nt.length bt.length acc.length ≤ ft.length := by
  intro v x p bt ft look
  have hn : Cell.nt v=nt:=Cell.rect_dimension .. 
  have hp : Cell.parameters v=p:=Cell.rect_settings ..
  have hb : Cell.bt v=bt := by change gridTape (Cell.parameters v).1=_;rw [hp]
  have pc : RectangularSource.Public.pad oracle=unary oracle.length:=List.map_const' ..
  refine ⟨?_,Prod.ext hn hb,?_⟩
  · change ((Cell.nt v,(Cell.bt v,ft)),(serializeMatrix (RationalInverse.Native.inputRows B),encQ R,RectangularSource.Public.pad oracle),_,_,OracleTable.lookup (advice,(query spec v).length))=_
    rw [hn,hb,pc,FineCodec.serializeMatrix_eq,look]
    rfl
  · have h:=Cell.qftAllowance_size v
    rw [hn,hb] at h
    exact h.ge

end

end InfoLossLAR.WorstCase.RegevSearch.RawBackend

end P2MDyadicModule216

/- Helper module RawJoined. -/
section P2MDyadicModule217

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

set_option maxRecDepth 12000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.RawFront

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute CoherentDecoder FiniteGateTransport ControlledNativeGates

open ControlledNativeCode RegevSearch RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid NativeDualQuotient IntegerBasis GaussianPoissonSeries RegevLWE.GaussConv

open SharedPoolCoherence Settings Public

noncomputable section

attribute [local irreducible] programFor allStageCodes withPool stageCodes activeWidth readStart beforeMachine

private theorem call_fields (v : FromPoolInput) : (withPool v).1=v.1 := by
  rcases v with ⟨⟨nt,x⟩,⟨mat,r,prec⟩,⟨⟨s,t⟩,k,l⟩,rows,desc⟩
  unfold withPool
  rfl

theorem seed_blank (n : ℕ) : SeedWrite.circuit (0:Bits n)=[] := by
  simp [SeedWrite.circuit,SeedWrite.flips,Pi.zero_def,compileReversible]

theorem joined (C : MFamily) (hC : IsMQPT C) :
    ∃ F : MFamily, IsMQPT F ∧ ∃ qa : ℕ, 0<qa ∧
    ∀ (nt bt ft count pw : List Unit) (tape : Str)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (hB : B.det≠0)
    (R r : ℚ) (hR : 0<R) (hr : 0<r) (cut : ℝ) (hc : 0<cut) (hn : 0<nt.length)
    (hg : gridAdequate B (r:ℝ) (2^bt.length))
    (hscale : (nt.length:ℝ)*(physics r)^2 ≤ cut^2) (sep : Separated (StageL B hB) cut)
    (hcut : cut ≤ (famσ nt.length:ℝ)/(2*(R:ℝ))) (budget : ℕ)
    (hq : GridReadout.Axis.precision nt.length bt.length budget ≤ ft.length)
    (prec : ℕ) (pool : Fin count.length→Fin nt.length→ℤ)
    (table : ∀ i, encVec encI (pool i) <+: (tape.drop (i.val*pw.length)).take pw.length)
    (t k l s old wf : List Unit) (width : wf.length=fineSize s)
    [Fintype (Residual B)] [Fintype (StageI B hB bt.length cut)]
    (ε : ℝ) (codes : List GateCode)
    (good : fits B hB bt R hR prec pool cut hcut ((t,k),(l,s),old))
    (source : preparedState B hB bt R r hr prec pool cut ((t,k),(l,s),old) ε wf codes),
    let call : FromPoolInput:=((nt,(bt,ft)),(encMat encI B,encQ R,unary prec),((s,t),(k,l)),((count,pw),tape),F.encAt l.length)
    let info:=withPool call
    let w:=activeWidth info
    let q (i : StageI B hB bt.length cut) := promisedShort B hB R hR cut hcut i
    let u:=taper B hB bt.length (r:ℝ) cut (by exact_mod_cast hr)
    ∃ G : Layered (w+old.length),
      codeList G=wholeCodes ((fineSize s,w),codes,stageInput qa call) ∧
      Cell.eventLaw G nt bt (readStart info) (RegevSketch.coefficientMass B (r:ℝ))
        (2*ε+(4*Real.sqrt (failureMass C prec pool q u.ofLp)+4*Real.sqrt (2*(1/2:ℝ)^nt.length)+
          1/(4*((budget:ℝ)+1))+GridReadout.gridError nt.length)) := by
  obtain ⟨F,hF,qa,hqa,kernelStep⟩ := coherent_step C hC
  refine ⟨F,hF,qa,hqa,?_⟩
  intro nt bt ft count pw tape B hB R r hR hr cut hc hn hg hscale sep hcut budget hq prec pool table t k l s old wf width _ _ ε codes good source call info w q u
  obtain ⟨hkl,frames,answers,queries⟩ := good
  obtain ⟨U,hU,hw,run⟩ := kernelStep nt (bt,ft) count pw tape B hB (r:ℝ) cut (by exact_mod_cast hr) hc hn hg hscale sep R hR hcut budget hq prec pool table k l s t hkl frames answers queries
  change codeList U=stageInput qa call at hU
  change fineSize s≤w at hw
  unfold preparedState at source
  dsimp only at source
  rw [width] at source
  obtain ⟨S,hS,j,hj,y,hy,near⟩:=source
  let src (z : Residual B×StageI B hB bt.length cut) := frameCode B hB bt k l s t R prec pool cut z.1 z.2
  let v:=beforeMachine s src (fun z=>j z.1*u z.2)
  have unit : stateNorm v=1 := machine_unit B hB bt k l s t R hR prec pool (r:ℝ) cut (by exact_mod_cast hr) hc hcut sep frames answers hscale j hj
  have data : FineWires.rawState (fineSize s) s src (fun z=>j z.1*u z.2)=v := FineWires.raw_machine s src _
  change stateNorm (runLayered S (basis 0)-tensorState (FineWires.rawState (fineSize s) s src (fun z=>j z.1*u z.2)) y)≤ε at near
  rw [data] at near
  have first : info.1=(nt,(bt,ft)) := by
    change (withPool call).1=_
    exact call_fields call
  have room:=room_for_read info
  rw [first] at room
  let err:=4*Real.sqrt (failureMass C prec pool q u.ofLp)+4*Real.sqrt (2*(1/2:ℝ)^nt.length)+1/(4*((budget:ℝ)+1))+GridReadout.gridError nt.length
  have events := fun ev=>remove_self v ((run j hj v unit).2 ev)
  obtain ⟨G,hG,hBorn⟩:=join_measured hw S 0 U (stageInput qa call) hU v unit y hy ε err near nt bt (readStart info) room (RegevSketch.coefficientMass B (r:ℝ)) events
  refine ⟨G,?_,hBorn⟩
  simpa only [seed_blank,List.nil_append,hS] using hG

end

end InfoLossLAR.WorstCase.RectangularSource.RawFront

end P2MDyadicModule217

/- Helper module RawCell. -/
section P2MDyadicModule218

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.RawBackend

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RectangularSource RectangularSource.RawFront RectangularSource.Settings RectangularSource.Public

open PhysicalFourier PhysicalGrid NativeDualQuotient IntegerBasis CoherentInjection ControlledNativeCode

open SharedPoolCoherence CoherentDecoder AdaptiveStages

noncomputable section

def realizes {n : ℕ} (raw : SignedSlot.Raw) (nt bt : List Unit) (mass : (Fin n→ℤ)→ℝ) (ε : ℝ) : Prop :=
  ∃ G : Layered raw.2.1.1.length, codeList G=raw.2.2 ∧ Cell.eventLaw G nt bt raw.2.1.2 mass ε

theorem realizes_of {n N : ℕ} {raw : SignedSlot.Raw} {nt bt : List Unit} {mass : (Fin n→ℤ)→ℝ} {ε : ℝ}
    {codes : List GateCode} {off : ℕ} (hn : raw.2.1.1.length=N) (href : raw.2.2=codes) (hr : raw.2.1.2=off)
    (G : Layered N) (gc : codeList G=codes) (h : Cell.eventLaw G nt bt off mass ε) : realizes raw nt bt mass ε := by
  subst N
  exact ⟨G,gc.trans href.symm,hr ▸ h⟩

def OnRows (C F : MFamily) (spec : Cell.Input→Spec) (emit : Cell.Input×List Unit→List GateCode) (qa : ℕ) : Prop :=
    ∀ (nt copies acc oracle count width : List Unit) (B : Matrix (Fin nt.length) (Fin nt.length) ℤ)
    (hB : B.det≠0) (hn : 0<nt.length) (R r : ℚ) (hR : 0<R) (hr : 0<r) (cut : ℝ) (hc : 0<cut)
    (hs : (nt.length:ℝ)*(physics r)^2 ≤ cut^2) (hcap : cut≤(nt.length+1:ℕ)*(r.den+1:ℕ))
    (hcut : cut ≤ (famσ nt.length:ℝ)/(2*(R:ℝ))) (sep : Separated (StageL B hB) cut) (raw tbl : Str)
    (z : Fin count.length→Fin nt.length→ℤ) (table : ∀ i, encVec encI (z i) <+: (raw.drop (i.val*width.length)).take width.length),
    let v:=Cell.encoded nt copies acc oracle count width B R r raw tbl
    let bt:=gridTape (atBasis B r nt.length acc).1
    ∀ [Fintype (Residual B)] [Fintype (StageI B hB bt.length cut)],
      OracleTable.lookup (tbl,(query spec v).length)=F.encAt (query spec v).length →
      Cell.schedule v=(nt,bt) ∧ realizes (describe spec emit qa v) nt bt (RegevSketch.coefficientMass B (r:ℝ))
        (Cell.error C B hB R r hR hr acc cut hcut oracle.length z)

theorem sampling (C : MFamily) (hC : IsMQPT C) (spec : Cell.Input→Spec) (emit : Cell.Input×List Unit→List GateCode)
    (front : frontContract spec emit) :
    ∃ F : MFamily, IsMQPT F ∧ ∃ qa : ℕ, OnRows C F spec emit qa := by
  obtain ⟨F,hF,qa,_,hstep⟩:=joined C hC
  refine ⟨F,hF,qa,?_⟩
  intro nt copies acc oracle count width B hB hn R r hR hr cut hc hs hcap hcut sep raw tbl z table v bt _ _ lookup
  let x:=spec (clear v)
  let wf:=fineWord x.2.1.2
  let p:=atBasis B r nt.length acc
  let ft:=Cell.qftAllowance v
  let c : FromPoolInput := ((nt,(bt,ft)),(encMat encI B,encQ R,unary oracle.length),((x.2.1.2,x.1.1),(x.1.2,x.2.1.1)),((count,width),raw),F.encAt x.2.1.1.length)
  obtain ⟨hc0,hsch,hbudget⟩:=call_exact (F:=F) spec nt copies acc oracle count width B R r raw tbl lookup
  change call spec v=c at hc0
  refine ⟨hsch,?_⟩
  obtain ⟨fit,prepared⟩:=front nt copies acc oracle count width B hB hn R r hR hr cut hc hs hcap hcut raw [] z table
  have source:=prepared wf (fineWord_fits x.2.1.2)
  have hg:=gridTape_adequate B r nt.length hr
  obtain ⟨G,hcode,hborn⟩:=hstep nt bt ft count width raw B hB R r hR hr cut hc hn hg hs sep hcut acc.length hbudget oracle.length z table
    x.1.1 x.1.2 x.2.1.1 x.2.1.2 x.2.2 wf (fineWord_exact _) (gap p nt.length nt.length) (emit (clear v,wf)) fit source
  change codeList G=wholeCodes ((fineSize x.2.1.2,activeWidth (withPool c)),emit (clear v,wf),stageInput qa c) at hcode
  change Cell.eventLaw G nt bt (readStart (withPool c)) (RegevSketch.coefficientMass B (r:ℝ)) (Cell.error C B hB R r hR hr acc cut hcut oracle.length z) at hborn
  apply realizes_of (G:=G) _ _ _ hcode hborn
  · change (wires spec v).length = activeWidth (withPool c)+x.2.2.length
    rw [wires_size,hc0]
  · change wholeCodes ((wf.length,activeWidth (withPool (call spec v))),emit (clear v,wf),stageInput qa (call spec v)) = _
    rw [hc0,fineWord_exact]
  · exact congrArg (fun q=>readStart (withPool q)) hc0

end

end InfoLossLAR.WorstCase.RegevSearch.RawBackend

end P2MDyadicModule218

/- Helper module UniformPhysical. -/
section P2MDyadicModule219

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RectangularSource RectangularSource.RawFront RectangularSource.Settings RectangularSource.Public

open RegevSketch PhysicalFourier PhysicalGrid NativeDualQuotient IntegerBasis CoherentDecoder

open AdaptiveStages AdaptiveStages.Outer GaussianIteration RawBackend

noncomputable section

theorem raw_rows {n m : ℕ} {C F : MFamily} {spec : Cell.Input→Spec} {emit : Cell.Input×List Unit→List ControlledNativeCode.GateCode} {qa : ℕ}
    (samples : OnRows C F spec emit qa) (nt copies acc oracle count width : List Unit) (dn : nt.length=n) (dm : count.length=m)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (hn : 0<n) (R r : ℚ) (hR : 0<R) (hr : 0<r) (cut : ℝ) (hc : 0<cut)
    (hs : (n:ℝ)*(physics r)^2≤cut^2) (hcap : cut≤(n+1:ℕ)*(r.den+1:ℕ)) (hcut : cut≤(famσ n:ℝ)/(2*(R:ℝ)))
    (sep : Separated (StageL B hB) cut) (tape advice : Str) (z : Rows n m)
    (table : ∀ i,encVec encI (z i) <+: (tape.drop (i.val*width.length)).take width.length)
    [Fintype (Residual B)] [Fintype (StageI B hB (gridTape (atBasis B r n acc).1).length cut)] :
    let v:=Cell.receipt (RationalInverse.Native.inputRows B) R r copies acc oracle count width tape advice
    let bt:=gridTape (atBasis B r n acc).1
    OracleTable.lookup (advice,(RawBackend.query spec v).length)=F.encAt (RawBackend.query spec v).length →
    Cell.schedule v=(nt,bt) ∧ realizes (describe spec emit qa v) nt bt (coefficientMass B (r:ℝ))
      (Cell.error C B hB R r hR hr acc cut hcut oracle.length z) := by
  subst n m
  exact samples nt copies acc oracle count width B hB hn R r hR hr cut hc hs hcap hcut sep tape advice z table

theorem _root_.solution (C : MFamily) (hC : IsMQPT C) (P : Polynomial ℕ) : UniformFourierRow C P := by
  obtain ⟨spec,hsp,emit,hem,front⟩:=InfoLossLAR.WorstCase.RegevSearch.uniform_rectangular_gaussian_preparation
  obtain ⟨F,hF,qa,samples⟩:=RawBackend.sampling C hC spec emit front
  refine ⟨F,hF,RawBackend.query spec,RawBackend.query_poly hsp,RawBackend.independent spec,?_⟩
  intro parse hp
  let f:=fun w=>describe spec emit qa (parse w)
  let hf:=Poly.comp (f:=describe spec emit qa) (g:=parse) (describe_poly hsp hem qa) hp
  obtain ⟨G,desc,hdesc,hdescEq,_,law⟩:=interpreted f hf
  refine ⟨G,desc,hdesc,hdescEq,?_⟩
  intro n B hB hn R t hR ht cut hc hs hcap hcut sep nt count acc oracle width dn cm ho widthBound
  let p:=atBasis B t n acc
  letI : Fintype (Residual B):=residualFintype B hB
  letI : Fintype (StageI B hB (gridTape p.1).length cut):=shortFintype _ (dualIntegerBasis B hB) cut sep
  refine ⟨oneAnalysis C P B hB R t hR ht acc cut hc hcut hs,?_⟩
  intro raw tbl w z v parsed lookup table
  obtain ⟨sched,circ,cc,events⟩:=raw_rows samples nt count acc oracle count width dn cm B hB hn R t hR ht cut hc hs hcap hcut sep raw tbl z table lookup
  let rv:=describe spec emit qa v
  have presented : f w=rv:=congrArg (describe spec emit qa) parsed
  have rs : rv.1=(nt,gridTape p.1):=sched
  have room:=read_fits spec v
  have h0 := congrArg (fun x : List Unit×List Unit => x.1.length*x.2.length) sched
  change (Cell.nt v).length*(Cell.bt v).length=nt.length*(gridTape p.1).length at h0
  rw [h0] at room
  obtain ⟨canon,near⟩:=law w rv presented nt (gridTape p.1) n dn rs circ cc _ _ events room width.length widthBound
  refine ⟨canon,?_⟩
  intro T
  have h:=near T
  rw [cost_eq C P B hB R t hR ht acc oracle cut hc hcut hs z ho] at h
  exact h

end

end InfoLossLAR.WorstCase.RegevSearch

end P2MDyadicModule219

#print axioms solution
