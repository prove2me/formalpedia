-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.iterate_uniform_fourier_row
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:52:57.114248+00:00
-- url     : https://prove2.me/submissions/c1344e4e-f9e1-416b-beb1-d9a33eeaf25a

import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
import Definitions.Def_QAlgorithms_Defs_Measurement
import Theorems.Thm_AFT_RationalNumerics_HeightBound_inv
import Theorems.Thm_InfoLossLAR_WorstCase_NativeLLL_Uniform_exists_reduce
import Theorems.Thm_InfoLossLAR_WorstCase_NativeLLL_basis_lattice_eq
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_compile_placed_gate_recipes
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_finite_grid_fourier_gaussian_event_bound
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_native_reduced_basis_halving_window
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_uniform_wide_gaussian_initial_sampler
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_RegevLWE_GaussConv_smoothing_remark
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq

set_option linter.all false
set_option Elab.async true
noncomputable section
set_option linter.all false

namespace AFT
end AFT

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace Function
end Function

namespace GridReadout
end GridReadout

namespace GridReadout.Axis
end GridReadout.Axis

namespace Hex.Internal
end Hex.Internal

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle
end InfoLossLAR.WorstCase.CoherentClassicalOracle

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute
end InfoLossLAR.WorstCase.CoherentComputeUncompute

namespace InfoLossLAR.WorstCase.CoherentDecoder
end InfoLossLAR.WorstCase.CoherentDecoder

namespace InfoLossLAR.WorstCase.CoherentProjection
end InfoLossLAR.WorstCase.CoherentProjection

namespace InfoLossLAR.WorstCase.ControlledLetterPlan
end InfoLossLAR.WorstCase.ControlledLetterPlan

namespace InfoLossLAR.WorstCase.ControlledNativeCode
end InfoLossLAR.WorstCase.ControlledNativeCode

namespace InfoLossLAR.WorstCase.ControlledNativeGates
end InfoLossLAR.WorstCase.ControlledNativeGates

namespace InfoLossLAR.WorstCase.ControlledRelocation
end InfoLossLAR.WorstCase.ControlledRelocation

namespace InfoLossLAR.WorstCase.FiniteGateTransport
end InfoLossLAR.WorstCase.FiniteGateTransport

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
end InfoLossLAR.WorstCase.GaussianPoissonSeries

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.rationalCode
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.rationalCode

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.readRational
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.readRational

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

namespace InfoLossLAR.WorstCase.NativeWordCoherent
end InfoLossLAR.WorstCase.NativeWordCoherent

namespace InfoLossLAR.WorstCase.NativeWordDescription
end InfoLossLAR.WorstCase.NativeWordDescription

namespace InfoLossLAR.WorstCase.NativeWordLayout
end InfoLossLAR.WorstCase.NativeWordLayout

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

namespace InfoLossLAR.WorstCase.RationalInverse
end InfoLossLAR.WorstCase.RationalInverse

namespace InfoLossLAR.WorstCase.RectangularSource
end InfoLossLAR.WorstCase.RectangularSource

namespace InfoLossLAR.WorstCase.RegevSearch
end InfoLossLAR.WorstCase.RegevSearch

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages
end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool
end InfoLossLAR.WorstCase.RegevSearch.FirstPool

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration
end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier
end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters
end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLAR.WorstCase.ShortProbe
end InfoLossLAR.WorstCase.ShortProbe

namespace InfoLossLAR.WorstCase.ShortProbePlan
end InfoLossLAR.WorstCase.ShortProbePlan

namespace InfoLossLAR.WorstCase.ShortProbePlan.parts
end InfoLossLAR.WorstCase.ShortProbePlan.parts

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

namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2NativeGaussian
end Integration9_9.TM2NativeGaussian

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

namespace OAI.MetricKMedian.Binary.Ratio.parts
end OAI.MetricKMedian.Binary.Ratio.parts

namespace OAI.MetricKMedian.Binary.Signed.parts
end OAI.MetricKMedian.Binary.Signed.parts

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

namespace SingleWidth
end SingleWidth

namespace Turing
end Turing


alias GridReadout.public_event_bound := InfoLossLAR.WorstCase.RegevSearch.finite_grid_fourier_gaussian_event_bound

set_option autoImplicit false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.NativeLLL
theorem determinant_from_same_lattice {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (same : lattice C=lattice B) : C.det≠0 := by
  classical
  have col (j : Fin n) : ∃ v, C.mulVec v = fun i => B i j := by
    let u : Fin n→ℤ:=Pi.single j 1
    have hb : latVec B u ∈ lattice B:=⟨u,rfl⟩
    rw [←same] at hb
    obtain ⟨v,hv⟩:=hb
    refine ⟨v,funext fun i=>?_⟩
    have hh:=congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) hv
    change ((C.mulVec v i:ℤ):ℝ)=((B.mulVec u i:ℤ):ℝ) at hh
    have he : C.mulVec v i=B.mulVec u i:=by exact_mod_cast hh
    simpa [u,Matrix.mulVec_single] using he
  choose v hv using col
  let T : Matrix (Fin n) (Fin n) ℤ:=fun i j=>v j i
  have eq : C*T=B := by ext i j;exact congrFun (hv j) i
  intro hz
  apply hB
  rw [←eq,Matrix.det_mul,hz,zero_mul]
theorem basis_det_ne_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) :
    (basis B).det≠0 := determinant_from_same_lattice _ _ hB (basis_lattice_eq B)
end InfoLossLAR.WorstCase.NativeLLL

open OAI.MetricKMedian.Binary.Automatic
namespace InfoLossLAR.WorstCase.NativeLLL.Uniform
noncomputable def reduce : List (List ℤ) → List (List ℤ) := Classical.choose exists_reduce
@[fun_prop] theorem reduce_poly : Poly reduce := (Classical.choose_spec exists_reduce).1
theorem reduce_exact {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) :
    reduce (RationalInverse.Native.inputRows B) = RationalInverse.Native.inputRows (basis B) :=
  (Classical.choose_spec exists_reduce).2 B hB
end InfoLossLAR.WorstCase.NativeLLL.Uniform
namespace SingleWidth
alias dimension_halvings := InfoLossLAR.WorstCase.RegevSearch.native_reduced_basis_halving_window
end SingleWidth

section
set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSearch InfoLossLAR.WorstCase.RegevSketch AFT AFT.RationalNumerics
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open scoped BigOperators Classical
namespace WideSamplerChoice
abbrev Setup := (List (List ℤ) × ℚ) × List Unit
noncomputable def bits : Setup → List Unit := Classical.choose uniform_wide_gaussian_initial_sampler
noncomputable def draw : Setup × List Bool → List ℤ := Classical.choose (Classical.choose_spec uniform_wide_gaussian_initial_sampler)
@[fun_prop] theorem bits_poly : Poly bits := (Classical.choose_spec (Classical.choose_spec uniform_wide_gaussian_initial_sampler)).1
@[fun_prop] theorem draw_poly : Poly draw := (Classical.choose_spec (Classical.choose_spec uniform_wide_gaussian_initial_sampler)).2.1
theorem small : ∀ {n : ℕ} {O : Type} [Fintype O] (D : Matrix (Fin n) (Fin n) ℤ), D.det≠0 → 1≤n →
    ∀ (r : ℚ) (a : List Unit) (post : (Fin n→ℤ) → FiniteDist O),
    let W : ℚ := max ((n+1:ℕ)*(1+∑ i,∑ j,|(D i j:ℚ)|)) (r*(famσ n:ℚ))
    let cfg := ((List.ofFn (fun i=>List.ofFn (fun j=>D i j)), W),a)
    let actual := (FiniteDist.uniform (Fin (bits cfg).length → Bool)).mix
      (fun tape => post (fun i => (draw (cfg,List.ofFn tape))[i.val]?.getD 0))
    ∃ ideal : FiniteDist O, (∀ o, ideal.weight o=∑' z,coefficientMass D W z*(post z).weight o) ∧
      FiniteDist.TVBound actual ideal
        (n*(2/(2:ℝ)^a.length+6*Real.exp (-Real.pi*((a.length:ℝ)+2)^2/2))+
          4*((n:ℝ)*(4/(2:ℝ)^(4*(n+1))))) :=
  (Classical.choose_spec (Classical.choose_spec uniform_wide_gaussian_initial_sampler)).2.2
theorem channel : ∀ {n : ℕ} {O : Type*} [Fintype O] (D : Matrix (Fin n) (Fin n) ℤ), D.det≠0 → 1≤n →
    ∀ (r : ℚ) (a : List Unit) (post : (Fin n→ℤ) → FiniteDist O),
    let W : ℚ := max ((n+1:ℕ)*(1+∑ i,∑ j,|(D i j:ℚ)|)) (r*(famσ n:ℚ))
    let cfg := ((List.ofFn (fun i=>List.ofFn (fun j=>D i j)), W),a)
    let actual := (FiniteDist.uniform (Fin (bits cfg).length → Bool)).mix
      (fun tape => post (fun i => (draw (cfg,List.ofFn tape))[i.val]?.getD 0))
    ∃ ideal : FiniteDist O, (∀ o, ideal.weight o=∑' z,coefficientMass D W z*(post z).weight o) ∧
      FiniteDist.TVBound actual ideal
        (n*(2/(2:ℝ)^a.length+6*Real.exp (-Real.pi*((a.length:ℝ)+2)^2/2))+
          4*((n:ℝ)*(4/(2:ℝ)^(4*(n+1))))) := by
  classical
  intro n O _ D hD hn r a post
  let e := Fintype.equivFin O
  obtain ⟨ideal, hm, ht⟩ := small D hD hn r a (fun z => (post z).map e)
  refine ⟨ideal.map e.symm, ?_, ?_⟩
  · intro o
    simpa only [FiniteDist.map_equiv_weight, Equiv.symm_symm, Equiv.symm_apply_apply] using hm (e o)
  · intro s
    have h := ht (s.map e.toEmbedding)
    simpa only [FiniteDist.event, Finset.sum_map, Equiv.coe_toEmbedding, FiniteDist.mix,
      FiniteDist.map_equiv_weight, Equiv.symm_apply_apply, Equiv.symm_symm] using h
end WideSamplerChoice
namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide
noncomputable def ticks := WideSamplerChoice.bits
noncomputable def sample := WideSamplerChoice.draw
@[fun_prop] theorem ticks_poly : OAI.MetricKMedian.Binary.Automatic.Poly ticks := WideSamplerChoice.bits_poly
@[fun_prop] theorem sample_poly : OAI.MetricKMedian.Binary.Automatic.Poly sample := WideSamplerChoice.draw_poly
alias scheduled_initial_sample := WideSamplerChoice.channel
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

end
/- Helper module AFT.Negligible. -/
section P2MDyadicModule0

namespace AFT

open Filter

open scoped Topology

/-- A positive stretched exponential dominates every real power. -/
theorem stretched_exponential_tendsto (power exponent rate : ℝ)
    (hexponent : 0 < exponent) (hrate : 0 < rate) :
    Tendsto (fun parameter : ℝ => parameter ^ power *
      Real.exp (-rate * parameter ^ exponent)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (power / exponent) rate hrate).comp (tendsto_rpow_atTop hexponent)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with parameter hp
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hp, mul_div_cancel₀ power hexponent.ne']

/-- Polynomially many stretched-exponential errors are genuinely negligible,
with arbitrary fixed positive exponent, including the leg exponent `1/4`. -/
theorem negligible_polynomial_stretched_exponential
    (constant : ℝ) (degree : ℕ) (exponent rate : ℝ)
    (hconstant : 0 ≤ constant) (hexponent : 0 < exponent) (hrate : 0 < rate) :
    Negligible (fun parameter => constant * (parameter : ℝ) ^ degree *
      Real.exp (-rate * (parameter : ℝ) ^ exponent)) := by
  intro order
  have hreal := (stretched_exponential_tendsto (degree + order : ℕ) exponent rate
    hexponent hrate).const_mul constant
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ parameter : ℕ in atTop,
      constant * ((parameter : ℝ) ^ (degree + order : ℕ) *
        Real.exp (-rate * (parameter : ℝ) ^ exponent)) < 1 := by
    simpa only [Function.comp_apply, mul_zero, Real.rpow_natCast] using
      hnat.eventually (gt_mem_nhds (show constant * (0 : ℝ) < 1 by simp))
  filter_upwards [hsmall, eventually_ge_atTop 1] with parameter hs hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hnonneg : 0 ≤ constant * (parameter : ℝ) ^ degree *
      Real.exp (-rate * (parameter : ℝ) ^ exponent) := by positivity
  rw [abs_of_nonneg hnonneg, le_div_iff₀ (pow_pos hp' order)]
  rw [pow_add] at hs
  nlinarith [hs]

theorem Negligible.add {left right : ℕ → ℝ} (hl : Negligible left)
    (hr : Negligible right) : Negligible (fun parameter => left parameter + right parameter) := by
  intro order
  filter_upwards [hl (order + 1), hr (order + 1), eventually_ge_atTop 2]
    with parameter hl' hr' hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have htwo : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
  apply (abs_add_le _ _).trans ((add_le_add hl' hr').trans ?_)
  rw [pow_succ, ← add_div]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hp' order) hp') (pow_pos hp' order)).mpr
  nlinarith [pow_pos hp' order]

theorem Negligible.mul_polynomial {error : ℕ → ℝ} (h : Negligible error) (degree : ℕ) :
    Negligible (fun parameter => (parameter : ℝ) ^ degree * error parameter) := by
  intro order
  filter_upwards [h (degree + order), eventually_ge_atTop 1] with parameter he hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (parameter : ℝ) ^ degree)]
  calc
    _ ≤ (parameter : ℝ) ^ degree * (1 / (parameter : ℝ) ^ (degree + order)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [pow_add]; field_simp

end AFT

end P2MDyadicModule0

/- Helper module AFT.RationalHeight. -/
section P2MDyadicModule1

namespace AFT.RationalNumerics

open scoped BigOperators

namespace HeightBound

theorem mono {value : ℚ} {first second : ℕ} (h : HeightBound value first) (hle : first ≤ second) :
    HeightBound value second := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
  exact ⟨h.1.trans hp,h.2.trans hp⟩

private theorem reduced_le (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (Rat.divInt num (den : ℤ)).num.natAbs ≤ num.natAbs ∧ (Rat.divInt num (den : ℤ)).den ≤ den := by
  constructor
  · by_cases hn : num=0
    · simp [hn]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd num (by exact_mod_cast hd.ne')))
  · exact Nat.le_of_dvd hd (by exact_mod_cast Rat.den_dvd num (den : ℤ))

theorem zero : HeightBound 0 0 := by norm_num [HeightBound]

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

end P2MDyadicModule1

/- Helper module Iteration. -/
section P2MDyadicModule2

set_option autoImplicit false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

noncomputable section

abbrev Test (X : Type*) := X → Set.Icc (0 : ℝ) 1

/-- A transition evaluates the conditional probability of the downstream test on the
actual stage input. Its codomain includes the probability bounds needed at the next step. -/
abbrev Transition (X Y : Type*) := Test Y → Test X

def evaluate {X : Type*} (p : PMF X) (f : Test X) : ℝ := ∑' x, (p x).toReal * (f x : ℝ)

theorem mass_summable {X : Type*} (p : PMF X) : HasSum (fun x => (p x).toReal) 1 := by
  have h := ENNReal.hasSum_toReal (f:=fun x => p x) (by rw [p.tsum_coe];simp)
  rwa [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x),p.tsum_coe,ENNReal.toReal_one] at h

theorem evaluate_summable {X : Type*} (p : PMF X) (f : Test X) :
    Summable (fun x => (p x).toReal*(f x:ℝ)) :=
  (mass_summable p).summable.of_nonneg_of_le (fun _ => mul_nonneg ENNReal.toReal_nonneg (f _).property.1)
    (fun _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (f _).property.2)

theorem evaluate_range {X : Type*} (p : PMF X) (f : Test X) : evaluate p f ∈ Set.Icc (0:ℝ) 1 := by
  exact ⟨tsum_nonneg (fun _ => mul_nonneg ENNReal.toReal_nonneg (f _).property.1),
    ((evaluate_summable p f).tsum_le_tsum (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg
      (f x).property.2) (mass_summable p).summable).trans_eq (mass_summable p).tsum_eq⟩

def transition {X Y : Type*} (K : X → PMF Y) : Transition X Y :=
  fun f x => ⟨evaluate (K x) f,evaluate_range _ _⟩

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule2

/- Helper module Markov. -/
section P2MDyadicModule3

set_option autoImplicit false

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

noncomputable section

def eexpect {Y : Type*} (p : PMF Y) (f : Test Y) : ℝ≥0∞ :=
  ∑' y, p y * ENNReal.ofReal (f y)

theorem eexpect_eq {Y : Type*} (p : PMF Y) (f : Test Y) :
    eexpect p f = ENNReal.ofReal (evaluate p f) := by
  unfold eexpect evaluate
  rw [ENNReal.ofReal_tsum_of_nonneg (fun y => mul_nonneg ENNReal.toReal_nonneg (f y).property.1)
    (evaluate_summable p f)]
  apply tsum_congr
  intro y
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (p.apply_ne_top y)]

theorem eval_bind {X Y : Type*} (p : PMF X) (K : X → PMF Y) (f : Test Y) :
    evaluate (p.bind K) f = evaluate p (transition K f) := by
  apply (ENNReal.ofReal_eq_ofReal_iff (evaluate_range _ _).1 (evaluate_range _ _).1).mp
  rw [← eexpect_eq,← eexpect_eq]
  change (∑' y, (p.bind K) y * ENNReal.ofReal (f y)) =
    ∑' x, p x * ENNReal.ofReal (evaluate (K x) f)
  simp_rw [PMF.bind_apply,← eexpect_eq,eexpect,← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_right,mul_assoc]
  exact ENNReal.tsum_comm

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule3

/- Helper module PoolStage. -/
section P2MDyadicModule4

set_option autoImplicit false

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

noncomputable section

def push {X Y : Type*} (g : X → Y) (f : Test Y) : Test X := fun x => f (g x)

theorem eval_pure {X : Type*} (x : X) (f : Test X) : evaluate (PMF.pure x) f = f x := by
  classical
  unfold evaluate
  rw [tsum_eq_single x]
  · simp
  · intro y hy
    simp [PMF.pure_apply,hy,Ne.symm hy]

theorem eval_map {X Y : Type*} (p : PMF X) (g : X → Y) (f : Test Y) :
    evaluate (p.map g) f = evaluate p (push g f) := by
  change evaluate (p.bind (fun x => pure (g x))) f = _
  rw [eval_bind]
  congr 1
  funext x
  exact Subtype.ext (eval_pure (g x) f)

theorem eval_difference {X : Type*} (p : PMF X) (f g : Test X) (d : ℝ) (h : ∀ x, |(f x:ℝ)-(g x:ℝ)|≤d) :
    |evaluate p f-evaluate p g|≤d := by
  let μ := fun x : X => (p x).toReal
  have hs := (evaluate_summable p f).sub (evaluate_summable p g)
  have hd := (mass_summable p).mul_right d
  have he : ∑' x, μ x*d = d := by simpa only [one_mul] using hd.tsum_eq
  unfold evaluate
  rw [← (evaluate_summable p f).tsum_sub (evaluate_summable p g)]
  apply abs_le.mpr
  constructor
  · have hle : ∀ x, -(μ x*d) ≤ (p x).toReal*(f x:ℝ)-(p x).toReal*(g x:ℝ) := by
      intro x
      simpa only [μ,mul_neg,mul_sub] using mul_le_mul_of_nonneg_left (abs_le.mp (h x)).1
        (ENNReal.toReal_nonneg (a:=p x))
    exact (show -d = ∑' x, -(μ x*d) by simp only [tsum_neg,he]).le.trans
      (hd.summable.neg.tsum_le_tsum hle hs)
  · have hle : ∀ x, (p x).toReal*(f x:ℝ)-(p x).toReal*(g x:ℝ) ≤ μ x*d := by
      intro x
      simpa only [μ,mul_sub] using mul_le_mul_of_nonneg_left (abs_le.mp (h x)).2
        (ENNReal.toReal_nonneg (a:=p x))
    exact (hs.tsum_le_tsum hle hd.summable).trans_eq he

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule4

/- Helper module PoolEvents. -/
section P2MDyadicModule5

set_option autoImplicit false

open scoped BigOperators Classical ENNReal

open Filter

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

noncomputable section

variable {X Y : Type*}

private theorem upper_finite (p q : PMF X) (d : ℝ) (he : ∀ T, |finiteMass p T-finiteMass q T|≤d)
    (f : Test X) (s : Finset X) :
    ∑ x ∈ s, ((p x).toReal*(f x:ℝ)-(q x).toReal*(f x:ℝ)) ≤ d := by
  classical
  let t := s.filter (fun x => (q x).toReal ≤ (p x).toReal)
  have hd := (abs_le.mp (he t)).2
  rw [finiteMass,finiteMass,←Finset.sum_sub_distrib] at hd
  change _ ≤ _ at hd
  apply le_trans _ hd
  dsimp only [t]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x hx
  rw [←sub_mul]
  by_cases h : (q x).toReal ≤ (p x).toReal
  · rw [if_pos h]
    exact mul_le_of_le_one_right (sub_nonneg.mpr h) (f x).property.2
  · rw [if_neg h]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge h)) (f x).property.1

theorem tests_of_finite_events (p q : PMF X) (d : ℝ) (he : ∀ T, |finiteMass p T-finiteMass q T|≤d)
    (f : Test X) : |evaluate p f-evaluate q f| ≤ d := by
  have upper (p q : PMF X) (h : ∀ T, |finiteMass p T-finiteMass q T|≤d) :
      evaluate p f-evaluate q f≤d := by
    have hs := (evaluate_summable p f).hasSum.sub (evaluate_summable q f).hasSum
    exact le_of_tendsto hs (Eventually.of_forall (upper_finite p q d h f))
  exact abs_le.mpr ⟨by have ht := upper q p (fun T => by simpa only [abs_sub_comm] using he T);linarith,
    upper p q he⟩

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule5

/- Helper module BornLaw. -/
section P2MDyadicModule6

set_option autoImplicit false

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open QAlgorithms.Complexity

noncomputable section

def indicator {X : Type*} (E : X → Prop) : Test X :=
  fun x => ⟨if E x then 1 else 0,by split <;> simp⟩

theorem born_native (F : MFamily) (w : Str) (E : Str → Prop) :
    evaluate (measuredWord F w) (indicator E) = outputProb F w E := by
  classical
  rw [measuredWord,eval_map]
  unfold evaluate outputProb
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [push,indicator,measuredBits,PMF.ofFintype_apply,ENNReal.toReal_ofReal (Complex.normSq_nonneg _)]
  split <;> simp [Complex.sq_norm]

theorem finite_event {X : Type*} (p : PMF X) (T : Finset X) :
    evaluate p (indicator (fun x => x∈T)) = finiteMass p T := by
  classical
  unfold evaluate finiteMass indicator
  rw [tsum_eq_sum (s:=T)]
  · apply Finset.sum_congr rfl
    intro x hx; simp [hx]
  · intro x hx; simp [hx]

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeInverseCircuit. -/
section P2MDyadicModule7

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

/-- A valid layered inverse circuit, using one gate per layer and no new wires. -/
def inverseCircuit {n : ℕ} (circuit : Layered n) : Layered n :=
  (inverseGates circuit.flatten).map (fun g => [g])

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

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeCoherentComputeUncompute. -/
section P2MDyadicModule8

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open FiniteGateTransport

open scoped BigOperators

variable {D W I : Type*} [Fintype D] [Fintype W] [DecidableEq W]

noncomputable def basis (w : W) : W → ℂ := fun r => if r=w then 1 else 0

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

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeCoherentBasisEmbedding. -/
section P2MDyadicModule9

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open scoped BigOperators

variable {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W]

/-- An analysis map storing all coherent indices in distinct physical basis
states. This specifies amplitudes and is not asserted to be a circuit. -/
noncomputable def basisEmbedding (e : I ↪ W) : (I → ℂ) →ₗ[ℂ] (W → ℂ) where
  toFun ψ := ∑ i,ψ i • basis (e i)
  map_add' ψ φ := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c ψ := by simp [mul_smul,Finset.smul_sum]

theorem basisEmbedding_at (e : I ↪ W) (ψ : I → ℂ) (i : I) :
    basisEmbedding e ψ (e i)=ψ i := by
  classical
  simp [basisEmbedding,basis,e.injective.eq_iff]

theorem basisEmbedding_outside (e : I ↪ W) (ψ : I → ℂ) (w : W)
    (h : w∉Set.range e) : basisEmbedding e ψ w=0 := by
  have he (i : I) : w≠e i := fun hh => h ⟨i,hh.symm⟩
  simp [basisEmbedding,basis,he]

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end P2MDyadicModule9

/- Helper module DeferredStage. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

noncomputable section

variable {A B X Y : Type*} [Fintype A] [Fintype B]

def born (v : A→ℂ) (h : ∑ a, ‖v a‖^2=1) : PMF A :=
  PMF.ofFintype (fun x => ENNReal.ofReal (‖v x‖^2))
    (by rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),h];simp)

theorem born_eval (v : A→ℂ) (hv : ∑ a, ‖v a‖^2=1) (f : Test A) :
    evaluate (born v hv) f=∑ a, ‖v a‖^2*(f a:ℝ) := by
  simp [born,evaluate,ENNReal.toReal_ofReal (sq_nonneg _),tsum_fintype]

attribute [local irreducible] born evaluate

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeWireRelocation. -/
section P2MDyadicModule11

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

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeToffoli. -/
section P2MDyadicModule12

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

end P2MDyadicModule12

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule13

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

/-- A concrete Boolean-list program is a platform string-time certificate. -/
theorem polyTime_of_poly {f : Str → Str} (h : Poly f) : PolyTimeComputable f := by
  let P := (BooleanLists.packProgram.comp h.program).comp BooleanLists.unpackProgram
  exact ⟨(P.congr f (fun _ => rfl)).stock⟩

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

end P2MDyadicModule13

/- Helper module Integration9_9.TM2OutputLength. -/
section P2MDyadicModule14

set_option autoImplicit false

namespace Integration9_9.TM2OutputLength

open Turing StateTransition

variable {K Λ σ : Type} {Γ : K → Type} [Fintype K] [DecidableEq K]

variable [Fintype Λ]

attribute [local instance] Integration9_9.TM2OutputLength.tmStacksFintype

attribute [local instance] Integration9_9.TM2OutputLength.tmLabelsFintype

/-- Polynomial-time TM2 computations have polynomially bounded encoded output
length. This is the size estimate required when composing time polynomials. -/
theorem polynomial_output_length {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (machine : TM2ComputableInPolyTime ea eb f) :
    ∃ p : Polynomial ℕ, ∀ a, (eb (f a)).length ≤ p.eval (ea a).length := by
  refine ⟨Polynomial.X + Polynomial.C (programPushBound machine.tm.m) * machine.time, ?_⟩
  intro a
  have h := output_length_le machine.tm
    (List.map machine.inputAlphabet.invFun (ea a))
    (List.map machine.outputAlphabet.invFun (eb (f a)))
    (machine.time.eval (ea a).length) (machine.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] using h

end Integration9_9.TM2OutputLength

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeInverseUniform. -/
section P2MDyadicModule15

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

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
section P2MDyadicModule16

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

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeReversibleUniform. -/
section P2MDyadicModule17

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

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule18

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

end P2MDyadicModule18

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule19

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

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeCircuitRelocation. -/
section P2MDyadicModule20

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity

open scoped BigOperators

/-- Relocate all five actual gate constructors along public physical wires. -/
def relocateInstr {k n : ℕ} (w : Fin k ↪ Fin n) : Instr k → Instr n
  | .h i => .h (w i)
  | .s i => .s (w i)
  | .t i => .t (w i)
  | .x i => .x (w i)
  | .cnot i j h => .cnot (w i) (w j) (w.injective.ne h)

def relocateCircuit {k n : ℕ} (w : Fin k ↪ Fin n) (circuit : Layered k) : Layered n :=
  circuit.map (List.map (relocateInstr w))

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

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeInitializedRelocation. -/
section P2MDyadicModule21

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

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeCircuitInitializedEmbedding. -/
section P2MDyadicModule22

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

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeControlledNativeCode. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledNativeCode

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Tags 0,1,2,3,4 mean H,S,T,X,CNOT. Natural addresses use binary coding. -/
abbrev GateCode := ℕ×ℕ×ℕ

def encodeInstr {n : ℕ} : Instr n → GateCode
  | .h i => (0,i.val,0)
  | .s i => (1,i.val,0)
  | .t i => (2,i.val,0)
  | .x i => (3,i.val,0)
  | .cnot i j _ => (4,i.val,j.val)

end InfoLossLAR.WorstCase.ControlledNativeCode

end P2MDyadicModule23

/- Helper module AdaptiveLoad. -/
section P2MDyadicModule24

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 950000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

noncomputable section

variable {h k : ℕ}

inductive Source (h : ℕ) where
  | literal (b : Bool)
  | wire (i : Fin h)

def Source.read (s : Source h) (x : Bits h) : Bool :=
  match s with | .literal b => b | .wire i => x i

def gate (target : Fin k) (v : Source h) : List (Instr (h+k)) :=
  match v with
  | .literal true => [.x (Fin.natAdd h target)]
  | .literal false => []
  | .wire i => [.cnot (Fin.castAdd k i) (Fin.natAdd h target) (by intro he;have := congrArg Fin.val he;simp at this;omega)]

def load (a : Fin k → Source h) := (List.finRange k).flatMap (fun t => gate t (a t))

private theorem x_action {n : ℕ} (t : Fin n) (ψ : QState n) (x : Bits n) :
    (Instr.x t).apply ψ x=ψ (Function.update x t (!(x t))) := by
  cases ht : x t <;> simp [Instr.apply,apply1,xMat,ht]

theorem append_update (x : Bits h) (y : Bits k) (t : Fin k) (b : Bool) :
    Function.update (Fin.append x y) (Fin.natAdd h t) b=Fin.append x (Function.update y t b) := by
  funext u; refine Fin.addCases ?_ ?_ u
  · intro i
    have hn : Fin.castAdd k i≠Fin.natAdd h t := by intro he; have := congrArg Fin.val he;simp at this;omega
    simp [Function.update_of_ne hn]
  · intro i
    by_cases he : i=t
    · subst i; simp
    · have hne : Fin.natAdd h i≠Fin.natAdd h t := by intro hi; apply he;exact Fin.ext (by have := congrArg Fin.val hi;simpa using this)
      simp [Function.update_of_ne he,Function.update_of_ne hne]

theorem single_action (t : Fin k) (s : Source h) (ψ : QState (h+k)) (x : Bits h) (y : Bits k) :
    runLayer (gate t s) ψ (Fin.append x y)=
      ψ (Fin.append x (Function.update y t (xor (y t) (s.read x)))) := by
  cases s with
  | literal b =>
    cases b
    · simp [gate,Source.read,runLayer]
    · change (Instr.x _).apply ψ _=_
      rw [x_action,append_update]
      simp [Source.read]
  | wire i =>
    change ψ (Function.update _ _ _) = _
    rw [append_update]
    simp [Source.read]

def mask (a : Fin k → Source h) (x : Bits h) (l : List (Fin k)) (y : Bits k) :=
  fun i => xor (y i) (decide (i∈l) && (a i).read x)

private theorem mask_push (a : Fin k → Source h) (x : Bits h) (t : Fin k) (l : List (Fin k))
    (ht : t∉l) (y : Bits k) :
    Function.update (mask a x l y) t (xor (mask a x l y t) ((a t).read x))=mask a x (t::l) y := by
  funext i
  by_cases hi : i=t
  · subst i;simp [mask,ht]
  · simp [mask,hi,Function.update_of_ne hi]

theorem partial_load (a : Fin k → Source h) (l : List (Fin k)) (hl : l.Nodup)
    (ψ : QState (h+k)) (x : Bits h) (y : Bits k) :
    runLayer (l.flatMap (fun t => gate t (a t))) ψ (Fin.append x y)=ψ (Fin.append x (mask a x l y)) := by
  induction l generalizing ψ with
  | nil =>
    have hm : mask a x [] y = y := by funext i;simp [mask]
    rw [hm];rfl
  | cons t l ih =>
    rw [List.flatMap_cons,runLayer_append,ih hl.of_cons,single_action,mask_push _ _ _ _ (List.nodup_cons.mp hl).1]

theorem load_action (a : Fin k → Source h) (ψ : QState (h+k)) (x : Bits h) (y : Bits k) :
    runLayer (load a) ψ (Fin.append x y)=ψ (Fin.append x (fun i => xor (y i) ((a i).read x))) := by
  rw [load,partial_load _ _ (List.nodup_finRange k)]
  apply congrArg (fun v => ψ (Fin.append x v))
  funext i;simp [mask]

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule24

/- Helper module AdaptiveBranch. -/
section P2MDyadicModule25

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open scoped BigOperators Classical

noncomputable section

variable {h k : ℕ}

def right (h k : ℕ) : Fin k ↪ Fin (h+k) := Fin.natAddEmb h

theorem right_parts (x : Bits h) (y z : Bits k) :
    (wireBitsEquiv (right h k) (Fin.append x y)).2=(wireBitsEquiv (right h k) (Fin.append x z)).2 := by
  funext i
  rcases i with ⟨i,hi⟩
  change Fin.append x y i=Fin.append x z i
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro i _;simp
  · intro j hj;exact False.elim (hj ⟨j,rfl⟩)

@[simp] theorem right_selected (x : Bits h) (y : Bits k) :
    (wireBitsEquiv (right h k) (Fin.append x y)).1=y := by funext i;exact Fin.append_right _ _ _

theorem right_slice (U : Layered k) (ψ : QState (h+k)) (x : Bits h) (y : Bits k) :
    runLayered (relocateCircuit (right h k) U) ψ (Fin.append x y)=runLayered U (fun j => ψ (Fin.append x j)) y := by
  let w := right h k
  let p := wireBitsEquiv w (Fin.append x y)
  have hs := congrFun (relocateCircuit_split w U ψ) p
  change runLayered (relocateCircuit w U) ψ ((wireBitsEquiv w).symm ((wireBitsEquiv w) (Fin.append x y)))=_ at hs
  rw [Equiv.symm_apply_apply] at hs
  have hf (j : Bits k) : (wireBitsEquiv w).symm (j,p.2)=Fin.append x j := by
    apply (wireBitsEquiv w).symm_apply_eq.mpr
    exact Prod.ext (right_selected x j).symm (right_parts x y j)
  rw [hs]
  have he : (fun j => splitState w ψ (j,p.2))=(fun j => ψ (Fin.append x j)) := by
    funext j; change ψ _=_; rw [hf]
  rw [he]
  exact congrArg (runLayered U (fun j => ψ (Fin.append x j))) (right_selected x y)

def stage (a : Fin k → Source h) (U : Layered k) : Layered (h+k) :=
  (load a).map (fun g => [g]) ++ relocateCircuit (right h k) U

theorem read_zero (u v : Bits k) :
    (fun i => xor (u i) (v i))=(fun _ => false) ↔ u=v := by
  constructor
  · intro h;funext i;have hi:=congrFun h i;cases a : u i <;> cases b : v i <;> simp_all
  · rintro rfl;funext i;simp

theorem stage_branch (a : Fin k→Source h) (U : Layered k) (v : QState h)
    (x : Bits h) (y : Bits k) :
    runLayered (stage a U) (tensorState v (basis (fun _ : Fin k => false))) (Fin.append x y)=
    v x * runLayered U (basis (fun i => (a i).read x)) y := by
  rw [stage,show ∀ {n : ℕ} (c d : Layered n) (ψ : QState n),runLayered (c++d) ψ=runLayered d (runLayered c ψ)
        from fun _ _ _ => List.foldl_append,runLayered_singletons,right_slice]
  have hf : (fun j => runLayer (load a) (tensorState v (basis (fun _ => false))) (Fin.append x j)) =
      (v x) • basis (fun i => (a i).read x) := by
    funext j
    rw [load_action]
    have hl (u : Bits k) : leftRegister (Fin.append x u)=x := by funext i;exact Fin.append_left _ _ _
    have hr (u : Bits k) : rightRegister (Fin.append x u)=u := by funext i;exact Fin.append_right _ _ _
    simp only [tensorState,hl,hr,basis,Pi.smul_apply,smul_eq_mul,read_zero]
  rw [hf,←runLayeredLinearMap_apply,map_smul]
  simp only [Pi.smul_apply,smul_eq_mul,runLayeredLinearMap_apply]

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule25

/- Helper module Solutions.AdvantageBridgeBundleEmitter. -/
section P2MDyadicModule26

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

end P2MDyadicModule26

/- Helper module Solutions.AdvantageBridgeBundleUniform. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity Turing Function Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open Integration9_9 Integration9_9.TM2StockLists QMCNumericRuntime

theorem bundleRequests_correct (budget : Polynomial ℕ) (input : Str) :
    bundleRequests budget input = List.ofFn (fun index : Fin (budget.eval input.length+1) => unary index.val) := by
  apply List.ext_getElem
  · simp [bundleRequests,bundleRequestsFromSlots]
  · intro i hi hj
    simp only [bundleRequests,bundleRequestsFromSlots,List.length_map,List.length_range,
      List.length_replicate] at hi
    simp only [bundleRequests,bundleRequestsFromSlots,List.getElem_map,List.getElem_range,
      List.take_replicate,List.getElem_ofFn,List.map_replicate,unary]
    rw [Nat.min_eq_left (by omega)]

end InfoLossLAR.WorstCase

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeBooleanUniform. -/
section P2MDyadicModule28

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

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule29

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

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule30

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

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule31

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

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule32

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

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule33

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

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeBooleanSize. -/
section P2MDyadicModule34

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

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule35

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

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeBooleanRPN. -/
section P2MDyadicModule36

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

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeBooleanRPNRun. -/
section P2MDyadicModule37

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

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeBooleanCodePoly. -/
section P2MDyadicModule38

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

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeTM2CodeFamily. -/
section P2MDyadicModule39

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

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeTM2CodeTransition. -/
section P2MDyadicModule40

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

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeTM2CodeEnumeration. -/
section P2MDyadicModule41

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

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule42

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

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeTM2Size. -/
section P2MDyadicModule43

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

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule44

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

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeTM2CodeRegisters. -/
section P2MDyadicModule45

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

end P2MDyadicModule45

/- Helper module Solutions.RegevBridgeBooleanRPNBounds. -/
section P2MDyadicModule46

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

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeTM2CodeStep. -/
section P2MDyadicModule47

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

end P2MDyadicModule47

/- Helper module Solutions.RegevBridgeTM2CodeLoop. -/
section P2MDyadicModule48

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

end P2MDyadicModule48

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule49

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

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeTM2CodeGenerate. -/
section P2MDyadicModule50

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

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeBooleanNodeSerialization. -/
section P2MDyadicModule51

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

end P2MDyadicModule51

/- Helper module Solutions.AdvantageBridgeQuantumCoins. -/
section P2MDyadicModule52

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

end P2MDyadicModule52

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule53

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

end InfoLossLAR.WorstCase

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule54

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

end P2MDyadicModule54

/- Helper module Solutions.RegevBridgeTM2CodeDescription. -/
section P2MDyadicModule55

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

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule56

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

end P2MDyadicModule56

/- Helper module Solutions.RegevBridgeTM2PolyUniform. -/
section P2MDyadicModule57

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

end P2MDyadicModule57

/- Helper module Solutions.AdvantageBridgeQueryQuantum. -/
section P2MDyadicModule58

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

end P2MDyadicModule58

/- Helper module Solutions.AdvantageBridgeQueryMetadata. -/
section P2MDyadicModule59

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

end P2MDyadicModule59

/- Helper module Solutions.RegevBridgeTM2MultiOutput. -/
section P2MDyadicModule60

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

end P2MDyadicModule60

/- Helper module Solutions.RegevBridgeGaussianPoissonSeries. -/
section P2MDyadicModule61

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open MeasureTheory FourierTransform RegevLWE.GaussConv

open scoped FourierTransform SchwartzMap

noncomputable section

variable {dimension : ℕ}

abbrev Space := EuclideanSpace ℝ (Fin dimension)

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

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule61

/- Helper module Solutions.RegevBridgeLatticeGaussianSummable. -/
section P2MDyadicModule62

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

end P2MDyadicModule62

/- Helper module Solutions.RegevBridgeGaussianRoundingNative. -/
section P2MDyadicModule63

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

end P2MDyadicModule63

/- Helper module Solutions.RegevBridgeGaussianProjectionSmoothing. -/
section P2MDyadicModule64

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

/-- Increasing the positive Gaussian width increases every actual mass. -/
theorem rho_width_mono {dimension : ℕ} {first second : ℝ} (hfirst : 0<first) (hsecond : first ≤ second)
    (value : EuclideanSpace ℝ (Fin dimension)) : rho first value ≤ rho second value := by
  have hs : 0<second := hfirst.trans_le hsecond
  unfold rho
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le (sq_nonneg ‖value‖))
    (sq_pos_of_pos hfirst) ((sq_le_sq₀ hfirst.le hs.le).mpr hsecond)
  simpa only [neg_div,neg_mul] using neg_le_neg h

/-- Summability of the actual nonzero-dual Gaussian, with all premises
discharged by the proved smoothing characterization, including dim 0. -/
theorem summable_dual_of_smoothing {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0<error) (hwidth : 0<width) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (fun value : {value : dual lattice // value≠0} => rho (1/width) (value : EuclideanSpace ℝ (Fin dimension))) := by
  rcases Nat.eq_zero_or_pos dimension with rfl | hdimension
  · have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have : IsEmpty {value : dual lattice // value≠0} :=
      ⟨fun value => value.property (Subsingleton.elim value.val 0)⟩
    have : Fintype {value : dual lattice // value≠0} := Fintype.ofIsEmpty
    exact HasSum.summable (hasSum_fintype _)
  · obtain ⟨_,_,_,_,hthreshold⟩ := RegevLWE.GaussConv.smoothing_remark hdimension lattice
    obtain ⟨hpositive,hequal⟩ := hthreshold error herror
    have hs : Summable (fun value : {value : dual lattice // value≠0} =>
        rho (1/smoothingParam lattice error) (value : EuclideanSpace ℝ (Fin dimension))) := by
      by_contra hnonsummable
      have hzero := tsum_eq_zero_of_not_summable hnonsummable
      change rhoDualNonzero (1/smoothingParam lattice error) lattice=0 at hzero
      rw [hequal] at hzero
      exact herror.ne' hzero
    apply Summable.of_nonneg_of_le (fun value => Real.exp_nonneg _) _ hs
    intro value
    apply rho_width_mono (div_pos zero_lt_one hwidth)
    exact one_div_le_one_div_of_le hpositive hsmoothing

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule64

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule65

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

/-- The Gaussian submodule is exactly the original worst-case target's
`L(B)=Bℤ^n`, with the original integer-basis convention. -/
theorem inputLattice_eq_target (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (inputLattice basis hdet : Set (Space (dimension:=dimension)))=InfoLossLAR.WorstCase.lattice basis := by
  ext point
  constructor
  · intro membership
    let value : inputLattice basis hdet := ⟨point,membership⟩
    refine ⟨(integerBasis basis hdet).equivFun value,?_⟩
    rw [←coefficient_point basis hdet,LinearEquiv.symm_apply_apply]
  · rintro ⟨value,rfl⟩
    rw [←coefficient_point basis hdet value]
    exact Subtype.prop _

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule65

/- Helper module Integration9_9.TM2NativeAffineApply. -/
section P2MDyadicModule66

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

private theorem zip_ofFn {α β : Type} {n : ℕ} (f : Fin n→α) (g : Fin n→β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i=>(f i,g i)) := by apply List.ext_getElem <;> simp

theorem dot_ofFn {n : ℕ} (f g : Fin n→ℤ) : dot (List.ofFn f,List.ofFn g)=∑i,f i*g i := by
  simp only [dot,zip_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]

end Integration9_9.TM2NativeAffineApply

end P2MDyadicModule66

/- Helper module Solutions.RegevBridgeGaussianNumericalBudget. -/
section P2MDyadicModule67

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

/-- Elementary explicit exponential bound, before taking any asymptotic
limit. It also discharges the theta smallness premise at every sigma≥2. -/
theorem sigma_gaussian_exp_le (sigma : ℕ) (hsigma : 2 ≤ sigma) :
    Real.exp (-Real.pi*(sigma : ℝ)^2/2) ≤ 1/(2 : ℝ)^(2*sigma) := by
  have hs : (2 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hp : (0 : ℝ)<sigma := by linarith
  have hquad : 2*(sigma : ℝ) ≤ Real.pi*(sigma : ℝ)^2/2 := by
    nlinarith [Real.pi_gt_three,sq_nonneg ((sigma : ℝ)-2)]
  have he : (2 : ℝ)^(2*sigma) ≤ Real.exp ((2*sigma : ℕ) : ℝ) := by
    have heq : Real.exp ((2*sigma : ℕ) : ℝ)=(Real.exp 1)^(2*sigma) := by
      rw [←Real.exp_nat_mul]
      simp only [mul_one]
    rw [heq]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
  calc
    _ ≤ Real.exp (-((2*sigma : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    _ = 1/Real.exp ((2*sigma : ℕ) : ℝ) := by rw [Real.exp_neg,one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) he

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule67

/- Helper module Solutions.RegevBridgeWideGaussianScale. -/
section P2MDyadicModule68

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

end P2MDyadicModule68

/- Helper module Solutions.RegevBridgeWideGaussianSampler. -/
section P2MDyadicModule69

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic GaussianProjection GaussianProjection.CosetGeometry

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

noncomputable section

open scoped Classical

def sampleError (precision : ℕ) : ℝ :=
  2/(2 : ℝ)^precision+6*Real.exp (-Real.pi*((precision : ℝ)+2)^2/2)

theorem sampleError_le_eight_dyadic (precision : ℕ) : sampleError precision ≤ 8/(2 : ℝ)^precision := by
  have he := sigma_gaussian_exp_le (precision+2) (by omega)
  simp only [Nat.cast_add,Nat.cast_ofNat] at he
  have hp : (2 : ℝ)^precision ≤ 2^(2*(precision+2)) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hf := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<2^precision) hp
  unfold sampleError
  simp only [div_eq_mul_inv,one_mul] at he hf ⊢
  linarith

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule69

/- Helper module Solutions.RegevBridgeRationalGramSchmidt. -/
section P2MDyadicModule70

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

theorem realVec_zero {dimension : ℕ} : realVec (0 : QVector dimension)=0 := by ext index;simp [realVec]

theorem realVec_add {dimension : ℕ} (left right : QVector dimension) : realVec (left+right)=realVec left+realVec right := by
  ext index
  exact Rat.cast_add _ _

theorem realVec_sub {dimension : ℕ} (left right : QVector dimension) : realVec (left-right)=realVec left-realVec right := by
  ext index
  exact Rat.cast_sub _ _

theorem realVec_smul {dimension : ℕ} (scalar : ℚ) (vector : QVector dimension) :
    realVec (scalar • vector)=(scalar : ℝ) • realVec vector := by
  ext index
  exact Rat.cast_mul _ _

theorem realVec_list_sum {dimension : ℕ} (vectors : List (QVector dimension)) :
    realVec vectors.sum=(vectors.map realVec).sum := by
  induction vectors with
  | nil => exact realVec_zero
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,realVec_add,ih]

theorem innerQ_real {dimension : ℕ} (left right : QVector dimension) :
    (innerQ left right : ℝ)=inner ℝ (realVec left) (realVec right) := by
  unfold innerQ realVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

theorem cache_length {dimension count : ℕ} (vectors : Fin count → QVector dimension) (steps : ℕ) :
    (cache vectors steps).length=steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [cache,List.length_append,List.length_singleton,ih]

def squaredNorm {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : ℚ := innerQ (orthogonal vectors index) (orthogonal vectors index)

noncomputable section

theorem projection_real {dimension : ℕ} (orthogonal current : QVector dimension) :
    realVec (projection orthogonal current)=
      (inner ℝ (realVec orthogonal) (realVec current)/‖realVec orthogonal‖^2) • realVec orthogonal := by
  rw [projection,realVec_smul,Rat.cast_div,innerQ_real,innerQ_real,real_inner_self_eq_norm_sq]

theorem orthogonalStep_real {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) :
    realVec (orthogonalStep previous current)=realVec current-
      ((previous.map realVec).map (fun orthogonal => (inner ℝ orthogonal (realVec current)/‖orthogonal‖^2) • orthogonal)).sum := by
  rw [orthogonalStep,realVec_sub,realVec_list_sum]
  simp only [List.map_map,Function.comp_def,projection_real]

private theorem sum_Iio_fin {count : ℕ} {Value : Type*} [AddCommMonoid Value]
    (index : Fin count) (function : Fin count → Value) :
    (∑ previous ∈ Finset.Iio index,function previous)=
      ∑ previous : Fin index.val,function ⟨previous.val,previous.isLt.trans index.isLt⟩ := by
  classical
  refine Finset.sum_bij (fun previous membership =>
    (⟨previous.val,show previous < index from Finset.mem_Iio.mp membership⟩ : Fin index.val)) ?_ ?_ ?_ ?_
  · intro previous membership
    exact Finset.mem_univ _
  · intro first hfirst second hsecond hequal
    exact Fin.ext (congrArg (fun value : Fin index.val => value.val) hequal)
  · intro previous membership
    refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,Finset.mem_Iio.mpr (show (⟨previous.val,previous.isLt.trans index.isLt⟩ : Fin count) < index from previous.isLt),?_⟩
    rfl
  · intro previous membership
    congr 1

/-- Every materialized rational cache prefix is exactly the ordinary real
Gram--Schmidt prefix after the actual rational-to-real embedding. -/
theorem cache_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (cache vectors steps).map realVec=List.ofFn (fun index : Fin steps =>
      gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hsteps index)) := by
  classical
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps<count := by omega
    let index : Fin count := ⟨steps,hstep⟩
    rw [cache,List.map_append,List.map_singleton,ih hprevious,List.ofFn_succ_last]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext previous
      congr 1
    · apply congrArg (fun value : Space dimension => [value])
      change realVec (orthogonalStep (cache vectors steps) (if h : steps<count then vectors ⟨steps,h⟩ else 0))=
        gramSchmidt ℝ (fun position => realVec (vectors position)) index
      rw [dif_pos hstep,orthogonalStep_real,ih hprevious]
      simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
      have h := gramSchmidt_def'' ℝ (fun position => realVec (vectors position)) index
      rw [sum_Iio_fin] at h
      have hequal : (∑ previous : Fin steps,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous)‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))=
          ∑ previous : Fin index.val,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩)
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩ := rfl
      rw [hequal]
      exact sub_eq_iff_eq_add.mpr h

theorem orthogonal_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    realVec (orthogonal vectors index)=gramSchmidt ℝ (fun position => realVec (vectors position)) index := by
  have h := congrArg (fun values : List (Space dimension) => values.getD index.val (realVec (0 : QVector dimension)))
    (cache_real vectors count (le_refl count))
  rw [List.getD_map] at h
  simpa [orthogonal,index.isLt] using h

theorem squaredNorm_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    (squaredNorm vectors index : ℝ)=‖gramSchmidt ℝ (fun position => realVec (vectors position)) index‖^2 := by
  rw [squaredNorm,innerQ_real,orthogonal_real,real_inner_self_eq_norm_sq]

/-- Orthogonal projection only decreases the original column's square norm. -/
theorem gramSchmidt_norm_sq_le {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    ‖gramSchmidt ℝ vectors index‖^2 ≤ ‖vectors index‖^2 := by
  let orthogonal := gramSchmidt ℝ vectors
  have heq : inner ℝ (orthogonal index) (vectors index)=inner ℝ (orthogonal index) (orthogonal index) := by
    conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
    simp only [RCLike.ofReal_real_eq_id,id_eq]
    rw [inner_add_right]
    suffices inner ℝ (orthogonal index)
        (∑ previous ∈ Finset.Iio index,
          (inner ℝ (orthogonal previous) (vectors index)/‖orthogonal previous‖^2) • orthogonal previous)=0 by
      change inner ℝ (orthogonal index) (orthogonal index)+_=inner ℝ (orthogonal index) (orthogonal index)
      rw [this,add_zero]
    simp only [inner_sum,inner_smul_right]
    apply Finset.sum_eq_zero
    intro previous membership
    rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]
  have hnonneg := (real_inner_self_nonneg (x := vectors index-orthogonal index))
  rw [inner_sub_sub_self,real_inner_comm (orthogonal index) (vectors index),heq,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hnonneg
  change ‖orthogonal index‖^2 ≤ _
  linarith

theorem squaredNorm_le {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    squaredNorm vectors index ≤ innerQ (vectors index) (vectors index) := by
  have h := gramSchmidt_norm_sq_le (fun position => realVec (vectors position)) index
  rw [←squaredNorm_real,←real_inner_self_eq_norm_sq,←innerQ_real] at h
  exact_mod_cast h

end

noncomputable section

theorem inputVectors_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (column : Fin dimension) :
    realVec (inputVectors basis column)=IntegerBasis.realBasis basis hdet column := by
  rw [IntegerBasis.realBasis_apply]
  ext row
  simp [realVec,inputVectors]

theorem inputVectors_independent {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    LinearIndependent ℝ (fun position => realVec (inputVectors basis position)) := by
  simpa only [inputVectors_real basis hdet] using (IntegerBasis.realBasis basis hdet).linearIndependent

end

def entryMass {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) : ℚ :=
  ∑ row,∑ column,|(basis row column : ℚ)|

def initialWidth {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (base : ℚ) : ℚ := base*(1+entryMass basis)

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule70

/- Helper module Solutions.RegevBridgeRationalGramSchmidtGeometry. -/
section P2MDyadicModule71

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

/-- Exact rational upper-triangular change from original input columns to
its materialized orthogonal cache. -/
def upper {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) : ℚ :=
  innerQ (orthogonal vectors row) (vectors column)/squaredNorm vectors row

noncomputable section

theorem inner_gramSchmidt_original {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    inner ℝ (gramSchmidt ℝ vectors index) (vectors index)=‖gramSchmidt ℝ vectors index‖^2 := by
  conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [inner_add_right]
  suffices inner ℝ (gramSchmidt ℝ vectors index)
      (∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ vectors previous) (vectors index)/‖gramSchmidt ℝ vectors previous‖^2) •
          gramSchmidt ℝ vectors previous)=0 by
    rw [this,add_zero,real_inner_self_eq_norm_sq]
  simp only [inner_sum,inner_smul_right]
  apply Finset.sum_eq_zero
  intro previous membership
  rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]

theorem upper_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) :
    (upper vectors row column : ℝ)=
      inner ℝ (gramSchmidt ℝ (fun index => realVec (vectors index)) row) (realVec (vectors column))/
        ‖gramSchmidt ℝ (fun index => realVec (vectors index)) row‖^2 := by
  rw [upper,Rat.cast_div,innerQ_real,orthogonal_real,squaredNorm_real]

theorem upper_diagonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index))) (index : Fin count) :
    upper vectors index index=1 := by
  have hreal : (upper vectors index index : ℝ)=1 := by
    rw [upper_real,inner_gramSchmidt_original]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero index independent)))
  exact_mod_cast hreal

theorem upper_triangular {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) (before : column < row) :
    upper vectors row column=0 := by
  have hreal : (upper vectors row column : ℝ)=0 := by
    rw [upper_real,gramSchmidt_inv_triangular ℝ (fun index => realVec (vectors index)) before,zero_div]
  exact_mod_cast hreal

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule71

/- Helper module Solutions.RegevBridgeInitialGaussianBudget. -/
section P2MDyadicModule72

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT GaussianSource

open scoped BigOperators

noncomputable section

def initialThetaBudget (width : ℕ) : ℝ := 4/(2 : ℝ)^(4*width)

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule72

/- Helper module Solutions.RegevBridgeGramDeterminant. -/
section P2MDyadicModule73

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

noncomputable section

theorem prefixGram_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).map (fun value => (value : ℝ))=
      Matrix.gram ℝ (fun index => realVec (inputVectors basis (Fin.castLE hsteps index))) := by
  ext first second
  simp only [prefixGram,Matrix.map_apply,Matrix.gram_apply,realVec,inputVectors,PiLp.inner_apply,
    Real.inner_apply,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]

theorem prefixGram_det_ne_zero {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).det ≠ 0 := by
  have independent : LinearIndependent ℝ
      (fun index : Fin steps => realVec (inputVectors basis (Fin.castLE hsteps index))) :=
    (inputVectors_independent basis hdet).comp (Fin.castLE hsteps) (Fin.castLE_injective hsteps)
  have h := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr independent
  rw [←prefixGram_real,←Int.cast_det] at h
  exact_mod_cast h

/-- The subtraction made by Gram--Schmidt lies in the span of precisely
the original earlier columns, not an assumed short basis. -/
theorem gramSchmidt_correction_mem_prefix {dimension count : ℕ}
    (vectors : Fin count → QVector dimension) (index : Fin count) :
    realVec (vectors index)-realVec (orthogonal vectors index) ∈
      Submodule.span ℝ (Set.range (fun previous : Fin index.val =>
        realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))) := by
  classical
  let family := fun position => realVec (vectors position)
  have hset : Set.range (fun previous : Fin index.val =>
      realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))=family '' Set.Iio index := by
    ext point
    constructor
    · rintro ⟨previous,rfl⟩
      refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,?_,rfl⟩
      exact previous.isLt
    · rintro ⟨previous,hprevious,rfl⟩
      exact ⟨⟨previous.val,hprevious⟩,rfl⟩
  rw [hset,←span_gramSchmidt_Iio ℝ family index,orthogonal_real]
  have h := gramSchmidt_def'' ℝ family index
  have hcorrection : family index-gramSchmidt ℝ family index=
      ∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ family previous) (family index)/‖gramSchmidt ℝ family previous‖^2) •
          gramSchmidt ℝ family previous := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm,RCLike.ofReal_real_eq_id,id_eq] using h)
  change family index-gramSchmidt ℝ family index ∈ _
  rw [hcorrection]
  apply Submodule.sum_mem
  intro previous hprevious
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨previous,Finset.mem_Iio.mp hprevious,rfl⟩

end

def prefixPairing {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (previous : Fin index.val) : ℤ :=
  ∑ row,basis row ⟨previous.val,previous.isLt.trans index.isLt⟩*basis row index

def gramNumerator {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (row : Fin dimension) : ℤ :=
  (prefixGram basis index.val index.isLt.le).det*basis row index-
    ∑ previous : Fin index.val,
      Matrix.cramer (prefixGram basis index.val index.isLt.le) (prefixPairing basis index) previous*
        basis row ⟨previous.val,previous.isLt.trans index.isLt⟩

noncomputable section

/-- Multiplying the cached rational GS vector by the original integer
prefix-Gram determinant gives an explicitly integral Cramer numerator.
This is the denominator control needed for binary, rather than unit-cost,
complexity of the cached rational orthogonalization. -/
theorem gram_determinant_scales_orthogonal {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (index : Fin dimension) :
    ((prefixGram basis index.val index.isLt.le).det : ℚ) • orthogonal (inputVectors basis) index=
      fun row => (gramNumerator basis index row : ℚ) := by
  classical
  let previousColumn (previous : Fin index.val) : Fin dimension :=
    ⟨previous.val,previous.isLt.trans index.isLt⟩
  let family (previous : Fin index.val) := realVec (inputVectors basis (previousColumn previous))
  let gram := prefixGram basis index.val index.isLt.le
  let rhs := prefixPairing basis index
  let castGram := gram.map (fun value => (value : ℝ))
  obtain ⟨coefficients,hcoefficients⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (gramSchmidt_correction_mem_prefix (inputVectors basis) index)
  change (∑ previous,coefficients previous • family previous)=
    realVec (inputVectors basis index)-realVec (orthogonal (inputVectors basis) index) at hcoefficients
  have hinner (first second : Fin index.val) : inner ℝ (family first) (family second)=
      (gram first second : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,
      gram,prefixGram,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
    rfl
  have htarget (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (inputVectors basis index))=(rhs previous : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,prefixPairing,rhs,
      Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
  have horthogonal (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (orthogonal (inputVectors basis) index))=0 := by
    rw [orthogonal_real,real_inner_comm]
    exact gramSchmidt_inv_triangular ℝ (fun position => realVec (inputVectors basis position)) previous.isLt
  have hlinear : castGram.mulVec coefficients=fun previous => (rhs previous : ℝ) := by
    funext previous
    have h := congrArg (fun vector : Space dimension => inner ℝ (family previous) vector) hcoefficients
    simp only [inner_sum,inner_smul_right,inner_sub_right,horthogonal,sub_zero,htarget,hinner] at h
    simpa only [Matrix.mulVec,dotProduct,castGram,Matrix.map_apply,mul_comm] using h
  have hcramer : Matrix.cramer castGram (fun previous => (rhs previous : ℝ))=
      (gram.det : ℝ) • coefficients := by
    rw [←hlinear,Matrix.cramer_eq_adjugate_mulVec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
      Matrix.smul_mulVec,Matrix.one_mulVec,←Int.cast_det]
  have hcramerCast (previous : Fin index.val) :
      Matrix.cramer castGram (fun position => (rhs position : ℝ)) previous=
        (Matrix.cramer gram rhs previous : ℝ) := by
    rw [Matrix.cramer_apply,Matrix.cramer_apply]
    have hmatrix : castGram.updateCol previous (fun position => (rhs position : ℝ))=
        (gram.updateCol previous rhs).map (fun value => (value : ℝ)) := by
      ext first second
      simp only [Matrix.updateCol_apply,Matrix.map_apply,castGram]
      split_ifs <;> rfl
    rw [hmatrix,←Int.cast_det]
  have hscaled : (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=
      ∑ previous,(Matrix.cramer gram rhs previous : ℝ) • family previous := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro previous _
    rw [smul_smul]
    have h := congrArg (fun values : Fin index.val → ℝ => values previous) hcramer
    simp only [Pi.smul_apply,smul_eq_mul,hcramerCast] at h
    rw [←h]
  have h := congrArg (fun vector : Space dimension => (gram.det : ℝ) • vector) hcoefficients
  change (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=_ at h
  rw [hscaled] at h
  ext row
  have hrow := congrArg (fun vector : Space dimension => vector row) h
  simp only [family,previousColumn,realVec,inputVectors,WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_sub,Finset.sum_apply,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Rat.cast_intCast] at hrow
  change (gram.det : ℚ)*orthogonal (inputVectors basis) index row=(gramNumerator basis index row : ℚ)
  apply Rat.cast_injective (α:=ℝ)
  simp only [gramNumerator,Rat.cast_sub,Rat.cast_mul,Rat.cast_sum,Rat.cast_intCast,Int.cast_sub,Int.cast_mul,Int.cast_sum]
  change (gram.det : ℝ)*(orthogonal (inputVectors basis) index row : ℝ)=_
  dsimp [gram,rhs] at hrow ⊢
  linarith

theorem prefixGram_entry_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) (first second : Fin steps) :
    |prefixGram basis steps hsteps first second| ≤ (dimension : ℤ)*bound^2 := by
  unfold prefixGram
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ row,|basis row (Fin.castLE hsteps first)*basis row (Fin.castLE hsteps second)|) ≤
        ∑ _row : Fin dimension,bound^2 := by
      apply Finset.sum_le_sum
      intro row _
      rw [abs_mul,pow_two]
      exact mul_le_mul (hentries row _) (hentries row _) (abs_nonneg _) hbound
    _ = _ := by simp

/-- Every prefix determinant has a bound whose logarithm is polynomial
in the input dimension and the logarithmic entry bound. -/
theorem prefixGram_det_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) :
    |(prefixGram basis steps hsteps).det| ≤ (steps.factorial : ℤ)*((dimension : ℤ)*bound^2)^steps := by
  have h := Matrix.det_le (abv:=AbsoluteValue.abs)
    (prefixGram_entry_bound basis steps hsteps bound hbound hentries)
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using h

/-- A uniform polynomial exponent bounds every integer prefix Gram
normalizer, directly from an entry bit bound of the original input. -/
theorem prefixGram_det_binary_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height) :
    |(prefixGram basis steps hsteps).det| ≤ (2 : ℤ)^((2*dimension+2*height)*dimension) := by
  have hdimension : (dimension : ℤ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hstep : (steps : ℤ) ≤ 2^dimension := (by exact_mod_cast hsteps : (steps : ℤ) ≤ dimension).trans hdimension
  have hfactorial : (steps.factorial : ℤ) ≤ 2^(dimension*steps) := by
    calc
      _ ≤ (steps : ℤ)^steps := by exact_mod_cast Nat.factorial_le_pow steps
      _ ≤ ((2 : ℤ)^dimension)^steps := pow_le_pow_left₀ (Nat.cast_nonneg steps) hstep _
      _ = _ := by rw [←pow_mul]
  have hentryGram : (dimension : ℤ)*((2 : ℤ)^height)^2 ≤ 2^(dimension+2*height) := by
    calc
      _ ≤ (2 : ℤ)^dimension*((2 : ℤ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimension (sq_nonneg _)
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;omega
  calc
    _ ≤ (steps.factorial : ℤ)*((dimension : ℤ)*((2 : ℤ)^height)^2)^steps :=
      prefixGram_det_bound basis steps hsteps ((2 : ℤ)^height) (by positivity) hentries
    _ ≤ (2 : ℤ)^(dimension*steps)*(2^(dimension+2*height))^steps :=
      mul_le_mul hfactorial (pow_le_pow_left₀ (by positivity) hentryGram _)
        (by positivity) (by positivity)
    _ = 2^((2*dimension+2*height)*steps) := by
      rw [←pow_mul,←pow_add]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left (2*dimension+2*height) hsteps)

/-- Every cached rational coordinate has a small absolute magnitude even
when canonical numerators and denominators require separate control. -/
theorem orthogonal_coordinate_abs_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    |orthogonal (inputVectors basis) index row| ≤ (2 : ℚ)^(dimension+height) := by
  have hcoordinate : orthogonal (inputVectors basis) index row^2 ≤
      squaredNorm (inputVectors basis) index := by
    unfold squaredNorm innerQ
    simp only [←sq]
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ row)
  have hcolumn : innerQ (inputVectors basis index) (inputVectors basis index) ≤
      (dimension : ℚ)*((2 : ℚ)^height)^2 := by
    unfold innerQ inputVectors
    simp only [←sq]
    calc
      _ ≤ ∑ _ : Fin dimension,((2 : ℚ)^height)^2 := by
        apply Finset.sum_le_sum
        intro position _
        have hentry : |(basis position index : ℚ)| ≤ (2 : ℚ)^height := by
          exact_mod_cast hentries position index
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hentry
      _ = _ := by simp
  have hdimension : (dimension : ℚ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hpower : (1 : ℚ) ≤ 2^dimension := one_le_pow₀ (by norm_num)
  have hdimensionSquare : (dimension : ℚ) ≤ ((2 : ℚ)^dimension)^2 := by nlinarith
  have hsquare : orthogonal (inputVectors basis) index row^2 ≤ ((2 : ℚ)^(dimension+height))^2 := by
    calc
      _ ≤ squaredNorm (inputVectors basis) index := hcoordinate
      _ ≤ innerQ (inputVectors basis index) (inputVectors basis index) := squaredNorm_le _ index
      _ ≤ (dimension : ℚ)*((2 : ℚ)^height)^2 := hcolumn
      _ ≤ ((2 : ℚ)^dimension)^2*((2 : ℚ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimensionSquare (sq_nonneg _)
      _ = _ := by rw [pow_add,mul_pow]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsquare)

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule73

/- Helper module Solutions.RegevBridgeRationalDenominator. -/
section P2MDyadicModule74

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RationalDenominator

/-- Any nonzero integral clearing denominator is divisible by the canonical
positive denominator of the rational number. -/
theorem den_dvd {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    (r.den : ℤ) ∣ D := by
  have hDQ : (D : ℚ)≠0 := by exact_mod_cast hD
  have hr : r=(N : ℚ)/(D : ℚ) := (eq_div_iff hDQ).mpr (by simpa only [mul_comm] using h)
  rw [hr]
  simpa only [Rat.divInt_eq_div] using Rat.den_dvd N D

/-- Canonical denominators never exceed any nonzero integral clearing denominator. -/
theorem den_le_natAbs {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    r.den≤D.natAbs := by
  have hd := den_dvd hD h
  have hn : r.den ∣ D.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hn

/-- Clearing-denominator bounds control the canonical numerator as well. -/
theorem num_bound_rat {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    |(r.num : ℚ)| ≤ |(D : ℚ)| * |r| := by
  have hd : (r.den : ℚ) ≤ |(D : ℚ)| := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (Nat.cast_le (α := ℚ)).mpr (den_le_natAbs hD h)
  calc
    |(r.num : ℚ)|=|(r.den : ℚ)*r| := congrArg abs (Rat.den_mul_eq_num r).symm
    _ = (r.den : ℚ)*|r| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (abs_nonneg _)

/-- A magnitude bound and clearing-denominator bound yield a natural bound
on both stored rational integer fields. -/
theorem fields_bound {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N)
    (M : ℕ) (hM : |r|≤M) : r.den≤D.natAbs ∧ r.num.natAbs≤D.natAbs*M := by
  refine ⟨den_le_natAbs hD h,?_⟩
  have hn := (num_bound_rat hD h).trans (mul_le_mul_of_nonneg_left hM (abs_nonneg _))
  have hn' : (r.num.natAbs : ℚ) ≤ ((D.natAbs*M : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul,Nat.cast_natAbs,Int.cast_abs] using hn
  exact_mod_cast hn'

end InfoLossLAR.WorstCase.RationalDenominator

end P2MDyadicModule74

/- Helper module Solutions.RegevBridgeRationalGramSchmidtHeight. -/
section P2MDyadicModule75

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT.RationalNumerics

open scoped BigOperators

/-- A fixed polynomial in the dimension and input entry height controls
every reduced cached rational coordinate. -/
def coordinateHeight (dimension height : ℕ) : ℕ :=
  (2*dimension+2*height)*dimension+dimension+height

noncomputable section

/-- Canonical numerator and denominator sizes are polynomial, using the
actual integer Gram determinant rather than an arithmetic-operation count. -/
theorem orthogonal_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    HeightBound (orthogonal (inputVectors basis) index row) (coordinateHeight dimension height) := by
  have hnonzero := prefixGram_det_ne_zero basis hdet index.val index.isLt.le
  have hvector := gram_determinant_scales_orthogonal basis index
  have hcoordinate := congrArg (fun vector : QVector dimension => vector row) hvector
  simp only [Pi.smul_apply,smul_eq_mul] at hcoordinate
  have habs := orthogonal_coordinate_abs_bound basis height hentries index row
  have hM : |orthogonal (inputVectors basis) index row| ≤ ((2^(dimension+height) : ℕ) : ℚ) := by
    exact_mod_cast habs
  obtain ⟨hden,hnum⟩ := RationalDenominator.fields_bound hnonzero hcoordinate (2^(dimension+height)) hM
  have hD : (prefixGram basis index.val index.isLt.le).det.natAbs ≤
      2^((2*dimension+2*height)*dimension) := by
    have h := prefixGram_det_binary_bound basis index.val index.isLt.le height hentries
    have hcast : (((prefixGram basis index.val index.isLt.le).det.natAbs : ℕ) : ℤ) ≤
        (2 : ℤ)^((2*dimension+2*height)*dimension) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast hcast
  constructor
  · apply hnum.trans
    apply (Nat.mul_le_mul_right (2^(dimension+height)) hD).trans_eq
    rw [←pow_add]
    congr 1
    unfold coordinateHeight
    omega
  · apply (hden.trans hD).trans
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by unfold coordinateHeight;omega)

theorem realVec_injective {dimension : ℕ} : Function.Injective (realVec (dimension:=dimension)) := by
  intro first second hequal
  funext index
  apply Rat.cast_injective (α:=ℝ)
  exact congrArg (fun vector : Space dimension => vector index) hequal

/-- Every materialized prefix consists of the very same final cached
orthogonal vectors, so all prefix state encodings share one height bound. -/
theorem cache_prefix_eq {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    cache vectors steps=List.ofFn (fun index : Fin steps => orthogonal vectors (Fin.castLE hsteps index)) := by
  apply (List.map_injective_iff.mpr realVec_injective)
  rw [cache_real vectors steps hsteps,List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact (orthogonal_real vectors _).symm

theorem cache_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) (vector : QVector dimension)
    (membership : vector ∈ cache (inputVectors basis) steps) (row : Fin dimension) :
    HeightBound (vector row) (coordinateHeight dimension height) := by
  rw [cache_prefix_eq _ steps hsteps] at membership
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp membership
  exact orthogonal_coordinate_height basis hdet height hentries _ row

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule75

/- Helper module Solutions.RegevBridgeRationalGramSchmidtNative. -/
section P2MDyadicModule76

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

/-- Total native rational list dot product; malformed lengths truncate. -/
def dot (input : List ℚ × List ℚ) : ℚ :=
  ((input.1.zip input.2).map (fun pair => pair.1*pair.2)).sum

@[fun_prop] theorem dot_poly : Poly dot := by unfold dot;fun_prop

def projectionEntry (input : (List ℚ × List ℚ) × ℕ) : ℚ :=
  dot (input.1.1,input.1.2)/dot (input.1.1,input.1.1)*input.1.1[input.2]?.getD 0

@[fun_prop] theorem projectionEntry_poly : Poly projectionEntry := by unfold projectionEntry;fun_prop

def rowValue (input : (List (List ℚ) × List ℚ) × ℕ) : ℚ :=
  input.1.2[input.2]?.getD 0-
    (input.1.1.map (fun previous => projectionEntry ((previous,input.1.2),input.2))).sum

@[fun_prop] theorem rowValue_poly : Poly rowValue := by unfold rowValue;fun_prop

/-- One native materialized Gram--Schmidt step uses its original current
column throughout and stores the complete new rational vector. -/
def orthogonalStep (input : List (List ℚ) × List ℚ) : List ℚ :=
  (List.range input.2.length).map (fun row => rowValue (input,row))

@[fun_prop] theorem orthogonalStep_poly : Poly orthogonalStep := by
  have hindices : Poly (fun input : List (List ℚ) × List ℚ => List.range input.2.length) :=
    Poly.comp (f:=fun values : List ℚ => List.range values.length) (g:=Prod.snd) Poly.list_indices Poly.snd
  unfold orthogonalStep
  exact Poly.list_map rowValue_poly hindices

@[fun_prop] theorem rationalTicks_poly : Poly rationalTicks := by unfold rationalTicks;fun_prop

def vectorTicks (vector : List ℚ) : List Unit :=
  vector.flatMap (fun value => rationalTicks value++rationalTicks value++[()])

@[fun_prop] theorem vectorTicks_poly : Poly vectorTicks := by unfold vectorTicks;fun_prop

def matrixTicks (matrix : List (List ℚ)) : List Unit :=
  matrix.flatMap (fun vector => vectorTicks vector++vectorTicks vector++[()])

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

/-- Every intermediate cache is size-guarded, giving an unconditional
polynomial-time loop on arbitrary encodings. Valid matrix correctness will
be discharged using the independently proved integer-Gram height bound. -/
def cacheStep (state : List Unit × List (List ℚ)) (current : List ℚ) : List Unit × List (List ℚ) :=
  let next := state.2++[orthogonalStep (state.2,current)]
  (state.1,if (matrixTicks next).length ≤ state.1.length then next else [])

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

/-- Actual guarded list cache program. The guard's complete runtime bound
holds for every encoded input, including malformed or singular matrices. -/
def cached (input : List (List ℚ) × List Unit) : List (List ℚ) :=
  (input.1.foldl cacheStep (input.2,[])).2

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

theorem vector_list_sum_apply {dimension : ℕ} (vectors : List (QVector dimension)) (index : Fin dimension) :
    vectors.sum index=(vectors.map (fun vector => vector index)).sum := by
  induction vectors with
  | nil => rfl
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,Pi.add_apply,ih]

theorem orthogonalStep_ofFn {dimension : ℕ} (previous : List (QVector dimension))
    (current : QVector dimension) :
    orthogonalStep (previous.map List.ofFn,List.ofFn current)=
      List.ofFn (RationalGramSchmidt.orthogonalStep previous current) := by
  apply List.ext_getElem
  · simp only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hrow : row < dimension := by
      simpa only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [orthogonalStep,List.length_ofFn,List.getElem_map,List.getElem_range,rowValue,
      List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some,List.map_map,Function.comp_def,
      projectionEntry,dot_ofFn,List.getElem_ofFn]
    simp only [RationalGramSchmidt.orthogonalStep,Pi.sub_apply,vector_list_sum_apply,List.map_map,
      Function.comp_def,projection,Pi.smul_apply,smul_eq_mul]

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule76

/- Helper module Solutions.RegevBridgeRationalGramSchmidtCacheBudget. -/
section P2MDyadicModule77

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

noncomputable section

theorem encoded_list_length_bound {Value : Type} (encoding : Value → List Bool)
    (values : List Value) (bound : ℕ) (hbound : ∀ value ∈ values,(encoding value).length ≤ bound) :
    (encodeList encoding values).length ≤ values.length*(2*bound+1) := by
  induction values with
  | nil => simp only [EncodedList.nil,List.length_nil,zero_mul,le_refl]
  | cons head tail ih =>
    rw [EncodedList.cons_length,List.length_cons]
    have hhead := hbound head (by simp)
    have htail := ih (fun value membership => hbound value (by simp [membership]))
    nlinarith

theorem rational_encoding_height {value : ℚ} {height : ℕ} (hvalue : HeightBound value height) :
    (Ratio.encode value).length ≤ 3*height+10 := by
  apply Ratio.length_height
  constructor
  · have h := (Nat.cast_le (α:=ℤ)).mpr hvalue.1
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h
  · exact_mod_cast hvalue.2

theorem vector_encoding_height {dimension : ℕ} (vector : QVector dimension) (height : ℕ)
    (hvector : ∀ row,HeightBound (vector row) height) :
    (encodeList Ratio.encode (List.ofFn vector)).length ≤ dimension*(6*height+21) := by
  have h := encoded_list_length_bound Ratio.encode (List.ofFn vector) (3*height+10) (by
    intro value membership
    obtain ⟨row,rfl⟩ := List.mem_ofFn.mp membership
    exact rational_encoding_height (hvector row))
  simpa only [List.length_ofFn,show 2*(3*height+10)+1=6*height+21 by omega] using h

def cacheEncodingBound (dimension height : ℕ) : ℕ :=
  dimension*(2*dimension*(6*coordinateHeight dimension height+21)+1)

/-- The original determinant-derived height bound controls every complete
native cache-prefix encoding by one public polynomial. -/
theorem cache_encoding_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (encodeList (encodeList Ratio.encode) ((cache (inputVectors basis) steps).map List.ofFn)).length ≤
      cacheEncodingBound dimension height := by
  have h := encoded_list_length_bound (encodeList Ratio.encode)
    ((cache (inputVectors basis) steps).map List.ofFn) (dimension*(6*coordinateHeight dimension height+21)) (by
      intro vector membership
      obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp membership
      exact vector_encoding_height source _ (cache_coordinate_height basis hdet height hentries steps hsteps source hsource))
  rw [List.length_map,cache_length] at h
  apply h.trans
  unfold cacheEncodingBound
  calc
    steps*(2*(dimension*(6*coordinateHeight dimension height+21))+1) ≤
        dimension*(2*(dimension*(6*coordinateHeight dimension height+21))+1) := Nat.mul_le_mul_right _ hsteps
    _ = _ := by ring

/-- Prefix refinement is proved for the actual guarded list loop. Its
encoding bound is a local arithmetic invariant, discharged below from the
original integer matrix's determinant-derived size bounds. -/
theorem cacheFold_ofFn {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (ticks : List Unit)
    (hbudget : ∀ steps,steps ≤ count →
      (encodeList (encodeList Ratio.encode) ((cache vectors steps).map List.ofFn)).length ≤ ticks.length)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hsteps index)))).foldl cacheStep (ticks,[])=
      (ticks,(cache vectors steps).map List.ofFn) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps < count := by omega
    rw [List.ofFn_succ_last,List.foldl_append]
    change List.foldl cacheStep
      ((List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hprevious index)))).foldl cacheStep (ticks,[]))
      [List.ofFn (vectors ⟨steps,hstep⟩)] = _
    rw [ih hprevious,List.foldl_cons,List.foldl_nil]
    have hnext : (cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))]=
        (cache vectors (steps+1)).map List.ofFn := by
      rw [orthogonalStep_ofFn,cache,List.map_append,List.map_singleton,dif_pos hstep]
    have hguard : (matrixTicks ((cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))])).length ≤ ticks.length := by
      rw [hnext,matrixTicks_length]
      exact hbudget (steps+1) hsteps
    simp only [cacheStep,hguard,if_true]
    exact congrArg (fun matrix => (ticks,matrix)) hnext

/-- For every nonsingular input basis, the actual native cache agrees
exactly with rational Gram--Schmidt once supplied the public polynomial
encoding budget. No oracle or assumed GS algorithm appears. -/
theorem cached_integer_basis {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (ticks : List Unit) (hticks : cacheEncodingBound dimension height ≤ ticks.length) :
    cached (List.ofFn (fun index => List.ofFn (inputVectors basis index)),ticks)=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  have h := cacheFold_ofFn (inputVectors basis) ticks (fun steps hsteps =>
    (cache_encoding_bound basis hdet height hentries steps hsteps).trans hticks) dimension (le_refl dimension)
  change (List.ofFn (fun index : Fin dimension => List.ofFn (inputVectors basis index))).foldl cacheStep (ticks,[])=_ at h
  exact congrArg Prod.snd h

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule77

/- Helper module Solutions.RegevBridgeRationalGramSchmidtInput. -/
section P2MDyadicModule78

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

@[fun_prop] theorem integerTicks_poly : Poly integerTicks := by unfold integerTicks;fun_prop

@[fun_prop] theorem integerVectorTicks_poly : Poly integerVectorTicks := by unfold integerVectorTicks;fun_prop

@[fun_prop] theorem integerMatrixTicks_poly : Poly integerMatrixTicks := by unfold integerMatrixTicks;fun_prop

/-- The guard budget is generated in unary polynomial size from the
actual binary input length, not from an exponentially large entry value. -/
def inputBudget (input : List (List ℤ)) : List Unit :=
  let slots := integerMatrixTicks input++[()]
  slots.flatMap (fun _ => slots.flatMap (fun _ => slots.flatMap
    (fun _ => slots.flatMap (fun _ => List.replicate 128 ()))))

@[fun_prop] theorem inputBudget_poly : Poly inputBudget := by unfold inputBudget;fun_prop

def rationalColumn (column : List ℤ) : List ℚ := column.map (fun value : ℤ => (value : ℚ))

@[fun_prop] theorem rationalColumn_poly : Poly rationalColumn := by
  unfold rationalColumn
  exact Poly.list_map (show Poly (fun input : List ℤ × ℤ => (input.2 : ℚ)) by fun_prop) Poly.identity

def rationalColumns (input : List (List ℤ)) : List (List ℚ) := input.map rationalColumn

@[fun_prop] theorem rationalColumns_poly : Poly rationalColumns := by
  unfold rationalColumns
  exact Poly.list_map (Poly.comp rationalColumn_poly Poly.snd) Poly.identity

/-- Complete unconditional native cached orthogonalization of original
integer input columns, with all guards and loop sizes computed publicly. -/
def inputCache (input : List (List ℤ)) : List (List ℚ) := cached (rationalColumns input,inputBudget input)

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

theorem inputBudget_length (matrix : List (List ℤ)) :
    (inputBudget matrix).length=128*((integerMatrixTicks matrix).length+1)^4 := by
  simp only [inputBudget,List.length_flatMap,List.map_const',List.sum_replicate,List.length_replicate,
    List.length_append,List.length_singleton,nsmul_eq_mul,Nat.cast_id]
  ring

def transposeColumn (input : List (List ℤ) × ℕ) : List ℤ :=
  input.1.map (fun row => row[input.2]?.getD 0)

@[fun_prop] theorem transposeColumn_poly : Poly transposeColumn := by unfold transposeColumn;fun_prop

def transpose (input : List (List ℤ)) : List (List ℤ) :=
  (List.range input.length).map (fun column => transposeColumn (input,column))

@[fun_prop] theorem transpose_poly : Poly transpose := by
  unfold transpose
  exact Poly.list_map transposeColumn_poly Poly.list_indices

/-- Actual row-encoded matrix input is transposed by a native program
before the cached column orthogonalization. -/
def basisCache (input : List (List ℤ)) : List (List ℚ) := inputCache (transpose input)

@[fun_prop] theorem basisCache_poly : Poly basisCache := by unfold basisCache;fun_prop

noncomputable section

/-- Coarse fixed polynomial suitable for unconditional guarded runtime. -/
theorem cacheEncodingBound_coarse (dimension height length : ℕ)
    (hdimension : dimension ≤ length) (hheight : height ≤ length) :
    cacheEncodingBound dimension height ≤ 128*(length+1)^4 := by
  have hlinear : length ≤ (length+1)^2 := by nlinarith
  have hcross : height*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hheight hdimension
      _ ≤ _ := by nlinarith
  have hsquare : dimension*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hdimension hdimension
      _ ≤ _ := by nlinarith
  have hcache : coordinateHeight dimension height ≤ 6*(length+1)^2 := by
    unfold coordinateHeight
    nlinarith
  unfold cacheEncodingBound
  calc
    _ ≤ (length+1)*(2*(length+1)*(6*(6*(length+1)^2)+21)+1) := by gcongr <;> omega
    _ ≤ _ := by
      have hpowerOne := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 1 ≤ 4 by omega)
      have hpowerTwo := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 2 ≤ 4 by omega)
      simp only [pow_one] at hpowerOne
      nlinarith

theorem inputColumns_dimension {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    dimension ≤ (integerMatrixTicks (inputColumns basis)).length := by
  rw [integerMatrixTicks_length]
  have h := EncodedList.length_le (encodeList Signed.encode) (inputColumns basis)
  simpa only [inputColumns,List.length_ofFn] using h

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

theorem rationalColumns_input {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    rationalColumns (inputColumns basis)=List.ofFn (fun index => List.ofFn (inputVectors basis index)) := by
  simp only [rationalColumns,rationalColumn,inputColumns,List.map_ofFn,Function.comp_def]
  rfl

/-- The fully generated binary-input native cache exactly returns the
original nonsingular integer basis's rational orthogonalization. Every
size guard is discharged from the actual input encoding itself. -/
theorem inputCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    inputCache (inputColumns basis)=(cache (inputVectors basis) dimension).map List.ofFn := by
  unfold inputCache
  rw [rationalColumns_input]
  apply cached_integer_basis basis hdet (integerMatrixTicks (inputColumns basis)).length
    (inputColumns_entry_height basis)
  rw [inputBudget_length]
  exact cacheEncodingBound_coarse dimension _ _ (inputColumns_dimension basis) le_rfl

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

/-- End-to-end exact native GS caching for the target's original row-major
integer matrix convention, with an unconditional polynomial-time program. -/
theorem basisCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    basisCache (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  rw [basisCache,transpose_input_rows,inputCache_correct basis hdet]

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule78

/- Helper module Solutions.RegevBridgeInitialGaussianParameters. -/
section P2MDyadicModule79

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

def rowMass (row : List ℤ) : ℚ := (row.map (fun value => (value.natAbs : ℚ))).sum

@[fun_prop] theorem rowMass_poly : Poly rowMass := by unfold rowMass;fun_prop

def entryMass (input : List (List ℤ)) : ℚ := (input.map rowMass).sum

@[fun_prop] theorem entryMass_poly : Poly entryMass := by unfold entryMass;fun_prop

def initialWidth (input : List (List ℤ) × ℕ) : ℚ := (input.2 : ℚ)*(1+entryMass input.1)

@[fun_prop] theorem initialWidth_poly : Poly initialWidth := by unfold initialWidth;fun_prop

noncomputable section

theorem entryMass_input {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    entryMass (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=
      RationalGramSchmidt.entryMass basis := by
  simp only [entryMass,rowMass,List.map_ofFn,Function.comp_def,List.sum_ofFn,RationalGramSchmidt.entryMass]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  simp only [Nat.cast_natAbs,Int.cast_abs]

theorem initialWidth_input {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (width : ℕ) :
    initialWidth (List.ofFn (fun row => List.ofFn (fun column => basis row column)),width)=
      RationalGramSchmidt.initialWidth basis (width : ℚ) := by
  rw [initialWidth,entryMass_input]
  rfl

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule79

/- Helper module Solutions.RegevBridgeLatticeInterfaces. -/
section P2MDyadicModule80

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- The fixed modulus is at least the explicit threshold used to choose it. -/
theorem famq_lower_bound (lam : ℕ) : 2 ^ 16 * famL lam ^ 64 ≤ famq lam :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64))).1

/-- The Gaussian width is strictly below the family's modulus at every parameter. -/
theorem famσ_lt_famq (lam : ℕ) : famσ lam < famq lam := by
  have hspec := famq_lower_bound lam
  have hL : 1 ≤ famL lam := by unfold famL; omega
  have hpow : famL lam ≤ famL lam ^ 64 := le_self_pow₀ hL (by norm_num)
  have hpos : 0 < famL lam ^ 64 := by positivity
  unfold famσ
  omega

end InfoLossLAR.WorstCase

end P2MDyadicModule80

/- Helper module Solutions.RegevBridgeGaussianVerification. -/
section P2MDyadicModule81

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open scoped BigOperators Classical

open Filter

open scoped Topology

/-- The local signed negligible predicate implies the platform predicate for a nonnegative error. -/
theorem platform_negligible_of_native {error : ℕ → ℝ}
    (h : AFT.Negligible error) (hpos : ∀ n, 0 ≤ error n) : Negligible error := by
  refine ⟨hpos, ?_⟩
  intro c hc
  let order : ℕ := ⌈c⌉₊
  have horder : c ≤ (order : ℝ) := Nat.le_ceil c
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 ((h order).and (eventually_ge_atTop 1))
  refine ⟨cutoff, ?_⟩
  intro n hn
  obtain ⟨he, hne⟩ := hcutoff n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hne
  calc
    error n ≤ 1 / (n : ℝ) ^ order := (le_abs_self _).trans he
    _ = (n : ℝ) ^ (-(order : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
    _ ≤ (n : ℝ) ^ (-c) := Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg horder)

/-- A fixed geometric failure rate is negligible in the exact platform sense. -/
theorem verification_geometric_negligible : Negligible (fun n => (3 / 4 : ℝ) ^ n) := by
  have hl : 0 < -Real.log (3 / 4 : ℝ) := neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  have h := AFT.negligible_polynomial_stretched_exponential 1 0 1 (-Real.log (3 / 4 : ℝ))
    (by norm_num) (by norm_num) hl
  apply platform_negligible_of_native ?_ (fun n => by positivity)
  convert h using 1
  funext n
  simp only [pow_zero, one_mul, Real.rpow_one, neg_neg]
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 4)]

end InfoLossLAR.WorstCase

end P2MDyadicModule81

/- Helper module Solutions.RegevBridgeNativeWordLayout. -/
section P2MDyadicModule82

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

def width (n : ℕ) : ℕ := n+((compiled P n).ops.length+1)

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

end P2MDyadicModule82

/- Helper module Solutions.RegevBridgeNativeWordCoherentCompute. -/
section P2MDyadicModule83

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

end P2MDyadicModule83

/- Helper module Solutions.RegevBridgeNativeWordLift. -/
section P2MDyadicModule84

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open scoped BigOperators

/-- Append arbitrary data/reference wires; original instruction addresses
remain fixed and every CNOT control/target remains distinct. -/
def extendInstr (k : ℕ) {W : ℕ} : Instr W → Instr (W+k)
  | .h i => .h (i.castAdd k)
  | .s i => .s (i.castAdd k)
  | .t i => .t (i.castAdd k)
  | .x i => .x (i.castAdd k)
  | .cnot i j h => .cnot (i.castAdd k) (j.castAdd k) (by intro he;exact h (Fin.castAdd_inj.mp he))

def extendCircuit (k : ℕ) {W : ℕ} (gates : Layered W) : Layered (W+k) :=
  gates.map (List.map (extendInstr k))

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

def gate (controls : Fin k → Fin W) (i : Fin k) : ReversibleGate (W+k) :=
  .controlled ((controls i).castAdd k) (Fin.natAdd W i) (by
    intro h;have hv:=congrArg Fin.val h;dsimp at hv;have hi:=(controls i).isLt;omega)

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

/-- Actual finite CNOTs copy all requested output bits into an arbitrary
separate register by XOR. Repeated controls are permitted; targets are distinct. -/
def circuit (controls : Fin k → Fin W) : Layered (W+k) :=
  compileReversible ((List.finRange k).map (gate controls))

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

/- Helper module Solutions.RegevBridgeNativeWordSerializer. -/
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

def inputAt (n : ℕ) (word : Str) (v : QState (capacity P n)) : QState (width P n+capacity P n) :=
  assembleMap _ _ (tensor v (initialWork P n word))

def maskedAt (n : ℕ) (word : Str) (data : Bits (capacity P n)) : Bits (capacity P n) :=
  fun i => xor (data i) (wordExtension (f word) i.val)

theorem fullCircuit_exact_at (n : ℕ) (word : Str) (hlen : word.length=n) (v : QState (capacity P n)) :
    runLayered (fullCircuit P n) (inputAt P n word v)=
      inputAt P n word (fun data => v (maskedAt P n word data)) := by
  subst n
  exact fullCircuit_exact P word v

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

/- Helper module Solutions.RegevBridgeCircuitRelocationWords. -/
section P2MDyadicModule89

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

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule89

/- Helper module Solutions.RegevBridgeNativePaddedWords. -/
section P2MDyadicModule90

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativePaddedWords

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.LARPlatformEncoding (readBinaryList_append_mapped encL_length_pos serializeBinaryWords_map)

open Integration9_9.TM2PlatformSerialization

def current (x : List Unit×Str) : Str := (x.2++x.1.map (fun _ => false)).take x.1.length

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

end P2MDyadicModule90

/- Helper module PoolInput. -/
section P2MDyadicModule91

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ShortProbePlan

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARPlatformEncoding (readS readS_append)

def parts (a : Str) := ((readS a).2,(readS (readS a).1).2)

@[fun_prop] theorem parts_poly : Poly parts := by unfold parts; fun_prop

@[simp] theorem parts_pair (a b : Str) : parts (encPair a b) = (a,b) := by
  have h : readS (encS b) = ([],b) := by simpa using readS_append b []
  simp [parts,encPair,readS_append,h]

end InfoLossLAR.WorstCase.ShortProbePlan

end P2MDyadicModule91

/- Helper module OracleTable. -/
section P2MDyadicModule92

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.OracleTable

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2PlatformSerialization Integration9_9.TM2StockLists QMCNumericRuntime

open Integration9_9.LARPlatformEncoding (readS readS_append serializeBinaryWords serializeBinaryWords_map readBinaryList_append_mapped encB_length_pos)

noncomputable section

def pack (xs : List (Str×Str)) : Str := serializeBinaryWords (xs.map fun t => encS t.2)

@[fun_prop] theorem pack_poly : Poly pack := by unfold pack;fun_prop

theorem unpack_exact (xs : List (Str×Str)) (tail : Str) :
    unpack (pack xs++tail)=(tail,xs.map Prod.snd) := by
  have h : pack xs=encL encS (xs.map Prod.snd) := by
    rw [←serializeBinaryWords_map];simp only [pack,List.map_map, Function.comp_def]
  rw [h]
  have hpos (s : Str) : 0<(encS s).length := by unfold encS;exact (encB_length_pos s.length).trans_le (by simp)
  simpa [unpack] using readBinaryList_append_mapped readS encS id hpos readS_append (xs.map Prod.snd) tail

def advice (g : Str→Str) (Q : Polynomial ℕ) (w : Str) := pack (generatedBundleDescriptions g Q w)

theorem advice_stock (g : Str→Str) (hg : PolyTimeComputable g) (Q : Polynomial ℕ) : PolyTimeComputable (advice g Q) := by
  obtain ⟨table⟩ := generatedBundleDescriptions_stock g hg Q
  obtain ⟨encoded⟩ := TM2Composition.comp table pack_poly.program.stock
  obtain ⟨raw⟩ := TM2Composition.comp encoded BooleanLists.unpackProgram.stock
  exact ⟨congrProgram raw _ (fun _ => rfl)⟩

theorem advice_lookup (F : MFamily) (g : Str→Str) (hc : ∀ n,g (unary n)=F.encAt n) (Q : Polynomial ℕ)
    (w tail : Str) (l : ℕ) (hl : l≤Q.eval w.length) :
    lookup (advice g Q w++tail,l)=F.encAt l := by
  unfold advice lookup
  rw [unpack_exact,generatedBundleDescriptions,bundleRequests_correct]
  simp only [List.map_ofFn,Function.comp_def,hc]
  rw [List.getElem?_eq_getElem (by simpa)]
  simp only [Option.getD_some,List.getElem_ofFn]

theorem family_table (F : MFamily) (hF : IsMQPT F) (Q : Polynomial ℕ) :
    ∃ v : Str→Str, PolyTimeComputable v ∧ ∀ n l (tail : Str), l≤Q.eval n →
      lookup (v (unary n)++tail,l)=F.encAt l := by
  obtain ⟨g,hg,h⟩ := hF.1
  refine ⟨advice g Q,advice_stock g hg Q,?_⟩
  intro n l tail hl
  apply advice_lookup F g h
  simpa [unary] using hl

end

end InfoLossLAR.WorstCase.RegevSearch.OracleTable

end P2MDyadicModule92

/- Helper module AdviceCap. -/
section P2MDyadicModule93

set_option autoImplicit false

set_option maxHeartbeats 1250000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.OracleTable

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization QMCNumericRuntime

noncomputable section

abbrev Inputs := Str × Str × Str

def mark (x : Str) := lengthToken x++x

def frame (x : Inputs) := mark x.1 ++ mark x.2.1 ++ x.2.2

def pop (w : Str) : Str×Str :=
  let m := (unarySlots w).length
  let r := (readUnary w).2
  (r.take m,r.drop m)

@[fun_prop] theorem pop_poly : Poly pop := by
  have hp : Poly (fun w : Str => ((readUnary w).2,(unarySlots w).length)) :=
    Poly.pair (Poly.comp (f:=Prod.snd) (g:=readUnary) Poly.snd readUnary_poly)
      (Poly.comp (f:=List.length (α:=Unit)) (g:=unarySlots) Poly.list_length unarySlots_poly)
  exact Poly.pair (Poly.comp parser_take_poly hp) (Poly.comp parser_drop_poly hp)

theorem pop_mark (s t : Str) : pop (mark s++t)=(s,t) := by
  simp only [pop,mark,lengthToken_eq,List.append_assoc,readUnary_append,unarySlots_append,List.length_replicate,
    List.take_left,List.drop_left]

def fields (w : Str) : Inputs := ((pop w).1,pop (pop w).2)

@[fun_prop] theorem fields_poly : Poly fields := by unfold fields;fun_prop

theorem frame_fields (z : Inputs) : fields (frame z)=z := by
  rcases z with ⟨s,t,u⟩
  simp only [fields,frame,List.append_assoc,pop_mark]

theorem frame_length (z : Inputs) : (frame z).length=2*z.1.length+2*z.2.1.length+z.2.2.length+2 := by
  simp [frame,mark,lengthToken];omega

/-- The first word is the original input. The second can be any padded pool or complete
physical history of bounded size. The third is a stage index or extra parameters. -/
theorem uniform_slot_cap (f : Inputs→List Unit) (hf : Poly f) (H J : Polynomial ℕ) :
    ∃ Q : Polynomial ℕ, ∀ s h j : Str, h.length≤H.eval s.length → j.length≤J.eval s.length →
      (f (s,h,j)).length ≤ Q.eval s.length := by
  let g := fun w : Str => (f (fields w)).map (fun _ => true)
  have hg : Poly g := by unfold g;fun_prop
  obtain ⟨C,hC⟩ := Integration9_9.TM2OutputLength.polynomial_output_length (polyTime_of_poly hg).some
  let U : Polynomial ℕ := 2*Polynomial.X+2*H+J+2
  refine ⟨C.comp U,?_⟩
  intro s h j hh hj
  have hg' := hC (frame (s,h,j))
  change (g (frame (s,h,j))).length≤ C.eval (frame (s,h,j)).length at hg'
  simp only [g,frame_fields,List.length_map] at hg'
  apply hg'.trans
  rw [Polynomial.eval_comp]
  apply polynomial_eval_mono
  simp only [U,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,frame_length]
  omega

theorem table_for_slots (F : MFamily) (hF : IsMQPT F) (f : Inputs→List Unit)
    (hf : Poly f) (H J : Polynomial ℕ) :
    ∃ (Q : Polynomial ℕ) (v : Str→Str), PolyTimeComputable v ∧
      (∀ s h j : Str, h.length≤H.eval s.length → j.length≤J.eval s.length →
        (f (s,h,j)).length≤Q.eval s.length) ∧
      (∀ s h j tail : Str, h.length≤H.eval s.length → j.length≤J.eval s.length →
        lookup (v (unary s.length)++tail,(f (s,h,j)).length)=F.encAt (f (s,h,j)).length) := by
  obtain ⟨Q,cap⟩ := uniform_slot_cap f hf H J
  obtain ⟨v,hv,correct⟩ := family_table F hF Q
  exact ⟨Q,v,hv,cap,fun s h j tail hh hj => correct _ _ tail (cap s h j hh hj)⟩

end

end InfoLossLAR.WorstCase.RegevSearch.OracleTable

end P2MDyadicModule93

/- Helper module PlanCode. -/
section P2MDyadicModule94

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

variable {h k : ℕ}

abbrev Pin := ℕ×ℕ

def pin {h : ℕ} : Source h→Pin | .literal false => (0,0) | .literal true => (1,0) | .wire i => (2,i.val)

def loadCode (base i : ℕ) (p : Pin) : List GateCode :=
  if p.1=0 then [] else if p.1=1 then [(3,base+i,0)] else [(4,p.2,base+i)]

@[fun_prop] theorem loadCode_poly : Poly (fun x : (ℕ×ℕ)×Pin => loadCode x.1.1 x.1.2 x.2) := by
  unfold loadCode;fun_prop

def shifted (d : ℕ) (g : GateCode) : GateCode := (g.1,d+g.2.1,if g.1=4 then d+g.2.2 else 0)

@[fun_prop] theorem shifted_poly : Poly (fun x : ℕ×GateCode => shifted x.1 x.2) := by unfold shifted;fun_prop

abbrev Block := List Pin × List GateCode

def pack (a : Fin k→Source h) (U : Layered k) : Block :=
  (List.ofFn (fun i => pin (a i)), U.flatten.map encodeInstr)

def blockCode (d : ℕ) (b : Block) : List GateCode :=
  ((List.range b.1.length).flatMap (fun i => loadCode d i (b.1[i]?.getD (0,0)))) ++
    b.2.map (shifted d)

@[fun_prop] theorem blockCode_poly : Poly (fun x : ℕ×Block => blockCode x.1 x.2) := by
  unfold blockCode
  have hi : Poly (fun x : ℕ×Block => List.range x.2.1.length) :=
    Poly.comp (f:=fun a : List Pin => List.range a.length) (g:=fun x : ℕ×Block => x.2.1) Poly.list_indices (by fun_prop)
  have hload : Poly (fun x : ℕ×Block => (List.range x.2.1.length).flatMap (fun i => loadCode x.1 i (x.2.1[i]?.getD (0,0)))) :=
    Poly.list_flatMap (Poly.comp (g:=fun u : (ℕ×Block)×ℕ => ((u.1.1,u.2),u.1.2.1[u.2]?.getD (0,0))) loadCode_poly (by fun_prop)) hi
  have hs : Poly (fun x : ℕ×Block => x.2.2.map (shifted x.1)) :=
    Poly.list_map (Poly.comp (g:=fun u : (ℕ×Block)×GateCode => (u.1.1,u.2)) shifted_poly (by fun_prop)) (by fun_prop)
  fun_prop

theorem loadCode_eq (i : Fin k) (s : Source h) : loadCode h i.val (pin s)=(gate i s).map encodeInstr := by
  cases s with
  | literal b => cases b <;> rfl
  | wire j => rfl

theorem block_eq (a : Fin k → Source h) (U : Layered k) :
    blockCode h (pack a U) = (stage a U).flatten.map encodeInstr := by
  simp only [blockCode,pack,List.length_ofFn,stage,List.flatten_append,
    relocateCircuit,List.map_append,List.map_flatMap,List.map_map]
  congr 1
  · rw [show List.range k = (List.finRange k).map Fin.val by simp]
    rw [show ((load a).map (fun g => [g])).flatten=load a by induction load a with | nil => rfl | cons x xs ih => simpa using ih]
    simp only [List.flatMap_map,load,List.map_flatMap,Function.comp_def,List.getElem?_ofFn,Fin.isLt,
      dif_pos,Option.getD_some,loadCode_eq]
  · induction U with
    | nil => rfl
    | cons row rest ih =>
      simp only [List.flatten_cons,List.map_cons,List.map_append,←ih]
      congr 1
      simp only [List.map_map,Function.comp_def]
      apply List.map_congr_left;intro g _;cases g <;> rfl

def used (s : List Unit × List Block) (i : ℕ) := s.1.length+((s.2.take i).flatMap Prod.fst).length

@[fun_prop] theorem used_poly : Poly (fun x : (List Unit×List Block)×ℕ => used x.1 x.2) := by
  have ht : Poly (fun x : (List Unit×List Block)×ℕ => x.1.2.take x.2) :=
    Poly.comp (f:=fun z : List Block×ℕ => z.1.take z.2) (g:=fun x : (List Unit×List Block)×ℕ => (x.1.2,x.2))
      ⟨PolyProgram.listTake Automatic.enc ([],[])⟩ (by fun_prop)
  have hf : Poly (fun x : (List Unit×List Block)×ℕ => (x.1.2.take x.2).flatMap Prod.fst) := Poly.list_flatMap (by fun_prop) ht
  unfold used;fun_prop

def allCode (s : List Unit × List Block) :=
  (List.range s.2.length).flatMap (fun i => blockCode (used s i) (s.2[i]?.getD ([],[])))

@[fun_prop] theorem allCode_poly : Poly allCode := by
  unfold allCode
  apply Poly.list_flatMap
  · exact Poly.comp (g:=fun x : (List Unit × List Block)×ℕ => (used x.1 x.2,x.1.2[x.2]?.getD ([],[]))) blockCode_poly (by fun_prop)
  · exact Poly.comp (f:=fun a : List Block => List.range a.length) (g:=Prod.snd) Poly.list_indices Poly.snd

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule94

/- Helper module PlanTrace. -/
section P2MDyadicModule95

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open scoped Classical BigOperators

noncomputable section

inductive Trace (s : ℕ) : ℕ → Type where
  | start : Trace s s
  | extend {h k : ℕ} (before : Trace s h) (pins : Fin k→Source h) (unit : Layered k) : Trace s (h+k)

variable {s h k : ℕ}

def Trace.blocks : {h : ℕ} → Trace s h → List Block
  | _, .start => []
  | _, .extend t a U => t.blocks ++ [pack a U]

def Trace.circuit : {h : ℕ} → Trace s h → Layered h
  | _, .start => []
  | _, .extend t a U => leftCircuit t.circuit ++ stage a U

theorem width_blocks (t : Trace s h) : s+(t.blocks.flatMap Prod.fst).length=h := by
  induction t with
  | start => simp [Trace.blocks]
  | extend t a U ih =>
    simp only [Trace.blocks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_append,pack,List.length_ofFn,← Nat.add_assoc,ih]

theorem left_words (U : Layered h) : (leftCircuit (m:=k) U).flatten.map encodeInstr=U.flatten.map encodeInstr := by
  induction U with
  | nil => rfl
  | cons r U ih =>
    simp only [leftCircuit,List.map_cons,List.flatten_cons,List.map_append,List.map_map,Function.comp_def] at ih ⊢
    rw [ih];congr 1
    apply List.map_congr_left;intro g _;cases g <;> rfl

theorem allCode_snoc (base : List Unit) (xs : List Block) (b : Block) :
    allCode (base,xs++[b])=allCode (base,xs) ++ blockCode (base.length+(xs.flatMap Prod.fst).length) b := by
  unfold allCode
  simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,List.range_succ,
    List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  congr 1
  · apply List.flatMap_congr
    intro i hi
    have hi' := List.mem_range.mp hi
    simp [used,List.take_append_of_le_length hi'.le,List.getElem?_append_left hi']
  · simp [used,List.take_append_of_le_length (le_refl xs.length)]

theorem native_trace (t : Trace s h) :
    allCode (List.replicate s (),t.blocks)=t.circuit.flatten.map encodeInstr := by
  induction t with
  | start => rfl
  | extend t a U ih =>
    rw [Trace.blocks,allCode_snoc,List.length_replicate,width_blocks,ih,block_eq]
    simp only [Trace.circuit,List.flatten_append,List.map_append,left_words]

def zeroBits (n : ℕ) : Bits n := fun _ => false

theorem zero_tensor : basis (zeroBits (h+k)) = tensorState (basis (zeroBits h)) (basis (zeroBits k)) := by
  funext x
  have he : x=zeroBits (h+k) ↔ leftRegister x=zeroBits h ∧ rightRegister x=zeroBits k := by
    constructor
    · rintro rfl;exact ⟨rfl,rfl⟩
    · rintro ⟨hl,hr⟩;funext i;refine Fin.addCases (fun j => congrFun hl j) (fun j => congrFun hr j) i
  simp only [basis,tensorState,he]
  split_ifs <;> simp_all

def Trace.state (t : Trace s h) := runLayered t.circuit (basis (zeroBits h))

theorem state_step (t : Trace s h) (a : Fin k→Source h) (U : Layered k) (x : Bits h) (y : Bits k) :
    (t.extend a U).state (Fin.append x y)=t.state x * runLayered U (basis (fun i => (a i).read x)) y := by
  unfold Trace.state
  rw [Trace.circuit,show ∀ {n : ℕ} (V W : Layered n) (ψ : QState n),runLayered (V++W) ψ=runLayered W (runLayered V ψ)
    from fun _ _ _ => List.foldl_append,zero_tensor,leftCircuit_tensor]
  exact stage_branch a U _ x y

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule95

/- Helper module PlanBorn. -/
section P2MDyadicModule96

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 950000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open QAlgorithms.Papers.Independent.Renew46.P12 GaussianIteration

open scoped Classical BigOperators

noncomputable section

variable {s h k : ℕ} {X Y : Type*}

theorem row_norm (U : Layered k) (b : Bits k) : ∑ y, ‖runLayered U (basis b) y‖^2=1 := by
  have ht := runLayered_mass U (basis b)
  simp only [Complex.normSq_eq_norm_sq] at ht
  rw [ht]
  rw [Finset.sum_eq_single b]
  · simp [basis]
  · intro x _ hx;simp [basis,hx]
  · simp

def law (t : Trace s h) := born t.state (row_norm t.circuit (zeroBits h))

def conditional (a : Fin k→Source h) (U : Layered k) (x : Bits h) :=
  born (runLayered U (basis (fun i => (a i).read x))) (row_norm U _)

theorem step_eval (t : Trace s h) (a : Fin k→Source h) (U : Layered k)
    (decode : Bits h→Bits k→Y) (f : Test Y) :
    evaluate (law (t.extend a U)) (fun b => f (decode (leftRegister b) (rightRegister b))) =
    evaluate (law t) (fun x => ⟨evaluate (conditional a U x) (fun y => f (decode x y)), evaluate_range _ _⟩) := by
  rw [law,born_eval,law,born_eval]
  calc _ = ∑ xy : Bits h×Bits k,
            ‖t.state xy.1 * runLayered U (basis (fun i => (a i).read xy.1)) xy.2‖^2*(f (decode xy.1 xy.2):ℝ) := by
              apply Fintype.sum_equiv (qubitsAppendEquiv h k)
              intro z
              have he := (qubitsAppendEquiv h k).symm_apply_apply z
              change Fin.append (leftRegister z) (rightRegister z)=z at he
              have h := state_step t a U (leftRegister z) (rightRegister z)
              rw [he] at h
              rw [h];rfl
       _ = _ := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro x hx
            simp only [conditional,born_eval,norm_mul,mul_pow,Finset.mul_sum,mul_assoc]

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule96

/- Helper module Solutions.RegevBridgeLoadedBatchPostFrame. -/
section P2MDyadicModule97

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

end P2MDyadicModule97

/- Helper module AdviceLaw. -/
section P2MDyadicModule98

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open TM2Boolean TM2Boolean.PolyProgramCircuit

open scoped Classical BigOperators

noncomputable section

def extended (n : ℕ) (w : Str) : Bits n := fun i => wordExtension w i.val

def probAt (F : MFamily) (n : ℕ) (s : Str) (E : Str→Prop) :=
  ∑ z, if E (List.ofFn fun i => z (F.outW n i)) then ‖runLayered (F.circ n) (basis (extended _ s)) z‖^2 else 0

theorem probAt_eq (F : MFamily) (s : Str) (E : Str→Prop) :
    probAt F s.length s E=outputProb F s E := by
  unfold probAt outputProb;rw [basisInput_eq_computationalBasis,wordExtension_basis];rfl

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

end P2MDyadicModule98

/- Helper module AdviceWords. -/
section P2MDyadicModule99

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open NativeWordDescription TM2Boolean TM2Boolean.CodeGenerator

open Integration9_9.TM2PlatformSerialization Integration9_9.LoadedBatch.PostComposition

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped Classical BigOperators

noncomputable section

def lit (b : Bool) : Pin := if b then (1,0) else (0,0)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

end P2MDyadicModule99

/- Helper module ExactProgram. -/
section P2MDyadicModule100

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

set_option maxRecDepth 12000

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT AFT.RationalNumerics GaussianRandomizedRounding

open scoped BigOperators

abbrev Setup := (List (List ℤ) × ℚ) × List Unit

def setup {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (W : ℚ) (a : List Unit) : Setup :=
  ((List.ofFn fun i => List.ofFn fun j => D i j,W),a)

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

end P2MDyadicModule100

/- Helper module Rebase. -/
section P2MDyadicModule101

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 700000

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

open AFT AFT.RationalNumerics GaussianRandomizedRounding IntegerBasis RegevSketch

noncomputable section

variable {n : ℕ}

private theorem same_module (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    inputModule B = inputLattice B hB := by
  unfold inputModule inputLattice
  congr 2
  funext i
  simp [realBasis_apply,latVec,Matrix.mulVec_single]

/-- The field of original coordinates can be computed from an integer lattice
point by an adjugate multiplication and exact division. -/
def originalWord (B D : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) : Fin n → ℤ :=
  fun i => B.adjugate.mulVec (D.mulVec z) i / B.det

private theorem recover {B D : Matrix (Fin n) (Fin n) ℤ} (hB : B.det ≠ 0)
    {z y : Fin n → ℤ} (hy : B.mulVec y = D.mulVec z) : originalWord B D z = y := by
  funext i
  simp only [originalWord, ←hy, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel_left _ hB

private theorem equal_range (D B : Matrix (Fin n) (Fin n) ℤ) (hd : D.det ≠ 0) (hb : B.det ≠ 0)
    (hs : inputModule D = inputModule B) (z : Fin n → ℤ) :
    ∃ y, B.mulVec y = D.mulVec z := by
  have hl : inputLattice D hd = inputLattice B hb := (same_module D hd).symm.trans (hs.trans (same_module B hb))
  have he : lattice D = lattice B := by rw [← inputLattice_eq_target D hd, ←inputLattice_eq_target B hb, hl]
  have hm : latVec D z ∈ lattice B := he ▸ (show latVec D z ∈ lattice D from ⟨z,rfl⟩)
  obtain ⟨y,hy⟩ := hm
  refine ⟨y, ?_⟩
  funext i
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hy
  change ((B.mulVec y i:ℤ):ℝ) = ((D.mulVec z i:ℤ):ℝ) at h
  exact_mod_cast h

theorem rebase_exists (D B : Matrix (Fin n) (Fin n) ℤ) (hd : D.det ≠ 0) (hb : B.det ≠ 0)
    (hs : inputModule D = inputModule B) :
    ∃ e : (Fin n → ℤ) ≃ (Fin n → ℤ), ∀ z, B.mulVec (e z) = D.mulVec z := by
  have f (z : Fin n → ℤ) : B.mulVec (originalWord B D z) = D.mulVec z := by
    obtain ⟨y,hy⟩ := equal_range D B hd hb hs z
    rw [recover hb hy,hy]
  have g (z : Fin n → ℤ) : D.mulVec (originalWord D B z) = B.mulVec z := by
    obtain ⟨y,hy⟩ := equal_range B D hb hd hs.symm z
    rw [recover hd hy,hy]
  exact ⟨⟨originalWord B D,originalWord D B,fun z => recover hd (f z).symm,
    fun z => recover hb (g z).symm⟩, f⟩

theorem originalWord_eq (B D : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (e : (Fin n → ℤ) ≃ (Fin n → ℤ)) (he : ∀ z, B.mulVec (e z) = D.mulVec z)
    (z : Fin n → ℤ) : originalWord B D z = e z := recover hB (he z)

theorem rebase_mass (D B : Matrix (Fin n) (Fin n) ℤ) (W : ℚ)
    (e : (Fin n → ℤ) ≃ (Fin n → ℤ)) (he : ∀ z, B.mulVec (e z) = D.mulVec z) (z : Fin n → ℤ) :
    coefficientMass D W z = coefficientMass B W (e z) := by
  unfold coefficientMass
  rw [he z, ←e.tsum_eq (fun x => rhoInt W (B.mulVec x))]
  simp_rw [he]

/-- The same measured fair bits, followed by a finite channel of the original
signed coefficient vector. -/
theorem scheduled_original_coordinates {O : Type*} [Fintype O]
    (D B : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (hB : B.det ≠ 0)
    (hs : inputModule D = inputModule B) (hn : 1 ≤ n) (r : ℚ)
    (a : List Unit) (ch : (Fin n → ℤ) → FiniteDist O) :
    let W := max (RationalGramSchmidt.initialWidth D (n+1:ℕ)) (r * (famσ n : ℚ))
    let actual := (FiniteDist.uniform (Fin (ticks (setup D W a)).length → Bool)).mix
      (fun tape => ch (originalWord B D (fun i => (sample (setup D W a,List.ofFn tape))[i.val]?.getD 0)))
    ∃ ideal : FiniteDist O,
      (∀ o, ideal.weight o = ∑' z, coefficientMass B W z * (ch z).weight o) ∧
      FiniteDist.TVBound actual ideal (n*Wide.sampleError a.length + 4*((n:ℝ)*initialThetaBudget (n+1))) := by
  obtain ⟨e,he⟩ := rebase_exists D B hD hB hs
  obtain ⟨ideal,hm,ht⟩ := scheduled_initial_sample D hD hn r a (fun x => ch (originalWord B D x))
  refine ⟨ideal, ?_, ht⟩
  intro o
  rw [hm]
  simp_rw [originalWord_eq B D hB e he, rebase_mass D B _ e he]
  exact e.tsum_eq (fun z => coefficientMass B (max (RationalGramSchmidt.initialWidth D (n+1:ℕ)) (r * (famσ n : ℚ)) : ℚ) z * (ch z).weight o)

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

end P2MDyadicModule101

/- Helper module Solutions.RegevBridgeRationalInverseAlgebra. -/
section P2MDyadicModule102

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

theorem rational_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : QVector n) (h : ∀ k,innerQ x (inputVectors B k)=innerQ y (inputVectors B k)) : x=y := by
  apply realVec_injective
  apply real_pairings_unique B hdet
  intro k
  rw [←inputVectors_real B hdet k,←innerQ_real,←innerQ_real,h k]

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

end P2MDyadicModule102

/- Helper module Solutions.RegevBridgeRationalInverseRecurrence. -/
section P2MDyadicModule103

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

@[simp] theorem innerQ_sub_left {n : ℕ} (x y z : QVector n) :
    innerQ (x-y) z=innerQ x z-innerQ y z := by simp [innerQ,sub_mul,Finset.sum_sub_distrib]

@[simp] theorem innerQ_smul_left {n : ℕ} (a : ℚ) (x y : QVector n) :
    innerQ (a • x) y=a*innerQ x y := by simp [innerQ,Finset.mul_sum,mul_assoc]

theorem innerQ_sum_left {n : ℕ} {J : Type*} (s : Finset J) (x : J → QVector n) (y : QVector n) :
    innerQ (∑ j∈s,x j) y=∑ j∈s,innerQ (x j) y := by
  simp only [innerQ,Finset.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

/-- One reverse triangular substitution step. Its only arithmetic operands
are the cached original rational orthogonalization and future dual columns. -/
def dualStep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (cache : Fin n → QVector n) (i : Fin n) : QVector n :=
  (squaredNorm (inputVectors B) i)⁻¹ • orthogonal (inputVectors B) i-
    ∑ j∈Finset.Ioi i,upper (inputVectors B) i j • cache j

noncomputable section

theorem dualStep_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i k : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) :
    innerQ (dualStep B cache i) (inputVectors B k)=if k=i then 1 else 0 := by
  rw [dualStep,innerQ_sub_left,innerQ_smul_left,innerQ_sum_left]
  simp only [innerQ_smul_left]
  have hfirst : (squaredNorm (inputVectors B) i)⁻¹*innerQ (orthogonal (inputVectors B) i) (inputVectors B k)=
      upper (inputVectors B) i k := by unfold upper;ring
  rw [hfirst]
  have hsum : (∑ j∈Finset.Ioi i,upper (inputVectors B) i j*innerQ (cache j) (inputVectors B k))=
      if i< k then upper (inputVectors B) i k else 0 := by
    calc
      _ = ∑ j∈Finset.Ioi i,if k=j then upper (inputVectors B) i j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcache j (Finset.mem_Ioi.mp hj),dualVector_pairing B hdet]
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_Ioi]
  rw [hsum]
  by_cases he : k=i
  · subst k
    simp [upper_diagonal _ (inputVectors_independent B hdet)]
  · by_cases hi : i< k
    · simp [hi,he]
    · have hk : k< i := lt_of_le_of_ne (le_of_not_gt hi) he
      rw [upper_triangular _ i k hk]
      simp [hi,he]

theorem dualStep_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) : dualStep B cache i=dualVector B i := by
  apply rational_pairings_unique B hdet
  intro k
  rw [dualStep_pairing B hdet cache i k hcache,dualVector_pairing B hdet]

/-- A complete matrix cache is updated from the last column backwards.
Every completed column is already a final original-input dual column. -/
def dualCache {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℕ → Fin n → QVector n
  | 0 => fun _ => 0
  | steps+1 =>
      let previous :=dualCache B steps
      if h : steps< n then
        let i : Fin n :=⟨n-1-steps,by omega⟩
        Function.update previous i (dualStep B previous i)
      else previous

theorem dualCache_formula {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (steps : ℕ) (hsteps : steps≤ n) (j : Fin n) :
    dualCache B steps j=if n-steps≤ j.val then dualVector B j else 0 := by
  induction steps generalizing j with
  | zero =>
    have hj : ¬n≤ j.val := by omega
    simp [dualCache,hj]
  | succ steps ih =>
    have hs : steps< n := by omega
    let i : Fin n :=⟨n-1-steps,by omega⟩
    have hf : ∀ k,i< k → dualCache B steps k=dualVector B k := by
      intro k hk
      rw [ih (by omega) k]
      have ht : n-steps≤ k.val := by change i.val< k.val at hk;dsimp [i] at hk;omega
      simp only [if_pos ht]
    have he:=dualStep_correct B hdet (dualCache B steps) i hf
    change (if h : steps< n then Function.update (dualCache B steps)
      (⟨n-1-steps,by omega⟩ : Fin n) (dualStep B (dualCache B steps) ⟨n-1-steps,by omega⟩) else dualCache B steps) j=_
    rw [dif_pos hs]
    change Function.update (dualCache B steps) i (dualStep B (dualCache B steps) i) j=_
    rw [he]
    by_cases hj : j=i
    · subst j
      rw [Function.update_self]
      have ht : n-(steps+1)≤ i.val := by dsimp [i];omega
      simp only [if_pos ht]
    · rw [Function.update_of_ne hj,ih (by omega) j]
      have hv : j.val≠n-1-steps := by intro h;apply hj;exact Fin.ext h
      have ht : (n-steps≤ j.val)=(n-(steps+1)≤ j.val) := propext (by omega)
      simp only [ht]

theorem dualCache_complete {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    dualCache B n=dualVector B := by
  funext j
  rw [dualCache_formula B hdet n (le_refl n)]
  simp

theorem dualCache_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (H : ℕ) (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H)
    (steps : ℕ) (hs : steps≤ n) (j row : Fin n) :
    HeightBound (dualCache B steps j row) (coordinateHeight n H) := by
  rw [dualCache_formula B hdet steps hs]
  split_ifs
  · exact (dualVector_height B H hentries j row).mono (by unfold dualHeight coordinateHeight;nlinarith)
  · exact HeightBound.zero.mono (Nat.zero_le _)

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule103

/- Helper module Solutions.RegevBridgeRationalInverseNative. -/
section P2MDyadicModule104

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

abbrev Context := List (List ℚ) × List (List ℚ)

abbrev State := Context × (List Unit × List (List ℚ))

/-- One rational summand of reverse triangular substitution. -/
def term (input : (((Context × List (List ℚ)) × ℕ) × ℕ) × ℕ) : ℚ :=
  let source := input.1
  let gs := source.1.1.1.2[source.1.2]?.getD []
  if source.1.2< input.2 then
    dot (gs,source.1.1.1.1[input.2]?.getD [])/dot (gs,gs)*
      (source.1.1.2[input.2]?.getD [])[source.2]?.getD 0 else 0

@[fun_prop] theorem term_poly : Poly term := by unfold term;fun_prop

/-- One entry uses only native rational operations and bounded index lists. -/
def entry (input : ((Context × List (List ℚ)) × ℕ) × ℕ) : ℚ :=
  let gs := input.1.1.1.2[input.1.2]?.getD []
  gs[input.2]?.getD 0/dot (gs,gs)-
    ((List.range input.1.1.1.1.length).map (fun j => term (input,j))).sum

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

def column (input : (Context × List (List ℚ)) × ℕ) : List ℚ :=
  (List.range input.1.1.1.length).map (fun row => entry (input,row))

@[fun_prop] theorem column_poly : Poly column := by
  have hi : Poly (fun input : (Context × List (List ℚ)) × ℕ => List.range input.1.1.1.length) := by
    exact Poly.comp (f:=fun values : List (List ℚ) => List.range values.length)
      (g:=fun input : (Context × List (List ℚ)) × ℕ => input.1.1.1) Poly.list_indices (by fun_prop)
  unfold column
  exact Poly.list_map entry_poly hi

def replaceColumn (input : (List (List ℚ) × ℕ) × List ℚ) : List (List ℚ) :=
  (List.range input.1.1.length).map (fun j => if j=input.1.2 then input.2 else input.1.1[j]?.getD [])

@[fun_prop] theorem replaceColumn_poly : Poly replaceColumn := by
  have hi : Poly (fun input : (List (List ℚ) × ℕ) × List ℚ => List.range input.1.1.length) :=
    Poly.comp (f:=fun values : List (List ℚ) => List.range values.length)
      (g:=fun input : (List (List ℚ) × ℕ) × List ℚ => input.1.1) Poly.list_indices (by fun_prop)
  unfold replaceColumn
  exact Poly.list_map (by fun_prop) hi

/-- A public encoding-length guard bounds every fold state, including
malformed and singular inputs. Correctness proves that it never fires on
nonsingular original integer matrices. -/
def step (state : State) (counter : ℕ) : State :=
  let index := state.1.1.length-1-counter
  let next := replaceColumn ((state.2.2,index),column ((state.1,state.2.2),index))
  (state.1,(state.2.1,if (matrixTicks next).length≤ state.2.1.length then next else []))

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

/-- The actual cache consumes the original row-major integer input. The
only preprocessing is the previously certified native orthogonalization. -/
def cached (input : List (List ℤ)) : List (List ℚ) :=
  let original := rationalColumns (transpose input)
  let gs := basisCache input
  let zeros := original.map (fun row => row.map (fun _ => (0 : ℚ)))
  ((List.range input.length).foldl step ((original,gs),(inputBudget input,zeros))).2.2

@[fun_prop] theorem cached_poly : Poly cached := by
  have hi : Poly (fun input : List (List ℤ) =>
      (List.range input.length,
        ((rationalColumns (transpose input),basisCache input),
          (inputBudget input,(rationalColumns (transpose input)).map (fun row => row.map (fun _ => (0 : ℚ))))))) := by
    fun_prop
  unfold cached
  exact Poly.comp (f:=fun state : State => state.2.2) (by fun_prop) (Poly.comp fold_poly hi)

def transposeRational (input : List (List ℚ)) : List (List ℚ) :=
  (List.range input.length).map (fun row => input.map (fun column => column[row]?.getD 0))

@[fun_prop] theorem transposeRational_poly : Poly transposeRational := by
  have hi : Poly (fun input : List (List ℚ) => List.range input.length) := Poly.list_indices
  unfold transposeRational
  exact Poly.list_map (by fun_prop) hi

/-- Native row-major output for the original integer matrix's inverse
transpose. No determinant, real dual-basis or arbitrary real oracle is
called by this program. -/
def current (input : List (List ℤ)) : List (List ℚ) := transposeRational (cached input)

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule104

/- Helper module Solutions.RegevBridgeRationalInverseRefinement. -/
section P2MDyadicModule105

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

def matrixOf {n : ℕ} (vectors : Fin n → QVector n) : List (List ℚ) :=
  List.ofFn (fun j => List.ofFn (vectors j))

def context {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Context :=
  (matrixOf (inputVectors B),matrixOf (orthogonal (inputVectors B)))

theorem term_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (cache : Fin n → QVector n) (i row j : Fin n) :
    term ((((context B,matrixOf cache),i.val),row.val),j.val)=
      if i< j then upper (inputVectors B) i j*cache j row else 0 := by
  simp only [term,context,matrixOf,List.getElem?_ofFn,i.isLt,j.isLt,row.isLt,
    ↓reduceDIte,Option.getD_some,dot_ofFn]
  rfl

theorem column_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (cache : Fin n → QVector n) (i : Fin n) :
    column ((context B,matrixOf cache),i.val)=List.ofFn (dualStep B cache i) := by
  apply List.ext_getElem
  · simp only [column,context,matrixOf,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hr : row< n := by simpa only [List.length_ofFn] using hsecond
    let r : Fin n :=⟨row,hr⟩
    have hs : (List.range n).map (fun j => term ((((context B,matrixOf cache),i.val),row),j))=
        List.ofFn (fun j : Fin n => if i< j then upper (inputVectors B) i j*cache j r else 0) := by
      apply List.ext_getElem
      · simp
      · intro j hj hk
        have hjn : j< n := by simpa using hj
        simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using term_ofFn B cache i r ⟨j,hjn⟩
    have hi : Finset.Ioi i=Finset.univ.filter (fun j => i< j) := by ext j;simp
    have hlen : (context B).1.length=n := by simp [context,matrixOf]
    simp only [column,hlen,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change entry ((((context B,matrixOf cache),i.val),row))=dualStep B cache i r
    simp only [entry,hlen]
    rw [hs,Fin.sum_ofFn]
    simp only [context,matrixOf,List.getElem?_ofFn,i.isLt,hr,↓reduceDIte,Option.getD_some,dot_ofFn]
    simp only [dualStep,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,hi,Finset.sum_filter,squaredNorm,ite_apply,Pi.zero_apply]
    ring

theorem replaceColumn_ofFn {n : ℕ} (cache : Fin n → QVector n) (i : Fin n) (value : QVector n) :
    replaceColumn ((matrixOf cache,i.val),List.ofFn value)=matrixOf (Function.update cache i value) := by
  apply List.ext_getElem
  · simp [replaceColumn,matrixOf]
  · intro j hj hk
    have hjn : j< n := by simpa only [matrixOf,List.length_ofFn] using hk
    let k : Fin n :=⟨j,hjn⟩
    simp only [replaceColumn,matrixOf,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change (if j=i.val then List.ofFn value else (List.ofFn (fun j => List.ofFn (cache j)))[j]?.getD [])=
      List.ofFn (Function.update cache i value k)
    by_cases h : k=i
    · subst k
      have hjval : j=i.val := congrArg Fin.val h
      simp only [hjval,ite_true,Function.update_self]
    · have hji : j≠i.val := by intro he;apply h;exact Fin.ext he
      simp only [hji,if_false,List.getElem?_ofFn,hjn,↓reduceDIte,Option.getD_some,Function.update_of_ne h]
      rfl

/-- The Cramer bound controls every whole reverse-substitution cache. -/
theorem dualCache_encoding_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (H : ℕ) (hentries : ∀ r c,|B r c|≤ (2 : ℤ)^H) (steps : ℕ) (hs : steps≤ n) :
    (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ cacheEncodingBound n H := by
  have he := encoded_list_length_bound (encodeList Ratio.encode) (matrixOf (dualCache B steps))
    (n*(6*coordinateHeight n H+21)) (by
      intro vector hv
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hv
      exact vector_encoding_height _ _ (fun row => dualCache_height B hdet H hentries steps hs j row))
  simpa only [matrixOf,List.length_ofFn,cacheEncodingBound,Nat.mul_assoc] using he

theorem step_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (steps : ℕ) (hs : steps< n)
    (hb : (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B (steps+1)))).length≤ ticks.length) :
    step (context B,(ticks,matrixOf (dualCache B steps))) steps=
      (context B,(ticks,matrixOf (dualCache B (steps+1)))) := by
  let i : Fin n :=⟨n-1-steps,by omega⟩
  have hn : replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val))=matrixOf (dualCache B (steps+1)) := by
    rw [column_ofFn,replaceColumn_ofFn]
    rw [dualCache,dif_pos hs]
  have hg : (matrixTicks (replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val)))).length≤ ticks.length := by
    rw [hn,matrixTicks_length]
    exact hb
  have hlen : (context B).1.length=n := by simp [context,matrixOf]
  simp only [step,hlen]
  change (context B,(ticks,if (matrixTicks (replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val)))).length≤ ticks.length then _ else []))=_
  rw [if_pos hg,hn]

theorem fold_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (hb : ∀ steps,steps≤ n →
      (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ ticks.length)
    (steps : ℕ) (hs : steps≤ n) :
    (List.range steps).foldl step (context B,(ticks,matrixOf (fun _ : Fin n => (0 : QVector n))))=
      (context B,(ticks,matrixOf (dualCache B steps))) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [List.range_succ,List.foldl_append,ih (by omega),List.foldl_cons,List.foldl_nil]
    exact step_ofFn B ticks steps (by omega) (hb (steps+1) hs)

theorem inputRows_dimension {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    n≤ (integerMatrixTicks (inputRows B)).length := inputColumns_dimension B.transpose

theorem inputRows_entry_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (row col : Fin n) :
    |B row col|≤ (2 : ℤ)^(integerMatrixTicks (inputRows B)).length :=
  inputColumns_entry_height B.transpose col row

theorem basisCache_matrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    basisCache (inputRows B)=matrixOf (orthogonal (inputVectors B)) := by
  rw [inputRows,basisCache_correct B hdet,cache_prefix_eq _ n (le_refl n),List.map_ofFn]
  rfl

/-- Exact refinement of the guarded reverse loop for every nonsingular
original integer input; the public bit-size guard never changes its data. -/
theorem cached_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    cached (inputRows B)=matrixOf (dualVector B) := by
  have hb : ∀ steps,steps≤ n →
      (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ (inputBudget (inputRows B)).length := by
    intro steps hs
    apply (dualCache_encoding_bound B hdet (integerMatrixTicks (inputRows B)).length
      (inputRows_entry_height B) steps hs).trans
    rw [inputBudget_length]
    exact cacheEncodingBound_coarse n _ _ (inputRows_dimension B) le_rfl
  have ho : rationalColumns (transpose (inputRows B))=matrixOf (inputVectors B) := by
    rw [inputRows,transpose_input_rows,rationalColumns_input]
    rfl
  have hz : (matrixOf (inputVectors B)).map (fun row => row.map (fun _ => (0 : ℚ)))=
      matrixOf (fun _ : Fin n => (0 : QVector n)) := by
    simp only [matrixOf,List.map_ofFn,Function.comp_def]
    rfl
  unfold cached
  rw [ho,basisCache_matrix B hdet]
  dsimp only
  rw [hz]
  have hl : (inputRows B).length=n := by simp [inputRows]
  rw [hl]
  change ((List.range n).foldl step
    (context B,(inputBudget (inputRows B),matrixOf (fun _ : Fin n => (0 : QVector n))))).2.2=_
  rw [fold_ofFn B _ hb n (le_refl n),dualCache_complete B hdet]

theorem transposeRational_ofFn {n : ℕ} (v : Fin n → QVector n) :
    transposeRational (matrixOf v)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => v col row)) := by
  apply List.ext_getElem
  · simp [transposeRational,matrixOf]
  · intro row hr hs
    have hrow : row< n := by simpa using hs
    simp only [transposeRational,matrixOf,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some]

/-- Row-major output is exactly the original matrix inverse transpose. -/
theorem current_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    current (inputRows B)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => dualVector B col row)) := by
  rw [current,cached_correct B hdet,transposeRational_ofFn]

end

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule105

/- Helper module Solutions.RegevBridgeBDDCoordinateRounding. -/
section P2MDyadicModule106

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

end P2MDyadicModule106

/- Helper module Solutions.RegevBridgeBDDNativeArithmetic. -/
section P2MDyadicModule107

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.BDDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open scoped BigOperators

/-- Apply the actual native original inverse transpose to arbitrary signed
integer coordinates. Invalid input shapes retain total list semantics. -/
def lift (input : List (List ℤ) × List ℤ) : List ℚ :=
  (RationalInverse.Native.current input.1).map (fun row =>
    dot (row,input.2.map (fun value : ℤ => (value : ℚ))))

@[fun_prop] theorem lift_poly : Poly lift := by unfold lift;fun_prop

end InfoLossLAR.WorstCase.BDDNative

end P2MDyadicModule107

/- Helper module Solutions.RegevBridgeBDDNativeSemantics. -/
section P2MDyadicModule108

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.BDDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

def combination {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (coords : Fin n → ℤ) : QVector n :=
  ∑ col,(coords col : ℚ) • dualVector B col

theorem lift_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (coords : Fin n → ℤ) :
    lift (RationalInverse.Native.inputRows B,List.ofFn coords)=List.ofFn (combination B coords) := by
  rw [lift,RationalInverse.Native.current_correct B hdet]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext row
  rw [dot_ofFn]
  simp only [innerQ,combination,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro col _
  ring

end

end InfoLossLAR.WorstCase.BDDNative

end P2MDyadicModule108

/- Helper module Recovery. -/
section P2MDyadicModule109

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.ShortProbe

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

abbrev intRows {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) :=
  List.ofFn fun i => List.ofFn (C i)

theorem lift_eq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (z : Fin n → ℤ) (u : Fin n → ℚ)
    (h : ∀ j, ∑ i, (B i j:ℚ)*u i=z j) :
    BDDNative.lift (intRows B,List.ofFn z) = List.ofFn u := by
  rw [show intRows B = RationalInverse.Native.inputRows B from rfl,BDDNative.lift_ofFn _ hB]
  apply congrArg List.ofFn
  apply rational_pairings_unique B hB
  intro k
  have hsum (i : Fin n) : innerQ (dualVector B i) (inputVectors B k) = if k=i then 1 else 0 :=
    dualVector_pairing B hB i k
  change (∑ j,(∑ i, (z i : ℚ) • dualVector B i) j * inputVectors B k j) = _
  simp only [Finset.sum_apply,Pi.smul_apply, smul_eq_mul,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ i,(z i:ℚ) * innerQ (dualVector B i) (inputVectors B k)) = _
  simp_rw [hsum]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simpa only [innerQ,inputVectors,mul_comm] using (h k).symm

theorem matrixApply_rows {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) (z : Fin n → ℤ) :
    IntegerBasis.Native.matrixApply (intRows C,List.ofFn z)=List.ofFn (C.mulVec z) := by
  simp only [intRows,IntegerBasis.Native.matrixApply,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext j
  rw [Integration9_9.TM2NativeAffineApply.dot_ofFn]
  rfl

theorem nearest_int (z : ℤ) : IntegerBasis.nearestInteger (z:ℚ)=z := by
  rw [IntegerBasis.nearestInteger_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule109

/- Helper module Original. -/
section P2MDyadicModule110

set_option autoImplicit false

set_option maxHeartbeats 1250000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QAlgorithms.Complexity Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2PlatformSerialization

open RationalGramSchmidt.Native RationalGramSchmidt.Native.ExactWide

open IntegerBasis RegevSketch

open ShortProbe (intRows)

open scoped BigOperators

abbrev Matrices := List (List ℤ) × List (List ℤ)

abbrev Cfg := (Matrices × ℚ) × List Unit

def original (v : Matrices × List ℤ) : List ℤ :=
  let z := (List.range v.1.2.length).map fun i => v.2[i]?.getD 0
  (BDDNative.lift (transpose v.1.1,IntegerBasis.Native.matrixApply (v.1.2,z))).map IntegerBasis.nearestInteger

@[fun_prop] theorem original_poly : Poly original := by
  have hr : Poly (fun v : Matrices × List ℤ => List.range v.1.2.length) := Poly.comp (f:=fun xs : List (List ℤ) => List.range xs.length) Poly.list_indices (by fun_prop)
  unfold original
  fun_prop

theorem original_exact {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (hD : D.det≠0)
    (hs : inputModule D = inputModule B) (raw : List ℤ) :
    original ((intRows B,intRows D),raw)=List.ofFn (originalWord B D (fun i => raw[i.val]?.getD 0)) := by
  let z := fun i : Fin n => raw[i.val]?.getD 0
  obtain ⟨e,he⟩ := rebase_exists D B hD hB hs
  have hr : (List.range (intRows D).length).map (fun i => raw[i]?.getD 0)=List.ofFn z := by
    apply List.ext_getElem <;> simp [intRows,z]
  have ht : transpose (intRows B)=intRows B.transpose := by
    exact transpose_input_rows B
  have hp (j : Fin n) : (∑ i, (B.transpose i j:ℚ)*(e z i:ℚ)) = (D.mulVec z j : ℚ) := by
    rw [←he z]
    simp [Matrix.mulVec,dotProduct,Int.cast_sum,Int.cast_mul]
  have hb' : B.transpose.det ≠ 0 := by rwa [Matrix.det_transpose]
  simp only [original,hr,ht,ShortProbe.matrixApply_rows, ShortProbe.lift_eq _ hb' _ _ hp, List.map_ofFn,Function.comp_def,ShortProbe.nearest_int,originalWord_eq B D hB e he]
  rfl

def width (c : Cfg) : ℚ :=
  let x := initialWidth (c.1.1.2,c.1.1.2.length+1)
  let y := c.1.2*(c.1.1.2.length+2:ℕ)
  if y ≤ x then x else y

@[fun_prop] theorem width_poly : Poly width := by unfold width; fun_prop

def settings (c : Cfg) : Setup := ((c.1.1.2,width c),c.2)

@[fun_prop] theorem settings_poly : Poly settings := by unfold settings; fun_prop

def row (v : Cfg × List Bool) : List ℤ := original (v.1.1.1,sample (settings v.1,v.2))

@[fun_prop] theorem row_poly : Poly row := by unfold row;fun_prop

def rowWord (v : Cfg × List Bool) : Str := serializeVector (row v)

@[fun_prop] theorem rowWord_poly : Poly rowWord := by unfold rowWord;fun_prop

noncomputable section

def cfg {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (a : List Unit) : Cfg :=
  (((intRows B,intRows D),r),a)

theorem settings_exact {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (a : List Unit) :
    settings (cfg B D r a) = setup D (max (RationalGramSchmidt.initialWidth D (n+1:ℕ)) (r * (famσ n:ℚ))) a := by
  unfold settings cfg width setup
  simp only [intRows,List.length_ofFn]
  rw [initialWidth_input D]
  simp only [famσ,famL,max_def]
  split <;> split <;> first |rfl |congr 3 <;> linarith

theorem row_exact {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (hD : D.det≠0)
    (hs : inputModule D=inputModule B) (r : ℚ) (a : List Unit) (t : Str) :
    row (cfg B D r a,t)=List.ofFn (originalWord B D (fun i =>
      (sample (settings (cfg B D r a),t))[i.val]?.getD 0)) := by
  apply original_exact B D hB hD hs

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule110

/- Helper module Layout. -/
section P2MDyadicModule111

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 12000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2NativeAffineEmitter

def skipU (w : Str) : Str := (readUnary w).2

@[fun_prop] theorem skipU_poly : Poly skipU := by
  have h := Poly.comp (f:=Prod.snd) (g:=readUnary) Poly.snd readUnary_poly
  exact h

theorem units_exact (s : List Unit) : List.replicate s.length ()=s := by
  symm
  exact List.eq_replicate_iff.mpr ⟨rfl,fun _ _ => Subsingleton.elim _ _⟩

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end P2MDyadicModule111

/- Helper module PoolProgram. -/
section P2MDyadicModule112

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QAlgorithms.Complexity Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2PlatformSerialization

open GaussianRandomizedRounding.Wide.Coherent (readRational rationalCode readRational_append)

open RationalGramSchmidt.Native.ExactWide TM2Boolean.PolyProgramCircuit QMCNumericRuntime

/-- The public row header ends immediately before the fair tape. -/
def header (c : Cfg) : Str := serializeMatrix c.1.1.1 ++ serializeMatrix c.1.1.2 ++ rationalCode c.1.2 ++ lengthToken c.2

@[fun_prop] theorem header_poly : Poly header := by unfold header; fun_prop

def parse (w : Str) : Cfg × Str :=
  let b := readMatrix w
  let d := readMatrix b.1
  let r := readRational d.1
  ((((b.2,d.2),r.2),unarySlots r.1),FineCodec.skipU r.1)

@[fun_prop] theorem parse_poly : Poly parse := by unfold parse; dsimp only; fun_prop

theorem parse_header (c : Cfg) (t : Str) : parse (header c ++ t)=(c,t) := by
  rcases c with ⟨⟨⟨b,d⟩,r⟩,a⟩
  simp only [parse,header,List.append_assoc,NativePaddedWords.readMatrix_serialized,
    FineCodec.skipU,readRational_append,lengthToken_eq,readUnary_append,unarySlots_append]
  exact congrArg (fun a' => ((((b,d),r),a'),t)) (FineCodec.units_exact a)

def one (w : Str) := rowWord (parse w)

@[fun_prop] theorem one_poly : Poly one := by unfold one;fun_prop

noncomputable def rowProgram : PolyProgram id id one := Integration9_9.LARCoinLayout.rawPolyProgram one_poly

/-- The unary width is identical for every fair tape for a fixed public configuration. -/
noncomputable def slot (c : Cfg) : List Unit :=
  (request rowProgram (header c ++ (ticks (settings c)).map (fun _ => false))).2.1

@[fun_prop] theorem slot_poly : Poly slot := by unfold slot;fun_prop

theorem row_fits (c : Cfg) (t : Str) (ht : t.length=(ticks (settings c)).length) :
    (rowWord (c,t)).length ≤ (slot c).length := by
  have h := actualOutput_length_lt_capacity rowProgram (header c ++ t)
  change (rowWord (parse (header c ++ t))).length<_ at h
  rw [parse_header] at h
  simpa only [slot,request,List.length_replicate,List.length_append,List.length_map,capacityPolynomial_eval,ht] using h.le

def slice (v : (ℕ × Str) × ℕ) : Str := (v.1.2.drop (v.2*v.1.1)).take v.1.1

@[fun_prop] theorem slice_poly : Poly slice := by
  have hd : Poly (fun v : (ℕ × Str) × ℕ => v.1.2.drop (v.2*v.1.1)) := Poly.comp parser_drop_poly (g:=fun v : (ℕ × Str) × ℕ => (v.1.2,v.2*v.1.1)) (by fun_prop)
  unfold slice
  exact Poly.comp parser_take_poly (Poly.pair hd (by fun_prop))

abbrev Batch := Cfg × List Unit

def tape (v : Batch) : List Unit := v.2.flatMap (fun _ => ticks (settings v.1))

@[fun_prop] theorem tape_poly : Poly tape := by unfold tape;fun_prop

@[simp] theorem tape_length (v : Batch) : (tape v).length=v.2.length*(ticks (settings v.1)).length := by
  simp only [tape,List.length_flatMap,List.map_const',List.sum_replicate,smul_eq_mul]

noncomputable def run (v : Batch × Str) : Str := (List.range v.1.2.length).flatMap (fun i =>
  NativePaddedWords.current (slot v.1.1,rowWord (v.1.1,slice (((ticks (settings v.1.1)).length,v.2),i))))

@[fun_prop] theorem run_poly : Poly run := by
  have hi : Poly (fun v : Batch × Str => List.range v.1.2.length) :=
    Poly.comp (f:=fun xs : List Unit => List.range xs.length) Poly.list_indices (by fun_prop)
  unfold run
  fun_prop

def batchHeader (v : Batch) := lengthToken v.2 ++ header v.1

@[fun_prop] theorem batchHeader_poly : Poly batchHeader := by unfold batchHeader;fun_prop

noncomputable def raw (w : Str) : Str :=
  let d := parse (FineCodec.skipU w)
  run ((d.1,unarySlots w),d.2)

@[fun_prop] theorem raw_poly : Poly raw := by unfold raw; dsimp only; fun_prop

theorem raw_exact (v : Batch) (t : Str) : raw (batchHeader v ++ t)=run (v,t) := by
  rcases v with ⟨c,m⟩
  simp only [batchHeader,raw,FineCodec.skipU,List.append_assoc,lengthToken_eq,readUnary_append,unarySlots_append,parse_header,FineCodec.units_exact]

noncomputable def program : PolyProgram id id raw := Integration9_9.LARCoinLayout.rawPolyProgram raw_poly

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule112

/- Helper module Solutions.RegevBridgeCoherentPublicPreparation. -/
section P2MDyadicModule113

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

def outputBits (n : ℕ) (word : Str) : Bits (capacity P n) := fun i => wordExtension (f word) i.val

theorem masked_zero (n : ℕ) (word : Str) :
    (fun data => coinZero (capacity P n) (CoherentClassicalOracle.maskedAt P n word data))=
      basis (outputBits P n word) := by
  funext data
  have hh : CoherentClassicalOracle.maskedAt P n word data=(fun _ => false) ↔ data=outputBits P n word := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      change xor (data i) (outputBits P n word i)=false at hi
      exact (show ∀ a b : Bool,xor a b=false → a=b by decide) _ _ hi
    · rintro rfl
      funext i
      simp only [CoherentClassicalOracle.maskedAt,outputBits,Bool.xor_self]
  simp only [coinZero,basis,hh]

theorem assemble_basis {W k : ℕ} (work : Bits W) (data : Bits k) :
    assembleMap W k (tensor (basis data) work)=basis (Fin.append work data) := by
  funext x
  have hx : x=Fin.append (fun j => x (j.castAdd k)) (fun j => x (Fin.natAdd W j)) :=
    ((qubitsAppendEquiv W k).symm_apply_apply x).symm
  rw [hx]
  simp only [assembleMap,LinearMap.coe_mk,AddHom.coe_mk,tensor,basis,
    Fin.append_left,Fin.append_right,CoherentXorCopy.append_eq_iff]
  by_cases hd : (fun j => x (Fin.natAdd W j))=data <;>
    by_cases hw : (fun j => x (j.castAdd k))=work <;> simp [hd,hw]

def originalBasis (n : ℕ) (word : Str) : Bits (width P n+capacity P n) := fun i => wordExtension word i.val

theorem initial_zero (n : ℕ) (word : Str) (hlen : word.length=n) :
    CoherentClassicalOracle.inputAt P n word (coinZero (capacity P n))=basis (originalBasis P n word) := by
  change assembleMap _ _ (tensor (basis (fun _ => false)) (CoherentClassicalOracle.initialWork P n word))=_
  rw [assemble_basis]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left,CoherentClassicalOracle.initialWork,originalBasis,Fin.val_castAdd]
  · intro j
    simp only [Fin.append_right,originalBasis,Fin.val_natAdd]
    change false=wordExtension word (width P n+j.val)
    symm
    apply wordExtension_after
    unfold width
    omega

def copiedBasis (n : ℕ) (word : Str) : Bits (width P n+capacity P n) :=
  Fin.append (CoherentClassicalOracle.initialWork P n word) (outputBits P n word)

theorem actual_copy_preparation (n : ℕ) (word : Str) (hlen : word.length=n) :
    runLayered (CoherentClassicalOracle.fullCircuit P n) (basis (originalBasis P n word))=
      basis (copiedBasis P n word) := by
  rw [←initial_zero P n word hlen,CoherentClassicalOracle.fullCircuit_exact_at P n word hlen,masked_zero]
  exact assemble_basis _ _

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

end P2MDyadicModule113

/- Helper module Tickets. -/
section P2MDyadicModule114

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentComputeUncompute

noncomputable section

def coinWires (h k s a : ℕ) : Fin k ↪ Fin (((h+k)+s)+a) where
  toFun i := ((Fin.natAdd h i).castAdd s).castAdd a
  inj' := by intro i j e;apply Fin.ext;have z:=congrArg Fin.val e;simp only [Fin.val_castAdd,Fin.val_natAdd] at z;omega

def frame {h k s a : ℕ} (p : Bits h) (t : Bits k) (w : Bits s) (y : Bits a) : Bits (((h+k)+s)+a) :=
  Fin.append (Fin.append (Fin.append p t) w) y

theorem frame_on {h k s a : ℕ} (p : Bits h) (t : Bits k) (w : Bits s) (y : Bits a) :
    (wireBitsEquiv (coinWires h k s a) (frame p t w y)).1 = t := by
  funext i
  change Fin.append (Fin.append (Fin.append p t) w) y (((Fin.natAdd h i).castAdd s).castAdd a)=t i
  simp

theorem frame_off {h k s a : ℕ} (p : Bits h) (t u : Bits k) (w : Bits s) (y : Bits a) :
    (wireBitsEquiv (coinWires h k s a) (frame p t w y)).2 =
      (wireBitsEquiv (coinWires h k s a) (frame p u w y)).2 := by
  funext z
  rcases z with ⟨i,hi⟩
  change frame p t w y i=frame p u w y i
  unfold frame
  induction i using Fin.addCases with
  | right j => simp
  | left j =>
    simp only [Fin.append_left]
    induction j using Fin.addCases with
    | right j => simp
    | left j =>
      simp only [Fin.append_left]
      induction j using Fin.addCases with
      | left j => simp
      | right j => exact (hi ⟨j,rfl⟩).elim

theorem prepare {h k s a : ℕ} (p : Bits h) (w : Bits s) (y : Bits a) :
    runLayered (relocateCircuit (coinWires h k s a) (coinCircuit k)) (basis (frame p (0:Bits k) w y)) =
      ∑ t : Bits k,coinAmplitude k • basis (frame p t w y) := by
  let f := coinWires h k s a
  let o := (wireBitsEquiv f (frame p (0:Bits k) w y)).2
  have hb (t : Bits k) : initializedWires f o (basis t) = basis (frame p t w y) := by
    have e := CoherentPublicPreparation.initializedWires_basis f (frame p t w y)
    rw [frame_on,frame_off p t 0 w y] at e
    exact e
  rw [←hb 0]
  change runLayered (relocateCircuit f (coinCircuit k)) (initializedWires f o (coinZero k))=_
  rw [relocateCircuit_initialized,coinCircuit_uniform]
  have he : (fun _ : Bits k => coinAmplitude k) = ∑ t : Bits k,coinAmplitude k • basis t := by
    funext x
    simp [Finset.sum_apply,Pi.smul_apply,basis]
  rw [he,initializedWires_eq_embedding,map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul,←initializedWires_eq_embedding, hb]

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule114

/- Helper module RunPool. -/
section P2MDyadicModule115

set_option autoImplicit false

set_option maxHeartbeats 1800000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open NativeWordLayout TM2Boolean TM2Boolean.PolyProgramCircuit

noncomputable section

abbrev machine (n : ℕ) := (compiled program n).ops.length+1

abbrev N (h k : ℕ) := ((h+k)+machine (h+k))+capacity program (h+k)

def circuit (h k : ℕ) : Layered (N h k) :=
  List.append (α:=List (Instr (N h k))) (relocateCircuit (coinWires h k (machine (h+k)) (capacity program (h+k))) (coinCircuit k))
    (CoherentClassicalOracle.fullCircuit program (h+k) : Layered (N h k))

def clean {h k : ℕ} (p : Bits h) (t : Bits k) : Bits (N h k) := frame p t 0 0

def withWord {h k : ℕ} (p : Bits h) (t : Bits k) (out : Str) : Bits (N h k) :=
  frame p t 0 (fun i => wordExtension out i.val)

theorem copy_frame {h k : ℕ} (p : Bits h) (t : Bits k) :
    runLayered (CoherentClassicalOracle.fullCircuit program (h+k)) (basis (clean p t)) =
      basis (withWord p t (raw (List.ofFn (Fin.append p t)))) := by
  let w := List.ofFn (Fin.append p t)
  have hlen : w.length=h+k := List.length_ofFn
  have hz (i : ℕ) (hi : h+k ≤ i) : wordExtension w i=false := wordExtension_after _ _ (by omega)
  have hv (i : Fin (h+k)) : wordExtension w i.val=Fin.append p t i := by simp only [w,wordExtension,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  have hin : CoherentPublicPreparation.originalBasis program (h+k) w=clean p t := by
    change (fun i : Fin (((h+k)+machine (h+k))+capacity program (h+k)) => wordExtension w i.val)=frame p t 0 0
    funext i
    induction i using Fin.addCases with
    | right i => simp only [frame,Fin.append_right,Fin.val_natAdd];apply hz;omega
    | left i =>
      simp only [frame,Fin.append_left,Fin.val_castAdd]
      induction i using Fin.addCases with
      | right i => simp only [Fin.val_natAdd,Fin.append_right];apply hz;omega
      | left i => simpa using hv i
  have hout : CoherentPublicPreparation.copiedBasis program (h+k) w=withWord p t (raw w) := by
    unfold CoherentPublicPreparation.copiedBasis withWord frame
    apply congrArg₂ Fin.append _ rfl
    funext i
    induction i using Fin.addCases with
    | left i => simpa only [CoherentClassicalOracle.initialWork,Fin.val_castAdd,Fin.append_left] using hv i
    | right i => simp only [CoherentClassicalOracle.initialWork,Fin.val_natAdd,Fin.append_right];apply hz;omega
  rw [←hin]
  exact (CoherentPublicPreparation.actual_copy_preparation program _ w hlen).trans (congrArg basis hout)

theorem run_append {n : ℕ} (u v : Layered n) (a : QState n) : runLayered (List.append u v) a=runLayered v (runLayered u a) := List.foldl_append

theorem circuit_amplitudes (v : Batch) :
    let p := toBits (batchHeader v)
    let k := (tape v).length
    runLayered (circuit (batchHeader v).length k) (basis (clean p (0:Bits k))) =
      ∑ t : Bits k,coinAmplitude k • basis (withWord p t (run (v,List.ofFn t))) := by
  dsimp only
  unfold circuit clean
  rw [run_append]
  change runLayered (CoherentClassicalOracle.fullCircuit program _) (runLayered _ (basis (frame _ _ _ _)))=_
  rw [prepare,←runLayeredLinearMap_apply,map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul,runLayeredLinearMap_apply]
  change _ • runLayered _ (basis (clean _ t))=_
  rw [copy_frame,List.ofFn_fin_append]
  have hp : List.ofFn (toBits (batchHeader v))=batchHeader v := List.ofFn_get _
  rw [hp,raw_exact]

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule115

/- Helper module EmitPool. -/
section P2MDyadicModule116

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization TM2Boolean.PolyProgramCircuit NativeWordLayout

noncomputable section

def decodeWord (w : Str) : GateCode :=
  let tail := FineCodec.skipU w
  ((unarySlots w).length,(unarySlots tail).length,(unarySlots (FineCodec.skipU tail)).length)

@[fun_prop] theorem decodeWord_poly : Poly decodeWord := by unfold decodeWord; fun_prop

theorem decodeWord_exact {n : ℕ} (g : Instr n) : decodeWord (encInstr g)=encodeInstr g := by
  have one (n : ℕ) : unarySlots (encNat n)=List.replicate n () := by simpa using unarySlots_append n []
  have skip (n : ℕ) : FineCodec.skipU (encNat n)=[] := by simpa [FineCodec.skipU] using congrArg Prod.snd (readUnary_append n [])
  cases g <;> simp only [encInstr,encodeInstr,decodeWord,List.append_assoc,FineCodec.skipU,readUnary_append,
    unarySlots_append,List.length_replicate,one] <;>
    simp [show ∀ n, (readUnary (encNat n)).2=[] from skip,unarySlots]

def clock (v : Batch) := (batchHeader v).map (fun _ => true) ++ (tape v).map (fun _ => true)

@[fun_prop] theorem clock_poly : Poly clock := by unfold clock;fun_prop

theorem clock_exact (v : Batch) : clock v=unary ((batchHeader v).length+(tape v).length) := by
  simp only [clock,List.map_const',unary,List.replicate_add]

def outputOffset (v : Batch) := machineWidth program (clock v)

@[fun_prop] theorem outputOffset_poly : Poly outputOffset := by unfold outputOffset;fun_prop

theorem outputOffset_exact (v : Batch) : outputOffset v=NativeWordLayout.width program ((batchHeader v).length+(tape v).length) := by rw [outputOffset,clock_exact,machineWidth_eq]

def had (v : Batch) : List GateCode := (List.range (tape v).length).map (fun i => (0,(batchHeader v).length+i,0))

@[fun_prop] theorem had_poly : Poly had := by
  have hi : Poly (fun v : Batch => List.range (tape v).length) := Poly.comp (f:=fun xs : List Unit => List.range xs.length) Poly.list_indices tape_poly
  unfold had;fun_prop

def emit (v : Batch) : List GateCode := had v ++ (CoherentClassicalOracle.publicLayers program (clock v)).flatMap (fun l => l.map decodeWord)

attribute [local irreducible] CoherentClassicalOracle.publicLayers program

@[fun_prop] theorem emit_poly : Poly emit := by
  have hp := Poly.comp (CoherentClassicalOracle.publicLayers_poly program) clock_poly
  apply Poly.comp Poly.list_append (Poly.pair had_poly _)
  apply Poly.list_flatMap _ hp
  apply Poly.list_map (Poly.comp decodeWord_poly Poly.snd) Poly.snd

theorem flatSingles {α : Type*} {k : ℕ} (f : Fin k → α) :
    (List.ofFn (fun i => [f i])).flatten=List.ofFn f := by
  induction k with
  | zero => simp
  | succ k ih => simp only [List.ofFn_succ,List.flatten_cons,List.singleton_append,ih]

theorem had_exact (v : Batch) :
    had v=(relocateCircuit (coinWires (batchHeader v).length (tape v).length (machine ((batchHeader v).length+(tape v).length))
        (capacity program ((batchHeader v).length+(tape v).length))) (coinCircuit (tape v).length)).flatten.map encodeInstr := by
  rw [coinCircuit_direct]
  unfold had relocateCircuit
  simp only [List.map_ofFn,Function.comp_def,List.map_cons,List.map_nil,flatSingles,List.map_ofFn]
  apply List.ext_getElem <;> simp only [List.length_map,List.length_range,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn]
  intro i _ _;rfl

theorem flatAppend {X Y : Type*} (xs ys : List (List X)) (f : X → Y) : (List.append xs ys).flatten.map f=xs.flatten.map f++ys.flatten.map f := by
  change (xs++ys).flatten.map f=_
  simp only [List.flatten_append,List.map_append]

theorem emit_exact (v : Batch) : emit v=(circuit (batchHeader v).length (tape v).length).flatten.map encodeInstr := by
  rw [emit,had_exact,clock_exact,CoherentClassicalOracle.publicLayers_exact]
  unfold circuit
  rw [flatAppend]
  simp only [List.flatMap_def,List.flatten_append,List.map_append,List.map_flatten,List.map_map,Function.comp_def,decodeWord_exact]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule116

/- Helper module ReadSlots. -/
section P2MDyadicModule117

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms.Complexity AFT RationalGramSchmidt.Native.ExactWide GaussianRandomizedRounding

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

noncomputable section

def split (m k : ℕ) : Bits (m*k) ≃ (Fin m → Bits k) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry (Fin m) (Fin k) Bool)

theorem slice_split {m k : ℕ} (t : Bits (m*k)) (i : Fin m) :
    slice ((k,List.ofFn t),i.val) = List.ofFn ((split m k t) i) := by
  have hle : i.val*k+k ≤ m*k := by
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ i.isLt
  apply List.ext_getElem
  · simp only [slice,List.length_take,List.length_drop,List.length_ofFn]; omega
  · intro j h₁ h₂
    have hj : j<k := by simpa using h₂
    simp only [slice,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    change t _=t (finProdFinEquiv (i,⟨j,hj⟩))
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

def code (c : Cfg) (t : Bits (ticks (settings c)).length) : Str :=
  NativePaddedWords.current (slot c,rowWord (c,List.ofFn t))

theorem code_decodes (c : Cfg) (t : Bits (ticks (settings c)).length) (rest : Str) :
    (readVector (code c t ++ rest)).2 = row (c,List.ofFn t) := by
  unfold code
  rw [NativePaddedWords.current_eq _ _ (row_fits c (List.ofFn t) List.length_ofFn)]
  rw [List.append_assoc]
  exact congrArg Prod.snd (NativePaddedWords.readVector_serialized _ _)

@[simp] theorem code_length (c : Cfg) (t : Bits (ticks (settings c)).length) : (code c t).length=(slot c).length := NativePaddedWords.current_length _ _

theorem run_tape (v : Batch) (t : Bits (v.2.length * (ticks (settings v.1)).length)) :
    run (v,List.ofFn t)= (List.ofFn (fun i => code v.1 ((split _ _ t) i))).flatten := by
  unfold run
  rw [List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have hj : j<v.2.length := by simpa using h₂
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [slice_split t ⟨j,hj⟩]
    rfl

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule117

/- Helper module PoolBorn. -/
section P2MDyadicModule118

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport AFT

open TM2Boolean.PolyProgramCircuit RationalGramSchmidt.Native.ExactWide

noncomputable section

def answer (v : Batch) (t : Bits (tape v).length) := withWord (toBits (batchHeader v)) t (run (v,List.ofFn t))

def outcomes (v : Batch) : Bits (tape v).length ↪ Bits (N (batchHeader v).length (tape v).length) where
  toFun := answer v
  inj' := by
    intro t u h
    let w := coinWires (batchHeader v).length (tape v).length (machine ((batchHeader v).length+(tape v).length)) (capacity program ((batchHeader v).length+(tape v).length))
    have he := congrArg (fun x => (wireBitsEquiv w x).1) h
    simpa only [answer,withWord,w,frame_on] using he

theorem weighted {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    (e : I ↪ X) (ψ : I → ℂ) (f : X → ℝ) :
    (∑ x,‖basisEmbedding e ψ x‖^2*f x)=∑ i, ‖ψ i‖^2*f (e i) := by
  classical
  calc
    _ = ∑ x∈Finset.univ.image e, ‖basisEmbedding e ψ x‖^2*f x := by
      symm;apply Finset.sum_subset (Finset.subset_univ _);intro x _ hx
      have hn : x ∉ Set.range e := by rintro ⟨i,rfl⟩;exact hx (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      simp [basisEmbedding_outside e ψ x hn]
    _ = ∑ i, ‖basisEmbedding e ψ (e i)‖^2*f (e i) := Finset.sum_image (fun _ _ _ _ hi => e.injective hi)
    _ = _ := by simp only [basisEmbedding_at]

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule118

/- Helper module FromZero. -/
section P2MDyadicModule119

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean.PolyProgramCircuit

noncomputable section

def headWire (h k : ℕ) : Fin h ↪ Fin (N h k) where
  toFun i := ((i.castAdd k).castAdd (machine (h+k))).castAdd (capacity program (h+k))
  inj' := by intro i j he;apply Fin.ext; exact congrArg (fun x : Fin (N h k) => x.val) he

def sites {h k : ℕ} (p : Bits h) : List (Fin (N h k)) := ((List.finRange h).filter p).map (headWire h k)

theorem flips {n : ℕ} (xs : List (Fin n)) (hn : xs.Nodup) (a : Bits n) :
    reversibleAction (xs.map ReversibleGate.flip) a=fun i => xor (a i) (decide (i ∈ xs)) := by
  induction xs generalizing a with
  | nil => simp [reversibleAction]
  | cons x xs ih =>
    change reversibleAction (xs.map ReversibleGate.flip) ((ReversibleGate.flip x).act a)=_
    rw [ih (List.nodup_cons.mp hn).2]
    funext i
    by_cases e : i=x
    · subst i;simp [ReversibleGate.act,(List.nodup_cons.mp hn).1]
    · simp only [ReversibleGate.act,Function.update_of_ne e,List.mem_cons,e,false_or]

def writeHeader {h k : ℕ} (p : Bits h) : Layered (N h k) := compileReversible ((sites (k:=k) p).map ReversibleGate.flip)

theorem sites_iff {h k : ℕ} (p : Bits h) (i : Fin (N h k)) : i∈sites p ↔ ∃ j, p j=true ∧ headWire h k j=i := by
  simp [sites]

theorem header_state {h k : ℕ} (p : Bits h) :
    (fun i => decide (i∈sites (k:=k) p))=clean p (0:Bits k) := by
  funext i
  simp only [sites_iff p i]
  induction i using Fin.addCases with
  | right i =>
    have he (j : Fin h) : headWire h k j≠Fin.natAdd _ i := by intro eq;have hh:=congrArg Fin.val eq;change j.val=h+k+machine (h+k)+i.val at hh;have:=j.isLt;omega
    simp [clean,frame,he];rfl
  | left i =>
    simp only [clean,frame,Fin.append_left]
    induction i using Fin.addCases with
    | right i =>
      have he (j : Fin h) : headWire h k j≠(Fin.natAdd _ i).castAdd _ := by intro eq;have hh:=congrArg Fin.val eq;change j.val=h+k+i.val at hh;have:=j.isLt;omega
      simp [he];rfl
    | left i =>
      simp only [Fin.append_left]
      induction i using Fin.addCases with
      | right i =>
        have he (j : Fin h) : headWire h k j≠((Fin.natAdd _ i).castAdd _).castAdd _ := by intro eq;have hh:=congrArg Fin.val eq;change j.val=h+i.val at hh;have:=j.isLt;omega
        simp [he];rfl
      | left i =>
        have he (j : Fin h) : headWire h k j=(((i.castAdd k).castAdd _).castAdd _) ↔ j=i := (headWire h k).injective.eq_iff
        simp [he]

theorem writeHeader_exact {h k : ℕ} (p : Bits h) : runLayered (writeHeader (k:=k) p) (basis (0:Bits (N h k))) = basis (clean p (0:Bits k)) := by
  unfold writeHeader
  have hn : (sites (k:=k) p).Nodup := ((List.nodup_finRange h).filter _).map (headWire h k).injective
  rw [CoherentXorCopy.compile_basis,flips _ hn]
  exact congrArg basis (by change (fun i => xor false (decide (i∈sites p)))=_;simpa using header_state (k:=k) p)

def loader (v : Batch) := List.append (α:=List (Instr (N (batchHeader v).length (tape v).length)))
  (writeHeader (k:=(tape v).length) (toBits (batchHeader v))) (circuit (batchHeader v).length (tape v).length)

theorem loader_exact (v : Batch) : runLayered (loader v) (basis 0)=
    ∑ t, coinAmplitude (tape v).length • basis (answer v t) := by
  rw [loader,run_append,writeHeader_exact]
  exact circuit_amplitudes v

def writeCodes (h : Str) : List GateCode := ((List.range h.length).filter (fun i => h[i]?.getD false)).map (fun i => (3,i,0))

@[fun_prop] theorem writeCodes_poly : Poly writeCodes := by
  have hi := (Poly.list_indices (α:=Bool))
  have hf : Poly (fun h : Str => (List.range h.length).filter (fun i => h[i]?.getD false)) := Poly.list_filter (by fun_prop) hi
  unfold writeCodes;fun_prop

def loaderCodes (v : Batch) := writeCodes (batchHeader v) ++ emit v

@[fun_prop] theorem loaderCodes_poly : Poly loaderCodes := by unfold loaderCodes;fun_prop

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule119

/- Helper module LoadCode. -/
section P2MDyadicModule120

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode

noncomputable section

theorem codeFlips {n : ℕ} (xs : List (Fin n)) :
  (compileReversible (xs.map ReversibleGate.flip)).flatten.map encodeInstr=xs.map (fun i => (3,i.val,0)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [compileReversible,List.map_cons,List.flatMap_cons,ReversibleGate.compile,List.cons_append,List.nil_append,List.flatten_cons,List.singleton_append,List.map_cons,encodeInstr] using congrArg (List.cons ((3,x.val,0):GateCode)) ih

theorem range_fin (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂; simp

theorem write_exact (h : Str) (k : ℕ) : writeCodes h=(writeHeader (k:=k) (toBits h)).flatten.map encodeInstr := by
  unfold writeHeader
  rw [codeFlips]
  simp only [writeCodes,range_fin h.length,List.filter_map,List.map_map,sites]
  have ht : (fun i : Fin h.length => h[i.val]?.getD false)=toBits h := by
    funext i; simp [toBits,List.getElem?_eq_getElem i.isLt]
  simp only [Function.comp_def,ht,List.map_map];rfl

theorem loaderCodes_exact (v : Batch) : loaderCodes v=(loader v).flatten.map encodeInstr := by
  rw [loaderCodes,loader,flatAppend,write_exact _ (tape v).length,emit_exact]

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule120

/- Helper module ReadActual. -/
section P2MDyadicModule121

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms.Complexity CoherentComputeUncompute RationalGramSchmidt.Native.ExactWide

open TM2Boolean TM2Boolean.PolyProgramCircuit

open Integration9_9.TM2NativeAffineEncoding

noncomputable section

attribute [local irreducible] program run tape slot

def castTape {a b : ℕ} (h : a=b) (t : Bits a) : Bits b := h ▸ t

@[simp] theorem ofFn_cast {a b : ℕ} (h : a=b) (t : Bits a) : List.ofFn (castTape h t)=List.ofFn t := by subst b;rfl

def castEquiv {a b : ℕ} (h : a=b) : Bits a ≃ Bits b := h ▸ Equiv.refl _

theorem castEquiv_apply {a b : ℕ} (h : a=b) (t : Bits a) : castEquiv h t=castTape h t := by subst b;rfl

def splitTape (v : Batch) : Bits (tape v).length ≃ (Fin v.2.length → Bits (ticks (settings v.1)).length) :=
  (castEquiv (tape_length v)).trans (split _ _)

theorem split_cast (v : Batch) (t : Bits (tape v).length) : splitTape v t=split _ _ (castTape (tape_length v) t) := by
  simp only [splitTape,Equiv.trans_apply,castEquiv_apply]

theorem runs (v : Batch) (t : Bits (tape v).length) :
    run (v,List.ofFn t) = (List.ofFn (fun i => code v.1 ((splitTape v t) i))).flatten := by
  rw [split_cast]
  simpa only [ofFn_cast] using run_tape v (castTape (tape_length v) t)

theorem select_cell {m : ℕ} (l : ℕ) (cells : Fin m → Str) (hc : ∀ i,(cells i).length=l) (tail : Str) (i : Fin m) :
    slice ((l,(List.ofFn cells).flatten++tail),i.val)=cells i := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    rw [List.ofFn_succ,List.flatten_cons,List.append_assoc]
    induction i using Fin.cases with
    | zero => simp only [slice,Fin.val_zero,Nat.zero_mul,List.drop_zero,List.take_left' (hc 0)]
    | succ j =>
      have hd : (cells 0 ++ (List.ofFn (fun i => cells i.succ)).flatten ++ tail).drop ((j.val+1)*l) =
          ((List.ofFn (fun i => cells i.succ)).flatten ++ tail).drop (j.val*l) := by
        rw [List.append_assoc,List.drop_append,hc,Nat.add_mul,Nat.one_mul]
        simp [List.drop_eq_nil_of_le (by simp [hc] : (cells 0).length≤j.val*l+l)]
      rw [List.append_assoc] at hd
      change ((cells 0 ++ ((List.ofFn (fun i => cells i.succ)).flatten ++ tail)).drop ((j.val+1)*l)).take l=_
      rw [hd]
      exact ih (fun i => cells i.succ) (fun i => hc i.succ) j

def outputData (v : Batch) (x : Bits (N (batchHeader v).length (tape v).length)) : Str :=
  List.ofFn (fun i : Fin (capacity program ((batchHeader v).length+(tape v).length)) => x (Fin.natAdd _ i))

theorem output_tail (v : Batch) (t : Bits (tape v).length) :
    ∃ tail, outputData v (answer v t) = run (v,List.ofFn t)++tail := by
  let w := batchHeader v ++ List.ofFn t
  have hl : w.length=(batchHeader v).length+(tape v).length := by simp [w]
  let cap := capacity program ((batchHeader v).length+(tape v).length)
  refine ⟨List.replicate (cap-(raw w).length) false,?_⟩
  have h := paddedOutput_eq_append program w
  unfold paddedOutput at h
  rw [hl] at h
  change List.ofFn (fun i : Fin cap => Fin.append _ (fun j : Fin cap => wordExtension (run (v,List.ofFn t)) j.val) (Fin.natAdd _ i))=_
  simp only [Fin.append_right]
  rw [←raw_exact]
  exact h

def rowAt (v : Batch) (x : Bits (N (batchHeader v).length (tape v).length)) (i : Fin v.2.length) : List ℤ :=
  (readVector (slice (((slot v.1).length,outputData v x),i.val))).2

theorem rowAt_answer (v : Batch) (t : Bits (tape v).length) (i : Fin v.2.length) :
    rowAt v (answer v t) i=row (v.1,List.ofFn (splitTape v t i)) := by
  obtain ⟨tail,ht⟩ := output_tail v t
  rw [rowAt,ht,runs,select_cell _ _ (fun j => code_length _ _)]
  simpa using code_decodes v.1 (splitTape v t i) []

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule121

/- Helper module PoolTuple. -/
section P2MDyadicModule122

set_option autoImplicit false

set_option maxHeartbeats 900000

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

noncomputable section

variable {X Y : Type*}

def tuple (p : PMF X) : (m : ℕ) → PMF (Fin m → X)
  | 0 => PMF.pure (fun i => i.elim0)
  | m+1 => p.bind (fun z => (tuple p m).map (Fin.cons z))

theorem tuple_weight (p : PMF X) (m : ℕ) (v : Fin m → X) :
    tuple p m v = ∏ i, p (v i) := by
  classical
  induction m with
  | zero =>
    have he : (fun i : Fin 0 => i.elim0 (α:=X))=v := Subsingleton.elim _ _
    simp [tuple,he]
  | succ m ih =>
    rw [tuple,PMF.bind_apply,Fin.prod_univ_succ]
    rw [tsum_eq_single (v 0)]
    · congr 1
      rw [PMF.map_apply,tsum_eq_single (Fin.tail v)]
      · simp [Fin.cons_self_tail,ih,Fin.tail]
      · intro ys hys
        have hn : Fin.cons (v 0) ys≠v := by intro h;apply hys;rw [←h];simp
        simp [hn,Ne.symm hn]
    · intro x hx
      have hs : (PMF.map (Fin.cons x) (tuple p m)) v=0 := by
        rw [PMF.map_apply]
        apply ENNReal.tsum_eq_zero.mpr
        intro ys;have hh : Fin.cons x ys≠v := by intro he;apply hx; simpa using congrFun he 0
        simp [hh,Ne.symm hh]
      rw [hs,mul_zero]

theorem tuple_real (p : PMF X) (m : ℕ) (v : Fin m → X) :
    (tuple p m v).toReal=∏ i,(p (v i)).toReal := by rw [tuple_weight,ENNReal.toReal_prod]

theorem eval_succ (p : PMF X) (m : ℕ) (f : Test (Fin (m+1)→X)) :
    evaluate (tuple p (m+1)) f =
      evaluate p (fun z => ⟨evaluate (tuple p m) (push (fun v : Fin m → X => Fin.cons z v) f),evaluate_range _ _⟩) := by
  rw [tuple,eval_bind]
  congr 1;funext z;exact Subtype.ext (eval_map _ _ _)

theorem tuple_error (p q : PMF X) (d : ℝ) (h : ∀ f, |evaluate p f-evaluate q f|≤d) :
    ∀ m (f : Test (Fin m→X)), |evaluate (tuple p m) f-evaluate (tuple q m) f| ≤ m*d := by
  intro m
  induction m with
  | zero => intro f;simp [tuple]
  | succ m ih =>
    intro f
    let A (p : PMF X) : Test X := fun x => ⟨evaluate (tuple p m) (push (fun v : Fin m → X => Fin.cons x v) f),evaluate_range _ _⟩
    rw [eval_succ,eval_succ]
    change |evaluate p (A p)-evaluate q (A q)|≤_
    calc _ ≤ |evaluate p (A p)-evaluate q (A p)|+|evaluate q (A p)-evaluate q (A q)| := abs_sub_le _ _ _
         _ ≤ d+m*d := add_le_add (h _) (eval_difference q (A p) (A q) _ (fun x => ih _))
         _ = _ := by push_cast;ring

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule122

/- Helper module Ideal. -/
section P2MDyadicModule123

set_option autoImplicit false

set_option maxHeartbeats 1800000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms.Complexity AFT AFT.RationalNumerics GaussianRandomizedRounding IntegerBasis RegevSketch

open RationalGramSchmidt RationalGramSchmidt.Native RationalGramSchmidt.Native.ExactWide GaussianIteration

noncomputable section

variable {n : ℕ}

attribute [local irreducible] row cfg settings ticks sample

abbrev start (D : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) : ℚ := max (RationalGramSchmidt.initialWidth D (n+1:ℕ)) (r*(famσ n:ℚ))

abbrev cost (n a : ℕ) : ℝ := n*Wide.sampleError a + 4*((n:ℝ)*initialThetaBudget (n+1))

def coeff (n : ℕ) (c : Cfg) (t : Str) : Fin n → ℤ := fun i => (row (c,t))[i.val]?.getD 0

def observe {O : Type*} [Fintype O] (s : Setup) (ch : Str → FiniteDist O) : FiniteDist O := (FiniteDist.uniform (Bits (ticks s).length)).mix (fun t => ch (List.ofFn t))

theorem channel {O : Type*} [Fintype O] (B D : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det≠0) (hD : D.det≠0) (hs : inputModule D=inputModule B) (hn : 1 ≤ n)
    (r : ℚ) (a : List Unit) (ch : (Fin n → ℤ) → FiniteDist O) :
    let c := cfg B D r a
    ∃ ideal : FiniteDist O, (∀ o, ideal.weight o=∑' z, coefficientMass B (start D r) z*(ch z).weight o) ∧
      FiniteDist.TVBound ((FiniteDist.uniform (Bits (ticks (settings c)).length)).mix (fun t => ch (coeff n c (List.ofFn t)))) ideal (cost n a.length) := by
  dsimp only
  have he (t : Str) : coeff n (cfg B D r a) t=originalWord B D (fun i => (sample (settings (cfg B D r a),t))[i.val]?.getD 0) := by
    funext j;simp only [coeff,row_exact B D hB hD hs,List.getElem?_ofFn,j.isLt,↓reduceDIte,Option.getD_some]
  change ∃ ideal, _ ∧ FiniteDist.TVBound (observe (settings (cfg B D r a)) (fun t => ch (coeff n (cfg B D r a) t))) ideal _
  simp only [he]
  rw [settings_exact]
  exact scheduled_original_coordinates D B hD hB hs hn r a ch

def testCoin (q : Set.Icc (0:ℝ) 1) : FiniteDist Bool where
  weight b := if b then q.val else 1-q.val
  nonneg b := by cases b <;> simp [q.property.1,sub_nonneg.mpr q.property.2]
  sum_one := by simp [Fintype.sum_bool]

def rowPMF (n : ℕ) (c : Cfg) : PMF (Fin n → ℤ) :=
  (PMF.uniformOfFintype (Bits (ticks (settings c)).length)).map (fun t => coeff n c (List.ofFn t))

theorem row_eval (n : ℕ) (c : Cfg) (f : Test (Fin n → ℤ)) : evaluate (rowPMF n c) f =
    ((Fintype.card (Bits (ticks (settings c)).length)):ℝ)⁻¹ * ∑ t : Bits (ticks (settings c)).length, (f (coeff n c (List.ofFn t)):ℝ) := by
  rw [rowPMF,eval_map,evaluate,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [PMF.uniformOfFintype_apply,push]

theorem scheduled_mass (B D : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det≠0) (hD : D.det≠0) (hs : inputModule D=inputModule B) (hn : 1≤n)
    (r : ℚ) (a : List Unit) :
    (∀ z, 0≤coefficientMass B (start D r) z) ∧ HasSum (coefficientMass B (start D r)) 1 := by
  have h0 (z : Fin n→ℤ) : 0≤coefficientMass B (start D r) z := by
    unfold coefficientMass rhoInt; exact div_nonneg (Real.exp_pos _).le (tsum_nonneg (fun _ => (Real.exp_pos _).le))
  obtain ⟨law,hl,_⟩ := channel B D hB hD hs hn r a (fun _ => FiniteDist.uniform Unit)
  have h1 := hl ()
  simp only [FiniteDist.uniform_weight,Fintype.card_unit,Nat.cast_one,inv_one,mul_one] at h1
  have hh : law.weight () = 1 := by simpa using law.sum_one
  have ht : ∑' z, coefficientMass B (start D r) z=1 := h1.symm.trans hh
  have hs : Summable (coefficientMass B (start D r)) := by
    by_contra hn;rw [tsum_eq_zero_of_not_summable hn] at ht;norm_num at ht
  exact ⟨h0,hs.hasSum_iff.mpr ht⟩

def pmfOfWeights {X : Type*} (μ : X → ℝ) (hn : ∀ x, 0≤μ x) (hs : HasSum μ 1) : PMF X := by
  refine ⟨fun x => ENNReal.ofReal (μ x),ENNReal.summable.hasSum_iff.mpr ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable,hs.tsum_eq,ENNReal.ofReal_one]

theorem ofWeights_real {X : Type*} (μ : X → ℝ) (hn : ∀ x, 0≤μ x) (hs : HasSum μ 1) (x : X) :
    (pmfOfWeights μ hn hs x).toReal=μ x := ENNReal.toReal_ofReal (hn x)

theorem initial_pool (B D : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det≠0) (hD : D.det≠0) (hs : inputModule D=inputModule B) (hn : 1≤n)
    (r : ℚ) (a : List Unit) :
    ∃ p : PMF (Fin n→ℤ), (∀ z, (p z).toReal=coefficientMass B (start D r) z) ∧
      ∀ m (f : Test (Fin m→Fin n→ℤ)),
        |evaluate (tuple (rowPMF n (cfg B D r a)) m) f - evaluate (tuple p m) f| ≤ m * cost n a.length := by
  obtain ⟨h0,h1⟩ := scheduled_mass B D hB hD hs hn r a
  let p := pmfOfWeights _ h0 h1
  have hm (z) : (p z).toReal=coefficientMass B (start D r) z := ofWeights_real _ h0 h1 z
  refine ⟨p,hm,tuple_error _ _ _ ?_⟩
  intro f
  obtain ⟨law,hl,ht⟩ := channel B D hB hD hs hn r a (fun z => testCoin (f z))
  have he := ht {true}
  simp only [FiniteDist.event,Finset.sum_singleton,FiniteDist.mix_weight,FiniteDist.uniform_weight,testCoin,↓reduceIte,←Finset.mul_sum] at he
  rw [row_eval,evaluate]
  simp_rw [hm]
  rw [hl true] at he
  exact he

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule123

/- Helper module TupleMap. -/
section P2MDyadicModule124

set_option autoImplicit false

set_option maxHeartbeats 800000

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open GaussianIteration

noncomputable section

theorem tuple_map {A B : Type*} (p : PMF A) (g : A→B) (m : ℕ) :
    tuple (p.map g) m = (tuple p m).map (fun t i => g (t i)) := by
  induction m with
  | zero => rw [tuple,tuple,PMF.pure_map];congr 1;funext i;exact i.elim0
  | succ m ih =>
    simp only [tuple,PMF.bind_map,PMF.map_bind,ih,PMF.map_comp]
    apply congrArg (PMF.bind p)
    funext a
    apply congrArg (fun f => (tuple p m).map f)
    funext t i
    induction i using Fin.cases <;> rfl

theorem tuple_fair {A : Type*} [Fintype A] [Nonempty A] (m : ℕ) :
    tuple (PMF.uniformOfFintype A) m = PMF.uniformOfFintype (Fin m→A) := by
  ext x
  simp only [tuple_weight,PMF.uniformOfFintype_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,ENNReal.inv_pow]

theorem uniform_eval {A : Type*} [Fintype A] [Nonempty A] (f : Test A) :
    evaluate (PMF.uniformOfFintype A) f=(Fintype.card A:ℝ)⁻¹ * ∑ x, (f x:ℝ) := by
  simp only [evaluate,tsum_fintype,PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,Finset.mul_sum]

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule124

/- Helper module FirstPool. -/
section P2MDyadicModule125

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute

open RationalGramSchmidt.Native.ExactWide IntegerBasis RegevSketch GaussianIteration

noncomputable section

attribute [local irreducible] program raw row slot rowPMF tuple loader

def readPool (n : ℕ) (v : Batch) (x : Bits (N (batchHeader v).length (tape v).length)) : Fin v.2.length → Fin n → ℤ :=
  fun i j => (rowAt v x i)[j.val]?.getD 0

theorem read_answer (n : ℕ) (v : Batch) (t : Bits (tape v).length) :
    readPool n v (answer v t)=fun i => coeff n v.1 (List.ofFn (splitTape v t i)) := by
  funext i j
  simp only [readPool,coeff,rowAt_answer]

def physical (n : ℕ) (v : Batch) (f : Test (Fin v.2.length→Fin n→ℤ)) : ℝ :=
  ∑ x, ‖runLayered (loader v) (basis 0) x‖^2 * (f (readPool n v x):ℝ)

theorem physical_exact (n : ℕ) (v : Batch) (f : Test (Fin v.2.length→Fin n→ℤ)) :
    physical n v f=evaluate (tuple (rowPMF n v.1) v.2.length) f := by
  unfold physical
  rw [loader_exact]
  change (∑ x, ‖basisEmbedding (outcomes v) (fun _ => coinAmplitude (tape v).length) x‖^2 * (f (readPool n v x):ℝ))=_
  rw [weighted,←Finset.mul_sum,coinAmplitude_mass]
  unfold rowPMF
  rw [tuple_map,tuple_fair,eval_map,uniform_eval]
  rw [Fintype.card_congr (splitTape v)]
  congr 1
  apply Fintype.sum_equiv (splitTape v)
  intro t
  change (f (readPool n v (answer v t)):ℝ)=_
  rw [read_answer]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule125

/- Helper module Arena. -/
section P2MDyadicModule126

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace InfoLossLAR.WorstCase.RegevSearch.FirstPool

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator NativeWordLayout

noncomputable section

def machineSlots {f : Str→Str} (P : PolyProgram id id f) (w : Str) : List Unit :=
  w.map (fun _ => ()) ++ (generate P.machine.code P.machine.input P.machine.main P.machine.initial (request P w)).2.2.2.map (fun _ => ()) ++ [()]

@[fun_prop] theorem machineSlots_poly {f : Str→Str} (P : PolyProgram id id f) : Poly (machineSlots P) := by unfold machineSlots;fun_prop

theorem machineSlots_length {f : Str→Str} (P : PolyProgram id id f) (w : Str) : (machineSlots P w).length=machineWidth P w := by simp only [machineSlots,machineWidth,List.length_append,List.length_map,List.length_singleton]

def arenaSlots (v : Batch) := machineSlots program (clock v) ++ (request program (clock v)).2.1

@[fun_prop] theorem arenaSlots_poly : Poly arenaSlots := by unfold arenaSlots;fun_prop

theorem arenaSlots_length (v : Batch) : (arenaSlots v).length=N (batchHeader v).length (tape v).length := by
  simp only [arenaSlots,List.length_append,machineSlots_length,clock_exact,machineWidth_eq,request_unary,List.length_replicate];rfl

end

end InfoLossLAR.WorstCase.RegevSearch.FirstPool

end P2MDyadicModule126

/- Helper module BatchTrace. -/
section P2MDyadicModule127

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Batch

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute GaussianIteration

open scoped Classical BigOperators

noncomputable section

variable {s h k : ℕ} {Y : Type*}

def size (h k : ℕ) : ℕ → ℕ
  | 0 => h
  | m+1 => size h k m+k

theorem size_eq (m : ℕ) : size h k m=h+m*k := by induction m <;> simp_all [size,Nat.succ_mul,Nat.add_assoc]

def oldWire (m : ℕ) : Fin h ↪ Fin (size h k m) := Fin.castLEEmb (by rw [size_eq];omega)

def original (m : ℕ) (x : Bits (size h k m)) : Bits h := fun i => x (oldWire m i)

def carry {h n : ℕ} (w : Fin h ↪ Fin n) : Source h → Source n
  | .literal b => .literal b
  | .wire i => .wire (w i)

def pins (a : Fin k → Source h) (m : ℕ) : Fin k→Source (size h k m) :=
  fun i => carry (oldWire m) (a i)

def trace (t : Trace s h) (a : Fin k→Source h) (U : Layered k) : (m : ℕ) → Trace s (size h k m)
  | 0 => t
  | m+1 => (trace t a U m).extend (pins a m) U

def rows (out : Bits k→Y) : (m : ℕ) → Bits (size h k m) → (Fin m→Y)
  | 0, _ => Fin.elim0
  | m+1, x => Fin.cons (out (rightRegister x)) (rows out m (leftRegister x))

theorem lifted_read (a : Fin k→Source h) (m : ℕ) (x : Bits (size h k m)) :
    (fun i => (pins a m i).read x)=(fun i => (a i).read (original m x)) := by
  funext i;unfold pins;cases a i <;> rfl

theorem conditional_pins (a : Fin k→Source h) (m : ℕ) (U : Layered k) (x : Bits (size h k m)) :
    conditional (pins a m) U x=conditional a U (original m x) := by unfold conditional;congr 1;rw [lifted_read]

def cell (a : Fin k→Source h) (U : Layered k) (out : Bits k→Y) (x : Bits h) :=
  (conditional a U x).map out

theorem eval_last (p : PMF Y) (m : ℕ) (f : Test (Fin (m+1)→Y)) :
    evaluate (tuple p (m+1)) f = evaluate (tuple p m) (fun v =>
      ⟨evaluate p (fun y => f (Fin.cons y v)),evaluate_range _ _⟩) := by
  change evaluate (p.bind (fun y => (tuple p m).bind (fun v => PMF.pure (Fin.cons y v)))) f=_
  rw [PMF.bind_comm,eval_bind]
  congr 1;funext v;apply Subtype.ext
  change evaluate (p.bind (fun y => PMF.pure (Fin.cons y v))) f=_
  rw [eval_bind]
  congr 1;funext y;exact Subtype.ext (eval_pure _ _)

theorem batch_measured (t : Trace s h) (a : Fin k→Source h) (U : Layered k) (out : Bits k→Y)
    (m : ℕ) (f : Bits h → Test (Fin m→Y)) :
    evaluate (law (trace t a U m)) (fun z => f (original m z) (rows out m z)) =
    evaluate (law t) (fun x => ⟨evaluate (tuple (cell a U out x) m) (f x),evaluate_range _ _⟩) := by
  induction m with
  | zero =>
    congr 1;funext x;apply Subtype.ext
    exact (eval_pure _ _).symm
  | succ m ih =>
    let F : Bits h → Test (Fin m→Y) := fun x v => ⟨evaluate (cell a U out x) (fun y => f x (Fin.cons y v)), evaluate_range _ _⟩
    change evaluate (law ((trace t a U m).extend _ _))
      (fun z => f (original m (leftRegister z)) (Fin.cons (out (rightRegister z)) (rows out m (leftRegister z))))=_
    rw [step_eval (trace t a U m) (pins a m) U (fun z y => (original m z,Fin.cons (out y) (rows out m z))) (fun p => f p.1 p.2)]
    have eq : (fun x : Bits (size h k m) => (⟨evaluate (conditional (pins a m) U x)
        (fun y => f (original m x) (Fin.cons (out y) (rows out m x))),evaluate_range _ _⟩ : Set.Icc (0:ℝ) 1)) =
        (fun x => F (original m x) (rows out m x)) := by
      funext x;apply Subtype.ext
      change _=evaluate ((conditional a U (original m x)).map out) _
      rw [conditional_pins,eval_map];rfl
    change evaluate (law (trace t a U m)) _=_
    rw [eq,ih F]
    congr 1;funext x;apply Subtype.ext;exact (eval_last _ _ _).symm

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Batch

end P2MDyadicModule127

/- Helper module GaussianLaw. -/
section P2MDyadicModule128

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open IntegerBasis GaussianPoissonSeries RegevLWE.GaussConv RegevSketch

noncomputable section

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem coefficient_hasSum (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (r : ℝ) (hr : 0 < r) : (∀ z, 0 ≤ coefficientMass B r z) ∧ HasSum (coefficientMass B r) 1 := by
  let L := inputLattice B hB
  let E : (Fin n → ℤ) ≃ L := (integerBasis B hB).equivFun.symm.toEquiv
  have he (z : Fin n → ℤ) : (E z : V) = latVec B z := coefficient_point B hB z
  let w := fun z : Fin n → ℤ => rho r (latVec B z)
  let Z := ∑' z, w z
  have hw (z) : 0 ≤ w z := (Real.exp_pos _).le
  have hs : Summable w := by
    have h := E.summable_iff.mpr (summable_gaussian_lattice L r hr)
    simpa only [Function.comp_def, he, w] using h
  have hp : 0 < Z := hs.tsum_pos hw 0 (Real.exp_pos _)
  refine ⟨fun z => by change 0 ≤ w z / Z; exact div_nonneg (hw z) hp.le, ?_⟩
  have h : HasSum (fun z => w z / Z) (Z / Z) := hs.hasSum.div_const Z
  rwa [div_self hp.ne'] at h

def gaussian (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) (hr : 0<r) : PMF (Fin n→ℤ) :=
  FirstPool.pmfOfWeights _ (coefficient_hasSum B hB r hr).1 (coefficient_hasSum B hB r hr).2

theorem gaussian_real (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) (hr : 0<r) (z : Fin n→ℤ) :
    (gaussian B hB r hr z).toReal=coefficientMass B r z :=
  FirstPool.ofWeights_real ..

theorem gaussian_unique (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) (hr : 0<r)
    (p : PMF (Fin n→ℤ)) (hp : ∀ z,(p z).toReal=coefficientMass B r z) : p=gaussian B hB r hr := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top _) ((gaussian B hB r hr).apply_ne_top _)).mp
  exact (hp z).trans (gaussian_real B hB r hr z).symm

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule128

/- Helper module Kept. -/
section P2MDyadicModule129

set_option autoImplicit false

set_option maxHeartbeats 900000

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

noncomputable section

theorem average_kept {X : Type*} (p : PMF X) (f : Test X) (v : Set.Icc (0:ℝ) 1) (s : Finset X)
    (d : X → ℝ) (h : ∀ x∈s, |(f x:ℝ)-(v:ℝ)|≤d x) :
    |evaluate p f-(v:ℝ)| ≤ (∑ x ∈ s,(p x).toReal*d x) + (1-finiteMass p s) := by
  classical
  let w := fun x => (p x).toReal
  let a := fun x => w x*(f x:ℝ)-w x*(v:ℝ)
  let b := fun x => if x∈s then w x*(d x-1) else 0
  have hw := mass_summable p
  have hs : Summable a := (evaluate_summable p f).sub (hw.mul_right v.val).summable
  have hb : Summable b := summable_of_ne_finset_zero (s:=s) (fun x hx => by simp [b,hx])
  have he : evaluate p f-(v:ℝ)=∑' x,a x := by
    rw [(evaluate_summable p f).tsum_sub (hw.mul_right v.val).summable,tsum_mul_right,hw.tsum_eq,one_mul]
    rfl
  have hmajor (x : X) : ‖a x‖ ≤ w x+b x := by
    change |w x*(f x:ℝ)-w x*(v:ℝ)| ≤ _
    rw [←mul_sub,abs_mul,abs_of_nonneg (ENNReal.toReal_nonneg (a:=p x))]
    by_cases hx : x∈s
    · simpa only [b,if_pos hx,mul_sub,mul_one,add_sub_cancel] using mul_le_mul_of_nonneg_left (h x hx) (ENNReal.toReal_nonneg (a:=p x))
    · have hf : |(f x:ℝ)-(v:ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [(f x).property.1,v.property.2],by linarith [(f x).property.2,v.property.1]⟩
      simpa [b,hx] using mul_le_mul_of_nonneg_left hf (ENNReal.toReal_nonneg (a:=p x))
  rw [he]
  change ‖∑' x, a x‖ ≤ _
  refine (norm_tsum_le_tsum_norm hs.norm).trans ((hs.norm.tsum_le_tsum hmajor (hw.summable.add hb)).trans_eq ?_)
  rw [hw.summable.tsum_add hb,tsum_eq_sum (s:=s) (f:=b) (fun x hx => by simp [b,hx])]
  change (∑' x,(p x).toReal)+_= _
  rw [hw.tsum_eq]
  have hb' : (∑ x∈s,b x)=(∑ x∈s,w x*d x)-(∑ x∈s,w x) := by
    rw [←Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intro x hx;simp [b,hx,mul_sub]
  rw [hb'];unfold finiteMass;change 1+(_-_) = _;ring

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule129

/- Helper module Cofactor. -/
section P2MDyadicModule130

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

end P2MDyadicModule130

/- Helper module GridKeep. -/
section P2MDyadicModule131

set_option autoImplicit false

set_option maxHeartbeats 950000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open RegevSketch

noncomputable section

def imageGrid (n M : ℕ) [NeZero M] : Finset (Fin n → ℤ) := Finset.univ.image (fun c : Fin n → ZMod M => fun i => (c i).valMinAbs)

def keeps {X : Type*} (m : ℕ) (s : Finset X) := Fintype.piFinset (fun _ : Fin m => s)

theorem tuple_keeps {X : Type*} (p : PMF X) (m : ℕ) (s : Finset X) :
    finiteMass (tuple p m) (keeps m s)=(finiteMass p s)^m := by
  simp only [finiteMass,keeps,tuple_real]
  exact (Finset.sum_pow' s (fun x => (p x).toReal) m).symm

theorem no_grid {n M : ℕ} [NeZero M] (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (s : Finset (Fin n→ℤ))
    (hs : ∀ p∈s,p∉imageGrid n M) : fourierEvent B r M s=0 := by
  have ha (c : Fin n→ZMod M) : (fun i => (c i).valMinAbs) ∉ s := fun h => hs _ h (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩)
  simp [fourierEvent,ha]

theorem grid_mass {n M : ℕ} [NeZero M] (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (p : PMF (Fin n→ℤ))
    (hm : ∀z, (p z).toReal=coefficientMass B r z) (d : ℝ)
    (he : ∀ T, |fourierEvent B r M T-∑ z∈T,coefficientMass B r z| ≤ d) :
    1-finiteMass p (imageGrid n M)≤d := by
  classical
  let s := imageGrid n M
  let keep := fun x => if x∈s then (p x).toReal else 0
  let drop := fun x => if x∈s then 0 else (p x).toReal
  have hk : Summable keep := summable_of_ne_finset_zero (s:=s) (fun x hx => by simp [keep,hx])
  have hkeq : ∑' x,keep x=finiteMass p s := by
    rw [tsum_eq_sum (s:=s) (fun x hx => by simp [keep,hx])]
    apply Finset.sum_congr rfl;intro x hx;simp [keep,hx]
  have hdrop : ∑' x,drop x=1-finiteMass p s := by
    have h : drop = (fun x => (p x).toReal)-keep := by funext x;by_cases hx : x∈s <;> simp [keep,drop,hx]
    rw [h];simp only [Pi.sub_apply];rw [(mass_summable p).summable.tsum_sub hk,(mass_summable p).tsum_eq,hkeq]
  rw [←hdrop]
  apply Real.tsum_le_of_sum_le (fun x => by dsimp [drop];split <;> positivity)
  intro u
  let T := u.filter (fun x => x ∉ s)
  have ht := he T
  rw [no_grid B r T (fun z hz => (Finset.mem_filter.mp hz).2),zero_sub,abs_neg] at ht
  have hv : (∑ x∈u,drop x)=∑ z∈T,coefficientMass B r z := by
    unfold T
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _;by_cases hx : x∈s <;> simp [drop,hx,hm]
  rw [hv]
  exact (le_abs_self _).trans ht

theorem pow_missing (b : ℝ) (hb : 0≤b) (h1 : b≤1) (m : ℕ) : 1-b^m ≤ (m:ℝ)*(1-b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm := pow_le_one₀ hb h1 (n:=m)
    have h := mul_le_of_le_one_left (sub_nonneg.mpr h1) hm
    rw [pow_succ,Nat.cast_succ];nlinarith

theorem outside_grid {n M : ℕ} [NeZero M] (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (r : ℝ) (hr : 0<r) (hn : 0<n) (hg : gridAdequate B r M) (p : PMF (Fin n→ℤ)) (hm : ∀z,(p z).toReal=coefficientMass B r z) (m : ℕ) :
    1-finiteMass (tuple p m) (keeps m (imageGrid n M)) ≤ m*GridReadout.gridError n := by
  let s := imageGrid n M
  have h := grid_mass B r p hm _ (GridReadout.public_event_bound B hB r hr hn hg)
  have h0 : 0≤finiteMass p s := Finset.sum_nonneg (fun x _ => ENNReal.toReal_nonneg)
  have h1 : finiteMass p s ≤ 1 := (mass_summable p).summable.sum_le_tsum s (fun _ _ => ENNReal.toReal_nonneg) |>.trans_eq (mass_summable p).tsum_eq
  rw [tuple_keeps]
  exact (pow_missing _ h0 h1 m).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg m))

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule131

/- Helper module schedule.Schedule. -/
section P2MDyadicModule132

set_option autoImplicit false

set_option maxHeartbeats 900000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSketch.DyadicSchedule

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARPlatformEncoding Integration9_9.TM2PolynomialBudget

open QMCNumericRuntime

open scoped Polynomial

@[fun_prop] theorem pairWord_poly : Poly (fun x : Str × Str => encPair x.1 x.2) := by
  unfold encPair
  fun_prop

end InfoLossLAR.WorstCase.RegevSketch.DyadicSchedule

end P2MDyadicModule132

/- Helper module CopyLaws. -/
section P2MDyadicModule133

set_option autoImplicit false

set_option maxHeartbeats 700000

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

open InfoLossLAR.WorstCase.RegevSearch RegevLWE.GaussConv

open scoped BigOperators Classical

namespace SharedPoolCoherence

noncomputable section

variable {n : ℕ}

private theorem row_error {β : Type*} [Fintype β] [DecidableEq β] (z : ℂ) (a b : β) :
    (∑ y : β, ‖(if y = a then z else 0) - (if y = b then z else 0)‖ ^ 2) =
      if a = b then 0 else 2 * ‖z‖ ^ 2 := by
  classical
  by_cases hab : a = b
  · simp [hab]
  · have hrow (y : β) :
        ‖(if y = a then z else 0) - (if y = b then z else 0)‖ ^ 2 =
          (if y = a then ‖z‖ ^ 2 else 0) + (if y = b then ‖z‖ ^ 2 else 0) := by
      by_cases hya : y = a <;> by_cases hyb : y = b <;> simp_all
    simp_rw [hrow]
    simp [Finset.sum_add_distrib, hab, two_mul]

/-- Exact error of copying a computed answer rather than the unique desired answer.
The answer may depend on a preserved query register, so the assertion applies to a
superposition of queries as well as to a single classical input. -/
theorem copied_error_sq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ψ : α → ℂ) (readout desired : α → β) :
    ‖copied ψ readout - copied ψ desired‖ ^ 2 =
      2 * ∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, copied, PiLp.sub_apply]
  simp_rw [row_error]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Dividing nonnegative weights by their total gives a summable subprobability.
For the Jensen estimate only the upper bound on total mass is needed. -/
theorem coeff_subprob (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) :
    (∀ z, 0 ≤ coefficientMass B r z) ∧ Summable (coefficientMass B r) ∧
      (∑' z, coefficientMass B r z) ≤ 1 := by
  classical
  let g (z : Fin n → ℤ) := rhoInt r (B.mulVec z)
  have hp (z) : 0 ≤ g z := (Real.exp_pos _).le
  have hZ : 0 ≤ ∑' z, g z := tsum_nonneg hp
  change (∀ z, 0 ≤ g z / ∑' y, g y) ∧ Summable (fun z => g z / ∑' y, g y) ∧ _
  refine ⟨fun z => div_nonneg (hp z) hZ, ?_⟩
  change Summable (fun z => g z / ∑' y, g y) ∧ (∑' z, g z / ∑' y, g y) ≤ 1
  by_cases hs : Summable g
  · refine ⟨hs.div_const _, ?_⟩
    rw [tsum_div_const]
    by_cases hz : (∑' z,g z)=0 <;> simp [hz]
  · rw [tsum_eq_zero_of_not_summable hs]
    simp

theorem outputProb_bounds (G : MFamily) (w : Str) (event : Str → Prop) :
    0 ≤ outputProb G w event ∧ outputProb G w event ≤ 1 := by
  classical
  unfold outputProb
  let state := runLayered (G.circ w.length) (basisInput (toBits w))
  have total : (∑ y, ‖state y‖^2) = 1 := by
    simpa only [state, ← Complex.normSq_eq_norm_sq] using
      (runLayered_mass (G.circ w.length) (basisInput (toBits w))).trans
        (basisInput_mass (a := G.anc w.length) (toBits w))
  constructor
  · exact Finset.sum_nonneg (by intro y _; split_ifs <;> positivity)
  · apply le_trans _ total.le
    apply Finset.sum_le_sum
    intro y _
    split_ifs <;> first | exact le_rfl | positivity

/-- Full jointly independent countable family normalization, allowing
coordinate-dependent channels and output tests in every factor. -/
theorem dependentProductMass_hasSum {Index : Type*} (dimension : ℕ)
    (mass : Fin dimension → Index → ℝ)
    (hnonnegative : ∀ index value,0 ≤ mass index value) (hsummable : ∀ index,Summable (mass index)) :
    HasSum (fun word : Fin dimension → Index => ∏ index,mass index (word index))
      (∏ index,∑' value,mass index value) := by
  classical
  induction dimension with
  | zero =>
    have heq : (fun word : Fin 0 → Index => ∏ index,mass index (word index))=(fun _ => (1 : ℝ)) := by
      funext word
      simp
    rw [heq]
    simpa only [Finset.univ_eq_empty,Finset.prod_empty,Fintype.sum_unique] using
      (hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)))
  | succ dimension ih =>
    have htail := ih (fun index => mass index.succ) (fun index => hnonnegative index.succ)
      (fun index => hsummable index.succ)
    have htailNonnegative (word : Fin dimension → Index) : 0 ≤ ∏ index,mass index.succ (word index) :=
      Finset.prod_nonneg (fun _ _ => hnonnegative _ _)
    have hs := (hsummable 0).mul_of_nonneg htail.summable (hnonnegative 0) htailNonnegative
    have hp := (hsummable 0).hasSum.mul htail hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass 0 pair.1*(∏ index,mass index.succ (pair.2 index)))=
        (fun word : Fin (dimension+1) → Index => ∏ index,mass index (word index)) ∘
          (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [Fin.prod_univ_succ] using h

theorem poolWeight_subprob (m : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ) :
    (∀ p, 0 ≤ poolWeight m B R p) ∧ Summable (poolWeight m B R) ∧ (∑' p, poolWeight m B R p) ≤ 1 := by
  obtain ⟨h,hs,hm⟩ := coeff_subprob B R
  have he := dependentProductMass_hasSum m (fun _ => coefficientMass B R) (fun _ => h) (fun _ => hs)
  refine ⟨fun p => Finset.prod_nonneg (fun j _ => h (p j)), he.summable, he.tsum_eq.trans_le ?_⟩
  exact Finset.prod_le_one (fun _ _ => tsum_nonneg h) (fun _ _ => hm)

/-- Exact squared norm error of a native decoder's copied answer on a finite
superposition of inputs. Any common isometric uncomputation preserves it. -/
theorem native_copy_error_sq {I β : Type} [Fintype I] [Fintype β] [DecidableEq β]
    (C : MFamily) (w : I → Str) (good : I → Str → Prop) (a : I → ℂ)
    (read : Outcomes C w → β) (target : I → β)
    (hread : ∀ x : Outcomes C w, read x = target x.1 ↔ good x.1 (nativeOutput C (w x.1) x.2)) :
    let ψ (x : Outcomes C w) := a x.1 * nativeAmplitude C (w x.1) x.2
    ‖SharedPoolCoherence.copied ψ read - SharedPoolCoherence.copied ψ (fun x => target x.1)‖^2 =
      2 * ∑ i, ‖a i‖^2 * outputProb C (w i) (fun y => ¬ good i y) := by
  classical
  dsimp only
  rw [SharedPoolCoherence.copied_error_sq, Fintype.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold outputProb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : good i (nativeOutput C (w i) y)
  · have hg := (hread ⟨i,y⟩).mpr h
    simp only [hg, if_true, nativeOutput] at *
    simp [h]
  · have hg := mt (hread ⟨i,y⟩).mp h
    simp only [hg, if_false, norm_mul, mul_pow]
    simp only [nativeOutput] at h
    simp [h, nativeAmplitude]

end

end SharedPoolCoherence

end P2MDyadicModule133

/- Helper module SharedRms. -/
section P2MDyadicModule134

set_option autoImplicit false

set_option maxHeartbeats 1100000

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

open InfoLossLAR.WorstCase.RegevSearch RegevLWE.GaussConv

open scoped BigOperators Classical

namespace SharedPoolCoherence

noncomputable section

variable {n : ℕ}

private def flagRegister {m t : ℕ} (C : MFamily) {B : Matrix (Fin n) (Fin n) ℤ} {R : ℚ}
    (precision : ℕ) (pool : Fin m → Fin n → ℤ) (q : Fin (t+1) → Query B R) : Register C precision pool q where
  width := 1
  read x := fun _ => decide (encVec encI (q x.1).answer <+: nativeOutput C (word precision pool (q x.1)) x.2)
  answer _ := fun _ => true
  correct x := by simp [funext_iff]

private theorem gap_flag {m t : ℕ} (C : MFamily) {B : Matrix (Fin n) (Fin n) ℤ} {R : ℚ}
    (precision : ℕ) (pool : Fin m → Fin n → ℤ) (q : Fin (t+1) → Query B R) (a : Fin (t+1) → ℂ) :
    let reg := flagRegister C precision pool q
    copyGap C (fun i => word precision pool (q i)) a reg.read reg.answer =
      Real.sqrt (2 * failureMass C precision pool q a) := by
  let reg := flagRegister C precision pool q
  let good (i : Fin (t+1)) (o : Str) := encVec encI (q i).answer <+: o
  have hh := native_copy_error_sq C (fun i => word precision pool (q i)) good a reg.read reg.answer reg.correct
  change copyGap C (fun i => word precision pool (q i)) a reg.read reg.answer = _
  rw [← Real.sqrt_sq (show 0 ≤ copyGap C (fun i => word precision pool (q i)) a reg.read reg.answer from norm_nonneg _)]
  exact congrArg Real.sqrt hh

/-- The platform's `Fin (t+1)` coherent copy budget controls the weighted
root-mean-square failure on any native bit reference. The superposition is
fixed before the common Gaussian pool is drawn. -/
theorem rms_budget {C : MFamily} {P calls : Polynomial ℕ} {N : ℕ} {S : Set ℕ} {e : ℕ → ℝ}
    (hcopy : CopyBudget C P calls N S e) (hn : n ∈ S) (hN : N ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℚ) (hR : 0 < R)
    (hs : Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ))
    (k : ℕ) {I : Type} [Fintype I] [Nonempty I] (q : I → Query B R) (a : I → ℂ) (ha : ∑ i,‖a i‖^2=1) :
    let prec := poolBDDPrecision (calls.eval n) k
    (∑' p : Fin (P.eval n) → Fin n → ℤ, poolWeight (P.eval n) B R p *
      (2*((calls.eval n : ℕ) : ℝ)*Real.sqrt (2*failureMass C prec p q a))) ≤ e n + 1/(4*((k:ℝ)+1)) := by
  classical
  let t := Fintype.card I - 1
  have ht : Fintype.card I = t+1 := by have := Fintype.card_pos (α:=I); dsimp only [t]; omega
  let eqv := (Fintype.equivFinOfCardEq ht).symm
  have hnrm : ∑ i,‖a (eqv i)‖^2=1 := (eqv.sum_comp (fun i => ‖a i‖^2)).trans ha
  let prec := poolBDDPrecision (calls.eval n) k
  have bound := hcopy n hn hN B hB R hR hs k t (q ∘ eqv) (a ∘ eqv) hnrm (fun p => flagRegister C prec p (q ∘ eqv))
  have hr (p : Fin (P.eval n) → Fin n → ℤ) : failureMass C prec p (q ∘ eqv) (a ∘ eqv) = failureMass C prec p q a :=
    eqv.sum_comp (fun i => ‖a i‖^2 * outputProb C (word prec p (q i)) (fun out => ¬ encVec encI (q i).answer <+: out))
  dsimp only at bound ⊢
  simpa only [gap_flag,hr,prec] using bound

end

end SharedPoolCoherence

end P2MDyadicModule134

/- Helper module PooledPhysical. -/
section P2MDyadicModule135

set_option autoImplicit false

set_option maxHeartbeats 1300000

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

open InfoLossLAR.WorstCase.RegevSearch RegevLWE.GaussConv

open scoped BigOperators Classical

namespace SharedPoolCoherence

noncomputable section

variable {n : ℕ}

private theorem failureMass_bounds {m : ℕ} {I : Type} [Fintype I] (C : MFamily)
    {B : Matrix (Fin n) (Fin n) ℤ} {R : ℚ} (prec : ℕ) (pool : Fin m → Fin n → ℤ)
    (q : I → Query B R) (a : I → ℂ) (ha : ∑ i, ‖a i‖^2=1) :
    0 ≤ failureMass C prec pool q a ∧ failureMass C prec pool q a ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (outputProb_bounds _ _ _).1
  · rw [←ha]
    exact Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (sq_nonneg _) (outputProb_bounds _ _ _).2

theorem finite_realization_budget {C : MFamily} {P calls : Polynomial ℕ} {N : ℕ} {S : Set ℕ} {e : ℕ → ℝ}
    (hcopy : CopyBudget C P (calls+calls) N S e) (hn : n ∈ S) (hN : N ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℚ) (hR : 0 < R)
    (hs : Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ))
    (k : ℕ) {I : Type} [Fintype I] [Nonempty I] (q : I → Query B R) (a : I → ℂ) (ha : ∑ i,‖a i‖^2=1)
    (keep : Finset (Fin (P.eval n) → Fin n → ℤ)) (err : (Fin (P.eval n) → Fin n → ℤ) → ℝ)
    (herr : ∀ p ∈ keep, err p ≤ 4*Real.sqrt (failureMass C (poolBDDPrecision ((calls+calls).eval n) k) p q a)) :
    ∑ p ∈ keep, poolWeight (P.eval n) B R p * (((calls.eval n : ℕ):ℝ) * err p) ≤ e n + 1/(4*((k:ℝ)+1)) := by
  let T : ℝ := (calls.eval n : ℕ)
  have hT : 0 ≤ T := Nat.cast_nonneg _
  let prec := poolBDDPrecision ((calls+calls).eval n) k
  let wt := poolWeight (P.eval n) B (R:ℝ)
  let mass (p : Fin (P.eval n) → Fin n → ℤ) := failureMass C prec p q a
  let f p := wt p * (4*T*Real.sqrt (2*mass p))
  have hmass p : 0 ≤ mass p ∧ mass p ≤ 1 := failureMass_bounds C prec p q a ha
  obtain ⟨hwt,hws,_⟩ := poolWeight_subprob (P.eval n) B (R:ℝ)
  have hnneg p : 0 ≤ f p := mul_nonneg (hwt p) (mul_nonneg (mul_nonneg (by norm_num) hT) (Real.sqrt_nonneg _))
  have hmaj p : f p ≤ wt p * (4*T*2) := by
    apply mul_le_mul_of_nonneg_left _ (hwt p)
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hT)
    exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith [(hmass p).2]⟩)
  have hfs : Summable f := Summable.of_nonneg_of_le hnneg hmaj (hws.mul_right (4*T*2))
  calc
    _ ≤ ∑ p ∈ keep, f p := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (hwt p)
      have h := herr p hp
      have hsqrt : Real.sqrt (mass p) ≤ Real.sqrt (2*mass p) := Real.sqrt_le_sqrt (by linarith [(hmass p).1])
      change T * err p ≤ 4*T*Real.sqrt (2*mass p)
      calc
        _ ≤ T*(4*Real.sqrt (mass p)) := mul_le_mul_of_nonneg_left h hT
        _ ≤ 4*T*Real.sqrt (2*mass p) := by rw [←mul_assoc,mul_comm T]; exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ ≤ ∑' p, f p := hfs.sum_le_tsum keep (fun p _ => hnneg p)
    _ ≤ _ := by
      have h := rms_budget hcopy hn hN B hB R hR hs k q a ha
      have hcoef : 2*(((calls+calls).eval n : ℕ):ℝ) = 4*T := by simp only [Polynomial.eval_add,Nat.cast_add,T]; ring
      simpa only [f,wt,mass,prec,hcoef] using h

end

end SharedPoolCoherence

end P2MDyadicModule135

/- Helper module PoolMarginal. -/
section P2MDyadicModule136

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1450000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity SharedPoolCoherence CoherentProjection GaussianPoissonSeries GaussianProjection

open RegevLWE.GaussConv RegevSketch

noncomputable section

variable {n m : ℕ}

/-- Common-pool averaging after finite-register implementation, including
pool-dependent normalized preparation junk and arbitrary truncation of the
old pool. This contracts the BDD contribution per stage without a
pointwise guarantee on any pool. -/
theorem average_stage {C : MFamily} {P T : Polynomial ℕ} {N : ℕ} {S : Set ℕ} {e : ℕ→ℝ}
    (copy : CopyBudget C P (T+T) N S e) (hn : n∈S) (hN : N≤n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℚ) (hR : 0<R)
    (hs : Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ))
    (budget : ℕ) {I : Type} [Fintype I] [Nonempty I] (q : I → Query B R) (v : I → ℂ) (hv : ∑ i,‖v i‖^2=1)
    (keep : Finset (Fin (P.eval n) → Fin n → ℤ)) (err : (Fin (P.eval n) → Fin n → ℤ) → ℝ)
    (ε : ℝ) (hε : 0≤ε) (herr : ∀ pool ∈ keep, err pool ≤ ε + 4*Real.sqrt
      (failureMass C (poolBDDPrecision ((T+T).eval n) budget) pool q v)) :
    ∑ pool ∈ keep, poolWeight (P.eval n) B R pool * (((T.eval n : ℕ):ℝ)*err pool) ≤
      ((T.eval n : ℕ):ℝ)*ε + e n+1/(4*((budget:ℝ)+1)) := by
  let D := (Fin (P.eval n) → Fin n → ℤ)
  let w := poolWeight (P.eval n) B (R:ℝ)
  let t := ((T.eval n:ℕ):ℝ)
  have ht : 0≤t := Nat.cast_nonneg _
  let f (p : D) := err p - ε
  have h := finite_realization_budget copy hn hN B hB R hR hs budget q v hv keep f (by
    intro p hp
    exact sub_le_iff_le_add.mpr (by simpa [add_comm] using herr p hp))
  obtain ⟨hw,hsum,hmass⟩ := poolWeight_subprob (P.eval n) B (R:ℝ)
  have hsmall : ∑ p ∈ keep,w p ≤ 1 := (hsum.sum_le_tsum keep (fun p _ => hw p)).trans hmass
  calc
    _ = (∑ p ∈ keep,w p)*(t*ε) + ∑ p ∈ keep,w p*(t*f p) := by
      rw [Finset.sum_mul,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      dsimp [f,w,t]
      ring
    _ ≤ 1*(t*ε)+(e n+1/(4*((budget:ℝ)+1))) := add_le_add (mul_le_mul_of_nonneg_right hsmall (mul_nonneg ht hε)) h
    _ = _ := by rw [one_mul,add_assoc]

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule136

/- Helper module StepTest. -/
section P2MDyadicModule137

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open QAlgorithms.Complexity SharedPoolCoherence RegevLWE.GaussConv IntegerBasis RegevSketch

noncomputable section

def stageTest {X : Type*} (keep : Finset X) (err : X→ℝ) (he : ∀ x,0≤err x) (calls : ℕ) : Test X := fun x =>
  if x∈keep then ⟨min 1 (calls*err x),le_min zero_le_one (mul_nonneg (Nat.cast_nonneg calls) (he x)),min_le_left _ _⟩ else ⟨1,zero_le_one,le_rfl⟩

theorem stageTest_lifts {X Y : Type*} (s : Finset X) (d : X→ℝ) (hd : ∀ x, 0≤d x) (m : ℕ)
    (p : PMF Y) (x : X) (actual : PMF Y) (h : x∈s → ∀ T, |finiteMass actual T-finiteMass p T|≤d x)
    (f : Test (Fin m→Y)) :
    |evaluate (tuple actual m) f - evaluate (tuple p m) f| ≤ stageTest s d hd m x := by
  have ha := evaluate_range (tuple actual m) f
  have hb := evaluate_range (tuple p m) f
  have one : |evaluate (tuple actual m) f-evaluate (tuple p m) f|≤1 := abs_le.mpr ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩
  by_cases hx : x∈s
  · rw [stageTest,if_pos hx];exact le_min one (tuple_error _ _ _ (tests_of_finite_events _ _ _ (h hx)) m f)
  · simpa [stageTest,hx] using one

theorem mass_stageTest {X : Type*} (s : Finset X) (d : X→ℝ) (hd : ∀ x,0≤d x) (m t : ℕ) (hmt : m ≤ t) (p : PMF X) :
    evaluate p (stageTest s d hd m) ≤ (∑ x∈s,(p x).toReal*((t:ℝ)*d x))+(1-finiteMass p s) := by
  let F := stageTest s d hd m
  have hv : ∀ x∈s, |(F x:ℝ)-(0:ℝ)| ≤ t*d x := by
    intro x hx
    rw [sub_zero,abs_of_nonneg (F x).property.1]
    change ((stageTest s d hd m x):ℝ)≤_
    simp only [stageTest,if_pos hx]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hmt) (hd x))
  have h := average_kept p F ⟨0,le_rfl,zero_le_one⟩ s (fun x => t*d x) hv
  simpa only [sub_zero,abs_of_nonneg (evaluate_range p F).1] using h

/-- The bounded error test depends on the pool's decoded integer coordinates alone. -/
theorem physical_stage_budget {n : ℕ} {C : MFamily} {P T : Polynomial ℕ} {N : ℕ} {S : Set ℕ} {e : ℕ→ℝ}
    (copy : CopyBudget C P (T+T) N S e) (hn : n∈S) (hN : N≤n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℚ) (hR : 0<R) (hn0 : 0<n)
    (hs : Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n)<(R:ℝ))
    {M : ℕ} [NeZero M] (hg : gridAdequate B R M) (p : PMF (Fin n→ℤ)) (hp : ∀z,(p z).toReal=coefficientMass B R z)
    (k : ℕ) {I : Type} [Fintype I] [Nonempty I] (q : I → Query B R) (v : I→ℂ) (hv : ∑ i,‖v i‖^2=1)
    (a : ℝ) (ha : 0≤a) (m : ℕ) (hm : m≤T.eval n) :
    let s := keeps (P.eval n) (imageGrid n M)
    let d := fun pool => a+4*Real.sqrt (failureMass C (poolBDDPrecision ((T+T).eval n) k) pool q v)
    let hd : ∀ x, 0≤d x := fun _ => add_nonneg ha (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    evaluate (tuple p (P.eval n)) (stageTest s d hd m) ≤
      ((T.eval n:ℕ):ℝ)*a+e n+1/(4*((k:ℝ)+1))+(P.eval n:ℕ)*GridReadout.gridError n := by
  intro s d hd
  have h := PhysicalFourier.average_stage copy hn hN B hB R hR hs k q v hv s d a ha (fun _ _ => le_rfl)
  have hw (x) : ((tuple p (P.eval n)) x).toReal=poolWeight (P.eval n) B R x := by simp only [tuple_real,hp,poolWeight]
  have hk := mass_stageTest s d hd m (T.eval n) hm (tuple p (P.eval n))
  simp only [hw] at hk
  exact hk.trans (add_le_add h (outside_grid B hB R (by exact_mod_cast hR) hn0 hg p hp (P.eval n)))

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule137

/- Helper module Negligible. -/
section P2MDyadicModule138

set_option autoImplicit false

open scoped BigOperators

namespace GridReadout

open InfoLossLAR.WorstCase

theorem negligible_gridError : Negligible gridError := by
  refine ⟨fun n => by unfold gridError; positivity, ?_⟩
  intro c hc
  obtain ⟨J,hJ⟩ := verification_geometric_negligible.2 (c+1) (by linarith)
  refine ⟨max J 9, ?_⟩
  intro n hn
  have h9n : 9 ≤ n := le_trans (Nat.le_max_right ..) hn
  have h9 : (9:ℝ) ≤ n := by exact_mod_cast h9n
  have hn' : (0:ℝ)<n := by linarith
  have hs : Real.sqrt (2*(1/2:ℝ)^n) ≤ 2*(3/4:ℝ)^n := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity,?_⟩
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤(3/4)^2) n
    rw [mul_pow, ←pow_mul, Nat.mul_comm, pow_mul]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤(3/4)^2) n]
  have hq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤3/4) n
  have hdec := hJ n (le_trans (Nat.le_max_left ..) hn)
  calc
    gridError n ≤ 9*(3/4:ℝ)^n := by unfold gridError; linarith
    _ ≤ (n:ℝ)*(n:ℝ)^(-(c+1)) := mul_le_mul h9 hdec (by positivity) hn'.le
    _ = (n:ℝ)^(-c) := by
      conv_lhs => lhs; rw [← Real.rpow_one (n:ℝ)]
      rw [←Real.rpow_add hn']; congr 1; ring

end GridReadout

end P2MDyadicModule138

/- Helper module Solutions.RegevBridgeLoadedBatchVerificationBudget. -/
section P2MDyadicModule139

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open Filter

open scoped Topology

/-- The two negligible-error conventions agree for nonnegative errors. -/
theorem native_negligible_of_platform {error : ℕ → ℝ} (h : Negligible error) :
    AFT.Negligible error := by
  intro order
  obtain ⟨cutoff,hcutoff⟩ := h.2 ((order : ℝ)+1) (by positivity)
  filter_upwards [eventually_ge_atTop cutoff,eventually_ge_atTop 1] with n hn hone
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hone
  have hpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  rw [abs_of_nonneg (h.1 n)]
  calc
    error n ≤ (n : ℝ)^(-((order : ℝ)+1)) := hcutoff n hn
    _ ≤ (n : ℝ)^(-(order : ℝ)) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    _ = 1/(n : ℝ)^order := by rw [Real.rpow_neg hpos.le,Real.rpow_natCast,one_div]

/-- Fixed constants preserve the full inverse-polynomial quantifier. -/
theorem native_negligible_const_mul {error : ℕ → ℝ} (h : AFT.Negligible error) (c : ℝ) :
    AFT.Negligible (fun n => c*error n) := by
  intro order
  filter_upwards [h (order+1),eventually_ge_atTop (⌈|c|⌉₊+1)] with n he hn
  have hc : |c|≤(n : ℝ) := (Nat.le_ceil |c|).trans (by exact_mod_cast (by omega : ⌈|c|⌉₊≤n))
  have hpos : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  rw [abs_mul]
  calc
    |c| * |error n| ≤ (n : ℝ)*(1/(n : ℝ)^(order+1)) :=
      mul_le_mul hc he (abs_nonneg _) hpos.le
    _ = 1/(n : ℝ)^order := by rw [pow_succ];field_simp

/-- Any fixed natural-coefficient polynomial preserves negligible error. -/
theorem native_negligible_polynomial_mul {error : ℕ → ℝ} (h : AFT.Negligible error)
    (p : Polynomial ℕ) : AFT.Negligible (fun n => ((p.eval n : ℕ) : ℝ)*error n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add,Nat.cast_add,add_mul] using hp.add hq
  | monomial degree c =>
    simpa only [Polynomial.eval_monomial,Nat.cast_mul,Nat.cast_pow,mul_assoc] using
      native_negligible_const_mul (h.mul_polynomial degree) (c : ℝ)

end InfoLossLAR.WorstCase

end P2MDyadicModule139

/- Helper module Budgets. -/
section P2MDyadicModule140

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open GaussianRandomizedRounding RationalGramSchmidt

noncomputable section

def rounds (n : ℕ) := 5*n+3

def precision (n m k : ℕ) := 64*rounds n*(m+2)*(k+1)

def geom (n : ℕ) := GridReadout.gridError n

theorem geom_pos (n : ℕ) : 0≤ geom n := GridReadout.negligible_gridError.1 n

theorem half_le_geom (n : ℕ) : (1/2:ℝ)^n ≤ geom n := by
  let x : ℝ := (1/2:ℝ)^n
  have h0 : 0≤ x := by dsimp [x];positivity
  have h1 : x ≤ 1 := pow_le_one₀ (a:=(1/2:ℝ)) (n:=n) (by norm_num) (by norm_num)
  have h2 : x≤ Real.sqrt (2*x) := (Real.le_sqrt (by positivity) (by positivity)).mpr (by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)])
  change x ≤ 4*Real.sqrt (2*x)+(1/4:ℝ)^n
  nlinarith [Real.sqrt_nonneg (2*x),pow_nonneg (by norm_num : (0:ℝ)≤ 1/4) n]

theorem quarter_sqrt (n : ℕ) : Real.sqrt ((1/4:ℝ)^n)=(1/2:ℝ)^n := by
  rw [show (1/4:ℝ)=(1/2)^2 by norm_num,←pow_mul,Nat.mul_comm,pow_mul,Real.sqrt_sq (by positivity)]

theorem dyad_le (n : ℕ) : 1/(2:ℝ)^n ≤ geom n := by simpa only [one_div,inv_pow] using half_le_geom n

theorem initial_cost (n : ℕ) : FirstPool.cost n n ≤ 24*(n:ℝ)*geom n := by
  have h1 := Wide.sampleError_le_eight_dyadic n
  have ht : initialThetaBudget (n+1)≤ 4*geom n := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤ 2) (show n≤ 4*(n+1) by omega)
    calc initialThetaBudget (n+1) = 4/(2:ℝ)^(4*(n+1)) := rfl
         _ ≤ 4/(2:ℝ)^n := div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
         _ ≤ _ := by simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left (dyad_le n) (by norm_num : (0:ℝ)≤ 4)
  have h2 : Wide.sampleError n ≤ 8*geom n := by
    calc _ ≤ _ := h1
         _ = 8*(1/2^n) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (dyad_le n) (by norm_num)
  unfold FirstPool.cost
  nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α:=ℝ) n), mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α:=ℝ) n)]

/-- Includes the rectangular frontend, grid approximation, truncated state and finite QFT. -/
theorem analytic_cost (n b : ℕ) (L : ℝ) (hL : (b:ℝ)+1≤ L) (d : ℕ) (hd : n≤ d) (prep : ℝ)
    (hprep : prep ≤ 2/L+1/(2:ℝ)^d+2*Real.sqrt ((1/4:ℝ)^n)) :
    2*prep+4*Real.sqrt (2*(1/2:ℝ)^n)+1/(4*((b:ℝ)+1))+GridReadout.gridError n ≤
      12*geom n+5/((b:ℝ)+1) := by
  have hp : (0:ℝ)<(b:ℝ)+1 := by positivity
  have hL' := one_div_le_one_div_of_le hp hL
  have hd' := (one_div_le_one_div_of_le (by positivity : 0<(2:ℝ)^n) (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤ 2) hd)).trans (dyad_le n)
  rw [quarter_sqrt] at hprep
  have hsg : 4*Real.sqrt (2*(1/2:ℝ)^n)≤ geom n := le_add_of_nonneg_right (by positivity : 0≤ (1/4:ℝ)^n)
  have hb : 1/(4*((b:ℝ)+1)) ≤ 1/((b:ℝ)+1) := one_div_le_one_div_of_le hp (by linarith)
  change _+_+_+geom n≤ _
  have half := half_le_geom n
  have gn := geom_pos n
  simp only [div_eq_mul_inv,one_mul] at hprep hL' hd' hb hsg half ⊢
  linarith

open Polynomial in
def errorPoly (P : Polynomial ℕ) : Polynomial ℕ := 24*Polynomial.X*P+(5*Polynomial.X+3)*(12*(P+1)+P)+1

def totalError (P : Polynomial ℕ) (e : ℕ→ℝ) (n : ℕ) : ℝ := ((errorPoly P).eval n:ℕ)*geom n + (rounds n:ℝ)*e n

theorem negligible_total (P : Polynomial ℕ) {e : ℕ→ℝ} (he : Negligible e) : Negligible (totalError P e) := by
  have h0 := native_negligible_polynomial_mul (native_negligible_of_platform GridReadout.negligible_gridError) (errorPoly P)
  have h1 := native_negligible_polynomial_mul (native_negligible_of_platform he) (5*Polynomial.X+3)
  apply platform_negligible_of_native _ (fun i => add_nonneg (mul_nonneg (Nat.cast_nonneg _) (geom_pos _)) (mul_nonneg (Nat.cast_nonneg _) (he.1 _)))
  simpa only [totalError,geom,rounds,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat] using h0.add h1

def stepError (P : Polynomial ℕ) (e : ℕ→ℝ) (n b : ℕ) : ℝ :=
  (((P.eval n:ℕ):ℝ)+1)*(12*geom n+5/(b+1:ℝ))+e n+1/(4*(b+1:ℝ))+((P.eval n:ℕ):ℝ)*geom n

theorem accumulate (P : Polynomial ℕ) (n k h : ℕ) (hh : h ≤ 5*n+2) (e : ℕ→ℝ) (he : 0≤ e n) :
    let b := precision n (P.eval n) k
    ((P.eval n:ℕ):ℝ)*FirstPool.cost n n + ((h:ℝ)+1)*stepError P e n b + geom n ≤
      totalError P e n + 1/(4*((k:ℝ)+1)) := by
  intro b
  let m : ℝ := (P.eval n:ℕ)
  let s : ℝ := rounds n
  have hc : (b:ℝ)=64*s*(m+2)*((k:ℝ)+1) := by simp [b,precision,s,m] <;> push_cast <;> ring
  have ms : 0 ≤ m := Nat.cast_nonneg _
  have ss : 0 ≤ s := Nat.cast_nonneg _
  have bs : 0 < (b:ℝ)+1 := by positivity
  have ks : 0 < (k:ℝ)+1 := by positivity
  have hsr : (h:ℝ)+1≤ s := by dsimp [s];exact_mod_cast (show h+1≤ rounds n by unfold rounds;omega)
  have hn : 0 ≤ stepError P e n b := by unfold stepError;have hg := geom_pos n;positivity
  have hin := mul_le_mul_of_nonneg_left (initial_cost n) ms
  have hstep := mul_le_mul_of_nonneg_right hsr hn
  have hdiv : s*(5*(m+1)+1)/((b:ℝ)+1) ≤ 1/(4*((k:ℝ)+1)) := by
    rw [div_le_div_iff₀ bs (by positivity),hc]
    nlinarith [mul_nonneg (mul_nonneg ss (by linarith : 0≤ 44*m+104)) ks.le]
  have hb : 1/(4*((b:ℝ)+1)) ≤ 1/((b:ℝ)+1) := one_div_le_one_div_of_le bs (by linarith)
  have hbh := mul_le_mul_of_nonneg_left hb ss
  have hr : (((errorPoly P).eval n : ℕ) : ℝ) = 24*(n:ℝ)*m+s*(12*(m+1)+m)+1 := by
    simp [errorPoly,s,m,rounds] <;> push_cast <;> ring
  unfold totalError
  rw [hr]
  change (m*FirstPool.cost n n + _ + _) ≤ _
  change _≤ _*geom n + s*e n + _
  unfold stepError at hstep
  change (↑h+1)*stepError P e n b ≤ s*((m+1)*(12*geom n+5/(b+1:ℝ))+e n+1/(4*(b+1:ℝ))+m*geom n) at hstep
  simp only [div_eq_mul_inv,one_mul] at hstep hdiv hbh ⊢
  linarith only [hin,hstep,hdiv,hbh]

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule140

/- Helper module Trajectory. -/
section P2MDyadicModule141

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open QAlgorithms.Complexity SharedPoolCoherence RegevLWE.GaussConv IntegerBasis RegevSketch

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

def multiplied (p : List Unit × List Unit) : List Unit := p.1.flatMap (fun _ => p.2)

@[fun_prop] theorem multiplied_poly : Poly multiplied := by unfold multiplied;fun_prop

@[simp] theorem multiplied_len (s t : List Unit) : (multiplied (s,t)).length=s.length*t.length := by
  simp [multiplied,List.length_flatMap,List.sum_replicate,Nat.mul_comm]

def precisionTape (p : (List Unit×List Unit)×List Unit) : List Unit :=
  let h := multiplied (List.replicate 5 (),p.1.1)++List.replicate 3 ()
  multiplied (List.replicate 64 (),multiplied (h,multiplied (p.1.2++[(),()],p.2++[()])))

@[fun_prop] theorem precisionTape_poly : Poly precisionTape := by unfold precisionTape;fun_prop

theorem precisionTape_len (n m k : List Unit) : (precisionTape ((n,m),k)).length=precision n.length m.length k.length := by
  simp [precisionTape,precision,rounds,Nat.mul_assoc]

/-- The same copy budget applies to an intermediate tuple or to one final draw. -/
theorem one_stage_bound {n : ℕ} {C : MFamily} {P : Polynomial ℕ} {N : ℕ} {S : Set ℕ} {e : ℕ→ℝ}
    (copy : CopyBudget C P ((P+1)+(P+1)) N S e) (hn : n∈S) (hN : N≤n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R : ℚ) (hR : 0<R) (hn0 : 0<n)
    (hs : Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n)<(R:ℝ))
    {M : ℕ} [NeZero M] (hg : gridAdequate B R M) (p : PMF (Fin n→ℤ)) (hp : ∀z,(p z).toReal=coefficientMass B R z)
    (b : ℕ) {I : Type} [Fintype I] [Nonempty I] (q : I → Query B R) (v : I→ℂ) (hv : ∑ i,‖v i‖^2=1)
    (a : ℝ) (ha : 0≤a) (hac : a ≤ 12*geom n+5/((b:ℝ)+1)) (m : ℕ) (hm : m≤P.eval n+1) :
    let s := keeps (P.eval n) (imageGrid n M)
    let d := fun pool => a+4*Real.sqrt (failureMass C (poolBDDPrecision (((P+1)+(P+1)).eval n) b) pool q v)
    let hd : ∀ x, 0≤d x := fun _ => add_nonneg ha (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    evaluate (tuple p (P.eval n)) (stageTest s d hd m) ≤ stepError P e n b := by
  intro s d hd
  have ht : m≤(P+1).eval n := by simpa using hm
  have h := physical_stage_budget copy hn hN B hB R hR hn0 hs hg p hp b q v hv a ha m ht
  refine h.trans ?_
  simp only [Polynomial.eval_add,Polynomial.eval_one,Nat.cast_add,Nat.cast_one]
  unfold stepError
  gcongr <;> exact le_rfl

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule141

/- Helper module SizeReduction. -/
section P2MDyadicModule142

set_option autoImplicit false

set_option maxHeartbeats 1200000

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Hex.Internal

namespace InfoLossLAR.WorstCase.NativeLLL

abbrev IntegerRows := List (List ℤ)

end InfoLossLAR.WorstCase.NativeLLL

end P2MDyadicModule142

/- Helper module Solutions.RegevBridgeNativeLLLOriginalBasis. -/
section P2MDyadicModule143

set_option autoImplicit true

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeLLL

open Hex.Internal

open scoped BigOperators

variable {n : Nat}

theorem basis_inputLattice_eq (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det ≠ 0) :
    IntegerBasis.inputLattice (basis B) (basis_det_ne_zero B hdet) = IntegerBasis.inputLattice B hdet := by
  apply SetLike.coe_injective
  rw [IntegerBasis.inputLattice_eq_target,IntegerBasis.inputLattice_eq_target,basis_lattice_eq]

end InfoLossLAR.WorstCase.NativeLLL

end P2MDyadicModule143

/- Helper module Solutions.RegevBridgeSmoothingDualSeparation. -/
section P2MDyadicModule144

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection

noncomputable section

variable {dimension : ℕ}

/-- A single genuine nonzero dual term forces reciprocal-width lattice
separation once the full smoothing error is below exp(-pi). -/
theorem smoothing_dual_separation
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi))
    (hwidth : 0 < width) (hsmoothing : smoothingParam lattice error ≤ width)
    (point : dual lattice) (hpoint : point ≠ 0) :
    1/width ≤ ‖(point : EuclideanSpace ℝ (Fin dimension))‖ := by
  have hs := summable_dual_of_smoothing lattice herror hwidth hsmoothing
  have hterm := hs.le_tsum (⟨point,hpoint⟩ : {point : dual lattice // point ≠ 0}) (fun _ _ => Real.exp_nonneg _)
  have hmass := dual_mass_le_of_smoothing lattice herror hwidth hsmoothing
  have hsingle : rho (1/width) (point : EuclideanSpace ℝ (Fin dimension)) ≤ Real.exp (-Real.pi) :=
    hterm.trans (hmass.trans hsmall)
  rw [rho,Real.exp_le_exp] at hsingle
  rw [one_div,inv_pow,div_inv_eq_mul] at hsingle
  have hnorm := norm_nonneg (point : EuclideanSpace ℝ (Fin dimension))
  have hproduct : (0 : ℝ) ≤ width*‖(point : EuclideanSpace ℝ (Fin dimension))‖ := mul_nonneg hwidth.le hnorm
  have hsquare : (1 : ℝ)^2 ≤ (width*‖(point : EuclideanSpace ℝ (Fin dimension))‖)^2 := by
    nlinarith [Real.pi_pos]
  have hlarge := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hproduct).mp hsquare
  exact (div_le_iff₀ hwidth).mpr (by nlinarith)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule144

/- Helper module Solutions.RegevBridgeDGSWidthStep. -/
section P2MDyadicModule145

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- The public fixed-family noise width, as a real analysis parameter. -/
def dgsSigma (dimension : ℕ) : ℝ := dimension+2

/-- Rational for rational r; no square-root dimension is encoded. -/
def dgsDecodingRadius (dimension : ℕ) (width : ℝ) : ℝ := dgsSigma dimension/(2*width)

/-- The genuine source smoothing promise itself proves the separation
needed by all retained fine-grid BDD queries. -/
theorem dgs_source_dual_separation
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width error : ℝ) (q : ℕ) [NeZero q]
    (hwidth : 0 < width) (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi))
    (hq : dgsSigma dimension ≤ (q : ℝ))
    (hsmoothing : smoothingParam lattice error ≤ width/(Real.sqrt 2*(q : ℝ))) :
    ∀ point : dual lattice,point ≠ 0 →
      2*dgsDecodingRadius dimension width ≤ ‖(point : Space (dimension:=dimension))‖ := by
  have hqpositive : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  have hreciprocal : 2*dgsDecodingRadius dimension width ≤ 1/(width/(Real.sqrt 2*(q : ℝ))) := by
    have hproduct : dgsSigma dimension ≤ Real.sqrt 2*(q : ℝ) :=
      hq.trans (le_mul_of_one_le_left hqpositive.le hroot)
    dsimp only [dgsDecodingRadius]
    have heq : 2*(dgsSigma dimension/(2*width))=dgsSigma dimension/width := by ring
    rw [heq,one_div_div]
    exact div_le_div_of_nonneg_right hproduct hwidth.le
  intro point hpoint
  exact hreciprocal.trans (smoothing_dual_separation lattice herror hsmall (by positivity) hsmoothing point hpoint)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule145

/- Helper module WidthSchedule. -/
section P2MDyadicModule146

set_option autoImplicit false

set_option maxHeartbeats 750000

open scoped BigOperators

namespace SingleWidth

noncomputable section

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

open InfoLossLAR.WorstCase.GaussianPoissonSeries InfoLossLAR.WorstCase.IntegerBasis

open InfoLossLAR.WorstCase.RationalGramSchmidt

open RegevLWE.GaussConv

theorem small_error {n : ℕ} (hn : 2 ≤ n) : smoothingError n ≤ Real.exp (-Real.pi) := by
  have h3 : 3 ≤ Nat.size (n+2) := (Nat.lt_size).mpr (by norm_num; omega)
  have hexp : Real.exp Real.pi ≤ (2:ℝ)^9 := by
    calc
      _ ≤ Real.exp 4 := Real.exp_le_exp.mpr Real.pi_lt_four.le
      _ = (Real.exp 1)^4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3:ℝ)^4 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
      _ ≤ _ := by norm_num
  unfold smoothingError
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (Real.exp_pos _)
  exact hexp.trans (pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.mul_self_le_mul_self h3]))

def startWidth {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (b : ℕ) : ℚ :=
  max (initialWidth (NativeLLL.basis B) b) (r * (famσ n : ℚ))

def terminal (n : ℕ) (r : ℚ) : ℝ :=
  (r:ℝ) * (famσ n : ℝ) / (Real.sqrt 2 * Real.sqrt n)

/-- The terminal lower edge still lies strictly above the smoothing threshold
for a valid source, and the upper edge gives the required decoder radius. -/
theorem terminal_window_valid {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (r : ℚ) (hr : 0 < r) (hp : dgsThreshold B ≤ (r:ℝ)) (v : ℝ)
    (hv : terminal n r / 2 ≤ v) (hv' : v ≤ terminal n r) :
    Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < v ∧
      Real.sqrt n / (Real.sqrt 2 * (r:ℝ)) ≤ (famσ n : ℝ)/(2*v) := by
  let η := smoothingParam (inputModule B) (smoothingError n)
  let d := Real.sqrt 2 * Real.sqrt n
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hs : 0 < (famσ n : ℝ) := by unfold famσ famL;positivity
  have hq : 0 < (famq n : ℝ) := by exact_mod_cast (NeZero.pos (famq n))
  have hd : 0 < d := mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr hn')
  have hw : 0 < terminal n r := div_pos (mul_pos hr' hs) hd
  have hσcle : 16*(famq n : ℝ)*Real.sqrt n*η ≤ (r:ℝ)*(famσ n : ℝ) := by
    apply (div_le_iff₀ hs).mp
    calc _ = dgsThreshold B := by unfold dgsThreshold;dsimp only [η];ring
         _ ≤ _ := hp
  have hroot : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · apply lt_of_lt_of_le _ hv
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    change (Real.sqrt 2 * (famq n:ℝ) * η) * 2 < (r:ℝ)*(famσ n:ℝ)/d
    apply (lt_div_iff₀ hd).mpr
    have heq : Real.sqrt 2 * (famq n:ℝ) * η * 2 * d = 4 * (famq n:ℝ)*Real.sqrt n*η := by
      dsimp only [d]; linear_combination 2 * (famq n:ℝ) * η * Real.sqrt n * hroot
    rw [heq]
    by_cases hz : η ≤ 0
    · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (by positivity) hz) (mul_pos hr' hs)
    have hh : 0 < (famq n:ℝ) * Real.sqrt n * η := by
      exact mul_pos (mul_pos hq (Real.sqrt_pos.mpr hn')) (lt_of_not_ge hz)
    linarith
  · have hvpos : 0<v := (half_pos hw).trans_le hv
    have hc := (le_div_iff₀ hd).mp hv'
    apply (div_le_div_iff₀ (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hr') (by positivity)).mpr
    calc
      _ = Real.sqrt 2 * (v * d) := by
        dsimp only [d]
        linear_combination -(v * Real.sqrt n) * hroot
      _ ≤ Real.sqrt 2 * ((r:ℝ)*(famσ n:ℝ)) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring

end

end SingleWidth

end P2MDyadicModule146

/- Helper module WidthProgram. -/
section P2MDyadicModule147

set_option autoImplicit false

set_option maxHeartbeats 950000

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.RunnableWidths

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding Integration9_9.TM2NativeFiniteDraw

open SingleWidth RegevLWE.GaussConv InfoLossLAR.WorstCase.RegevSketch

abbrev Data := List Unit × (ℚ × ℚ)

def fuel (d : Data) := d.1.flatMap (fun _ => List.replicate 5 ()) ++ [(),(),()]

@[fun_prop] theorem fuel_poly : Poly fuel := by unfold fuel;fun_prop

theorem fuel_length (d : Data) : (fuel d).length=5*d.1.length+3 := by
  simp [fuel,List.length_flatMap,List.sum_replicate,Nat.mul_comm]

def width (d : Data) (j : ℕ) : ℚ := d.2.1/(dyadicPower ((fuel d).take j) : ℚ)

@[fun_prop] theorem width_poly : Poly (fun x : Data×ℕ => width x.1 x.2) := by
  have ht : Poly (fun x : Data×ℕ => (fuel x.1).take x.2) :=
    Poly.comp (f:=fun p : List Unit×ℕ => p.1.take p.2) (g:=fun x : Data × ℕ => (fuel x.1,x.2))
      ⟨PolyProgram.listTake Automatic.enc ()⟩ (by fun_prop)
  unfold width
  fun_prop

def above (d : Data) (j : ℕ) : Bool :=
  let v := width d j
  let t := d.2.2*(d.1.length+2 : ℕ)
  decide (t*t < 2*(d.1.length:ℚ)*v*v)

@[fun_prop] theorem above_poly : Poly (fun x : Data×ℕ => above x.1 x.2) := by
  unfold above;fun_prop

def count (d : Data) := ((List.range (fuel d).length).filter (above d)).length

@[fun_prop] theorem count_poly : Poly count := by
  have hr : Poly (fun d : Data => List.range (fuel d).length) :=
    Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=fuel) Poly.list_indices fuel_poly
  unfold count
  have hf : Poly (fun d : Data => (List.range (fuel d).length).filter (above d)) :=
    Poly.list_filter above_poly hr
  fun_prop

theorem width_eq (d : Data) (j : ℕ) (hj : j≤(fuel d).length) :
    width d j=d.2.1/2^j := by simp [width,dyadicPower,List.length_take,min_eq_left hj]

theorem above_iff (d : Data) (j : ℕ) (hw : 0<d.2.1) (hr : 0<d.2.2)
    (hn : 0<d.1.length) :
    above d j=true ↔ terminal d.1.length d.2.2 < (width d j:ℝ) := by
  let v : ℝ := width d j
  let a : ℝ := (d.2.2:ℝ)*(famσ d.1.length:ℝ)
  let b : ℝ := Real.sqrt 2*Real.sqrt d.1.length
  have hb : 0<b := mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have ha : 0≤a := by dsimp [a]; positivity
  have hv : 0≤v := by dsimp [v,width,dyadicPower]; positivity
  have hbsq : b^2=2*(d.1.length:ℝ) := by simp [b,mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ d.1.length)]
  unfold above
  rw [decide_eq_true_eq]
  change _ ↔ a/b < v
  rw [div_lt_iff₀ hb]
  rw [←sq_lt_sq₀ ha (mul_nonneg hv hb.le),mul_pow v b,hbsq]
  have hcast : ((d.2.2*(d.1.length+2:ℕ))^2 < 2*(d.1.length:ℚ)*(width d j)^2) ↔
      a^2 < 2*(d.1.length:ℝ)*v^2 := by dsimp [a,v,famσ,famL];exact_mod_cast Iff.rfl
  convert hcast using 1 <;> constructor <;> intro h <;> nlinarith

def data {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) : Data :=
  (List.replicate n (),startWidth B r (n+1),r)

private theorem range_prefix (h m : ℕ) (hm : h ≤ m) :
    (List.range m).filter (fun j => decide (j<h))=List.range h := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => simp only [Nat.add_zero];apply List.filter_eq_self.mpr;intro x hx;simpa using List.mem_range.mp hx
  | succ k ih => rw [Nat.add_succ,List.range_succ,List.filter_append,ih (by omega)];simp

theorem count_first {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (hn : 2≤n)
    (hB : B.det≠0) (hr : 0<r) (hp : dgsThreshold B ≤ (r:ℝ)) :
    let d := data B r
    count d ≤ 5*n+2 ∧
    (∀ j ≤ count d, Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n) <
      (width d j:ℝ)) ∧
    Real.sqrt n/(Real.sqrt 2*(r:ℝ)) ≤ (famσ n:ℝ)/(2*(width d (count d):ℝ)) := by
  obtain ⟨h,hmax,hl,hu,hb⟩ := dimension_halvings hn B hB r hr hp
  let d := data B r
  have hlen : d.1.length=n := List.length_replicate
  have hw : 0<d.2.1 := (show 0<r*(famσ n:ℚ) by dsimp [famσ,famL]; positivity).trans_le (le_max_right _ _)
  have hF : (fuel d).length=5*n+3 := by rw [fuel_length,hlen]
  have equal (j : ℕ) (hj : j≤(fuel d).length) : (width d j:ℝ)=(startWidth B r (n+1):ℝ)/2^j := by
    rw [width_eq _ _ hj];push_cast; rfl
  have hc : count d=h := by
    unfold count
    have he : (List.range (fuel d).length).filter (above d)=List.range h := by
      have hh : (List.range (fuel d).length).filter (fun j => decide (j<h))=List.range h := by
        exact range_prefix _ _ (by omega)
      rw [←hh]
      apply List.filter_congr
      intro j hj
      have hj' := List.mem_range.mp hj
      rw [Bool.eq_iff_iff,above_iff d j hw hr (hlen ▸ (by omega)),decide_eq_true_eq,equal _ hj'.le,hlen]
      constructor
      · intro hlt
        by_contra! hle
        have hdec := div_le_div_of_nonneg_left (show (0:ℝ) ≤ startWidth B r (n+1) by exact_mod_cast hw.le)
          (by positivity : (0:ℝ)<2^h) (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hle)
        exact (not_lt_of_ge (hdec.trans hu)) hlt
      · exact hb j
    rw [he,List.length_range]
  change count d≤_ ∧ _
  rw [hc]
  have hd := terminal_window_valid hn B r hr hp _ hl hu
  refine ⟨hmax,?_,?_⟩
  · intro j hj
    rw [equal j (by omega)]
    exact hd.1.trans_le (div_le_div_of_nonneg_left (show 0≤(startWidth B r (n+1):ℝ) by exact_mod_cast hw.le)
      (by positivity) (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj))
  · rw [equal h (by omega)];exact hd.2

end InfoLossLAR.WorstCase.RegevSearch.RunnableWidths

end P2MDyadicModule147

/- Helper module Parameters. -/
section P2MDyadicModule148

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

open QAlgorithms.Complexity RegevSketch GaussianIteration

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeAffineEncoding (readMatrix readMatrix_append)

open GaussianRandomizedRounding.Wide.Coherent (readRational readRational_append)

open ShortProbePlan (parts parts_pair)

noncomputable section

abbrev Raw := (List (List ℤ) × ℚ) × List Unit

def read (w : Str) : Raw :=
  let s := parts w
  let t := parts s.2
  (((readMatrix s.1).2,(readRational t.1).2),(parts t.2).2.map (fun _ => ()))

@[fun_prop] theorem read_poly : Poly read := by unfold read;fun_prop

theorem read_input {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (k : ℕ) :
    read (dgsInput B r 1 k)=((RationalInverse.Native.inputRows B,r),List.replicate k ()) := by
  simp only [read,dgsInput,parts_pair]
  rw [←List.append_nil (encMat encI B),readMatrix_append,←List.append_nil (encQ r),show readRational (encQ r++[])=([],r) from readRational_append r []]
  simp [unary,RationalInverse.Native.inputRows]

def dim (d : Raw) : List Unit := d.1.1.map (fun _ => ())

@[fun_prop] theorem dim_poly : Poly dim := by unfold dim;fun_prop

def copies (P : Polynomial ℕ) (d : Raw) := List.replicate (P.eval (dim d).length) ()

@[fun_prop] theorem copies_poly (P : Polynomial ℕ) : Poly (copies P) :=
  Poly.comp (f:=fun x : List Unit => List.replicate (P.eval x.length) ()) (g:=dim) (Integration9_9.TM2PolynomialBudget.polynomialSlots_poly P) dim_poly

def initial (P : Polynomial ℕ) (d : Raw) : FirstPool.Batch :=
  ((((d.1.1,NativeLLL.Uniform.reduce d.1.1),d.1.2),dim d),copies P d)

@[fun_prop] theorem initial_poly (P : Polynomial ℕ) : Poly (initial P) := by unfold initial;fun_prop

def widths (d : Raw) : RunnableWidths.Data :=
  (dim d,FirstPool.width ((((d.1.1,NativeLLL.Uniform.reduce d.1.1),d.1.2),dim d)),d.1.2)

@[fun_prop] theorem widths_poly : Poly widths := by unfold widths;fun_prop

def budget (P : Polynomial ℕ) (d : Raw) := precisionTape ((dim d,copies P d),d.2)

@[fun_prop] theorem budget_poly (P : Polynomial ℕ) : Poly (budget P) := by unfold budget;fun_prop

def oracle (P : Polynomial ℕ) (d : Raw) : List Unit :=
  let calls := copies P d ++ [()] ++ copies P d ++ [()]
  let t := multiplied (List.replicate 16 (),multiplied (calls++[()],budget P d++[()]))
  multiplied (t,t)

@[fun_prop] theorem oracle_poly (P : Polynomial ℕ) : Poly (oracle P) := by unfold oracle;fun_prop

def old (v : Raw × ℕ) := RunnableWidths.width (widths v.1) v.2

@[fun_prop] theorem old_poly : Poly old := by
  exact Poly.comp RunnableWidths.width_poly (g:=fun v : Raw×ℕ => (widths v.1,v.2)) (by fun_prop)

def next (v : Raw × ℕ) := if v.2 < RunnableWidths.count (widths v.1) then old v / 2 else v.1.1.2

@[fun_prop] theorem next_poly : Poly next := by unfold next;fun_prop

theorem exact_parameters (P : Polynomial ℕ) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (k : ℕ) :
    let d := read (dgsInput B r 1 k)
    initial P d=(FirstPool.cfg B (NativeLLL.basis B) r (List.replicate n ()),List.replicate (P.eval n) ()) ∧
      widths d=RunnableWidths.data B r ∧
      (budget P d).length=precision n (P.eval n) k ∧
      (oracle P d).length=poolBDDPrecision (((P+1)+(P+1)).eval n) (precision n (P.eval n) k) := by
  dsimp only
  rw [read_input]
  let d : Raw := ((RationalInverse.Native.inputRows B,r),List.replicate k ())
  have hd : dim d=List.replicate n () := by
    apply Integration9_9.TM2PolynomialBudget.unitList_eq
    simp [dim,d,RationalInverse.Native.inputRows]
  have hm : copies P d=List.replicate (P.eval n) () := by simp [copies,hd]
  have hc : initial P d=(FirstPool.cfg B (NativeLLL.basis B) r (List.replicate n ()),List.replicate (P.eval n) ()) := by
    simp only [initial,hm,hd,d,NativeLLL.Uniform.reduce_exact B hB];rfl
  have hw := congrArg (fun s : RationalGramSchmidt.Native.ExactWide.Setup => s.1.2)
    (FirstPool.settings_exact B (NativeLLL.basis B) r (List.replicate n ()))
  have hb : (budget P d).length=precision n (P.eval n) k := by simp [budget,precisionTape_len,hd,hm,d]
  refine ⟨hc,?_,hb,?_⟩
  · change widths d=_
    simp only [widths,hd,d,NativeLLL.Uniform.reduce_exact B hB,RunnableWidths.data,Prod.mk.injEq,true_and,and_true]
    exact hw
  · change (oracle P d).length=_
    simp only [oracle,multiplied_len,List.length_append,List.length_replicate,List.length_cons,List.length_nil,hm,hb,Polynomial.eval_add,Polynomial.eval_one,poolBDDPrecision]
    ring

end

end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

end P2MDyadicModule148

/- Helper module StepGeometry. -/
section P2MDyadicModule149

set_option autoImplicit false

set_option maxHeartbeats 1100000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

open RegevLWE.GaussConv GaussianPoissonSeries IntegerBasis RegevSketch PhysicalFourier

noncomputable section

def radius (n : ℕ) (next : ℚ) : ℝ := Real.sqrt n/(Real.sqrt 2*(next:ℝ))

theorem radius_pos {n : ℕ} {r : ℚ} (hn : 0<n) (hr : 0<r) : 0<radius n r := by
  unfold radius; positivity

theorem radius_sq (n : ℕ) (r : ℚ) :
    (n:ℝ)*(1/(Real.sqrt 2*(r:ℝ)))^2=(radius n r)^2 := by
  simp only [radius,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg _),mul_one_div]

theorem half_radius (n : ℕ) (R : ℚ) (hR : 0<R) :
    radius n (R/2) ≤ (famσ n:ℝ)/(2*(R:ℝ)) := by
  have ha := sq_nonneg (Real.sqrt (n:ℝ)-Real.sqrt 2)
  have hn := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ)≤n)
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hroot : 0<Real.sqrt 2 := by positivity
  have hr : 0<(R:ℝ) := by exact_mod_cast hR
  unfold radius
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  change _ ≤ ((n+2:ℕ):ℝ)*_
  push_cast
  have h : 2*Real.sqrt (n:ℝ)*Real.sqrt 2≤(n:ℝ)+2 := by nlinarith
  have hh : 4*Real.sqrt (n:ℝ) ≤ ((n:ℝ)+2)*Real.sqrt 2 := by
    nlinarith [mul_le_mul_of_nonneg_right h hroot.le,
      congrArg (fun x : ℝ => Real.sqrt n*x) h2]
  nlinarith [mul_le_mul_of_nonneg_right hh hr.le]

theorem denominator_cap {n : ℕ} {r : ℚ} (hr : 0<r) :
    radius n r ≤ (n+1:ℕ)*(r.den+1:ℕ) := by
  have hroot : (1:ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  have hn : Real.sqrt n ≤ (n:ℝ)+1 := by
    have h := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ)≤n)
    nlinarith [sq_nonneg (n:ℝ),Real.sqrt_nonneg (n:ℝ)]
  have hrR : 0<(r:ℝ) := by exact_mod_cast hr
  have hnum : 0<r.num := by exact (Rat.num_pos.mpr hr)
  have hi : (1:ℝ)≤(r.num:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ r.num by omega)
  have hden : 0<(r.den:ℝ) := by exact_mod_cast r.den_pos
  have heq : (r:ℝ)*r.den=r.num := by rw [Rat.cast_def];field_simp
  unfold radius
  rw [div_le_iff₀ (by positivity)]
  have hh : (1:ℝ) ≤ (r.den+1:ℕ)*(Real.sqrt 2*(r:ℝ)) := by
    calc
      _ ≤ (r:ℝ)*r.den := heq ▸ hi
      _ ≤ (r.den+1:ℕ)*(Real.sqrt 2*(r:ℝ)) := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hroot hrR.le,
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hrR.le) hden.le]
  push_cast
  push_cast at hh
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0≤(n:ℝ)+1 by positivity)]

theorem separated {n : ℕ} (hn : 2≤n) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (R : ℚ) (hR : 0<R)
    (hs : Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n)<(R:ℝ))
    (c : ℝ) (hc : c≤(famσ n:ℝ)/(2*(R:ℝ))) :
    Separated (dual (inputLattice B hB)) c := by
  have he : inputModule B=inputLattice B hB := by
    unfold inputModule inputLattice
    congr 2
    funext i
    simp [realBasis_apply,latVec,Matrix.mulVec_single]
  have hq : 0<famq n := (NeZero.pos _)
  have : NeZero (famq n) := ⟨hq.ne'⟩
  have hpos : (0:ℝ)<Real.sqrt 2*(famq n:ℝ) := by positivity
  have hsm : smoothingParam (inputLattice B hB) (smoothingError n) ≤ (R:ℝ)/(Real.sqrt 2*(famq n:ℝ)) := by
    rw [le_div_iff₀ hpos,←he,mul_comm];exact hs.le
  have hsig : dgsSigma n=(famσ n:ℝ) := by simp [dgsSigma,famσ,famL]
  have hh := dgs_source_dual_separation (inputLattice B hB) (R:ℝ) (smoothingError n) (famq n)
    (by exact_mod_cast hR) (by unfold smoothingError;positivity) (SingleWidth.small_error hn)
    (show dgsSigma n≤(famq n:ℝ) by rw [hsig];exact_mod_cast (famσ_lt_famq n).le) hsm
  simp only [dgsDecodingRadius,hsig] at hh
  intro z hz
  exact (mul_le_mul_of_nonneg_left hc (by norm_num)).trans (hh z hz)

end

end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

end P2MDyadicModule149

/- Helper module Launcher. -/
section P2MDyadicModule150

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

open QAlgorithms.Complexity RegevLWE.GaussConv IntegerBasis RegevSketch PhysicalFourier GaussianIteration

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

def stageProgram (P : Polynomial ℕ) (v : Str × ℕ) :=
  let d := read v.1
  (d.1.1,((old (d,v.2),next (d,v.2)),(copies P d,(budget P d,oracle P d))))

@[fun_prop] theorem stageProgram_poly (P : Polynomial ℕ) : Poly (stageProgram P) := by unfold stageProgram;fun_prop

theorem width_step (d : RunnableWidths.Data) (i : ℕ) (h : i+1≤(RunnableWidths.fuel d).length) :
    RunnableWidths.width d (i+1) = RunnableWidths.width d i/2 := by
  rw [RunnableWidths.width_eq _ _ h,RunnableWidths.width_eq _ _ (by omega),pow_succ]
  ring

theorem stage_guarantees {n : ℕ} (hn : 2≤n) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (r : ℚ) (hr : 0<r) (hp : dgsThreshold B ≤ (r:ℝ)) (user i : ℕ) :
    let d := read (dgsInput B r 1 user)
    let w := widths d
    let h := RunnableWidths.count w
    let R := old (d,i)
    let t := next (d,i)
    let c := radius n t
    h≤5*n+2 ∧ (i≤h →
      (0<R ∧ 0<t) ∧
      (Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n)<(R:ℝ)) ∧
      (0<c ∧ c ≤ (famσ n:ℝ)/(2*(R:ℝ))) ∧
      ((n:ℝ)*(1/(Real.sqrt 2*(t:ℝ)))^2 ≤ c^2 ∧ c≤(n+1:ℕ)*(t.den+1:ℕ)) ∧
      Separated (dual (inputLattice B hB)) c ∧
      (i<h → t=old (d,i+1)) ∧ (i=h → t=r)) := by
  intro d w h R t c
  have hw : w=RunnableWidths.data B r := (exact_parameters 0 B hB r user).2.1
  obtain ⟨hm,hsm,hl⟩ := RunnableWidths.count_first B r hn hB hr hp
  rw [←hw] at hm hsm hl
  refine ⟨hm,?_⟩
  intro hi
  have hdim : w.1.length=n := by rw [hw];simp [RunnableWidths.data]
  have hd : d.1.2=r := by simp [d,read_input]
  have hwpos : 0<w.2.1 := by
    rw [hw]
    exact (show 0<r*(famσ n:ℚ) by simp [famσ,famL];positivity).trans_le (le_max_right _ _)
  have hF : i≤(RunnableWidths.fuel w).length := by
    rw [RunnableWidths.fuel_length,hdim];omega
  have hR : 0<R := by
    change 0<RunnableWidths.width w i
    rw [RunnableWidths.width_eq _ _ hF]
    exact div_pos hwpos (pow_pos (by norm_num) _)
  have hnext : i<h → t=R/2 := by intro hi;exact if_pos hi
  have hlast : i=h → t=r := by intro hi;exact (if_neg (by omega : ¬ i<h)).trans hd
  have ht : 0<t := by
    by_cases lt : i<h
    · rw [hnext lt];exact div_pos hR (by norm_num)
    · rw [hlast (by omega)];exact hr
  have hcut : c≤(famσ n:ℝ)/(2*(R:ℝ)) := by
    by_cases lt : i<h
    · change radius n t≤_
      rw [hnext lt];exact half_radius n R hR
    · have eq : i=h := by omega
      change radius n t≤(famσ n:ℝ)/(2*(RunnableWidths.width w i:ℝ))
      rw [hlast eq,eq];exact hl
  have hc : 0<c := radius_pos (by omega) ht
  refine ⟨⟨hR,ht⟩,hsm i hi,⟨hc,hcut⟩,⟨(radius_sq n t).le,denominator_cap ht⟩,
    separated hn B hB R hR (hsm i hi) c hcut,?_,hlast⟩
  intro lt
  rw [hnext lt]
  apply Eq.symm
  apply width_step
  change i+1≤(RunnableWidths.fuel w).length
  rw [RunnableWidths.fuel_length,hdim]
  omega

end

end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

end P2MDyadicModule150

/- Helper module ComputeSlot. -/
section P2MDyadicModule151

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 950000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit NativeWordLayout NativeWordDescription

open Integration9_9.TM2PlatformSerialization CoherentClassicalOracle

open scoped Classical BigOperators

noncomputable section

variable {f : Str → Str} (P : PolyProgram id id f) {h j : ℕ}

def input (p : Fin j→Source h) (x : Bits h) := List.ofFn (fun i => (p i).read x)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule151

/- Helper module Modulus. -/
section P2MDyadicModule152

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

end P2MDyadicModule152

/- Helper module SignedSlot. -/
section P2MDyadicModule153

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1100000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization GridReadout.Axis PhysicalFourier

open TM2Boolean TM2Boolean.PolyProgramCircuit NativeWordLayout

open scoped Classical BigOperators

noncomputable section

@[fun_prop] theorem prefix_poly : Poly (fun x : List Unit×List Unit => prefixWord x.1 x.2) := by unfold prefixWord;fun_prop

variable {h n b : ℕ}

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end P2MDyadicModule153

/- Helper module RunRecipe. -/
section P2MDyadicModule154

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1100000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.PlacedCPU

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped Classical BigOperators

noncomputable section

abbrev Recipe := (List Unit×List Unit)×List GateCode

def bound {α : Type} [Coding α] {f : Str→List α} (hf : Poly f) :=
  hf.program.sizeBound.comp (3*Polynomial.X)

theorem bound_length {α : Type} [Coding α] {f : Str→List α} (hf : Poly f) (s : Str) :
    (f s).length≤(bound hf).eval s.length := by
  have hl := hf.program.length_bound s
  change (encodeList enc (f s)).length ≤ hf.program.sizeBound.eval (encodeList encodeBool s).length at hl
  apply (EncodedList.length_le _ _).trans
  simpa only [bound,BooleanLists.length,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using hl

variable (plan : Str→Recipe) (hp : Poly plan)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.PlacedCPU

end P2MDyadicModule154

/- Helper module SignedRecipe. -/
section P2MDyadicModule155

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

@[fun_prop] theorem digits_poly : Poly digits := by unfold digits;fun_prop

@[fun_prop] theorem inputTape_poly : Poly inputTape := by unfold inputTape;fun_prop

@[fun_prop] theorem clock_poly : Poly clock := by unfold clock;fun_prop

@[fun_prop] theorem slot_poly : Poly slot := by unfold slot;fun_prop

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end P2MDyadicModule155

/- Helper module GridBudget. -/
section P2MDyadicModule156

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

end P2MDyadicModule156

/- Helper module GridProgram. -/
section P2MDyadicModule157

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

end P2MDyadicModule157

/- Helper module Universal. -/
section P2MDyadicModule158

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

open QAlgorithms.Complexity RegevSketch GaussianIteration

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AdaptiveStages

noncomputable section

def rowGrid (v : Raw×ℕ) : List Unit := PhysicalGrid.gridTape (v.1.1.1,next v,dim v.1)

@[fun_prop] theorem rowGrid_poly : Poly rowGrid := by unfold rowGrid;fun_prop

def rowSlot (v : Raw×ℕ) : List Unit := SignedSlot.slot (dim v.1,rowGrid v)

@[fun_prop] theorem rowSlot_poly : Poly rowSlot := by unfold rowSlot;fun_prop

def stages (d : Raw) := List.range (RunnableWidths.fuel (widths d)).length

@[fun_prop] theorem stages_poly : Poly stages := Poly.comp
  (f:=fun l : List Unit => List.range l.length) (g:=fun d => RunnableWidths.fuel (widths d))
  Poly.list_indices (by fun_prop)

def universalSlot (P : Polynomial ℕ) (d : Raw) :=
  FirstPool.slot (initial P d).1 ++ (stages d).flatMap (fun i => rowSlot (d,i))

@[fun_prop] theorem universalSlot_poly (P : Polynomial ℕ) : Poly (universalSlot P) := by
  unfold universalSlot
  fun_prop

def poolSpace (P : Polynomial ℕ) (s : Str) := multiplied (copies P (read s),universalSlot P (read s))

@[fun_prop] theorem poolSpace_poly (P : Polynomial ℕ) : Poly (poolSpace P) := by unfold poolSpace;fun_prop

theorem first_fits (P : Polynomial ℕ) (d : Raw) :
    (FirstPool.slot (initial P d).1).length≤(universalSlot P d).length := by
  simp [universalSlot]

theorem later_fits (P : Polynomial ℕ) (d : Raw) (i : ℕ) (hi : i<(RunnableWidths.fuel (widths d)).length) :
    (rowSlot (d,i)).length≤(universalSlot P d).length := by
  have hm : i∈stages d := List.mem_range.mpr hi
  have sub (xs : List ℕ) (hx : i∈xs) : (rowSlot (d,i)).length≤(xs.flatMap (fun j => rowSlot (d,j))).length := by
    induction xs with
    | nil => simp at hx
    | cons a xs ih => rcases List.mem_cons.mp hx with rfl|hh
                      · simp
                      · exact (ih hh).trans (by simp)
  have hs := sub _ hm
  simp only [universalSlot,List.length_append]
  omega

theorem pool_size (P : Polynomial ℕ) (s : Str) :
    (poolSpace P s).length=(copies P (read s)).length*(universalSlot P (read s)).length :=
  multiplied_len _ _

theorem pool_cap (P : Polynomial ℕ) : ∃ H : Polynomial ℕ, ∀ s : Str,
    (copies P (read s)).length*(universalSlot P (read s)).length≤H.eval s.length := by
  have hp : Poly (fun s : Str => (poolSpace P s).map (fun _ => true)) := by fun_prop
  obtain ⟨H,hH⟩ := Integration9_9.TM2OutputLength.polynomial_output_length (Integration9_9.TM2PlatformSerialization.polyTime_of_poly hp).some
  exact ⟨H,fun s => by simpa only [id_eq,List.length_map,pool_size] using hH s⟩

theorem all_stage_fit (P : Polynomial ℕ) {n : ℕ} (hn : 2≤n) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (r : ℚ) (hr : 0<r) (hp : dgsThreshold B ≤ (r:ℝ)) (k i : ℕ) :
    let d := read (dgsInput B r 1 k)
    i≤RunnableWidths.count (widths d) → (rowSlot (d,i)).length≤(universalSlot P d).length := by
  intro d hi
  have hw : widths d=RunnableWidths.data B r := (exact_parameters P B hB r k).2.1
  have hc := (RunnableWidths.count_first B r hn hB hr hp).1
  apply later_fits
  rw [hw] at hi ⊢
  rw [RunnableWidths.fuel_length]
  change i < 5*(List.replicate n ()).length+3
  rw [List.length_replicate]
  omega

end

end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

end P2MDyadicModule158

/- Helper module SlotRead. -/
section P2MDyadicModule159

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

open QAlgorithms.Complexity AdaptiveStages GaussianIteration

open TM2Boolean.PolyProgramCircuit Integration9_9.TM2NativeAffineEmitter

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

theorem preserve (S : List Unit) {code word : Str} (h : code <+: word) (fit : code.length ≤ S.length) :
    code <+: NativePaddedWords.current (S,word) := by
  obtain ⟨tail,rfl⟩ := h
  simp only [NativePaddedWords.current,List.append_assoc,List.take_append,List.take_of_length_le fit]
  exact ⟨_,rfl⟩

theorem first_read (P : Polynomial ℕ) (d : Raw) (t : QAlgorithms.Complexity.Bits (FirstPool.tape (initial P d)).length)
    (i : Fin (initial P d).2.length) :
    let v := initial P d
    let w := FirstPool.slice (((FirstPool.slot v.1).length,FirstPool.outputData v (FirstPool.answer v t)),i.val)
    let z := FirstPool.rowWord (v.1,List.ofFn (FirstPool.splitTape v t i))
    z <+: NativePaddedWords.current (universalSlot P d,w) := by
  intro v w z
  have hl := FirstPool.row_fits v.1 (List.ofFn (FirstPool.splitTape v t i)) List.length_ofFn
  apply preserve _ _ (hl.trans (first_fits P d))
  obtain ⟨tail,ht⟩ := FirstPool.output_tail v t
  change z <+: FirstPool.slice (((FirstPool.slot v.1).length,FirstPool.outputData v (FirstPool.answer v t)),i.val)
  rw [ht,FirstPool.runs,FirstPool.select_cell _ _ (fun j => FirstPool.code_length _ _)]
  change z <+: NativePaddedWords.current (_,z)
  rw [NativePaddedWords.current_eq _ z hl]
  exact ⟨_,rfl⟩

theorem all_descriptions (F : MFamily) (hF : IsMQPT F) (P : Polynomial ℕ)
    (body : OracleTable.Inputs→List Unit) (hb : Poly body) (J : Polynomial ℕ) :
    ∃ (v : Str→Str), PolyTimeComputable v ∧ ∀ s h j tail : Str,
      h.length≤(poolSpace P s).length → j.length≤J.eval s.length →
      OracleTable.lookup (v (unary s.length)++tail,(body (s,h,j)).length)=F.encAt (body (s,h,j)).length := by
  obtain ⟨H,hh⟩ := pool_cap P
  obtain ⟨_,v,hv,_,hlookup⟩ := OracleTable.table_for_slots F hF body hb H J
  exact ⟨v,hv,fun s h j tail hsz hjsz => hlookup s h j tail (hsz.trans (by rw [pool_size];exact hh _)) hjsz⟩

end

end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

end P2MDyadicModule159

/- Helper module HistoryLaw. -/
section P2MDyadicModule160

set_option autoImplicit false

set_option linter.style.haveILetI false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open QAlgorithms.Complexity SharedPoolCoherence CoherentDecoder RegevSketch

noncomputable section

def close {X : Type*} (p q : PMF X) (d : ℝ) := ∀ f : Test X, |evaluate p f-evaluate q f|≤d

theorem history_bound {Ω X Y : Type*} [Fintype Ω] (μ : PMF Ω) (decode : Ω→X) (K : Ω→PMF Y)
    (a : PMF X) (b : PMF Y) (d : Test X) (δ : ℝ) (hp : close (μ.map decode) a δ)
    (hr : ∀ x, μ x≠0 → ∀ f : Test Y, |evaluate (K x) f-evaluate b f|≤(d (decode x):ℝ)) :
    close (μ.bind K) b (δ+evaluate a d) := by
  intro f
  let c := evaluate b f
  let w := fun x => (μ x).toReal
  have hsum : ∑ x, w x = 1 := by simpa only [tsum_fintype,w] using (mass_summable μ).tsum_eq
  have eq : evaluate (μ.bind K) f-c=∑ x,w x*(evaluate (K x) f-c) := by
    rw [eval_bind]
    change (∑' x, w x*evaluate (K x) f)-c=_
    simp only [tsum_fintype,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
  have hb : |∑ x,w x*(evaluate (K x) f-c)| ≤ ∑ x,w x*(d (decode x):ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum;intro x hx
    by_cases hn : μ x=0
    · simp [w,hn]
    · rw [abs_mul,abs_of_nonneg (show 0≤w x from ENNReal.toReal_nonneg)]
      exact mul_le_mul_of_nonneg_left (hr x hn f) ENNReal.toReal_nonneg
  have hh : evaluate (μ.map decode) d=∑ x,w x*(d (decode x):ℝ) := by
    rw [eval_map,evaluate,tsum_fintype];rfl
  have hz := (abs_le.mp (hp d)).2
  change |evaluate (μ.bind K) f-c|≤_
  rw [eq]
  exact hb.trans (by rw [←hh];linarith)

structure Round {n : ℕ} (C : MFamily) (P : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (R t : ℚ) (budget m : ℕ) (prev : PMF (Rows n (P.eval n))) (out : PMF (Rows n m)) where
  oldBits : ℕ
  tape : PMF (Bits oldBits)
  decode : Bits oldBits→Rows n (P.eval n)
  row : Bits oldBits→PMF (Vec n)
  before : prev=tape.map decode
  after_ : out=tape.bind (fun x => tuple (row x) m)
  grid : ℕ
  covers : gridAdequate B R (2^grid)
  I : Type
  inst : Fintype I
  inhabited : Nonempty I
  query : I→Query B R
  amp : I→ℂ
  norm : letI := inst;∑ i,‖amp i‖^2=1
  prep : ℝ
  prep_nonneg : 0≤prep
  L : ℕ
  length_ge : budget+1≤L
  source : prep≤2/(L:ℝ)+1/(2:ℝ)^n+2*Real.sqrt ((1/4:ℝ)^n)
  event : letI := inst; ∀ x, tape x≠0 → decode x ∈ keeps (P.eval n) (imageGrid n (2^grid)) → ∀ T : Finset (Vec n),
    |finiteMass (row x) T- ∑ z∈T, coefficientMass B t z| ≤ 2*prep+
      4*Real.sqrt (failureMass C (poolBDDPrecision (((P+1)+(P+1)).eval n) budget) (decode x) query amp)
      +4*Real.sqrt (2*(1/2:ℝ)^n)+1/(4*((budget:ℝ)+1))+GridReadout.gridError n

theorem round_bound {n : ℕ} {C : MFamily} {P : Polynomial ℕ} {N : ℕ} {S : Set ℕ} {e : ℕ→ℝ}
    (copy : CopyBudget C P ((P+1)+(P+1)) N S e) (hn : n∈S) (hN : N≤n) (hn0 : 0<n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (R t : ℚ) (hR : 0<R) (ht : 0<t)
    (hs : Real.sqrt 2*(famq n:ℝ)*RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n)<(R:ℝ))
    {budget m : ℕ} (hm : m≤P.eval n+1) (prev : PMF (Rows n (P.eval n))) (out : PMF (Rows n m))
    (w : Round C P B R t budget m prev out) (δ : ℝ)
    (hp : close prev (tuple (gaussian B hB R (by exact_mod_cast hR)) (P.eval n)) δ) :
    close out (tuple (gaussian B hB t (by exact_mod_cast ht)) m) (δ+stepError P e n budget) := by
  letI := w.inst
  letI := w.inhabited
  let s := keeps (P.eval n) (imageGrid n (2^w.grid))
  let a := 2*w.prep+4*Real.sqrt (2*(1/2:ℝ)^n)+1/(4*((budget:ℝ)+1))+GridReadout.gridError n
  have ha : 0≤a := by dsimp [a];positivity [w.prep_nonneg,geom_pos n]
  let d (z : Rows n (P.eval n)) := a+4*Real.sqrt (failureMass C (poolBDDPrecision (((P+1)+(P+1)).eval n) budget) z w.query w.amp)
  have hd (z) : 0≤d z := add_nonneg ha (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hac : a≤12*geom n+5/((budget:ℝ)+1) := analytic_cost n budget w.L (by exact_mod_cast w.length_ge) n le_rfl _ w.source
  let p := gaussian B hB R (by exact_mod_cast hR)
  let q := gaussian B hB t (by exact_mod_cast ht)
  have old := one_stage_bound copy hn hN B hB R hR hn0 hs w.covers p (fun z => gaussian_real ..) budget
    w.query w.amp w.norm a ha hac m hm
  change evaluate (tuple p (P.eval n)) (stageTest s d hd m) ≤ stepError P e n budget at old
  rw [w.after_]
  have hp' : close (w.tape.map w.decode) (tuple p (P.eval n)) δ := w.before ▸ hp
  have bound := history_bound w.tape w.decode (fun x => tuple (w.row x) m) (tuple p (P.eval n)) (tuple q m) (stageTest s d hd m) δ hp' (by
    intro x hx f
    apply stageTest_lifts s d hd m q (w.decode x) (w.row x) _ f
    intro hz T
    have he := w.event x hx hz T
    have hw : finiteMass q T=∑ z∈T,coefficientMass B t z := by simp only [finiteMass,q,gaussian_real]
    rw [hw];apply he.trans;dsimp only [d,a];ring_nf;exact le_rfl)
  intro f
  exact (bound f).trans (by linarith)

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule160

/- Helper module Execution. -/
section P2MDyadicModule161

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open QAlgorithms.Complexity SharedPoolCoherence RegevSketch IntegerBasis

noncomputable section

abbrev W {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (i : ℕ) := RunnableWidths.width (RunnableWidths.data B r) i

abbrev stop {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) := RunnableWidths.count (RunnableWidths.data B r)

theorem width_positive {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (hr : 0<r) (i : ℕ) : 0<W B r i := by
  have h : 0<SingleWidth.startWidth B r (n+1) := (show 0<r*(famσ n:ℚ) by simp [famσ,famL];positivity).trans_le (le_max_right _ _)
  apply div_pos h
  unfold Integration9_9.TM2NativeFiniteDraw.dyadicPower
  positivity

theorem width_start {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) : W B r 0=FirstPool.start (NativeLLL.basis B) r := by
  rw [W,RunnableWidths.width_eq _ _ (Nat.zero_le _),pow_zero,div_one];rfl

def zeroIdeal {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (m : ℕ) :=
  tuple (FirstPool.rowPMF n (FirstPool.cfg B (NativeLLL.basis B) r (List.replicate n ()))) m

theorem begin_close {n : ℕ} (hn : 0<n) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (r : ℚ) (hr : 0<r) (m : ℕ) : close (zeroIdeal B r m)
    (tuple (gaussian B hB (W B r 0) (by exact_mod_cast width_positive B r hr 0)) m) (m*FirstPool.cost n n) := by
  let D := NativeLLL.basis B
  have hD : D.det≠0 := NativeLLL.basis_det_ne_zero B hB
  have he {t : ℕ} (A : Matrix (Fin t) (Fin t) ℤ) (hA : A.det≠0) : inputModule A=inputLattice A hA := by
    unfold inputModule inputLattice;congr 2;funext i;simp [realBasis_apply,latVec,Matrix.mulVec_single]
  have hDB : inputModule D=inputModule B := (he D hD).trans ((NativeLLL.basis_inputLattice_eq B hB).trans (he B hB).symm)
  obtain ⟨p,hp,good⟩ := FirstPool.initial_pool B D hB hD hDB hn r (List.replicate n ())
  have pe : p=gaussian B hB (W B r 0) (by exact_mod_cast width_positive B r hr 0) := by
    apply gaussian_unique;intro z;rw [width_start];exact hp z
  rw [←pe]
  intro f
  simpa only [List.length_replicate,zeroIdeal,D] using good m f

theorem single_eval {X : Type*} (p : PMF X) (f : Test X) :
    evaluate (tuple p 1) (fun y => f (y 0))=evaluate p f := by
  rw [eval_succ p 0]
  apply congrArg (evaluate p)
  funext x;apply Subtype.ext
  change evaluate (PMF.pure _) _=_
  rw [eval_pure];rfl

def eventTest {X : Type*} (T : Finset X) : Test (Fin 1→X) := fun y => indicator (fun x => x∈T) (y 0)

structure Execution {n : ℕ} (H C : MFamily) (P : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (k : ℕ) where
  layer : ℕ→PMF (Rows n (P.eval n))
  boot : layer 0=zeroIdeal B r (P.eval n)
  last : PMF (Rows n 1)
  physical : ∀ i<stop B r, Round C P B (W B r i) (W B r (i+1))
    (precision n (P.eval n) k) (P.eval n) (layer i) (layer (i+1))
  terminal : Round C P B (W B r (stop B r)) r (precision n (P.eval n) k) 1 (layer (stop B r)) last
  reads : outputProb H (dgsInput B r 1 k) (fun out => ∃ z : Vec n, encVec encI z <+: out)=1
  read_event : ∀ T : Finset (Vec n), outputProb H (dgsInput B r 1 k) (fun out => ∃ z∈T,encVec encI z <+: out)=
    evaluate last (eventTest T)

theorem from_execution {n : ℕ} {C : MFamily} {P : Polynomial ℕ} {N : ℕ} {S : Set ℕ} {e : ℕ→ℝ}
    (copy : CopyBudget C P ((P+1)+(P+1)) N S e) (hn : n∈S) (hN : N≤n) (hn2 : 2≤n) (he : 0≤e n)
    (H : MFamily) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (hr : 0<r) (hp : dgsThreshold B≤(r:ℝ))
    (k : ℕ) (z : Execution H C P B r k) :
    ∃ b : ℕ, gridAdequate B (r:ℝ) (2^b) ∧
      outputProb H (dgsInput B r 1 k) (fun out => ∃ v : Vec n, encVec encI v <+: out)=1 ∧
      ∀ T : Finset (Vec n), |outputProb H (dgsInput B r 1 k) (fun out => ∃ v∈T,encVec encI v <+: out)-
        fourierEvent B r (2^b) T| ≤ totalError P e n+1/(4*((k:ℝ)+1)) := by
  let E := stepError P e n (precision n (P.eval n) k)
  let D (i : ℕ) := ((P.eval n:ℕ):ℝ)*FirstPool.cost n n+(i:ℝ)*E
  have hn0 : 0<n := by omega
  obtain ⟨hh,hsm,_⟩ := RunnableWidths.count_first B r hn2 hB hr hp
  let p (i : ℕ) := gaussian B hB (W B r i) (by exact_mod_cast width_positive B r hr i)
  have Hprev (i : ℕ) (hi : i ≤ stop B r) : close (z.layer i) (tuple (p i) (P.eval n)) (D i) := by
    induction i with
    | zero =>
      rw [z.boot]
      simpa only [D,Nat.cast_zero,zero_mul,add_zero] using begin_close hn0 B hB r hr (P.eval n)
    | succ i ih =>
      have hi' : i<stop B r := by omega
      have hh' := round_bound copy hn hN hn0 B hB _ _ (width_positive B r hr i) (width_positive B r hr (i+1))
        (hsm i hi'.le) (show P.eval n≤P.eval n+1 by omega) _ _ (z.physical i hi') _ (ih hi'.le)
      have eq : D (i+1)=D i+E := by dsimp [D];push_cast;ring
      rw [eq];exact hh'
  have tail := round_bound copy hn hN hn0 B hB _ r (width_positive B r hr _) hr
    (hsm _ le_rfl) (show 1≤P.eval n+1 by omega) _ _ z.terminal _ (Hprev _ le_rfl)
  let b := (PhysicalGrid.gridTape (PhysicalGrid.setup B r n)).length
  have hG : gridAdequate B (r:ℝ) (2^b) := PhysicalGrid.gridTape_adequate B r n hr
  refine ⟨b,hG,z.reads,?_⟩
  intro T
  have hfirst := tail (eventTest T)
  have hyes : evaluate (tuple (gaussian B hB r (by exact_mod_cast hr)) 1) (eventTest T)=
      ∑ a∈T,coefficientMass B r a := by
    change evaluate (tuple (gaussian B hB r (by exact_mod_cast hr)) 1) (fun x : Rows n 1 => indicator (fun y => y∈T) (x 0))=_
    rw [single_eval,finite_event];simp only [finiteMass,gaussian_real]
  rw [hyes] at hfirst
  have hlast := GridReadout.public_event_bound B hB r (by exact_mod_cast hr) hn0 hG T
  rw [z.read_event]
  apply (abs_sub_le _ (∑ a∈T,coefficientMass B r a) _).trans
  rw [abs_sub_comm (∑ a∈T,coefficientMass B r a)]
  apply (add_le_add hfirst hlast).trans
  change D (stop B r)+E+geom n≤_
  apply le_trans _ (accumulate P n k (stop B r) hh e he)
  dsimp only [D,E]
  ring_nf
  exact le_rfl

theorem assemble (S : Set ℕ) (C : MFamily) (P : Polynomial ℕ) (N : ℕ)
    (hcopy : ∀ calls : Polynomial ℕ, ∃ e : ℕ→ℝ, Negligible e ∧ CopyBudget C P calls N S e)
    (H : MFamily) (hH : IsMQPT H)
    (machine : ∀ n∈S, N≤n → 2≤n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det≠0 → ∀ r : ℚ, 0<r →
      dgsThreshold B≤(r:ℝ) → ∀ k : ℕ, Nonempty (Execution H C P B r k)) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ e : ℕ→ℝ, Negligible e ∧ ∃ N' : ℕ, ∀ n∈S,N'≤n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ,B.det≠0 → ∀ r : ℚ,0<r → dgsThreshold B≤(r:ℝ) → ∀ k : ℕ,
        ∃ b : ℕ, gridAdequate B (r:ℝ) (2^b) ∧ outputProb H (dgsInput B r 1 k)
           (fun out => ∃ z : Fin n→ℤ, encVec encI z <+: out)=1 ∧ ∀ T : Finset (Vec n),
          |outputProb H (dgsInput B r 1 k) (fun out => ∃ z∈T,encVec encI z <+: out)-
            fourierEvent B r (2^b) T|≤e n+1/(4*((k:ℝ)+1)) := by
  obtain ⟨e,he,h⟩ := hcopy ((P+1)+(P+1))
  refine ⟨H,hH,totalError P e,negligible_total P he,max N 2,?_⟩
  intro n hn hN B hB r hr hp k
  obtain ⟨z⟩ := machine n hn ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN) B hB r hr hp k
  exact from_execution h hn ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN) (he.1 n) H B hB r hr hp k z

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end P2MDyadicModule161

/- Helper module BatchSupport. -/
section P2MDyadicModule162

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Batch

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute GaussianIteration

open scoped Classical BigOperators ENNReal

noncomputable section

variable {s h k : ℕ} {Y : Type*}

theorem test_ext {X : Type*} {p q : PMF X} (h : ∀ f : Test X, evaluate p f=evaluate q f) : p=q := by
  ext x
  have he := h (indicator (fun y => y∈({x}:Finset X)))
  rw [finite_event,finite_event] at he
  apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top _) (q.apply_ne_top _)).mp
  simpa [finiteMass] using he

theorem actual_pool (t : Trace s h) (a : Fin k→Source h) (U : Layered k) (out : Bits k→Y) (m : ℕ) :
    (law (trace t a U m)).map (rows out m)=(law t).bind (fun x => tuple (cell a U out x) m) := by
  apply test_ext;intro f
  rw [eval_map,eval_bind]
  exact batch_measured t a U out m (fun _ => f)

theorem joint (t : Trace s h) (a : Fin k→Source h) (U : Layered k) (out : Bits k→Y) (m : ℕ) :
    (law (trace t a U m)).map (fun z => (original m z,rows out m z)) =
      (law t).bind (fun x => (tuple (cell a U out x) m).map (Prod.mk x)) := by
  apply test_ext;intro f
  rw [eval_map,eval_bind]
  have he := batch_measured t a U out m (fun x y => f (x,y))
  apply he.trans
  apply congrArg (evaluate (law t))
  funext x
  exact Subtype.ext (eval_map _ _ _).symm

theorem support (t : Trace s h) (a : Fin k→Source h) (U : Layered k) (out : Bits k→Y) (m : ℕ)
    (z : Bits (size h k m)) (hz : law (trace t a U m) z≠0) :
    law t (original m z)≠0 ∧ ∀ i,cell a U out (original m z) (rows out m z i)≠0 := by
  let y := (original m z,rows out m z)
  have hy : y∈((law (trace t a U m)).map (fun z => (original m z,rows out m z))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨z,(PMF.mem_support_iff _ _).mpr hz,rfl⟩
  rw [joint] at hy
  obtain ⟨x,hx,hxs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
  obtain ⟨v,hv,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hxs
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  refine ⟨(PMF.mem_support_iff _ _).mp hx,?_⟩
  have hn := (PMF.mem_support_iff _ _).mp hv
  rw [tuple_weight] at hn
  exact fun i => (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ _)

theorem law_ne {w l : ℕ} (t : Trace w l) (x : Bits l) :
    law t x≠0 ↔ t.state x≠0 := by
  simp [law,born,PMF.ofFintype_apply]

theorem canonical (t : Trace s h) (a : Fin k→Source h) (U : Layered k) (out : Bits k→Y) (m : ℕ)
    (Good : Bits h→Prop) (Row : Bits h→Y→Prop) (hold : ∀ x,t.state x≠0 → Good x)
    (hrow : ∀ x,t.state x≠0 → ∀ y,cell a U out x y≠0 → Row x y) (z : Bits (size h k m))
    (hz : (trace t a U m).state z≠0) :
    Good (original m z) ∧ ∀ i,Row (original m z) (rows out m z i) := by
  obtain ⟨ho,hr⟩ := support t a U out m z ((law_ne _ _).mpr hz)
  exact ⟨hold _ ((law_ne _ _).mp ho),fun i => hrow _ ((law_ne _ _).mp ho) _ (hr i)⟩

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Batch

end P2MDyadicModule162

/- Helper module NativeCall. -/
section P2MDyadicModule163

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.NativeCall

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport

open Integration9_9.TM2PlatformSerialization Integration9_9.LoadedBatch.PostComposition

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit GaussianIteration

open scoped Classical BigOperators

noncomputable section

variable {h j : ℕ}

def sources (F : MFamily) (p : Fin j→Source h) : Fin (j+(F.anc j+1))→Source h :=
  Fin.append p (fun _ => Source.literal false)

def chosen (F : MFamily) (j : ℕ) (z : Bits (j+(F.anc j+1))) := List.ofFn (fun i => z (F.outW j i))

def typed (F : MFamily) (p : Fin j→Source h) := pack (sources F p) (F.circ j)

def clock (p : List Pin) : Str := p.map (fun _ => true)

@[fun_prop] theorem clock_poly : Poly clock := by unfold clock;fun_prop

def build (desc : Str→Str) (p : List Pin) : Block :=
  let t := clock p
  let d := desc t
  (p++(unarySlots d++[()]).map (fun _ => ((0,0):Pin)),
    (readFrame (t,d)).2.2.flatten.map readGateCode)

@[fun_prop] theorem build_poly (desc : Str→Str) (hd : Poly desc) : Poly (build desc) := by
  unfold build
  have hr : Poly (fun p : List Pin => (readFrame (clock p,desc (clock p))).2.2) := by fun_prop
  have hf : Poly (List.flatten : List (List Str) → List Str) := ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  have he := Poly.list_map (f:=fun (_ : List Pin) (w : Str) => readGateCode w) (Poly.comp (f:=readGateCode) readGateCode_poly Poly.snd) (Poly.comp hf hr)
  fun_prop

theorem built (F : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=F.encAt n)
    (p : Fin j→Source h) :
    build desc (List.ofFn (fun i => pin (p i)))=typed F p := by
  have hc : clock (List.ofFn fun i => pin (p i))=unary j := by simp only [clock,List.map_const',List.length_ofFn,unary]
  have ha : unarySlots (F.encAt j)=List.replicate (F.anc j) () := by simp only [multi_encoding,List.append_assoc,unarySlots_append]
  have hs : (fun i => pin (sources F p i))=Fin.append (fun i => pin (p i)) (fun _ : Fin (F.anc j+1) => ((0,0):Pin)) := by
    funext i;refine Fin.addCases ?_ ?_ i <;> intro i <;> simp only [sources,Fin.append_left,Fin.append_right,pin]
  simp only [build,hc,hd,readFrame_correct,ha,typed,pack,hs,List.ofFn_fin_append,List.ofFn_const,List.map_append,List.map_replicate,
      List.map_cons,List.map_nil,List.map_flatten,List.map_map,Function.comp_def,readGateCode_exact,List.replicate_succ']

def outputList (desc : Str→Str) (p : List Pin) : List ℕ :=
  (readFrame (clock p,desc (clock p))).2.1.map (fun s => (unarySlots s).length)

@[fun_prop] theorem outputList_poly (desc : Str→Str) (hd : Poly desc) : Poly (outputList desc) := by unfold outputList;fun_prop

theorem outs (F : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=F.encAt n) (p : List Pin) :
    outputList desc p=List.ofFn (fun i => (F.outW p.length i).val) := by
  have hu (n : ℕ) : unarySlots (encNat n)=List.replicate n () := by simpa only [List.append_nil] using unarySlots_append n []
  have hc : clock p=unary p.length := by simp only [clock,List.map_const',unary]
  simp only [outputList,hc,hd,readFrame_correct,List.map_map,List.map_ofFn,Function.comp_def,hu,List.length_replicate]

def pureInput (F : MFamily) (p : Fin j→Source h) (x : Bits h) : Bits (j+(F.anc j+1)) :=
  fun i => (sources F p i).read x

theorem prepare_input (F : MFamily) (p : Fin j→Source h) (x : Bits h) :
    pureInput F p x=UniformInput.extended _ (input p x) := by
  funext i;refine Fin.addCases ?_ ?_ i
  · intro i;simp [pureInput,sources,UniformInput.extended,input,wordExtension,List.getElem?_ofFn]
  · intro i;change (sources F p (Fin.natAdd _ i)).read x=_
    rw [sources,Fin.append_right]
    exact (wordExtension_after _ _ (by simp [input])).symm

theorem measured (F : MFamily) (p : Fin j→Source h) (x : Bits h) (E : Str→Prop) :
  evaluate (conditional (sources F p) (F.circ j) x) (fun z => indicator E (chosen F j z))=outputProb F (input p x) E := by
  rw [conditional,born_eval,←UniformInput.probAt_eq]
  have hj : (input p x).length=j := List.length_ofFn
  rw [hj]
  unfold UniformInput.probAt
  rw [←prepare_input F p x]
  simp only [indicator,chosen,mul_ite,mul_one,mul_zero]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.NativeCall

end P2MDyadicModule163

/- Helper module MeasuredSlot. -/
section P2MDyadicModule164

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean GaussianIteration

open scoped Classical BigOperators

noncomputable section

theorem same_prefix {n : ℕ} (u v : Fin n→ℤ) (w : Str) (hu : encVec encI u <+: w) (hv : encVec encI v <+: w) : u=v := by
  obtain ⟨su,eu⟩ := hu
  obtain ⟨sv,ev⟩ := hv
  have he := congrArg (fun t : Str => (Integration9_9.TM2NativeAffineEncoding.readVector t).2) (eu.trans ev.symm)
  simp only [Integration9_9.TM2NativeAffineEncoding.readVector_append] at he
  exact List.ofFn_injective he



end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end P2MDyadicModule164

/- Helper module StageInput. -/
section P2MDyadicModule165

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1550000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARPlatformEncoding Integration9_9.TM2PlatformSerialization

open RegevSketch SamplerParameters RectangularSource

open scoped Classical BigOperators

noncomputable section

def split (outer : Str) : Str×Str :=
  let a := readS outer
  let b := readS a.1
  (encPair a.2 b.2,b.1)

@[fun_prop] theorem split_poly : Poly split := by unfold split;fun_prop

theorem split_append (a b tbl : Str) : split (encPair a b++tbl)=(encPair a b,tbl) := by simp [split,encPair,List.append_assoc,readS_append]

theorem split_input {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (k : ℕ) (tbl : Str) :
    split (dgsInput B r 1 k++tbl)=(dgsInput B r 1 k,tbl) := split_append _ _ _

def head (v : Str×ℕ) := encS v.1++encB v.2

@[fun_prop] theorem head_poly : Poly head := by unfold head;fun_prop

def parse (w : Str) : (Str×ℕ)×Str :=
  let framed := readS w
  let number := readB framed.1
  ((framed.2,number.2),number.1)

@[fun_prop] theorem parse_poly : Poly parse := by unfold parse;fun_prop

theorem parse_head (v : Str×ℕ) (tail : Str) : parse (head v++tail)=(v,tail) := by
  simp only [parse,head,List.append_assoc,readS_append,readB_append]

def fromParts (P : Polynomial ℕ) (v : (Str×ℕ)×Str) : Cell.Input :=
  let g := split v.1.1
  let d := SamplerParameters.read g.1
  ((stageProgram P (g.1,v.1.2),(copies P d,universalSlot P d)),v.2,g.2)

@[fun_prop] theorem fromParts_poly (P : Polynomial ℕ) : Poly (fromParts P) := by
  unfold fromParts;fun_prop

def stageData (P : Polynomial ℕ) (w : Str) := fromParts P (parse w)

@[fun_prop] theorem stageData_poly (P : Polynomial ℕ) : Poly (stageData P) :=
  Poly.comp (f:=fromParts P) (g:=parse) (fromParts_poly P) parse_poly

theorem stageData_exact (P : Polynomial ℕ) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (k i : ℕ) (tbl tape : Str) :
    let s := dgsInput B r 1 k
    let d := SamplerParameters.read s
    stageData P (head (s++tbl,i)++tape)=((stageProgram P (s,i),(copies P d,universalSlot P d)),tape,tbl) := by
  simp only [stageData,parse_head,fromParts,split_input]

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule165

/- Helper module CanonicalSlot. -/
section P2MDyadicModule166

set_option autoImplicit false

set_option maxHeartbeats 1350000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean GaussianIteration

noncomputable section

theorem decode_prefix {n : ℕ} (z : Vec n) (w : Str) (hz : encVec encI z <+: w) : decodeWord n w=z := by
  rcases hz with ⟨u,rfl⟩;funext i
  simp [decodeWord,Integration9_9.TM2NativeAffineEncoding.readVector_append]

theorem pins_law {j h : ℕ} (F : MFamily) (pins : Fin j→Source h) (x : Bits h) :
    Batch.cell (NativeCall.sources F pins) (F.circ j) (NativeCall.chosen F j) x = measuredWord F (input pins x) := by
  ext w
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  let T : Finset Str := {w}
  have he := NativeCall.measured F pins x (fun y => y∈T)
  rw [←born_native] at he
  have h : evaluate (Batch.cell (NativeCall.sources F pins) (F.circ j) (NativeCall.chosen F j) x) (indicator (fun y => y∈T))=
      evaluate (measuredWord F (input pins x)) (indicator (fun y => y∈T)) := by
    rw [Batch.cell,eval_map];exact he
  rw [finite_event,finite_event] at h
  simpa [finiteMass,T] using h

theorem pins_decodes {j h n : ℕ} (F : MFamily) (pins : Fin j→Source h) (x : Bits h) :
    Batch.cell (NativeCall.sources F pins) (F.circ j) (fun y => decodeWord n (NativeCall.chosen F j y)) x =
      (measuredWord F (input pins x)).map (decodeWord n) := by
  rw [←pins_law F pins x,Batch.cell,Batch.cell,PMF.map_comp]
  rfl

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end P2MDyadicModule166

/- Helper module PhysicalRound. -/
section P2MDyadicModule167

set_option autoImplicit false

set_option maxHeartbeats 1550000

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity GaussianIteration RegevSketch SharedPoolCoherence

noncomputable section

variable {n : ℕ} {C : MFamily} {P : Polynomial ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {R t : ℚ} {k m : ℕ}

def outputRow (n : ℕ) (G : MFamily) (j : ℕ) := fun y => SignedSlot.decodeWord n (NativeCall.chosen G j y)

def actual_round {s h j : ℕ} (G : MFamily) (pins : Fin j→Source h) (tr : Trace s h)
    (a : AnalysisData C P B R k) (outer : Str) (i S : ℕ) (decode : Bits h→Rows n (P.eval n)) (tape : Bits h→Str)
    (input_ok : ∀ x, tr.state x≠0 → input pins x=head (outer,i)++tape x)
    (size : ∀ x, tr.state x≠0 → (tape x).length=(P.eval n)*S)
    (valid : ∀ x,tr.state x≠0 → ∀ u, encVec encI (decode x u) <+: ((tape x).drop (u.val*S)).take S)
    (event : ∀ raw (z : Rows n (P.eval n)), raw.length=(P.eval n)*S → (∀ u,encVec encI (z u) <+: (raw.drop (u.val*S)).take S) →
      z∈keeps (P.eval n) (imageGrid n (2^a.grid)) → ∀ T : Finset (Vec n),
      |finiteMass ((measuredWord G (head (outer,i)++raw)).map (SignedSlot.decodeWord n)) T-
        ∑ v∈T,coefficientMass B t v| ≤ a.cost z) :
    Round C P B R t k m ((law tr).map decode)
      ((law (Batch.trace tr (NativeCall.sources G pins) (G.circ j) m)).map (Batch.rows (outputRow n G j) m)) where
  oldBits := h
  tape := law tr
  decode := decode
  row := Batch.cell (NativeCall.sources G pins) (G.circ j) (outputRow n G j)
  before := rfl
  after_ := Batch.actual_pool tr _ _ _ m
  grid := a.grid
  covers := a.covers
  I := a.I
  inst := a.inst
  inhabited := a.inhabited
  query := a.query
  amp := a.amp
  norm := a.norm
  prep := a.prep
  prep_nonneg := a.prep_nonneg
  L := a.L
  length_ge := a.length_ge
  source := a.source
  event := by
    intro x hx hkeep T
    have hst := (Batch.law_ne tr x).mp hx
    change |finiteMass (Batch.cell _ _ (fun y => SignedSlot.decodeWord n (NativeCall.chosen G j y)) x) T-_|≤_
    rw [SignedSlot.pins_decodes,input_ok x hst]
    exact event (tape x) (decode x) (size x hst) (valid x hst) hkeep T

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule167

/- Helper module PoolPrefix. -/
section P2MDyadicModule168

set_option autoImplicit false

set_option maxHeartbeats 1250000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

open GaussianIteration QAlgorithms QAlgorithms.Complexity FiniteGateTransport

noncomputable section

theorem supported_event {X : Type*} (p : PMF X) (E : X→Prop) (h : evaluate p (indicator E)=1) :
    ∀ x,p x≠0 → E x := by
  let g (x : X) := (p x).toReal-(p x).toReal*(indicator E x:ℝ)
  have hg : Summable g := (mass_summable p).summable.sub (evaluate_summable p (indicator E))
  have he : ∑' x,g x=0 := by
    rw [show g=(fun x => (p x).toReal-(p x).toReal*(indicator E x:ℝ)) from rfl,
      (mass_summable p).summable.tsum_sub (evaluate_summable p (indicator E)),(mass_summable p).tsum_eq]
    change 1-evaluate p (indicator E)=0
    rw [h,sub_self]
  have hn (x : X) : 0≤g x := sub_nonneg.mpr (mul_le_of_le_one_right ENNReal.toReal_nonneg (indicator E x).2.2)
  intro x hx
  by_contra ha
  have hp : g x≤0 := (hg.le_tsum x (fun y _ => hn y)).trans_eq he
  simp only [g,indicator,ha,if_false,mul_zero,sub_zero] at hp
  exact (ENNReal.toReal_pos hx (p.apply_ne_top _)).not_ge hp

theorem conditional_prefix {j h n S : ℕ} (G : MFamily) (pins : Fin j→Source h) (x : Bits h)
    (ok : outputProb G (input pins x) (canon n S)=1) {w : Str}
    (hw : Batch.cell (NativeCall.sources G pins) (G.circ j) (NativeCall.chosen G j) x w≠0) :
    encVec encI (decodeWord n w) <+: w.take S := by
  have wh : measuredWord G (input pins x) w≠0 := by rwa [pins_law G pins x] at hw
  obtain ⟨z,hz⟩ := supported_event (measuredWord G (input pins x)) (canon n S) ((born_native ..).trans ok) w wh
  rw [decode_prefix z w (hz.trans (List.take_prefix _ _))]
  exact hz

theorem mapped_rows {j h : ℕ} {X Y : Type*} (g : X→Y) (out : Bits j→X) (m : ℕ)
    (x : Bits (Batch.size h j m)) : Batch.rows (fun y => g (out y)) m x = fun i => g (Batch.rows out m x i) := by
  induction m with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
    funext i;refine Fin.cases ?_ (fun l => ?_) i
    · rfl
    · exact congrFun (ih (leftRegister x)) l

theorem batch_prefix {s h j n S : ℕ} (G : MFamily) (pins : Fin j→Source h) (tr : Trace s h) (m : ℕ)
    (ok : ∀ x,tr.state x≠0 → outputProb G (input pins x) (canon n S)=1)
    (z : Bits (Batch.size h (j+(G.anc j+1)) m)) (hz : (Batch.trace tr (NativeCall.sources G pins) (G.circ j) m).state z≠0) :
    ∀ i, encVec encI (Batch.rows (Outer.outputRow n G j) m z i) <+:
      (Batch.rows (NativeCall.chosen G j) m z i).take S := by
  have h := Batch.canonical tr (NativeCall.sources G pins) (G.circ j) (NativeCall.chosen G j) m (fun _ => True)
    (fun _ w => encVec encI (decodeWord n w) <+: w.take S) (fun _ _ => trivial)
    (fun x hx _ hw => conditional_prefix G pins x (ok x hx) hw) z hz
  intro i
  have hr := congrFun (mapped_rows (decodeWord n) (NativeCall.chosen G j) m z) i
  change encVec encI (Batch.rows (fun y => decodeWord n (NativeCall.chosen G j y)) m z i) <+: _
  rw [hr]
  exact h.2 i

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end P2MDyadicModule168

/- Helper module FinalRead. -/
section P2MDyadicModule169

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open GaussianIteration QAlgorithms.Complexity

noncomputable section

theorem eval_on_support {Ω : Type*} (p : PMF Ω) (f g : Test Ω) (h : ∀ x,p x≠0 → f x=g x) :
    evaluate p f=evaluate p g := by
  unfold evaluate
  apply tsum_congr;intro x
  by_cases z : p x=0
  · simp [z]
  · rw [h x z]

theorem final_read {Ω : Type*} {n : ℕ} (μ : PMF Ω) (words : Ω→Str) (row : Ω→Rows n 1)
    (H : MFamily) (w : Str) (hprob : ∀ E : Str→Prop, outputProb H w E=evaluate μ (fun x => indicator E (words x)))
    (good : ∀ x, μ x≠0 → encVec encI (row x 0) <+: words x) :
    outputProb H w (fun out => ∃ z : Vec n,encVec encI z <+: out)=1 ∧
    ∀ T : Finset (Vec n), outputProb H w (fun out => ∃ z∈T,encVec encI z <+: out)=
      evaluate (μ.map row) (eventTest T) := by
  constructor
  · rw [hprob]
    let one : Test Ω := fun _ => ⟨1,zero_le_one,le_rfl⟩
    have e := eval_on_support μ (fun x => indicator (fun out => ∃ z : Vec n, encVec encI z <+: out) (words x)) one (by
      intro x hx;apply Subtype.ext
      simp [indicator,one,show ∃ z : Vec n,encVec encI z<+:words x from ⟨_,good x hx⟩])
    rw [e]
    simpa [evaluate,one] using (mass_summable μ).tsum_eq
  · intro T
    rw [hprob,eval_map]
    apply eval_on_support;intro x hx
    have iff : (∃ z∈T,encVec encI z<+:words x) ↔ row x 0∈T := by
      constructor
      · rintro ⟨z,hz,hp⟩;rwa [←SignedSlot.same_prefix z (row x 0) (words x) hp (good x hx)]
      · intro hz;exact ⟨_,hz,good x hx⟩
    apply Subtype.ext
    simp [push,eventTest,indicator,iff]

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule169

/- Helper module OuterLayout. -/
section P2MDyadicModule170

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1900000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.LoadedBatch.PostComposition

open SamplerParameters

open scoped Classical BigOperators

noncomputable section

variable (P : Polynomial ℕ)

def unframed (s : Str) := (split s).1

@[fun_prop] theorem unframed_poly : Poly unframed := by unfold unframed;fun_prop

def data (s : Str) := SamplerParameters.read (unframed s)

@[fun_prop] theorem data_poly : Poly data := Poly.comp (f:=SamplerParameters.read) (g:=unframed) read_poly unframed_poly

def batch0 (s : Str) := initial P (data s)

@[fun_prop] theorem batch0_poly : Poly (batch0 P) := by unfold batch0;fun_prop

def initBlock (s : Str) : Block :=
  ((FirstPool.arenaSlots (batch0 P s)).map (fun _ => ((0,0):Pin)),FirstPool.loaderCodes (batch0 P s))

@[fun_prop] theorem initBlock_poly : Poly (initBlock P) := by unfold initBlock;fun_prop

abbrev Request := Str×ℕ

def inputs (r : Request) := (head r).map (fun _ => ())++poolSpace P (unframed r.1)

@[fun_prop] theorem inputs_poly : Poly (inputs P) := by unfold inputs;fun_prop

def imaginary (r : Request) := (inputs P r).map (fun _ => ((0,0):Pin))

@[fun_prop] theorem imaginary_poly : Poly (imaginary P) := by unfold imaginary;fun_prop

variable (desc : Str→Str) (hd : Poly desc)

def unitTicks (r : Request) := (NativeCall.build desc (imaginary P r)).1.map (fun _ => ())

include hd in
@[fun_prop] theorem unitTicks_poly : Poly (unitTicks P desc) := by unfold unitTicks;fun_prop

def ports (r : Request) := NativeCall.outputList desc (imaginary P r)

include hd in
@[fun_prop] theorem ports_poly : Poly (ports P desc) := by unfold ports;fun_prop

attribute [local irreducible] data widths stages RunnableWidths.count RunnableWidths.fuel

def internal (s : Str) : List ℕ := (stages (data s)).take (RunnableWidths.count (widths (data s)))

@[fun_prop] theorem internal_poly : Poly internal := by
  have hs : Poly (fun s : Str => widths (data s)) := Poly.comp (f:=widths) (g:=data) widths_poly data_poly
  have hc := Poly.comp (f:=RunnableWidths.count) (g:=fun s : Str=>widths (data s)) RunnableWidths.count_poly hs
  have hr := Poly.comp (f:=stages) (g:=data) stages_poly data_poly
  have ht : Poly (fun u : List ℕ×ℕ => u.1.take u.2) := ⟨PolyProgram.listTake Automatic.enc 0⟩
  exact Poly.comp (f:=fun u : List ℕ×ℕ => u.1.take u.2) (g:=fun s : Str => (stages (data s),RunnableWidths.count (widths (data s))))
    ht (Poly.pair hr hc)

attribute [local irreducible] internal batch0 unitTicks ports SamplerParameters.copies FirstPool.arenaSlots

def repeats (r : Request) : List Unit := if r.2<(internal r.1).length then copies P (data r.1) else [()]

@[fun_prop] theorem repeats_poly : Poly (repeats P) := by unfold repeats;fun_prop

attribute [local irreducible] repeats

def groupTicks (r : Request) : List Unit := (repeats P r).flatMap (fun _ => unitTicks P desc r)

include hd in
@[fun_prop] theorem groupTicks_poly : Poly (groupTicks P desc) := by unfold groupTicks;fun_prop

attribute [local irreducible] groupTicks

def usedBefore (r : Request) : List Unit :=
  (FirstPool.arenaSlots (batch0 P r.1))++((internal r.1).take r.2).flatMap (fun i => groupTicks P desc (r.1,i))

include hd in
@[fun_prop] theorem usedBefore_poly : Poly (usedBefore P desc) := by
  have ht := Poly.comp (f:=fun u : List ℕ×ℕ => u.1.take u.2) (g:=fun r : Request => (internal r.1,r.2))
    (show Poly (fun u : List ℕ×ℕ => u.1.take u.2) from ⟨PolyProgram.listTake Automatic.enc 0⟩) (by fun_prop)
  unfold usedBefore
  have hf := Poly.list_flatMap (f:=fun r : Request => fun i => groupTicks P desc (r.1,i)) (Poly.comp (f:=groupTicks P desc) (groupTicks_poly P desc hd) (by fun_prop)) ht
  fun_prop

attribute [local irreducible] usedBefore FirstPool.slot FirstPool.outputOffset

def firstPin (x : (Str×ℕ)×ℕ) : Pin :=
  let v := batch0 P x.1.1
  let d := (FirstPool.slot v.1).length
  if x.2<d then (2, FirstPool.outputOffset v+x.1.2*d+x.2) else (0,0)

@[fun_prop] theorem firstPin_poly : Poly (firstPin P) := by unfold firstPin;fun_prop

attribute [local irreducible] firstPin

def oldPin (v : (Request×ℕ)×ℕ) : Pin :=
  let r := v.1.1
  if r.2=0 then firstPin P ((r.1,v.1.2),v.2)
  else
    let prev := (r.1,r.2-1)
    let read := ports P desc prev
    let idx := (repeats P prev).length-1-v.1.2
    if v.2<read.length then (2,(usedBefore P desc prev).length+idx*(unitTicks P desc prev).length+read[v.2]?.getD 0)
    else (0,0)

include hd in
@[fun_prop] theorem oldPin_poly : Poly (oldPin P desc) := by unfold oldPin;fun_prop

attribute [local irreducible] oldPin

def rowRange (s : Str) := List.range (copies P (data s)).length

@[fun_prop] theorem rowRange_poly : Poly (rowRange P) := Poly.comp (f:=fun xs : List Unit=>List.range xs.length)
  (g:=fun s : Str=>copies P (data s)) Poly.list_indices (by fun_prop)

def columnRange (s : Str) := List.range (universalSlot P (data s)).length

@[fun_prop] theorem columnRange_poly : Poly (columnRange P) := Poly.comp (f:=fun xs : List Unit=>List.range xs.length)
  (g:=fun s : Str=>universalSlot P (data s)) Poly.list_indices (by fun_prop)

attribute [local irreducible] rowRange columnRange

def rowPins (v : Request×ℕ) := (columnRange P v.1.1).map (fun col => oldPin P desc (v,col))

include hd in
@[fun_prop] theorem rowPins_poly : Poly (rowPins P desc) := by unfold rowPins;exact Poly.list_map (oldPin_poly P desc hd) (by fun_prop)

attribute [local irreducible] rowPins

def oldPins (r : Request) := (rowRange P r.1).flatMap (fun row => rowPins P desc (r,row))

include hd in
@[fun_prop] theorem oldPins_poly : Poly (oldPins P desc) := by unfold oldPins;exact Poly.list_flatMap (rowPins_poly P desc hd) (by fun_prop)

attribute [local irreducible] oldPins

def clipped (h : ℕ) (p : Pin) : Pin := if p.1=2 ∧ p.2<h then p else if p.1=1 then (1,0) else (0,0)

@[fun_prop] theorem clipped_poly : Poly (fun u : ℕ×Pin => clipped u.1 u.2) := by unfold clipped;fun_prop

def allPins (r : Request) : List Pin := (head r).map UniformInput.lit ++ (oldPins P desc r).map (clipped (usedBefore P desc r).length)

include hd in
@[fun_prop] theorem allPins_poly : Poly (allPins P desc) := by unfold allPins UniformInput.lit;fun_prop

attribute [local irreducible] clipped allPins initBlock NativeCall.build

def blocks (s : Str) : List Block := [initBlock P s]++((internal s)++[(internal s).length]).flatMap
  (fun i => (repeats P (s,i)).map (fun _ => NativeCall.build desc (allPins P desc (s,i))))

include hd in
@[fun_prop] theorem blocks_poly : Poly (blocks P desc) := by
  unfold blocks
  have hx := Poly.list_flatMap (f:=fun s : Str => fun i => (repeats P (s,i)).map (fun _ => NativeCall.build desc (allPins P desc (s,i))))
    (by fun_prop) (show Poly (fun s : Str => internal s ++ [(internal s).length]) by fun_prop)
  fun_prop

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule170

/- Helper module OutputStage. -/
section P2MDyadicModule171

set_option autoImplicit false

set_option maxHeartbeats 1100000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open SamplerParameters

noncomputable section

variable (P : Polynomial ℕ) (desc : Str→Str) (hd : Poly desc)

def occupied (s : Str) := (blocks P desc s).flatMap (fun b => b.1.map (fun _ => ()))

include hd in
@[fun_prop] theorem occupied_poly : Poly (occupied P desc) := by
  unfold occupied
  exact Poly.list_flatMap (f:=fun (_ : Str) (b : Block) => b.1.map (fun _ => ())) (by fun_prop) (blocks_poly P desc hd)

def terminalPin (u : Str×ℕ) : Pin :=
  let r := (u.1,(internal u.1).length)
  let wires := ports P desc r
  if u.2<wires.length then clipped (occupied P desc u.1).length (2,(usedBefore P desc r).length+wires[u.2]?.getD 0) else (0,0)

include hd in
@[fun_prop] theorem terminalPin_poly : Poly (terminalPin P desc) := by unfold terminalPin;fun_prop

def readBlock (s : Str) : Block := ((columnRange P s).map (fun j => terminalPin P desc (s,j)),[])

include hd in
@[fun_prop] theorem readBlock_poly : Poly (readBlock P desc) := by
  unfold readBlock
  exact Poly.pair (Poly.list_map (terminalPin_poly P desc hd) (columnRange_poly P)) (Automatic.Poly.const ([]:List GateCode))

def plan (s : Str) : PlacedCPU.Recipe :=
  ((occupied P desc s,universalSlot P (data s)),allCode ([],blocks P desc s++[readBlock P desc s]))

include hd in
@[fun_prop] theorem plan_poly : Poly (plan P desc) := by unfold plan;fun_prop

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule171

/- Helper module WaveTrace. -/
section P2MDyadicModule172

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1050000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Batch

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport GaussianIteration

open scoped Classical BigOperators

noncomputable section

variable {s h k : ℕ} {Y : Type*}

def change {u v : ℕ} (eq : u=v) (t : Trace s u) : Trace s v := eq ▸ t

theorem change_blocks {u v : ℕ} (eq : u=v) (t : Trace s u) : (change eq t).blocks=t.blocks := by subst v;rfl

theorem change_eval {u v : ℕ} (eq : u=v) (t : Trace s u) (x : Bits v) :
    (change eq t).state x=t.state (fun i => x (Fin.cast eq i)) := by subst v;rfl

def initial (c : Layered k) : Trace 0 k :=
  change (Nat.zero_add k) ((Trace.start (s:=0)).extend (fun _ : Fin k => Source.literal false) c)

theorem initial_blocks (c : Layered k) :
    (initial c).blocks=[((List.replicate k ((0,0):Pin)),c.flatten.map encodeInstr)] := by
  simp only [initial,change_blocks,Trace.blocks,List.nil_append,pack,pin,List.ofFn_const]

theorem initial_state (c : Layered k) (x : Bits k) : (initial c).state x=runLayered c (basis (zeroBits k)) x := by
  rw [initial,change_eval]
  have he : (fun i : Fin (0+k) => x (Fin.cast (Nat.zero_add k) i))=Fin.append (zeroBits 0) x := by
    funext i;refine Fin.addCases (fun j => j.elim0) ?_ i
    intro j;rw [Fin.append_right];apply congrArg x;apply Fin.ext;simp
  rw [he,state_step]
  change basis (zeroBits 0) (zeroBits 0) * _ = _
  simp only [basis,if_true,one_mul,Source.read];rfl

theorem pack_pins (a : Fin k→Source h) (U : Layered k) (m : ℕ) : pack (pins a m) U=pack a U := by
  unfold pack
  have same : (fun i => pin (pins a m i))=(fun i => pin (a i)) := by
    funext i;unfold pins;cases a i with
    | wire j => rfl
    | literal b => cases b <;> rfl
  rw [same]

theorem trace_blocks (t : Trace s h) (a : Fin k→Source h) (U : Layered k) (m : ℕ) :
    (trace t a U m).blocks=t.blocks++List.replicate m (pack a U) := by
  induction m with
  | zero => simp [trace]
  | succ m ih => rw [trace,Trace.blocks,ih,pack_pins,List.replicate_succ',List.append_assoc]

def rowWire (h : ℕ) {m : ℕ} (i : Fin m) (j : Fin k) : Fin (size h k m) where
  val := h+(m-1-i.val)*k+j.val
  isLt := by
    rw [size_eq]
    have hi : m-1-i.val+1 ≤ m := by omega
    have hb := Nat.mul_le_mul_right k hi
    rw [Nat.succ_mul] at hb
    omega

theorem rows_wire (out : Bits k→Y) (m : ℕ) (z : Bits (size h k m)) (i : Fin m) :
    rows out m z i=out (fun j => z (rowWire h i j)) := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    refine Fin.cases ?_ ?_ i
    · simp only [rows,Fin.cons_zero]
      apply congrArg out;funext j;apply congrArg z;apply Fin.ext
      simp [rowWire,size_eq,Nat.add_assoc]
    · intro i
      simp only [rows,Fin.cons_succ,ih]
      apply congrArg out;funext j;apply congrArg z;apply Fin.ext
      change h+(m-1-i.val)*k+j.val=h+(m+1-1-(i.val+1))*k+j.val
      congr 3 <;> omega

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Batch

end P2MDyadicModule172

/- Helper module StartHistory. -/
section P2MDyadicModule173

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters.StartHistory

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute GaussianIteration AdaptiveStages

open FirstPool TM2Boolean.PolyProgramCircuit Integration9_9.TM2NativeAffineEmitter

open RegevLWE.GaussConv RegevSketch IntegerBasis SharedPoolCoherence

noncomputable section

attribute [local irreducible] FirstPool.program FirstPool.loader FirstPool.row FirstPool.run FirstPool.tape FirstPool.slot

abbrev size (v : Batch) := N (batchHeader v).length (FirstPool.tape v).length

def law (v : Batch) : PMF (Bits (size v)) := GaussianIteration.born (runLayered (FirstPool.loader v) (basis 0)) (row_norm _ _)

theorem supported (v : Batch) (x : Bits (size v)) (hx : law v x≠0) :
    ∃ s,answer v s=x := by
  by_contra! h
  have hno : x∉Set.range (outcomes v) := by rintro ⟨z,hz⟩;exact h z hz
  have hh : runLayered (FirstPool.loader v) (basis 0) x=0 := by
    rw [loader_exact]
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have ne : x≠answer v i := fun hh=>h i hh.symm
    simp only [Pi.smul_apply,basis,if_neg ne,smul_zero]
  apply hx
  simp only [law,GaussianIteration.born,PMF.ofFintype_apply,hh,norm_zero,zero_pow (by decide : 2≠0),ENNReal.ofReal_zero]



theorem rightTape (m k : ℕ) (x : Bits (m+k)) :
    List.ofFn (fun i : Fin k => x (Fin.natAdd m i))=(List.ofFn x).drop m := by
  rw [List.ofFn_add (n:=m) (m:=k) (f:=x)]
  simp only [List.drop_append,List.length_ofFn,Nat.sub_self,List.drop_zero]
  rw [List.drop_of_length_le (by simp),List.nil_append]

theorem tail_bits (v : Batch) (x : Bits (size v)) :
    outputData v x=(List.ofFn x).drop (outputOffset v) := by
  rw [outputOffset_exact]
  let m:=NativeWordLayout.width program ((batchHeader v).length+(FirstPool.tape v).length)
  let k:=capacity program ((batchHeader v).length+(FirstPool.tape v).length)
  change List.ofFn (fun i : Fin k => x (Fin.natAdd m i))=(List.ofFn (n:=m+k) x).drop m
  exact rightTape m k x

def absolute (v : Batch) (S : List Unit) (x : Bits (size v)) (i : ℕ) :=
  NativePaddedWords.current (S,((List.ofFn x).drop (outputOffset v+i*(FirstPool.slot v.1).length)).take (FirstPool.slot v.1).length)

theorem absolute_eq (v : Batch) (S : List Unit) (x : Bits (size v)) (i : ℕ) :
    absolute v S x i=NativePaddedWords.current (S,FirstPool.slice (((FirstPool.slot v.1).length,outputData v x),i)) := by
  rw [tail_bits,FirstPool.slice,List.drop_drop]
  rfl

theorem map_law (n : ℕ) (v : Batch) : (law v).map (readPool n v)=tuple (rowPMF n v.1) v.2.length := by
  let p:=(law v).map (readPool n v)
  let q:=tuple (rowPMF n v.1) v.2.length
  have hh (f : Test (Fin v.2.length→Fin n→ℤ)) : evaluate p f=evaluate q f := by
    rw [show p=(law v).map (readPool n v) from rfl,eval_map,law,born_eval]
    exact physical_exact n v f
  ext x
  apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top x) (q.apply_ne_top x)).mp
  have h:=hh (indicator (fun z=>z∈({x}:Finset _)))
  rw [finite_event,finite_event] at h
  simpa [finiteMass] using h

theorem map_count (n m : ℕ) (v : Batch) (hm : v.2.length=m) :
    (law v).map (fun x i => readPool n v x (Fin.cast hm.symm i))=tuple (rowPMF n v.1) m := by
  subst m
  exact map_law n v

theorem row_encoding {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (hD : D.det≠0)
    (same : inputModule D=inputModule B) (r : ℚ) (a : List Unit) (w : Str) :
    rowWord (cfg B D r a,w)=encVec encI (coeff n (cfg B D r a) w) := by
  unfold rowWord FirstPool.coeff
  rw [FirstPool.row_exact B D hB hD same]
  simpa only [List.getElem?_ofFn,Fin.is_lt,↓reduceDIte,Option.getD_some] using
    (show ∀ f : Fin n→ℤ,serializeVector (List.ofFn f)=encVec encI f from fun f=>by
      simp only [serializeVector,Integration9_9.LARPlatformEncoding.serializeBinaryWords_map,encVec]) _

theorem actual_prefix {n : ℕ} (P : Polynomial ℕ) (d : Raw) (B D : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det≠0) (hD : D.det≠0) (same : inputModule D=inputModule B)
    (r : ℚ) (a : List Unit) (hc : (initial P d).1=cfg B D r a)
    (x : Bits (size (initial P d))) (hx : law (initial P d) x≠0) (i : Fin (initial P d).2.length) :
    encVec encI (readPool n (initial P d) x i) <+: absolute (initial P d) (universalSlot P d) x i.val := by
  let v:=initial P d
  obtain ⟨s,rfl⟩:=supported v x hx
  have h:=first_read P d s i
  rw [absolute_eq,read_answer]
  dsimp only at h
  have hr : rowWord (v.1,List.ofFn (splitTape v s i))=encVec encI (coeff n v.1 (List.ofFn (splitTape v s i))) := by
    generalize List.ofFn (splitTape v s i)=w
    change rowWord ((initial P d).1,w)=_
    rw [hc]
    exact row_encoding B D hB hD same r a w
  exact hr ▸ h

end

end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters.StartHistory

end P2MDyadicModule173

/- Helper module StartGround. -/
section P2MDyadicModule174

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters.StartHistory

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute GaussianIteration AdaptiveStages IntegerBasis RegevSketch

open FirstPool TM2Boolean.PolyProgramCircuit Integration9_9.TM2NativeAffineEmitter

noncomputable section

theorem module_same {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) :
    inputModule (NativeLLL.basis B)=inputModule B := by
  have he {t : ℕ} (A : Matrix (Fin t) (Fin t) ℤ) (hA : A.det≠0) : inputModule A=inputLattice A hA := by
    unfold inputModule inputLattice;congr 2;funext i;simp [realBasis_apply,latVec,Matrix.mulVec_single]
  exact (he _ (NativeLLL.basis_det_ne_zero B hB)).trans ((NativeLLL.basis_inputLattice_eq B hB).trans (he B hB).symm)

theorem base {n : ℕ} (P : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (k : ℕ) :
    let d:=read (dgsInput B r 1 k)
    let v:=initial P d
    ∃ hm : v.2.length=P.eval n,
    let decode (x : Bits (size v)) (i : Fin (P.eval n)) := readPool n v x (Fin.cast hm.symm i)
    (law v).map decode=zeroIdeal B r (P.eval n) ∧
      ∀ x,law v x≠0 → ∀ i : Fin (P.eval n),encVec encI (decode x i) <+: absolute v (universalSlot P d) x i.val := by
  intro d v
  have hpar := (exact_parameters P B hB r k).1
  change v=(_,_) at hpar
  have hm : v.2.length=P.eval n := (congrArg (fun t : Batch=>t.2.length) hpar).trans List.length_replicate
  have hc := congrArg (fun t : Batch => t.1) hpar
  refine ⟨hm,?_,?_⟩
  · rw [map_count n (P.eval n) v hm]
    unfold zeroIdeal
    rw [hc]
  · intro x hx i
    exact actual_prefix P d B (NativeLLL.basis B) hB (NativeLLL.basis_det_ne_zero B hB) (module_same B hB)
      r (List.replicate n ()) hc x hx (Fin.cast hm.symm i)

end

end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters.StartHistory

end P2MDyadicModule174

/- Helper module StartPins. -/
section P2MDyadicModule175

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters.StartHistory

open QAlgorithms QAlgorithms.Complexity FirstPool

noncomputable section

theorem padded (S : List Unit) (w : Str) (a d : ℕ) :
    NativePaddedWords.current (S,(w.drop a).take d)=List.ofFn (fun i : Fin S.length=>if i.val<d then (w[a+i.val]?).getD false else false) := by
  apply List.ext_getElem
  · rw [NativePaddedWords.current_length,List.length_ofFn]
  · intro i hl hr
    have hi : i<S.length := by simpa using hr
    simp only [NativePaddedWords.current,List.getElem_take,List.getElem_ofFn]
    by_cases hd : i<d
    · simp only [hd,↓reduceIte]
      by_cases ha : a+i<w.length
      · have hw : i<((w.drop a).take d).length := by simp only [List.length_take,List.length_drop];omega
        rw [List.getElem_append_left hw,List.getElem_take,List.getElem_drop,List.getElem?_eq_getElem ha]
        rfl
      · have hw : ((w.drop a).take d).length ≤ i := by simp only [List.length_take,List.length_drop];omega
        rw [List.getElem_append_right hw,List.getElem_map,List.getElem?_eq_none (by omega)]
        rfl
    · have hw : ((w.drop a).take d).length ≤ i := by simp only [List.length_take];omega
      rw [List.getElem_append_right hw,List.getElem_map,if_neg hd]

theorem absolute_pins (v : Batch) (S : List Unit) (x : Bits (size v)) (i : ℕ) :
    absolute v S x i=List.ofFn (fun j : Fin S.length=>if j.val<(slot v.1).length then
      ((List.ofFn x)[outputOffset v+i*(slot v.1).length+j.val]?).getD false else false) := padded _ _ _ _

end

end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters.StartHistory

end P2MDyadicModule175

/- Helper module WaveRead. -/
section P2MDyadicModule176

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute GaussianIteration SamplerParameters

noncomputable section

def pickup (h off : ℕ) (ps : List ℕ) (S : List Unit) (i : Fin S.length) : Source h :=
  let pos:=off+ps[i.val]?.getD 0
  if i.val<ps.length then if hh : pos<h then .wire ⟨pos,hh⟩ else .literal false else .literal false

def reader (P : Polynomial ℕ) (desc : Str→Str) (s : Str) :=
  let r:=(s,(internal s).length)
  pickup (occupied P desc s).length (usedBefore P desc r).length (ports P desc r) (universalSlot P (data s))

theorem pickup_pin (h off : ℕ) (ps : List ℕ) (S : List Unit) (i : Fin S.length) :
    pin (pickup h off ps S i)=(if i.val<ps.length then clipped h (2,off+ps[i.val]?.getD 0) else (0,0)) := by
  let pos:=off+ps[i.val]?.getD 0
  change pin (if i.val<ps.length then (if hh : pos<h then Source.wire ⟨pos,hh⟩ else Source.literal false) else Source.literal false) =
    (if i.val<ps.length then clipped h (2,pos) else (0,0))
  by_cases near : i.val<ps.length
  · rw [if_pos near,if_pos near]
    by_cases fits : pos<h
    · rw [dif_pos fits];simp [clipped,pin,fits]
    · rw [dif_neg fits];simp [clipped,pin,fits]
  · rw [if_neg near,if_neg near];rfl

theorem readPack (P : Polynomial ℕ) (desc : Str→Str) (s : Str) :
    pack (reader P desc s) []=readBlock P desc s := by
  refine Prod.ext ?_ (show (pack (reader P desc s) []).2=(readBlock P desc s).2 from rfl)
  change List.ofFn _=(List.range (universalSlot P (data s)).length).map _
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    exact pickup_pin _ _ _ _ _

theorem read_eval {h k : ℕ} (t : Trace 0 h) (a : Fin k→Source h) (f : Bits (h+k)→Str) (E : Str→Prop) :
    (∑ z,if E (f z) then ‖(t.extend a []).state z‖^2 else 0)=
      evaluate (law t) (fun x=>indicator E (f (Fin.append x (fun i=>(a i).read x)))) := by
  let d (x : Bits h) (y : Bits k):=f (Fin.append x y)
  have he:=step_eval t a ([] : Layered k) d (indicator E)
  have hread (x : Bits h) : evaluate (conditional a ([]:Layered k) x) (fun y=>indicator E (d x y))=
      (indicator E (d x (fun i=>(a i).read x)):ℝ) := by
    simp only [conditional,born_eval,runLayered,List.foldl_nil]
    let u:Bits k:=fun i=>(a i).read x
    rw [Finset.sum_eq_single u]
    · simp [basis,u]
    · intro y hy hne
      simp [basis,show y≠fun i=>(a i).read x from hne]
    · simp
  have hright : (fun x : Bits h=> (⟨evaluate (conditional a ([]:Layered k) x) (fun y=>indicator E (d x y)),evaluate_range _ _⟩ : Set.Icc (0:ℝ) 1))=
    (fun x=>indicator E (f (Fin.append x (fun i=>(a i).read x)))) := by
    funext x;apply Subtype.ext;exact hread x
  rw [hright] at he
  rw [←he,law,born_eval]
  apply Finset.sum_congr rfl
  intro z _
  have hh : Fin.append (leftRegister z) (rightRegister z)=z := (qubitsAppendEquiv h k).symm_apply_apply z
  simp only [d,hh,indicator]
  split <;> simp_all

attribute [local irreducible] occupied blocks readBlock reader allCode Trace.circuit

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule176

/- Helper module WaveWidth. -/
section P2MDyadicModule177

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport

open SamplerParameters Integration9_9.LoadedBatch.PostComposition

open scoped Classical BigOperators

noncomputable section

variable (P : Polynomial ℕ) (F : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=F.encAt n)

attribute [local irreducible] data internal unframed widths SamplerParameters.copies universalSlot FirstPool.slot

theorem row_len (v : Request×ℕ) : (rowPins P desc v).length=(universalSlot P (data v.1.1)).length := by simp [rowPins,columnRange]

theorem pin_len (r : Request) : (allPins P desc r).length=(inputs P r).length := by
  have he : (fun i => (rowPins P desc (r,i)).length)=(fun _ : ℕ => (universalSlot P (data r.1)).length) := funext (fun i => row_len P desc (r,i))
  simp only [allPins,oldPins,inputs,List.length_append,List.length_map,List.length_flatMap,Function.comp_def,he,List.map_const',List.sum_replicate,
    rowRange,List.length_range,SamplerParameters.pool_size,data,List.length_replicate,nsmul_eq_mul,Nat.cast_id]

theorem zeroPins_len (r : Request) : (imaginary P r).length=(inputs P r).length := List.length_map _

include hd in
theorem cell_width (r : Request) : (unitTicks P desc r).length = (inputs P r).length+(F.anc (inputs P r).length+1) := by
  have ha : Integration9_9.TM2PlatformSerialization.unarySlots (F.encAt (inputs P r).length)=List.replicate (F.anc (inputs P r).length) () := by
    simp only [multi_encoding,List.append_assoc,Integration9_9.TM2PlatformSerialization.unarySlots_append]
  have hh : NativeCall.clock (imaginary P r)=unary (inputs P r).length := by simp only [NativeCall.clock,List.map_const',zeroPins_len,unary]
  simp only [unitTicks,List.length_map,NativeCall.build,hh,hd,ha,List.length_append,List.length_replicate,List.length_singleton,zeroPins_len]

theorem internal_eq (s : Str) : internal s=List.range (RunnableWidths.count (widths (data s))) := by
  have hh : RunnableWidths.count (widths (data s))≤(RunnableWidths.fuel (widths (data s))).length := by
    dsimp only [RunnableWidths.count];simpa only [List.length_range] using List.length_filter_le (RunnableWidths.above (widths (data s))) (List.range (RunnableWidths.fuel (widths (data s))).length)
  simp only [internal,stages,List.take_range,Nat.min_eq_left hh]

theorem base_zero (s : Str) : (usedBefore P desc (s,0)).length=(FirstPool.arenaSlots (batch0 P s)).length := by simp [usedBefore]

theorem prior_succ (s : Str) (i : ℕ) (hi : i<(internal s).length) :
    (usedBefore P desc (s,i+1)).length=(usedBefore P desc (s,i)).length+
      (repeats P (s,i)).length*(unitTicks P desc (s,i)).length := by
  have h := hi;rw [internal_eq,List.length_range] at h
  simp only [usedBefore,internal_eq,List.take_range,Nat.min_eq_left h.le,Nat.min_eq_left h,
    Nat.min_eq_left (Nat.succ_le_of_lt h),List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.length_append,Nat.add_assoc]
  unfold groupTicks;simp [List.length_flatMap,List.sum_replicate]

theorem start_active (s : Str) (i : ℕ) (hi : i<(internal s).length) : repeats P (s,i)=copies P (data s) := if_pos hi

theorem end_active (s : Str) : repeats P (s,(internal s).length)=[()] := by simp [repeats]

def choose (n : ℕ) (p : Pin) : Source n :=
  if hp : p.1=2 ∧ p.2<n then .wire ⟨p.2,hp.2⟩ else .literal (decide (p.1=1))

theorem chosen_pin (n : ℕ) (p : Pin) : pin (choose n p)=clipped n p := by
  rcases p with ⟨tag,i⟩
  by_cases a : tag=2 ∧ i<n
  · have h:=a.1;subst tag;simp [choose,clipped,pin,a.2]
  · by_cases one : tag=1 <;> simp [choose,clipped,pin,a,one]

theorem clipped_idem (n : ℕ) (p : Pin) : clipped n (clipped n p)=clipped n p := by unfold clipped;split_ifs <;> simp_all

theorem literal_clipped (n : ℕ) (b : Bool) : clipped n (UniformInput.lit b)=UniformInput.lit b := by cases b <;> rfl

def prepares (s : Str) (i n : ℕ) : Fin (allPins P desc (s,i)).length → Source n :=
  fun j => choose n (allPins P desc (s,i))[j.val]

theorem raw_pins (s : Str) (i n : ℕ) (hn : n=(usedBefore P desc (s,i)).length) :
    List.ofFn (fun j => pin (prepares P desc s i n j))=allPins P desc (s,i) := by
  subst n
  let n := (usedBefore P desc (s,i)).length
  have he (p : Pin) (hp : p∈allPins P desc (s,i)) : clipped n p=p := by
    rcases List.mem_append.mp hp with h|h
    · obtain ⟨b,_,rfl⟩:=List.mem_map.mp h;exact literal_clipped _ _
    · obtain ⟨q,_,rfl⟩:=List.mem_map.mp h;exact clipped_idem _ _
  apply List.ext_getElem
  · simp
  · intro j hj _
    simp only [List.getElem_ofFn,prepares,chosen_pin]
    exact he _ (List.getElem_mem _)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule177

/- Helper module WaveBuild. -/
section P2MDyadicModule178

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport SamplerParameters

noncomputable section

variable (P : Polynomial ℕ) (F : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=F.encAt n)

structure Wave where
  width : ℕ
  tr : Trace 0 width

abbrev pinCount (s : Str) (i : ℕ) := (allPins P desc (s,i)).length

def beginWave (s : Str) : Wave := ⟨_,Batch.initial (FirstPool.loader (batch0 P s))⟩

def moreWave (s : Str) (i : ℕ) (w : Wave) : Wave :=
  let p := prepares P desc s i w.width
  ⟨_, Batch.trace w.tr (NativeCall.sources F p) (F.circ (pinCount P desc s i)) (repeats P (s,i)).length⟩

def waves (s : Str) : ℕ→Wave
| 0 => beginWave P s
| i+1 => moreWave P F desc s i (waves s i)

attribute [local irreducible] allPins inputs repeats usedBefore internal FirstPool.arenaSlots batch0 FirstPool.loader unitTicks ports

theorem begin_width (s : Str) : (beginWave P s).width=(FirstPool.arenaSlots (batch0 P s)).length :=
  (FirstPool.arenaSlots_length _).symm

theorem begin_blocks (s : Str) : (beginWave P s).tr.blocks=[initBlock P s] := by
  simp only [beginWave,Batch.initial_blocks,initBlock,List.map_const',FirstPool.arenaSlots_length,FirstPool.loaderCodes_exact]

include hd in
theorem more_width (s : Str) (i : ℕ) (w : Wave) : (moreWave P F desc s i w).width=
    w.width+(repeats P (s,i)).length*(unitTicks P desc (s,i)).length := by
  change Batch.size _ _ _=_
  rw [Batch.size_eq,cell_width P F desc hd]
  simp only [pinCount,pin_len]

include hd in
theorem more_blocks (s : Str) (i : ℕ) (w : Wave) (hw : w.width=(usedBefore P desc (s,i)).length) :
    (moreWave P F desc s i w).tr.blocks=w.tr.blocks++List.replicate (repeats P (s,i)).length (NativeCall.build desc (allPins P desc (s,i))) := by
  change (Batch.trace _ _ _ _).blocks=_
  rw [Batch.trace_blocks]
  have eq := NativeCall.built F desc hd (prepares P desc s i w.width)
  rw [raw_pins P desc s i w.width hw] at eq
  rw [eq];rfl

include hd in
theorem waves_width (s : Str) (i : ℕ) (hi : i ≤ (internal s).length) :
    (waves P F desc s i).width=(usedBefore P desc (s,i)).length := by
  induction i with
  | zero => rw [waves,begin_width,base_zero]
  | succ i ih =>
    have h : i < (internal s).length := by omega
    rw [waves,more_width P F desc hd,prior_succ P desc s i h,ih h.le]

def epochBlocks (s : Str) (i : ℕ) := (repeats P (s,i)).map (fun _ => NativeCall.build desc (allPins P desc (s,i)))

include hd in
theorem prefix_blocks (s : Str) (i : ℕ) (hi : i ≤ (internal s).length+1) : (waves P F desc s i).tr.blocks=
    [initBlock P s]++(List.range i).flatMap (epochBlocks P desc s) := by
  induction i with
  | zero => rw [waves,begin_blocks];rfl
  | succ i ih =>
    have h : i ≤ (internal s).length := by omega
    rw [waves,more_blocks P F desc hd s i _ (waves_width P F desc hd s i h),ih (by omega),List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,←List.append_assoc,epochBlocks,List.map_const']

include hd in
theorem all_blocks (s : Str) : (waves P F desc s ((internal s).length+1)).tr.blocks=blocks P desc s := by
  rw [prefix_blocks P F desc hd _ _ le_rfl,blocks,List.range_succ]
  have e : List.range (internal s).length=internal s := by rw [internal_eq,List.length_range]
  rw [e];rfl

theorem block_width {s h : ℕ} (t : Trace s h) :
    s+(t.blocks.flatMap (fun b => b.1.map (fun _ => ()))).length=h := by
  induction t with
  | start => simp [Trace.blocks]
  | extend t a u ih =>
    simp only [Trace.blocks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,List.length_map,pack,List.length_ofFn,←Nat.add_assoc,ih]

include hd in
theorem all_width (s : Str) : (waves P F desc s ((internal s).length+1)).width=(occupied P desc s).length := by
  have H := block_width (waves P F desc s ((internal s).length+1)).tr
  rw [all_blocks P F desc hd s,Nat.zero_add] at H
  exact H.symm

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule178

/- Helper module WaveFinal. -/
section P2MDyadicModule179

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute GaussianIteration SamplerParameters

noncomputable section

theorem pickup_word {h k m : ℕ} (S : List Unit) (port : Fin m→Fin k) (x : Bits (h+k)) :
    List.ofFn (fun i=>(pickup (h+k) h (List.ofFn (fun j=>(port j).val)) S i).read x)=
      NativePaddedWords.current (S,List.ofFn (fun j=>rightRegister x (port j))) := by
  let w:=List.ofFn (fun j=>rightRegister x (port j))
  have hp:=StartHistory.padded S w 0 w.length
  simp only [List.drop_zero,List.take_length] at hp
  rw [←show w=List.ofFn (fun j=>rightRegister x (port j)) from rfl,hp]
  apply congrArg List.ofFn
  funext i
  by_cases hh : i.val < m
  · have ho : h+(port ⟨i.val,hh⟩).val < h+k:=by have:=(port ⟨i.val,hh⟩).isLt;omega
    simp [pickup,List.length_ofFn,hh,ho,w,Source.read,rightRegister]
    exact congrArg x (Fin.ext rfl)
  · simp [pickup,List.length_ofFn,hh,w,Source.read]

theorem read_ports (P : Polynomial ℕ) (F : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=F.encAt n) (s : Str) (i : ℕ) :
    ports P desc (s,i)=List.ofFn (fun j=>(F.outW (pinCount P desc s i) j).val) := by
  rw [ports,NativeCall.outs F desc hd]
  have e : (imaginary P (s,i)).length=pinCount P desc s i := (zeroPins_len P _).trans (pin_len P desc _).symm
  exact congrArg (fun j=>List.ofFn (fun p=>(F.outW j p).val)) e

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule179

/- Helper module UseCompiler. -/
section P2MDyadicModule180

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity GaussianIteration SamplerParameters ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary.Automatic

noncomputable section

variable (P : Polynomial ℕ) (desc : Str→Str) (hp : Poly desc)

def rebuilt (table : Str→Str) : MFamily :=
  Classical.choose (compile_placed_gate_recipes (plan P desc) (plan_poly P desc hp) table)

theorem rebuilt_qpt (table : Str→Str) (ht : PolyTimeComputable table) :
    IsMQPT (rebuilt P desc hp table) :=
  (Classical.choose_spec (compile_placed_gate_recipes (plan P desc) (plan_poly P desc hp) table)).1 ht

attribute [local irreducible] occupied blocks readBlock reader allCode Trace.circuit data universalSlot usedBefore ports internal

theorem rebuilt_measures (table : Str→Str) (w : Str) {h : ℕ} :
    let s:=w++table (unary w.length)
    let i:=(internal s).length
    ∀ (t : Trace 0 h), h=(occupied P desc s).length → t.blocks=blocks P desc s →
    ∃ msg : Bits h→Str,
      (∀ E : Str→Prop, outputProb (rebuilt P desc hp table) w E=evaluate (law t) (fun x=>indicator E (msg x))) ∧
      ∀ x,List.ofFn (fun j=>(pickup h (usedBefore P desc (s,i)).length (ports P desc (s,i)) (universalSlot P (data s)) j).read x) <+: msg x := by
  intro s i t heq hb
  subst h
  let a:=reader P desc s
  let tr:=t.extend a ([] : Layered (universalSlot P (data s)).length)
  have code : allCode ([],blocks P desc s++[readBlock P desc s])=tr.circuit.flatten.map encodeInstr := by
    have hh:=native_trace tr
    change allCode ([],tr.blocks)=_ at hh
    rw [show tr.blocks=t.blocks++[pack a []] from rfl,hb,readPack] at hh
    exact hh
  let c := tr.circuit
  obtain ⟨f,pre,lawE⟩ := (Classical.choose_spec (compile_placed_gate_recipes (plan P desc) (plan_poly P desc hp) table)).2 w
  let g (x : Bits (occupied P desc s).length) := Fin.append x (fun j=>(a j).read x)
  refine ⟨fun x=>f (g x),fun E=>?_,fun x=>?_⟩
  · refine (lawE c ?_ E).trans (read_eval t a f E)
    change allCode ([],blocks P desc s++[readBlock P desc s]) = _
    refine code.trans ?_
    congr 1
    funext g
    cases g <;> rfl
  · have z:=pre (g x)
    change List.ofFn (fun j=>Fin.append x (fun j=>(a j).read x) (Fin.natAdd _ j)) <+: f (g x) at z
    simpa only [Fin.append_right,a,reader,i] using z

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule180

/- Helper module WaveAdvice. -/
section P2MDyadicModule181

set_option autoImplicit false

set_option maxHeartbeats 1100000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity RectangularSource SamplerParameters

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

variable (P : Polynomial ℕ)

def plainCell (s : Str) (i : ℕ) (raw tbl : Str) : Cell.Input :=
  ((stageProgram P (s,i),(copies P (SamplerParameters.read s),universalSlot P (SamplerParameters.read s))),raw,tbl)

@[fun_prop] theorem plain_poly : Poly (fun u : (Str×ℕ)×(Str×Str) => plainCell P u.1.1 u.1.2 u.2.1 u.2.2) := by
  unfold plainCell;fun_prop

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule181

/- Helper module WaveLaw. -/
section P2MDyadicModule182

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1350000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute SamplerParameters GaussianIteration

open scoped Classical BigOperators

noncomputable section

variable (P : Polynomial ℕ) (F : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=F.encAt n)

attribute [local irreducible] allPins inputs repeats usedBefore internal data FirstPool.arenaSlots batch0 unitTicks ports

include hd in
theorem pin_cell (s : Str) (i : ℕ) : (unitTicks P desc (s,i)).length=pinCount P desc s i+(F.anc (pinCount P desc s i)+1) := by
  rw [pinCount,pin_len];exact cell_width P F desc hd _

include hd in
theorem counted_ports (s : Str) (i : ℕ) : ports P desc (s,i)=List.ofFn (fun u => (F.outW (pinCount P desc s i) u).val) := by
  rw [ports,NativeCall.outs F desc hd,zeroPins_len,pinCount,pin_len]

theorem begin_law (s : Str) : law (beginWave P s).tr=StartHistory.law (batch0 P s) := by
  apply DFunLike.ext;intro x
  simp only [beginWave,law,StartHistory.law,GaussianIteration.born,PMF.ofFintype_apply,Batch.initial_state];rfl

def reindex {n m m' : ℕ} (e : m=m') (f : Rows n m) : Rows n m' :=
  fun j => f (Fin.cast e.symm j)

def newRows (n m : ℕ) (s : Str) (i : ℕ) (w : Wave) (hm : (repeats P (s,i)).length=m)
    (x : Bits (moreWave P F desc s i w).width) : Rows n m :=
  reindex hm (Batch.rows (outputRow n F (pinCount P desc s i)) _ x)

theorem map_agree {X Y : Type*} (p : PMF X) (f g : X→Y) (e : ∀ x,p x≠0 → f x=g x) :
    p.map f=p.map g := by
  ext y
  simp only [PMF.map_apply]
  apply tsum_congr;intro x
  by_cases hv : p x=0
  · simp [hv]
  · rw [e x hv]

def lawAt {n : ℕ} (s : Str) (i : ℕ) (read : Bits (waves P F desc s i).width→Rows n (P.eval n)) :=
  (law (waves P F desc s i).tr).map read

def Step (P : Polynomial ℕ) (F : MFamily) {n : ℕ} (C : MFamily) (B : Matrix (Fin n) (Fin n) ℤ) (R t : ℚ)
    (k : ℕ) (s : Str) (i S : ℕ) : Type 1 :=
  (a : AnalysisData C P B R k) ×'
    (∀ raw (z : Rows n (P.eval n)), raw.length=(P.eval n)*S →
     (∀ u,encVec encI (z u) <+: (raw.drop (u.val*S)).take S) →
       outputProb F (head (s,i)++raw) (SignedSlot.canon n S)=1 ∧
       (z∈keeps (P.eval n) (imageGrid n (2^a.grid)) → ∀ T : Finset (Vec n),
        |finiteMass ((measuredWord F (head (s,i)++raw)).map (SignedSlot.decodeWord n)) T-
         ∑ v∈T,RegevSketch.coefficientMass B t v| ≤ a.cost z))

def new_round {n : ℕ} (C : MFamily) (B : Matrix (Fin n) (Fin n) ℤ) (R t : ℚ) (k : ℕ) (s : Str) (i S m : ℕ)
    (hm : (repeats P (s,i)).length=m) (w : Wave) (decode : Bits w.width → Rows n (P.eval n))
    (tape : Bits w.width → Str) (ok : ∀ x, w.tr.state x≠0 → input (prepares P desc s i w.width) x=head (s,i)++tape x)
    (len : ∀ x,w.tr.state x≠0 → (tape x).length=(P.eval n)*S)
    (valid : ∀ x,w.tr.state x≠0 → ∀ u, encVec encI (decode x u) <+: ((tape x).drop (u.val*S)).take S)
    (a : Step P F C B R t k s i S) :
    Round C P B R t k m ((law w.tr).map decode) ((law (moreWave P F desc s i w).tr).map (newRows P F desc n m s i w hm)) := by
  subst m
  exact actual_round F _ w.tr a.1 s i S decode tape ok len valid (fun raw z hr hv => (a.2 raw z hr hv).2)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule182

/- Helper module OldTape. -/
section P2MDyadicModule183

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport

open SamplerParameters

noncomputable section

variable {h : ℕ}

def value (x : Bits h) (p : Pin) : Bool :=
  if p.1=2 then (List.ofFn x)[p.2]?.getD false else decide (p.1=1)

theorem value_wire (x : Bits h) (i : Fin h) : value x (2,i.val)=x i := by simp [value]

theorem value_false (x : Bits h) : value x (0,0)=false := by simp [value]

def encodedRow (P : Polynomial ℕ) (desc : Str→Str) (r : Request) (x : Bits h) (i : ℕ) : Str :=
  List.ofFn (fun j : Fin (universalSlot P (data r.1)).length => value x (oldPin P desc ((r,i),j.val)))

def oldTape (P : Polynomial ℕ) (desc : Str→Str) (r : Request) (x : Bits h) : Str :=
  (List.ofFn (fun i : Fin (copies P (data r.1)).length => encodedRow P desc r x i.val)).flatten

theorem map_range_eq {X : Type*} (f : ℕ→X) (n : ℕ) : (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

theorem actual_pins (P : Polynomial ℕ) (desc : Str→Str) (r : Request) (x : Bits h) :
    (oldPins P desc r).map (value x)=oldTape P desc r x := by
  simp only [oldPins,rowPins,oldTape,encodedRow,rowRange,columnRange,List.flatMap_def,map_range_eq,List.map_flatten,List.map_ofFn,Function.comp_def]

theorem tape_length (P : Polynomial ℕ) (desc : Str→Str) (r : Request) (x : Bits h) :
    (oldTape P desc r x).length=(copies P (data r.1)).length*(universalSlot P (data r.1)).length := by
  simp [oldTape,encodedRow,List.length_flatten,List.map_ofFn,Function.comp_def,List.ofFn_const,List.sum_replicate]

theorem tape_row (P : Polynomial ℕ) (desc : Str→Str) (r : Request) (x : Bits h)
    (i : Fin (copies P (data r.1)).length) :
    ((oldTape P desc r x).drop (i.val*(universalSlot P (data r.1)).length)).take (universalSlot P (data r.1)).length=
      encodedRow P desc r x i.val := by
  simpa only [oldTape,FirstPool.slice,List.append_nil] using
    FirstPool.select_cell (universalSlot P (data r.1)).length
      (fun i : Fin (copies P (data r.1)).length => encodedRow P desc r x i.val) (fun _ => List.length_ofFn) [] i

attribute [local irreducible] FirstPool.slot batch0 FirstPool.outputOffset universalSlot data

theorem first_row (P : Polynomial ℕ) (desc : Str→Str) (s : Str) (x : Bits (StartHistory.size (batch0 P s))) (i : ℕ) :
    encodedRow P desc (s,0) x i=StartHistory.absolute (batch0 P s) (universalSlot P (data s)) x i := by
  rw [StartHistory.absolute_pins]
  apply congrArg List.ofFn;funext j
  change value x (firstPin P ((s,i),j.val))=_
  unfold firstPin
  by_cases hc : j.val<(FirstPool.slot (batch0 P s).1).length
  · simp only [hc,if_true,value]
  · simp only [hc,if_false,value_false]

theorem current_chars (S : List Unit) (w : Str) :
    NativePaddedWords.current (S,w)=List.ofFn (fun i : Fin S.length => w[i.val]?.getD false) := by
  have ht := StartHistory.padded S w 0 w.length
  simp only [List.drop_zero,List.take_length,zero_add] at ht
  rw [ht]
  apply congrArg List.ofFn;funext i
  by_cases hi : i.val<w.length
  · simp [hi]
  · simp [hi,List.getElem?_eq_none (by omega : w.length≤i.val)]

theorem later_row (P : Polynomial ℕ) (desc : Str→Str) (G : MFamily) (s : Str) (i j m h : ℕ)
    (hbase : (usedBefore P desc (s,i)).length=h)
    (hcell : (unitTicks P desc (s,i)).length=j+(G.anc j+1))
    (hc : (repeats P (s,i)).length=m)
    (ho : ports P desc (s,i)=List.ofFn (fun u => (G.outW j u).val))
    (x : Bits (Batch.size h (j+(G.anc j+1)) m)) (row : Fin m) :
    encodedRow P desc (s,i+1) x row.val=
      NativePaddedWords.current (universalSlot P (data s),Batch.rows (NativeCall.chosen G j) m x row) := by
  rw [current_chars,Batch.rows_wire]
  apply congrArg List.ofFn;funext col
  simp only [oldPin,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,ho,List.length_ofFn,hbase,hcell,hc]
  by_cases hcol : col.val<G.outLen j
  · simp only [hcol,if_true,List.getElem?_ofFn,↓reduceDIte,Option.getD_some]
    let u : Fin (G.outLen j) := ⟨_,hcol⟩
    have hh := value_wire x (Batch.rowWire h row (G.outW j u))
    rw [show ((2,h+(m-1-row.val)*(j+(G.anc j+1))+(G.outW j u).val):Pin)=(2,(Batch.rowWire h row (G.outW j u)).val) from rfl,hh]
    simp only [NativeCall.chosen,List.getElem?_ofFn,hcol,↓reduceDIte,Option.getD_some]
    rfl
  · simp only [hcol,if_false,value_false,NativeCall.chosen,List.getElem?_ofFn,↓reduceDIte,Option.getD_none]

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule183

/- Helper module WaveHistory. -/
section P2MDyadicModule184

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity SamplerParameters GaussianIteration RegevSketch

open scoped Classical BigOperators

noncomputable section

variable (P : Polynomial ℕ) (G : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=G.encAt n)

abbrev space (s : Str) := (universalSlot P (data s)).length

def slice {h : ℕ} (s : Str) (i : ℕ) (x : Bits h) (r : ℕ) :=
  ((oldTape P desc (s,i) x).drop (r*space P s)).take (space P s)

def view {h : ℕ} (n : ℕ) (s : Str) (i : ℕ) (x : Bits h) : Rows n (P.eval n) :=
  fun u => SignedSlot.decodeWord n (slice P desc s i x u.val)

def Valid (n : ℕ) (s : Str) (i : ℕ) : Prop :=
  ∀ x,(waves P G desc s i).tr.state x≠0 → ∀ u : Fin (P.eval n),
   encVec encI (view P desc n s i x u) <+: slice P desc s i x u.val

def history (n : ℕ) (s : Str) (i : ℕ) := lawAt P G desc s i (view P desc n s i)

theorem slice_decodes {n h : ℕ} (s : Str) (i : ℕ) (x : Bits h) (u : Fin (P.eval n))
    (z : Vec n) (hz : encVec encI z <+: slice P desc s i x u.val) :
    view P desc n s i x u=z := SignedSlot.decode_prefix _ _ hz

attribute [local irreducible] universalSlot allPins copies FirstPool.loader FirstPool.slot internal

def initialRead {n : ℕ} (v : FirstPool.Batch) (hm : v.2.length=P.eval n)
    (x : Bits (StartHistory.size v)) (j : Fin (P.eval n)) :=
  FirstPool.readPool n v x (Fin.cast hm.symm j)

theorem boot_from {n : ℕ} (s : Str) (p : PMF (Rows n (P.eval n)))
    (hm : (batch0 P s).2.length=P.eval n)
    (base : (StartHistory.law (batch0 P s)).map (initialRead P (batch0 P s) hm)=p)
    (pre : ∀ x,StartHistory.law (batch0 P s) x≠0 → ∀ j, encVec encI (initialRead P (batch0 P s) hm x j) <+:
      StartHistory.absolute (batch0 P s) (universalSlot P (data s)) x j.val) :
    history P G desc n s 0=p ∧ Valid P G desc n s 0 := by
  have hc : (copies P (data s)).length=P.eval n := hm
  have hh (x : Bits (StartHistory.size (batch0 P s))) (hx : StartHistory.law (batch0 P s) x≠0) (j : Fin (P.eval n)) :
      encVec encI (initialRead P (batch0 P s) hm x j) <+: slice P desc s 0 x j.val := by
    let u : Fin (copies P (data s)).length := Fin.cast hc.symm j
    change _ <+: slice P desc s 0 x u.val
    rw [slice,tape_row P desc (s,0) x u,first_row]
    exact pre x hx j
  constructor
  · change (law (beginWave P s).tr).map _=_
    rw [begin_law,←base];apply map_agree;intro x hx;funext j
    exact slice_decodes P desc s 0 x j _ (hh x hx j)
  · intro x hx j
    have nz := (Batch.law_ne (beginWave P s).tr x).mpr hx
    rw [begin_law] at nz
    have h := hh x nz j
    rw [slice_decodes P desc s 0 x j _ h]
    exact h

theorem boot_ok {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (k : ℕ) (tbl : Str) :
    let s := dgsInput B r 1 k++tbl
    history P G desc n s 0=zeroIdeal B r (P.eval n) ∧ Valid P G desc n s 0 := by
  intro s
  let d := SamplerParameters.read (dgsInput B r 1 k)
  have hdata : data s=d := by simp only [s,data,unframed,split_input,d]
  obtain ⟨hm,base,pre⟩ : ∃ hm : (batch0 P s).2.length=P.eval n,
      (StartHistory.law (batch0 P s)).map (initialRead P (batch0 P s) hm)=zeroIdeal B r (P.eval n) ∧
      ∀ x,StartHistory.law (batch0 P s) x≠0 → ∀ j, encVec encI (initialRead P (batch0 P s) hm x j) <+:
          StartHistory.absolute (batch0 P s) (universalSlot P (data s)) x j.val := by
    rw [batch0,hdata]
    exact StartHistory.base P B hB r k
  exact boot_from P G desc s _ hm base pre

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule184

/- Helper module WiredInputs. -/
section P2MDyadicModule185

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute FiniteGateTransport SamplerParameters

open scoped Classical

noncomputable section

variable {h : ℕ}

theorem read_choose (x : Bits h) (p : Pin) : (choose h p).read x=value x p := by
  obtain ⟨t,i⟩ := p
  by_cases ht : t=2
  · subst t
    by_cases hi : i<h <;> simp [choose,Source.read,value,hi]
  · simp [choose,Source.read,value,ht]

theorem read_clipped (x : Bits h) (p : Pin) : value x (clipped h p)=value x p := by
  obtain ⟨t,i⟩ := p
  by_cases ht : t=2
  · subst t
    by_cases hi : i<h <;> simp [clipped,value,hi]
  · by_cases hu : t=1 <;> simp [clipped,value,ht,hu]

theorem read_lit (x : Bits h) (b : Bool) : value x (UniformInput.lit b)=b := by cases b <;> rfl

variable (P : Polynomial ℕ) (G : MFamily) (desc : Str→Str) (hd : ∀ j,desc (unary j)=G.encAt j)

attribute [local irreducible] oldPins allPins usedBefore data universalSlot inputs internal stages batch0 FirstPool.slot copies unitTicks ports repeats

theorem prepared_tape (s : Str) (i : ℕ) (x : Bits h) (hh : (usedBefore P desc (s,i)).length=h) :
    input (prepares P desc s i h) x=head (s,i)++oldTape P desc (s,i) x := by
  have he : input (prepares P desc s i h) x=(allPins P desc (s,i)).map (value x) := by
    apply List.ext_getElem
    · simp only [input,List.length_ofFn,List.length_map]
    · intro j hj1 hj2
      simp only [input,List.getElem_ofFn,prepares,read_choose,List.getElem_map]
  rw [he,allPins,List.map_append,List.map_map,List.map_map]
  simp only [Function.comp_def,read_lit,hh,read_clipped,actual_pins]
  rw [show (fun x : Bool=>x)=id from rfl,List.map_id]

include hd in
theorem wave_tape (s : Str) (i : ℕ) (hi : i≤(internal s).length) (x : Bits (waves P G desc s i).width) :
    input (prepares P desc s i _) x=head (s,i)++oldTape P desc (s,i) x :=
  prepared_tape P desc s i x (waves_width P G desc hd s i hi).symm

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule185

/- Helper module WaveJourney. -/
section P2MDyadicModule186

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1700000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity SamplerParameters GaussianIteration

open scoped Classical BigOperators

noncomputable section

variable (P : Polynomial ℕ) (G : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=G.encAt n)

attribute [local irreducible] allPins repeats internal universalSlot copies oldTape SignedSlot.decodeWord

def nativeRows (n m : ℕ) (s : Str) (i : ℕ) (hm : (repeats P (s,i)).length=m) :=
  newRows P G desc n m s i (waves P G desc s i) hm

def wordRow (m : ℕ) (s : Str) (i : ℕ) (hm : (repeats P (s,i)).length=m)
    (x : Bits (waves P G desc s (i+1)).width) (u : Fin m) :=
  NativePaddedWords.current (universalSlot P (data s),Batch.rows (NativeCall.chosen G (pinCount P desc s i)) _ x (Fin.cast hm.symm u))

def afterLaw (n m : ℕ) (s : Str) (i : ℕ) (hm : (repeats P (s,i)).length=m) :=
  (law (waves P G desc s (i+1)).tr).map (nativeRows P G desc n m s i hm)

include hd in
theorem step_law {n : ℕ} (C : MFamily) (B : Matrix (Fin n) (Fin n) ℤ) (R t : ℚ) (k : ℕ) (s : Str) (i m : ℕ)
    (hi : i ≤ (internal s).length) (hm : (repeats P (s,i)).length=m) (hc : (copies P (data s)).length=P.eval n)
    (v : Valid P G desc n s i) (a : Step P G C B R t k s i (space P s)) :
    Nonempty (Round C P B R t k m (history P G desc n s i) (afterLaw P G desc n m s i hm)) ∧
    ∀ x, (waves P G desc s (i+1)).tr.state x≠0 → ∀ u : Fin m,
      encVec encI (nativeRows P G desc n m s i hm x u) <+: wordRow P G desc m s i hm x u := by
  let w := waves P G desc s i
  let read := view P desc n s i (h:=w.width)
  let raw := oldTape P desc (s,i) (h:=w.width)
  have inp (x : Bits w.width) := wave_tape P G desc hd s i hi x
  have len (x : Bits w.width) : (raw x).length=(P.eval n)*(space P s) := by rw [show raw x=oldTape P desc (s,i) x from rfl,tape_length,hc]
  have canon (x : Bits w.width) (hx : w.tr.state x≠0) : outputProb G (input (prepares P desc s i _) x) (SignedSlot.canon n (space P s))=1 := by
    rw [inp];exact (a.2 (raw x) (read x) (len x) (v x hx)).1
  refine ⟨⟨new_round P G desc C B R t k s i (space P s) m hm w read raw (fun x _ => inp x) (fun x _ => len x) v a⟩,?_⟩
  intro x hx u
  have h := SignedSlot.batch_prefix G (prepares P desc s i _) w.tr _ canon x hx (Fin.cast hm.symm u)
  apply preserve _ (h.trans (List.take_prefix _ _))
  exact h.length_le.trans (List.length_take_le ..)

include hd in
theorem next_law {n : ℕ} (C : MFamily) (B : Matrix (Fin n) (Fin n) ℤ) (R t : ℚ) (k : ℕ) (s : Str) (i : ℕ)
    (hi : i < (internal s).length) (hc : (copies P (data s)).length=P.eval n)
    (v : Valid P G desc n s i) (a : Step P G C B R t k s i (space P s)) :
    Nonempty (Round C P B R t k (P.eval n) (history P G desc n s i) (history P G desc n s (i+1))) ∧ Valid P G desc n s (i+1) := by
  have hm := (congrArg List.length (start_active P s i hi)).trans hc
  obtain ⟨round,good⟩ := step_law P G desc hd C B R t k s i _ hi.le hm hc v a
  have eq (x : Bits (waves P G desc s (i+1)).width) (u : Fin (P.eval n)) :
      slice P desc s (i+1) x u.val=wordRow P G desc _ s i hm x u := by
    let j : Fin (copies P (data s)).length := Fin.cast hc.symm u
    let l : Fin (repeats P (s,i)).length := Fin.cast hm.symm u
    change slice P desc s (i+1) x j.val=_
    rw [slice,tape_row P desc (s,i+1) x j]
    exact later_row P desc G s i _ _ _ (waves_width P G desc hd s i hi.le).symm (pin_cell P G desc hd s i) rfl (counted_ports P G desc hd s i) x l
  have first (x : Bits (waves P G desc s (i+1)).width) (hx : (waves P G desc s (i+1)).tr.state x≠0) (u : Fin (P.eval n)) :
      encVec encI (nativeRows P G desc n (P.eval n) s i hm x u) <+: slice P desc s (i+1) x u.val := by
    rw [eq];exact good x hx u
  have same (x : Bits (waves P G desc s (i+1)).width) (hx : (waves P G desc s (i+1)).tr.state x≠0) :
      view P desc n s (i+1) x=nativeRows P G desc n (P.eval n) s i hm x := by
    funext u;exact slice_decodes P desc s _ x u _ (first x hx u)
  have prob : history P G desc n s (i+1)=afterLaw P G desc n _ s i hm :=
    map_agree _ _ _ (fun x hx => same x ((Batch.law_ne _ _).mp hx))
  refine ⟨prob.symm ▸ round,?_⟩
  intro x hx u;rw [same x hx];exact first x hx u

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule186

/- Helper module WaveExecution. -/
section P2MDyadicModule187

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity SamplerParameters GaussianIteration RegevSketch

open scoped Classical BigOperators

noncomputable section

variable (P : Polynomial ℕ) (G : MFamily) (desc : Str→Str) (hd : ∀ n,desc (unary n)=G.encAt n)

attribute [local irreducible] allPins repeats internal universalSlot copies usedBefore data batch0

def terminalCount (s : Str) : (repeats P (s,(internal s).length)).length=1 := congrArg List.length (end_active P s)

def Measures (H : MFamily) (s w : Str) :=
  let i := (internal s).length
  ∃ msg : Bits (waves P G desc s (i+1)).width→Str,
    (∀ E : Str→Prop, outputProb H w E=evaluate (law (waves P G desc s (i+1)).tr) (fun x=>indicator E (msg x))) ∧
    ∀ x,wordRow P G desc 1 s i (terminalCount P s) x 0 <+: msg x

abbrev successor {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (i : ℕ) :=
  if i < stop B r then W B r (i+1) else r

theorem run_constants {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℚ) (k : ℕ) (tbl : Str) :
    let s:=dgsInput B r 1 k++tbl
    (internal s).length=stop B r ∧ (copies P (data s)).length=P.eval n := by
  intro s
  let d := SamplerParameters.read (dgsInput B r 1 k)
  have hdata : data s=d := by simp only [s,data,unframed,split_input,d]
  have p := exact_parameters P B hB r k
  constructor
  · rw [internal_eq,List.length_range,hdata,p.2.1]
  · rw [hdata]
    have eq := congrArg (fun v : FirstPool.Batch => v.2.length) p.1
    exact eq.trans List.length_replicate

include hd in
theorem execution_of_steps {n : ℕ} (C H : MFamily) (B : Matrix (Fin n) (Fin n) ℤ) (s : Str) (r : ℚ) (k : ℕ)
    (hs : (internal s).length=stop B r) (hc : (copies P (data s)).length=P.eval n)
    (boot : history P G desc n s 0=zeroIdeal B r (P.eval n)) (start : Valid P G desc n s 0)
    (steps : ∀ i, i ≤ stop B r → Nonempty (Step P G C B (W B r i) (successor B r i) (precision n (P.eval n) k) s i (space P s)))
    (out : Measures P G desc H s (dgsInput B r 1 k)) : Nonempty (Execution H C P B r k) := by
  let L := (internal s).length
  let q := precision n (P.eval n) k
  have hstep (i : ℕ) (hi : i < L) (v : Valid P G desc n s i) :
      Nonempty (Round C P B (W B r i) (W B r (i+1)) q (P.eval n) (history P G desc n s i) (history P G desc n s (i+1))) ∧
      Valid P G desc n s (i+1) := by
    have h : i<stop B r := hi.trans_eq hs
    obtain ⟨a⟩:=steps i h.le
    rw [successor,if_pos h] at a
    exact next_law P G desc hd C B _ _ q s i hi hc v a
  have valid (i : ℕ) (hi : i ≤ L) : Valid P G desc n s i := by
    induction i with
    | zero => exact start
    | succ i ih =>
      have h : i<L := by omega
      exact (hstep i h (ih h.le)).2
  have endstep := steps L (le_of_eq hs)
  obtain ⟨a⟩:=endstep
  rw [successor,if_neg (by omega : ¬L<stop B r)] at a
  have hm := terminalCount P s
  obtain ⟨⟨last⟩,prefixes⟩:=step_law P G desc hd C B _ _ q s L 1 le_rfl hm hc (valid _ le_rfl) a
  obtain ⟨msg,meas,front⟩:=out
  have pair := final_read (law (waves P G desc s (L+1)).tr) msg (nativeRows P G desc n 1 s L hm) H (dgsInput B r 1 k) meas
    (fun x hx => (prefixes x ((Batch.law_ne _ _).mp hx) 0).trans (front x))
  refine ⟨⟨history P G desc n s,boot,afterLaw P G desc n 1 s L hm,?_,?_,pair.1,pair.2⟩⟩
  · intro i hi
    have h : i<L := hi.trans_eq hs.symm
    exact Classical.choice (hstep i h (valid i h.le)).1
  · change Round C P B (W B r (stop B r)) r q 1 (history P G desc n s (stop B r)) _
    rw [←hs];exact last

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule187

/- Helper module WaveTerminal. -/
section P2MDyadicModule188

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute GaussianIteration SamplerParameters

noncomputable section

theorem capture_row {h j m : ℕ} (F : MFamily) (hm : m=1) (S : List Unit) (off : ℕ) (ps : List ℕ)
    (ho : off=h) (hps : ps=List.ofFn (fun i=>(F.outW j i).val))
    (z : Bits (Batch.size h (j+(F.anc j+1)) m)) :
    List.ofFn (fun i=>(pickup (Batch.size h (j+(F.anc j+1)) m) off ps S i).read z)=
      NativePaddedWords.current (S,Batch.rows (NativeCall.chosen F j) m z (Fin.cast hm.symm 0)) := by
  subst m;subst off;subst ps
  exact pickup_word S (F.outW j) z

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule188

/- Helper module MeasureCompiled. -/
section P2MDyadicModule189

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute GaussianIteration SamplerParameters

noncomputable section

attribute [local irreducible] allPins usedBefore repeats occupied ports internal universalSlot plan

theorem actual_measure_compiled (P : Polynomial ℕ) (F : MFamily) (desc : Str→Str)
    (hp : OAI.MetricKMedian.Binary.Automatic.Poly desc) (hd : ∀ n,desc (unary n)=F.encAt n)
    (table : Str→Str) (w : Str) :
    Measures P F desc (rebuilt P desc hp table) (w++table (unary w.length)) w := by
  let s:=w++table (unary w.length)
  let i:=(internal s).length
  let w₀:=waves P F desc s i
  let last:=waves P F desc s (i+1)
  let j:=pinCount P desc s i
  let m:=(repeats P (s,i)).length
  have hm : m=1:=terminalCount P s
  obtain ⟨msg,hprob,hprefix⟩:=rebuilt_measures P desc hp table w last.tr (all_width P F desc hd s) (all_blocks P F desc hd s)
  refine ⟨msg,hprob,fun x=>?_⟩
  have h₀ : (usedBefore P desc (s,i)).length=w₀.width := (waves_width P F desc hd s i le_rfl).symm
  have eq:= capture_row (h:=w₀.width) (j:=j) (m:=m) F hm (universalSlot P (data s))
    (usedBefore P desc (s,i)).length (ports P desc (s,i)) h₀ (read_ports P F desc hd s i) x
  exact (congrArg (fun z=>z <+: msg x) eq).mp (hprefix x)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule189

/- Helper module PublicController. -/
section P2MDyadicModule190

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity RegevSketch GaussianIteration RectangularSource SamplerParameters

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

noncomputable section

variable (P : Polynomial ℕ)

def requestSize (req : Cell.Input→List Unit) (u : OracleTable.Inputs) := req (plainCell P u.1 u.2.2.length u.2.1 [])

@[fun_prop] theorem requestSize_poly (req : Cell.Input→List Unit) (hq : Poly req) : Poly (requestSize P req) := by
  let f (u : OracleTable.Inputs) : (Str×ℕ)×(Str×Str) := ((u.1,u.2.2.length),(u.2.1,[]))
  have hf : Poly f := by unfold f;fun_prop
  let select := fun u : (Str×ℕ)×(Str×Str) => plainCell P u.1.1 u.1.2 u.2.1 u.2.2
  have hs : Poly (fun u : OracleTable.Inputs => select (f u)) := Poly.comp (f:=select) (g:=f) (plain_poly P) hf
  exact Poly.comp (f:=req) (g:=fun u : OracleTable.Inputs => select (f u)) (hq) hs

theorem generic_table (F : MFamily) (hF : IsMQPT F) (req : Cell.Input→List Unit) (hq : Poly req) (hfree : TableIndependent req) :
    ∃ tbl : Str→Str, PolyTimeComputable tbl ∧ ∀ s i raw,
      i ≤ (RunnableWidths.fuel (widths (SamplerParameters.read s))).length →
      raw.length ≤ (poolSpace P s).length →
      let t := tbl (unary s.length)
      let len := (req (plainCell P s i raw t)).length
      OracleTable.lookup (t,len)=F.encAt len := by
  let fuel := fun s : Str => RunnableWidths.fuel (widths (SamplerParameters.read s))
  have hf : Poly fuel := by unfold fuel;fun_prop
  obtain ⟨tbl,ht,lookup⟩ := all_descriptions F hF P (requestSize P req) (requestSize_poly P req hq) (PlacedCPU.bound hf)
  refine ⟨tbl,ht,?_⟩
  intro s i raw hi hr
  have bound : (unary i).length ≤ (PlacedCPU.bound hf).eval s.length := by
    change _ ≤ _
    simpa only [unary,List.length_replicate] using hi.trans (PlacedCPU.bound_length hf s)
  have he := lookup s raw (unary i) [] hr bound
  simp only [List.append_nil,requestSize,unary,List.length_replicate] at he
  dsimp only
  rw [show req (plainCell P s i raw (tbl (unary s.length)))=req (plainCell P s i raw []) from hfree _ _ _ _]
  exact he

def TransitionSource (P : Polynomial ℕ) (C F G : MFamily) (req : Cell.Input→List Unit) :=
  ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ), B.det≠0 → 2≤n → ∀ r : ℚ, 0<r → dgsThreshold B≤(r:ℝ) →
    ∀ (user i : ℕ) (tbl : Str),
    let s:=dgsInput B r 1 user
    let d:=SamplerParameters.read s
    i ≤ RunnableWidths.count (widths d) →
    (∀ raw : Str, raw.length ≤ (poolSpace P s).length →
      let l := (req (plainCell P s i raw tbl)).length
      OracleTable.lookup (tbl,l)=F.encAt l) →
    Nonempty (Step P G C B (old (d,i)) (next (d,i)) (precision n (P.eval n) user) (s++tbl) i (universalSlot P d).length)

def Descriptions (P : Polynomial ℕ) (F : MFamily) (req : Cell.Input→List Unit) (t : Str→Str) :=
  ∀ (s : Str) (i : ℕ) (raw : Str), i ≤ (RunnableWidths.fuel (widths (SamplerParameters.read s))).length →
     raw.length ≤ (poolSpace P s).length →
     let v:=t (unary s.length)
     let l:=(req (plainCell P s i raw v)).length
     OracleTable.lookup (v,l)=F.encAt l

theorem all_transitions (P : Polynomial ℕ) (C F G : MFamily) (req : Cell.Input→List Unit) (src : TransitionSource P C F G req)
    (t : Str→Str) (table : Descriptions P F req t) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (hn : 2≤n) (r : ℚ) (hr : 0<r) (hp : dgsThreshold B≤(r:ℝ)) (k : ℕ) :
    let s := dgsInput B r 1 k
    let outer := s++t (unary s.length)
    ∀ i, i ≤ stop B r → Nonempty (Step P G C B (W B r i) (successor B r i) (precision n (P.eval n) k) outer i (space P outer)) := by
  intro s outer i hi
  let d := SamplerParameters.read s
  let tbl := t (unary s.length)
  have hdata : data outer=d := by simp only [outer,s,d,data,unframed,split_input]
  have hwidth : widths d=RunnableWidths.data B r := (exact_parameters P B hB r k).2.1
  have hcount : RunnableWidths.count (widths d)=stop B r := congrArg RunnableWidths.count hwidth
  have hlim : i ≤ RunnableWidths.count (widths d) := hi.trans_eq hcount.symm
  have hfu : i ≤ (RunnableWidths.fuel (widths d)).length := by
    apply hlim.trans
    unfold RunnableWidths.count
    simpa only [List.length_range] using List.length_filter_le (RunnableWidths.above (widths d)) (List.range (RunnableWidths.fuel (widths d)).length)
  have hz := src B hB hn r hr hp k i tbl hlim (fun raw e => table s i raw hfu e)
  have hR (l : ℕ) : old (d,l)=W B r l := congrArg (fun x=>RunnableWidths.width x l) hwidth
  have ht : next (d,i)=successor B r i := by
    have g := (stage_guarantees hn B hB r hr hp k i).2 hlim
    by_cases h : i<stop B r
    · rw [successor,if_pos h]
      exact (g.2.2.2.2.2.1 (h.trans_eq hcount.symm)).trans (hR (i+1))
    · rw [successor,if_neg h]
      exact g.2.2.2.2.2.2 ((le_antisymm hi (Nat.le_of_not_lt h)).trans hcount.symm)
  rw [hR,ht] at hz
  change Nonempty (Step P G C B _ _ _ outer i (universalSlot P (data outer)).length)
  rw [hdata];exact hz

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule190

/- Helper module PublicTop. -/
section P2MDyadicModule191

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity RegevSketch GaussianIteration SamplerParameters RectangularSource

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

noncomputable section

theorem as_transition (P : Polynomial ℕ) (C F G : MFamily) (query : Cell.Input→List Unit)
    (perform : FourierRowGuarantee P C F G query (stageData P)) : TransitionSource P C F G query := by
  intro n B hB hn r hr hp k i tbl s d hi lookup
  have pars:=exact_parameters P B hB r k
  let nt:=dim d
  let count:=copies P d
  let acc:=budget P d
  let ora:=oracle P d
  let S:=universalSlot P d
  let R:=old (d,i)
  let t:=next (d,i)
  let c:=radius n t
  have mat : d.1.1=RationalInverse.Native.inputRows B := by simp [d,s,read_input]
  have ntw : nt=List.replicate n () := by
    apply Integration9_9.TM2PolynomialBudget.unitList_eq
    simp [nt,d,s,read_input,dim,RationalInverse.Native.inputRows]
  have dn : nt.length=n := by rw [ntw,List.length_replicate]
  have hm : count.length=P.eval n := by change (List.replicate (P.eval nt.length) ()).length=_;rw [dn,List.length_replicate]
  have hb : acc.length=precision n (P.eval n) k := pars.2.2.1
  have ho : ora.length=poolBDDPrecision (((P+1)+(P+1)).eval n) acc.length := by rw [hb];exact pars.2.2.2
  have gr : PhysicalGrid.gridTape (PhysicalGrid.setup B t n)=rowGrid (d,i) := by
    change PhysicalGrid.gridTape (RationalInverse.Native.inputRows B,t,List.replicate n ())=PhysicalGrid.gridTape (d.1.1,t,nt)
    rw [mat,ntw]
  have size : (SignedSlot.slot (nt,PhysicalGrid.gridTape (PhysicalGrid.setup B t n))).length≤S.length := by
    rw [gr];exact all_stage_fit P hn B hB r hr hp k i hi
  obtain ⟨⟨hR,ht⟩,_,⟨hc,hcut⟩,⟨scale,cap⟩,sep,_⟩:=(stage_guarantees hn B hB r hr hp k i).2 hi
  obtain ⟨a,work⟩:=perform B hB (by omega) R t hR ht c hc scale cap hcut sep nt count acc ora S dn hm ho size
  rw [←hb]
  refine ⟨⟨a,?_⟩⟩
  intro raw z len valid
  let w:=head (s++tbl,i)++raw
  let v:=plainCell P s i raw tbl
  have eq : v=Cell.receipt (RationalInverse.Native.inputRows B) R t count acc ora count S raw tbl := by
    change Cell.receipt d.1.1 _ _ _ _ _ _ _ _ _=_
    rw [mat]
  have inp : stageData P w=v := stageData_exact P B r k i tbl raw
  have hit := lookup raw (by rw [pool_size,show (copies P (SamplerParameters.read s)).length=P.eval n from hm];exact len.le)
  have result:=work raw tbl w z (inp.trans eq) (eq ▸ hit) valid
  exact ⟨result.1,fun _ => result.2⟩

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule191

/- Helper module TopCompiled. -/
section P2MDyadicModule192

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity RegevSketch GaussianIteration SamplerParameters RectangularSource

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

noncomputable section

theorem from_compiled_row (S : Set ℕ) (C : MFamily) (P : Polynomial ℕ) (N : ℕ)
    (hcopy : ∀ calls : Polynomial ℕ, ∃ e : ℕ→ℝ, Negligible e ∧ SharedPoolCoherence.CopyBudget C P calls N S e)
    (row : UniformFourierRow C P) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ e : ℕ→ℝ, Negligible e ∧ ∃ N' : ℕ, ∀ n∈S,N'≤n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ,B.det≠0 → ∀ r : ℚ,0<r → dgsThreshold B≤(r:ℝ) → ∀ k : ℕ,
        ∃ b : ℕ, gridAdequate B (r:ℝ) (2^b) ∧ outputProb H (dgsInput B r 1 k)
           (fun out => ∃ z : Fin n→ℤ, encVec encI z <+: out)=1 ∧ ∀ T : Finset (Vec n),
          |outputProb H (dgsInput B r 1 k) (fun out => ∃ z∈T,encVec encI z <+: out)-
            fourierEvent B r (2^b) T|≤e n+1/(4*((k:ℝ)+1)) := by
  obtain ⟨F,hF,query,hq,independent,impl⟩:=row
  obtain ⟨G,desc,hp,hd,operation⟩:=impl (stageData P) (stageData_poly P)
  obtain ⟨table,ht,lookup⟩:=generic_table P F hF query hq independent
  let H:=rebuilt P desc hp table
  apply assemble S C P N hcopy H (rebuilt_qpt P desc hp table ht)
  intro n _ _ hn B hB r hr hthreshold k
  let w:=dgsInput B r 1 k
  let tbl:=table (unary w.length)
  obtain ⟨count,hm⟩:=run_constants P B hB r k tbl
  obtain ⟨start,good⟩:=boot_ok P G desc B hB r k tbl
  exact execution_of_steps P G desc hd C H B (w++tbl) r k count hm start good
    (all_transitions P C F G query (as_transition P C F G query operation) table lookup B hB hn r hr hthreshold k)
    (actual_measure_compiled P G desc hp hd table w)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule192
set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch.GaussianIteration
open scoped BigOperators Classical

open InfoLossLAR.WorstCase.RegevSearch

theorem solution (S : Set ℕ) (C : MFamily) (P : Polynomial ℕ) (N : ℕ)
    (hcopy : ∀ calls : Polynomial ℕ, ∃ e : ℕ→ℝ, Negligible e ∧ SharedPoolCoherence.CopyBudget C P calls N S e)
    (row : UniformFourierRow C P) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ e : ℕ→ℝ, Negligible e ∧ ∃ N' : ℕ, ∀ n∈S,N'≤n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ,B.det≠0 → ∀ r : ℚ,0<r → dgsThreshold B≤(r:ℝ) → ∀ k : ℕ,
        ∃ b : ℕ, gridAdequate B (r:ℝ) (2^b) ∧ outputProb H (dgsInput B r 1 k)
           (fun out => ∃ z : Fin n→ℤ, encVec encI z <+: out)=1 ∧ ∀ T : Finset (Vec n),
          |outputProb H (dgsInput B r 1 k) (fun out => ∃ z∈T,encVec encI z <+: out)-
            fourierEvent B r (2^b) T|≤e n+1/(4*((k:ℝ)+1)) := AdaptiveStages.Outer.from_compiled_row S C P N hcopy row


end
