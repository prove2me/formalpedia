-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.coherent_gaussian_ticket_preparation
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:11:06.821465+00:00
-- url     : https://prove2.me/submissions/c0c66f80-6b1b-4c85-a21e-5dfb46e29dde

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_CoherentGaussianTickets
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_01
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_07
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_08
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_NativeCompactPrefix_01
import Definitions.Def_InfoLossLAR_NativeSparsePrefix_01
import Definitions.Def_InfoLossLAR_NativeSparsePrefix_02
import Definitions.Def_InfoLossLAR_ReciprocallyScaledGaussianSource
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RuntimeBundle_01
import Definitions.Def_InfoLossLAR_RuntimeBundle_02
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib
import Theorems.Thm_CliffordTApprox_Ancilla_main_result
set_option Elab.async true
set_option cleanup.letToHave false

set_option linter.all false

namespace AFT
end AFT

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace AFT.FiniteConvolutionProgram
end AFT.FiniteConvolutionProgram

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute
end InfoLossLAR.WorstCase.CoherentComputeUncompute

namespace InfoLossLAR.WorstCase.CoherentControlledSwap
end InfoLossLAR.WorstCase.CoherentControlledSwap

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative
end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

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

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

namespace InfoLossLAR.WorstCase.NativeWordCoherent
end InfoLossLAR.WorstCase.NativeWordCoherent

namespace InfoLossLAR.WorstCase.NativeWordControls
end InfoLossLAR.WorstCase.NativeWordControls

namespace InfoLossLAR.WorstCase.NativeWordLayout
end InfoLossLAR.WorstCase.NativeWordLayout

namespace InfoLossLAR.WorstCase.TM2Boolean
end InfoLossLAR.WorstCase.TM2Boolean

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

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

namespace Integration9_9.LARRankOneMachine
end Integration9_9.LARRankOneMachine

namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2NativeGaussian
end Integration9_9.TM2NativeGaussian

namespace Integration9_9.TM2NativeRootGroupProfiles
end Integration9_9.TM2NativeRootGroupProfiles

namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength

namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization

namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

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

namespace Turing
end Turing

/- Helper module AFT.RationalPiProgram. -/
section P2MDyadicModule0

namespace AFT.RationalNumerics

open scoped BigOperators

noncomputable section

open scoped Classical

theorem arctan_term_bound (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- On the two actual rational inputs, absolute geometric majorization
bounds the entire remaining series, including its alternating signs. -/
theorem arctanSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
    |(arctanSum value terms : ℝ)-Real.arctan value| ≤ (1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  let term := fun index : ℕ => (-1 : ℝ)^index*(value : ℝ)^(2*index+1)/(2*index+1 : ℕ)
  have hseries : HasSum term (Real.arctan value) := Real.hasSum_arctan (by
    rw [Real.norm_eq_abs,abs_of_nonneg hv0]
    linarith)
  have hsplit := hseries.summable.sum_add_tsum_nat_add terms
  rw [hseries.tsum_eq] at hsplit
  have hcast : (arctanSum value terms : ℝ)=∑ i∈Finset.range terms,term i := by
    unfold arctanSum term
    push_cast
    rfl
  have hgeom : Summable (fun i : ℕ => (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left _
  have hbound (i : ℕ) : ‖term (i+terms)‖ ≤ (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i := by
    have hh := arctan_term_bound (value : ℝ) hv0 hv1 (i+terms)
    rw [← pow_add]
    have hi : i+terms+1=terms+1+i := by omega
    simpa only [term,Real.norm_eq_abs,hi] using hh
  have htail := (summable_nat_add_iff terms).mpr hseries.summable
  have hnorm := htail.norm
  have hsum := (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hbound hnorm hgeom)
  have hgeomval : (∑' i : ℕ,(1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i)=(1/2 : ℝ)^terms := by
    have hh := ((hasSum_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left
      ((1/2 : ℝ)^(terms+1))).tsum_eq
    calc
      _ = (1/2 : ℝ)^(terms+1)*2 := by
        simpa only [show ((1 : ℝ)-1/2)⁻¹=2 by norm_num] using hh
      _ = _ := by rw [pow_succ]; ring
  rw [hgeomval,Real.norm_eq_abs] at hsum
  rw [hcast,abs_sub_comm,show Real.arctan (value : ℝ)-(∑ i∈Finset.range terms,term i)=
    ∑' i,term (i+terms) by linarith]
  exact hsum

/-- `bits+3` terms of each short series give the requested binary accuracy. -/
theorem piApprox_error (bits : ℕ) : |(piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := arctanSum_error (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := arctanSum_error (1/3) (by norm_num) (by norm_num) (bits+3)
  have hid : Real.pi=4*(Real.arctan (1/2)+Real.arctan (1/3)) := by
    have hh := Real.arctan_inv_2_add_arctan_inv_3
    norm_num only [one_div] at ⊢
    linarith
  have he : (piApprox bits : ℝ)-Real.pi=4*((arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)+
      ((arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3))) := by
    rw [hid]
    simp only [piApprox,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4*(|(arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)|+
        |(arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 4*((1/2 : ℝ)^(bits+3)+(1/2 : ℝ)^(bits+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using add_le_add h1 h2
    _ = _ := by rw [pow_add,div_pow,one_pow]; norm_num; ring

end

end AFT.RationalNumerics

end P2MDyadicModule0

/- Helper module AFT.RationalExpProgram. -/
section P2MDyadicModule1

namespace AFT.RationalNumerics

open scoped BigOperators

noncomputable section

open scoped Classical

theorem expSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2)
    (terms : ℕ) (ht : 0 < terms) :
    |(expSum value terms : ℝ)-Real.exp value| ≤ 2*(1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  have hterm : (1 : ℝ) ≤ terms := by exact_mod_cast ht
  have hfactorial : (1 : ℝ) ≤ terms.factorial := by exact_mod_cast Nat.factorial_pos terms
  have hden : (0 : ℝ) < (terms.factorial : ℝ)*terms := by positivity
  have hquot : ((terms+1 : ℕ) : ℝ)/((terms.factorial : ℝ)*terms) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith
  have hh := Real.exp_bound (x := (value : ℝ)) (by rw [abs_of_nonneg hv0]; linarith) ht
  have he : (expSum value terms : ℝ)=∑ i∈Finset.range terms,(value : ℝ)^i/(i.factorial : ℕ) := by
    unfold expSum
    push_cast
    rfl
  rw [he,abs_sub_comm]
  apply hh.trans
  rw [abs_of_nonneg hv0]
  exact (mul_le_mul (pow_le_pow_left₀ hv0 hv1 terms) hquot (by positivity) (by positivity)).trans_eq (mul_comm _ _)

/-- Taking reciprocals of quantities at least one has Lipschitz constant
one; it avoids amplification by an exponentially large positive exponential. -/
theorem inv_error_of_ge_one (first second : ℝ) (hf : 1 ≤ first) (hs : 1 ≤ second) :
    |first⁻¹-second⁻¹| ≤ |first-second| := by
  have hfirst : first ≠ 0 := by linarith
  have hsecond : second ≠ 0 := by linarith
  have he : first⁻¹-second⁻¹=(second-first)/(first*second) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ first*second)]
  exact div_le_self (abs_nonneg _) (by nlinarith)

theorem power_error_unit_interval (first second : ℝ)
    (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1) (count : ℕ) :
    |first^count-second^count| ≤ (count : ℝ)*|first-second| := by
  have hh := abs_pow_sub_pow_le first second count
  rw [abs_of_nonneg hf.1,abs_of_nonneg hs.1] at hh
  have hp : max first second^(count-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hf.1) (max_le hf.2 hs.2)
  calc
    _ ≤ |first-second| *count*max first second^(count-1) := hh
    _ ≤ |first-second| *count*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- A polynomial range reduction parameter is sufficient for any requested
number of binary digits. The approximation remains positive and bounded. -/
theorem expNegScaled_error (argument : ℚ) (scale bits : ℕ)
    (ha : 0 ≤ argument) (hscale : 0 < scale) (hbound : 2*argument ≤ (scale : ℚ)) :
    |(expNegScaled argument scale bits : ℝ)-Real.exp (-(argument : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let value : ℚ := argument/(scale : ℚ)
  let terms := bits+scale+1
  have hs0 : (0 : ℚ) < scale := by exact_mod_cast hscale
  have hv0 : 0 ≤ value := div_nonneg ha hs0.le
  have hv1 : value ≤ 1/2 := by
    apply (div_le_iff₀ hs0).mpr
    linarith
  have ht : 0 < terms := by dsimp [terms]; omega
  have hfirst := expSum_ge_one value hv0 terms ht
  have hsecond : (1 : ℝ) ≤ Real.exp (value : ℝ) := Real.one_le_exp_iff.mpr (by exact_mod_cast hv0)
  have hpi := power_error_unit_interval ((expSum value terms : ℝ)⁻¹) ((Real.exp (value : ℝ))⁻¹)
    ⟨by positivity,inv_le_one_of_one_le₀ hfirst⟩ ⟨by positivity,inv_le_one_of_one_le₀ hsecond⟩ scale
  have hi := inv_error_of_ge_one (expSum value terms) (Real.exp (value : ℝ)) hfirst hsecond
  have happrox := (hpi.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg scale))).trans
    (mul_le_mul_of_nonneg_left (expSum_error value hv0 hv1 terms ht) (Nat.cast_nonneg scale))
  have hexp : (Real.exp (value : ℝ))⁻¹^scale=Real.exp (-(argument : ℝ)) := by
    rw [← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    dsimp [value]
    push_cast
    field_simp
  have hprogram : (expNegScaled argument scale bits : ℝ)=(expSum value terms : ℝ)⁻¹^scale := by
    simp only [expNegScaled,value,terms,Rat.cast_pow,Rat.cast_inv]
  rw [hprogram,← hexp]
  apply happrox.trans
  have hsbound : (scale : ℝ) ≤ (2 : ℝ)^scale := by exact_mod_cast (Nat.lt_two_pow_self (n:=scale)).le
  calc
    _ ≤ (2 : ℝ)^scale*(2*(1/2 : ℝ)^terms) := mul_le_mul_of_nonneg_right hsbound (by positivity)
    _ = _ := by
      dsimp [terms]
      rw [pow_add,pow_add,div_pow,one_pow,div_pow,one_pow]
      field_simp

theorem expNegApprox_error (argument : ℚ) (bits : ℕ) :
    |(expNegApprox argument bits : ℝ)-Real.exp (-max (argument : ℝ) 0)| ≤ 1/(2 : ℝ)^bits := by
  have hb : 2*max argument 0 ≤ (expScale argument : ℚ) := by
    have hh := Nat.le_ceil (max argument 0)
    simp only [expScale,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hh := expNegScaled_error (max argument 0) (expScale argument) bits
    (le_max_right _ _) (expScale_positive argument) hb
  simpa only [expNegApprox,Rat.cast_max,Rat.cast_zero] using hh

/-- On nonnegative arguments the negative exponential is globally
one-Lipschitz. This controls the separate rational argument approximation. -/
theorem exp_neg_lipschitz (first second : ℝ) (hf : 0 ≤ first) (hs : 0 ≤ second) :
    |Real.exp (-first)-Real.exp (-second)| ≤ |first-second| := by
  have ordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Real.exp (-a)-Real.exp (-b) ≤ b-a := by
    have he := Real.add_one_le_exp (a-b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have heq : Real.exp (-a)*Real.exp (a-b)=Real.exp (-b) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hm
    have hl : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total first second with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := ordered first second hf h
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := ordered second first hs h
    linarith

end

end AFT.RationalNumerics

end P2MDyadicModule1

/- Helper module AFT.RationalGaussianProgram. -/
section P2MDyadicModule2

namespace AFT.RationalNumerics

noncomputable section

/-- The finite pi and exponential programs together approximate the actual
Gaussian exponential; all precision guard digits are computed rationally. -/
theorem gaussianApprox_error (squaredWidth : ℚ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) :
    |(gaussianApprox squaredWidth point bits : ℝ)-
      Real.exp (-Real.pi*(point : ℝ)^2/(squaredWidth : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let ratio := gaussianRatio squaredWidth point
  let guard := gaussianGuard squaredWidth point
  let argument := piApprox (bits+guard+1)*ratio
  have hr0 : (0 : ℚ) ≤ ratio := div_nonneg (sq_nonneg _) hwidth.le
  have hr : (0 : ℝ) ≤ ratio := by exact_mod_cast hr0
  have hguard : (ratio : ℝ) ≤ (guard : ℝ) := by exact_mod_cast Nat.le_ceil ratio
  have hguardpow : (guard : ℝ) ≤ (2 : ℝ)^guard := by exact_mod_cast (Nat.lt_two_pow_self (n:=guard)).le
  have hpi := piApprox_error (bits+guard+1)
  have harg : |(argument : ℝ)-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have he : (argument : ℝ)-Real.pi*(ratio : ℝ)=((piApprox (bits+guard+1) : ℝ)-Real.pi)*(ratio : ℝ) := by
      dsimp [argument]
      push_cast
      ring
    rw [he,abs_mul,abs_of_nonneg hr]
    calc
      _ ≤ (1/(2 : ℝ)^(bits+guard+1))*(2 : ℝ)^guard :=
        mul_le_mul hpi (hguard.trans hguardpow) hr (by positivity)
      _ = _ := by rw [pow_add,pow_add,pow_add]; field_simp
  have ht : 0 ≤ Real.pi*(ratio : ℝ) := mul_nonneg Real.pi_pos.le hr
  have hclip : |max (argument : ℝ) 0-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have hh := abs_max_sub_max_le_abs (argument : ℝ) (Real.pi*(ratio : ℝ)) 0
    rw [max_eq_left ht] at hh
    exact hh.trans harg
  have he := expNegApprox_error argument (bits+1)
  have hl := exp_neg_lipschitz (max (argument : ℝ) 0) (Real.pi*(ratio : ℝ)) (le_max_right _ _) ht
  have htarget : -Real.pi*(point : ℝ)^2/(squaredWidth : ℝ) = -(Real.pi*(ratio : ℝ)) := by
    dsimp [ratio,gaussianRatio]
    push_cast
    ring
  rw [htarget]
  calc
    _ ≤ |(expNegApprox argument (bits+1) : ℝ)-Real.exp (-max (argument : ℝ) 0)|+
        |Real.exp (-max (argument : ℝ) 0)-Real.exp (-(Real.pi*(ratio : ℝ)))| := abs_sub_le _ _ _
    _ ≤ 1/(2 : ℝ)^(bits+1)+1/(2 : ℝ)^(bits+1) := add_le_add he (hl.trans hclip)
    _ = _ := by rw [pow_succ]; field_simp; norm_num

end

end AFT.RationalNumerics

end P2MDyadicModule2

/- Helper module AFT.GaussianConvolution. -/
section P2MDyadicModule3

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

end P2MDyadicModule3

/- Helper module AFT.CenteredGaussianProgram. -/
section P2MDyadicModule4

namespace AFT.RationalNumerics

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem centeredGaussianSquaredWidth_pos (squaredWidth center : ℚ) (hw : 0<squaredWidth) :
    0<centeredGaussianSquaredWidth squaredWidth center := by
  unfold centeredGaussianSquaredWidth
  have hd : (0 : ℚ)<center.den := by exact_mod_cast center.den_pos
  positivity

theorem centeredGaussianRatio (squaredWidth center : ℚ) (point : ℤ) :
    (gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center point) : ℝ)=
      ((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ) := by
  have hd : (center.den : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt center.den_pos)
  have hc : (center : ℝ)=(center.num : ℝ)/(center.den : ℝ) := Rat.cast_def center
  unfold gaussianRatio centeredGaussianSquaredWidth centeredGaussianNumerator
  push_cast
  rw [hc]
  field_simp

/-- The error is uniform in the center and integer point. All guard
precision in the pi and exponential programs is computed rationally. -/
theorem centeredGaussianApprox_error (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ)
    (hw : 0<squaredWidth) :
    |(centeredGaussianApprox squaredWidth center point bits : ℝ)-
      Real.exp (-Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ))|≤1/(2 : ℝ)^bits := by
  have hh := gaussianApprox_error (centeredGaussianSquaredWidth squaredWidth center)
    (centeredGaussianNumerator center point) bits (centeredGaussianSquaredWidth_pos squaredWidth center hw)
  have he : -Real.pi*(centeredGaussianNumerator center point : ℝ)^2 /
      (centeredGaussianSquaredWidth squaredWidth center : ℝ)=
      -Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ) := by
    have hr := centeredGaussianRatio squaredWidth center point
    simp only [gaussianRatio,Rat.cast_div,Rat.cast_pow,Rat.cast_intCast] at hr
    calc
      _ = -Real.pi*((centeredGaussianNumerator center point : ℝ)^2 /
          (centeredGaussianSquaredWidth squaredWidth center : ℝ)) := by ring
      _ = -Real.pi*(((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ)) := congrArg (-Real.pi*·) hr
      _ = _ := by ring
  rw [he] at hh
  exact hh

theorem centeredGaussianAnchor_bounds (center : ℚ) :
    (centeredGaussianAnchor center : ℝ)≤(center : ℝ) ∧
      (center : ℝ)<(centeredGaussianAnchor center : ℝ)+1 := by
  constructor
  · exact_mod_cast (Int.floor_le center)
  · exact_mod_cast (Int.lt_floor_add_one center)

end

end AFT.RationalNumerics

end P2MDyadicModule4

/- Helper module AFT.CenteredGaussianResources. -/
section P2MDyadicModule5

namespace AFT.RationalNumerics

open GaussianSource FiniteConvolutionProgram

open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

set_option maxRecDepth 2048

theorem centeredGaussianRatio_rat (squaredWidth center : ℚ) (point : ℤ) :
    gaussianRatio (centeredGaussianSquaredWidth squaredWidth center) (centeredGaussianNumerator center point)=
      ((point : ℚ)-center)^2/squaredWidth := by
  exact_mod_cast centeredGaussianRatio squaredWidth center point

end

end AFT.RationalNumerics

end P2MDyadicModule5

/- Helper module AFT.RationalAcceptanceCoin. -/
section P2MDyadicModule6

namespace AFT.RationalAcceptanceCoin

open scoped BigOperators

noncomputable section

/-- Clipping does not amplify error against any legal target probability. -/
theorem clipped_error (value : ℚ) (target : ℝ) (ht : 0 ≤ target ∧ target ≤ 1) :
    |(clipped value : ℝ)-target| ≤ |(value : ℝ)-target| := by
  have he : (clipped value : ℝ)=min 1 (max (value : ℝ) 0) := by
    simp [clipped]
  rw [he]
  by_cases hv : (value : ℝ) ≤ 0
  · rw [max_eq_right hv,min_eq_right (by norm_num : (0 : ℝ) ≤ 1),zero_sub,abs_neg,
      abs_of_nonneg ht.1,abs_of_nonpos (by linarith : (value : ℝ)-target ≤ 0)]
    linarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ value)]
    by_cases hv1 : (value : ℝ) ≤ 1
    · rw [min_eq_right hv1]
    · rw [min_eq_left (by linarith : (1 : ℝ) ≤ value),
        abs_of_nonneg (by linarith : 0 ≤ (1 : ℝ)-target),
        abs_of_nonneg (by linarith : 0 ≤ (value : ℝ)-target)]
      linarith

end

end AFT.RationalAcceptanceCoin

end P2MDyadicModule6

/- Helper module Integration9_9.TM2NativeFiniteDraw. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativeFiniteDraw

open AFT AFT.RationalNumerics AFT.BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2NativeFiniteSeries TM2NativeRootGroupProfiles

open scoped BigOperators

theorem clipped_eq (q : ℚ) : clipped q=RationalAcceptanceCoin.clipped q := by
  unfold clipped RationalAcceptanceCoin.clipped
  split_ifs with h0 h1
  · rw [max_eq_right h0.le,min_eq_right (by norm_num)]
  · rw [max_eq_left (le_of_not_gt h0),min_eq_right h1.le]
  · rw [max_eq_left (le_of_not_gt h0),min_eq_left (le_of_not_gt h1)]

end Integration9_9.TM2NativeFiniteDraw

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeFiniteGateTransport. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity

def oneWire {n : ℕ} (i : Fin n) : Fin 1 ↪ Fin n where
  toFun _ := i
  inj' _ _ _ := Subsingleton.elim _ _

theorem oneWire_range {n : ℕ} (i : Fin n) : Set.range (oneWire i)={i} := by
  ext a
  simp only [Set.mem_range,oneWire,Set.mem_singleton_iff]
  constructor
  · rintro ⟨_,rfl⟩;rfl
  · intro h;exact ⟨0,h.symm⟩

theorem off_oneWire_iff {n : ℕ} (i : Fin n) (y z : Bits n) :
    (∀ a, a ∉ Set.range (oneWire i) → y a=z a) ↔ z=Function.update y i (z i) := by
  rw [oneWire_range]
  constructor
  · intro h;funext a
    by_cases ha : a=i
    · subst a;simp
    · simp only [Function.update_of_ne ha];exact (h a ha).symm
  · intro h a ha
    have hai : a≠i := ha
    rw [h,Function.update_of_ne hai]

theorem embed_oneWire_entry {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (y z : Bits n) :
    embedOp (Gate.ofMatrix1 U).mat (oneWire i) y z =
      ∑ b : Bool, if z=Function.update y i b then U (y i) b else 0 := by
  classical
  have hsum : (∑ b : Bool, if z=Function.update y i b then U (y i) b else 0) =
      if z=Function.update y i (z i) then U (y i) (z i) else 0 := by
    apply Finset.sum_eq_single (z i)
    · intro b _ hne
      have hnot : z≠Function.update y i b := by
        intro h
        have hb := congrFun h i
        simp only [Function.update_self] at hb
        exact hne hb.symm
      simp only [if_neg hnot]
    · simp
  rw [hsum]
  change (if ∀ a, a ∉ Set.range (oneWire i) → y a=z a then U (y i) (z i) else 0)=_
  simp only [off_oneWire_iff]

theorem embed_oneWire_mulVec {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    (embedOp (Gate.ofMatrix1 U).mat (oneWire i)).mulVec ψ = apply1 U i ψ := by
  classical
  funext y
  simp only [Matrix.mulVec, dotProduct,embed_oneWire_entry,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem twoWire_range {n : ℕ} (w : Fin 2 ↪ Fin n) : Set.range w={w 0,w 1} := by
  ext a
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨j,rfl⟩;fin_cases j <;> simp
  · rintro (h|h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩

theorem cnot_condition {n : ℕ} (w : Fin 2 ↪ Fin n) (y z : Bits n) :
    ((∀ a, a ∉ Set.range w → y a=z a) ∧
      y (w 0)=z (w 0) ∧ y (w 1)=xor (z (w 1)) (z (w 0))) ↔
      z=Function.update y (w 1) (xor (y (w 1)) (y (w 0))) := by
  have hw : w 0 ≠ w 1 := w.injective.ne (by decide)
  constructor
  · rintro ⟨hoff,hzero,hone⟩
    funext a
    by_cases h1 : a=w 1
    · subst a
      simp only [Function.update_self,hone,hzero,Bool.xor_assoc,Bool.xor_self,Bool.xor_false]
    · by_cases h0 : a=w 0
      · subst a;simp only [Function.update_of_ne hw];exact hzero.symm
      · rw [Function.update_of_ne h1]
        exact (hoff a (by rw [twoWire_range];simpa using And.intro h0 h1)).symm
  · intro h
    subst z
    refine ⟨?_,?_,?_⟩
    · intro a ha
      have h1 : a≠w 1 := by intro hh;apply ha;exact ⟨1,hh.symm⟩
      rw [Function.update_of_ne h1]
    · rw [Function.update_of_ne hw]
    · simp only [Function.update_self,Function.update_of_ne hw,
        Bool.xor_assoc,Bool.xor_self,Bool.xor_false]

theorem embed_cnot_entry {n : ℕ} (w : Fin 2 ↪ Fin n) (y z : Bits n) :
    embedOp (Gate.ofMatrix2 cnot).mat w y z =
      if z=Function.update y (w 1) (xor (y (w 1)) (y (w 0))) then 1 else 0 := by
  classical
  change (if (∀ a, a ∉ Set.range w → y a=z a) then
    (if y (w 0)=z (w 0) ∧ y (w 1)=xor (z (w 1)) (z (w 0)) then (1 : ℂ) else 0) else 0)=_
  simp only [←ite_and,cnot_condition]

theorem embed_cnot_mulVec {n : ℕ} (w : Fin 2 ↪ Fin n) (ψ : QState n) :
    (embedOp (Gate.ofMatrix2 cnot).mat w).mulVec ψ =
      cnotState (w 0) (w 1) (w.injective.ne (by decide)) ψ := by
  classical
  funext y
  simp only [Matrix.mulVec,dotProduct,embed_cnot_entry,ite_mul,zero_mul,one_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,cnotState]

def twoWire {n : ℕ} (i j : Fin n) (hij : i≠j) : Fin 2 ↪ Fin n where
  toFun k := if k=0 then i else j
  inj' a b h := by
    fin_cases a <;> fin_cases b <;> simp_all

noncomputable def Letter.toGate {n : ℕ} : Letter n → GateApp htcxGateSet n
  | .h i => ⟨Gate.ofMatrix1 hadamard,Or.inl rfl,oneWire i⟩
  | .t i => ⟨Gate.ofMatrix1 gateT,Or.inr (Or.inl rfl),oneWire i⟩
  | .cnot i j hij => ⟨Gate.ofMatrix2 QAlgorithms.cnot,Or.inr (Or.inr rfl),twoWire i j hij⟩

theorem embedding_one {n : ℕ} (w : Fin 1 ↪ Fin n) : oneWire (w 0)=w := by
  ext a;have ha : a=0 := Subsingleton.elim _ _;subst a;rfl

theorem embedding_two {n : ℕ} (w : Fin 2 ↪ Fin n) :
    twoWire (w 0) (w 1) (w.injective.ne (by decide))=w := by
  apply Function.Embedding.ext
  intro a;fin_cases a <;> rfl

theorem Letter.toGate_surjective {n : ℕ} : Function.Surjective (@Letter.toGate n) := by
  intro ⟨g,hmem,w⟩
  rcases hmem with hg|hg|hg
  · subst g
    change Fin 1 ↪ Fin n at w
    refine ⟨.h (w 0),?_⟩
    simp only [Letter.toGate,embedding_one]
  · subst g
    change Fin 1 ↪ Fin n at w
    refine ⟨.t (w 0),?_⟩
    simp only [Letter.toGate,embedding_one]
  · subst g
    change Fin 2 ↪ Fin n at w
    refine ⟨.cnot (w 0) (w 1) (w.injective.ne (by decide)),?_⟩
    simp only [Letter.toGate,embedding_two]

theorem hadamard_eq_hMat : hadamard=hMat := by
  ext a b
  simp only [hadamard,hMat,Matrix.of_apply,Complex.ofReal_inv]

theorem gateT_eq_tMat : gateT=tMat := by
  ext a b
  simp only [gateT,tMat,Matrix.diagonal_apply,Matrix.of_apply]

theorem Letter.mulVec_eq {n : ℕ} (a : Letter n) (ψ : QState n) :
    (embedOp a.toGate.gate.mat a.toGate.wires).mulVec ψ=a.toInstr.apply ψ := by
  cases a with
  | h i => simpa only [Letter.toGate,Letter.toInstr,Instr.apply,hadamard_eq_hMat] using
      embed_oneWire_mulVec hadamard i ψ
  | t i => simpa only [Letter.toGate,Letter.toInstr,Instr.apply,gateT_eq_tMat] using
      embed_oneWire_mulVec gateT i ψ
  | cnot i j hij =>
      have h := embed_cnot_mulVec (twoWire i j hij) ψ
      change (embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (twoWire i j hij)).mulVec ψ =
        cnotState i j hij ψ
      exact h

noncomputable def matrix {n : ℕ} (word : List (Letter n)) : Matrix (Bits n) (Bits n) ℂ :=
  Circuit.unitary (word.map Letter.toGate)

theorem matrix_mulVec {n : ℕ} (word : List (Letter n)) (ψ : QState n) :
    (matrix word).mulVec ψ=runLayer (instructions word) ψ := by
  induction word generalizing ψ with
  | nil => simp [matrix,Circuit.unitary,instructions,runLayer]
  | cons a rest ih =>
    have hmatrix : matrix (a::rest)=matrix rest*embedOp a.toGate.gate.mat a.toGate.wires := by
      simp [matrix,Circuit.unitary,List.reverse_cons,List.prod_append]
    rw [hmatrix,←Matrix.mulVec_mulVec,Letter.mulVec_eq,ih]
    rfl

theorem exists_word {n : ℕ} (c : Circuit htcxGateSet n) :
    ∃ word : List (Letter n), word.map Letter.toGate=c := by
  induction c with
  | nil => exact ⟨[],rfl⟩
  | cons g rest ih =>
    obtain ⟨a,ha⟩ := Letter.toGate_surjective g
    obtain ⟨word,hw⟩ := ih
    exact ⟨a::word,by simp only [List.map_cons,ha,hw]⟩

/-- The approximation theorem now ranges over an explicit finite instruction alphabet.
This is an existence and semantics statement; it does not yet assert an efficient search. -/
theorem exists_approximation :
    ∃ A : ℝ, 0<A ∧ ∀ U : Matrix (Qubits 1) (Qubits 1) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits 1) ℂ →
      ∀ ε : ℝ, 0<ε → ε≤1 →
      ∃ word : List (Letter 3),
        QAlgorithms.frobNorm
          (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (matrix word)-
           QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2)≤ε ∧
        (word.length : ℝ)≤A*(Real.log (1/ε)/Real.log 2+1) := by
  obtain ⟨A,hA,happrox⟩ := CliffordTApprox.Ancilla.main_result
  refine ⟨A,hA,?_⟩
  intro U hU ε hε hεone
  obtain ⟨c,herror,hsize⟩ := happrox U hU ε hε hεone
  obtain ⟨word,hw⟩ := exists_word c
  refine ⟨word,?_,?_⟩
  · simpa only [matrix,hw] using herror
  · simpa only [←hw,Circuit.size,List.length_map] using hsize

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeFiniteGateError. -/
section P2MDyadicModule9
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms

open scoped BigOperators

private theorem frobNorm_column {n : Type*} [Fintype n] (ψ : n → ℂ) :
    frobNorm ((fun i (_ : Unit) => ψ i) : Matrix n Unit ℂ)=‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ n)‖ := by
  simpa only [frobNorm,Fintype.sum_unique,EuclideanSpace.norm_eq,
    Real.sqrt_eq_rpow,Real.rpow_two] using
      (Matrix.frobenius_norm_def ((fun i (_ : Unit) => ψ i) : Matrix n Unit ℂ))

/-- The initialized-map Frobenius error controls the error on every input vector. -/
theorem mulVec_error_bound {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (ψ : n → ℂ) :
    ‖(WithLp.toLp 2 (A.mulVec ψ) : EuclideanSpace ℂ m)‖ ≤
      frobNorm A*‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ n)‖ := by
  let column : Matrix n Unit ℂ := fun i _ => ψ i
  have h := Matrix.frobenius_norm_mul A column
  change frobNorm (A*column)≤frobNorm A*frobNorm column at h
  have hcol : A*column=((fun i (_ : Unit) => A.mulVec ψ i) : Matrix m Unit ℂ) := rfl
  rw [hcol,frobNorm_column] at h
  change _≤frobNorm A*frobNorm ((fun i (_ : Unit) => ψ i) : Matrix n Unit ℂ) at h
  rw [frobNorm_column] at h
  exact h

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeFiniteGateEntangledError. -/
section P2MDyadicModule10
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms

open scoped BigOperators

/-- Apply a rectangular map on one register, keeping the arbitrary reference
register. No product-state assumption is imposed. -/
noncomputable def applyWithReference {m n r : Type*} [Fintype n]
    (A : Matrix m n ℂ) (ψ : n × r → ℂ) : m × r → ℂ :=
  fun pair => A.mulVec (fun j => ψ (j,pair.2)) pair.1

theorem norm_sq_slices {n r : Type*} [Fintype n] [Fintype r]
    (ψ : n × r → ℂ) :
    ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (n×r))‖^2 =
      ∑ k : r, ‖(WithLp.toLp 2 (fun j => ψ (j,k)) : EuclideanSpace ℂ n)‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Frobenius error remains a state error bound in the presence of an arbitrary
entangled reference register, with no dimension-dependent loss. -/
theorem applyWithReference_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    (A : Matrix m n ℂ) (ψ : n×r → ℂ) :
    ‖(WithLp.toLp 2 (applyWithReference A ψ) : EuclideanSpace ℂ (m×r))‖ ≤
      frobNorm A*‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (n×r))‖ := by
  have ha : 0≤frobNorm A := by change 0≤‖A‖;exact norm_nonneg A
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp
  rw [mul_pow,norm_sq_slices,norm_sq_slices,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hk := mulVec_error_bound A (fun j => ψ (j,k))
  have hp := pow_le_pow_left₀ (norm_nonneg _) hk 2
  simpa only [mul_pow,applyWithReference] using hp

theorem applyWithReference_sub {m n r : Type*} [Fintype n]
    (A B : Matrix m n ℂ) (ψ : n×r → ℂ) :
    applyWithReference (A-B) ψ=applyWithReference A ψ-applyWithReference B ψ := by
  funext x
  simp only [applyWithReference,Matrix.sub_mulVec,Pi.sub_apply]

/-- The local initialized-map guarantee controls the actual state difference
for every external entangled state. Ancilla output rows remain present. -/
theorem applyWithReference_error {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    (A B : Matrix m n ℂ) (ε : ℝ) (h : frobNorm (A-B)≤ε) (ψ : n×r → ℂ) :
    ‖(WithLp.toLp 2 (applyWithReference A ψ-applyWithReference B ψ) : EuclideanSpace ℂ (m×r))‖ ≤
      ε*‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (n×r))‖ := by
  rw [←applyWithReference_sub]
  exact (applyWithReference_bound (A-B) ψ).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg _))

end InfoLossLAR.WorstCase.FiniteGateTransport

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

@[simp] theorem wireBitsEquiv_fst {k n : ℕ} (w : Fin k ↪ Fin n) (y : Bits n) :
    (wireBitsEquiv w y).1=y ∘ w := rfl

/-- Pulling an embedded operator into selected/reference coordinates exposes
exactly the identity on the reference register. -/
theorem embedOp_split_entry {k n : ℕ} (w : Fin k ↪ Fin n)
    (M : Matrix (Bits k) (Bits k) ℂ) (y z : Bits n) :
    embedOp M w y z = if (wireBitsEquiv w y).2=(wireBitsEquiv w z).2
      then M (wireBitsEquiv w y).1 (wireBitsEquiv w z).1 else 0 := by
  have h : (∀ a : Fin n, a ∉ Set.range w → y a=z a) ↔
      (wireBitsEquiv w y).2=(wireBitsEquiv w z).2 := by
    constructor
    · intro h;funext a;exact h a a.property
    · intro h a ha;exact congrFun h ⟨a,ha⟩
  simp only [embedOp,Matrix.of_apply,h,wireBitsEquiv_fst]

/-- Actual whole-register matrix multiplication agrees with the local map
on every reference slice, including entangled states. -/
theorem embedOp_split_mulVec {k n : ℕ} (w : Fin k ↪ Fin n)
    (M : Matrix (Bits k) (Bits k) ℂ) (ψ : QState n) :
    splitState w ((embedOp M w).mulVec ψ)=applyWithReference M (splitState w ψ) := by
  classical
  funext p
  change (∑ z : Bits n,embedOp M w ((wireBitsEquiv w).symm p) z*ψ z)=_
  have hsum := Fintype.sum_equiv (wireBitsEquiv w)
    (fun z : Bits n => embedOp M w ((wireBitsEquiv w).symm p) z*ψ z)
    (fun q : Bits k × OutsideBits w =>
      (if p.2=q.2 then M p.1 q.1 else 0)*splitState w ψ q) (by
        intro z
        rw [embedOp_split_entry]
        simp only [Equiv.apply_symm_apply,splitState,Equiv.symm_apply_apply])
  rw [hsum,Fintype.sum_prod_type]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rfl

/-- Wire reindexing is an isometry for the Euclidean state norm. -/
theorem splitState_norm {k n : ℕ} (w : Fin k ↪ Fin n) (ψ : QState n) :
    ‖(WithLp.toLp 2 (splitState w ψ) : EuclideanSpace ℂ (Bits k × OutsideBits w))‖=
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits n))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,splitState]
  exact Fintype.sum_equiv (wireBitsEquiv w).symm _ _ (by intro p;rfl)

/-- Nested embeddings are exactly their composed physical-wire embedding. -/
theorem embedOp_embedOp {a k n : ℕ} (M : Matrix (Bits a) (Bits a) ℂ)
    (v : Fin a ↪ Fin k) (w : Fin k ↪ Fin n) :
    embedOp (embedOp M v) w=embedOp M (v.trans w) := by
  classical
  ext y z
  have h : ((∀ i : Fin n,i ∉ Set.range w → y i=z i) ∧
      (∀ j : Fin k,j ∉ Set.range v → y (w j)=z (w j))) ↔
      (∀ i : Fin n,i ∉ Set.range (v.trans w) → y i=z i) := by
    constructor
    · rintro ⟨hout,hin⟩ i hi
      by_cases hw : i ∈ Set.range w
      · obtain ⟨j,rfl⟩ := hw
        exact hin j (by rintro ⟨l,hl⟩;apply hi;exact ⟨l,congrArg w hl⟩)
      · exact hout i hw
    · intro hall
      constructor
      · intro i hi
        exact hall i (by rintro ⟨l,hl⟩;apply hi;exact ⟨v l,hl⟩)
      · intro j hj
        exact hall (w j) (by rintro ⟨l,hl⟩;apply hj;exact ⟨l,w.injective hl⟩)
  simp only [embedOp,Matrix.of_apply,Function.comp_apply,←ite_and,h]
  rfl

theorem Letter.relocate_embedded {k n : ℕ} (w : Fin k ↪ Fin n) (a : Letter k) :
    embedOp (embedOp a.toGate.gate.mat a.toGate.wires) w=
      embedOp (a.relocate w).toGate.gate.mat (a.relocate w).toGate.wires := by
  rw [embedOp_embedOp]
  cases a with
  | h i =>
    change embedOp (Gate.ofMatrix1 hadamard).mat ((oneWire i).trans w)=
      embedOp (Gate.ofMatrix1 hadamard).mat (oneWire (w i))
    congr 1
  | t i =>
    change embedOp (Gate.ofMatrix1 gateT).mat ((oneWire i).trans w)=
      embedOp (Gate.ofMatrix1 gateT).mat (oneWire (w i))
    congr 1
  | cnot i j hij =>
    change embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat ((twoWire i j hij).trans w)=
      embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (twoWire (w i) (w j) (w.injective.ne hij))
    congr 1
    ext z
    fin_cases z <;> rfl

/-- Every relocated physical instruction acts on the selected register and
leaves the complete external register untouched. -/
theorem Letter.relocate_split {k n : ℕ} (w : Fin k ↪ Fin n) (a : Letter k) (ψ : QState n) :
    splitState w ((a.relocate w).toInstr.apply ψ)=
      (fun p => a.toInstr.apply (fun b => splitState w ψ (b,p.2)) p.1) := by
  rw [←Letter.mulVec_eq,←Letter.relocate_embedded,embedOp_split_mulVec]
  funext p
  exact congrFun (Letter.mulVec_eq a (fun b => splitState w ψ (b,p.2))) p.1

/-- The entire relocated native word has exactly the intended local action,
with all spectator amplitudes and ancillary output amplitudes retained. -/
theorem relocate_word_split {k n : ℕ} (w : Fin k ↪ Fin n)
    (word : List (Letter k)) (ψ : QState n) :
    splitState w (runLayer (instructions (word.map (Letter.relocate w))) ψ)=
      applyWithReference (matrix word) (splitState w ψ) := by
  have h (word : List (Letter k)) (ψ : QState n) :
      splitState w (runLayer (instructions (word.map (Letter.relocate w))) ψ)=
        (fun p => runLayer (instructions word) (fun b => splitState w ψ (b,p.2)) p.1) := by
    induction word generalizing ψ with
    | nil => rfl
    | cons a rest ih =>
      change splitState w (runLayer (instructions (rest.map (Letter.relocate w)))
        ((a.relocate w).toInstr.apply ψ))=_
      rw [ih,Letter.relocate_split]
      rfl
  rw [h]
  funext p
  exact (congrFun (matrix_mulVec word (fun b => splitState w ψ (b,p.2))) p.1).symm

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeInverseCircuit. -/
section P2MDyadicModule12

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

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgeToffoli. -/
section P2MDyadicModule13

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

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
section P2MDyadicModule14

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

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule15

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

end P2MDyadicModule15

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule16

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

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeCircuitRelocation. -/
section P2MDyadicModule17

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

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeControlledPhase. -/
section P2MDyadicModule18

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity

def phaseMatrix (z : ℂ) : Matrix Bool Bool ℂ := Matrix.diagonal (fun bit => if bit then z else 1)

theorem phaseMatrix_apply {n : ℕ} (z : ℂ) (i : Fin n) (ψ : QState n) (y : Bits n) :
    apply1 (phaseMatrix z) i ψ y=(if y i then z else 1)*ψ y := by
  classical
  simp only [apply1,phaseMatrix,Matrix.diagonal_apply,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  simp

noncomputable def controlledPhase {n : ℕ} (z : ℂ) (i j : Fin n) (ψ : QState n) : QState n :=
  fun y => (if y i && y j then z else 1)*ψ y

/-- The exact controlled phase is built from three one-qubit phases and two
CNOTs. This algebraic identity is valid on the entire workspace state. -/
theorem controlledPhase_decomposition {n : ℕ} (z : ℂ) (hz : z≠0)
    (i j : Fin n) (hij : i≠j) (ψ : QState n) :
    cnotState i j hij (apply1 (phaseMatrix z⁻¹) j
      (cnotState i j hij (apply1 (phaseMatrix z) j (apply1 (phaseMatrix z) i ψ))))=
      controlledPhase (z^2) i j ψ := by
  funext y
  simp only [cnotState,phaseMatrix_apply,controlledPhase,Function.update_self,
    Function.update_of_ne hij,Function.update_idem,Bool.xor_assoc,Bool.xor_self,Bool.xor_false,
    Function.update_eq_self]
  cases hi : y i <;> cases hj : y j <;>
    simp [hi,hj,pow_two,mul_assoc,hz]

theorem diagonal_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (values : ι → ℂ) (hvalues : ∀ i, ‖values i‖=1) :
    Matrix.diagonal values∈Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  simp only [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    change values i * (starRingEnd ℂ) (values i)=1
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hvalues,one_pow,Complex.ofReal_one]
  · simp [Matrix.diagonal_apply,hij]

noncomputable def phaseValue (angle : ℝ) : ℂ := Complex.exp ((angle : ℂ)*Complex.I)

theorem phaseValue_norm (angle : ℝ) : ‖phaseValue angle‖=1 := by
  simp [phaseValue,Complex.norm_exp,Complex.mul_re]

theorem phaseValue_sq (angle : ℝ) : phaseValue angle^2=phaseValue (2*angle) := by
  rw [pow_two,phaseValue,←Complex.exp_add,phaseValue]
  congr 1
  push_cast
  ring

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgePhaseTarget. -/
section P2MDyadicModule19
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12

open scoped BigOperators

theorem frobNorm_square {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A^2=∑ i,∑ j,‖A i j‖^2 := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def,←Real.sqrt_eq_rpow,Real.sq_sqrt]
  · simp only [Real.rpow_two]
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))

theorem idealMap_frobNorm {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (w : ℕ) :
    frobNorm (idealMap U w)=frobNorm U := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change frobNorm (idealMap U w)^2=frobNorm U^2
  rw [frobNorm_square,frobNorm_square]
  have h := Fintype.sum_equiv (qubitsAppendEquiv n w)
    (fun y : Qubits (n+w) => ∑ x : Qubits n,‖idealMap U w y x‖^2)
    (fun p : Qubits n×Qubits w => ∑ x : Qubits n,
      ‖(if p.2=(fun _ => false) then U p.1 x else 0 : ℂ)‖^2) (by intro y;rfl)
  rw [h,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro data _
  have hh := Finset.sum_eq_single (fun _ : Fin w => false)
    (s:=Finset.univ)
    (f:=fun anc : Qubits w => ∑ x : Qubits n,
      ‖(if anc=(fun _ => false) then U data x else 0 : ℂ)‖^2)
    (by intro anc _ hanc;simp [hanc]) (by simp)
  simpa only [ite_true] using hh

theorem idealMap_sub {n : ℕ} (U V : Matrix (Qubits n) (Qubits n) ℂ) (w : ℕ) :
    idealMap (U-V) w=idealMap U w-idealMap V w := by
  ext y x
  simp only [idealMap,Matrix.of_apply,Matrix.sub_apply]
  split <;> simp_all

theorem idealMap_error {n : ℕ} (U V : Matrix (Qubits n) (Qubits n) ℂ) (w : ℕ) :
    frobNorm (idealMap U w-idealMap V w)=frobNorm (U-V) := by
  rw [←idealMap_sub,idealMap_frobNorm]

def oneBitEquiv : Qubits 1 ≃ Bool where
  toFun bits := bits 0
  invFun bit := fun _ => bit
  left_inv bits := by funext i;have hi : i=0 := Subsingleton.elim _ _;rw [hi]
  right_inv _ := rfl

noncomputable def phaseQubitMatrix (z : ℂ) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  (Gate.ofMatrix1 (phaseMatrix z)).mat

theorem phaseQubitMatrix_diagonal (z : ℂ) : phaseQubitMatrix z=
    Matrix.diagonal (fun x : Qubits 1 => if x 0 then z else 1) := by
  classical
  ext x y
  have heq : (x 0=y 0) ↔ x=y := ⟨fun h => oneBitEquiv.injective h,fun h => congrFun h 0⟩
  simp only [phaseQubitMatrix,Gate.ofMatrix1,phaseMatrix,Matrix.submatrix_apply,Matrix.diagonal_apply,heq]

theorem phaseQubitMatrix_unitary (z : ℂ) (hz : ‖z‖=1) :
    phaseQubitMatrix z∈Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [phaseQubitMatrix_diagonal]
  apply diagonal_unitary
  intro x
  split <;> simp_all

theorem phaseQubitMatrix_error (z v : ℂ) :
    frobNorm (phaseQubitMatrix z-phaseQubitMatrix v)=‖z-v‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change frobNorm (phaseQubitMatrix z-phaseQubitMatrix v)^2=‖z-v‖^2
  rw [frobNorm_square,phaseQubitMatrix_diagonal,phaseQubitMatrix_diagonal]
  have hrow (x : Qubits 1) :
      (∑ y : Qubits 1, ‖(Matrix.diagonal (fun b : Qubits 1 => if b 0 then z else 1)-
        Matrix.diagonal (fun b : Qubits 1 => if b 0 then v else 1)) x y‖^2)=
      ‖(if x 0 then z else 1)-(if x 0 then v else 1)‖^2 := by
    have hh := Finset.sum_eq_single x (s:=Finset.univ)
      (f:=fun y : Qubits 1 => ‖(Matrix.diagonal (fun b : Qubits 1 => if b 0 then z else 1)-
        Matrix.diagonal (fun b : Qubits 1 => if b 0 then v else 1)) x y‖^2)
      (by intro y _ hy;simp [Matrix.sub_apply,Matrix.diagonal_apply,Ne.symm hy]) (by simp)
    simpa only [Matrix.sub_apply,Matrix.diagonal_apply_eq] using hh
  simp_rw [hrow]
  have h := Fintype.sum_equiv oneBitEquiv
    (fun x : Qubits 1 => ‖(if x 0 then z else 1)-(if x 0 then v else 1)‖^2)
    (fun bit : Bool => ‖(if bit then z else 1)-(if bit then v else 1)‖^2) (by intro x;rfl)
  rw [h]
  simp [Fintype.sum_bool]

theorem initialized_phase_error (z v : ℂ) (w : ℕ) :
    frobNorm (idealMap (phaseQubitMatrix z) w-idealMap (phaseQubitMatrix v) w)=‖z-v‖ := by
  rw [idealMap_error,phaseQubitMatrix_error]

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeInitializedRelocation. -/
section P2MDyadicModule20

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity QAlgorithms.Papers.Independent.Renew46.P12

open scoped BigOperators

/-- Initialize only the selected local ancillas. The input may be arbitrarily
entangled with every external wire. -/
noncomputable def initWithReference {k r : ℕ} {R : Type*}
    (ψ : Bits k × R → ℂ) : Bits (k+r) × R → ℂ :=
  fun p => if (qubitsAppendEquiv k r p.1).2=(fun _ => false)
    then ψ ((qubitsAppendEquiv k r p.1).1,p.2) else 0

theorem initWithReference_norm {k r : ℕ} {R : Type*} [Fintype R]
    (ψ : Bits k × R → ℂ) :
    ‖(WithLp.toLp 2 (initWithReference (r:=r) ψ) : EuclideanSpace ℂ (Bits (k+r)×R))‖=
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits k×R))‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_slices,norm_sq_slices]
  apply Finset.sum_congr rfl
  intro outside _
  simp only [EuclideanSpace.norm_sq_eq,initWithReference]
  have h := Fintype.sum_equiv (qubitsAppendEquiv k r)
    (fun y : Bits (k+r) => ‖(if (qubitsAppendEquiv k r y).2=(fun _ => false)
      then ψ ((qubitsAppendEquiv k r y).1,outside) else 0 : ℂ)‖^2)
    (fun p : Bits k×Bits r => ‖(if p.2=(fun _ => false) then ψ (p.1,outside) else 0 : ℂ)‖^2)
    (by intro y;rfl)
  rw [h,Fintype.sum_prod_type]
  simp only [ite_apply,Pi.zero_apply,apply_ite,norm_zero,zero_pow (by decide : 2≠0)]
  simp

/-- The initialized rectangular map is the actual matrix action on zero
local ancillas, with all ancillary output rows kept. -/
theorem applyWithReference_initialized {k r : ℕ} {R : Type*}
    (M : Matrix (Bits (k+r)) (Bits (k+r)) ℂ) (ψ : Bits k×R → ℂ) :
    applyWithReference M (initWithReference (r:=r) ψ)=
      applyWithReference (initializedMap (n:=k) (w:=r) M) ψ := by
  classical
  funext p
  change (∑ y : Bits (k+r),M p.1 y*initWithReference ψ (y,p.2))=_
  have h := Fintype.sum_equiv (qubitsAppendEquiv k r)
    (fun y : Bits (k+r) => M p.1 y*initWithReference ψ (y,p.2))
    (fun q : Bits k×Bits r => M p.1 (Fin.append q.1 q.2)*
      if q.2=(fun _ => false) then ψ (q.1,p.2) else 0) (by
        intro y
        simp only [initWithReference]
        have hy := (qubitsAppendEquiv k r).symm_apply_apply y
        change Fin.append (qubitsAppendEquiv k r y).1 (qubitsAppendEquiv k r y).2=y at hy
        rw [hy])
  rw [h,Fintype.sum_prod_type]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rfl

/-- Reassemble the physical register after selecting local and spectator wires. -/
noncomputable def unsplitState {k n : ℕ} (w : Fin k ↪ Fin n)
    (ψ : Bits k × OutsideBits w → ℂ) : QState n := fun x => ψ (wireBitsEquiv w x)

@[simp] theorem split_unsplit {k n : ℕ} (w : Fin k ↪ Fin n)
    (ψ : Bits k × OutsideBits w → ℂ) : splitState w (unsplitState w ψ)=ψ := by
  funext p
  simp only [splitState,unsplitState,Equiv.apply_symm_apply]

/-- Native word semantics after local initialization, expressed without a
product-state assumption on the data/reference registers. -/
theorem relocate_word_initialized {k r n : ℕ} (w : Fin (k+r) ↪ Fin n)
    (word : List (Letter (k+r))) (ψ : Bits k×OutsideBits w → ℂ) :
    splitState w (runLayer (instructions (word.map (Letter.relocate w)))
      (unsplitState w (initWithReference (r:=r) ψ)))=
        applyWithReference (initializedMap (n:=k) (w:=r) (matrix word)) ψ := by
  rw [relocate_word_split,split_unsplit,applyWithReference_initialized]

/-- The ideal initialized map returns every local ancilla to zero and acts
only on the intended data register. -/
theorem applyWithReference_ideal {k r : ℕ} {R : Type*}
    (U : Matrix (Bits k) (Bits k) ℂ) (ψ : Bits k×R → ℂ) :
    applyWithReference (idealMap U r) ψ=
      initWithReference (r:=r) (applyWithReference U ψ) := by
  classical
  funext p
  simp only [applyWithReference,idealMap,initWithReference,Matrix.mulVec,dotProduct,Matrix.of_apply]
  split_ifs <;> simp_all [Finset.sum_mul]

/-- The full relocated circuit error is bounded by its initialized-map error
on arbitrary entangled data. Leakage into nonzero ancillas remains in the norm. -/
theorem relocate_initialized_error {k r n : ℕ} (w : Fin (k+r) ↪ Fin n)
    (word : List (Letter (k+r))) (U : Matrix (Bits k) (Bits k) ℂ)
    (ε : ℝ) (h : frobNorm (initializedMap (matrix word)-idealMap U r)≤ε)
    (ψ : Bits k×OutsideBits w → ℂ) :
    ‖(WithLp.toLp 2
      (runLayer (instructions (word.map (Letter.relocate w)))
          (unsplitState w (initWithReference (r:=r) ψ))-
        unsplitState w (initWithReference (r:=r) (applyWithReference U ψ))) :
      EuclideanSpace ℂ (Bits n))‖ ≤
        ε*‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits k×OutsideBits w))‖ := by
  rw [←splitState_norm w]
  have hs : splitState w
      (runLayer (instructions (word.map (Letter.relocate w)))
          (unsplitState w (initWithReference (r:=r) ψ))-
        unsplitState w (initWithReference (r:=r) (applyWithReference U ψ)))=
      splitState w (runLayer (instructions (word.map (Letter.relocate w)))
          (unsplitState w (initWithReference (r:=r) ψ)))-
        splitState w (unsplitState w (initWithReference (r:=r) (applyWithReference U ψ))) := rfl
  rw [hs,relocate_word_initialized,split_unsplit,←applyWithReference_ideal]
  exact applyWithReference_error (initializedMap (matrix word)) (idealMap U r) ε h ψ

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeFiniteGateAlphabet. -/
section P2MDyadicModule21

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

@[simp] theorem alphabet_length : alphabet.length=12 := rfl

theorem mem_alphabet (a : Letter 3) : a∈alphabet := by
  cases a with
  | h i => fin_cases i <;> simp [alphabet]
  | t i => fin_cases i <;> simp [alphabet]
  | cnot i j hij => fin_cases i <;> fin_cases j <;> simp_all [alphabet] <;> exact hij rfl

/-- A concrete finite list, including every word of length at most the given bound. -/
def words : ℕ → List (List (Letter 3))
  | 0 => [[]]
  | k+1 => []::alphabet.flatMap (fun a => (words k).map (a::·))

theorem mem_words_iff (word : List (Letter 3)) (k : ℕ) : word∈words k ↔ word.length≤k := by
  induction k generalizing word with
  | zero => simp [words,List.length_eq_zero_iff]
  | succ k ih =>
    cases word with
    | nil => simp [words]
    | cons a rest =>
      simp only [words,List.mem_cons,List.cons_ne_nil,false_or,List.mem_flatMap,List.mem_map,
        List.cons.injEq,List.length_cons,Nat.add_le_add_iff_right]
      constructor
      · rintro ⟨b,_,tail,ht,hba,htail⟩
        subst b;subst tail;exact (ih rest).mp ht
      · intro h
        exact ⟨a,mem_alphabet a,rest,(ih rest).mpr h,rfl,rfl⟩

/-- One absolute integer search-length constant works for every target one-qubit unitary
and every dyadic precision. The finite candidate list reads neither an unknown solution
nor a real-valued search oracle. This statement certifies coverage only. -/
theorem exists_dyadic_approximation :
    ∃ a : ℕ, 0<a ∧ ∀ U : Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ,
      U∈Matrix.unitaryGroup (QAlgorithms.Qubits 1) ℂ → ∀ bits : ℕ,
      ∃ word∈words (a*(bits+1)),
        QAlgorithms.frobNorm
          (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (matrix word)-
           QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2)≤1/(2 : ℝ)^bits := by
  obtain ⟨A,hA,happrox⟩ := exists_approximation
  let a : ℕ := ⌈A⌉₊
  have hceil : A≤(a : ℝ) := Nat.le_ceil A
  have ha : 0<a := by
    by_contra h
    have hz : a=0 := by omega
    rw [hz] at hceil
    norm_num at hceil
    linarith
  refine ⟨a,ha,?_⟩
  intro U hU bits
  have hp : (0 : ℝ)<2^bits := by positivity
  have hone : (1 : ℝ)≤2^bits := one_le_pow₀ (by norm_num)
  obtain ⟨word,herror,hsize⟩ := happrox U hU (1/(2 : ℝ)^bits)
    (by positivity) ((div_le_one hp).mpr hone)
  have htwo : Real.log 2≠0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  have hlog : Real.log (1/(1/(2 : ℝ)^bits))/Real.log 2=(bits : ℝ) := by
    simp only [one_div,inv_inv,Real.log_pow]
    field_simp
  rw [hlog] at hsize
  refine ⟨word,(mem_words_iff _ _).mpr ?_,herror⟩
  have hb : (0 : ℝ)≤bits+1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hceil hb
  have hbound : (word.length : ℝ)≤((a*(bits+1) : ℕ) : ℝ) := by
    push_cast
    exact hsize.trans hmul
  exact_mod_cast hbound

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeFiniteGateNativeAlgebra. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def conj (x : Scalar) : Scalar := (x.1,negReal x.2)

noncomputable def evalReal (x : RealPair) : ℝ := x.1+(x.2 : ℝ)*Real.sqrt 2

noncomputable def eval (x : Scalar) : ℂ := ⟨evalReal x.1,evalReal x.2⟩

@[simp] theorem evalReal_add (x y : RealPair) : evalReal (addReal x y)=evalReal x+evalReal y := by
  simp only [evalReal,addReal,Rat.cast_add]
  ring

@[simp] theorem evalReal_neg (x : RealPair) : evalReal (negReal x)= -evalReal x := by
  simp only [evalReal,negReal,Rat.cast_neg]
  ring

@[simp] theorem evalReal_sub (x y : RealPair) : evalReal (subReal x y)=evalReal x-evalReal y := by
  simp [subReal,sub_eq_add_neg]

@[simp] theorem evalReal_mul (x y : RealPair) : evalReal (mulReal x y)=evalReal x*evalReal y := by
  simp only [evalReal,mulReal,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ)≤2 by norm_num)]

@[simp] theorem eval_zero : eval zero=0 := by apply Complex.ext <;> simp [eval,evalReal,zero]

@[simp] theorem eval_one : eval one=1 := by apply Complex.ext <;> simp [eval,evalReal,one]

@[simp] theorem eval_add (x y : Scalar) : eval (add x y)=eval x+eval y := by
  apply Complex.ext <;> simp [eval,add]

@[simp] theorem eval_neg (x : Scalar) : eval (neg x)= -eval x := by
  apply Complex.ext <;> simp [eval,neg]

@[simp] theorem eval_sub (x y : Scalar) : eval (sub x y)=eval x-eval y := by
  simp [sub,sub_eq_add_neg]

@[simp] theorem eval_mul (x y : Scalar) : eval (mul x y)=eval x*eval y := by
  apply Complex.ext <;> simp [eval,mul,Complex.mul_re,Complex.mul_im]

@[simp] theorem eval_conj (x : Scalar) : eval (conj x)=star (eval x) := by
  apply Complex.ext <;> simp [eval,conj]

@[simp] theorem eval_normSq (x : Scalar) : evalReal (normSq x)=Complex.normSq (eval x) := by
  simp [normSq,eval,Complex.normSq_apply]

private theorem sign_of_nonneg_second (a b : ℝ) (hb : 0≤b) (ha : a<0) :
    0≤a+b*Real.sqrt 2 ↔ a^2≤2*b^2 := by
  have hs : 0≤Real.sqrt 2 := Real.sqrt_nonneg _
  have hc : 0≤b*Real.sqrt 2 := mul_nonneg hb hs
  have ha' : 0≤ -a := by linarith
  have hsq : (b*Real.sqrt 2)^2=2*b^2 := by
    rw [mul_pow,Real.sq_sqrt (show (0 : ℝ)≤2 by norm_num)]
    ring
  have h := sq_le_sq₀ ha' hc
  rw [neg_sq,hsq] at h
  constructor
  · intro hp;exact h.mpr (by linarith)
  · intro hp;have := h.mp hp;linarith

private theorem sign_of_neg_second (a b : ℝ) (hb : b<0) (ha : 0≤a) :
    0≤a+b*Real.sqrt 2 ↔ 2*b^2≤a^2 := by
  have hs : 0≤Real.sqrt 2 := Real.sqrt_nonneg _
  have hc : 0≤ -(b*Real.sqrt 2) := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hb.le hs)
  have hsq : (-(b*Real.sqrt 2))^2=2*b^2 := by
    rw [neg_sq,mul_pow,Real.sq_sqrt (show (0 : ℝ)≤2 by norm_num)]
    ring
  have h := sq_le_sq₀ hc ha
  rw [hsq] at h
  constructor
  · intro hp;exact h.mpr (by linarith)
  · intro hp;have := h.mp hp;linarith

theorem nonnegReal_correct (x : RealPair) : nonnegReal x=true ↔ 0≤evalReal x := by
  unfold nonnegReal
  by_cases hb : 0≤x.2
  · rw [if_pos hb]
    have hb' : (0 : ℝ)≤x.2 := by exact_mod_cast hb
    by_cases ha : 0≤x.1
    · rw [if_pos ha]
      have ha' : (0 : ℝ)≤x.1 := by exact_mod_cast ha
      simp only [true_iff]
      exact add_nonneg ha' (mul_nonneg hb' (Real.sqrt_nonneg _))
    · rw [if_neg ha,decide_eq_true_eq]
      have ha' : (x.1 : ℝ)<0 := by exact_mod_cast lt_of_not_ge ha
      rw [evalReal,sign_of_nonneg_second _ _ hb' ha']
      norm_cast
  · rw [if_neg hb]
    have hb' : (x.2 : ℝ)<0 := by exact_mod_cast lt_of_not_ge hb
    by_cases ha : x.1<0
    · rw [if_pos ha]
      have ha' : (x.1 : ℝ)<0 := by exact_mod_cast ha
      simp only [Bool.false_eq_true,false_iff,not_le]
      exact add_neg_of_neg_of_nonpos ha' (mul_nonpos_of_nonpos_of_nonneg hb'.le (Real.sqrt_nonneg _))
    · rw [if_neg ha,decide_eq_true_eq]
      have ha' : (0 : ℝ)≤x.1 := by exact_mod_cast le_of_not_gt ha
      rw [evalReal,sign_of_neg_second _ _ hb' ha']
      norm_cast

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

theorem leRational_correct (x : RealPair) (bound : ℚ) :
    leRational x bound=true ↔ evalReal x≤bound := by
  rw [leRational,nonnegReal_correct,evalReal_sub]
  simp only [evalReal,Rat.cast_zero,zero_mul,add_zero]
  constructor <;> intro h <;> linarith

@[fun_prop] theorem leRational_poly : Poly (fun x : RealPair×ℚ => leRational x.1 x.2) := by
  unfold leRational
  fun_prop

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeFiniteGateNativeCoefficients. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

@[simp] theorem eval_hScale : eval hScale=((Real.sqrt 2)⁻¹ : ℂ) := by
  apply Complex.ext
  · norm_num [eval,evalReal,hScale]
    ring
  · simp [eval,evalReal,hScale]

@[simp] theorem eval_tPhase : eval tPhase=Complex.exp (Complex.I*Real.pi/4) := by
  have harg : Complex.I*(Real.pi : ℂ)/4=(((Real.pi/4 : ℝ) : ℂ)*Complex.I) := by
    push_cast
    ring
  rw [harg]
  apply Complex.ext
  · norm_num [eval,evalReal,tPhase,Complex.exp_re,Complex.mul_re,Complex.mul_im,Real.cos_pi_div_four]
    ring
  · norm_num [eval,evalReal,tPhase,Complex.exp_im,Complex.mul_re,Complex.mul_im,Real.sin_pi_div_four]
    ring

@[simp] theorem eval_hCoefficient (row column : Bool) :
    eval (hCoefficient row column)=QAlgorithms.Complexity.hMat row column := by
  simp only [hCoefficient,QAlgorithms.Complexity.hMat,Matrix.of_apply]
  split <;> simp

@[simp] theorem eval_tCoefficient (row column : Bool) :
    eval (tCoefficient row column)=QAlgorithms.Complexity.tMat row column := by
  simp only [tCoefficient,QAlgorithms.Complexity.tMat,Matrix.of_apply]
  by_cases h : row=column
  · rw [if_pos h,if_pos h]
    split <;> simp_all
  · simp [h]

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeFiniteGateNativeBounds. -/
section P2MDyadicModule24

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

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeFiniteGateNativeMatrix. -/
section P2MDyadicModule25

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

theorem basis_nodup : basis.Nodup := by decide

theorem basis_toFinset : basis.toFinset=Finset.univ := by
  ext x
  simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
  exact mem_basis x

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

theorem sumAt_eval (indices : List Bits) (f : Bits→Scalar) :
    eval (sumAt indices f)=(indices.map (fun i => eval (f i))).sum := by
  induction indices with
  | nil => simp [sumAt]
  | cons i rest ih => simpa [sumAt,List.foldr_cons,eval_add] using congrArg (fun z => eval (f i)+z) ih

theorem sumAt_poly {α : Type} [Coding α] (indices : List Bits) (f : α→Bits→Scalar)
    (hf : ∀ i∈indices,Poly (fun x => f x i)) : Poly (fun x => sumAt indices (f x)) := by
  induction indices with
  | nil => exact Automatic.Poly.const zero
  | cons i rest ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun x => add (f x i) (sumAt rest (f x)))
    exact Poly.comp add_poly (Poly.pair hi ht)

noncomputable def evalMatrix (m : NativeMatrix) : Matrix Bits Bits ℂ := fun r c => eval (m r c)

theorem eval_matrixMul (first second : NativeMatrix) :
    evalMatrix (matrixMul first second)=evalMatrix first*evalMatrix second := by
  funext r c
  simp only [evalMatrix,matrixMul,sumAt_eval,eval_mul]
  rw [←List.sum_toFinset _ basis_nodup,basis_toFinset]
  rfl

@[fun_prop] theorem matrixMul_poly : Poly (fun x : NativeMatrix×NativeMatrix => matrixMul x.1 x.2) := by
  apply matrix_build_poly
  intro r hr c hc
  apply sumAt_poly
  intro k hk
  exact Poly.comp mul_poly (Poly.pair
    (Poly.comp (matrix_entry_poly r k) Poly.fst)
    (Poly.comp (matrix_entry_poly k c) Poly.snd))

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeFiniteGateNativeMatrixBounds. -/
section P2MDyadicModule26

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

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeFiniteGateNativeEnumeration. -/
section P2MDyadicModule27

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

def encode : List ℕ → ℕ
  | [] => 0
  | a::w => 13*encode w+(a+1)

theorem encode_pos {a : ℕ} {w : List ℕ} : 0<encode (a::w) := by simp only [encode];omega

theorem step_encode (a : ℕ) (w acc : List ℕ) (ha : a<12) (u : Unit) :
    step ((encode (a::w),acc),u)=(encode w,a::acc) := by
  have hn := encode_pos (a:=a) (w:=w)
  have hdiv : encode (a::w)/13=encode w := by
    change (13*encode w+(a+1))/13=encode w
    omega
  have hmod : encode (a::w)%13-1=a := by
    simp only [encode,Nat.mul_add_mod,Nat.mod_eq_of_lt (by omega : a+1<13),Nat.add_sub_cancel]
  simp only [step,if_neg hn.ne',hdiv,hmod]

theorem fold_zero (slots : List Unit) (acc : List ℕ) :
    slots.foldl (fun s u => step (s,u)) (0,acc)=(0,acc) := by
  induction slots with
  | nil => rfl
  | cons u us ih => simpa only [List.foldl_cons,step,ite_true] using ih

theorem fold_encode (w acc : List ℕ) (slots : List Unit)
    (hw : ∀ a∈w,a<12) (hl : w.length≤ slots.length) :
    slots.foldl (fun s u => step (s,u)) (encode w,acc)=(0,w.reverse++acc) := by
  induction w generalizing slots acc with
  | nil => simpa only [encode,List.reverse_nil,List.nil_append] using fold_zero slots acc
  | cons a w ih =>
    cases slots with
    | nil => simp at hl
    | cons u us =>
      rw [List.foldl_cons,step_encode a w acc (hw a (by simp)) u]
      rw [ih (a::acc) us (by intro b hb;exact hw b (by simp [hb])) (by simpa using hl)]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem decode_encode (w : List ℕ) (slots : List Unit)
    (hw : ∀ a∈w,a<12) (hl : w.length≤ slots.length) :
    decode (slots,encode w)=w := by
  unfold decode
  rw [fold_encode w [] slots hw hl]
  simp

theorem length_le_encode (w : List ℕ) : w.length≤encode w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.length_cons,encode];omega

theorem encode_lt_pow (w : List ℕ) (hw : ∀ a∈w,a<12) : encode w<13^w.length := by
  induction w with
  | nil => norm_num [encode]
  | cons a w ih =>
    have ha := hw a (by simp)
    have ht := ih (by intro b hb;exact hw b (by simp [hb]))
    simp only [encode,List.length_cons,pow_succ]
    omega

@[fun_prop] theorem candidates_poly : Poly candidates := by
  unfold candidates
  exact Poly.list_map (Poly.comp decode_poly (by fun_prop)) Poly.list_indices

theorem mem_candidates (slots : List Unit) (w : List ℕ)
    (hw : ∀ a∈w,a<12) (hcode : encode w<slots.length) : w∈candidates slots := by
  apply List.mem_map.mpr
  exact ⟨encode w,List.mem_range.mpr hcode,decode_encode w slots hw
    ((length_le_encode w).trans hcode.le)⟩

theorem div_bits_decrease (index : ℕ) (hi : index≠0) :
    (index/13).bits.length+1 ≤ index.bits.length := by
  have hdiv : index/13 ≤ index.div2 := by
    rw [Nat.div2_val]
    exact Nat.div_le_div_left (by decide : 2≤13) (by decide : 0<2)
  have hm := NatBinary.length_mono hdiv
  have hh := NatBinary.half_lt_length hi
  omega

theorem fold_length_bound (slots : List Unit) (index : ℕ) (acc : List ℕ) :
    (slots.foldl (fun s u => step (s,u)) (index,acc)).2.length ≤
      acc.length+index.bits.length := by
  induction slots generalizing index acc with
  | nil => simp
  | cons u us ih =>
    by_cases hi : index=0
    · subst index
      rw [fold_zero]
      simp
    · rw [List.foldl_cons]
      change (us.foldl (fun s u => step (s,u))
        (if index=0 then (index,acc) else (index/13,(index%13-1)::acc))).2.length ≤ _
      rw [if_neg hi]
      have hh := ih (index/13) ((index%13-1)::acc)
      have hd := div_bits_decrease index hi
      simp only [List.length_cons] at hh
      omega

theorem decode_length (slots : List Unit) (index : ℕ) :
    (decode (slots,index)).length ≤ index.bits.length := by
  simpa only [decode,List.length_reverse,List.length_nil,Nat.zero_add] using fold_length_bound slots index []

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

theorem search_coverage (a bits : ℕ) (budget : List Unit) (hbits : 2^bits≤budget.length+1)
    (word : List ℕ) (hw : ∀ letter∈word,letter<12) (hlen : word.length≤a*(bits+1)) :
    word∈search a budget := by
  apply mem_candidates _ word hw
  rw [searchSlots_length]
  have hc := encode_lt_pow word hw
  have hp := Nat.pow_le_pow_right (by decide : 1≤13) hlen
  have hb : 13≤2^4 := by decide
  have hm : 13^(a*(bits+1)) ≤ 13^(a+1)*(budget.length+1)^(4*a) := by
    calc
      13^(a*(bits+1)) ≤ 13^(a*(bits+1)+1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ = 13^(a+1)*(13^a)^bits := by rw [←pow_mul,←pow_add];congr 1;ring
      _ ≤ 13^(a+1)*((2^4)^a)^bits :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.pow_le_pow_left hb a) bits)
      _ = 13^(a+1)*(2^bits)^(4*a) := by congr 1;simp only [←pow_mul];congr 1;ring
      _ ≤ 13^(a+1)*(budget.length+1)^(4*a) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbits (4*a))
  exact hc.trans_le (hp.trans hm)

theorem mem_search_length (a : ℕ) (budget : List Unit) (codes : List ℕ)
    (hcodes : codes∈search a budget) :
    codes.length ≤ (13^(a+1)*(budget.length+1)^(4*a)).bits.length := by
  obtain ⟨index,hi,rfl⟩ := List.mem_map.mp hcodes
  have hindex := List.mem_range.mp hi
  have hm := NatBinary.length_mono hindex.le
  rw [searchSlots_length] at hm
  exact (decode_length _ _).trans hm

open FiniteGateTransport

def letterCode (letter : Letter 3) : ℕ := alphabet.idxOf letter

theorem letterCode_lt (letter : Letter 3) : letterCode letter<12 := by
  have h := List.idxOf_lt_length_of_mem (mem_alphabet letter)
  exact h

theorem letterOfCode_code (letter : Letter 3) : letterOfCode (letterCode letter)=letter := by
  simp only [letterOfCode,letterCode,List.getElem?_idxOf (mem_alphabet letter),Option.getD_some]

def wordCodes (word : List (Letter 3)) : List ℕ := word.map letterCode

theorem interpreted_wordCodes (word : List (Letter 3)) : interpreted (wordCodes word)=word := by
  simp only [interpreted,wordCodes,List.map_map,Function.comp_def,letterOfCode_code]
  exact List.map_id _

theorem wordCodes_valid (word : List (Letter 3)) : ∀ code∈wordCodes word,code<12 := by
  intro code hc
  obtain ⟨letter,_,rfl⟩ := List.mem_map.mp hc
  exact letterCode_lt letter

/-- A fixed native search program covers all approximating finite-gate words
at inverse precision bounded by the supplied unary budget. The target unitary
appears only in correctness, never in the executable candidate generator. -/
theorem search_contains_approximation :
    ∃ a : ℕ, 0<a ∧ ∀ U : Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ,
      U∈Matrix.unitaryGroup (QAlgorithms.Qubits 1) ℂ → ∀ bits : ℕ,
      ∀ budget : List Unit, 2^bits≤budget.length+1 →
      ∃ codes∈search a budget,
        QAlgorithms.frobNorm
          (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (matrix (interpreted codes))-
           QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2)≤1/(2 : ℝ)^bits := by
  obtain ⟨a,ha,h⟩ := exists_dyadic_approximation
  refine ⟨a,ha,?_⟩
  intro U hU bits budget hbits
  obtain ⟨word,hw,herror⟩ := h U hU bits
  refine ⟨wordCodes word,search_coverage a bits budget hbits _ (wordCodes_valid word) ?_,?_⟩
  · simpa only [wordCodes,List.length_map] using (mem_words_iff word _).mp hw
  · simpa only [interpreted_wordCodes] using herror

end InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeFiniteGateNativeGates. -/
section P2MDyadicModule28

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

theorem eval_singleGate (coefficient : Bool→Bool→Scalar) (U : Matrix Bool Bool ℂ)
    (hU : ∀ row column,eval (coefficient row column)=U row column) (i : Fin 3) :
    evalMatrix (singleGate coefficient i)=
      QAlgorithms.embedOp (QAlgorithms.Gate.ofMatrix1 U).mat (oneWire i) := by
  funext row column
  change eval (if column=Function.update row i (column i) then coefficient (row i) (column i) else zero)=
    if (∀ a,a∉Set.range (oneWire i) → row a=column a) then U (row i) (column i) else 0
  simp only [off_oneWire_iff]
  by_cases h : column=Function.update row i (column i)
  · simp only [if_pos h]
    exact hU (row i) (column i)
  · simp only [if_neg h,eval_zero]

theorem eval_letterNative (letter : Letter 3) :
    evalMatrix (letterNative letter)=
      QAlgorithms.embedOp letter.toGate.gate.mat letter.toGate.wires := by
  cases letter with
  | h i =>
    change evalMatrix (singleGate hCoefficient i)=
      QAlgorithms.embedOp (QAlgorithms.Gate.ofMatrix1 QAlgorithms.hadamard).mat (oneWire i)
    rw [FiniteGateTransport.hadamard_eq_hMat]
    exact eval_singleGate hCoefficient QAlgorithms.Complexity.hMat eval_hCoefficient i
  | t i =>
    change evalMatrix (singleGate tCoefficient i)=
      QAlgorithms.embedOp (QAlgorithms.Gate.ofMatrix1 QAlgorithms.gateT).mat (oneWire i)
    rw [FiniteGateTransport.gateT_eq_tMat]
    exact eval_singleGate tCoefficient QAlgorithms.Complexity.tMat eval_tCoefficient i
  | cnot i j hij =>
    funext row column
    rw [show (QAlgorithms.embedOp (Letter.toGate (.cnot i j hij)).gate.mat
      (Letter.toGate (.cnot i j hij)).wires) row column=
      if column=Function.update row j (xor (row j) (row i)) then 1 else 0 by
        exact embed_cnot_entry (twoWire i j hij) row column]
    change eval (if column=Function.update row j (xor (row j) (row i)) then one else zero)=_
    split <;> simp

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

theorem eval_nativeGate (code : ℕ) :
    evalMatrix (nativeGate code)=
      QAlgorithms.embedOp (FiniteGateNativeEnumeration.letterOfCode code).toGate.gate.mat
        (FiniteGateNativeEnumeration.letterOfCode code).toGate.wires := by
  rw [nativeGate_eq,eval_letterNative]

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeFiniteGateNativeResourceBounds. -/
section P2MDyadicModule29

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

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeFiniteGateNativeWord. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

@[simp] theorem eval_identityMatrix : evalMatrix identityMatrix=1 := by
  funext row column
  change eval (if row=column then one else zero)=if row=column then 1 else 0
  split <;> simp

def nativeRun (codes : List ℕ) (state : NativeMatrix) : NativeMatrix :=
  codes.foldl (fun current code => matrixMul (nativeGate code) current) state

theorem nativeRun_eval (codes : List ℕ) (state : NativeMatrix) :
    evalMatrix (nativeRun codes state)=
      matrix (FiniteGateNativeEnumeration.interpreted codes)*evalMatrix state := by
  induction codes generalizing state with
  | nil => simp [nativeRun,FiniteGateNativeEnumeration.interpreted,matrix,QAlgorithms.Circuit.unitary]
  | cons code rest ih =>
    change evalMatrix (nativeRun rest (matrixMul (nativeGate code) state))=_
    rw [ih,eval_matrixMul,eval_nativeGate]
    have hm : matrix (FiniteGateNativeEnumeration.interpreted (code::rest))=
        matrix (FiniteGateNativeEnumeration.interpreted rest)*
          QAlgorithms.embedOp (FiniteGateNativeEnumeration.letterOfCode code).toGate.gate.mat
            (FiniteGateNativeEnumeration.letterOfCode code).toGate.wires := by
      simp [FiniteGateNativeEnumeration.interpreted,matrix,QAlgorithms.Circuit.unitary,
        List.reverse_cons,List.prod_append]
    rw [hm,Matrix.mul_assoc]

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

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeFiniteGateNativeBounded. -/
section P2MDyadicModule31

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

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeFiniteGateNativeWordPoly. -/
section P2MDyadicModule32

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

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeFiniteGateNativePredicate. -/
section P2MDyadicModule33
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

theorem mem_inputs (x : InputBits) : x∈inputs := by
  cases h : x 0
  · have hx : x=(fun _ => false) := by funext i;have hi : i=0 := Subsingleton.elim _ _;simpa [hi] using h
    simp [hx,inputs]
  · have hx : x=(fun _ => true) := by funext i;have hi : i=0 := Subsingleton.elim _ _;simpa [hi] using h
    simp [hx,inputs]

theorem inputs_nodup : inputs.Nodup := by decide

theorem inputs_toFinset : inputs.toFinset=Finset.univ := by ext x;simp [mem_inputs]

theorem sumReal_eval {ι : Type} (indices : List ι) (f : ι→RealPair) :
    evalReal (sumReal indices f)=(indices.map (fun i => evalReal (f i))).sum := by
  induction indices with
  | nil => simp [sumReal,evalReal]
  | cons i rest ih => simpa [sumReal,List.foldr_cons,evalReal_add] using congrArg (fun z => evalReal (f i)+z) ih

theorem sumReal_poly {α ι : Type} [Coding α] (indices : List ι) (f : α→ι→RealPair)
    (hf : ∀ i∈indices,Poly (fun x => f x i)) : Poly (fun x => sumReal indices (f x)) := by
  induction indices with
  | nil => exact Automatic.Poly.const (0,0)
  | cons i rest ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun x => addReal (f x i) (sumReal rest (f x)))
    exact Poly.comp addReal_poly (Poly.pair hi ht)

noncomputable def initializedNative (m : NativeMatrix) : Matrix Bits InputBits ℂ :=
  fun row column => eval (m row (initializedColumn column))

theorem initializedNative_eq (m : NativeMatrix) : initializedNative m=
    QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2) (evalMatrix m) := rfl

theorem frobNorm_sq {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    QAlgorithms.frobNorm A^2=∑ row,∑ column,Complex.normSq (A row column) := by
  unfold QAlgorithms.frobNorm
  rw [Matrix.frobenius_norm_def,←Real.sqrt_eq_rpow,Real.sq_sqrt]
  · simp only [Real.rpow_two,Complex.normSq_eq_norm_sq]
  · exact Finset.sum_nonneg (fun row _ => Finset.sum_nonneg (fun column _ => Real.rpow_nonneg (norm_nonneg _) _))

theorem rectangleError_eval (first second : NativeMatrix) :
    evalReal (rectangleError first second)=
      QAlgorithms.frobNorm (initializedNative first-initializedNative second)^2 := by
  rw [frobNorm_sq]
  simp only [rectangleError,sumReal_eval,eval_normSq,eval_sub]
  rw [←List.sum_toFinset _ basis_nodup,basis_toFinset]
  apply Finset.sum_congr rfl
  intro row _
  rw [←List.sum_toFinset _ inputs_nodup,inputs_toFinset]
  rfl

@[fun_prop] theorem rectangleError_poly : Poly (fun x : NativeMatrix×NativeMatrix => rectangleError x.1 x.2) := by
  apply sumReal_poly
  intro row _
  apply sumReal_poly
  intro column _
  exact Poly.comp normSq_poly (Poly.comp sub_poly (Poly.pair
    (Poly.comp (matrix_entry_poly row (initializedColumn column)) Poly.fst)
    (Poly.comp (matrix_entry_poly row (initializedColumn column)) Poly.snd)))

theorem accepts_correct (first second : NativeMatrix) (tolerance : ℚ) (ht : 0≤tolerance) :
    accepts first second tolerance=true ↔
      QAlgorithms.frobNorm (initializedNative first-initializedNative second)≤tolerance := by
  rw [accepts,leRational_correct,rectangleError_eval,Rat.cast_pow]
  exact sq_le_sq₀ (norm_nonneg _) (by exact_mod_cast ht)

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

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeFiniteGateNativeCompiler. -/
section P2MDyadicModule34

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

attribute [local irreducible] matrixMul nativeGate maxSteps

theorem evalFold_exact (a : ℕ) (codes : List ℕ) (state : EvalState)
    (hlen : state.1.2+codes.length ≤ maxSteps a state.1.1) :
    evalFold a codes state=((state.1.1,state.1.2+codes.length),nativeRun codes state.2) := by
  induction codes generalizing state with
  | nil => rfl
  | cons code rest ih =>
    have hlt : state.1.2 < maxSteps a state.1.1 := by simp only [List.length_cons] at hlen;omega
    change evalFold a rest (evalStep a (state,code))=_
    simp only [evalStep,if_pos hlt]
    have hrest : state.1.2+1+rest.length ≤ maxSteps a state.1.1 := by simp only [List.length_cons] at hlen;omega
    have hh := ih (((state.1.1,state.1.2+1),matrixMul (nativeGate code) state.2)) hrest
    simpa only [nativeRun,List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem boundedMatrix_eval (a : ℕ) (budget : List Unit) (codes : List ℕ)
    (hlen : codes.length ≤ maxSteps a budget) :
    evalMatrix (boundedMatrix a (budget,codes))=matrix (FiniteGateNativeEnumeration.interpreted codes) := by
  unfold boundedMatrix
  rw [evalFold_exact a codes ((budget,0),identityMatrix) (by simpa using hlen)]
  simp only [nativeRun_eval,eval_identityMatrix,Matrix.mul_one]

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

theorem compilerTest_correct (a : ℕ) (request : CompileRequest) (codes : List ℕ)
    (hcodes : codes∈FiniteGateNativeEnumeration.search a request.1.1) (ht : 0≤ request.2) :
    compilerTest a (request,codes)=true ↔
      QAlgorithms.frobNorm
        (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
          (matrix (FiniteGateNativeEnumeration.interpreted codes))-initializedNative request.1.2)≤ request.2 := by
  have hlen : codes.length ≤ maxSteps a request.1.1 := by
    simpa only [maxSteps] using FiniteGateNativeEnumeration.mem_search_length a request.1.1 codes hcodes
  rw [compilerTest,accepts_correct _ _ _ ht,initializedNative_eq,boundedMatrix_eval a _ _ hlen]

theorem compileWord_witness (a : ℕ) (request : CompileRequest)
    (hexists : ∃ codes∈FiniteGateNativeEnumeration.search a request.1.1,
      compilerTest a (request,codes)=true) :
    compileWord a request∈FiniteGateNativeEnumeration.search a request.1.1 ∧
      compilerTest a (request,compileWord a request)=true := by
  let candidates := FiniteGateNativeEnumeration.search a request.1.1
  have hi : candidates.findIdx (fun codes => compilerTest a (request,codes)) < candidates.length :=
    List.findIdx_lt_length_of_exists hexists
  have hg := List.getElem?_eq_getElem hi
  have hp := List.findIdx_getElem (xs:=candidates) (p:=fun codes => compilerTest a (request,codes)) (w:=hi)
  have hc : compileWord a request=candidates[candidates.findIdx (fun codes => compilerTest a (request,codes))]'hi := by
    unfold compileWord
    change candidates[candidates.findIdx (fun codes => compilerTest a (request,codes))]?.getD []=_
    rw [hg]
    rfl
  rw [hc]
  exact ⟨List.mem_of_getElem rfl,hp⟩

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeFiniteGateNativeGuarantee. -/
section P2MDyadicModule35
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

theorem frob_triangle {m n : Type} [Fintype m] [Fintype n] (A B C : Matrix m n ℂ) :
    QAlgorithms.frobNorm (A-C)≤ QAlgorithms.frobNorm (A-B)+QAlgorithms.frobNorm (B-C) := by
  have h : A-C=(A-B)+(B-C) := by abel
  rw [h]
  exact norm_add_le _ _

theorem frob_sub_comm {m n : Type} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) :
    QAlgorithms.frobNorm (A-B)=QAlgorithms.frobNorm (B-A) := norm_sub_rev _ _

@[fun_prop] theorem compilerTolerance_poly : Poly compilerTolerance := by unfold compilerTolerance;fun_prop

attribute [local irreducible] compileWord nativeCompile compilerTolerance

theorem nativeCompile_poly (a : ℕ) : Poly (nativeCompile a) := by
  unfold nativeCompile
  exact Poly.comp (compileWord_poly a) (Poly.pair Poly.identity (Poly.comp compilerTolerance_poly Poly.fst))

private theorem dyadic_scale (N : ℕ) : ∃ bits : ℕ,
    2^bits≤ N+1 ∧ 1/(2 : ℝ)^bits≤2/((N : ℝ)+1) := by
  let bits := (N+1).size-1
  have hs : 0<(N+1).size := Nat.size_pos.mpr (by omega)
  have hlo : 2^bits≤ N+1 := Nat.lt_size.mp (by dsimp [bits];omega)
  have hhi : N+1<2^(bits+1) := by
    have hh := Nat.lt_size_self (N+1)
    have he : bits+1=(N+1).size := by dsimp [bits];omega
    rwa [he]
  have hN : (0 : ℝ)<(N : ℝ)+1 := by positivity
  have hp : (0 : ℝ)<2^bits := by positivity
  refine ⟨bits,hlo,(div_le_div_iff₀ hp hN).mpr ?_⟩
  have hh : (N : ℝ)+1≤(2 : ℝ)^bits*2 := by
    have hn := hhi.le
    rw [pow_succ] at hn
    exact_mod_cast hn
  nlinarith

/-- The executable compiler reads a finite rational matrix table and a unary budget.
The real unitary occurs only in this correctness theorem, never in its machine input. -/
theorem exists_nativeCompile_accuracy :
    ∃ a : ℕ,0< a ∧ ∀ U : Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ,
      U∈Matrix.unitaryGroup (QAlgorithms.Qubits 1) ℂ →
      ∀ (budget : List Unit) (target : NativeMatrix),
      QAlgorithms.frobNorm (initializedNative target-
        QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2)≤1/((budget.length : ℝ)+1) →
      nativeCompile a (budget,target)∈FiniteGateNativeEnumeration.search a budget ∧
      QAlgorithms.frobNorm
        (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
          (matrix (FiniteGateNativeEnumeration.interpreted (nativeCompile a (budget,target))))-
          QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2)≤5/((budget.length : ℝ)+1) := by
  obtain ⟨a,ha,happrox⟩ := FiniteGateNativeEnumeration.search_contains_approximation
  refine ⟨a,ha,?_⟩
  intro U hU budget target htarget
  obtain ⟨bits,hbits,hscale⟩ := dyadic_scale budget.length
  obtain ⟨word,hword,herror⟩ := happrox U hU bits budget hbits
  let request : CompileRequest := ((budget,target),compilerTolerance budget)
  have htol : (compilerTolerance budget : ℝ)=4/((budget.length : ℝ)+1) := by
    simp only [compilerTolerance,Rat.cast_div,Rat.cast_ofNat,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]
  have htolRat : 0≤ compilerTolerance budget := by unfold compilerTolerance;positivity
  have hwtest : compilerTest a (request,word)=true := by
    apply (compilerTest_correct a request word hword htolRat).mpr
    change QAlgorithms.frobNorm
      (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
        (matrix (FiniteGateNativeEnumeration.interpreted word))-initializedNative target)≤(compilerTolerance budget : ℝ)
    rw [htol]
    have htri := frob_triangle
      (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
        (matrix (FiniteGateNativeEnumeration.interpreted word)))
      (QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2) (initializedNative target)
    rw [frob_sub_comm (QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2) (initializedNative target)] at htri
    calc
      _ ≤ (1/(2 : ℝ)^bits)+1/((budget.length : ℝ)+1) :=
        htri.trans (add_le_add herror htarget)
      _ ≤ 2/((budget.length : ℝ)+1)+1/((budget.length : ℝ)+1) :=
        add_le_add hscale le_rfl
      _ ≤ 4/((budget.length : ℝ)+1) := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hchosen := compileWord_witness a request ⟨word,hword,hwtest⟩
  have hchosenError := (compilerTest_correct a request (compileWord a request) hchosen.1 htolRat).mp hchosen.2
  change QAlgorithms.frobNorm
    (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
      (matrix (FiniteGateNativeEnumeration.interpreted (compileWord a request)))-initializedNative target)≤
      (compilerTolerance budget : ℝ) at hchosenError
  rw [htol] at hchosenError
  have htri := frob_triangle
    (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
      (matrix (FiniteGateNativeEnumeration.interpreted (compileWord a request))))
    (initializedNative target) (QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2)
  constructor
  · simpa only [nativeCompile,request] using hchosen.1
  · unfold nativeCompile
    change QAlgorithms.frobNorm
      (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
        (matrix (FiniteGateNativeEnumeration.interpreted (compileWord a request)))-
        QAlgorithms.Papers.Independent.Renew46.P12.idealMap U 2)≤ _
    calc
      _ ≤ 4/((budget.length : ℝ)+1)+1/((budget.length : ℝ)+1) :=
        htri.trans (add_le_add hchosenError htarget)
      _ = 5/((budget.length : ℝ)+1) := by ring

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgePhaseTaylor. -/
section P2MDyadicModule36

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open scoped BigOperators

noncomputable def taylorSum (z : ℂ) (terms : ℕ) : ℂ :=
  ∑ k∈Finset.range terms,z^k/(k.factorial : ℂ)

theorem taylorSum_error {z : ℂ} (hz : ‖z‖≤1) {terms : ℕ} (ht : 0<terms) :
    ‖Complex.exp z-taylorSum z terms‖≤2/(terms : ℝ) := by
  have htn : (1 : ℝ)≤terms := by exact_mod_cast ht
  have hratio : ‖z‖/(terms+1)≤(1 : ℝ)/2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<terms+1)).mpr
    linarith
  have h := Complex.exp_bound' (x:=z) (n:=terms) (by simpa only [Nat.cast_succ] using hratio)
  have hf : (terms : ℝ)≤terms.factorial := by exact_mod_cast Nat.self_le_factorial terms
  have hp : ‖z‖^terms≤1 := pow_le_one₀ (norm_nonneg _) hz
  change ‖Complex.exp z-taylorSum z terms‖≤_ at h
  calc
    _ ≤ ‖z‖^terms/(terms.factorial : ℝ)*2 := h
    _ ≤ 1/(terms.factorial : ℝ)*2 := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hp (by positivity)) (by norm_num)
    _ ≤ 1/(terms : ℝ)*2 := mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le (by positivity) hf) (by norm_num)
    _ = _ := by ring

theorem phaseValue_lipschitz (first second : ℝ) :
    ‖phaseValue first-phaseValue second‖≤|first-second| := by
  have hid : phaseValue first-phaseValue second=
      phaseValue second*(phaseValue (first-second)-1) := by
    unfold phaseValue
    rw [mul_sub,mul_one,←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hid,norm_mul,phaseValue_norm,one_mul]
  simpa only [phaseValue,mul_comm,Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=first-second))

theorem fourth_power_error (x y : ℂ) (hx : ‖x‖≤1) (hy : ‖y‖≤3) :
    ‖x^4-y^4‖≤40*‖x-y‖ := by
  have hid : x^4-y^4=(x-y)*(x^3+x^2*y+x*y^2+y^3) := by ring
  rw [hid,norm_mul]
  have hp : ‖x^3+x^2*y+x*y^2+y^3‖≤40 := by
    calc
      _ ≤ ‖x^3+x^2*y+x*y^2‖+‖y^3‖ := norm_add_le _ _
      _ ≤ (‖x^3+x^2*y‖+‖x*y^2‖)+‖y^3‖ := by gcongr;exact norm_add_le _ _
      _ ≤ ((‖x^3‖+‖x^2*y‖)+‖x*y^2‖)+‖y^3‖ := by gcongr;exact norm_add_le _ _
      _ = ‖x‖^3+‖x‖^2*‖y‖+‖x‖*‖y‖^2+‖y‖^3 := by simp only [norm_pow,norm_mul]
      _ ≤ 1^3+1^2*3+1*3^2+3^3 := by gcongr
      _ = 40 := by norm_num
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg (x-y))

/-- A fourth power keeps the series argument in the unit disk. All Taylor
coefficients are rational when angle is rational. -/
noncomputable def phaseTaylor (angle : ℝ) (terms : ℕ) : ℂ :=
  (taylorSum (((angle/4 : ℝ) : ℂ)*Complex.I) terms)^4

theorem phaseTaylor_error (angle : ℝ) (ha : |angle|≤4) (terms : ℕ) (ht : 0<terms) :
    ‖phaseValue angle-phaseTaylor angle terms‖≤80/(terms : ℝ) := by
  let z : ℂ := ((angle/4 : ℝ) : ℂ)*Complex.I
  have hz : ‖z‖≤1 := by
    simp only [z,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs,abs_div,Nat.abs_ofNat]
    linarith
  have herror := taylorSum_error hz ht
  have hunit : ‖Complex.exp z‖=1 := phaseValue_norm (angle/4)
  have hnorm : ‖taylorSum z terms‖≤3 := by
    have hn := norm_sub_le (taylorSum z terms) (Complex.exp z)
    have htri := norm_add_le (taylorSum z terms-Complex.exp z) (Complex.exp z)
    rw [sub_add_cancel,hunit,norm_sub_rev] at htri
    have htn : (1 : ℝ)≤terms := by exact_mod_cast ht
    have htwo : 2/(terms : ℝ)≤2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have hpower : (Complex.exp z)^4=phaseValue angle := by
    rw [←Complex.exp_nat_mul]
    unfold phaseValue z
    congr 1
    push_cast
    ring
  have hp := fourth_power_error (Complex.exp z) (taylorSum z terms) hunit.le hnorm
  rw [hpower] at hp
  change ‖phaseValue angle-phaseTaylor angle terms‖≤_ at hp
  calc
    _ ≤ 40*‖Complex.exp z-taylorSum z terms‖ := hp
    _ ≤ 40*(2/(terms : ℝ)) := mul_le_mul_of_nonneg_left herror (by norm_num)
    _ = _ := by ring

/-- A rationally supplied angle approximation propagates directly to the
complex phase target, including negative angles. -/
theorem phaseTaylor_approximate_angle (target approximate δ : ℝ)
    (ha : |approximate|≤4) (hangle : |approximate-target|≤δ)
    (terms : ℕ) (ht : 0<terms) :
    ‖phaseValue target-phaseTaylor approximate terms‖≤80/(terms : ℝ)+δ := by
  have hphase := phaseValue_lipschitz target approximate
  rw [abs_sub_comm] at hphase
  have he := hphase.trans hangle
  have htaylor := phaseTaylor_error approximate ha terms ht
  have htri := norm_sub_le_norm_sub_add_norm_sub (phaseValue target)
    (phaseValue approximate) (phaseTaylor approximate terms)
  linarith

/-- The half-angle needed by a QFT controlled phase uses only an existing
finite rational pi program and an integer power of two. -/
def rationalQFTAngle (bits gap : ℕ) : ℚ :=
  AFT.RationalNumerics.piApprox bits/(2 : ℚ)^(gap+1)

theorem rationalQFTAngle_bound (bits gap : ℕ) : |(rationalQFTAngle bits gap : ℝ)|≤4 := by
  have hpi := abs_le.mp (AFT.RationalNumerics.piApprox_error bits)
  have hpow : (1 : ℝ)≤2^bits := one_le_pow₀ (by norm_num)
  have he : 1/(2 : ℝ)^bits≤1 := (div_le_one (by positivity)).mpr hpow
  have hab : |(AFT.RationalNumerics.piApprox bits : ℝ)|≤5 :=
    abs_le.mpr ⟨by linarith [Real.pi_pos],by linarith [Real.pi_lt_four]⟩
  have hg : (2 : ℝ)≤2^(gap+1) := by
    rw [pow_succ]
    have hh : (1 : ℝ)≤2^gap := one_le_pow₀ (by norm_num)
    linarith
  simp only [rationalQFTAngle,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ)≤2^(gap+1))]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2^(gap+1))).mpr
  linarith

theorem rationalQFTAngle_error (bits gap : ℕ) :
    |(rationalQFTAngle bits gap : ℝ)-Real.pi/(2 : ℝ)^(gap+1)|≤1/(2 : ℝ)^bits := by
  have hden : (1 : ℝ)≤2^(gap+1) := one_le_pow₀ (by norm_num)
  simp only [rationalQFTAngle,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,←sub_div,
    abs_div,abs_of_nonneg (by positivity : (0 : ℝ)≤2^(gap+1))]
  exact (div_le_self (abs_nonneg _) hden).trans (AFT.RationalNumerics.piApprox_error bits)

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeNativePhaseTaylor. -/
section P2MDyadicModule37

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativePhaseTaylor

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeFiniteSeries

open FiniteGateNative FiniteGateTransport

open scoped BigOperators

theorem term_semantics (a : ℚ) (slots : List Unit) (i : ℕ) (hi : i≤ slots.length) :
    (realTerm ((a,slots),i) : ℂ)+(imagTerm ((a,slots),i) : ℂ)*Complex.I=
      ((((a : ℂ)/4)*Complex.I)^i)/(i.factorial : ℂ) := by
  have ht : termValue ((a,slots),i)=(a/4)^i/(i.factorial : ℚ) := cappedTaylor_eq (a/4) slots i hi
  rw [mul_pow,Complex.I_pow_eq_pow_mod]
  have hm : i%4<4 := Nat.mod_lt _ (by decide)
  unfold realTerm imagTerm
  interval_cases hmod : i%4 <;>
    simp [hmod,ht,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_neg,Complex.I_sq,
      Complex.I_pow_three] <;> ring

private theorem sum_range {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum=∑ i∈Finset.range n,f i := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ,List.map_append,List.sum_append,ih,
      List.map_singleton,List.sum_cons,List.sum_nil,add_zero,Finset.sum_range_succ]

theorem base_semantics (x : Input) :
    FiniteGateNative.eval (base x)=taylorSum ((((x.1 : ℝ)/4 : ℝ) : ℂ)*Complex.I) x.2.length := by
  have he : FiniteGateNative.eval (base x)=(realSum x : ℂ)+(imagSum x : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [base,FiniteGateNative.eval,FiniteGateNative.evalReal]
  rw [he]
  simp only [realSum,imagSum,sum_range,Rat.cast_sum,Finset.sum_mul,
    ←Finset.sum_add_distrib,taylorSum]
  apply Finset.sum_congr rfl
  intro i hi
  have ht := term_semantics x.1 x.2 i (Finset.mem_range.mp hi).le
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_ratCast,Prod.eta] using ht

theorem current_semantics (x : Input) :
    FiniteGateNative.eval (current x)=phaseTaylor x.1 x.2.length := by
  simp only [current,FiniteGateNative.eval_mul,base_semantics,phaseTaylor]
  ring

theorem angle_eq (x : QFTRequest) :
    angle x=rationalQFTAngle x.1.1.length x.1.2.1.length := by
  simp only [angle,powerValue,List.length_append,List.length_singleton,rationalQFTAngle]

noncomputable def targetAngle (x : QFTRequest) : ℝ :=
  if x.2 then -(Real.pi/(2 : ℝ)^(x.1.2.1.length+1)) else Real.pi/(2 : ℝ)^(x.1.2.1.length+1)

theorem signedAngle_bound (x : QFTRequest) : |(signedAngle x : ℝ)|≤4 := by
  simp only [signedAngle,angle_eq]
  split <;> simpa only [Rat.cast_neg,abs_neg] using rationalQFTAngle_bound x.1.1.length x.1.2.1.length

theorem signedAngle_error (x : QFTRequest) :
    |(signedAngle x : ℝ)-targetAngle x|≤1/(2 : ℝ)^x.1.1.length := by
  simp only [signedAngle,angle_eq,targetAngle]
  split <;> simp_all only [Rat.cast_neg,neg_sub_neg,abs_sub_comm]
  all_goals
    have h := rationalQFTAngle_error x.1.1.length x.1.2.1.length
    rw [abs_sub_comm] at h
    exact h

/-- Accuracy for the actual native rational output. All three precision
parameters are lengths of supplied finite buffers. -/
theorem qftCurrent_error (x : QFTRequest) (ht : 0<x.1.2.2.length) :
    ‖phaseValue (targetAngle x)-FiniteGateNative.eval (qftCurrent x)‖≤
      80/(x.1.2.2.length : ℝ)+1/(2 : ℝ)^x.1.1.length := by
  rw [qftCurrent,current_semantics]
  exact phaseTaylor_approximate_angle (targetAngle x) (signedAngle x) _
    (signedAngle_bound x) (signedAngle_error x) x.1.2.2.length ht

end InfoLossLAR.WorstCase.NativePhaseTaylor

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeInitializedTarget. -/
section P2MDyadicModule38

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P12

/-- Acting on the leading data wires and initializing all trailing wires is
exactly the ideal initialized map, for every matrix rather than just unitaries. -/
theorem embed_prefix_initialized {k r : ℕ} (U : Matrix (Qubits k) (Qubits k) ℂ) :
    initializedMap (n:=k) (w:=r) (embedOp U (Fin.castAddEmb r))=idealMap U r := by
  classical
  ext y x
  have hc : (∀ a : Fin (k+r),a ∉ Set.range (Fin.castAddEmb r : Fin k ↪ Fin (k+r)) →
      y a=Fin.append x (fun _ : Fin r => false) a) ↔
      (qubitsAppendEquiv k r y).2=(fun _ => false) := by
    constructor
    · intro h;funext j
      have hj : Fin.natAdd k j ∉ Set.range (Fin.castAddEmb r : Fin k ↪ Fin (k+r)) := by
        rintro ⟨i,hi⟩
        have hh := congrArg Fin.val hi
        simp only [Fin.castAddEmb_apply,Fin.val_castAdd,Fin.val_natAdd] at hh
        omega
      simpa only [qubitsAppendEquiv,Equiv.coe_fn_mk,Fin.append_right] using h (Fin.natAdd k j) hj
    · intro h a
      refine Fin.addCases (fun i ha => ?_) (fun j _ => ?_) a
      · exact False.elim (ha ⟨i,rfl⟩)
      · have hh := congrFun h j
        simpa only [qubitsAppendEquiv,Equiv.coe_fn_mk,Fin.append_right] using hh
  have hx : (Fin.append x (fun _ : Fin r => false)) ∘ (Fin.castAddEmb r : Fin k ↪ Fin (k+r))=x := by
    funext i
    simp only [Function.comp_apply,Fin.castAddEmb_apply,Fin.append_left]
  simp only [initializedMap,embedOp,idealMap,Matrix.of_apply,hc,hx]
  rfl

/-- The executable diagonal one-wire target used by the gate search has the
same rectangular initialized target as the analytic approximation theorem. -/
theorem embed_oneWire_initialized (U : Matrix Bool Bool ℂ) :
    initializedMap (n:=1) (w:=2)
      (embedOp (Gate.ofMatrix1 U).mat (oneWire (0 : Fin 3)))=
        idealMap (Gate.ofMatrix1 U).mat 2 := by
  have hw : oneWire (0 : Fin 3)=(Fin.castAddEmb 2 : Fin 1 ↪ Fin 3) := by
    ext i
    fin_cases i
    rfl
  rw [hw]
  exact embed_prefix_initialized (Gate.ofMatrix1 U).mat

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeNativePhaseGates. -/
section P2MDyadicModule39
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.NativePhaseGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport FiniteGateNative

theorem coefficient_eval (z : Scalar) (row col : Bool) :
    eval (coefficient z row col)=phaseMatrix (eval z) row col := by
  cases row <;> cases col <;> simp [coefficient,phaseMatrix,eval_one,eval_zero]

theorem target_initialized (x : NativePhaseTaylor.QFTRequest) :
    initializedNative (target x)=QAlgorithms.Papers.Independent.Renew46.P12.idealMap
      (phaseQubitMatrix (eval (NativePhaseTaylor.qftCurrent x))) 2 := by
  rw [initializedNative_eq,target,eval_singleGate _ _ (coefficient_eval _),embed_oneWire_initialized]
  rfl

noncomputable def ideal (x : NativePhaseTaylor.QFTRequest) :
    Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ :=
  phaseQubitMatrix (phaseValue (NativePhaseTaylor.targetAngle x))

theorem ideal_unitary (x : NativePhaseTaylor.QFTRequest) :
    ideal x∈Matrix.unitaryGroup (QAlgorithms.Qubits 1) ℂ :=
  phaseQubitMatrix_unitary _ (phaseValue_norm _)

theorem target_error (budget : List Unit) (x : NativePhaseTaylor.QFTRequest)
    (ht : 160*(budget.length+1)≤ x.1.2.2.length)
    (hp : 2*(budget.length+1)≤2^x.1.1.length) :
    QAlgorithms.frobNorm (initializedNative (target x)-
      QAlgorithms.Papers.Independent.Renew46.P12.idealMap (ideal x) 2)≤1/((budget.length : ℝ)+1) := by
  rw [target_initialized,ideal,initialized_phase_error,norm_sub_rev]
  have herror := NativePhaseTaylor.qftCurrent_error x (by omega)
  have hN : (0 : ℝ)<(budget.length : ℝ)+1 := by positivity
  have hterms : 160*((budget.length : ℝ)+1)≤(x.1.2.2.length : ℝ) := by exact_mod_cast ht
  have htermsPos : (0 : ℝ)<(x.1.2.2.length : ℝ) := by linarith
  have hpi : 2*((budget.length : ℝ)+1)≤(2 : ℝ)^x.1.1.length := by exact_mod_cast hp
  have htermBound : (80 : ℝ)/(x.1.2.2.length : ℝ)≤1/(2*((budget.length : ℝ)+1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have hpiBound : 1/(2 : ℝ)^x.1.1.length≤1/(2*((budget.length : ℝ)+1)) :=
    one_div_le_one_div_of_le (by positivity) hpi
  calc
    _ ≤ 80/(x.1.2.2.length : ℝ)+1/(2 : ℝ)^x.1.1.length := herror
    _ ≤ 1/(2*((budget.length : ℝ)+1))+1/(2*((budget.length : ℝ)+1)) := add_le_add htermBound hpiBound
    _ = 1/((budget.length : ℝ)+1) := by field_simp;ring

attribute [local irreducible] nativeCompile current target

theorem exists_current_accuracy :
    ∃ a : ℕ,0< a ∧ ∀ x : Input,
      160*(x.1.length+1)≤ x.2.1.2.2.length →
      2*(x.1.length+1)≤2^x.2.1.1.length →
      current a x∈FiniteGateNativeEnumeration.search a x.1 ∧
      QAlgorithms.frobNorm
        (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
          (matrix (FiniteGateNativeEnumeration.interpreted (current a x)))-
          QAlgorithms.Papers.Independent.Renew46.P12.idealMap (ideal x.2) 2)≤5/((x.1.length : ℝ)+1) := by
  obtain ⟨a,ha,haccuracy⟩ := exists_nativeCompile_accuracy
  refine ⟨a,ha,?_⟩
  intro x ht hp
  simpa only [current] using haccuracy (ideal x.2) (ideal_unitary x.2)
    x.1 (target x.2) (target_error x.1 x.2 ht hp)

theorem termBudget_length (budget : List Unit) :
    (termBudget budget).length=160*(budget.length+1) := by
  simp [termBudget,List.length_flatMap,Nat.mul_comm,Nat.add_mul]

theorem request_terms (x : AutomaticInput) :
    160*(x.1.length+1)≤(request x).1.2.2.length := by
  simp only [request,termBudget_length,le_refl]

theorem request_pi (x : AutomaticInput) :
    2*(x.1.length+1)≤2^(request x).1.1.length := by
  have hh : x.1.length+1≤2^x.1.length := by
    have h : x.1.length<2^x.1.length := Nat.lt_two_pow_self
    omega
  simpa only [request,List.length_append,List.length_singleton,pow_succ,Nat.mul_comm] using
    Nat.mul_le_mul_left 2 hh

theorem request_targetAngle (x : AutomaticInput) :
    NativePhaseTaylor.targetAngle (request x)=
      if x.2.2 then -(Real.pi/(2 : ℝ)^(x.2.1.length+1))
      else Real.pi/(2 : ℝ)^(x.2.1.length+1) := rfl

/-- This total native generator takes only a unary accuracy budget, a unary public
QFT gap, and the public sign. It generates its rational target and all precision
buffers itself, then returns an actual finite gate word. -/
theorem exists_automatic_accuracy :
    ∃ a : ℕ,0< a ∧ ∀ x : AutomaticInput,
      automatic a x∈FiniteGateNativeEnumeration.search a x.1 ∧
      QAlgorithms.frobNorm
        (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
          (matrix (FiniteGateNativeEnumeration.interpreted (automatic a x)))-
          QAlgorithms.Papers.Independent.Renew46.P12.idealMap (ideal (request x)) 2)≤5/((x.1.length : ℝ)+1) := by
  obtain ⟨a,ha,haccuracy⟩ := exists_current_accuracy
  exact ⟨a,ha,fun x => haccuracy (x.1,request x) (request_terms x) (request_pi x)⟩

end InfoLossLAR.WorstCase.NativePhaseGates

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeFreshPhaseRelocation. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity

open scoped BigOperators

/-- Only the final two fresh wires are initialized. All original data and
control wires, with arbitrary entanglement, remain in the input state. -/
noncomputable def initializeAux {n : ℕ} (ψ : QState n) : QState (n+2) :=
  fun x => if (fun j : Fin 2 => x (Fin.natAdd n j))=(fun _ => false)
    then ψ (fun j => x (Fin.castAdd 2 j)) else 0

theorem initializeAux_norm {n : ℕ} (ψ : QState n) :
    ‖(WithLp.toLp 2 (initializeAux ψ) : EuclideanSpace ℂ (Bits (n+2)))‖=
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits n))‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,initializeAux]
  have hh := Fintype.sum_equiv (qubitsAppendEquiv n 2)
    (fun x : Bits (n+2) => ‖(if (fun j : Fin 2 => x (Fin.natAdd n j))=(fun _ => false)
      then ψ (fun j => x (Fin.castAdd 2 j)) else 0 : ℂ)‖^2)
    (fun p : Bits n×Bits 2 => ‖(if p.2=(fun _ => false) then ψ p.1 else 0 : ℂ)‖^2)
    (by intro x;rfl)
  rw [hh,Fintype.sum_prod_type]
  simp only [apply_ite,norm_zero]
  simp

@[simp] theorem freshPhaseWires_aux {n : ℕ} (i : Fin n) (j : Fin 2) :
    freshPhaseWires i (Fin.natAdd 1 j)=Fin.natAdd n j := by fin_cases j <;> rfl

/-- The local data wire and every other original wire form the reference slice. -/
noncomputable def phaseInput {n : ℕ} (i : Fin n) (ψ : QState n) :
    Bits 1×OutsideBits (freshPhaseWires i) → ℂ :=
  fun p => ψ (fun j => ((wireBitsEquiv (freshPhaseWires i)).symm
    (Fin.append p.1 (fun _ : Fin 2 => false),p.2)) (j.castAdd 2))

theorem split_initializeAux {n : ℕ} (i : Fin n) (ψ : QState n) :
    splitState (freshPhaseWires i) (initializeAux ψ)=
      initWithReference (r:=2) (phaseInput i ψ) := by
  funext p
  have hw (j : Fin 3) :
      ((wireBitsEquiv (freshPhaseWires i)).symm p) (freshPhaseWires i j)=p.1 j :=
    congrFun (congrArg Prod.fst ((wireBitsEquiv (freshPhaseWires i)).apply_symm_apply p)) j
  have ha : (fun j : Fin 2 => ((wireBitsEquiv (freshPhaseWires i)).symm p) (Fin.natAdd n j))=
      (qubitsAppendEquiv 1 2 p.1).2 := by
    funext j
    rw [←freshPhaseWires_aux i j,hw]
    rfl
  change (if (fun j : Fin 2 => ((wireBitsEquiv (freshPhaseWires i)).symm p) (Fin.natAdd n j))=(fun _ => false)
    then ψ (fun j => ((wireBitsEquiv (freshPhaseWires i)).symm p) (j.castAdd 2)) else 0)=_
  rw [ha]
  unfold initWithReference phaseInput
  split_ifs with h
  · have hp : Fin.append (qubitsAppendEquiv 1 2 p.1).1 (fun _ : Fin 2 => false)=p.1 := by
      rw [←h]
      exact (qubitsAppendEquiv 1 2).symm_apply_apply p.1
    rw [hp]
  · rfl

@[simp] theorem unsplit_split {k n : ℕ} (w : Fin k ↪ Fin n) (ψ : QState n) :
    unsplitState w (splitState w ψ)=ψ := by
  funext x
  simp only [unsplitState,splitState,Equiv.symm_apply_apply]

theorem unsplit_phaseInput {n : ℕ} (i : Fin n) (ψ : QState n) :
    unsplitState (freshPhaseWires i) (initWithReference (r:=2) (phaseInput i ψ))=initializeAux ψ := by
  rw [←split_initializeAux,unsplit_split]

theorem phaseInput_norm {n : ℕ} (i : Fin n) (ψ : QState n) :
    ‖(WithLp.toLp 2 (phaseInput i ψ) : EuclideanSpace ℂ (Bits 1×OutsideBits (freshPhaseWires i)))‖=
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits n))‖ := by
  calc
    _ = ‖(WithLp.toLp 2 (initWithReference (r:=2) (phaseInput i ψ)) :
        EuclideanSpace ℂ (Bits 3×OutsideBits (freshPhaseWires i)))‖ := (initWithReference_norm _).symm
    _ = _ := by rw [←split_initializeAux,splitState_norm,initializeAux_norm]

theorem fresh_suffix_update {n : ℕ} (i : Fin n) (x : Bits (n+2)) (b : Bool) :
    (fun j : Fin 2 => Function.update x (i.castAdd 2) b (Fin.natAdd n j))=
      (fun j : Fin 2 => x (Fin.natAdd n j)) := by
  funext j
  have hn : Fin.natAdd n j≠i.castAdd 2 := by intro h;have hv:=congrArg Fin.val h;dsimp at hv;omega
  exact Function.update_of_ne hn b x

theorem fresh_prefix_update {n : ℕ} (i : Fin n) (x : Bits (n+2)) (b : Bool) :
    (fun j : Fin n => Function.update x (i.castAdd 2) b (j.castAdd 2))=
      Function.update (fun j : Fin n => x (j.castAdd 2)) i b := by
  funext j
  by_cases h : j=i
  · subst j;simp
  · have hn : j.castAdd 2≠i.castAdd 2 := by intro he;apply h;exact Fin.castAdd_inj.mp he
    simp only [Function.update_of_ne hn,Function.update_of_ne h]

theorem initializeAux_apply1 {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ) (ψ : QState n) :
    initializeAux (apply1 U i ψ)=apply1 U (i.castAdd 2) (initializeAux ψ) := by
  funext x
  simp only [initializeAux,apply1,fresh_suffix_update,fresh_prefix_update]
  split_ifs <;> simp_all

theorem initializeAux_cnot {n : ℕ} (i j : Fin n) (hij : i≠j) (ψ : QState n) :
    initializeAux (cnotState i j hij ψ)=
      cnotState (i.castAdd 2) (j.castAdd 2) (by intro h;apply hij;exact Fin.castAdd_inj.mp h)
        (initializeAux ψ) := by
  funext x
  simp only [initializeAux,cnotState,fresh_suffix_update,fresh_prefix_update]

def prefixInstr {n : ℕ} : Instr n → Instr (n+2)
  | .h i => .h (i.castAdd 2)
  | .s i => .s (i.castAdd 2)
  | .t i => .t (i.castAdd 2)
  | .x i => .x (i.castAdd 2)
  | .cnot i j h => .cnot (i.castAdd 2) (j.castAdd 2) (by intro he;apply h;exact Fin.castAdd_inj.mp he)

theorem initializeAux_instr {n : ℕ} (g : Instr n) (ψ : QState n) :
    initializeAux (g.apply ψ)=(prefixInstr g).apply (initializeAux ψ) := by
  cases g with
  | h i => exact initializeAux_apply1 i _ ψ
  | s i => exact initializeAux_apply1 i _ ψ
  | t i => exact initializeAux_apply1 i _ ψ
  | x i => exact initializeAux_apply1 i _ ψ
  | cnot i j h => exact initializeAux_cnot i j h ψ

theorem initializeAux_runLayer {n : ℕ} (gates : List (Instr n)) (ψ : QState n) :
    initializeAux (runLayer gates ψ)=runLayer (gates.map prefixInstr) (initializeAux ψ) := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g rest ih => simpa only [runLayer,List.foldl_cons,List.map_cons,initializeAux_instr] using ih (g.apply ψ)

theorem initializeAux_phase {n : ℕ} (i : Fin n) (z : ℂ) (ψ : QState n) :
    initializeAux (apply1 (phaseMatrix z) i ψ)=
      apply1 (phaseMatrix z) (i.castAdd 2) (initializeAux ψ) := by
  funext x
  simp only [phaseMatrix_apply,initializeAux]
  split_ifs <;> simp_all

theorem initWithReference_phase {R : Type*} (z : ℂ) (ψ : Bits 1×R → ℂ) (p : Bits 3×R) :
    initWithReference (r:=2) (applyWithReference (phaseQubitMatrix z) ψ) p=
      if p.1 0 then z*initWithReference (r:=2) ψ p else initWithReference (r:=2) ψ p := by
  simp only [initWithReference,applyWithReference,phaseQubitMatrix_diagonal,Matrix.mulVec_diagonal]
  change (if _ then (if p.1 0 then z else 1)*_ else 0)=_
  split_ifs <;> simp_all

theorem unsplit_phase {n : ℕ} (i : Fin n) (z : ℂ) (ψ : QState n) :
    unsplitState (freshPhaseWires i) (initWithReference (r:=2)
      (applyWithReference (phaseQubitMatrix z) (phaseInput i ψ)))=
      initializeAux (apply1 (phaseMatrix z) i ψ) := by
  rw [initializeAux_phase]
  funext x
  change initWithReference (k:=1) (r:=2) _ ((wireBitsEquiv (freshPhaseWires i)) x)=_
  rw [initWithReference_phase,phaseMatrix_apply]
  have hw : ((wireBitsEquiv (freshPhaseWires i)) x).1 0=x (i.castAdd 2) := rfl
  rw [hw]
  have hh := congrFun (unsplit_phaseInput i ψ) x
  change initWithReference (k:=1) (r:=2) (phaseInput i ψ) ((wireBitsEquiv (freshPhaseWires i)) x)=_ at hh
  rw [hh]
  split_ifs <;> simp_all

/-- The same last two zero ancillas can be shared across calls. The input
may entangle the phase target with every original data/control wire. -/
theorem fresh_phase_word_error {n : ℕ} (i : Fin n) (word : List (Letter 3))
    (z : ℂ) (error : ℝ)
    (h : frobNorm (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (matrix word)-
      QAlgorithms.Papers.Independent.Renew46.P12.idealMap (phaseQubitMatrix z) 2)≤ error)
    (ψ : QState n) :
    ‖(WithLp.toLp 2 (runLayer (instructions (word.map (Letter.relocate (freshPhaseWires i))))
      (initializeAux ψ)-initializeAux (apply1 (phaseMatrix z) i ψ)) :
      EuclideanSpace ℂ (Bits (n+2)))‖≤ error*‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits n))‖ := by
  have hh :=relocate_initialized_error (k:=1) (r:=2) (n:=n+2)
    (freshPhaseWires i) word (phaseQubitMatrix z) error h (phaseInput i ψ)
  rw [unsplit_phaseInput,unsplit_phase,phaseInput_norm] at hh
  exact hh

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeControlledHadamard. -/
section P2MDyadicModule41

set_option autoImplicit false

set_option maxHeartbeats 2400000

namespace InfoLossLAR.WorstCase.ControlledHadamard

open QAlgorithms QAlgorithms.Complexity

open FiniteGateNative

abbrev Mat2 := Bool→Bool→Scalar

def mul2 (A B : Mat2) : Mat2 := fun i j =>
  add (mul (A i false) (B false j)) (mul (A i true) (B true j))

def star2 (A : Mat2) : Mat2 := fun i j => conj (A j i)

noncomputable def eval2 (A : Mat2) : Matrix Bool Bool ℂ := fun i j => eval (A i j)

def S : Mat2 := fun i j => if i=j then (if i then ((0,0),(1,0)) else one) else zero

def turn : Mat2 := mul2 S (mul2 hCoefficient (mul2 tCoefficient (mul2 hCoefficient (star2 S))))

theorem eval2_mul (A B : Mat2) : eval2 (mul2 A B)=eval2 A*eval2 B := by
  ext i j
  simp only [eval2,mul2,eval_add,eval_mul,Matrix.mul_apply,Fintype.sum_bool]
  ring

theorem eval2_star (A : Mat2) : eval2 (star2 A)=star (eval2 A) := by
  ext i j
  simp only [eval2,star2,eval_conj,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]

theorem eval2_H : eval2 hCoefficient=hMat := by ext i j;exact eval_hCoefficient i j

theorem eval2_T : eval2 tCoefficient=tMat := by ext i j;exact eval_tCoefficient i j

theorem eval2_S : eval2 S=sMat := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;> norm_num [eval2,S,eval,evalReal,one,zero,sMat]

noncomputable def V : Matrix Bool Bool ℂ := sMat*hMat*tMat*hMat*star sMat

theorem eval2_turn : eval2 turn=V := by
  simp only [turn,eval2_mul,eval2_star,eval2_H,eval2_T,eval2_S,V,Matrix.mul_assoc]

def X : Mat2 := fun i j => if i=j then zero else one

def controlTurn : Mat2 := mul2 turn hCoefficient

theorem controlTurn_conjugates_X : mul2 controlTurn (mul2 X (star2 controlTurn))=hCoefficient := by
  funext i j
  cases i <;> cases j <;> decide +kernel

theorem controlTurn_unitary : mul2 controlTurn (star2 controlTurn)=fun i j => if i=j then one else zero := by
  funext i j
  cases i <;> cases j <;> decide +kernel

theorem eval2_X : eval2 X=xMat := by
  ext i j
  cases i <;> cases j <;> simp [eval2,X,xMat,eval_one,eval_zero]

noncomputable def W : Matrix Bool Bool ℂ := V*hMat

theorem eval2_controlTurn : eval2 controlTurn=W := by
  simp only [controlTurn,eval2_mul,eval2_turn,eval2_H,W]

theorem W_unitary : W∈Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := congrArg eval2 controlTurn_unitary
  rw [eval2_mul,eval2_star,eval2_controlTurn] at h
  convert h using 1
  ext i j
  cases i <;> cases j <;> simp [eval2,Matrix.one_apply,eval_one,eval_zero]

theorem W_conjugates_X : W*xMat*star W=hMat := by
  have h := congrArg eval2 controlTurn_conjugates_X
  simpa only [eval2_mul,eval2_star,eval2_controlTurn,eval2_X,eval2_H,Matrix.mul_assoc] using h

/-- Controlled action on a target wire. The control and every other wire
remain in the state, so the definition applies to arbitrary superpositions. -/
noncomputable def controlled {n : ℕ} (U : Matrix Bool Bool ℂ) (c t : Fin n)
    (ψ : QState n) : QState n := fun x => if x c then apply1 U t ψ x else ψ x

theorem apply1_control_split {n : ℕ} (U : Matrix Bool Bool ℂ) (c t : Fin n) (hct : c≠t)
    (ψ φ : QState n) : apply1 U t (fun x => if x c then ψ x else φ x)=
      fun x => if x c then apply1 U t ψ x else apply1 U t φ x := by
  funext x
  cases hc : x c <;> simp [apply1,Function.update_of_ne hct,hc]

theorem controlled_conjugate {n : ℕ} (U Z V : Matrix Bool Bool ℂ)
    (c t : Fin n) (hct : c≠t) (ψ : QState n) :
    apply1 U t (controlled Z c t (apply1 V t ψ))=
      fun x => if x c then apply1 (U*Z*V) t ψ x else apply1 (U*V) t ψ x := by
  unfold controlled
  rw [apply1_control_split U c t hct]
  simp only [apply1_comp,Matrix.mul_assoc]

theorem controlled_X {n : ℕ} (c t : Fin n) (hct : c≠t) (ψ : QState n) :
    controlled xMat c t ψ=cnotState c t hct ψ := by
  funext x
  cases hc : x c <;> cases ht : x t <;>
    simp [controlled,apply1,xMat,cnotState,hc,ht]
  all_goals rw [←ht,Function.update_eq_self]

theorem W_sandwich_cnot {n : ℕ} (c t : Fin n) (hct : c≠t) (ψ : QState n) :
    apply1 W t (cnotState c t hct (apply1 (star W) t ψ))=controlled hMat c t ψ := by
  rw [←controlled_X,controlled_conjugate W xMat (star W) c t hct,W_conjugates_X,
    Matrix.mem_unitaryGroup_iff.mp W_unitary,apply1_one]
  rfl

theorem sMat_cube : sMat^3=star sMat := by
  ext i j
  cases i <;> cases j <;>
    norm_num [pow_succ,Matrix.mul_apply,sMat,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]

def turnWord {n : ℕ} (t : Fin n) : List (Instr n) :=
  [.h t]++List.replicate 3 (.s t)++[.h t,.t t,.h t,.s t]

theorem turnWord_semantics {n : ℕ} (t : Fin n) (ψ : QState n) :
    runLayer (turnWord t) ψ=apply1 W t ψ := by
  simp only [turnWord,runLayer_append,runLayer_replicate,Instr.apply,apply1_iterate,sMat_cube]
  simp only [runLayer,List.foldl_cons,List.foldl_nil,Instr.apply,apply1_comp,W,V,Matrix.mul_assoc]

theorem inverse_turnWord_semantics {n : ℕ} (t : Fin n) (ψ : QState n) :
    runLayer (inverseGates (turnWord t)) ψ=apply1 (star W) t ψ := by
  have h := inverseGates_left (turnWord t) (apply1 (star W) t ψ)
  rw [turnWord_semantics,apply1_comp,Matrix.mem_unitaryGroup_iff.mp W_unitary,apply1_one] at h
  exact h

/-- A fixed exact native gate sequence for controlled Hadamard. -/
def gates {n : ℕ} (c t : Fin n) (hct : c≠t) : List (Instr n) :=
  inverseGates (turnWord t)++[.cnot c t hct]++turnWord t

theorem gates_semantics {n : ℕ} (c t : Fin n) (hct : c≠t) (ψ : QState n) :
    runLayer (gates c t hct) ψ=controlled hMat c t ψ := by
  rw [gates,runLayer_append,runLayer_append,inverse_turnWord_semantics,turnWord_semantics]
  change apply1 W t (cnotState c t hct (apply1 (star W) t ψ))=_
  exact W_sandwich_cnot c t hct ψ

end InfoLossLAR.WorstCase.ControlledHadamard

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeQFTPhaseCircuit. -/
section P2MDyadicModule42

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity

theorem phaseValue_neg (angle : ℝ) : phaseValue (-angle)=(phaseValue angle)⁻¹ := by
  simp only [phaseValue,Complex.ofReal_neg,neg_mul,Complex.exp_neg]

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeControlledLetterPlan. -/
section P2MDyadicModule43

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ControlledLetterPlan

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

/-- Only the fixed public eighth-turn phase remains to be synthesized. -/
inductive Atom (n : ℕ) where
  | native (gate : Instr n)
  | eighth (i : Fin n) (negative : Bool)

noncomputable def Atom.apply {n : ℕ} : Atom n → QState n → QState n
  | .native gate => gate.apply
  | .eighth i negative =>
    apply1 (phaseMatrix (phaseValue (if negative then -(Real.pi/8) else Real.pi/8))) i

noncomputable def run {n : ℕ} (atoms : List (Atom n)) (ψ : QState n) : QState n :=
  atoms.foldl (fun state atom => atom.apply state) ψ

theorem run_native {n : ℕ} (gates : List (Instr n)) (ψ : QState n) :
    run (gates.map Atom.native) ψ=runLayer gates ψ := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons gate rest ih => exact ih (gate.apply ψ)

def Avoids {n : ℕ} (c : Fin n) : Letter n → Prop
  | .h i => c≠i
  | .t i => c≠i
  | .cnot i j _ => c≠i ∧ c≠j

def plan {n : ℕ} (c : Fin n) (gate : Letter n) (h : Avoids c gate) : List (Atom n) :=
  match gate with
  | .h i => (ControlledHadamard.gates c i h).map Atom.native
  | .t i => [.eighth c false,.eighth i false,.native (.cnot c i h),.eighth i true,.native (.cnot c i h)]
  | .cnot i j hij => (toffoliGates c i j h.1 h.2 hij).map Atom.native

noncomputable def controlled {n : ℕ} (c : Fin n) (gate : Letter n) (ψ : QState n) : QState n :=
  fun x => if x c then gate.toInstr.apply ψ x else ψ x

theorem phase_quarter_T : phaseMatrix (phaseValue (Real.pi/4))=tMat := by
  have h : phaseValue (Real.pi/4)=Complex.exp (Complex.I*Real.pi/4) := by
    unfold phaseValue
    congr 1
    push_cast
    ring
  ext i j
  cases i <;> cases j <;> simp [phaseMatrix,tMat,h,Matrix.diagonal_apply]

theorem controlled_phase_T {n : ℕ} (c t : Fin n) (ψ : QState n) :
    controlledPhase (phaseValue (Real.pi/4)) c t ψ=controlled c (.t t) ψ := by
  funext x
  simp only [controlled,Letter.toInstr,Instr.apply,←phase_quarter_T,phaseMatrix_apply,controlledPhase]
  cases x c <;> cases x t <;> simp

theorem runLayered_singletons {n : ℕ} (gates : List (Instr n)) (ψ : QState n) :
    runLayered (gates.map (fun g => [g])) ψ=runLayer gates ψ := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons gate rest ih => exact ih (gate.apply ψ)

theorem toffoliGates_semantics {n : ℕ} (c i j : Fin n) (hci : c≠i) (hcj : c≠j) (hij : i≠j)
    (ψ : QState n) : runLayer (toffoliGates c i j hci hcj hij) ψ=
      fun x => ψ (Function.update x j (xor (x j) (x c && x i))) := by
  rw [←runLayered_singletons]
  exact toffoliCircuit_apply c i j hci hcj hij ψ

/-- Every atom sequence controls the complete physical instruction. The
statement holds with arbitrary entanglement in the control and work registers. -/
theorem plan_semantics {n : ℕ} (c : Fin n) (gate : Letter n) (h : Avoids c gate) (ψ : QState n) :
    run (plan c gate h) ψ=controlled c gate ψ := by
  cases gate with
  | h i =>
    rw [plan,run_native,ControlledHadamard.gates_semantics]
    rfl
  | t i =>
    simp only [plan,run,List.foldl_cons,List.foldl_nil,Atom.apply,Instr.apply,Bool.false_eq_true,if_false,if_true]
    rw [phaseValue_neg,controlledPhase_decomposition (phaseValue (Real.pi/8)) (Complex.exp_ne_zero _) c i h ψ,phaseValue_sq]
    have he : 2*(Real.pi/8)=Real.pi/4 := by ring
    rw [he,controlled_phase_T]
  | cnot i j hij =>
    rw [plan,run_native,toffoliGates_semantics]
    funext x
    cases hc : x c <;> simp [controlled,Letter.toInstr,Instr.apply,cnotState,hc,Function.update_eq_self]

end InfoLossLAR.WorstCase.ControlledLetterPlan

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeControlledNativeCode. -/
section P2MDyadicModule44

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

end InfoLossLAR.WorstCase.ControlledNativeCode

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeControlledNativeGates. -/
section P2MDyadicModule45

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledNativeGates

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan

open scoped BigOperators

noncomputable def eighthAngle (negative : Bool) : ℝ := if negative then -(Real.pi/8) else Real.pi/8

def eighthWord (a : ℕ) (budget : List Unit) (negative : Bool) : List (Letter 3) :=
  FiniteGateNativeEnumeration.interpreted (NativePhaseGates.automatic a (budget,([(),()],negative)))

def PhaseAccurate (a : ℕ) : Prop := ∀ (budget : List Unit) (negative : Bool),
  frobNorm (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (matrix (eighthWord a budget negative))-
    QAlgorithms.Papers.Independent.Renew46.P12.idealMap (phaseQubitMatrix (phaseValue (eighthAngle negative))) 2)≤
      5/((budget.length : ℝ)+1)

theorem exists_parameter : ∃ a : ℕ,0< a ∧ PhaseAccurate a := by
  obtain ⟨a,ha,haccuracy⟩ :=NativePhaseGates.exists_automatic_accuracy
  refine ⟨a,ha,?_⟩
  intro budget negative
  have hh :=(haccuracy (budget,([(),()],negative))).2
  simpa only [PhaseAccurate,eighthWord,NativePhaseGates.ideal,NativePhaseGates.request_targetAngle,
    List.length_cons,List.length_nil,show (2 : ℝ)^(0+1+1+1)=8 by norm_num,eighthAngle] using hh

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

theorem layer_norm {n : ℕ} (word : List (Instr n)) (ψ : QState n) :
    stateNorm (runLayer word ψ)=stateNorm ψ := by
  exact (circuitIsometry [word]).norm_map (WithLp.toLp 2 ψ)

theorem layer_distance {n : ℕ} (word : List (Instr n)) (ψ φ : QState n) :
    stateNorm (runLayer word ψ-runLayer word φ)=stateNorm (ψ-φ) := by
  change ‖(circuitIsometry [word]) (WithLp.toLp 2 ψ)-(circuitIsometry [word]) (WithLp.toLp 2 φ)‖=
    ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits n))-WithLp.toLp 2 φ‖
  rw [←map_sub,(circuitIsometry [word]).norm_map]

theorem atom_norm {n : ℕ} (atom : Atom n) (ψ : QState n) : stateNorm (atom.apply ψ)=stateNorm ψ := by
  cases atom with
  | native gate => exact layer_norm [gate] ψ
  | eighth i negative =>
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change stateNorm (apply1 (phaseMatrix (phaseValue (eighthAngle negative))) i ψ)^2=stateNorm ψ^2
    simp only [stateNorm,EuclideanSpace.norm_sq_eq,phaseMatrix_apply]
    apply Finset.sum_congr rfl
    intro x _
    cases hx : x i <;> simp [phaseValue_norm]

def phaseCount {n : ℕ} : List (Atom n) → ℕ
  | [] => 0
  | .native _::rest => phaseCount rest
  | .eighth _ _::rest => phaseCount rest+1

theorem phaseCount_native {n : ℕ} (word : List (Instr n)) : phaseCount (word.map Atom.native)=0 := by
  induction word with
  | nil => rfl
  | cons gate rest ih => exact ih

theorem atom_error {n : ℕ} (a : ℕ) (ha : PhaseAccurate a) (budget : List Unit) (atom : Atom n)
    (ψ : QState n) :
    stateNorm (runLayer (atomGates a budget atom) (initializeAux ψ)-initializeAux (atom.apply ψ))≤
      (phaseCount [atom] : ℝ)*(5/((budget.length : ℝ)+1))*stateNorm ψ := by
  cases atom with
  | native gate =>
    simp only [atomGates,runLayer,List.foldl_cons,List.foldl_nil,Atom.apply,←initializeAux_instr,
      sub_self,phaseCount,Nat.cast_zero,zero_mul,stateNorm,WithLp.toLp_zero,norm_zero,le_refl]
  | eighth i negative =>
    simpa only [atomGates,Atom.apply,phaseCount,Nat.cast_add,Nat.cast_zero,Nat.cast_one,
      zero_add,one_mul,eighthAngle,stateNorm] using
      fresh_phase_word_error i (eighthWord a budget negative) (phaseValue (eighthAngle negative))
        (5/((budget.length : ℝ)+1)) (ha budget negative) ψ

/-- Ideal prefixes return both shared ancillary wires to zero. Actual
ancillary leakage is retained and propagated by later unitary gates. -/
theorem gates_error {n : ℕ} (a : ℕ) (ha : PhaseAccurate a) (budget : List Unit)
    (atoms : List (Atom n)) (ψ : QState n) :
    stateNorm (runLayer (gates a budget atoms) (initializeAux ψ)-initializeAux (run atoms ψ))≤
      (phaseCount atoms : ℝ)*(5/((budget.length : ℝ)+1))*stateNorm ψ := by
  induction atoms generalizing ψ with
  | nil => simp [gates,run,runLayer,phaseCount,stateNorm]
  | cons atom rest ih =>
    have htri :=norm_sub_le_norm_sub_add_norm_sub
      (WithLp.toLp 2 (runLayer (gates a budget rest) (runLayer (atomGates a budget atom) (initializeAux ψ))) :
        EuclideanSpace ℂ (Bits (n+2)))
      (WithLp.toLp 2 (runLayer (gates a budget rest) (initializeAux (atom.apply ψ))))
      (WithLp.toLp 2 (initializeAux (run rest (atom.apply ψ))))
    change stateNorm (runLayer (gates a budget rest) (runLayer (atomGates a budget atom) (initializeAux ψ))-
      initializeAux (run rest (atom.apply ψ)))≤
      stateNorm (runLayer (gates a budget rest) (runLayer (atomGates a budget atom) (initializeAux ψ))-
        runLayer (gates a budget rest) (initializeAux (atom.apply ψ)))+
      stateNorm (runLayer (gates a budget rest) (initializeAux (atom.apply ψ))-initializeAux (run rest (atom.apply ψ))) at htri
    rw [layer_distance] at htri
    have htail :=ih (atom.apply ψ)
    rw [atom_norm] at htail
    have hhead :=atom_error a ha budget atom ψ
    have hh :=htri.trans (add_le_add hhead htail)
    change stateNorm (runLayer (atomGates a budget atom++gates a budget rest) (initializeAux ψ)-
      initializeAux (run rest (atom.apply ψ)))≤ _
    rw [runLayer,List.foldl_append]
    change stateNorm (runLayer (gates a budget rest) (runLayer (atomGates a budget atom) (initializeAux ψ))-
      initializeAux (run rest (atom.apply ψ)))≤ _
    convert hh using 1 <;> first
    | rfl
    | (cases atom <;> simp [phaseCount] <;> ring)

theorem plan_phaseCount {n : ℕ} (control : Fin n) (letter : Letter n) (h : Avoids control letter) :
    phaseCount (plan control letter h)≤3 := by
  cases letter with
  | h i => rw [plan,phaseCount_native];omega
  | t i => norm_num [plan,phaseCount]
  | cnot i j hij => rw [plan,phaseCount_native];omega

end InfoLossLAR.WorstCase.ControlledNativeGates

end P2MDyadicModule45

/- Helper module Solutions.RegevBridgeCoherentProjection. -/
section P2MDyadicModule46

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

noncomputable def project {X : Type*} [Fintype X]
    (event : X → Prop) [DecidablePred event] (ψ : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => if event x then ψ x else 0)

theorem projection_error_sq {X : Type*} [Fintype X]
    (event : X → Prop) [DecidablePred event] (ψ : EuclideanSpace ℂ X) :
    ‖ψ-project event ψ‖^2=∑ x,if event x then 0 else ‖ψ x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : event x <;> simp [project,h]

/-- A small failure branch gives closeness to the normalized complete
success vector; it is not silently removed by postselection. -/
theorem normalized_success_close {X : Type*} [Fintype X]
    (event : X → Prop) [DecidablePred event] (ψ : EuclideanSpace ℂ X)
    (hψ : ‖ψ‖=1) (hgood : project event ψ≠0) (ε : ℝ)
    (hfailure : (∑ x,if event x then 0 else ‖ψ x‖^2)≤ε) :
    ‖ψ-normalized (project event ψ)‖≤2*Real.sqrt ε := by
  have hs : ‖ψ-project event ψ‖≤Real.sqrt ε := by
    apply (Real.le_sqrt (norm_nonneg _) (by
      exact (Finset.sum_nonneg (fun x _ => by split_ifs <;> positivity)).trans hfailure)).mpr
    rw [projection_error_sq]
    exact hfailure
  exact (normalized_close ψ _ hψ hgood).trans (mul_le_mul_of_nonneg_left hs (by norm_num))

theorem tensorState_norm {O J : Type*} [Fintype O] [Fintype J]
    (target : EuclideanSpace ℂ O) (junk : EuclideanSpace ℂ J) :
    ‖tensorState target junk‖=‖target‖*‖junk‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  simp only [tensorState,Fintype.sum_prod_type,norm_mul,mul_pow]
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul]

theorem normalized_tensor {O J : Type*} [Fintype O] [Fintype J]
    (target : EuclideanSpace ℂ O) (junk : EuclideanSpace ℂ J) (ht : ‖target‖=1) :
    normalized (tensorState target junk)=tensorState target (normalized junk) := by
  rw [normalized,tensorState_norm,ht,one_mul]
  ext p
  simp only [tensorState,PiLp.smul_apply,normalized]
  change (‖junk‖⁻¹ : ℝ) • (target p.1*junk p.2)=target p.1*((‖junk‖⁻¹ : ℝ) • junk p.2)
  rw [Algebra.smul_def,Algebra.smul_def]
  ring

/-- When the complete success branch factors at amplitude level, the
unconditional output is close to a pure target tensored with normalized junk. -/
theorem pure_success_close {O J : Type*} [Fintype O] [Fintype J]
    (event : O×J → Prop) [DecidablePred event] (ψ : EuclideanSpace ℂ (O×J))
    (target : EuclideanSpace ℂ O) (junk : EuclideanSpace ℂ J)
    (hψ : ‖ψ‖=1) (ht : ‖target‖=1) (hj : junk≠0)
    (hfactor : project event ψ=tensorState target junk) (ε : ℝ)
    (hfailure : (∑ x,if event x then 0 else ‖ψ x‖^2)≤ε) :
    ∃ clean : EuclideanSpace ℂ J,‖clean‖=1 ∧
      ‖ψ-tensorState target clean‖≤2*Real.sqrt ε := by
  refine ⟨normalized junk,normalized_norm junk hj,?_⟩
  have hn : tensorState target junk≠0 := by
    intro hzero
    have hnorm := tensorState_norm target junk
    rw [hzero,norm_zero,ht,one_mul] at hnorm
    exact hj (norm_eq_zero.mp hnorm.symm)
  have h := normalized_success_close event ψ hψ (by rwa [hfactor]) ε hfailure
  rw [hfactor,normalized_tensor target junk ht] at h
  exact h

end InfoLossLAR.WorstCase.CoherentProjection

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeControlledPlanNative. -/
section P2MDyadicModule47

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledPlanNative

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

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

end P2MDyadicModule47

/- Helper module Solutions.RegevBridgeNativeWordControls. -/
section P2MDyadicModule48

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.NativeWordControls

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport FiniteGateNativeEnumeration

theorem normalizedCode_lt (code : ℕ) : normalizedCode code<12 := by
  unfold normalizedCode
  split <;> omega

theorem normalizedCode_semantics (code : ℕ) :
    letterOfCode (normalizedCode code)=letterOfCode code := by
  by_cases h : code<12
  · simp [normalizedCode,h]
  · have hh : FiniteGateTransport.alphabet.length≤code := by
      have : 12≤code := Nat.le_of_not_gt h
      simpa only [FiniteGateTransport.alphabet_length] using this
    simp only [normalizedCode,if_neg h,letterOfCode,List.getElem?_eq_none hh,Option.getD_none]
    rfl

theorem inactive_all_false (x : Input) (slot : ℕ) (hslot : x.1.length ≤ slot) (code : ℕ) :
    selected (x,(slot,code))=false := by
  simp [selected,Nat.not_lt.mpr hslot]

end InfoLossLAR.WorstCase.NativeWordControls

end P2MDyadicModule48

/- Helper module Solutions.RegevBridgeNativeWordControlSemantics. -/
section P2MDyadicModule49

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.NativeWordControls

open FiniteGateTransport FiniteGateNativeEnumeration

private theorem filterMap_single {α β : Type*} [DecidableEq α]
    (xs : List α) (a : α) (f : α → β) (hnd : xs.Nodup) (ha : a∈xs) :
    xs.filterMap (fun x => if a=x then some (f x) else none)=[f a] := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.nodup_cons.mp hnd
    by_cases h : a=x
    · subst x
      have hrest : xs.filterMap (fun x => if a=x then some (f x) else none)=[] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro x hmem
        have hh : a≠x := by intro hh;subst x;exact hx hmem
        simp [hh]
      simp [hrest]
    · have hat : a∈xs := (List.mem_cons.mp ha).resolve_left h
      simp only [List.filterMap_cons,if_neg h]
      exact ih ht hat

/-- Interpret the twelve physical one-hot controls at one program position. -/
def rowWord (x : Input) (slot : ℕ) : List (Letter 3) :=
  (List.range 12).filterMap (fun code =>
    if selected (x,(slot,code)) then some (letterOfCode code) else none)

theorem rowWord_active (x : Input) (slot : ℕ) (hslot : slot<x.1.length) :
    rowWord x slot=[letterOfCode x.1[slot]] := by
  unfold rowWord
  have hfun (code : ℕ) :
      (if selected (x,(slot,code)) then some (letterOfCode code) else none)=
      (if normalizedCode (x.1[slot]?.getD 0)=code then some (letterOfCode code) else none) := by
    simp [selected,hslot]
  simp_rw [hfun]
  rw [filterMap_single _ _ _ List.nodup_range (List.mem_range.mpr (normalizedCode_lt _))]
  rw [normalizedCode_semantics,List.getElem?_eq_getElem hslot,Option.getD_some]

theorem rowWord_inactive (x : Input) (slot : ℕ) (hslot : x.1.length ≤ slot) :
    rowWord x slot=[] := by
  unfold rowWord
  apply List.filterMap_eq_nil_iff.mpr
  intro code _
  simp only [inactive_all_false x slot hslot code,Bool.false_eq_true,if_false]

def prefixWord (x : Input) (slots : ℕ) : List (Letter 3) :=
  (List.range slots).flatMap (rowWord x)

/-- Every finite buffer interprets exactly its available prefix, including
zero gates on padded positions and the compiler's specified fallback codes. -/
theorem prefixWord_eq (x : Input) (slots : ℕ) :
    prefixWord x slots=(x.1.take slots).map letterOfCode := by
  induction slots with
  | zero => simp [prefixWord]
  | succ n ih =>
    simp only [prefixWord,List.range_succ,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil] at *
    rw [ih,List.take_add_one,List.map_append]
    by_cases hn : n<x.1.length
    · rw [rowWord_active x n hn,List.getElem?_eq_getElem hn]
      rfl
    · rw [rowWord_inactive x n (Nat.le_of_not_gt hn),List.getElem?_eq_none (Nat.le_of_not_gt hn)]
      rfl

theorem complete_word (x : Input) (hbound : x.1.length≤x.2.length) :
    prefixWord x x.2.length=interpreted x.1 := by
  rw [prefixWord_eq,List.take_of_length_le hbound]
  rfl

end InfoLossLAR.WorstCase.NativeWordControls

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule50

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

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule51

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

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule52

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

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule53

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

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule54

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

end P2MDyadicModule54

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule55

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

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule56

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

end P2MDyadicModule56

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule57

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

/- Helper module Solutions.AdvantageBridgeQuantumCoins. -/
section P2MDyadicModule59

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

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

section Description

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

end Description

end InfoLossLAR.WorstCase

end P2MDyadicModule59

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule60

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

end P2MDyadicModule60

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule61

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

end P2MDyadicModule61

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule62

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

end PolyProgramCircuit

end InfoLossLAR.WorstCase.TM2Boolean

end

end P2MDyadicModule62

/- Helper module Solutions.RegevBridgeNativeWordControlProgram. -/
section P2MDyadicModule63

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.NativeWordControls

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

theorem rawControls_length (x : Input) : (rawControls x).length=12*x.2.length := by
  simp [rawControls]

theorem rawControls_get (x : Input) (slot code : ℕ)
    (hs : slot<x.2.length) (hc : code<12) :
    (rawControls x)[12*slot+code]'(by rw [rawControls_length];omega)=selected (x,(slot,code)) := by
  simp only [rawControls,List.getElem_map,List.getElem_range]
  have hd : (12*slot+code)/12=slot := by omega
  have hm : (12*slot+code)%12=code := by omega
  rw [hd,hm]

theorem rawCurrent_length (words : Str → List ℕ) (p : Polynomial ℕ) (word : Str) :
    (rawCurrent words p word).length=12*p.eval word.length := by
  simp only [rawCurrent,rawControls_length,List.length_replicate]

end InfoLossLAR.WorstCase.NativeWordControls

end P2MDyadicModule63

/- Helper module Solutions.AdvantageBridgeBoundedUniform. -/
section P2MDyadicModule64

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase

open AFT

open scoped BigOperators Classical

/-- A single joint rejection attempt succeeds with probability at least one half. -/
theorem boundedFinSuccess_half (count : ℕ) (hcount : 0<count) :
    (1/2 : ℝ) ≤ boundedFinSuccess count := by
  have hs : 0<Nat.size count := Nat.size_pos.mpr hcount
  have hm : Nat.size count-1<Nat.size count := by omega
  have hpow : 2^(Nat.size count-1) ≤ count := Nat.lt_size.mp hm
  have hsucc : Nat.size count-1+1=Nat.size count := by omega
  have hcap : 2^Nat.size count ≤ 2*count := by
    calc
      _ = 2^(Nat.size count-1)*2 := by
        simpa only [Nat.succ_eq_add_one,hsucc] using Nat.pow_succ 2 (Nat.size count-1)
      _ ≤ count*2 := Nat.mul_le_mul_right 2 hpow
      _ = _ := Nat.mul_comm _ _
  have hcap' : (2 : ℝ)^Nat.size count ≤ 2*(count : ℝ) := by exact_mod_cast hcap
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^Nat.size count)).mpr
  nlinarith

end InfoLossLAR.WorstCase

end P2MDyadicModule64

/- Helper module Solutions.AdvantageBridgeCoinMachine. -/
section P2MDyadicModule65

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

end P2MDyadicModule65

/- Helper module Solutions.AdvantageBridgeQueryQuantum. -/
section P2MDyadicModule66

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

end P2MDyadicModule66

/- Helper module Solutions.AdvantageBridgeQueryMetadata. -/
section P2MDyadicModule67

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

theorem outputSlotIndex_eq (width : ℕ) (index : Fin width) :
    outputSlotIndex P width index.val=
      (slotEquiv P.machine.K P.machine.Label P.machine.State width
        (.inr (.inr (P.machine.output,index,some true)))).val :=
  (slot_stack_index width P.machine.output index (some true)).symm

theorem generatedOutputAddress_eq (x : Request) (hw : 0<x.2.1.length) (index : Fin x.2.1.length) :
    generatedOutputAddress P x index.val=
      (machineProgram hw P.machine.code P.machine.input P.machine.main P.machine.initial
        x.2.2.length x.1.length).output (.inr (.inr (P.machine.output,index,some true))) := by
  unfold generatedOutputAddress
  rw [outputSlotIndex_eq]
  exact (generate_machineProgram P.machine.code P.machine.input P.machine.main P.machine.initial x hw).2.2 _

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

end P2MDyadicModule67

/- Helper module Solutions.RegevBridgeNativeWordControlCircuit. -/
section P2MDyadicModule68

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeWordControls

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit Integration9_9.TM2OutputLength

/-- The physical output wire of the reversible native computation carries the
selected one-hot bit for every well-addressed program slot. -/
theorem rawCurrent_wire (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)
    (word : Str) (slot code : ℕ) (hs : slot<p.eval word.length) (hc : code<12) :
    ∃ i : Fin (capacity (rawCurrentProgram words hw p) word.length),
      i.val=12*slot+code ∧
      result (rawCurrentProgram words hw p) word
        (outputWire (rawCurrentProgram words hw p) word.length i (some true))=
        selected ((words word,List.replicate (p.eval word.length) ()),(slot,code)) := by
  let P := rawCurrentProgram words hw p
  have hlen : 12*p.eval word.length<capacity P word.length := by
    simpa only [rawCurrent_length] using actualOutput_length_lt_capacity P word
  let i : Fin (capacity P word.length) := ⟨12*slot+code,by omega⟩
  refine ⟨i,rfl,?_⟩
  rw [output_correct]
  have hin : 12*slot+code<(rawCurrent words p word).length := by rw [rawCurrent_length];omega
  rw [List.getElem?_eq_getElem hin]
  change decide (some true=some ((rawControls (words word,
    List.replicate (p.eval word.length) ()))[12*slot+code]))=_
  rw [rawControls_get _ slot code (by simpa only [List.length_replicate] using hs) hc]
  simp

end InfoLossLAR.WorstCase.NativeWordControls

end P2MDyadicModule68

/- Helper module Solutions.RegevBridgeControlledRelocation. -/
section P2MDyadicModule69

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

theorem spectator_value {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : {c : Fin n // c ∉ Set.range w}) (p : Bits k×OutsideBits w) :
    (wireBitsEquiv w).symm p c.val=p.2 c := by
  have h := congrArg Prod.snd ((wireBitsEquiv w).apply_symm_apply p)
  exact congrFun h c

/-- Pull one actual controlled plan into data/reference coordinates. The
reference may itself be in arbitrary coherent superposition. -/
theorem plan_split {k n : ℕ} (w : Fin k ↪ Fin n) (op : Operation w) (ψ : QState n) :
    splitState w (run (plan op.1.val (op.2.relocate w) (outside_avoids w op.1 op.2)) ψ)=
      fun p => if p.2 op.1 then op.2.toInstr.apply (fun j => splitState w ψ (j,p.2)) p.1
        else splitState w ψ p := by
  rw [plan_semantics]
  funext p
  change (if (wireBitsEquiv w).symm p op.1.val then
    (op.2.relocate w).toInstr.apply ψ ((wireBitsEquiv w).symm p) else
    ψ ((wireBitsEquiv w).symm p))=_
  rw [spectator_value]
  have h := congrFun (Letter.relocate_split w op.2 ψ) p
  change (op.2.relocate w).toInstr.apply ψ ((wireBitsEquiv w).symm p)=_ at h
  rw [h]
  rfl

def program {k n : ℕ} (w : Fin k ↪ Fin n) (ops : List (Operation w)) : List (Atom n) :=
  ops.flatMap (fun op => plan op.1.val (op.2.relocate w) (outside_avoids w op.1 op.2))

def branchWord {k n : ℕ} {w : Fin k ↪ Fin n}
    (ops : List (Operation w)) (reference : OutsideBits w) : List (Letter k) :=
  ops.filterMap (fun op => if reference op.1 then some op.2 else none)

theorem run_append {n : ℕ} (a b : List (Atom n)) (ψ : QState n) :
    run (a++b) ψ=run b (run a ψ) := List.foldl_append

/-- A fixed physical plan coherently interprets every reference-selected
subsequence. It realizes branchwise gate words, not a classical mixture. -/
theorem program_split {k n : ℕ} (w : Fin k ↪ Fin n)
    (ops : List (Operation w)) (ψ : QState n) :
    splitState w (run (program w ops) ψ)=fun p =>
      runLayer (instructions (branchWord ops p.2)) (fun j => splitState w ψ (j,p.2)) p.1 := by
  induction ops generalizing ψ with
  | nil => rfl
  | cons op rest ih =>
    simp only [program,List.flatMap_cons,run_append]
    rw [show run ((rest.flatMap fun op => plan op.1.val (op.2.relocate w)
        (outside_avoids w op.1 op.2)))=
        run (program w rest) from rfl]
    rw [ih,plan_split]
    funext p
    cases h : p.2 op.1 <;>
      simp only [branchWord,List.filterMap_cons,h,if_false,if_true,Bool.false_eq_true,
        instructions,List.map_cons,runLayer,List.foldl_cons]
    all_goals rfl

end InfoLossLAR.WorstCase.ControlledRelocation

end P2MDyadicModule69

/- Helper module Solutions.RegevBridgeControlledWordInterpreter. -/
section P2MDyadicModule70

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

theorem operationGrid_length {n : ℕ} (w : Fin 3 ↪ Fin n)
    (controls : ℕ → ℕ → {c : Fin n // c∉Set.range w}) (slots : ℕ) :
    (operationGrid w controls slots).length=12*slots := by
  simp [operationGrid,List.length_flatMap]
  omega

/-- Each coherent reference branch supplies its own complete program word. -/
theorem branchWord_eq {n : ℕ} (w : Fin 3 ↪ Fin n)
    (controls : ℕ → ℕ → {c : Fin n // c∉Set.range w}) (x : Input)
    (reference : OutsideBits w)
    (hcontrols : ∀ slot<x.2.length,∀ code<12,
      reference (controls slot code)=selected (x,(slot,code))) :
    branchWord (operationGrid w controls x.2.length) reference=prefixWord x x.2.length := by
  simp only [branchWord,operationGrid,List.filterMap_flatMap,List.filterMap_map,prefixWord]
  apply List.flatMap_congr
  intro slot hs
  apply List.filterMap_congr
  intro code hc
  simp only [Function.comp_def]
  rw [hcontrols slot (List.mem_range.mp hs) code (List.mem_range.mp hc)]

/-- A fixed gate plan interprets a different native word on every coherent
program branch and preserves the reference register. -/
theorem interpret_word {n : ℕ} (w : Fin 3 ↪ Fin n)
    (controls : ℕ → ℕ → {c : Fin n // c∉Set.range w}) (slots : List Unit)
    (words : OutsideBits w → List ℕ)
    (hbound : ∀ r,(words r).length ≤ slots.length)
    (ψ : QState n)
    (hcontrols : ∀ r,(∃ j,splitState w ψ (j,r)≠0) →
      ∀ slot,slot<slots.length → ∀ code,code<12 →
      r (controls slot code)=selected ((words r,slots),(slot,code)))
    :
    splitState w (ControlledLetterPlan.run
      (program w (operationGrid w controls slots.length)) ψ)=
      fun p => runLayer (instructions (interpreted (words p.2)))
        (fun j => splitState w ψ (j,p.2)) p.1 := by
  rw [program_split]
  funext p
  classical
  by_cases hactive : ∃ j,splitState w ψ (j,p.2)≠0
  · rw [branchWord_eq w controls (words p.2,slots) p.2 (hcontrols p.2 hactive),
      complete_word (words p.2,slots) (hbound p.2)]
  · have hz : (fun j => splitState w ψ (j,p.2))=(0 : QState 3) := by
      funext j
      exact not_not.mp (fun hj => hactive ⟨j,hj⟩)
    rw [hz,←runLayerLinearMap_apply,←runLayerLinearMap_apply]
    simp only [map_zero]

end InfoLossLAR.WorstCase.ControlledWordInterpreter

end P2MDyadicModule70

/- Helper module Solutions.RegevBridgeNativeWordLayout. -/
section P2MDyadicModule71

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

theorem slots_length (word : Str) : (slots p word).length=p.eval word.length := by
  simp only [slots,List.length_replicate]

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

end InfoLossLAR.WorstCase.NativeWordLayout

end

end P2MDyadicModule71

/- Helper module Solutions.RegevBridgeNativeWordLayoutSemantics. -/
section P2MDyadicModule72

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

theorem typedGrid_length (n : ℕ) : (typedGrid P p n).length=12*p.eval n :=
  ControlledWordInterpreter.operationGrid_length _ _ _

theorem phaseCount_append {n : ℕ} (first rest : List (Atom n)) :
    phaseCount (first++rest)=phaseCount first+phaseCount rest := by
  induction first with
  | nil => simp [phaseCount]
  | cons atom tail ih => cases atom <;> simp only [List.cons_append,phaseCount,ih] <;> omega

theorem program_phaseCount {k n : ℕ} (w : Fin k ↪ Fin n) (ops : List (Operation w)) :
    phaseCount (program w ops)≤3*ops.length := by
  induction ops with
  | nil => simp [program,phaseCount]
  | cons op rest ih =>
    change phaseCount (plan op.1.val (op.2.relocate w) (outside_avoids w op.1 op.2)++program w rest)≤ _
    rw [phaseCount_append]
    have hh :=plan_phaseCount op.1.val (op.2.relocate w) (outside_avoids w op.1 op.2)
    simp only [List.length_cons]
    omega

theorem idealAtoms_phaseCount (n : ℕ) : phaseCount (idealAtoms P p n)≤36*p.eval n := by
  have hh:=program_phaseCount (dataWires P n) (typedGrid P p n)
  rw [typedGrid_length] at hh
  change phaseCount (program (dataWires P n) (typedGrid P p n))≤ _
  nlinarith

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

/-- A complete public operation grid approximates the exact coherent word
interpreter. The physical error includes the machine, data, reference, and
both shared auxiliary output wires, with no dimension loss. -/
theorem current_error (hfit : SlotsFit P p) (n a : ℕ) (ha : PhaseAccurate a)
    (budget : List Unit) (ψ : QState (width P n+3)) :
    stateNorm (runLayer ((current P p a (unary n,budget)).filterMap (decodeGate (width P n+3+2)))
        (initializeAux ψ)-initializeAux (run (idealAtoms P p n) ψ))≤
      (180*((p.eval n : ℕ) : ℝ)/((budget.length : ℝ)+1))*stateNorm ψ := by
  rw [current_decode P p hfit n a budget]
  have hh:=gates_error a ha budget (idealAtoms P p n) ψ
  have hc : (phaseCount (idealAtoms P p n) : ℝ)≤36*((p.eval n : ℕ) : ℝ) := by
    exact_mod_cast idealAtoms_phaseCount P p n
  have hd : (0 : ℝ)≤5/((budget.length : ℝ)+1) := by positivity
  calc
    _ ≤ (phaseCount (idealAtoms P p n) : ℝ)*(5/((budget.length : ℝ)+1))*stateNorm ψ := hh
    _ ≤ (36*((p.eval n : ℕ) : ℝ))*(5/((budget.length : ℝ)+1))*stateNorm ψ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hd) (norm_nonneg _)
    _ = _ := by ring

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

end P2MDyadicModule72

/- Helper module Solutions.RegevBridgeDependentGateError. -/
section P2MDyadicModule73

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms

open scoped BigOperators

/-- A coherently retained classical reference may select a different local
matrix on every basis branch. No measurement or mixture is performed. -/
noncomputable def applyDependentReference {m n r : Type*} [Fintype n]
    (A : r → Matrix m n ℂ) (ψ : n×r → ℂ) : m×r → ℂ :=
  fun pair => (A pair.2).mulVec (fun j => ψ (j,pair.2)) pair.1

theorem applyDependentReference_sub {m n r : Type*} [Fintype n]
    (A B : r → Matrix m n ℂ) (ψ : n×r → ℂ) :
    applyDependentReference (fun k => A k-B k) ψ=
      applyDependentReference A ψ-applyDependentReference B ψ := by
  funext p
  simp only [applyDependentReference,Matrix.sub_mulVec,Pi.sub_apply]

/-- Pointwise compiler errors combine in squared norm on a superposition of
program inputs. Every reference slice, including its phase, is retained. -/
theorem applyDependentReference_error_sq {m n r : Type*}
    [Fintype m] [Fintype n] [Fintype r]
    (A B : r → Matrix m n ℂ) (error : r → ℝ) (_herror : ∀ k,0≤error k)
    (hlocal : ∀ k,frobNorm (A k-B k)≤error k) (ψ : n×r → ℂ) :
    ‖(WithLp.toLp 2 (applyDependentReference A ψ-applyDependentReference B ψ) :
      EuclideanSpace ℂ (m×r))‖^2≤
      ∑ k : r,(error k)^2*‖(WithLp.toLp 2 (fun j => ψ (j,k)) : EuclideanSpace ℂ n)‖^2 := by
  rw [←applyDependentReference_sub,norm_sq_slices]
  apply Finset.sum_le_sum
  intro k _
  have hk := (mulVec_error_bound (A k-B k) (fun j => ψ (j,k))).trans
    (mul_le_mul_of_nonneg_right (hlocal k) (norm_nonneg _))
  have hp := pow_le_pow_left₀ (norm_nonneg _) hk 2
  simpa only [applyDependentReference,mul_pow] using hp

/-- A uniform initialized-map bound remains uniform for input-dependent
compiled words in coherent superposition, with no reference-dimension loss. -/
theorem applyDependentReference_error {m n r : Type*}
    [Fintype m] [Fintype n] [Fintype r]
    (A B : r → Matrix m n ℂ) (error : ℝ) (herror : 0≤error)
    (hlocal : ∀ k,frobNorm (A k-B k)≤error) (ψ : n×r → ℂ) :
    ‖(WithLp.toLp 2 (applyDependentReference A ψ-applyDependentReference B ψ) :
      EuclideanSpace ℂ (m×r))‖≤
      error*‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (n×r))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg herror (norm_nonneg _))).mp
  rw [mul_pow]
  have h := applyDependentReference_error_sq A B (fun _ => error) (fun _ => herror) hlocal ψ
  rw [←Finset.mul_sum,←norm_sq_slices] at h
  exact h

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule73

/- Helper module Solutions.RegevBridgeCoherentComputeUncompute. -/
section P2MDyadicModule74

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

end P2MDyadicModule74

/- Helper module Solutions.RegevBridgeNativeWordCoherent. -/
section P2MDyadicModule75

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan ControlledRelocation

open NativeWordLayout ControlledNativeGates

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

/-- The complete work basis, including every arithmetic and program cell,
is retained alongside an arbitrary three-qubit data vector. -/
def workTensor {W : ℕ} (work : Bits W) (v : QState 3) : QState (W+3) :=
  fun x => v (fun j => x (Fin.natAdd W j))*CoherentComputeUncompute.basis work (fun j => x (j.castAdd 3))

def oldWire (W : ℕ) (i : Fin W) : {c : Fin (W+3) // c∉Set.range (Fin.natAddEmb W : Fin 3 ↪ Fin (W+3))} :=
  ⟨i.castAdd 3,by rintro ⟨j,h⟩;have hv:=congrArg Fin.val h;change W+j.val=i.val at hv;omega⟩

def referenceWork {W : ℕ} (r : OutsideBits (Fin.natAddEmb W : Fin 3 ↪ Fin (W+3))) : Bits W :=
  fun i => r (oldWire W i)

theorem split_workTensor {W : ℕ} (work : Bits W) (v : QState 3)
    (pair : Bits 3×OutsideBits (Fin.natAddEmb W : Fin 3 ↪ Fin (W+3))) :
    splitState (Fin.natAddEmb W) (workTensor work v) pair=
      v pair.1*CoherentComputeUncompute.basis work (referenceWork pair.2) := by
  have hd (i : Fin 3) : ((wireBitsEquiv (Fin.natAddEmb W)).symm pair) (Fin.natAdd W i)=pair.1 i :=
    congrFun (congrArg Prod.fst ((wireBitsEquiv (Fin.natAddEmb W)).apply_symm_apply pair)) i
  have hw (i : Fin W) : ((wireBitsEquiv (Fin.natAddEmb W)).symm pair) (i.castAdd 3)=pair.2 (oldWire W i) :=
    spectator_value (Fin.natAddEmb W) (oldWire W i) pair
  change v (fun i => ((wireBitsEquiv (Fin.natAddEmb W)).symm pair) (Fin.natAdd W i))*
    CoherentComputeUncompute.basis work (fun i => ((wireBitsEquiv (Fin.natAddEmb W)).symm pair) (i.castAdd 3))=_
  rw [show (fun i => ((wireBitsEquiv (Fin.natAddEmb W)).symm pair) (Fin.natAdd W i))=pair.1 by funext i;exact hd i]
  rw [show (fun i => ((wireBitsEquiv (Fin.natAddEmb W)).symm pair) (i.castAdd 3))=referenceWork pair.2 by funext i;exact hw i]

def atomLinearMap {n : ℕ} (atom : Atom n) : QState n →ₗ[ℂ] QState n where
  toFun :=atom.apply
  map_add' ψ φ := by
    cases atom with
    | native gate => exact (instrLinearMap gate).map_add ψ φ
    | eighth i negative => funext x;simp [Atom.apply,apply1,mul_add,Finset.sum_add_distrib]
  map_smul' c ψ := by
    cases atom with
    | native gate => exact (instrLinearMap gate).map_smul c ψ
    | eighth i negative => funext x;simp [Atom.apply,apply1,mul_left_comm,←Finset.mul_sum]

def runLinearMap {n : ℕ} (atoms : List (Atom n)) : QState n →ₗ[ℂ] QState n :=
  atoms.foldl (fun U atom => (atomLinearMap atom).comp U) LinearMap.id

@[simp] theorem runLinearMap_apply {n : ℕ} (atoms : List (Atom n)) (ψ : QState n) :
    runLinearMap atoms ψ=run atoms ψ := by
  have hh (rest : List (Atom n)) (U : QState n →ₗ[ℂ] QState n) :
      rest.foldl (fun V atom => (atomLinearMap atom).comp V) U ψ=run rest (U ψ) := by
    induction rest generalizing U with
    | nil => rfl
    | cons atom tail ih =>
      simpa only [List.foldl_cons,run,atomLinearMap,LinearMap.comp_apply,LinearMap.coe_mk,AddHom.coe_mk] using
        ih ((atomLinearMap atom).comp U)
  exact hh atoms LinearMap.id

theorem run_sum {n : ℕ} {I : Type*} [Fintype I] (atoms : List (Atom n)) (ψ : I → QState n) :
    run atoms (∑ i,ψ i)=∑ i,run atoms (ψ i) := by
  simpa only [runLinearMap_apply] using map_sum (runLinearMap atoms) ψ Finset.univ

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

theorem computed_control (word : Str) (slot code : ℕ) (hs : slot< p.eval word.length) (hc : code<12) :
    result (P words hw p) word
      (outputWire (P words hw p) word.length (controlIndex (P words hw p) word.length slot code) (some true))=
      NativeWordControls.selected ((words word,List.replicate (p.eval word.length) ()),(slot,code)) := by
  obtain ⟨index,hi,hvalue⟩ :=NativeWordControls.rawCurrent_wire words hw p word slot code hs hc
  have hcap : 12*p.eval word.length<capacity (P words hw p) word.length := rawSlotsFit words hw p word.length
  have hin : 12*slot+code< capacity (P words hw p) word.length := by omega
  have he : index=controlIndex (P words hw p) word.length slot code := by
    apply Fin.ext
    rw [hi]
    simp only [controlIndex,dif_pos hin]
  simpa only [he] using hvalue

theorem reference_computed_control (word : Str)
    (r : OutsideBits (dataWires (P words hw p) word.length))
    (hr : referenceWork r=result (P words hw p) word)
    (slot code : ℕ) (hs : slot< p.eval word.length) (hc : code<12) :
    r (controls (P words hw p) word.length slot code)=
      NativeWordControls.selected ((words word,List.replicate (p.eval word.length) ()),(slot,code)) := by
  have hh:=congrFun hr (outputWire (P words hw p) word.length
    (controlIndex (P words hw p) word.length slot code) (some true))
  change r (controls (P words hw p) word.length slot code)=_ at hh
  rw [hh]
  exact computed_control words hw p word slot code hs hc

theorem runLayer_scale {n : ℕ} (gates : List (Instr n)) (v : QState n) (c : ℂ) :
    runLayer gates (fun x => v x*c)=(fun x => runLayer gates v x*c) := by
  have he : (fun x => v x*c)=c • v := by funext x;simp [mul_comm]
  rw [he,←runLayerLinearMap_apply,map_smul]
  rw [runLayerLinearMap_apply]
  funext x
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

/-- The true computed work basis selects the native word of the original
input. The entire work basis is returned unchanged, with arbitrary data. -/
theorem interpret_computed_word (word : Str) (v : QState 3)
    (hbound : (words word).length≤ p.eval word.length) :
    run (idealAtoms (P words hw p) p word.length) (workTensor (result (P words hw p) word) v)=
      workTensor (result (P words hw p) word)
        (runLayer (instructions (FiniteGateNativeEnumeration.interpreted (words word))) v) := by
  let prog :=P words hw p
  let slots :=List.replicate (p.eval word.length) ()
  have hh :=ControlledWordInterpreter.interpret_word (dataWires prog word.length) (controls prog word.length)
    slots (fun _ => words word) (by intro r;simpa only [slots,List.length_replicate] using hbound)
    (workTensor (result prog word) v) (by
      intro r hactive slot hs code hc
      obtain ⟨j,hj⟩ :=hactive
      unfold dataWires width at *
      rw [split_workTensor] at hj
      have hr : referenceWork r=result prog word := by
        by_contra hn
        simp only [CoherentComputeUncompute.basis,if_neg hn,mul_zero] at hj
        exact hj rfl
      exact reference_computed_control words hw p word r hr slot code
        (by simpa only [slots,List.length_replicate] using hs) hc)
  have hslots : slots.length=p.eval word.length := List.length_replicate
  rw [hslots] at hh
  change splitState (dataWires prog word.length) (run (idealAtoms prog p word.length)
      (workTensor (result prog word) v))=_ at hh
  apply (fun h => congrArg (unsplitState (dataWires prog word.length)) h) at hh
  rw [unsplit_split] at hh
  rw [hh]
  apply funext
  intro x
  let pair :=wireBitsEquiv (dataWires prog word.length) x
  have hpoint :
      runLayer (instructions (FiniteGateNativeEnumeration.interpreted (words word)))
        (fun j => splitState (dataWires prog word.length) (workTensor (result prog word) v) (j,pair.2)) pair.1=
      splitState (dataWires prog word.length)
        (workTensor (result prog word)
          (runLayer (instructions (FiniteGateNativeEnumeration.interpreted (words word))) v)) pair := by
    unfold dataWires width at *
    simp only [split_workTensor]
    rw [runLayer_scale]
  change _=workTensor (result prog word) _ x
  have he:=congrFun (unsplit_split (dataWires prog word.length)
    (workTensor (result prog word) (runLayer (instructions (FiniteGateNativeEnumeration.interpreted (words word))) v))) x
  exact hpoint.trans he

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule75

/- Helper module Solutions.RegevBridgeNativeWordCoherentCompute. -/
section P2MDyadicModule76

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

theorem assemble_norm (W k : ℕ) (φ : Bits k×Bits W → ℂ) :
    stateNorm (assembleMap W k φ)=‖(WithLp.toLp 2 φ : EuclideanSpace ℂ (Bits k×Bits W))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [stateNorm,EuclideanSpace.norm_sq_eq]
  exact Fintype.sum_equiv ((qubitsAppendEquiv W k).trans (Equiv.prodComm _ _)) _ _ (by intro x;rfl)

@[simp] theorem assemble_tensor {W : ℕ} (v : QState 3) (work : Bits W) :
    assembleMap W 3 (CoherentComputeUncompute.tensor v work)=workTensor work v := rfl

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

def resultAt (n : ℕ) (word : Str) (hword : word.length=n) : Bits (width (P words hw p) n) :=
  hword ▸ result (P words hw p) word

theorem basis_computes (n : ℕ) (word : Str) (hword : word.length=n) :
    runLayeredLinearMap (circuit (P words hw p) n)
      (CoherentComputeUncompute.basis (initialWork words hw p n word))=
      CoherentComputeUncompute.basis (resultAt words hw p n word hword) := by
  subst n
  have hh:=circuit_basis (P words hw p) word
  rw [basisInput_eq_computationalBasis,wordExtension_basis] at hh
  rw [runLayeredLinearMap_apply]
  change runLayered (circuit (P words hw p) word.length)
    (computationalBasis (fun i => wordExtension word i.val))=computationalBasis (result (P words hw p) word)
  exact hh

theorem interpret_resultAt (n : ℕ) (word : Str) (hword : word.length=n)
    (v : QState 3) (hbound : (words word).length≤ p.eval n) :
    run (idealAtoms (P words hw p) p n) (workTensor (resultAt words hw p n word hword) v)=
      workTensor (resultAt words hw p n word hword)
        (runLayer (instructions (FiniteGateNativeEnumeration.interpreted (words word))) v) := by
  subst n
  exact interpret_computed_word words hw p word v hbound

/-- The actual full reversible native computation is an isometry even when
its input is entangled with the complete data/reference register. -/
theorem onWork_circuit_norm (n k : ℕ) (φ : Bits k×Bits (width (P words hw p) n) → ℂ) :
    ‖(WithLp.toLp 2 (CoherentComputeUncompute.onWork (runLayeredLinearMap (circuit (P words hw p) n)) φ) :
      EuclideanSpace ℂ (Bits k×Bits (width (P words hw p) n)))‖=
      ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ (Bits k×Bits (width (P words hw p) n)))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro data _
  have hn :=(circuitIsometry (circuit (P words hw p) n)).norm_map
    (WithLp.toLp 2 (fun work => φ (data,work)))
  change ‖(WithLp.toLp 2 (runLayered (circuit (P words hw p) n) (fun work => φ (data,work))) :
    EuclideanSpace ℂ (Bits (width (P words hw p) n)))‖=
    ‖(WithLp.toLp 2 (fun work => φ (data,work)) : EuclideanSpace ℂ (Bits (width (P words hw p) n)))‖ at hn
  have hh:=congrArg (fun x : ℝ => x^2) hn
  unfold width at *
  simpa only [EuclideanSpace.norm_sq_eq,CoherentComputeUncompute.onWork,
    LinearMap.coe_mk,AddHom.coe_mk,runLayeredLinearMap_apply] using hh

variable {I : Type*} [Fintype I]

def initialState (n : ℕ) (input : I → Str) (v : I → QState 3) : QState (width (P words hw p) n+3) :=
  assembleMap _ 3 (∑ i,CoherentComputeUncompute.tensor (v i) (initialWork words hw p n (input i)))

/-- This is the actual native circuit applied to an arbitrary coherent sum
of original inputs and data vectors, with only its fresh work initialized. -/
def computedState (n : ℕ) (input : I → Str) (v : I → QState 3) : QState (width (P words hw p) n+3) :=
  assembleMap _ 3 (CoherentComputeUncompute.onWork (runLayeredLinearMap (circuit (P words hw p) n))
    (∑ i,CoherentComputeUncompute.tensor (v i) (initialWork words hw p n (input i))))

theorem computedState_norm (n : ℕ) (input : I → Str) (v : I → QState 3) :
    stateNorm (computedState words hw p n input v)=stateNorm (initialState words hw p n input v) := by
  unfold computedState initialState
  rw [assemble_norm,assemble_norm,onWork_circuit_norm]

section
attribute [local irreducible] TM2Boolean.PolyProgramCircuit.circuit
theorem computedState_eq (n : ℕ) (input : I → Str) (hlen : ∀ i,(input i).length=n) (v : I → QState 3) :
    computedState words hw p n input v=
      ∑ i,workTensor (resultAt words hw p n (input i) (hlen i)) (v i) := by
  unfold computedState
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (assembleMap (width (P words hw p) n) 3)
    (CoherentComputeUncompute.onWork_tensor (W:=Bits (width (P words hw p) n))
      (runLayeredLinearMap (circuit (P words hw p) n)) (v i)
      (initialWork words hw p n (input i)) (resultAt words hw p n (input i) (hlen i))
      (basis_computes words hw p n (input i) (hlen i)))

end

/-- Relative phases between every input component are retained. No work
register is traced out or replaced by a measurement distribution. -/
theorem interpret_superposition (n : ℕ) (input : I → Str) (hlen : ∀ i,(input i).length=n)
    (v : I → QState 3) (hbound : ∀ i,(words (input i)).length≤ p.eval n) :
    run (idealAtoms (P words hw p) p n) (computedState words hw p n input v)=
      ∑ i,workTensor (resultAt words hw p n (input i) (hlen i))
        (runLayer (instructions (FiniteGateNativeEnumeration.interpreted (words (input i)))) (v i)) := by
  rw [computedState_eq words hw p n input hlen v,run_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact interpret_resultAt words hw p n (input i) (hlen i) (v i) (hbound i)

/-- The actually emitted finite gate code replaces the entire coherent native
word execution. Its error is measured against the original input norm and
retains all machine, data, and shared ancillary output amplitudes. -/
theorem finite_execution_error (n a : ℕ) (ha : PhaseAccurate a)
    (budget : List Unit) (input : I → Str) (hlen : ∀ i,(input i).length=n)
    (v : I → QState 3) (hbound : ∀ i,(words (input i)).length≤ p.eval n) :
    stateNorm (runLayer
        ((NativeWordLayout.current (P words hw p) p a (unary n,budget)).filterMap
          (ControlledNativeCode.decodeGate (width (P words hw p) n+3+2)))
        (initializeAux (computedState words hw p n input v))-
      initializeAux (∑ i,workTensor (resultAt words hw p n (input i) (hlen i))
        (runLayer (instructions (FiniteGateNativeEnumeration.interpreted (words (input i)))) (v i))))≤
      (180*((p.eval n : ℕ) : ℝ)/((budget.length : ℝ)+1))*stateNorm (initialState words hw p n input v) := by
  have hh:=NativeWordLayout.current_error (P words hw p) p (rawSlotsFit words hw p) n a ha budget
    (computedState words hw p n input v)
  rw [interpret_superposition words hw p n input hlen v hbound,computedState_norm] at hh
  exact hh

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule76

/- Helper module Solutions.RegevBridgeNativeWordLift. -/
section P2MDyadicModule77

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

theorem onWork_layer_norm {W : ℕ} (gates : Layered W) (k : ℕ) (φ : Bits k×Bits W → ℂ) :
    ‖(WithLp.toLp 2 (CoherentComputeUncompute.onWork (runLayeredLinearMap gates) φ) :
      EuclideanSpace ℂ (Bits k×Bits W))‖=‖(WithLp.toLp 2 φ : EuclideanSpace ℂ (Bits k×Bits W))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro data _
  have hn:=(circuitIsometry gates).norm_map (WithLp.toLp 2 (fun work => φ (data,work)))
  change ‖(WithLp.toLp 2 (runLayered gates (fun work => φ (data,work))) : EuclideanSpace ℂ (Bits W))‖=
    ‖(WithLp.toLp 2 (fun work => φ (data,work)) : EuclideanSpace ℂ (Bits W))‖ at hn
  have hh:=congrArg (fun x : ℝ => x^2) hn
  simpa only [EuclideanSpace.norm_sq_eq,CoherentComputeUncompute.onWork,
    LinearMap.coe_mk,AddHom.coe_mk,runLayeredLinearMap_apply] using hh

theorem workAction_norm {W : ℕ} (gates : Layered W) (k : ℕ) (ψ : QState (W+k)) :
    ControlledNativeGates.stateNorm (workAction gates k ψ)=ControlledNativeGates.stateNorm ψ := by
  change ControlledNativeGates.stateNorm (assembleMap W k
    (CoherentComputeUncompute.onWork (runLayeredLinearMap gates) (separateMap W k ψ)))=_
  rw [assemble_norm,onWork_layer_norm]
  have hh:=assemble_norm W k (separateMap W k ψ)
  rw [assemble_separate] at hh
  exact hh.symm

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule77

/- Helper module Solutions.RegevBridgeNativeWordCleanup. -/
section P2MDyadicModule78

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

private theorem initializeAux_circuit {n : ℕ} (gates : Layered n) (ψ : QState n) :
    initializeAux (runLayered gates ψ)=
      runLayered (gates.map (List.map prefixInstr)) (initializeAux ψ) := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons layer rest ih =>
    change initializeAux (runLayered rest (runLayer layer ψ))=
      runLayered (rest.map (List.map prefixInstr)) (runLayer (layer.map prefixInstr) (initializeAux ψ))
    rw [ih,initializeAux_runLayer]

private theorem prefix_extend_three {W : ℕ} (gate : Instr W) :
    prefixInstr (extendInstr 3 gate)=extendInstr 5 gate := by cases gate <;> rfl

private theorem prefix_circuit_three {W : ℕ} (gates : Layered W) :
    (extendCircuit 3 gates).map (List.map prefixInstr)=extendCircuit 5 gates := by
  simp only [extendCircuit,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  exact prefix_extend_three gate

/-- Only the ideal state has zero new auxiliaries. Actual leaked amplitudes
are propagated by the full five-reference-wire isometry. -/
theorem workAction_initializeAux {W : ℕ} (gates : Layered W) (ψ : QState (W+3)) :
    workAction gates 5 (initializeAux ψ)=initializeAux (workAction gates 3 ψ) := by
  rw [←extendCircuit_semantics,←extendCircuit_semantics]
  rw [initializeAux_circuit,prefix_circuit_three]

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

variable {I : Type*} [Fintype I]

def dataResult (word : Str) (v : QState 3) : QState 3 :=
  runLayer (instructions (FiniteGateNativeEnumeration.interpreted (words word))) v

def cleanState (n : ℕ) (input : I → Str) (v : I → QState 3) : QState (width (P words hw p) n+3) :=
  ∑ i,workTensor (initialWork words hw p n (input i)) (dataResult words (input i) (v i))

def idealComputedState (n : ℕ) (input : I → Str) (hlen : ∀ i,(input i).length=n) (v : I → QState 3) :
    QState (width (P words hw p) n+3) :=
  ∑ i,workTensor (resultAt words hw p n (input i) (hlen i)) (dataResult words (input i) (v i))

theorem inverse_computed_basis (n : ℕ) (word : Str) (hlen : word.length=n) :
    runLayeredLinearMap (inverseCircuit (baseCircuit words hw p n))
      (CoherentComputeUncompute.basis (resultAt words hw p n word hlen))=
      CoherentComputeUncompute.basis (initialWork words hw p n word) :=
  CoherentComputeUncompute.inverse_basis (baseCircuit words hw p n) _ _
    (basis_computes words hw p n word hlen)

section
set_option maxHeartbeats 450000
attribute [local irreducible] TM2Boolean.PolyProgramCircuit.circuit NativeWordLayout.width

/-- The real inverse of the same machine clears every computed cell and
restores the original input basis, with all input/data phases intact. -/
theorem uncompute_ideal (n : ℕ) (input : I → Str) (hlen : ∀ i,(input i).length=n) (v : I → QState 3) :
    workAction (inverseCircuit (baseCircuit words hw p n)) 3
      (idealComputedState words hw p n input hlen v)=cleanState words hw p n input v := by
  have he : idealComputedState words hw p n input hlen v=
      assembleMap _ 3 (∑ i,CoherentComputeUncompute.tensor (dataResult words (input i) (v i))
        (resultAt words hw p n (input i) (hlen i))) := by
    simp only [idealComputedState,map_sum,assemble_tensor]
  rw [he]
  simp only [workAction, LinearMap.comp_apply,separate_assemble,map_sum,cleanState]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (assembleMap (width (P words hw p) n) 3)
    (CoherentComputeUncompute.onWork_tensor
      (runLayeredLinearMap (inverseCircuit (baseCircuit words hw p n)))
      (dataResult words (input i) (v i))
      (resultAt words hw p n (input i) (hlen i)) (initialWork words hw p n (input i))
      (inverse_computed_basis words hw p n (input i) (hlen i)))


end

theorem uncompute_ideal_aux (n : ℕ) (input : I → Str) (hlen : ∀ i,(input i).length=n) (v : I → QState 3) :
    workAction (inverseCircuit (baseCircuit words hw p n)) 5
      (initializeAux (idealComputedState words hw p n input hlen v))=
      initializeAux (cleanState words hw p n input v) := by
  rw [workAction_initializeAux,uncompute_ideal]

theorem forward_initial (n : ℕ) (input : I → Str) (v : I → QState 3) :
    workAction (baseCircuit words hw p n) 3 (initialState words hw p n input v)=
      computedState words hw p n input v := by
  change assembleMap _ 3 (CoherentComputeUncompute.onWork _ (separateMap _ 3 (assembleMap _ 3 _)))=_
  rw [separate_assemble]
  rfl

theorem forward_initial_aux (n : ℕ) (input : I → Str) (v : I → QState 3) :
    workAction (baseCircuit words hw p n) 5 (initializeAux (initialState words hw p n input v))=
      initializeAux (computedState words hw p n input v) := by
  rw [workAction_initializeAux,forward_initial]

def finalState (n a : ℕ) (budget : List Unit) (input : I → Str) (v : I → QState 3) :
    QState (width (P words hw p) n+5) :=
  workAction (inverseCircuit (baseCircuit words hw p n)) 5
    (runLayer (nativeMiddle words hw p n a budget) (initializeAux (computedState words hw p n input v)))

/-- Uncomputation does not amplify synthesis error. The inverse acts on the
machine only; all data and all leaked auxiliary amplitudes remain in the norm. -/
theorem finalState_error (n a : ℕ) (ha : PhaseAccurate a) (budget : List Unit)
    (input : I → Str) (hlen : ∀ i,(input i).length=n) (v : I → QState 3)
    (hbound : ∀ i,(words (input i)).length≤ p.eval n) :
    stateNorm (finalState words hw p n a budget input v-initializeAux (cleanState words hw p n input v))≤
      (180*((p.eval n : ℕ) : ℝ)/((budget.length : ℝ)+1))*stateNorm (initialState words hw p n input v) := by
  have hh:=finite_execution_error words hw p n a ha budget input hlen v hbound
  change stateNorm (runLayer (nativeMiddle words hw p n a budget) _-
    initializeAux (idealComputedState words hw p n input hlen v))≤ _ at hh
  unfold finalState
  rw [←uncompute_ideal_aux words hw p n input hlen v,←map_sub,workAction_norm]
  exact hh

private theorem layered_append {n : ℕ} (first rest : Layered n) (ψ : QState n) :
    runLayered (first++rest) ψ=runLayered rest (runLayered first ψ) := List.foldl_append

theorem wholeCircuit_semantics (n a : ℕ) (budget : List Unit) (input : I → Str) (v : I → QState 3) :
    runLayered (wholeCircuit words hw p n a budget) (initializeAux (initialState words hw p n input v))=
      finalState words hw p n a budget input v := by
  unfold wholeCircuit
  rw [layered_append,layered_append,InfoLossLAR.WorstCase.runLayered_singletons]
  rw [extendCircuit_semantics (baseCircuit words hw p n) 5,forward_initial_aux]
  rw [extendCircuit_semantics (inverseCircuit (baseCircuit words hw p n)) 5]
  rfl

/-- A literal forward circuit, emitted finite controlled-word circuit, and
literal inverse circuit form the promised coherent cleaned computation. -/
theorem wholeCircuit_error (n a : ℕ) (ha : PhaseAccurate a) (budget : List Unit)
    (input : I → Str) (hlen : ∀ i,(input i).length=n) (v : I → QState 3)
    (hbound : ∀ i,(words (input i)).length≤ p.eval n) :
    stateNorm (runLayered (wholeCircuit words hw p n a budget)
        (initializeAux (initialState words hw p n input v))-
      initializeAux (cleanState words hw p n input v))≤
      (180*((p.eval n : ℕ) : ℝ)/((budget.length : ℝ)+1))*stateNorm (initialState words hw p n input v) := by
  rw [wholeCircuit_semantics]
  exact finalState_error words hw p n a ha budget input hlen v hbound

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule78

/- Helper module Solutions.RegevBridgeCoherentInputEmbedding. -/
section P2MDyadicModule79

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open scoped BigOperators

variable {D I W : Type*} [Fintype D] [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]

/-- Retain an injective classical encoding of a coherent index in the work
register, including every relative phase and arbitrary data amplitudes. -/
noncomputable def embedInputs (input : I → W) : (D×I → ℂ) →ₗ[ℂ] (D×W → ℂ) where
  toFun ψ := ∑ i,tensor (fun d => ψ (d,i)) (input i)
  map_add' ψ φ := by
    funext x
    simp [tensor,Pi.add_apply,Finset.sum_add_distrib,add_mul]
  map_smul' c ψ := by
    funext x
    simp [tensor,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

theorem embedInputs_at (input : I → W) (hinj : Function.Injective input)
    (ψ : D×I → ℂ) (d : D) (i : I) : embedInputs input ψ (d,input i)=ψ (d,i) := by
  simp [embedInputs,tensor,basis,hinj.eq_iff]

theorem embedInputs_outside (input : I → W) (ψ : D×I → ℂ) (d : D) (w : W)
    (h : w∉Set.range input) : embedInputs input ψ (d,w)=0 := by
  have hn (i : I) : w≠input i := fun he => h ⟨i,he.symm⟩
  simp [embedInputs,tensor,basis,hn]

theorem embedInputs_row_mass (input : I → W) (hinj : Function.Injective input)
    (ψ : D×I → ℂ) (d : D) :
    (∑ w,‖embedInputs input ψ (d,w)‖^2)=∑ i,‖ψ (d,i)‖^2 := by
  have hs : (Finset.univ.image input : Finset W)⊆Finset.univ := Finset.subset_univ _
  calc
    _ = ∑ w∈Finset.univ.image input,‖embedInputs input ψ (d,w)‖^2 := by
      symm
      apply Finset.sum_subset hs
      intro w _ hw
      have hn : w∉Set.range input := by
        rintro ⟨i,rfl⟩
        exact hw (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      rw [embedInputs_outside input ψ d w hn,norm_zero,zero_pow (by decide : 2≠0)]
    _ = ∑ i,‖embedInputs input ψ (d,input i)‖^2 :=
      Finset.sum_image (fun _ _ _ _ he => hinj he)
    _ = _ := by simp only [embedInputs_at input hinj]

/-- Injective physical storage is an isometry, so it introduces no factor
equal to the number of coherent indices in any subsequent error bound. -/
theorem embedInputs_norm (input : I → W) (hinj : Function.Injective input) (ψ : D×I → ℂ) :
    ‖(WithLp.toLp 2 (embedInputs input ψ) : EuclideanSpace ℂ (D×W))‖=
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (D×I))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,embedInputs_row_mass input hinj]

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end P2MDyadicModule79

/- Helper module Solutions.RegevBridgeCoherentBasisEmbedding. -/
section P2MDyadicModule80

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

/-- Exact action on each encoded classical basis state lifts to arbitrary
coherent input amplitudes, including their phases. -/
theorem basisEmbedding_permutation (e : I ↪ W) (s : Equiv.Perm I)
    (U : (W → ℂ) →ₗ[ℂ] (W → ℂ))
    (h : ∀ i,U (basis (e i))=basis (e (s i))) (ψ : I → ℂ) :
    U (basisEmbedding e ψ)=basisEmbedding e (fun i => ψ (s.symm i)) := by
  simp only [basisEmbedding,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,h]
  exact Fintype.sum_equiv s _ _ (by intro i;simp only [Equiv.symm_apply_apply])

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end P2MDyadicModule80

/- Helper module Solutions.RegevBridgeCoherentXorCopy. -/
section P2MDyadicModule81

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentXorCopy

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent

open scoped BigOperators

variable {W k : ℕ}

theorem append_eq_iff (a c : Bits W) (b d : Bits k) :
    Fin.append a b=Fin.append c d ↔ a=c ∧ b=d := by
  change (qubitsAppendEquiv W k).symm (a,b)=(qubitsAppendEquiv W k).symm (c,d) ↔ _
  rw [(qubitsAppendEquiv W k).symm.injective.eq_iff,Prod.mk.injEq]

end InfoLossLAR.WorstCase.CoherentXorCopy

end

end P2MDyadicModule81

/- Helper module Solutions.RegevBridgeCircuitInitializedEmbedding. -/
section P2MDyadicModule82

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

end P2MDyadicModule82

/- Helper module Solutions.RegevBridgeCoherentPublicPreparation. -/
section P2MDyadicModule83

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

end P2MDyadicModule83

/- Helper module Solutions.RegevBridgeGaussianRandomizedRounding. -/
section P2MDyadicModule84

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

end P2MDyadicModule84

/- Helper module Solutions.RegevBridgeGaussianRoundingTail. -/
section P2MDyadicModule85

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

end P2MDyadicModule85

/- Helper module Solutions.RegevBridgeGaussianRoundingTruncation. -/
section P2MDyadicModule86

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

end P2MDyadicModule86

/- Helper module Solutions.RegevBridgeGaussianRoundingContinuous. -/
section P2MDyadicModule87

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

end P2MDyadicModule87

/- Helper module Solutions.RegevBridgeGaussianRoundingNative. -/
section P2MDyadicModule88

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

end P2MDyadicModule88

/- Helper module Solutions.RegevBridgeGaussianGridProjection. -/
section P2MDyadicModule89

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

end P2MDyadicModule89

/- Helper module Solutions.RegevBridgeGaussianNumericalBudget. -/
section P2MDyadicModule90

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

end P2MDyadicModule90

/- Helper module Solutions.RegevBridgeWideGaussianScale. -/
section P2MDyadicModule91

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

end P2MDyadicModule91

/- Helper module Solutions.RegevBridgeWideGaussianPoint. -/
section P2MDyadicModule92

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

theorem pointGuardTicks_length (input : PointRequest) : (pointGuardTicks input).length=8*(input.2.1.length+1)^2 := by
  simp only [pointGuardTicks,List.length_flatMap,List.length_append,List.length_singleton,List.map_const',List.sum_replicate,List.length_replicate]
  ring

noncomputable def pointProgram : PolyProgram Automatic.enc Ratio.encode pointValue := by
  let prepare : PolyProgram Automatic.enc TM2NativeGaussian.requestCode
      (fun input : PointRequest × ℕ => ((pointRatio input,input.1.2.2),pointGuardTicks input.1)) :=
    (show Poly (fun input : PointRequest × ℕ => ((pointRatio input,input.1.2.2),pointGuardTicks input.1)) by fun_prop).program
  exact prepare.comp gaussianProgram

@[fun_prop] theorem pointValue_poly : Poly pointValue := ⟨pointProgram⟩

noncomputable section

theorem variance_ge_one (input : PointRequest) : 1 ≤ variance input := by unfold variance;split <;> first | assumption | exact le_rfl

/-- Every accepted interval proposal obeys the same width-independent
polynomial Gaussian exponent guard. -/
theorem pointRatio_bounds (input : PointRequest) (index : Fin (intervalCount input)) :
    0 ≤ pointRatio (input,index.val) ∧ pointRatio (input,index.val) ≤ (pointGuardTicks input).length := by
  have hv : (0 : ℚ)<variance input := zero_lt_one.trans_le (variance_ge_one input)
  have hscale := (scale_variance_bounds (variance input) (variance_ge_one input)).2
  have hsNat : 1 ≤ scale (variance input) := by rw [scale_eq];exact Nat.one_le_pow _ _ (by norm_num)
  have hs : (1 : ℚ) ≤ scale (variance input) := by exact_mod_cast hsNat
  have hindex : (index.val : ℚ) ≤ 2*(radius input : ℚ) := by
    have hi := index.isLt
    unfold intervalCount at hi
    exact_mod_cast (show index.val ≤ 2*radius input by omega)
  have hfloor := Int.floor_le input.1.2
  have hfloorUpper := Int.lt_floor_add_one input.1.2
  have hdisplacement : |(point (input,index.val) : ℚ)-input.1.2| ≤ (radius input : ℚ)+1 := by
    rw [abs_le]
    simp only [point,anchorInteger_eq,Int.cast_sub,Int.cast_add,Int.cast_natCast]
    constructor <;> linarith [show (0 : ℚ) ≤ index.val by positivity]
  have hrad : (radius input : ℚ)+1 ≤ (input.2.1.length+1 : ℚ)*(scale (variance input) : ℚ) := by
    unfold radius
    push_cast
    nlinarith
  have hsq : ((point (input,index.val) : ℚ)-input.1.2)^2 ≤
      (input.2.1.length+1 : ℚ)^2*(scale (variance input) : ℚ)^2 := by
    have hb := hdisplacement.trans hrad
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : (0 : ℚ) ≤ (input.2.1.length+1 : ℚ)*(scale (variance input) : ℚ))).mpr hb
    simpa only [sq_abs,mul_pow] using hh
  constructor
  · unfold pointRatio;positivity
  · unfold pointRatio
    rw [pointGuardTicks_length]
    apply (div_le_iff₀ hv).mpr
    have hmul := mul_le_mul_of_nonneg_left hscale (sq_nonneg (input.2.1.length+1 : ℚ))
    push_cast
    nlinarith

/-- The literal capped native exponent evaluator equals the previously
verified exact rational Gaussian approximation at this one point. -/
theorem pointValue_eq (input : PointRequest) (index : Fin (intervalCount input)) :
    pointValue (input,index.val)=centeredGaussianApprox (variance input) input.1.2
      (point (input,index.val)) input.2.2.length := by
  have h := pointRatio_bounds input index
  rw [pointValue,gaussianCapped_eq _ h.1 h.2]
  simp only [centeredGaussianApprox,gaussianApprox,gaussianGuard,centeredGaussianRatio_rat]
  rfl

/-- Actual finite rational exponent evaluation has the requested absolute
error, uniformly in a binary-wide variance and arbitrary rational center. -/
theorem pointValue_error (input : PointRequest) (index : Fin (intervalCount input)) :
    |(pointValue (input,index.val) : ℝ)-Real.exp (-Real.pi*((point (input,index.val) : ℝ)-(input.1.2 : ℝ))^2/(variance input : ℝ))| ≤
      1/(2 : ℝ)^input.2.2.length := by
  rw [pointValue_eq input index]
  exact centeredGaussianApprox_error (variance input) input.1.2 (point (input,index.val)) input.2.2.length
    (zero_lt_one.trans_le (variance_ge_one input))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule92

/- Helper module Solutions.RegevBridgeWideGaussianMass. -/
section P2MDyadicModule93

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

/-- Every valid wide window contains nearly all true shifted Gaussian
mass; the discarded infinite tail is bounded without enumerating points. -/
theorem wide_tail_half (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    tailEnvelope width (radius input) ≤ 1/2 := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hscale := (scale_width_bounds input width hwidth hsquare).1
  have hf : (2 : ℝ) ≤ input.2.1.length := by exact_mod_cast hfactor
  have hrad : 2*width ≤ (radius input : ℝ) := by
    unfold radius
    push_cast
    nlinarith
  have htail := (VarianceGrid.tailEnvelope_interval (radius input : ℝ) hwidth le_rfl le_rfl).trans
    (intervalTail_le_six hwidth)
  have hratio : (2 : ℝ) ≤ (radius input : ℝ)^2/(2*width^2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<2*width^2)).mpr
    nlinarith
  have hexponent : -Real.pi*(radius input : ℝ)^2/(2*width^2) ≤ -Real.pi*(2 : ℝ)^2/2 := by
    calc
      _ = -Real.pi*((radius input : ℝ)^2/(2*width^2)) := by ring
      _ ≤ -Real.pi*2 := mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr Real.pi_pos.le)
      _ = _ := by ring
  have hexp := Real.exp_le_exp.mpr hexponent
  have htwo : Real.exp (-Real.pi*(2 : ℝ)^2/2) ≤ 1/16 := by
    convert sigma_gaussian_exp_le 2 (by omega) using 1 <;> norm_num
  have hbound := hexp.trans htwo
  linarith

/-- The true accepted weight has a width-linear lower bound, even at an
arbitrary rational shifted center and exponentially wide binary scale. -/
theorem trueWindowMass_lower (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    width/4 ≤ trueWindowMass input width := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have ht := roundingError_lt_half width hwidth
  have hrelative := (abs_le.mp (theta_relative_error_exp width (input.1.2 : ℝ) hw)).1
  have htheta : width/2 ≤ theta width input.1.2 := by
    have hlo : 1-thetaError width ≤ theta width input.1.2/width := by linarith
    have hb := (le_div_iff₀ hw).mp hlo
    nlinarith
  have hout := (outsideWindowMass_le width hwidth input.1.2 (radius input)).trans (wide_tail_half input width hwidth hsquare hfactor)
  have heq := outsideWindowMass_eq 1 width hw input.1.2 (radius input)
  rw [retainedResidue_sum] at heq
  simp_rw [roundingPMF_toReal] at heq
  rw [←Finset.sum_div] at heq
  have hmass : (∑ index : Fin (2*radius input+1),shiftedWeight width input.1.2 (windowPoint input.1.2 (radius input) index))=
      trueWindowMass input width := by
    unfold trueWindowMass
    simp_rw [point_eq_windowPoint]
    rfl
  rw [hmass] at heq
  have hr : 1/2 ≤ trueWindowMass input width/theta width input.1.2 := by linarith
  have hb := (le_div_iff₀ (theta_pos width input.1.2 hw)).mp hr
  linarith

/-- Binary ticket length is controlled by the width-linear window size;
this is the key cancellation in the rejection success probability. -/
theorem wide_ticket_bound (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    (2 : ℝ)^Nat.size (intervalCount input) ≤ 14*(input.2.1.length : ℝ)*width := by
  have hscale := (scale_width_bounds input width hwidth hsquare).2
  have hf : (2 : ℝ) ≤ input.2.1.length := by exact_mod_cast hfactor
  have hcount : (intervalCount input : ℝ) ≤ 7*(input.2.1.length : ℝ)*width := by
    unfold intervalCount radius
    push_cast
    nlinarith
  have hhalf := boundedFinSuccess_half (intervalCount input) (by unfold intervalCount;omega)
  unfold boundedFinSuccess at hhalf
  have hb := (le_div_iff₀ (by positivity : (0 : ℝ)<2^Nat.size (intervalCount input))).mp hhalf
  nlinarith

/-- One ideal Gaussian-weight interval trial succeeds with inverse-linear
probability in the public unary multiplier, independent of width value. -/
theorem ideal_trial_success_lower (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    1/(56*(input.2.1.length : ℝ)) ≤ trueWindowMass input width/(2 : ℝ)^Nat.size (intervalCount input) := by
  have hmass := trueWindowMass_lower input width hwidth hsquare hfactor
  have hticket := wide_ticket_bound input width hwidth hsquare hfactor
  have hf : (0 : ℝ) < input.2.1.length := by exact_mod_cast (show 0 < input.2.1.length by omega)
  have hh := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 56*(input.2.1.length : ℝ) by positivity)
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<2^Nat.size (intervalCount input))).mpr
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<56*(input.2.1.length : ℝ))).mpr
  nlinarith

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule93

/- Helper module Solutions.RegevBridgeNativeSquareRoot. -/
section P2MDyadicModule94

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

theorem capacity_pos (x : Input) : 0<capacity x := Nat.zero_lt_succ _

theorem index_le (x : Input) : index x≤capacity x := by
  simpa only [index,List.length_range] using
    (List.findIdx_le_length (xs:=List.range (capacity x)) (p:=fun i => test (x,i)))

theorem current_nonneg (x : Input) : 0≤current x := by unfold current;positivity

theorem current_square_le (x : Input) (hu : 0≤x.1) : current x^2≤x.1 := by
  by_cases hz : index x=0
  · simpa only [current,hz,Nat.cast_zero,zero_div,zero_pow (by decide : 2≠0)] using hu
  · have hi : index x-1 < index x := by omega
    have ht := List.not_of_lt_findIdx (xs:=List.range (capacity x)) (p:=fun i => test (x,i)) hi
    simp only [List.getElem_range,test,decide_eq_false_iff_not,not_lt] at ht
    have he : index x-1+1=index x := by omega
    simpa only [he,current,pow_two] using ht

theorem sqrt_lower (x : Input) (hu : 0≤x.1) :
    (current x : ℝ)≤Real.sqrt (x.1 : ℝ) := by
  apply (Real.le_sqrt (by exact_mod_cast current_nonneg x) (by exact_mod_cast hu)).mpr
  exact_mod_cast current_square_le x hu

theorem sqrt_upper (x : Input) (hu : x.1≤1) :
    Real.sqrt (x.1 : ℝ)≤(current x : ℝ)+1/(capacity x : ℝ) := by
  have hpos : (0 : ℝ)<capacity x := by exact_mod_cast capacity_pos x
  by_cases hlt : index x<capacity x
  · have hh : (List.range (capacity x)).findIdx (fun i => test (x,i))<
        (List.range (capacity x)).length := by simpa only [index,List.length_range] using hlt
    have ht := List.findIdx_getElem (p:=fun i => test (x,i)) (xs:=List.range (capacity x)) (w:=hh)
    simp only [List.getElem_range,test,decide_eq_true_eq] at ht
    change x.1<((index x+1 : ℕ) : ℚ)/(capacity x : ℚ)*
      (((index x+1 : ℕ) : ℚ)/(capacity x : ℚ)) at ht
    have he : ((current x : ℝ)+1/(capacity x : ℝ))=
        (((index x+1 : ℕ) : ℚ)/(capacity x : ℚ) : ℚ) := by
      simp only [current,Rat.cast_div,Rat.cast_natCast,Nat.cast_add,Nat.cast_one,Rat.cast_add,Rat.cast_one]
      ring
    rw [he]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [pow_two]
      exact_mod_cast ht.le
  · have he : index x=capacity x := le_antisymm (index_le x) (Nat.le_of_not_gt hlt)
    have hc : current x=1 := by
      simp only [current,he]
      exact div_self (by exact_mod_cast (capacity_pos x).ne')
    rw [hc,Rat.cast_one]
    apply (Real.sqrt_le_one.mpr (by exact_mod_cast hu)).trans
    have : (0 : ℝ)≤1/(capacity x : ℝ) := by positivity
    linarith

/-- A real square root is approximated by a genuinely executable rational
program. The enumeration is bounded by the supplied unary buffer. -/
theorem current_error (x : Input) (hu0 : 0≤x.1) (hu1 : x.1≤1) :
    |Real.sqrt (x.1 : ℝ)-(current x : ℝ)|≤1/(capacity x : ℝ) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (sqrt_lower x hu0))]
  linarith [sqrt_upper x hu1]

end InfoLossLAR.WorstCase.NativeSquareRoot

end P2MDyadicModule94

/- Helper module Solutions.RegevBridgeAcceptanceRotation. -/
section P2MDyadicModule95
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.AcceptanceRotation

open QAlgorithms FiniteGateTransport

open scoped BigOperators

noncomputable def rotation (c s : ℝ) : Matrix Bool Bool ℂ :=
  fun row col => if row then (if col then (c : ℂ) else (s : ℂ))
    else (if col then (-s : ℂ) else (c : ℂ))

/-- The first column has true-flag amplitude sqrt(u), as required by coherent
rejection; the second column completes an actual unitary matrix. -/
noncomputable def ideal (u : ℝ) : Matrix Bool Bool ℂ :=
  rotation (Real.sqrt (1-u)) (Real.sqrt u)

theorem rotation_unitary (c s : ℝ) (hnorm : c^2+s^2=1) :
    rotation c s∈Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      rotation,Fintype.sum_bool,Matrix.one_apply,←Complex.ofReal_mul,←Complex.ofReal_add]
  all_goals
    first
    | norm_cast; nlinarith
    | ring

theorem ideal_unitary (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) :
    ideal u∈Matrix.unitaryGroup Bool ℂ := by
  apply rotation_unitary
  rw [Real.sq_sqrt (sub_nonneg.mpr hu1),Real.sq_sqrt hu0]
  ring

theorem oneBit_unitary (U : Matrix Bool Bool ℂ) (hU : U∈Matrix.unitaryGroup Bool ℂ) :
    (Gate.ofMatrix1 U).mat∈Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  change U.submatrix oneBitEquiv oneBitEquiv*star (U.submatrix oneBitEquiv oneBitEquiv)=1
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv U U.conjTranspose oneBitEquiv oneBitEquiv oneBitEquiv]
  rw [Matrix.star_eq_conjTranspose] at hU
  rw [hU,Matrix.submatrix_one_equiv]

theorem oneBit_frobNorm (U : Matrix Bool Bool ℂ) :
    frobNorm (Gate.ofMatrix1 U).mat=frobNorm U := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change frobNorm (Gate.ofMatrix1 U).mat^2=frobNorm U^2
  rw [frobNorm_square,frobNorm_square]
  apply Fintype.sum_equiv oneBitEquiv
  intro x
  exact Fintype.sum_equiv oneBitEquiv _ _ (by intro y;rfl)

theorem rotation_error (c s c' s' ε : ℝ) (hε : 0≤ε)
    (hc : |c-c'|≤ε) (hs : |s-s'|≤ε) :
    frobNorm (rotation c s-rotation c' s')≤2*ε := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change frobNorm (rotation c s-rotation c' s')^2≤(2*ε)^2
  rw [frobNorm_square]
  simp only [Fintype.sum_bool,rotation,Bool.false_eq_true,if_false,if_true,Matrix.sub_apply]
  have hc2 := pow_le_pow_left₀ (abs_nonneg (c-c')) hc 2
  have hs2 := pow_le_pow_left₀ (abs_nonneg (s-s')) hs 2
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,neg_sub_neg,
    abs_sub_comm s' s] at ⊢
  nlinarith

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

theorem coefficient_eval (x : Input) (row col : Bool) :
    FiniteGateNative.eval (coefficient x row col)=rotation (cValue x) (sValue x) row col := by
  cases row <;> cases col <;>
    apply Complex.ext <;> simp [coefficient,rotation,FiniteGateNative.eval,FiniteGateNative.evalReal]

theorem nativeTarget_initialized (x : Input) :
    QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
      (FiniteGateNative.evalMatrix (nativeTarget x))=
      QAlgorithms.Papers.Independent.Renew46.P12.idealMap (n:=1)
        (Gate.ofMatrix1 (rotation (cValue x) (sValue x))).mat 2 := by
  rw [nativeTarget,FiniteGateNative.eval_singleGate _ _ (coefficient_eval x),embed_oneWire_initialized]

/-- The actual rational target is within the requested inverse-unary accuracy
of an actual unitary on the initialized input, including all output rows. -/
theorem nativeTarget_error (x : Input) (hu0 : 0≤x.1) (hu1 : x.1≤1) :
    frobNorm (QAlgorithms.Papers.Independent.Renew46.P12.idealMap (n:=1)
        (Gate.ofMatrix1 (ideal (x.1 : ℝ))).mat 2-
      QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
        (FiniteGateNative.evalMatrix (nativeTarget x)))≤2/(NativeSquareRoot.capacity x : ℝ) := by
  rw [nativeTarget_initialized,idealMap_error]
  change frobNorm (Gate.ofMatrix1 (ideal (x.1 : ℝ)-rotation (cValue x) (sValue x))).mat≤_
  rw [oneBit_frobNorm]
  have hc := NativeSquareRoot.current_error (1-x.1,x.2) (sub_nonneg.mpr hu1) (by linarith)
  have hs := NativeSquareRoot.current_error x hu0 hu1
  simp only [NativeSquareRoot.capacity,Rat.cast_sub,Rat.cast_one] at hc hs ⊢
  simpa only [div_eq_mul_inv,mul_one,one_mul,ideal] using rotation_error
    (Real.sqrt (1-(x.1 : ℝ))) (Real.sqrt (x.1 : ℝ)) (cValue x) (sValue x)
    (1/(x.2.length+1 : ℕ)) (by positivity) hc hs

/-- Square-root amplitudes have the needed Holder error bound even near the
endpoints of the acceptance interval. -/
theorem sqrt_difference (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    |Real.sqrt x-Real.sqrt y|≤Real.sqrt |x-y| := by
  apply (Real.le_sqrt (abs_nonneg _) (abs_nonneg _)).mpr
  have hxq := Real.sq_sqrt hx
  have hyq := Real.sq_sqrt hy
  rcases le_total x y with hxy|hyx
  · have hr := Real.sqrt_le_sqrt hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hr),abs_of_nonpos (sub_nonpos.mpr hxy)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hr)]
  · have hr := Real.sqrt_le_sqrt hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hr),abs_of_nonneg (sub_nonneg.mpr hyx)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg y) (sub_nonneg.mpr hr)]

/-- A finite-precision acceptance probability perturbs the coherent rotation
by at most twice the square root of its scalar error. -/
theorem ideal_error (u v δ : ℝ) (hu0 : 0≤u) (hu1 : u≤1)
    (hv0 : 0≤v) (hv1 : v≤1) (hδ : |u-v|≤δ) :
    frobNorm (ideal u-ideal v)≤2*Real.sqrt δ := by
  apply rotation_error _ _ _ _ _ (Real.sqrt_nonneg δ)
  · have h := (sqrt_difference (1-u) (1-v) (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1)).trans
      (Real.sqrt_le_sqrt (show |(1-u)-(1-v)|≤δ by
        have he : (1-u)-(1-v)=-(u-v) := by ring
        rw [he,abs_neg];exact hδ))
    exact h
  · exact (sqrt_difference u v hu0 hv0).trans (Real.sqrt_le_sqrt hδ)

end InfoLossLAR.WorstCase.AcceptanceRotation

end P2MDyadicModule95

/- Helper module Solutions.RegevBridgeCoherentRejection. -/
section P2MDyadicModule96

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentRejection

open scoped BigOperators

/-- A reversible swap with the chosen copy. The copy's entire junk register
is retained; only its output is exchanged with the designated output. -/
def swapOutput {O J : Type*} {m : ℕ} (j : Fin m)
    (x : O × (Fin m → O×J)) : O × (Fin m → O×J) :=
  ((x.2 j).1,Function.update x.2 j (x.1,(x.2 j).2))

theorem swapOutput_involutive {O J : Type*} {m : ℕ} (j : Fin m) :
    Function.Involutive (swapOutput (O:=O) (J:=J) j) := by
  intro x
  apply Prod.ext
  · simp [swapOutput]
  · funext i
    by_cases hi : i=j
    · subst i;simp [swapOutput]
    · simp [swapOutput,Function.update_of_ne hi]

def swapEquiv {O J : Type*} {m : ℕ} (j : Fin m) :
    (O×(Fin m → O×J)) ≃ (O×(Fin m → O×J)) where
  toFun := swapOutput j
  invFun := swapOutput j
  left_inv := swapOutput_involutive j
  right_inv := swapOutput_involutive j

@[simp] theorem swapEquiv_apply {O J : Type*} {m : ℕ} (j : Fin m)
    (x : O×(Fin m → O×J)) : swapEquiv j x=swapOutput j x := rfl

/-- The first true flag in the public order of the copies. -/
def firstSuccess {m : ℕ} (flags : Fin m → Bool) : Option (Fin m) :=
  (List.finRange m).find? flags

theorem firstSuccess_true {m : ℕ} (flags : Fin m → Bool) (j : Fin m)
    (h : firstSuccess flags=some j) : flags j=true := List.find?_some h

theorem firstSuccess_none {m : ℕ} (flags : Fin m → Bool) :
    firstSuccess flags=none ↔ flags=(fun _ => false) := by
  simp only [firstSuccess,List.find?_eq_none,List.mem_finRange,forall_const]
  constructor
  · intro h;funext i;exact Bool.eq_false_iff.mpr (h i)
  · intro h i;simp [h]

def selectedSwap {O J : Type*} {m : ℕ} (flags : Fin m → Bool) :
    (O×(Fin m → O×J)) ≃ (O×(Fin m → O×J)) :=
  match firstSuccess flags with
  | none => Equiv.refl _
  | some j => swapEquiv j

noncomputable def initialState {O J : Type*} [DecidableEq O] {m : ℕ}
    (zero : O) (single : Bool → O → J → ℂ) (flags : Fin m → Bool)
    (x : O×(Fin m → O×J)) : ℂ :=
  if x.1=zero then ∏ i,single (flags i) (x.2 i).1 (x.2 i).2 else 0

/-- Amplitude semantics of the actual reversible flag-controlled swap. -/
noncomputable def swappedState {O J : Type*} [DecidableEq O] {m : ℕ}
    (zero : O) (single : Bool → O → J → ℂ) (flags : Fin m → Bool)
    (x : O×(Fin m → O×J)) : ℂ :=
  initialState zero single flags (selectedSwap flags x)

/-- The retained successful garbage amplitude. It includes the original copy
flags, all unused outputs, every junk register, and the emptied selected output. -/
noncomputable def garbageAmplitude {O J : Type*} [DecidableEq O] {m : ℕ}
    (zero : O) (single : Bool → O → J → ℂ) (alpha : ℂ) (junk : J → ℂ)
    (flags : Fin m → Bool) (copies : Fin m → O×J) : ℂ :=
  match firstSuccess flags with
  | none => 0
  | some j => if (copies j).1=zero then
      alpha*junk (copies j).2*(∏ i∈Finset.univ.erase j,single (flags i) (copies i).1 (copies i).2)
    else 0

/-- First-success selection preserves a pure output on the entire success
branch. The needed single-copy factorization is an explicit hypothesis. -/
theorem success_factorization {O J : Type*} [DecidableEq O] {m : ℕ}
    (zero : O) (single : Bool → O → J → ℂ) (alpha : ℂ) (target : O → ℂ) (junk : J → ℂ)
    (hsingle : ∀ o j,single true o j=alpha*target o*junk j)
    (flags : Fin m → Bool) (x : O×(Fin m → O×J)) :
    (if firstSuccess flags=none then 0 else swappedState zero single flags x)=
      target x.1*garbageAmplitude zero single alpha junk flags x.2 := by
  classical
  cases hfirst : firstSuccess flags with
  | none => simp [hfirst,garbageAmplitude]
  | some j =>
    have hj := firstSuccess_true flags j hfirst
    simp only [hfirst,Option.some_ne_none,if_false,swappedState,selectedSwap,
      swapEquiv_apply,swapOutput,initialState,garbageAmplitude]
    by_cases hz : (x.2 j).1=zero
    · rw [if_pos hz,if_pos hz]
      rw [←Finset.mul_prod_erase Finset.univ
        (fun i => single (flags i) ((Function.update x.2 j (x.1,(x.2 j).2)) i).1
          ((Function.update x.2 j (x.1,(x.2 j).2)) i).2) (Finset.mem_univ j)]
      simp only [Function.update_self,hj,hsingle]
      have hrest : (∏ i∈Finset.univ.erase j,
          single (flags i) ((Function.update x.2 j (x.1,(x.2 j).2)) i).1
            ((Function.update x.2 j (x.1,(x.2 j).2)) i).2)=
          ∏ i∈Finset.univ.erase j,single (flags i) (x.2 i).1 (x.2 i).2 := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
      rw [hrest]
      ring
    · simp [hz]

noncomputable def flagMass {O J : Type*} [Fintype O] [Fintype J]
    (single : Bool → O → J → ℂ) (flag : Bool) : ℝ :=
  ∑ o : O,∑ j : J,‖single flag o j‖^2

/-- The full flag-block mass is the product of the single-copy masses. -/
theorem initial_flag_mass {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O]
    {m : ℕ} (zero : O) (single : Bool → O → J → ℂ) (flags : Fin m → Bool) :
    (∑ x : O×(Fin m → O×J),‖initialState zero single flags x‖^2)=
      ∏ i,flagMass single (flags i) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [initialState]
  have hsum : (∑ o : O,∑ copies : Fin m → O×J,
      ‖(if o=zero then ∏ i,single (flags i) (copies i).1 (copies i).2 else 0 : ℂ)‖^2)=
      ∑ copies : Fin m → O×J,‖∏ i,single (flags i) (copies i).1 (copies i).2‖^2 := by
    have h := Finset.sum_eq_single zero (s:=Finset.univ)
      (f:=fun o : O => ∑ copies : Fin m → O×J,
        ‖(if o=zero then ∏ i,single (flags i) (copies i).1 (copies i).2 else 0 : ℂ)‖^2)
      (by intro o _ ho;simp [ho]) (by simp)
    simpa only [if_pos rfl,ite_true] using h
  rw [hsum]
  simp only [norm_prod,←Finset.prod_pow]
  rw [←Fintype.prod_sum (fun (i : Fin m) (v : O×J) => ‖single (flags i) v.1 v.2‖^2)]
  apply Finset.prod_congr rfl
  intro i _
  exact Fintype.sum_prod_type _

/-- The flag-controlled operation is a permutation, hence preserves each
flag block's probability while retaining the entire work space. -/
theorem swapped_flag_mass {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O]
    {m : ℕ} (zero : O) (single : Bool → O → J → ℂ) (flags : Fin m → Bool) :
    (∑ x : O×(Fin m → O×J),‖swappedState zero single flags x‖^2)=
      ∏ i,flagMass single (flags i) := by
  have h := (selectedSwap (O:=O) (J:=J) flags).sum_comp
    (fun x => ‖initialState zero single flags x‖^2)
  exact h.trans (initial_flag_mass zero single flags)

/-- Failure occurs exactly when every independent copy failed. -/
theorem failure_mass {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O]
    {m : ℕ} (zero : O) (single : Bool → O → J → ℂ) (p : ℝ)
    (hfail : flagMass single false=1-p) :
    (∑ flags : Fin m → Bool,∑ x : O×(Fin m → O×J),
      if firstSuccess flags=none then ‖swappedState zero single flags x‖^2 else 0)=(1-p)^m := by
  classical
  simp_rw [firstSuccess_none]
  rw [Finset.sum_eq_single (fun _ : Fin m => false)]
  · simp only [if_true,swapped_flag_mass,hfail,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  · intro flags _ hflags;simp [hflags]
  · simp

/-- Independent normalized copies and the output swap give a normalized
complete state; no postselection is hidden in the construction. -/
theorem complete_mass {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O]
    {m : ℕ} (zero : O) (single : Bool → O → J → ℂ)
    (hnorm : flagMass single false+flagMass single true=1) :
    (∑ flags : Fin m → Bool,∑ x : O×(Fin m → O×J),
      ‖swappedState zero single flags x‖^2)=1 := by
  simp_rw [swapped_flag_mass]
  rw [←Fintype.prod_sum]
  simp only [Fintype.sum_bool,add_comm (flagMass single true),hnorm,Finset.prod_const_one]

/-- The total successful mass is exactly one minus the all-failure mass. -/
theorem success_mass {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O]
    {m : ℕ} (zero : O) (single : Bool → O → J → ℂ) (p : ℝ)
    (hfail : flagMass single false=1-p)
    (hnorm : flagMass single false+flagMass single true=1) :
    (∑ flags : Fin m → Bool,∑ x : O×(Fin m → O×J),
      if firstSuccess flags=none then 0 else ‖swappedState zero single flags x‖^2)=1-(1-p)^m := by
  have hf := failure_mass (m:=m) zero single p hfail
  have ht := complete_mass (m:=m) zero single hnorm
  have hsum : (∑ flags : Fin m → Bool,∑ x : O×(Fin m → O×J),
      if firstSuccess flags=none then 0 else ‖swappedState zero single flags x‖^2)+
      (∑ flags : Fin m → Bool,∑ x : O×(Fin m → O×J),
      if firstSuccess flags=none then ‖swappedState zero single flags x‖^2 else 0)=
      ∑ flags : Fin m → Bool,∑ x : O×(Fin m → O×J),‖swappedState zero single flags x‖^2 := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro flags _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [hf,ht] at hsum
  linarith

/-- Successful output probabilities factor from the entire retained garbage.
This is a consequence of amplitudes, rather than a claim inferred from a
classical sampler's output distribution. -/
theorem success_output_factor {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O]
    {m : ℕ} (zero : O) (single : Bool → O → J → ℂ) (alpha : ℂ)
    (target : O → ℂ) (junk : J → ℂ)
    (hsingle : ∀ o j,single true o j=alpha*target o*junk j) (o : O) :
    (∑ flags : Fin m → Bool,∑ copies : Fin m → O×J,
      if firstSuccess flags=none then 0 else ‖swappedState zero single flags (o,copies)‖^2)=
      ‖target o‖^2*(∑ flags : Fin m → Bool,∑ copies : Fin m → O×J,
        ‖garbageAmplitude zero single alpha junk flags copies‖^2) := by
  have hpoint (flags : Fin m → Bool) (copies : Fin m → O×J) :
      (if firstSuccess flags=none then 0 else ‖swappedState zero single flags (o,copies)‖^2)=
        ‖target o‖^2*‖garbageAmplitude zero single alpha junk flags copies‖^2 := by
    have h := congrArg (fun z : ℂ => ‖z‖^2)
      (success_factorization zero single alpha target junk hsingle flags (o,copies))
    simp only [norm_mul,mul_pow] at h
    split_ifs at h ⊢ <;> simpa using h
  simp_rw [hpoint,←Finset.mul_sum]

/-- A normalized target means that the retained success-garbage mass equals
the success probability; in particular the successful output law is exact. -/
theorem successful_garbage_mass {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O]
    {m : ℕ} (zero : O) (single : Bool → O → J → ℂ) (alpha : ℂ)
    (target : O → ℂ) (junk : J → ℂ)
    (hsingle : ∀ o j,single true o j=alpha*target o*junk j)
    (htarget : ∑ o,‖target o‖^2=1) (p : ℝ)
    (hfail : flagMass single false=1-p)
    (hnorm : flagMass single false+flagMass single true=1) :
    (∑ flags : Fin m → Bool,∑ copies : Fin m → O×J,
      ‖garbageAmplitude zero single alpha junk flags copies‖^2)=1-(1-p)^m := by
  have hsum := success_mass (m:=m) zero single p hfail hnorm
  simp only [Fintype.sum_prod_type] at hsum
  rw [Finset.sum_comm] at hsum
  simp_rw [success_output_factor zero single alpha target junk hsingle] at hsum
  rw [←Finset.sum_mul,htarget,one_mul] at hsum
  exact hsum

end InfoLossLAR.WorstCase.CoherentRejection

end P2MDyadicModule96

/- Helper module Solutions.RegevBridgeCoherentWeightedPreparation. -/
section P2MDyadicModule97

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentWeightedPreparation

open QAlgorithms FiniteGateTransport

open scoped BigOperators

variable {O : Type*} [Fintype O] [Nonempty O]

noncomputable def initial : Bool×O → ℂ :=
  fun p => if p.1 then 0 else ((Real.sqrt (Fintype.card O : ℝ))⁻¹ : ℝ)

noncomputable def prepared (w : O → ℝ) : Bool×O → ℂ :=
  applyDependentReference (fun o => AcceptanceRotation.ideal (w o)) initial

noncomputable def successAmplitude (w : O → ℝ) : ℂ :=
  (Real.sqrt (weightSum w)/Real.sqrt (Fintype.card O : ℝ) : ℝ)

theorem cardinal_pos : (0 : ℝ)<Fintype.card O := by exact_mod_cast Fintype.card_pos

theorem initial_normalized : (∑ p : Bool×O,‖(initial : Bool×O → ℂ) p‖^2)=1 := by
  have hN : (Fintype.card O : ℝ)≠0 := cardinal_pos.ne'
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,initial,if_true,Bool.false_eq_true,
    if_false,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
    Finset.sum_const_zero,zero_add,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    inv_pow,Real.sq_sqrt (Nat.cast_nonneg _),Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ hN

theorem prepared_true (w : O → ℝ) (o : O) :
    prepared w (true,o)=(Real.sqrt (w o)/Real.sqrt (Fintype.card O : ℝ) : ℝ) := by
  simp [prepared,applyDependentReference,Matrix.mulVec,dotProduct,Fintype.sum_bool,
    AcceptanceRotation.ideal,AcceptanceRotation.rotation,initial,div_eq_mul_inv]

theorem prepared_false (w : O → ℝ) (o : O) :
    prepared w (false,o)=(Real.sqrt (1-w o)/Real.sqrt (Fintype.card O : ℝ) : ℝ) := by
  simp [prepared,applyDependentReference,Matrix.mulVec,dotProduct,Fintype.sum_bool,
    AcceptanceRotation.ideal,AcceptanceRotation.rotation,initial,div_eq_mul_inv]

/-- Uniform proposal followed by a coordinate-controlled ideal acceptance
rotation has a pure weighted success branch at the amplitude level. -/
theorem success_factorization (w : O → ℝ) (hZ : 0<weightSum w) (o : O) :
    prepared w (true,o)=successAmplitude w*target w o := by
  rw [prepared_true]
  unfold successAmplitude target
  have hZ' : Real.sqrt (weightSum w)≠0 := (Real.sqrt_pos.mpr hZ).ne'
  have hN' : Real.sqrt (Fintype.card O : ℝ)≠0 := (Real.sqrt_pos.mpr cardinal_pos).ne'
  have hreal : Real.sqrt (w o)/Real.sqrt (Fintype.card O : ℝ)=
      (Real.sqrt (weightSum w)/Real.sqrt (Fintype.card O : ℝ))*
        (Real.sqrt (w o)/Real.sqrt (weightSum w)) := by field_simp
  exact_mod_cast hreal

/-- The weighted target is normalized, including zero weight coordinates. -/
theorem target_normalized (w : O → ℝ) (hw : ∀ o,0≤w o) (hZ : 0<weightSum w) :
    (∑ o,‖target w o‖^2)=1 := by
  simp only [target,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,
    Real.sq_sqrt (le_of_lt hZ)]
  simp_rw [Real.sq_sqrt (hw _)]
  rw [←Finset.sum_div]
  exact div_self hZ.ne'

theorem true_mass (w : O → ℝ) (hw : ∀ o,0≤w o) :
    (∑ o,‖prepared w (true,o)‖^2)=weightSum w/(Fintype.card O : ℝ) := by
  simp only [prepared_true,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [Real.sq_sqrt (hw _)]
  exact (Finset.sum_div _ _ _).symm

theorem false_mass (w : O → ℝ) (hw : ∀ o,w o≤1) :
    (∑ o,‖prepared w (false,o)‖^2)=1-weightSum w/(Fintype.card O : ℝ) := by
  simp only [prepared_false,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [Real.sq_sqrt (sub_nonneg.mpr (hw _))]
  rw [←Finset.sum_div,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [sub_div,div_self cardinal_pos.ne']
  rfl

end InfoLossLAR.WorstCase.CoherentWeightedPreparation

end P2MDyadicModule97

/- Helper module Solutions.RegevBridgeNativeAcceptanceGates. -/
section P2MDyadicModule98
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

noncomputable def ideal (u : ℚ) : Matrix (QAlgorithms.Qubits 1) (QAlgorithms.Qubits 1) ℂ :=
  (QAlgorithms.Gate.ofMatrix1 (AcceptanceRotation.ideal (u : ℝ))).mat

theorem ideal_unitary (u : ℚ) (hu0 : 0≤ u) (hu1 : u≤1) :
    ideal u∈Matrix.unitaryGroup (QAlgorithms.Qubits 1) ℂ :=
  AcceptanceRotation.oneBit_unitary _ (AcceptanceRotation.ideal_unitary _
    (by exact_mod_cast hu0) (by exact_mod_cast hu1))

theorem target_error (x : Input) (hu0 : 0≤ x.1) (hu1 : x.1≤1) :
    QAlgorithms.frobNorm (initializedNative (target x)-
      QAlgorithms.Papers.Independent.Renew46.P12.idealMap (ideal x.1) 2)≤1/((x.2.length : ℝ)+1) := by
  have hh := AcceptanceRotation.nativeTarget_error (x.1,sqrtBudget x.2) hu0 hu1
  have hcap : (NativeSquareRoot.capacity (x.1,sqrtBudget x.2) : ℝ)=2*((x.2.length : ℝ)+1) := by
    simp only [NativeSquareRoot.capacity,sqrtBudget,List.length_append,List.length_singleton]
    push_cast
    ring
  rw [hcap] at hh
  have he : (2 : ℝ)/(2*((x.2.length : ℝ)+1))=1/((x.2.length : ℝ)+1) := by field_simp
  rw [he] at hh
  rw [frob_sub_comm] at hh
  simpa only [target,ideal,initializedNative_eq] using hh

/-- A genuine finite H/T/CNOT word implements coherent acceptance for the rational
probability supplied to the machine. Its two auxiliary qubits are initialized to zero,
and the error bound retains every output row, including auxiliary leakage. -/
theorem exists_current_accuracy :
    ∃ a : ℕ,0< a ∧ ∀ x : Input,0≤ x.1 → x.1≤1 →
      current a x∈FiniteGateNativeEnumeration.search a x.2 ∧
      QAlgorithms.frobNorm
        (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
          (matrix (FiniteGateNativeEnumeration.interpreted (current a x)))-
          QAlgorithms.Papers.Independent.Renew46.P12.idealMap (ideal x.1) 2)≤5/((x.2.length : ℝ)+1) := by
  obtain ⟨a,ha,haccuracy⟩ := exists_nativeCompile_accuracy
  refine ⟨a,ha,?_⟩
  intro x hu0 hu1
  simpa only [current] using haccuracy (ideal x.1) (ideal_unitary x.1 hu0 hu1)
    x.2 (target x) (target_error x hu0 hu1)

end InfoLossLAR.WorstCase.NativeAcceptanceGates

end P2MDyadicModule98

/- Helper module Solutions.RegevBridgeNativeCoherentAcceptanceError. -/
section P2MDyadicModule99
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeCoherentAcceptanceError

open QAlgorithms FiniteGateTransport

open QAlgorithms.Papers.Independent.Renew46.P12

open FiniteGateNativeEnumeration

noncomputable def realIdeal (w : ℝ) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  (Gate.ofMatrix1 (AcceptanceRotation.ideal w)).mat

theorem ideal_error (q : ℚ) (w δ : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (hw0 : 0≤w) (hw1 : w≤1) (hδ : |(q : ℝ)-w|≤δ) :
    frobNorm (idealMap (NativeAcceptanceGates.ideal q) 2-idealMap (realIdeal w) 2)≤
      2*Real.sqrt δ := by
  rw [idealMap_error]
  change frobNorm (Gate.ofMatrix1
    (AcceptanceRotation.ideal (q : ℝ)-AcceptanceRotation.ideal w)).mat≤_
  rw [AcceptanceRotation.oneBit_frobNorm]
  exact AcceptanceRotation.ideal_error _ _ _ (by exact_mod_cast hq0)
    (by exact_mod_cast hq1) hw0 hw1 hδ

/-- One fixed polynomial-time compiler exponent works for every rational
probability and every real target to which it is numerically close. -/
theorem exists_local_accuracy :
    ∃ a : ℕ,0<a ∧ ∀ (budget : List Unit) (q : ℚ) (w δ : ℝ),
      0≤q → q≤1 → 0≤w → w≤1 → |(q : ℝ)-w|≤δ →
      frobNorm (initializedMap (n:=1) (w:=2)
        (matrix (interpreted (NativeAcceptanceGates.current a (q,budget))))-
        idealMap (realIdeal w) 2)≤5/((budget.length : ℝ)+1)+2*Real.sqrt δ := by
  obtain ⟨a,ha,h⟩ := NativeAcceptanceGates.exists_current_accuracy
  refine ⟨a,ha,?_⟩
  intro budget q w δ hq0 hq1 hw0 hw1 hδ
  have hfirst := (h (q,budget) hq0 hq1).2
  have hsecond := ideal_error q w δ hq0 hq1 hw0 hw1 hδ
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hsecond)

/-- Numerical probability errors and finite-gate synthesis errors combine
uniformly over a coherently retained input register; all auxiliary rows remain
in the norm, including leakage. -/
theorem exists_coherent_accuracy :
    ∃ a : ℕ,0<a ∧ ∀ (R : Type*) [Fintype R] (budget : List Unit)
      (q : R → ℚ) (w : R → ℝ) (δ : ℝ),
      0≤δ → (∀ r,0≤q r) → (∀ r,q r≤1) → (∀ r,0≤w r) → (∀ r,w r≤1) →
      (∀ r,|(q r : ℝ)-w r|≤δ) → ∀ ψ : Qubits 1×R → ℂ,
      ‖(WithLp.toLp 2
        (applyDependentReference (fun r => initializedMap (n:=1) (w:=2)
          (matrix (interpreted (NativeAcceptanceGates.current a (q r,budget))))) ψ-
         applyDependentReference (fun r => idealMap (realIdeal (w r)) 2) ψ) :
        EuclideanSpace ℂ (Qubits 3×R))‖≤
        (5/((budget.length : ℝ)+1)+2*Real.sqrt δ)*
          ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Qubits 1×R))‖ := by
  obtain ⟨a,ha,h⟩ := exists_local_accuracy
  refine ⟨a,ha,?_⟩
  intro R _ budget q w δ hδ hq0 hq1 hw0 hw1 herr ψ
  exact applyDependentReference_error _ _ _ (by positivity)
    (fun r => h budget (q r) (w r) δ (hq0 r) (hq1 r) (hw0 r) (hw1 r) (herr r)) ψ

end InfoLossLAR.WorstCase.NativeCoherentAcceptanceError

end P2MDyadicModule99

/- Helper module Solutions.RegevBridgeCoherentWideGaussian. -/
section P2MDyadicModule100

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

theorem numericalProbability_bounds (x : PointRequest×ℕ) :
    0 ≤ numericalProbability x ∧ numericalProbability x ≤ 1 := by
  unfold numericalProbability
  split
  · rw [Integration9_9.TM2NativeFiniteDraw.clipped_eq]
    exact RationalAcceptanceCoin.clipped_bounds _
  · norm_num

theorem weight_bounds (input : PointRequest) (width : ℝ) (index : ℕ) :
    0 ≤ weight input width index ∧ weight input width index ≤ 1 := by
  unfold weight
  split
  · refine ⟨Real.exp_nonneg _,Real.exp_le_one_iff.mpr ?_⟩
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (div_nonneg Real.pi_pos.le (sq_nonneg _))
    · exact sq_nonneg _
  · norm_num

/-- Every binary ticket, including rejected out-of-window tickets, has a
uniform scalar error bound from the actual guarded rational evaluator. -/
theorem numericalProbability_error (input : PointRequest) (width : ℝ)
    (hsquare : width^2=(variance input : ℝ)) (index : ℕ) :
    |(numericalProbability (input,index) : ℝ)-weight input width index| ≤ 1/(2 : ℝ)^input.2.2.length := by
  by_cases hi : index < intervalCount input
  · simp only [numericalProbability,weight,if_pos hi,
      Integration9_9.TM2NativeFiniteDraw.clipped_eq]
    have htarget := weight_bounds input width index
    simp only [weight,if_pos hi] at htarget
    refine (RationalAcceptanceCoin.clipped_error _ _ htarget).trans ?_
    have h := pointValue_error input ⟨index,hi⟩
    have he : shiftedWeight width input.1.2 (point (input,index))=
        Real.exp (-Real.pi*((point (input,index) : ℝ)-(input.1.2 : ℝ))^2/(variance input : ℝ)) := by
      unfold shiftedWeight
      rw [hsquare]
      congr 1
      ring
    simpa only [he] using h
  · simp only [numericalProbability,weight,if_neg hi,Rat.cast_zero,sub_self,abs_zero]
    positivity

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

/-- The pure success branch has inverse-polynomial probability, independent
of the numerical magnitude of the binary Gaussian width. -/
theorem coherent_success_lower (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    1/(56*(input.2.1.length : ℝ)) ≤ ∑ ticket : Ticket input,‖CoherentWeightedPreparation.prepared
        (fun t : Ticket input => weight input width t.val) (true,ticket)‖^2 := by
  rw [CoherentWeightedPreparation.true_mass
      (fun t : Ticket input => weight input width t.val)
      (fun t => (weight_bounds input width t.val).1),
    CoherentWeightedPreparation.weightSum,sum_weight,Fintype.card_fin]
  simp only [ticketCount,Nat.cast_pow,Nat.cast_ofNat]
  exact ideal_trial_success_lower input width hwidth hsquare hfactor

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end P2MDyadicModule100

/- Helper module Solutions.RegevBridgeCoherentWideGaussianGates. -/
section P2MDyadicModule101
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

end P2MDyadicModule101

/- Helper module Solutions.RegevBridgeCoherentWideGaussianProposal. -/
section P2MDyadicModule102

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

theorem gateWordBits_exact (a : ℕ) (input : PointRequest) (budget : List Unit)
    (tape : Bits (Nat.size (intervalCount input))) :
    gateWordBits a ((input,List.ofFn tape),budget)=
      gateWord a ((input,(proposalTicket input tape).val),budget) := by
  simp only [gateWordBits,proposalTicket_value]

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end P2MDyadicModule102

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingBuilder. -/
section P2MDyadicModule103

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

open QAlgorithms QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

@[simp] theorem publicHeader_length (word : Str) : (publicHeader word).length=2*word.length+1 := by
  simp only [publicHeader,lengthToken,List.length_append,List.length_map,List.length_singleton]
  omega

@[simp] theorem paddedPublic_length (slots : List Unit) (word : Str) : (paddedPublic slots word).length=slots.length := by
  simp only [paddedPublic,List.length_take,List.length_append,List.length_map]
  omega

theorem paddedPublic_eq (slots : List Unit) (word : Str) (h : 2*word.length+1≤ slots.length) :
    paddedPublic slots word=publicHeader word++List.replicate (slots.length-(publicHeader word).length) false := by
  have hh : (publicHeader word).length≤ slots.length := by simpa only [publicHeader_length] using h
  simp only [paddedPublic,List.take_append,List.take_of_length_le hh]
  rw [List.map_const',List.take_replicate]
  congr 2
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

theorem parsePublic_exact (slots : List Unit) (word tape : Str)
    (h : 2*word.length+1≤ slots.length) : parsePublic (rawInput slots word tape)=(word,tape) := by
  have hp := paddedPublic_eq slots word h
  have hl := paddedPublic_length slots word
  simp only [parsePublic,rawInput,List.append_assoc,lengthToken_eq,readUnary_append,unarySlots_append,List.length_replicate]
  apply Prod.ext
  · rw [hp]
    simp only [publicHeader,List.append_assoc,lengthToken_eq,readUnary_append,unarySlots_append,List.length_replicate,List.take_left]
  · rw [←hl,List.drop_left]

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

theorem parse_exact (slots : List Unit) (word tape : Str) (h : 2*word.length+1≤ slots.length) :
    parse request (rawInput slots word tape)=
      (((request word).1,tape.take (Nat.size (intervalCount (request word).1))),(request word).2) := by
  simp only [parse,parsePublic_exact slots word tape h,Nat.size_eq_bits_len]

include hr in
@[fun_prop] theorem gateWord_poly (a : ℕ) : Poly (gateWord request a) := by
  unfold gateWord
  exact Poly.comp (gateWordBits_poly a) (parse_poly request hr)

noncomputable def wordBound (a : ℕ) : Polynomial ℕ :=
  (gateWord_poly request hr a).program.sizeBound.comp (3*Polynomial.X)

theorem gateWord_bound (a : ℕ) (word : Str) :
    (gateWord request a word).length≤(wordBound request hr a).eval word.length := by
  have h := (gateWord_poly request hr a).program.length_bound word
  have hl := EncodedList.length_le (enc : ℕ→Str) (gateWord request a word)
  change (encodeList enc (gateWord request a word)).length≤
    (gateWord_poly request hr a).program.sizeBound.eval (encodeList encodeBool word).length at h
  simpa only [wordBound,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,BooleanLists.length] using hl.trans h

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

end P2MDyadicModule103

/- Helper module Solutions.RegevBridgeNativeWordInputEmbedding. -/
section P2MDyadicModule104

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

def inputMap (n k : ℕ) (input : I → Str) : (Bits k×I → ℂ) →ₗ[ℂ] QState (width (P words hw p) n+k) :=
  (assembleMap _ k).comp (CoherentComputeUncompute.embedInputs (initialWork words hw p n ∘ input))

theorem inputMap_norm (n k : ℕ) (input : I → Str) (hlen : ∀ i,(input i).length=n)
    (hinj : Function.Injective input) (ψ : Bits k×I → ℂ) :
    stateNorm (inputMap words hw p n k input ψ)=‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits k×I))‖ := by
  have hwork : Function.Injective (initialWork words hw p n ∘ input) := by
    intro i j he
    apply hinj
    exact initialWork_injective words hw p n _ _ (hlen i) (hlen j) he
  unfold inputMap
  rw [LinearMap.comp_apply,assemble_norm,CoherentComputeUncompute.embedInputs_norm _ hwork]

theorem inputMap_error (n k : ℕ) (input : I → Str) (hlen : ∀ i,(input i).length=n)
    (hinj : Function.Injective input) (ψ φ : Bits k×I → ℂ) :
    stateNorm (inputMap words hw p n k input ψ-inputMap words hw p n k input φ)=
      ‖(WithLp.toLp 2 (ψ-φ) : EuclideanSpace ℂ (Bits k×I))‖ := by
  rw [←map_sub,inputMap_norm words hw p n k input hlen hinj]

theorem initialState_inputMap (n : ℕ) (input : I → Str) (ψ : Bits 3×I → ℂ) :
    initialState words hw p n input (fun i d => ψ (d,i))=inputMap words hw p n 3 input ψ := rfl

theorem cleanState_inputMap (n : ℕ) (input : I → Str) (ψ : Bits 3×I → ℂ) :
    cleanState words hw p n input (fun i d => ψ (d,i))=
      inputMap words hw p n 3 input (fun x => dataResult words (input x.2) (fun d => ψ (d,x.2)) x.1) := by
  simp only [inputMap,LinearMap.comp_apply,CoherentComputeUncompute.embedInputs,
    LinearMap.coe_mk,AddHom.coe_mk,map_sum,assemble_tensor,cleanState,Function.comp_apply]

/-- The literal whole native circuit is accurate on arbitrary coherent
encoded inputs. Its bound uses exactly the original joint-state norm. -/
theorem wholeCircuit_input_error (n a : ℕ) (ha : PhaseAccurate a) (budget : List Unit)
    (input : I → Str) (hlen : ∀ i,(input i).length=n) (hinj : Function.Injective input)
    (hbound : ∀ i,(words (input i)).length≤p.eval n) (ψ : Bits 3×I → ℂ) :
    stateNorm (runLayered (wholeCircuit words hw p n a budget)
      (initializeAux (inputMap words hw p n 3 input ψ))-
        initializeAux (inputMap words hw p n 3 input
          (fun x => dataResult words (input x.2) (fun d => ψ (d,x.2)) x.1)))≤
      (180*((p.eval n : ℕ) : ℝ)/((budget.length : ℝ)+1))*
        ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits 3×I))‖ := by
  have h := wholeCircuit_error words hw p n a ha budget input hlen (fun i d => ψ (d,i)) hbound
  rw [initialState_inputMap,cleanState_inputMap,inputMap_norm words hw p n 3 input hlen hinj] at h
  exact h

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule104

/- Helper module Solutions.RegevBridgeNativeQFTPlanRealization. -/
section P2MDyadicModule105

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open scoped BigOperators

noncomputable def initializeAuxLinearMap {n : ℕ} : QState n →ₗ[ℂ] QState (n+2) where
  toFun := initializeAux
  map_add' ψ φ := by funext x;simp [initializeAux];split_ifs <;> simp
  map_smul' z ψ := by funext x;simp [initializeAux]

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end

end P2MDyadicModule105

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPhysical. -/
section P2MDyadicModule106

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open QAlgorithms.Papers.Independent.Renew46.P12

open NativeWordCoherent NativeWordLayout ControlledNativeGates

open FiniteGateNativeEnumeration

theorem dependent_initialized {k r : ℕ} {R : Type*}
    (M : R → Matrix (Bits (k+r)) (Bits (k+r)) ℂ) (ψ : Bits k×R → ℂ) :
    applyDependentReference M (initWithReference (r:=r) ψ)=
      applyDependentReference (fun t => initializedMap (n:=k) (w:=r) (M t)) ψ := by
  funext x
  exact congrFun (applyWithReference_initialized (M x.2) ψ) x

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end

end P2MDyadicModule106

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingApproximation. -/
section P2MDyadicModule107

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent

open ControlledNativeGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem initialized_native_inputMap_error
    (words : Str→List ℕ) (hw : Poly words) (p : Polynomial ℕ) (n : ℕ)
    (input : I→Str) (hlen : ∀ i,(input i).length=n) (hinj : Function.Injective input)
    (ψ φ : Bits 3×I→ℂ) :
    stateNorm (initializeAux (NativeWordCoherent.inputMap words hw p n 3 input ψ)-
      initializeAux (NativeWordCoherent.inputMap words hw p n 3 input φ))=
      ‖(WithLp.toLp 2 (ψ-φ) : EuclideanSpace ℂ (Bits 3×I))‖ := by
  have he := NativeQFTPlanCompile.initializeAuxLinearMap.map_sub
    (NativeWordCoherent.inputMap words hw p n 3 input ψ)
    (NativeWordCoherent.inputMap words hw p n 3 input φ)
  change initializeAux (NativeWordCoherent.inputMap words hw p n 3 input ψ-
    NativeWordCoherent.inputMap words hw p n 3 input φ)=
    initializeAux (NativeWordCoherent.inputMap words hw p n 3 input ψ)-
    initializeAux (NativeWordCoherent.inputMap words hw p n 3 input φ) at he
  rw [←he]
  change ‖(WithLp.toLp 2 (initializeAux _) : EuclideanSpace ℂ _)‖=_
  rw [initializeAux_norm]
  exact NativeWordCoherent.inputMap_error words hw p n 3 input hlen hinj ψ φ

/-- A generic full-vector composition principle for the actual native
compute/interpret/uncompute family. Input bytes and every auxiliary remain. -/
theorem wholeCircuit_input_approximation
    (words : Str→List ℕ) (hw : Poly words) (p : Polynomial ℕ)
    (n a : ℕ) (ha : PhaseAccurate a) (budget : List Unit)
    (input : I→Str) (hlen : ∀ i,(input i).length=n) (hinj : Function.Injective input)
    (hbound : ∀ i,(words (input i)).length≤p.eval n)
    (ψ φ : Bits 3×I→ℂ) (ε : ℝ)
    (hε : ‖(WithLp.toLp 2 ((fun x => dataResult words (input x.2)
        (fun d => ψ (d,x.2)) x.1)-φ) : EuclideanSpace ℂ (Bits 3×I))‖≤
      ε*‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits 3×I))‖) :
    stateNorm (runLayered (wholeCircuit words hw p n a budget)
      (initializeAux (NativeWordCoherent.inputMap words hw p n 3 input ψ))-
      initializeAux (NativeWordCoherent.inputMap words hw p n 3 input φ))≤
      (180*((p.eval n : ℕ) : ℝ)/((budget.length : ℝ)+1)+ε)*
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits 3×I))‖ := by
  let actualData : Bits 3×I→ℂ := fun x => dataResult words (input x.2) (fun d => ψ (d,x.2)) x.1
  have hfirst := wholeCircuit_input_error words hw p n a ha budget input hlen hinj hbound ψ
  have hsecond : stateNorm
      (initializeAux (NativeWordCoherent.inputMap words hw p n 3 input actualData)-
       initializeAux (NativeWordCoherent.inputMap words hw p n 3 input φ))≤
      ε*‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits 3×I))‖ := by
    rw [initialized_native_inputMap_error words hw p n input hlen hinj]
    exact hε
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (WithLp.toLp 2 (runLayered (wholeCircuit words hw p n a budget)
      (initializeAux (NativeWordCoherent.inputMap words hw p n 3 input ψ))))
    (WithLp.toLp 2 (initializeAux (NativeWordCoherent.inputMap words hw p n 3 input actualData)))
    (WithLp.toLp 2 (initializeAux (NativeWordCoherent.inputMap words hw p n 3 input φ)))
  change stateNorm _≤ stateNorm _+stateNorm _ at ht
  exact ht.trans ((add_le_add hfirst hsecond).trans_eq (add_mul _ _ _).symm)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

end

end P2MDyadicModule107

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingBuilderPhysical. -/
section P2MDyadicModule108

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

theorem gateWord_encoded (a : ℕ) (slots : List Unit) (word : Str)
    (h : 2*word.length+1≤ slots.length) {K : ℕ}
    (hK : Nat.size (intervalCount (request word).1)≤K) (tape : Bits K) :
    gateWord request a (encoded slots word tape)=
      Coherent.gateWord a (((request word).1,
        (Padding.activeTicket (request word).1 hK tape).val),(request word).2) := by
  rw [gateWord,encoded,parse_exact request slots word (List.ofFn tape) h,
    ←Fin.ofFn_take_eq_take_ofFn hK]
  exact gateWordBits_exact a (request word).1 (request word).2 _

def inputMap (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    (Bits 3×Bits K→ℂ) →ₗ[ℂ] QState
      (width (P (gateWord request a) (gateWord_poly request hr a) (wordBound request hr a))
        (2*slots.length+1+K)+3) :=
  NativeWordCoherent.inputMap (gateWord request a) (gateWord_poly request hr a)
    (wordBound request hr a) (2*slots.length+1+K) 3 (encoded slots word)

def physicalCircuit (synthesis interpreter : ℕ) (slots : List Unit) (K : ℕ)
    (interpreterBudget : List Unit) :=
  wholeCircuit (gateWord request synthesis) (gateWord_poly request hr synthesis)
    (wordBound request hr synthesis) (2*slots.length+1+K) interpreter interpreterBudget

/-- This concrete family keeps the original binary basis/control word in
its input register. Every point parameter is computed inside the native
program and the complete work is uncomputed. Compiler exponents are fixed
before all input values, capacities and unary accuracy budgets. -/
theorem exists_physicalCircuit_accuracy :
    ∃ synthesis : ℕ,0<synthesis ∧ ∀ interpreter : ℕ,PhaseAccurate interpreter →
      ∀ (slots : List Unit) (word : Str) (s : ℝ) (interpreterBudget : List Unit)
        (h : 2*word.length+1≤ slots.length) (K : ℕ)
        (hK : Nat.size (intervalCount (request word).1)≤K),
      s^2=(variance (request word).1 : ℝ) → ∀ ψ : Bits 1×Bits K→ℂ,
      stateNorm (runLayered (physicalCircuit request hr synthesis interpreter slots K interpreterBudget)
        (initializeAux (inputMap request hr synthesis slots word K (initWithReference (r:=2) ψ)))-
        initializeAux (inputMap request hr synthesis slots word K
          (applyDependentReference (fun tape => idealMap (NativeCoherentAcceptanceError.realIdeal
            (weight (request word).1 s (Padding.activeTicket (request word).1 hK tape).val)) 2) ψ)))≤
        (180*(((wordBound request hr synthesis).eval (2*slots.length+1+K) : ℕ) : ℝ)/
          ((interpreterBudget.length : ℝ)+1)+
          (5/(((request word).2.length : ℝ)+1)+2*Real.sqrt (1/(2 : ℝ)^((request word).1.2.2.length))))*
        ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits 1×Bits K))‖ := by
  obtain ⟨a,ha,h⟩ := NativeCoherentAcceptanceError.exists_coherent_accuracy
  refine ⟨a,ha,?_⟩
  intro interpreter hi slots word s interpreterBudget hh K hK hs ψ
  have hg := h (Bits K) (request word).2
    (fun tape => numericalProbability ((request word).1,(Padding.activeTicket (request word).1 hK tape).val))
    (fun tape => weight (request word).1 s (Padding.activeTicket (request word).1 hK tape).val) _ (by positivity)
    (fun _ => (numericalProbability_bounds _).1) (fun _ => (numericalProbability_bounds _).2)
    (fun _ => (weight_bounds _ _ _).1) (fun _ => (weight_bounds _ _ _).2)
    (fun _ => numericalProbability_error _ _ hs _) ψ
  have hd : (fun x : Bits 3×Bits K =>
      dataResult (gateWord request a) (encoded slots word x.2)
        (fun d => initWithReference (r:=2) ψ (d,x.2)) x.1)=
      applyDependentReference (fun tape => initializedMap (n:=1) (w:=2)
        (matrix (interpreted (Coherent.gateWord a (((request word).1,
          (Padding.activeTicket (request word).1 hK tape).val),(request word).2))))) ψ := by
    rw [←Coherent.dependent_initialized (k:=1) (r:=2)]
    funext x
    simp only [dataResult,gateWord_encoded request a slots word hh hK,applyDependentReference,matrix_mulVec]
  have he : ‖(WithLp.toLp 2
      ((fun x : Bits 3×Bits K => dataResult (gateWord request a) (encoded slots word x.2)
        (fun d => initWithReference (r:=2) ψ (d,x.2)) x.1)-
       applyDependentReference (fun tape => idealMap (NativeCoherentAcceptanceError.realIdeal
         (weight (request word).1 s (Padding.activeTicket (request word).1 hK tape).val)) 2) ψ) :
        EuclideanSpace ℂ (Bits 3×Bits K))‖≤
      (5/(((request word).2.length : ℝ)+1)+2*Real.sqrt (1/(2 : ℝ)^((request word).1.2.2.length)))*
        ‖(WithLp.toLp 2 (initWithReference (r:=2) ψ) : EuclideanSpace ℂ (Bits 3×Bits K))‖ := by
    rw [hd,initWithReference_norm]
    exact hg
  have hf := wholeCircuit_input_approximation (gateWord request a) (gateWord_poly request hr a)
    (wordBound request hr a) (2*slots.length+1+K) interpreter hi interpreterBudget
    (encoded slots word) (encoded_length slots word) (encoded_injective slots word K)
    (fun tape => by simpa only [encoded_length] using gateWord_bound request hr a (encoded slots word tape))
    (initWithReference (r:=2) ψ)
    (applyDependentReference (fun tape => idealMap (NativeCoherentAcceptanceError.realIdeal
      (weight (request word).1 s (Padding.activeTicket (request word).1 hK tape).val)) 2) ψ) _ he
  rw [initWithReference_norm] at hf
  exact hf

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

end

end P2MDyadicModule108

/- Helper module Solutions.RegevBridgeCoherentPaddedInputPreparation. -/
section P2MDyadicModule109

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentPaddedInputPreparation

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentComputeUncompute

open NativeWordCoherent NativeWordLayout ControlledNativeGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean

open scoped BigOperators

variable (words : Str→List ℕ) (hw : Poly words) (p : Polynomial ℕ) (headerBits : Str) (K : ℕ)

abbrev inputLength : ℕ := headerBits.length+K

abbrev workSize : ℕ := width (P words hw p) (inputLength headerBits K)

def fullBasis (tape : Bits K) : Bits (workSize words hw p headerBits K+3+2) :=
  fun j => wordExtension (headerBits++List.ofFn tape) j.val

def ticketWires : Fin K↪Fin (workSize words hw p headerBits K+3+2) where
  toFun i := ⟨headerBits.length+i.val,by unfold workSize width inputLength;omega⟩
  inj' := by intro i j h;apply Fin.ext;exact Nat.add_left_cancel (congrArg (fun x : Fin (workSize words hw p headerBits K+3+2) => x.val) h)

@[simp] theorem ticketWires_val (i : Fin K) :
    (ticketWires words hw p headerBits K i).val=headerBits.length+i.val := rfl

@[simp] theorem fullBasis_selected (tape : Bits K) (i : Fin K) :
    fullBasis words hw p headerBits K tape (ticketWires words hw p headerBits K i)=tape i := by
  unfold fullBasis
  rw [ticketWires_val,wordExtension_before _ _ (by simp only [List.length_append,List.length_ofFn];omega)]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,List.getElem_ofFn]

/-- Varying a raw ticket changes exactly the fixed public ticket wires;
the original binary headerBits and all zero native work are unchanged. -/
theorem fullBasis_split (tape : Bits K) :
    wireBitsEquiv (ticketWires words hw p headerBits K) (fullBasis words hw p headerBits K tape)=
      (tape,(wireBitsEquiv (ticketWires words hw p headerBits K)
        (fullBasis words hw p headerBits K (fun _ => false))).2) := by
  apply Prod.ext
  · funext i
    exact fullBasis_selected words hw p headerBits K tape i
  · funext j
    change wordExtension (headerBits++List.ofFn tape) j.val.val=
      wordExtension (headerBits++List.ofFn (fun _ : Fin K => false)) j.val.val
    by_cases hj : j.val.val<headerBits.length
    · rw [wordExtension_before _ _ (by simp only [List.length_append,List.length_ofFn];omega),
        wordExtension_before _ _ (by simp only [List.length_append,List.length_ofFn];omega)]
      simp only [List.getElem_append_left hj]
    · have ht : headerBits.length+K≤j.val.val := by
        by_contra hnot
        have hi : j.val.val-headerBits.length<K := by omega
        apply j.property
        refine ⟨⟨j.val.val-headerBits.length,hi⟩,?_⟩
        apply Fin.ext
        simp only [ticketWires_val]
        omega
      rw [wordExtension_after _ _ (by simp only [List.length_append,List.length_ofFn];exact ht),
        wordExtension_after _ _ (by simp only [List.length_append,List.length_ofFn];exact ht)]

def fullEmbedding : Bits K↪Bits (workSize words hw p headerBits K+3+2) where
  toFun := fullBasis words hw p headerBits K
  inj' := by
    intro a b h
    funext i
    have he:=congrArg (fun bits => bits (ticketWires words hw p headerBits K i)) h
    simpa only [fullBasis_selected] using he

theorem fullEmbedding_eq :
    initializedWireEmbedding (ticketWires words hw p headerBits K)
      (wireBitsEquiv (ticketWires words hw p headerBits K)
        (fullBasis words hw p headerBits K (fun _ => false))).2=
      fullEmbedding words hw p headerBits K := by
  apply Function.Embedding.ext
  intro tape
  apply (wireBitsEquiv (ticketWires words hw p headerBits K)).injective
  change wireBitsEquiv (ticketWires words hw p headerBits K)
    ((wireBitsEquiv (ticketWires words hw p headerBits K)).symm (tape,
      (wireBitsEquiv (ticketWires words hw p headerBits K)
        (fullBasis words hw p headerBits K (fun _ => false))).2))=
    wireBitsEquiv (ticketWires words hw p headerBits K) (fullBasis words hw p headerBits K tape)
  rw [Equiv.apply_symm_apply]
  exact (fullBasis_split words hw p headerBits K tape).symm

def initialData : Bits 3×Bits K→ℂ := fun x => coinAmplitude K*basis (fun _ => false) x.1

def initial : QState (workSize words hw p headerBits K+3+2) :=
  initializeAux (NativeWordCoherent.inputMap words hw p (inputLength headerBits K) 3
    (fun tape : Bits K => headerBits++List.ofFn tape) (initialData K))

theorem initializeAux_basis {n : ℕ} (bits : Bits n) :
    initializeAux (basis bits)=basis (Fin.append bits (fun _ : Fin 2 => false)) := by
  funext x
  obtain ⟨⟨a,b⟩,rfl⟩ := (qubitsAppendEquiv n 2).symm.surjective x
  change initializeAux (basis bits) (Fin.append a b)=basis (Fin.append bits (fun _ : Fin 2 => false)) (Fin.append a b)
  simp only [initializeAux,Fin.append_left,Fin.append_right,basis,CoherentXorCopy.append_eq_iff]
  by_cases hb : b=(fun _ => false) <;> by_cases ha : a=bits <;> simp [hb,ha]

theorem fullBasis_append (tape : Bits K) :
    fullBasis words hw p headerBits K tape=
      Fin.append (Fin.append (NativeWordCoherent.initialWork words hw p
        (inputLength headerBits K) (headerBits++List.ofFn tape)) (fun _ : Fin 3 => false)) (fun _ : Fin 2 => false) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [fullBasis,NativeWordCoherent.initialWork,Fin.append_left,Fin.val_castAdd]
    · intro j
      simp only [fullBasis,Fin.append_left,Fin.append_right,Fin.val_castAdd,Fin.val_natAdd]
      apply wordExtension_after
      simp only [List.length_append,List.length_ofFn]
      unfold workSize width inputLength
      omega
  · intro j
    simp only [fullBasis,Fin.append_right,Fin.val_natAdd]
    apply wordExtension_after
    simp only [List.length_append,List.length_ofFn]
    unfold workSize width inputLength
    omega

/-- The native input embedding is exactly the full positive uniform raw
binary ticket superposition, with the same original public headerBits. -/
theorem initial_expansion : initial words hw p headerBits K=
    basisEmbedding (fullEmbedding words hw p headerBits K) (fun _ => coinAmplitude K) := by
  change initializeAux (assembleMap _ 3 (∑ tape : Bits K,
    tensor (fun data => initialData K (data,tape))
      (NativeWordCoherent.initialWork words hw p (inputLength headerBits K) (headerBits++List.ofFn tape))))=_
  rw [map_sum]
  have hs (F : Bits K→QState (workSize words hw p headerBits K+3)) :
      initializeAux (∑ tape,F tape)=∑ tape,initializeAux (F tape) := by
    funext x
    by_cases h : (fun j : Fin 2 => x (Fin.natAdd (workSize words hw p headerBits K+3) j))=(fun _ => false)
    · simp only [initializeAux,h,if_true,Finset.sum_apply]
    · simp only [Finset.sum_apply,initializeAux,h,if_false,Finset.sum_const_zero]
  rw [hs]
  change (∑ tape : Bits K,initializeAux (assembleMap _ 3
    (tensor (fun data => initialData K (data,tape))
      (NativeWordCoherent.initialWork words hw p (inputLength headerBits K) (headerBits++List.ofFn tape)))))=
    ∑ tape : Bits K,coinAmplitude K •basis (fullBasis words hw p headerBits K tape)
  apply Finset.sum_congr rfl
  intro tape _
  have ht (work : Bits (workSize words hw p headerBits K)) :
      tensor (fun data => initialData K (data,tape)) work=
        coinAmplitude K •tensor (basis (fun _ : Fin 3 => false)) work := by
    funext x
    simp only [tensor,initialData,Pi.smul_apply,smul_eq_mul,mul_assoc]
  rw [ht,map_smul,CoherentPublicPreparation.assemble_basis]
  rw [show initializeAux (coinAmplitude K •basis
      (Fin.append (NativeWordCoherent.initialWork words hw p (inputLength headerBits K)
        (headerBits++List.ofFn tape)) (fun _ : Fin 3 => false)))=
      coinAmplitude K •initializeAux (basis
      (Fin.append (NativeWordCoherent.initialWork words hw p (inputLength headerBits K)
        (headerBits++List.ofFn tape)) (fun _ : Fin 3 => false))) from
    NativeQFTPlanCompile.initializeAuxLinearMap.map_smul (coinAmplitude K) _]
  rw [initializeAux_basis,fullBasis_append]

/-- Literal fixed-position H gates prepare exactly the input state used by
the already proved padded native Gaussian interpreter. -/
theorem actual_hadamard_prepares :
    runLayered (relocateCircuit (ticketWires words hw p headerBits K) (coinCircuit K))
      (basis (fullBasis words hw p headerBits K (fun _ => false)))=initial words hw p headerBits K := by
  rw [←CoherentPublicPreparation.initializedWires_basis (ticketWires words hw p headerBits K)
    (fullBasis words hw p headerBits K (fun _ => false))]
  have hz : (wireBitsEquiv (ticketWires words hw p headerBits K)
      (fullBasis words hw p headerBits K (fun _ => false))).1=(fun _ => false) := by
    exact congrArg Prod.fst (fullBasis_split words hw p headerBits K (fun _ => false))
  rw [hz]
  change runLayered (relocateCircuit (ticketWires words hw p headerBits K) (coinCircuit K))
    (initializedWires (ticketWires words hw p headerBits K) _ (coinZero K))=_
  rw [relocateCircuit_initialized,coinCircuit_uniform,initializedWires_eq_embedding,fullEmbedding_eq,initial_expansion]

end InfoLossLAR.WorstCase.CoherentPaddedInputPreparation

end

end P2MDyadicModule109

/- Helper module Solutions.RegevBridgeCoherentRejectionPure. -/
section P2MDyadicModule110

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentRejection

open scoped BigOperators

open CoherentProjection

variable {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O] {m : ℕ}

noncomputable def completeState (zero : O) (single : Bool → O → J → ℂ) :
    EuclideanSpace ℂ (O×Retained O J m) :=
  WithLp.toLp 2 (fun x => swappedState zero single x.2.1 (x.1,x.2.2))

noncomputable def completeJunk (zero : O) (single : Bool → O → J → ℂ)
    (alpha : ℂ) (junk : J → ℂ) : EuclideanSpace ℂ (Retained O J m) :=
  WithLp.toLp 2 (fun x => garbageAmplitude zero single alpha junk x.1 x.2)

def succeeded (x : O×Retained O J m) : Prop := firstSuccess x.2.1≠none

instance succeeded_decidable : DecidablePred (succeeded (O:=O) (J:=J) (m:=m)) :=
  fun _ => inferInstanceAs (Decidable (_≠none))

theorem completeState_norm (zero : O) (single : Bool → O → J → ℂ)
    (hnorm : flagMass single false+flagMass single true=1) :
    ‖completeState (m:=m) zero single‖=1 := by
  have h := complete_mass (m:=m) zero single hnorm
  have hn : ‖completeState (m:=m) zero single‖^2=1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [completeState,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using h
  nlinarith [norm_nonneg (completeState (m:=m) zero single)]

theorem completeState_failure (zero : O) (single : Bool → O → J → ℂ) (p : ℝ)
    (hfail : flagMass single false=1-p) :
    (∑ x : O×Retained O J m,
      if succeeded x then 0 else ‖completeState zero single x‖^2)=(1-p)^m := by
  have h := failure_mass (m:=m) zero single p hfail
  have he (x : O×Retained O J m) :
      (if succeeded x then 0 else ‖completeState zero single x‖^2)=
      (if firstSuccess x.2.1=none then ‖swappedState zero single x.2.1 (x.1,x.2.2)‖^2 else 0) := by
    by_cases hx : firstSuccess x.2.1=none <;> simp [succeeded,completeState,hx]
  simp_rw [he]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type] using h

/-- The projection keeps all flags and all unselected copies; its exact
factorization is inherited from the reversible first-success output swap. -/
theorem completeState_factor (zero : O) (single : Bool → O → J → ℂ)
    (alpha : ℂ) (target : O → ℂ) (junk : J → ℂ)
    (hsingle : ∀ o j,single true o j=alpha*target o*junk j) :
    project succeeded (completeState (m:=m) zero single)=
      InfoLossLAR.WorstCase.CoherentProjection.tensorState (WithLp.toLp 2 target) (completeJunk zero single alpha junk) := by
  ext x
  have h := success_factorization zero single alpha target junk hsingle x.2.1 (x.1,x.2.2)
  by_cases hx : firstSuccess x.2.1=none <;>
    simpa [project,succeeded,completeState,completeJunk,InfoLossLAR.WorstCase.CoherentProjection.tensorState,hx] using h

/-- Bounded coherent rejection prepares a pure target unconditionally, up
to the square root of its all-failure probability. The retained registers are
explicit, and no measurement or postselection is used in this statement. -/
theorem completeState_pure_close (zero : O) (single : Bool → O → J → ℂ)
    (alpha : ℂ) (target : O → ℂ) (junk : J → ℂ)
    (hsingle : ∀ o j,single true o j=alpha*target o*junk j)
    (htarget : ∑ o,‖target o‖^2=1) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hm : m≠0) (hfail : flagMass single false=1-p)
    (hnorm : flagMass single false+flagMass single true=1) :
    ∃ clean : EuclideanSpace ℂ (Retained O J m),‖clean‖=1 ∧
      ‖completeState (m:=m) zero single-InfoLossLAR.WorstCase.CoherentProjection.tensorState (WithLp.toLp 2 target) clean‖ ≤
        2*Real.sqrt ((1-p)^m) := by
  have hpow : (1-p)^m < 1 := pow_lt_one₀ (by linarith) (by linarith) hm
  have hj : completeJunk (m:=m) zero single alpha junk≠0 := by
    intro hz
    have h := successful_garbage_mass (m:=m) zero single alpha target junk
      hsingle htarget p hfail hnorm
    have hzero : (∑ flags : Fin m → Bool,∑ copies : Fin m → O×J,
        ‖garbageAmplitude zero single alpha junk flags copies‖^2)=0 := by
      have hn := congrArg (fun v : EuclideanSpace ℂ (Retained O J m) => ‖v‖^2) hz
      simpa only [EuclideanSpace.norm_sq_eq,completeJunk,Fintype.sum_prod_type,
        norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] using hn
    linarith
  have ht : ‖(WithLp.toLp 2 target : EuclideanSpace ℂ O)‖=1 := by
    have hs : ‖(WithLp.toLp 2 target : EuclideanSpace ℂ O)‖^2=1 := by
      simpa only [EuclideanSpace.norm_sq_eq] using htarget
    nlinarith [norm_nonneg (WithLp.toLp 2 target : EuclideanSpace ℂ O)]
  exact pure_success_close succeeded (completeState zero single)
    (WithLp.toLp 2 target) (completeJunk zero single alpha junk)
    (completeState_norm zero single hnorm) ht hj
    (completeState_factor zero single alpha target junk hsingle) ((1-p)^m)
    (completeState_failure zero single p hfail).le

end InfoLossLAR.WorstCase.CoherentRejection

end P2MDyadicModule110

/- Helper module Solutions.RegevBridgeCoherentProductError. -/
section P2MDyadicModule111

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

end P2MDyadicModule111

/- Helper module Solutions.RegevBridgeCoherentRejectionError. -/
section P2MDyadicModule112

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentRejection

open CoherentProjection

open scoped BigOperators

variable {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O] {m : ℕ}

def splitCopies : (Fin m → Bool×(O×J)) ≃ Retained O J m where
  toFun x := (fun i => (x i).1,fun i => (x i).2)
  invFun x := fun i => (x.1 i,x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def completeSwap : (O×Retained O J m) ≃ (O×Retained O J m) where
  toFun x := let y := selectedSwap x.2.1 (x.1,x.2.2); (y.1,(x.2.1,y.2))
  invFun x := let y := (selectedSwap x.2.1).symm (x.1,x.2.2); (y.1,(x.2.1,y.2))
  left_inv x := by simp only [Prod.eta,Equiv.symm_apply_apply]
  right_inv x := by simp only [Prod.eta,Equiv.apply_symm_apply]

noncomputable def initialCopies (zero : O) (ψ : EuclideanSpace ℂ (Fin m → Bool×(O×J))) :
    EuclideanSpace ℂ (O×Retained O J m) :=
  WithLp.toLp 2 (fun x => if x.1=zero then ψ (splitCopies.symm x.2) else 0)

theorem initialCopies_norm (zero : O) (ψ : EuclideanSpace ℂ (Fin m → Bool×(O×J))) :
    ‖initialCopies zero ψ‖=‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,initialCopies,Fintype.sum_prod_type]
  have hsum : (∑ o : O,∑ r : Retained O J m,
      ‖(if o=zero then ψ (splitCopies.symm r) else 0 : ℂ)‖^2)=
      ∑ r : Retained O J m,‖ψ (splitCopies.symm r)‖^2 := by
    rw [Finset.sum_eq_single zero]
    · simp
    · intro o _ ho; simp [ho]
    · simp
  have he := Fintype.sum_equiv (splitCopies (O:=O) (J:=J) (m:=m)).symm
    (fun r => ‖ψ (splitCopies.symm r)‖^2) (fun r => ‖ψ r‖^2) (by intro r;rfl)
  simpa only [Fintype.sum_prod_type] using hsum.trans he

theorem initialCopies_sub (zero : O) (ψ φ : EuclideanSpace ℂ (Fin m → Bool×(O×J))) :
    initialCopies zero ψ-initialCopies zero φ=initialCopies zero (ψ-φ) := by
  ext x
  by_cases hx : x.1=zero <;> simp [initialCopies,hx]

noncomputable def swapState (ψ : EuclideanSpace ℂ (O×Retained O J m)) :
    EuclideanSpace ℂ (O×Retained O J m) := WithLp.toLp 2 (fun x => ψ (completeSwap x))

theorem swapState_norm (ψ : EuclideanSpace ℂ (O×Retained O J m)) : ‖swapState ψ‖=‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,swapState]
  exact Fintype.sum_equiv completeSwap _ _ (by intro x;rfl)

theorem swapState_sub (ψ φ : EuclideanSpace ℂ (O×Retained O J m)) :
    swapState ψ-swapState φ=swapState (ψ-φ) := rfl

noncomputable def singleVector (single : Bool → O → J → ℂ) : EuclideanSpace ℂ (Bool×(O×J)) :=
  WithLp.toLp 2 (fun x => single x.1 x.2.1 x.2.2)

theorem singleVector_norm (single : Bool → O → J → ℂ)
    (hn : flagMass single false+flagMass single true=1) : ‖singleVector single‖=1 := by
  have hs : ‖singleVector single‖^2=1 := by
    simp only [EuclideanSpace.norm_sq_eq,singleVector,Fintype.sum_prod_type,Fintype.sum_bool]
    change flagMass single true+flagMass single false=1
    linarith
  nlinarith [norm_nonneg (singleVector single)]

theorem completeState_as_copies (zero : O) (single : Bool → O → J → ℂ) :
    completeState (m:=m) zero single=
      swapState (initialCopies zero (repeatState m (singleVector single))) := rfl

/-- The exact reversible selection preserves the product-state error.
Every failed branch, unused copy and auxiliary remains in this norm. -/
theorem completeState_error (zero : O) (actual ideal : Bool → O → J → ℂ)
    (ha : flagMass actual false+flagMass actual true=1)
    (hi : flagMass ideal false+flagMass ideal true=1) (ε : ℝ)
    (he : ‖singleVector actual-singleVector ideal‖≤ε) :
    ‖completeState (m:=m) zero actual-completeState zero ideal‖≤(m : ℝ)*ε := by
  rw [completeState_as_copies,completeState_as_copies,swapState_sub,swapState_norm,
    initialCopies_sub,initialCopies_norm]
  exact repeatState_error m _ _ (singleVector_norm actual ha) (singleVector_norm ideal hi) ε he

/-- A physically approximate normalized trial inherits the ideal pure
success target after a fixed number of reversible attempts, without
postselection or an unproved branch-independent garbage assumption. -/
theorem completeState_approx_pure (zero : O) (actual ideal : Bool → O → J → ℂ)
    (ha : flagMass actual false+flagMass actual true=1)
    (hi : flagMass ideal false+flagMass ideal true=1) (ε : ℝ)
    (he : ‖singleVector actual-singleVector ideal‖≤ε)
    (alpha : ℂ) (target : O → ℂ) (junk : J → ℂ)
    (hsingle : ∀ o j,ideal true o j=alpha*target o*junk j)
    (htarget : ∑ o,‖target o‖^2=1) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hm : m≠0) (hfail : flagMass ideal false=1-p) :
    ∃ clean : EuclideanSpace ℂ (Retained O J m),‖clean‖=1 ∧
      ‖completeState (m:=m) zero actual-InfoLossLAR.WorstCase.CoherentProjection.tensorState (WithLp.toLp 2 target) clean‖≤
        (m : ℝ)*ε+2*Real.sqrt ((1-p)^m) := by
  obtain ⟨clean,hn,hc⟩ := completeState_pure_close zero ideal alpha target junk
    hsingle htarget p hp0 hp1 hm hfail hi
  refine ⟨clean,hn,?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ (completeState zero ideal) _).trans
    (add_le_add (completeState_error zero actual ideal ha hi ε he) hc)

end InfoLossLAR.WorstCase.CoherentRejection

end P2MDyadicModule112

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPure. -/
section P2MDyadicModule113

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open CoherentWeightedPreparation CoherentProjection

open scoped BigOperators

noncomputable def successProbability (input : PointRequest) (width : ℝ) : ℝ :=
  weightSum (fun t : Ticket input => weight input width t.val)/(ticketCount input : ℝ)

noncomputable def single (input : PointRequest) (width : ℝ) : Bool → Ticket input → Unit → ℂ :=
  fun flag t _ => prepared (fun t : Ticket input => weight input width t.val) (flag,t)

theorem single_false_mass (input : PointRequest) (width : ℝ) :
    CoherentRejection.flagMass (single input width) false=1-successProbability input width := by
  simpa only [CoherentRejection.flagMass,single,Fintype.sum_unique,Fintype.card_fin,
    successProbability] using false_mass (fun t : Ticket input => weight input width t.val)
      (fun t => (weight_bounds input width t.val).2)

theorem successProbability_bounds (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    1/(56*(input.2.1.length : ℝ)) ≤ successProbability input width ∧
      successProbability input width ≤ 1 := by
  constructor
  · have h := coherent_success_lower input width hwidth hsquare hfactor
    rw [true_mass (fun t : Ticket input => weight input width t.val)
      (fun t => (weight_bounds input width t.val).1),Fintype.card_fin] at h
    exact h
  · have h : 0 ≤ CoherentRejection.flagMass (single input width) false :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [single_false_mass] at h
    linarith

/-- A real-valued estimate for the all-failure amplitude, used only in the
analysis; it is not an oracle supplied to the circuit generator. -/
theorem failure_sqrt_exp (p η : ℝ) (hp1 : p ≤ 1) (hη : η ≤ p) (m : ℕ) :
    Real.sqrt ((1-p)^m) ≤ Real.exp (-(m : ℝ)*η/2) := by
  have hone : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1-p) hone m
  rw [←Real.exp_nat_mul] at hpow
  have hexp : Real.exp ((m : ℝ)*(-p)) ≤ Real.exp (-(m : ℝ)*η) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have hs := Real.sqrt_le_sqrt (hpow.trans hexp)
  have heq : Real.exp (-(m : ℝ)*η/2)^2=Real.exp (-(m : ℝ)*η) := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [←heq,Real.sqrt_sq (Real.exp_pos _).le] at hs
  exact hs

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end P2MDyadicModule113

/- Helper module Solutions.RegevBridgeCoherentWideGaussianTrial. -/
section P2MDyadicModule114

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent NativeWordLayout

open QAlgorithms.Papers.Independent.Renew46.P12

open CoherentWeightedPreparation CoherentComputeUncompute ControlledNativeGates

open scoped BigOperators

abbrev TrialJunk := Bits 2×Bits 2

def reorderTrial (W : ℕ) : ((Bits W×(Bool×Bits 2))×Bits 2) ≃ Bool×(Bits W×TrialJunk) where
  toFun x := (x.1.2.1,(x.1.1,(x.1.2.2,x.2)))
  invFun x := ((x.2.1,(x.1,x.2.2.1)),x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reorder only: the success flag, entire original input/work register,
two synthesis ancillas and two interpreter ancillas are all retained. -/
def trialCoordinates (W : ℕ) : Bits (W+3+2) ≃ Bool×(Bits W×TrialJunk) :=
  (qubitsAppendEquiv (W+3) 2).trans
    ((Equiv.prodCongr (qubitsAppendEquiv W 3) (Equiv.refl (Bits 2))).trans
      ((Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (Bits W)) (qubitsAppendEquiv 1 2))
        (Equiv.refl (Bits 2))).trans
        ((Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (Bits W))
          (Equiv.prodCongr oneBitEquiv (Equiv.refl (Bits 2)))) (Equiv.refl (Bits 2))).trans
          (reorderTrial W))))

theorem trialCoordinates_symm (W : ℕ) (flag : Bool) (work : Bits W) (junk : TrialJunk) :
    (trialCoordinates W).symm (flag,(work,junk))=
      Fin.append (Fin.append work (Fin.append (fun _ : Fin 1 => flag) junk.1)) junk.2 := rfl

theorem dependent_ideal {k r : ℕ} {R : Type*}
    (M : R → Matrix (Bits k) (Bits k) ℂ) (ψ : Bits k×R → ℂ) :
    applyDependentReference (fun t => idealMap (M t) r) ψ=
      initWithReference (r:=r) (applyDependentReference M ψ) := by
  funext x
  exact congrFun (applyWithReference_ideal (M x.2) ψ) x

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end

end P2MDyadicModule114

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingProposal. -/
section P2MDyadicModule115

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

theorem weightAverage_product (w : O→ℝ) :
    weightSum (fun x : O×E => w x.1)/(Fintype.card (O×E) : ℝ)=
      weightSum w/(Fintype.card O : ℝ) := by
  have hn : (Fintype.card E : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  rw [weightSum_product,Fintype.card_prod,Nat.cast_mul]
  field_simp

end Product

section Reindex

variable {O E : Type*} [Fintype O] [Fintype E] [Nonempty O] [Nonempty E]

theorem weightSum_equiv (e : O≃E) (w : E→ℝ) : weightSum (fun x => w (e x))=weightSum w := by
  exact Fintype.sum_equiv e _ _ (by intro i;rfl)

end Reindex

/-- All public capacity qubits receive H. Under the exact register split,
the inactive suffix is a retained positive uniform tensor factor. -/
def ticketEquiv (input : PointRequest) (extra : ℕ) :
    Bits (Nat.size (intervalCount input)+extra)≃Ticket input×Bits extra :=
  (qubitsAppendEquiv _ extra).trans (Equiv.prodCongr (proposalTicket input) (Equiv.refl _))

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

end

end P2MDyadicModule115

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingPreparation. -/
section P2MDyadicModule116

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2500000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Preparation

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentWeightedPreparation

open CoherentComputeUncompute ControlledNativeGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

/-- The same standard positive proposal as the proved Gaussian trial,
now over a fixed public K-bit ticket cube. -/
def proposalInitial (K : ℕ) : Bits 1×Bits K→ℂ :=
  fun x => CoherentWeightedPreparation.initial (oneBitEquiv x.1,x.2)

theorem proposalInitial_value (K : ℕ) (x : Bits 1×Bits K) :
    proposalInitial K x=if oneBitEquiv x.1 then 0 else coinAmplitude K := by
  rw [coinAmplitude_sqrt]
  simp only [proposalInitial,CoherentWeightedPreparation.initial,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

theorem initialized_proposal (K : ℕ) :
    initWithReference (r:=2) (proposalInitial K)=CoherentPaddedInputPreparation.initialData K := by
  funext x
  rcases x with ⟨data,tape⟩
  obtain ⟨⟨flag,aux⟩,rfl⟩ := (qubitsAppendEquiv 1 2).symm.surjective data
  have hflag : flag=(fun _ => false) ↔ oneBitEquiv flag=false := by
    constructor
    · rintro rfl;rfl
    · intro h
      apply oneBitEquiv.injective
      exact h
  have hz : (fun _ : Fin 3 => false)=Fin.append (fun _ : Fin 1 => false) (fun _ : Fin 2 => false) := by
    funext i
    refine Fin.addCases (m:=1) (n:=2) (fun j => ?_) (fun j => ?_) i <;> simp
  simp only [initWithReference,Equiv.apply_symm_apply,CoherentPaddedInputPreparation.initialData]
  rw [show (qubitsAppendEquiv 1 2).symm (flag,aux)=Fin.append flag aux from rfl]
  change (if aux=(fun _ => false) then proposalInitial K (flag,tape) else 0)=
    coinAmplitude K*basis (fun _ : Fin 3 => false) (Fin.append flag aux)
  rw [proposalInitial_value,hz]
  have he : Fin.append flag aux=Fin.append (fun _ : Fin 1 => false) (fun _ : Fin 2 => false) ↔
      oneBitEquiv flag=false ∧ aux=(fun _ => false) :=
    (CoherentXorCopy.append_eq_iff flag (fun _ => false) aux (fun _ => false)).trans (and_congr hflag Iff.rfl)
  simp only [basis,he]
  by_cases ha : aux=(fun _ => false) <;> cases hb : oneBitEquiv flag <;> simp [ha,hb]

theorem proposalInitial_norm (K : ℕ) :
    ‖(WithLp.toLp 2 (proposalInitial K) : EuclideanSpace ℂ (Bits 1×Bits K))‖=1 := by
  have hs : ‖(WithLp.toLp 2 (proposalInitial K) : EuclideanSpace ℂ (Bits 1×Bits K))‖^2=1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have he := Fintype.sum_equiv (Equiv.prodCongr oneBitEquiv (Equiv.refl (Bits K)))
      (fun x => ‖proposalInitial K x‖^2)
      (fun x : Bool×Bits K => ‖CoherentWeightedPreparation.initial x‖^2) (by intro x;rfl)
    rw [he]
    exact initial_normalized
  nlinarith [norm_nonneg (WithLp.toLp 2 (proposalInitial K) : EuclideanSpace ℂ (Bits 1×Bits K))]

/-- The physically prepared state is exactly the initialized input map to
which the full-vector native Gaussian acceptance error theorem applies. -/
theorem actual_hadamard_prepares
    (words : Str→List ℕ) (hw : Poly words) (p : Polynomial ℕ) (headerBits : Str) (K : ℕ) :
    runLayered (relocateCircuit (CoherentPaddedInputPreparation.ticketWires words hw p headerBits K) (coinCircuit K))
      (basis (CoherentPaddedInputPreparation.fullBasis words hw p headerBits K (fun _ => false)))=
      initializeAux (NativeWordCoherent.inputMap words hw p (headerBits.length+K) 3
        (fun tape : Bits K => headerBits++List.ofFn tape)
        (initWithReference (r:=2) (proposalInitial K))) := by
  rw [initialized_proposal]
  exact CoherentPaddedInputPreparation.actual_hadamard_prepares words hw p headerBits K

/-- The original binary B/control word is retained in this fixed-capacity
self-delimited prefix, and the actual native request builder reads it. -/
def builderHeader (slots : List Unit) (word : Str) : Str :=
  lengthToken slots++Builder.paddedPublic slots word

@[simp] theorem builderHeader_length (slots : List Unit) (word : Str) :
    (builderHeader slots word).length=2*slots.length+1 := by
  simp only [builderHeader,List.length_append,lengthToken,List.length_map,List.length_singleton,
    Builder.paddedPublic_length]
  omega

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Preparation

end

end P2MDyadicModule116

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingCapacity. -/
section P2MDyadicModule117

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

theorem capacityWeight_eq (input : PointRequest) (s : ℝ) (K : ℕ)
    (hK : Nat.size (intervalCount input)≤K) :
    capacityWeight input s K hK=(fun tape =>
      (fun x : Ticket input×Bits (K-Nat.size (intervalCount input)) => weight input s x.1.val)
        (capacityTicketEquiv input K hK tape)) := rfl

theorem capacity_success_probability (input : PointRequest) (s : ℝ) (K : ℕ)
    (hK : Nat.size (intervalCount input)≤K) :
    weightSum (capacityWeight input s K hK)/(Fintype.card (Bits K) : ℝ)=successProbability input s := by
  rw [capacityWeight_eq,weightSum_equiv (capacityTicketEquiv input K hK)
    (fun x : Ticket input×Bits (K-Nat.size (intervalCount input)) => weight input s x.1.val),
    Fintype.card_congr (capacityTicketEquiv input K hK),
    weightAverage_product (E:=Bits (K-Nat.size (intervalCount input)))
      (fun t : Ticket input => weight input s t.val)]
  simp only [successProbability,Fintype.card_fin]

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

end

end P2MDyadicModule117

/- Helper module Solutions.RegevBridgeCoherentWideGaussianActualTrial. -/
section P2MDyadicModule118

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent

open ControlledNativeGates CoherentRejection

open scoped BigOperators

def regroupTrial {W : ℕ} (ψ : QState (W+3+2)) : Bool → Bits W → TrialJunk → ℂ :=
  fun flag work junk => ψ ((trialCoordinates W).symm (flag,(work,junk)))

theorem regroupTrial_norm {W : ℕ} (ψ : QState (W+3+2)) :
    ‖singleVector (regroupTrial ψ)‖=stateNorm ψ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,singleVector,regroupTrial,stateNorm]
  exact Fintype.sum_equiv (trialCoordinates W).symm _ _ (by intro x;rfl)

theorem regroupTrial_sub {W : ℕ} (ψ φ : QState (W+3+2)) :
    singleVector (regroupTrial ψ)-singleVector (regroupTrial φ)=singleVector (regroupTrial (ψ-φ)) := rfl

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end

end P2MDyadicModule118

/- Helper module Solutions.RegevBridgeCoherentControlledSwap. -/
section P2MDyadicModule119

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity ControlledLetterPlan

def bitSwap {n : ℕ} (c i j : Fin n) (x : Bits n) : Bits n :=
  if x c then Function.update (Function.update x i (x j)) j (x i) else x

/-- The exact full-amplitude action, with every surrounding register kept. -/
theorem gates_semantics {n : ℕ} (c i j : Fin n) (hci : c≠i) (hcj : c≠j) (hij : i≠j)
    (ψ : QState n) : runLayer (gates c i j hci hcj hij) ψ=(fun x => ψ (bitSwap c i j x)) := by
  have hji : j≠i := hij.symm
  have hic : i≠c := hci.symm
  have hjc : j≠c := hcj.symm
  have he : runLayer (gates c i j hci hcj hij) ψ=
      (.cnot j i hij.symm : Instr n).apply
        (runLayer (toffoliGates c i j hci hcj hij) ((.cnot j i hij.symm : Instr n).apply ψ)) := by
    simp only [gates,runLayer,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [he,toffoliGates_semantics]
  funext x
  simp only [Instr.apply,cnotState]
  cases hc : x c <;> cases hi : x i <;> cases hj : x j <;>
    apply congrArg ψ <;> funext k <;>
    by_cases hki : k=i <;> by_cases hkj : k=j <;>
    simp_all [bitSwap]

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule119

/- Helper module Solutions.RegevBridgeCoherentFirstSuccessControls. -/
section P2MDyadicModule120

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentRejection

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[simp] theorem controls_length (flags : List Bool) : (controls flags).length=flags.length := by
  simp [controls]

theorem firstSuccess_index {m : ℕ} (flags : Fin m → Bool) (index : Fin m) :
    firstSuccess flags=some index ↔ (List.ofFn flags).findIdx id=index.val := by
  have he : (List.ofFn flags).findIdx id=(List.finRange m).findIdx flags := by
    rw [List.ofFn_eq_map,List.findIdx_map]
    rfl
  simp only [firstSuccess,List.find?_eq_getElem?_findIdx,←he]
  by_cases h : (List.ofFn flags).findIdx id < m
  · rw [List.getElem?_eq_getElem (by simpa only [List.length_finRange] using h)]
    simp only [List.getElem_finRange,Option.some.injEq,Fin.ext_iff,Fin.val_cast]
  · rw [List.getElem?_eq_none (by simpa only [List.length_finRange] using Nat.le_of_not_gt h)]
    constructor
    · intro hn
      cases hn
    · intro hi
      exact (h (hi.symm ▸ index.isLt)).elim

theorem controls_get {m : ℕ} (flags : Fin m → Bool) (index : Fin m) :
    (controls (List.ofFn flags))[index.val]'(by rw [controls_length,List.length_ofFn];exact index.isLt)=
      decide (firstSuccess flags=some index) := by
  simp only [controls,List.length_ofFn,List.getElem_map,List.getElem_range,firstSuccess_index]

end InfoLossLAR.WorstCase.CoherentRejection

end P2MDyadicModule120

/- Helper module Solutions.RegevBridgeCoherentFirstSuccessNative. -/
section P2MDyadicModule121

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity NativeWordLayout

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit Integration9_9.TM2OutputLength

def computedWork (m : ℕ) (word : Str) (hlen : word.length=m) : Bits (width P m) :=
  hlen ▸ result P word

theorem control_result (m : ℕ) (word : Str) (hlen : word.length=m) (i : Fin m) :
    computedWork m word hlen (controlWire i)=decide (some true=(CoherentRejection.controls word)[i.val]?) := by
  subst m
  change result P word (outputWire P word.length (controlIndex i) (some true))=_
  exact output_correct P word (controlIndex i) (some true)

/-- Actual physical wires of the native reversible computation hold the
exact first-success selector bits for every coherent input branch. -/
theorem control_flags {m : ℕ} (flags : Fin m → Bool) (i : Fin m) :
    computedWork m (List.ofFn flags) (List.length_ofFn) (controlWire i)=
      decide (CoherentRejection.firstSuccess flags=some i) := by
  rw [control_result]
  have hi : i.val < (CoherentRejection.controls (List.ofFn flags)).length := by
    simpa only [CoherentRejection.controls_length,List.length_ofFn] using i.isLt
  rw [List.getElem?_eq_getElem hi,CoherentRejection.controls_get]
  simp

attribute [local irreducible] baseCircuit

theorem basis_computes (m : ℕ) (word : Str) (hlen : word.length=m) :
    runLayeredLinearMap (baseCircuit m) (CoherentComputeUncompute.basis (initialWork m word))=
      CoherentComputeUncompute.basis (computedWork m word hlen) := by
  subst m
  have h := circuit_basis P word
  rw [basisInput_eq_computationalBasis,wordExtension_basis] at h
  rw [runLayeredLinearMap_apply]
  unfold baseCircuit
  change runLayered (circuit P word.length)
    (computationalBasis (fun i => wordExtension word i.val))=computationalBasis (result P word)
  exact h

theorem inverse_basis_computed (m : ℕ) (word : Str) (hlen : word.length=m) :
    runLayeredLinearMap (inverseCircuit (baseCircuit m))
      (CoherentComputeUncompute.basis (computedWork m word hlen))=
      CoherentComputeUncompute.basis (initialWork m word) :=
  CoherentComputeUncompute.inverse_basis _ _ _ (basis_computes m word hlen)

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule121

/- Helper module Solutions.RegevBridgeCoherentRegisterSwap. -/
section P2MDyadicModule122

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b n : ℕ}

def blockAction (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (slots : List (Fin b)) (x : Bits n) : Bits n :=
  slots.foldr (fun i y => bitSwap c (w (i,false)) (w (i,true)) y) x

theorem bitSwap_control (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (hc : ∀ p,c≠w p) (i : Fin b) (x : Bits n) :
    bitSwap c (w (i,false)) (w (i,true)) x c=x c := by
  cases hx : x c <;> simp [bitSwap,hx,hc]

theorem bitSwap_pair (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (i j : Fin b) (s : Bool) (x : Bits n) :
    bitSwap c (w (i,false)) (w (i,true)) x (w (j,s))=
      if j=i ∧ x c=true then x (w (j,!s)) else x (w (j,s)) := by
  by_cases h : j=i
  · subst j
    cases s <;> cases hx : x c <;>
      simp [bitSwap,hx,w.injective.eq_iff]
  · cases s <;> cases hx : x c <;>
      simp [bitSwap,hx,w.injective.eq_iff,h]

theorem blockAction_control (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (hc : ∀ p,c≠w p) (slots : List (Fin b)) (x : Bits n) :
    blockAction w c slots x c=x c := by
  induction slots with
  | nil => rfl
  | cons i slots ih =>
    change bitSwap c (w (i,false)) (w (i,true)) (blockAction w c slots x) c=_
    rw [bitSwap_control w c hc,ih]

/-- Each paired register bit is exchanged exactly once when control is true. -/
theorem blockAction_pair (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (hc : ∀ p,c≠w p) (slots : List (Fin b)) (hslots : slots.Nodup)
    (j : Fin b) (s : Bool) (x : Bits n) :
    blockAction w c slots x (w (j,s))=
      if j∈slots ∧ x c=true then x (w (j,!s)) else x (w (j,s)) := by
  induction slots generalizing j s with
  | nil => simp [blockAction]
  | cons i slots ih =>
    obtain ⟨hi,hrest⟩ := List.nodup_cons.mp hslots
    change bitSwap c (w (i,false)) (w (i,true)) (blockAction w c slots x) (w (j,s))=_
    rw [bitSwap_pair,blockAction_control w c hc]
    by_cases hji : j=i
    · subst j
      cases hx : x c <;> simp [hi,hx,ih hrest]
    · rw [if_neg (by tauto),ih hrest]
      simp [hji]

theorem blockAction_outside (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (slots : List (Fin b)) (x : Bits n) (k : Fin n) (hk : k∉Set.range w) :
    blockAction w c slots x k=x k := by
  have hn (p) : k≠w p := by intro h;exact hk ⟨p,h.symm⟩
  induction slots with
  | nil => rfl
  | cons i slots ih =>
    change bitSwap c (w (i,false)) (w (i,true)) (blockAction w c slots x) k=_
    cases hx : blockAction w c slots x c <;>
      simp [bitSwap,hx,hn,ih]

/-- The emitted full finite-gate word realizes the paired-wire permutation
on arbitrary amplitudes, not merely on basis probabilities. -/
theorem blockGates_semantics (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (hc : ∀ p,c≠w p) (slots : List (Fin b)) (ψ : QState n) :
    runLayer (blockGates w c hc slots) ψ=(fun x => ψ (blockAction w c slots x)) := by
  induction slots generalizing ψ with
  | nil => rfl
  | cons i slots ih =>
    have he : runLayer (blockGates w c hc (i::slots)) ψ=
        runLayer (blockGates w c hc slots) (runLayer (pairGates w c hc i) ψ) := by
      simp only [blockGates,List.flatMap_cons,runLayer,List.foldl_append]
    rw [he,ih]
    simp only [pairGates,gates_semantics]
    rfl

/-- The full public slot list exchanges both complete data registers. -/
theorem full_block_pair (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (hc : ∀ p,c≠w p) (j : Fin b) (s : Bool) (x : Bits n) :
    blockAction w c (List.finRange b) x (w (j,s))=
      if x c then x (w (j,!s)) else x (w (j,s)) := by
  simpa only [List.mem_finRange,true_and] using
    blockAction_pair w c hc (List.finRange b) (List.nodup_finRange b) j s x

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule122

/- Helper module Solutions.RegevBridgeCoherentSelectionCircuit. -/
section P2MDyadicModule123

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b m n : ℕ}

theorem blockAction_false (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (slots : List (Fin b)) (x : Bits n) (hx : x c=false) : blockAction w c slots x=x := by
  induction slots with
  | nil => rfl
  | cons i slots ih =>
    change bitSwap c (w (i,false)) (w (i,true)) (blockAction w c slots x)=x
    rw [ih]
    simp [bitSwap,hx]

def selectionAction (w : Fin m → (Fin b×Bool) ↪ Fin n) (c : Fin m → Fin n)
    (slots : List (Fin m)) (x : Bits n) : Bits n :=
  slots.foldr (fun i y => blockAction (w i) (c i) (List.finRange b) y) x

theorem selectionAction_controls (w : Fin m → (Fin b×Bool) ↪ Fin n) (c : Fin m → Fin n)
    (hc : ∀ i j p,c i≠w j p) (slots : List (Fin m)) (x : Bits n) (k : Fin m) :
    selectionAction w c slots x (c k)=x (c k) := by
  induction slots with
  | nil => rfl
  | cons i slots ih =>
    change blockAction (w i) (c i) (List.finRange b) (selectionAction w c slots x) (c k)=_
    rw [blockAction_outside _ _ _ _ _ (by rintro ⟨p,hp⟩;exact hc k i p hp.symm),ih]

theorem selectionAction_none (w : Fin m → (Fin b×Bool) ↪ Fin n) (c : Fin m → Fin n)
    (slots : List (Fin m)) (x : Bits n) (hx : ∀ i∈slots,x (c i)=false) :
    selectionAction w c slots x=x := by
  induction slots with
  | nil => rfl
  | cons i slots ih =>
    change blockAction (w i) (c i) (List.finRange b) (selectionAction w c slots x)=x
    rw [ih (by intro j hj;exact hx j (List.mem_cons_of_mem _ hj))]
    exact blockAction_false _ _ _ x (hx i (List.mem_cons_self))

/-- Exactly one computed first-success control selects exactly one entire
register, although every public copy is visited by the fixed circuit. -/
theorem selectionAction_one (w : Fin m → (Fin b×Bool) ↪ Fin n) (c : Fin m → Fin n)
    (hc : ∀ i j p,c i≠w j p) (slots : List (Fin m)) (hslots : slots.Nodup)
    (x : Bits n) (chosen : Fin m) (hx : ∀ i,x (c i)=decide (i=chosen)) :
    selectionAction w c slots x=
      if chosen∈slots then blockAction (w chosen) (c chosen) (List.finRange b) x else x := by
  induction slots with
  | nil => simp [selectionAction]
  | cons i slots ih =>
    obtain ⟨hi,hrest⟩ := List.nodup_cons.mp hslots
    change blockAction (w i) (c i) (List.finRange b) (selectionAction w c slots x)=_
    by_cases hij : i=chosen
    · subst i
      have hn : selectionAction w c slots x=x := selectionAction_none w c slots x (by
        intro j hj
        rw [hx]
        simp only [decide_eq_false_iff_not]
        intro hji
        exact hi (hji ▸ hj))
      rw [hn,if_pos List.mem_cons_self]
    · have hz : selectionAction w c slots x (c i)=false := by
        rw [selectionAction_controls w c hc,hx]
        simp [hij]
      rw [blockAction_false _ _ _ _ hz,ih hrest]
      simp [Ne.symm hij]

/-- The finite word has the exact full-amplitude permutation semantics. -/
theorem selectionGates_semantics (w : Fin m → (Fin b×Bool) ↪ Fin n) (c : Fin m → Fin n)
    (hc : ∀ i j p,c i≠w j p) (slots : List (Fin m)) (ψ : QState n) :
    runLayer (selectionGates w c hc slots) ψ=(fun x => ψ (selectionAction w c slots x)) := by
  induction slots generalizing ψ with
  | nil => rfl
  | cons i slots ih =>
    have he : runLayer (selectionGates w c hc (i::slots)) ψ=
        runLayer (selectionGates w c hc slots)
          (runLayer (blockGates (w i) (c i) (hc i i) (List.finRange b)) ψ) := by
      simp only [selectionGates,List.flatMap_cons,runLayer,List.foldl_append]
    rw [he,ih,blockGates_semantics]
    rfl

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule123

/- Helper module Solutions.RegevBridgeCoherentSelectionLayout. -/
section P2MDyadicModule124

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

/-- The exact output/copy row permutation on the entire bit array. -/
def swapRows (chosen : Fin m) (data : Bits ((m+1)*b)) : Bits ((m+1)*b) :=
  fun k =>
    let p := finProdFinEquiv.symm k
    if p.1=0 then data (rowWire chosen.succ p.2)
    else if p.1=chosen.succ then data (rowWire 0 p.2) else data k

theorem swapRows_zero (chosen : Fin m) (data : Bits ((m+1)*b)) (i : Fin b) :
    swapRows chosen data (rowWire 0 i)=data (rowWire chosen.succ i) := by
  simp [swapRows,rowWire]

theorem swapRows_chosen (chosen : Fin m) (data : Bits ((m+1)*b)) (i : Fin b) :
    swapRows chosen data (rowWire chosen.succ i)=data (rowWire 0 i) := by
  simp [swapRows,rowWire,Fin.succ_ne_zero]

theorem swapRows_other (chosen : Fin m) (data : Bits ((m+1)*b))
    (r : Fin (m+1)) (i : Fin b) (hr0 : r≠0) (hrj : r≠chosen.succ) :
    swapRows chosen data (rowWire r i)=data (rowWire r i) := by
  simp [swapRows,rowWire,hr0,hrj]

theorem row_outside (chosen : Fin m) (r : Fin (m+1)) (i : Fin b)
    (hr0 : r≠0) (hrj : r≠chosen.succ) :
    Fin.natAdd W (rowWire r i)∉Set.range (candidateFullPairs (W:=W) (b:=b) chosen) := by
  rintro ⟨⟨j,s⟩,h⟩
  change Fin.natAdd W (candidatePairs chosen (j,s))=Fin.natAdd W (rowWire r i) at h
  have hp : candidatePairs chosen (j,s)=rowWire r i :=
    Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  have he := congrArg Prod.fst (finProdFinEquiv.injective hp)
  cases s <;> simp at he
  · exact hr0 he.symm
  · exact hrj he.symm

/-- An active register block exchanges the exact designated/output rows and
retains every original machine work bit. -/
theorem candidate_block_append (chosen : Fin m) (control : Fin W)
    (work : Bits W) (data : Bits ((m+1)*b)) (hcontrol : work control=true) :
    blockAction (candidateFullPairs (W:=W) (b:=b) chosen)
      (control.castAdd ((m+1)*b)) (List.finRange b) (Fin.append work data)=
      Fin.append work (swapRows chosen data) := by
  have hc (p) : control.castAdd ((m+1)*b)≠candidateFullPairs (W:=W) (b:=b) chosen p :=
    fun h => work_outside control chosen ⟨p,h.symm⟩
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    rw [blockAction_outside _ _ _ _ _ (work_outside i chosen)]
    simp only [Fin.append_left]
  · intro i
    obtain ⟨⟨r,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    by_cases hr0 : r=0
    · subst r
      have h := full_block_pair (candidateFullPairs (W:=W) (b:=b) chosen)
        (control.castAdd ((m+1)*b)) hc j false (Fin.append work data)
      simpa [candidateFullPairs,appendPairs,candidatePairs,Fin.append_left,
        Fin.append_right,hcontrol,rowWire,swapRows] using h
    · by_cases hrj : r=chosen.succ
      · subst r
        have h := full_block_pair (candidateFullPairs (W:=W) (b:=b) chosen)
          (control.castAdd ((m+1)*b)) hc j true (Fin.append work data)
        simpa [candidateFullPairs,appendPairs,candidatePairs,Fin.append_left,
          Fin.append_right,hcontrol,rowWire,swapRows] using h
      · calc
          _ = data (rowWire r j) := by
            simpa only [Fin.append_right,rowWire] using
              blockAction_outside (candidateFullPairs (W:=W) (b:=b) chosen)
                (control.castAdd ((m+1)*b)) (List.finRange b) (Fin.append work data)
                (Fin.natAdd W (rowWire r j)) (row_outside (W:=W) chosen r j hr0 hrj)
          _ = _ := by
            simpa only [Fin.append_right,rowWire] using (swapRows_other chosen data r j hr0 hrj).symm

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule124

/- Helper module Solutions.RegevBridgeCoherentSelectionTensor. -/
section P2MDyadicModule125

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent

variable {b m W : ℕ}

/-- The retained first-success flags specify a whole-row swap, or identity
on the explicit all-failure branch. -/
def selectedRows (flags : Fin m → Bool) (data : Bits ((m+1)*b)) : Bits ((m+1)*b) :=
  match CoherentRejection.firstSuccess flags with
  | none => data
  | some j => swapRows j data

theorem selectionAction_work (controls : Fin m → Fin W) (slots : List (Fin m))
    (x : Bits (W+(m+1)*b)) (k : Fin W) :
    selectionAction (candidateFullPairs (W:=W) (b:=b))
      (fun i => (controls i).castAdd ((m+1)*b)) slots x (k.castAdd ((m+1)*b))=
        x (k.castAdd ((m+1)*b)) := by
  induction slots with
  | nil => rfl
  | cons i slots ih =>
    change blockAction (candidateFullPairs (W:=W) (b:=b) i)
      ((controls i).castAdd ((m+1)*b)) (List.finRange b)
      (selectionAction (candidateFullPairs (W:=W) (b:=b))
        (fun i => (controls i).castAdd ((m+1)*b)) slots x) (k.castAdd ((m+1)*b))=_
    rw [blockAction_outside _ _ _ _ _ (work_outside k i),ih]

theorem selection_append (controls : Fin m → Fin W) (work : Bits W)
    (data : Bits ((m+1)*b)) (flags : Fin m → Bool)
    (hcontrols : ∀ i,work (controls i)=decide (CoherentRejection.firstSuccess flags=some i)) :
    selectionAction (candidateFullPairs (W:=W) (b:=b))
      (fun i => (controls i).castAdd ((m+1)*b)) (List.finRange m) (Fin.append work data)=
      Fin.append work (selectedRows flags data) := by
  cases hf : CoherentRejection.firstSuccess flags with
  | none =>
    have hh : ∀ i∈List.finRange m,Fin.append work data
        ((controls i).castAdd ((m+1)*b))=false := by
      intro i _
      simp only [Fin.append_left,hcontrols,hf,reduceCtorEq,decide_false]
    rw [selectionAction_none _ _ _ _ hh]
    simp only [selectedRows,hf]
  | some chosen =>
    have hh : ∀ i,Fin.append work data ((controls i).castAdd ((m+1)*b))=decide (i=chosen) := by
      intro i
      simp only [Fin.append_left,hcontrols,hf,Option.some.injEq,eq_comm]
    rw [selectionAction_one _ _ (controls_fresh controls) (List.finRange m)
      (List.nodup_finRange m) (Fin.append work data) chosen hh,
      if_pos (List.mem_finRange chosen),candidate_block_append]
    · simp only [selectedRows,hf]
    · simp only [hcontrols,hf,decide_true]

/-- The middle selection circuit acts on the data while retaining its entire
computed work basis, hence can safely precede the actual inverse computation. -/
theorem selection_tensor (controls : Fin m → Fin W) (work : Bits W)
    (flags : Fin m → Bool) (v : QState ((m+1)*b))
    (hcontrols : ∀ i,work (controls i)=decide (CoherentRejection.firstSuccess flags=some i)) :
    runLayer (selectionGates (candidateFullPairs (W:=W) (b:=b))
      (fun i => (controls i).castAdd ((m+1)*b)) (controls_fresh controls) (List.finRange m))
      (assembleMap W ((m+1)*b) (CoherentComputeUncompute.tensor v work))=
    assembleMap W ((m+1)*b)
      (CoherentComputeUncompute.tensor (fun data => v (selectedRows flags data)) work) := by
  rw [selectionGates_semantics]
  funext x
  let xwork : Bits W := fun i => x (i.castAdd ((m+1)*b))
  let xdata : Bits ((m+1)*b) := fun i => x (Fin.natAdd W i)
  have hx : x=Fin.append xwork xdata := ((qubitsAppendEquiv W ((m+1)*b)).symm_apply_apply x).symm
  rw [hx]
  by_cases hw : xwork=work
  · rw [hw,selection_append controls work xdata flags hcontrols]
    simp [assembleMap,CoherentComputeUncompute.tensor,CoherentComputeUncompute.basis]
  · have hp : (fun i => selectionAction (candidateFullPairs (W:=W) (b:=b))
        (fun i => (controls i).castAdd ((m+1)*b)) (List.finRange m)
        (Fin.append xwork xdata) (i.castAdd ((m+1)*b)))=xwork := by
      funext i
      rw [selectionAction_work,Fin.append_left]
    change v (fun i => selectionAction (candidateFullPairs (W:=W) (b:=b))
      (fun i => (controls i).castAdd ((m+1)*b)) (List.finRange m)
      (Fin.append xwork xdata) (Fin.natAdd W i))*CoherentComputeUncompute.basis work _=
        v (selectedRows flags (fun i => Fin.append xwork xdata (Fin.natAdd W i)))*
          CoherentComputeUncompute.basis work (fun i => Fin.append xwork xdata (i.castAdd ((m+1)*b)))
    rw [hp]
    simp [CoherentComputeUncompute.basis,hw]

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule125

/- Helper module Solutions.RegevBridgeCoherentFirstSuccessCircuit. -/
section P2MDyadicModule126

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity NativeWordCoherent CoherentControlledSwap NativeWordLayout

open scoped BigOperators

attribute [local irreducible] CoherentRejection.controlsProgram baseCircuit

def inputState {m : ℕ} (b : ℕ) (flags : Fin m → Bool) (v : QState ((m+1)*b)) :
    QState (width P m+(m+1)*b) :=
  assembleMap _ _ (CoherentComputeUncompute.tensor v (initialWork m (List.ofFn flags)))

def cleanState {m : ℕ} (b : ℕ) (flags : Fin m → Bool) (v : QState ((m+1)*b)) :
    QState (width P m+(m+1)*b) :=
  assembleMap _ _ (CoherentComputeUncompute.tensor (fun data => v (selectedRows flags data))
    (initialWork m (List.ofFn flags)))

/-- Forward computation, exact physical register selection, and inverse
computation are one literal circuit; the original flags and all phases remain. -/
theorem wholeCircuit_exact {m : ℕ} (b : ℕ) (flags : Fin m → Bool) (v : QState ((m+1)*b)) :
    runLayered (wholeCircuit b m) (inputState b flags v)=cleanState b flags v := by
  have hf : runLayered (extendCircuit ((m+1)*b) (baseCircuit m)) (inputState b flags v)=
      assembleMap _ _ (CoherentComputeUncompute.tensor v
        (computedWork m (List.ofFn flags) List.length_ofFn)) := by
    rw [extendCircuit_semantics]
    simp only [workAction,inputState,LinearMap.comp_apply,separate_assemble]
    rw [CoherentComputeUncompute.onWork_tensor _ _ _ _
      (basis_computes m (List.ofFn flags) List.length_ofFn)]
  have hm : runLayered ((middle b m).map (fun g => [g]))
      (assembleMap _ _ (CoherentComputeUncompute.tensor v
        (computedWork m (List.ofFn flags) List.length_ofFn)))=
      assembleMap _ _ (CoherentComputeUncompute.tensor (fun data => v (selectedRows flags data))
        (computedWork m (List.ofFn flags) List.length_ofFn)) := by
    rw [ControlledLetterPlan.runLayered_singletons]
    exact selection_tensor controlWire _ flags v (control_flags flags)
  have hb : runLayered (extendCircuit ((m+1)*b) (inverseCircuit (baseCircuit m)))
      (assembleMap _ _ (CoherentComputeUncompute.tensor (fun data => v (selectedRows flags data))
        (computedWork m (List.ofFn flags) List.length_ofFn)))=cleanState b flags v := by
    rw [extendCircuit_semantics]
    simp only [workAction,cleanState,LinearMap.comp_apply,separate_assemble]
    rw [CoherentComputeUncompute.onWork_tensor _ _ _ _
      (inverse_basis_computed m (List.ofFn flags) List.length_ofFn)]
  have he : runLayered (wholeCircuit b m) (inputState b flags v)=
      runLayered (extendCircuit ((m+1)*b) (inverseCircuit (baseCircuit m)))
        (runLayered ((middle b m).map (fun g => [g]))
          (runLayered (extendCircuit ((m+1)*b) (baseCircuit m)) (inputState b flags v))) := by
    simp only [wholeCircuit,runLayered,List.foldl_append]
  rw [he,hf,hm,hb]

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule126

/- Helper module Solutions.RegevBridgeCoherentRejectionLayout. -/
section P2MDyadicModule127

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b m : ℕ}

@[simp] theorem assembleRows_zero (out : Bits b) (copies : Fin m → Bits b) :
    dataRow (assembleRows out copies) 0=out := by
  funext j
  simp [dataRow,assembleRows,rowWire]

@[simp] theorem assembleRows_succ (out : Bits b) (copies : Fin m → Bits b) (i : Fin m) :
    dataRow (assembleRows out copies) i.succ=copies i := by
  funext j
  simp [dataRow,assembleRows,rowWire]

theorem assembleRows_split (data : Bits ((m+1)*b)) :
    assembleRows (dataRow data 0) (fun i => dataRow data i.succ)=data := by
  funext k
  obtain ⟨⟨r,j⟩,rfl⟩ := finProdFinEquiv.surjective k
  refine Fin.cases ?_ (fun i => ?_) r
  · exact congrFun (assembleRows_zero (dataRow data 0) (fun i => dataRow data i.succ)) j
  · exact congrFun (assembleRows_succ (dataRow data 0) (fun i => dataRow data i.succ) i) j

/-- This coordinate identification retains every copy's local junk. -/
def rowsWithJunkEquiv (J : Type*) :
    (Bits ((m+1)*b)×(Fin m → J)) ≃ Bits b×(Fin m → Bits b×J) where
  toFun p := (dataRow p.1 0,fun i => (dataRow p.1 i.succ,p.2 i))
  invFun p := (assembleRows p.1 (fun i => (p.2 i).1),fun i => (p.2 i).2)
  left_inv p := by simp only [assembleRows_split,Prod.eta]
  right_inv p := by simp only [assembleRows_zero,assembleRows_succ,Prod.eta]

theorem dataRow_swap_zero (chosen : Fin m) (data : Bits ((m+1)*b)) :
    dataRow (swapRows chosen data) 0=dataRow data chosen.succ := by
  funext j
  exact swapRows_zero chosen data j

theorem dataRow_swap_chosen (chosen : Fin m) (data : Bits ((m+1)*b)) :
    dataRow (swapRows chosen data) chosen.succ=dataRow data 0 := by
  funext j
  exact swapRows_chosen chosen data j

theorem dataRow_swap_other (chosen i : Fin m) (data : Bits ((m+1)*b)) (hi : i≠chosen) :
    dataRow (swapRows chosen data) i.succ=dataRow data i.succ := by
  funext j
  exact swapRows_other chosen data i.succ j (Fin.succ_ne_zero i)
    (fun he => hi (Fin.succ_injective _ he))

/-- The concrete row exchange realizes exactly the abstract reversible
output/copy swap, with all local auxiliary values untouched. -/
theorem rowsWithJunk_swap {J : Type*} (chosen : Fin m) (data : Bits ((m+1)*b)) (junk : Fin m → J) :
    rowsWithJunkEquiv J (swapRows chosen data,junk)=
      CoherentRejection.swapOutput chosen (rowsWithJunkEquiv J (data,junk)) := by
  apply Prod.ext
  · exact dataRow_swap_zero chosen data
  · funext i
    by_cases hi : i=chosen
    · subst i
      simp only [rowsWithJunkEquiv,Equiv.coe_fn_mk,CoherentRejection.swapOutput,
        Function.update_self,dataRow_swap_chosen]
    · simp only [rowsWithJunkEquiv,Equiv.coe_fn_mk,CoherentRejection.swapOutput,
        Function.update_of_ne hi,dataRow_swap_other chosen i data hi]

theorem rowsWithJunk_selected {J : Type*} (flags : Fin m → Bool)
    (data : Bits ((m+1)*b)) (junk : Fin m → J) :
    rowsWithJunkEquiv J (selectedRows flags data,junk)=
      CoherentRejection.selectedSwap flags (rowsWithJunkEquiv J (data,junk)) := by
  cases h : CoherentRejection.firstSuccess flags with
  | none => simp [selectedRows,CoherentRejection.selectedSwap,h]
  | some i => simpa only [selectedRows,CoherentRejection.selectedSwap,h,
      CoherentRejection.swapEquiv_apply] using rowsWithJunk_swap i data junk

end InfoLossLAR.WorstCase.CoherentControlledSwap

end P2MDyadicModule127

/- Helper module Solutions.RegevBridgeCoherentRejectionPhysical. -/
section P2MDyadicModule128

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute CoherentControlledSwap

open NativeWordLayout

open scoped BigOperators

theorem initial_flags {m : ℕ} (flags : Bits m) (i : Fin m) :
    initialWork m (List.ofFn flags) ⟨i.val,by unfold width;omega⟩=flags i := by
  have hi : i.val < (List.ofFn flags).length := by simp
  simp only [initialWork,TM2Boolean.wordExtension_before _ _ hi,List.getElem_ofFn]

theorem swapRows_involutive {b m : ℕ} (chosen : Fin m) :
    Function.Involutive (swapRows (b:=b) chosen) := by
  intro data
  funext k
  obtain ⟨⟨r,i⟩,rfl⟩ := finProdFinEquiv.surjective k
  change swapRows chosen (swapRows chosen data) (rowWire r i)=data (rowWire r i)
  by_cases h0 : r=0
  · subst r;rw [swapRows_zero,swapRows_chosen]
  · by_cases hj : r=chosen.succ
    · subst r;rw [swapRows_chosen,swapRows_zero]
    · rw [swapRows_other chosen _ r i h0 hj,swapRows_other chosen _ r i h0 hj]

theorem selectedRows_involutive {b m : ℕ} (flags : Bits m) :
    Function.Involutive (selectedRows (b:=b) flags) := by
  intro data
  cases hf : CoherentRejection.firstSuccess flags with
  | none => simp [selectedRows,hf]
  | some i => simpa only [selectedRows,hf] using swapRows_involutive (b:=b) i data

def selectionEquiv (b m k : ℕ) : Equiv.Perm (Coordinates b m k) where
  toFun x := (selectedRows x.2.1 x.1,x.2)
  invFun x := (selectedRows x.2.1 x.1,x.2)
  left_inv x := by exact Prod.ext (selectedRows_involutive x.2.1 x.1) rfl
  right_inv x := by exact Prod.ext (selectedRows_involutive x.2.1 x.1) rfl

theorem basis_append {n m : ℕ} (x : Bits n) (y : Bits m) :
    basis (Fin.append x y)=tensorState (basis x) (basis y) := computationalBasis_tensor x y

theorem inputState_basis {m : ℕ} (b : ℕ) (flags : Bits m) (data : Bits ((m+1)*b)) :
    inputState b flags (basis data)=basis (Fin.append (initialWork m (List.ofFn flags)) data) := by
  rw [basis_append]
  funext x
  change basis data (rightRegister x)*basis (initialWork m (List.ofFn flags)) (leftRegister x)=_
  exact mul_comm _ _

theorem basis_selected {m : ℕ} (b : ℕ) (flags : Bits m) (data : Bits ((m+1)*b)) :
    (fun d => basis data (selectedRows flags d))=basis (selectedRows flags data) := by
  funext d
  have he : selectedRows flags d=data ↔ d=selectedRows flags data := by
    constructor
    · intro h;rw [←h,selectedRows_involutive]
    · intro h;rw [h,selectedRows_involutive]
  simp only [basis,he]

/-- The complete first-success machine computes, swaps the actual output
row, and uncomputes. Every outside junk wire is retained exactly. -/
theorem fullCircuit_basis (b m k : ℕ) (x : Coordinates b m k) :
    runLayered (fullCircuit b m k) (basis (physicalEmbedding b m k x))=
      basis (physicalEmbedding b m k (selectionEquiv b m k x)) := by
  change runLayered (leftCircuit (wholeCircuit b m))
    (basis (Fin.append (Fin.append (initialWork m (List.ofFn x.2.1)) x.1) x.2.2))=_
  rw [basis_append,←inputState_basis,leftCircuit_tensor,wholeCircuit_exact]
  have hc : cleanState b x.2.1 (basis x.1)=
      inputState b x.2.1 (basis (selectedRows x.2.1 x.1)) := by
    unfold cleanState inputState
    rw [basis_selected]
  rw [hc,inputState_basis,←basis_append]
  rfl

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule128

/- Helper module Solutions.RegevBridgeCoherentRejectionPhysicalState. -/
section P2MDyadicModule129

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity CoherentComputeUncompute CoherentControlledSwap CoherentRejection CoherentProjection

open NativeWordLayout

open scoped BigOperators

theorem abstractCoordinates_selection (b m k : ℕ) (x : Coordinates b m (m*k)) :
    abstractCoordinates b m k (selectionEquiv b m (m*k) x)=
      completeSwap (abstractCoordinates b m k x) := by
  have hh:=rowsWithJunk_selected x.2.1 x.1 (junkRows x.2.2)
  exact congrArg (fun p : Bits b×(Fin m → Bits b×Bits k) => (p.1,(x.2.1,p.2))) hh

theorem abstractEmbedding_selection (b m k : ℕ) (x : AbstractCoordinates b m k) :
    physicalEmbedding b m (m*k) (selectionEquiv b m (m*k) ((abstractCoordinates b m k).symm x))=
      abstractEmbedding b m k (completeSwap x) := by
  have hh:=abstractCoordinates_selection b m k ((abstractCoordinates b m k).symm x)
  rw [Equiv.apply_symm_apply] at hh
  apply (fun h => congrArg (fun y => physicalEmbedding b m (m*k) ((abstractCoordinates b m k).symm y)) h) at hh
  simpa only [Equiv.symm_apply_apply,abstractEmbedding,Function.Embedding.trans_apply,Equiv.toEmbedding_apply] using hh

theorem completeSwap_symm {O J : Type*} {m : ℕ} (x : O×Retained O J m) :
    (completeSwap (O:=O) (J:=J) (m:=m)).symm x=completeSwap x := by
  cases hf : firstSuccess x.2.1 <;> simp [completeSwap,selectedSwap,hf,swapEquiv]

/-- A fully specified native circuit realizes the abstract first-success
amplitudes after an injective physical storage map, with zero selection work. -/
theorem fullCircuit_abstract (b m k : ℕ) (ψ : AbstractCoordinates b m k → ℂ) :
    runLayered (fullCircuit b m (m*k)) (basisEmbedding (abstractEmbedding b m k) ψ)=
      basisEmbedding (abstractEmbedding b m k) (fun x => ψ (completeSwap x)) := by
  rw [←runLayeredLinearMap_apply]
  have hh := basisEmbedding_permutation (abstractEmbedding b m k) completeSwap
    (runLayeredLinearMap (fullCircuit b m (m*k))) (fun x => by
      rw [runLayeredLinearMap_apply]
      change runLayered (fullCircuit b m (m*k))
        (basis (physicalEmbedding b m (m*k) ((abstractCoordinates b m k).symm x)))=_
      rw [fullCircuit_basis,abstractEmbedding_selection]) ψ
  simpa only [completeSwap_symm] using hh

theorem fullCircuit_completeState (b m k : ℕ) (zero : Bits b) (single : Bool → Bits b → Bits k → ℂ) :
    runLayered (fullCircuit b m (m*k))
      (basisEmbedding (abstractEmbedding b m k)
        (initialCopies zero (repeatState m (singleVector single))))=
      basisEmbedding (abstractEmbedding b m k) (completeState zero single) := by
  rw [fullCircuit_abstract]
  rfl

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule129

/- Helper module Solutions.RegevBridgeCoherentParallelTrials. -/
section P2MDyadicModule130

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentParallelTrials

open QAlgorithms QAlgorithms.Complexity

open scoped BigOperators

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

@[simp] theorem coordinates_zero (n m : ℕ) (x : Bits (width n (m+1))) :
    coordinates n (m+1) x 0=leftRegister x := rfl

@[simp] theorem coordinates_succ (n m : ℕ) (x : Bits (width n (m+1))) (i : Fin m) :
    coordinates n (m+1) x i.succ=coordinates n m (rightRegister x) i := rfl

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

/-- Coordinate regrouping of the actual tensor circuit is an isometry. -/
theorem circuit_regroup {n : ℕ} (trial : Layered n) (ψ : QState n) (m : ℕ) :
    (fun x : Fin m → Bits n => runLayered (circuit trial m) (initial ψ m) ((coordinates n m).symm x))=
      CoherentProjection.repeatState m (WithLp.toLp 2 (runLayered trial ψ)) := by
  funext x
  simp only [circuit_product,Equiv.apply_symm_apply,CoherentProjection.repeatState]

end InfoLossLAR.WorstCase.CoherentParallelTrials

end P2MDyadicModule130

/- Helper module Solutions.RegevBridgeCoherentTrialPlacement. -/
section P2MDyadicModule131

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

end P2MDyadicModule131

/- Helper module Solutions.RegevBridgeCoherentTrialEncoding. -/
section P2MDyadicModule132

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms QAlgorithms.Complexity CoherentControlledSwap NativeWordLayout

/-- Every physical bit of every coherent trial reaches its designated
output, actual input flag, or spectator auxiliary wire without duplication. -/
theorem copyEncoding_placed (b m k : ℕ) (copies : Fin m → Bits (b+1+k))
    (i : Fin m) (j : Fin (b+1+k)) :
    copyEncoding b m k copies (trialPlacement b m k (i,j))=copies i j := by
  refine Fin.addCases ?_ ?_ j
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro l
      rw [trialPlacement_output]
      simp only [copyEncoding,encoded,Fin.append_left,Fin.append_right]
      change assembleRows (fun _ => false) (fun i => (splitTrial b k (copies i)).2.1) (rowWire i.succ l)=_
      exact congrFun (assembleRows_succ (fun _ => false) (fun i => (splitTrial b k (copies i)).2.1) i) l
    · intro l
      have he : l=(0 : Fin 1) := Subsingleton.elim _ _
      subst l
      rw [trialPlacement_flag]
      simp only [copyEncoding,encoded,Fin.append_left,Fin.append_right]
      change initialWork m (List.ofFn (fun i => (splitTrial b k (copies i)).1)) (flagPosition i)=_
      unfold flagPosition
      rw [initial_flags]
      rfl
  · intro l
    rw [trialPlacement_junk]
    simp only [copyEncoding,encoded,Fin.append_left,Fin.append_right]
    change packJunk (fun i => (splitTrial b k (copies i)).2.2) (finProdFinEquiv (i,l))=_
    simp only [packJunk,Equiv.symm_apply_apply]
    rfl

theorem copyEncoding_injective (b m k : ℕ) : Function.Injective (copyEncoding b m k) := by
  intro x y h
  funext i j
  have hh:=congrFun h (trialPlacement b m k (i,j))
  simpa only [copyEncoding_placed] using hh

/-- All selected-machine work and the distinguished output row start at
zero. No unsupported extra input is hidden in the complement of the trials. -/
theorem copyEncoding_outside (b m k : ℕ) (copies : Fin m → Bits (b+1+k))
    (j : Fin (width P m+(m+1)*b+m*k))
    (hout : j∉Set.range (trialPlacement b m k)) : copyEncoding b m k copies j=false := by
  revert hout
  refine Fin.addCases ?_ ?_ j
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j hout
      by_cases hj : j.val < m
      · exfalso
        apply hout
        refine ⟨(⟨j.val,hj⟩,(Fin.natAdd b (0 : Fin 1)).castAdd k),?_⟩
        rw [trialPlacement_flag]
        rfl
      · simp only [copyEncoding,encoded,Fin.append_left,Fin.append_right]
        change TM2Boolean.wordExtension (List.ofFn (fun i => (splitTrial b k (copies i)).1)) j.val=false
        apply TM2Boolean.wordExtension_after
        simpa only [List.length_ofFn] using Nat.le_of_not_gt hj
    · intro j
      obtain ⟨⟨r,l⟩,rfl⟩:=finProdFinEquiv.surjective j
      refine Fin.cases ?_ (fun i => ?_) r
      · intro hout
        simp only [copyEncoding,encoded,Fin.append_left,Fin.append_right]
        change assembleRows (fun _ => false) (fun i => (splitTrial b k (copies i)).2.1) (rowWire 0 l)=false
        exact congrFun (assembleRows_zero (fun _ => false) (fun i => (splitTrial b k (copies i)).2.1)) l
      · intro hout
        exfalso
        apply hout
        exact ⟨(i,(l.castAdd 1).castAdd k),trialPlacement_output b m k i l⟩
  · intro j
    obtain ⟨⟨i,l⟩,rfl⟩:=finProdFinEquiv.surjective j
    intro hout
    exfalso
    apply hout
    exact ⟨(i,Fin.natAdd (b+1) l),trialPlacement_junk b m k i l⟩

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule132

/- Helper module Solutions.RegevBridgeParallelTrialWires. -/
section P2MDyadicModule133

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentParallelTrials

open QAlgorithms.Complexity

theorem flatWire_zero (n m : ℕ) (j : Fin n) :
    flatWire n (m+1) (0,j)=j.castAdd (width n m) := by
  apply Fin.ext
  simp [flatWire,finProdFinEquiv]

theorem flatWire_succ (n m : ℕ) (i : Fin m) (j : Fin n) :
    flatWire n (m+1) (i.succ,j)=Fin.natAdd n (flatWire n m (i,j)) := by
  apply Fin.ext
  simp [flatWire,finProdFinEquiv,Nat.mul_add,Nat.add_comm,Nat.add_left_comm]

/-- The amplitude regrouping of the real parallel circuit is exactly this
public wire indexing, not an arbitrary permutation of basis states. -/
theorem coordinates_flatWire (n m : ℕ) (x : Bits (width n m)) (i : Fin m) (j : Fin n) :
    coordinates n m x i j=x (flatWire n m (i,j)) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [coordinates_zero,flatWire_zero]
      rfl
    · rw [coordinates_succ,ih,flatWire_succ]
      rfl

end InfoLossLAR.WorstCase.CoherentParallelTrials

end P2MDyadicModule133

/- Helper module Solutions.RegevBridgeCoherentParallelPlacement. -/
section P2MDyadicModule134

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

def copyEmbedding (b m k : ℕ) :
    (Fin m → Bits (b+1+k)) ↪ Bits (width P m+(m+1)*b+m*k) :=
  ⟨copyEncoding b m k,copyEncoding_injective b m k⟩

/-- The actual complete physical copy encoding is exactly the selected
trial wires with all complementary wires at zero. -/
theorem copyEncoding_split (b m k : ℕ) (x : Bits (CoherentParallelTrials.width (b+1+k) m)) :
    wireBitsEquiv (allTrialWires b m k)
      (copyEncoding b m k (CoherentParallelTrials.coordinates (b+1+k) m x))=(x,fun _ => false) := by
  apply Prod.ext
  · funext j
    obtain ⟨⟨i,j⟩,rfl⟩ := (CoherentParallelTrials.flatWire (b+1+k) m).surjective j
    change copyEncoding b m k _ (allTrialWires b m k _)=_
    rw [allTrialWires_at,copyEncoding_placed,CoherentParallelTrials.coordinates_flatWire]
  · funext j
    apply copyEncoding_outside
    rintro ⟨⟨i,l⟩,he⟩
    apply j.property
    exact ⟨CoherentParallelTrials.flatWire (b+1+k) m (i,l),(allTrialWires_at b m k i l).trans he⟩

theorem initializedWireEmbedding_copy (b m k : ℕ)
    (x : Bits (CoherentParallelTrials.width (b+1+k) m)) :
    initializedWireEmbedding (allTrialWires b m k) (fun _ => false) x=
      copyEmbedding b m k (CoherentParallelTrials.coordinates (b+1+k) m x) := by
  apply (wireBitsEquiv (allTrialWires b m k)).injective
  change wireBitsEquiv (allTrialWires b m k) ((wireBitsEquiv (allTrialWires b m k)).symm (x,fun _ => false))=wireBitsEquiv (allTrialWires b m k) (copyEncoding b m k (CoherentParallelTrials.coordinates (b+1+k) m x))
  rw [copyEncoding_split]
  exact (wireBitsEquiv (allTrialWires b m k)).apply_symm_apply (x,fun _ => false)

theorem initializedWires_copies (b m k : ℕ) (ψ : QState (CoherentParallelTrials.width (b+1+k) m)) :
    initializedWires (allTrialWires b m k) (fun _ => false) ψ=
      basisEmbedding (copyEmbedding b m k)
        (fun copies => ψ ((CoherentParallelTrials.coordinates (b+1+k) m).symm copies)) := by
  rw [initializedWires_eq_embedding]
  simp only [basisEmbedding,LinearMap.coe_mk,AddHom.coe_mk,initializedWireEmbedding_copy]
  exact Fintype.sum_equiv (CoherentParallelTrials.coordinates (b+1+k) m) _ _
    (by intro x;simp only [Equiv.symm_apply_apply])

def parallelInitial (b m k : ℕ) (ψ : QState (b+1+k)) :
    QState (width P m+(m+1)*b+m*k) :=
  initializedWires (allTrialWires b m k) (fun _ => false) (CoherentParallelTrials.initial ψ m)

/-- The real relocated parallel circuit produces all trial amplitudes in
exactly the same physical encoding consumed by the first-success machine.
The equality includes every flag, original work bit and auxiliary bit. -/
theorem parallelPreparation_copies (b m k : ℕ) (trial : Layered (b+1+k)) (ψ : QState (b+1+k)) :
    runLayered (parallelPreparation b m k trial) (parallelInitial b m k ψ)=
      basisEmbedding (copyEmbedding b m k) (repeatState m (WithLp.toLp 2 (runLayered trial ψ))) := by
  rw [parallelPreparation,parallelInitial,relocateCircuit_initialized,initializedWires_copies]
  congr 1
  exact CoherentParallelTrials.circuit_regroup trial ψ m

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule134

/- Helper module Solutions.RegevBridgeCoherentRejectionPipeline. -/
section P2MDyadicModule135

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity CoherentComputeUncompute CoherentProjection CoherentRejection

open NativeWordLayout

open scoped BigOperators

def trialCopies (b m k : ℕ) : (Fin m → Bits (b+1+k)) ≃ (Fin m → Bool×(Bits b×Bits k)) where
  toFun x i := splitTrial b k (x i)
  invFun x i := (splitTrial b k).symm (x i)
  left_inv x := by funext i;exact (splitTrial b k).symm_apply_apply (x i)
  right_inv x := by funext i;exact (splitTrial b k).apply_symm_apply (x i)

def retainedCopies (b m k : ℕ) : (Fin m → Bits (b+1+k)) ≃ Retained (Bits b) (Bits k) m :=
  (trialCopies b m k).trans splitCopies

theorem copyEncoding_abstract (b m k : ℕ) (x : Fin m → Bits (b+1+k)) :
    copyEmbedding b m k x=abstractEmbedding b m k ((fun _ => false),retainedCopies b m k x) := rfl

theorem abstractInitial_expansion (b m k : ℕ)
    (ψ : EuclideanSpace ℂ (Fin m → Bool×(Bits b×Bits k))) :
    basisEmbedding (abstractEmbedding b m k) (initialCopies (fun _ => false) ψ)=
      ∑ r : Retained (Bits b) (Bits k) m,
        ψ (splitCopies.symm r) • basis (abstractEmbedding b m k ((fun _ => false),r)) := by
  change (∑ x : AbstractCoordinates b m k,
    initialCopies (fun _ => false) ψ x • basis (abstractEmbedding b m k x))=_
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (fun _ : Fin b => false)]
  · simp [initialCopies]
  · intro o _ ho
    simp only [initialCopies,if_neg ho,zero_smul,Finset.sum_const_zero]
  · simp

/-- The actual output of repeated physical trial circuits equals the full
abstract product state in the physical selection encoding, including every
flag and auxiliary amplitude. -/
theorem copyEmbedding_initial (b m k : ℕ) (ψ : QState (b+1+k)) :
    basisEmbedding (copyEmbedding b m k) (repeatState m (WithLp.toLp 2 ψ))=
      basisEmbedding (abstractEmbedding b m k)
        (initialCopies (fun _ => false) (repeatState m
          (WithLp.toLp 2 (fun x => ψ ((splitTrial b k).symm x))))) := by
  rw [abstractInitial_expansion]
  change (∑ x : Fin m → Bits (b+1+k),
    repeatState m (WithLp.toLp 2 ψ) x • basis (copyEmbedding b m k x))=_
  apply Fintype.sum_equiv (retainedCopies b m k)
  intro x
  rw [copyEncoding_abstract]
  apply congrArg (fun z : ℂ => z • basis (abstractEmbedding b m k ((fun _ => false),retainedCopies b m k x)))
  simp only [repeatState,retainedCopies,Equiv.trans_apply,Equiv.symm_apply_apply,trialCopies,
    Equiv.coe_fn_mk,Equiv.symm_apply_apply]

def physicalSingle (b k : ℕ) (trial : Layered (b+1+k)) (ψ : QState (b+1+k)) :
    Bool → Bits b → Bits k → ℂ :=
  fun flag out junk => runLayered trial ψ ((splitTrial b k).symm (flag,(out,junk)))

/-- The composed real circuit realizes exactly the complete coherent
rejection state. No conditional success branch or discarded register is
substituted for its actual whole output. -/
theorem pipelineCircuit_complete (b m k : ℕ) (trial : Layered (b+1+k)) (ψ : QState (b+1+k)) :
    runLayered (pipelineCircuit b m k trial) (parallelInitial b m k ψ)=
      basisEmbedding (abstractEmbedding b m k)
        (completeState (fun _ => false) (physicalSingle b k trial ψ)) := by
  unfold pipelineCircuit
  rw [runLayered,List.foldl_append]
  change runLayered (fullCircuit b m (m*k))
    (runLayered (parallelPreparation b m k trial) (parallelInitial b m k ψ))=_
  rw [parallelPreparation_copies,copyEmbedding_initial]
  exact fullCircuit_completeState b m k (fun _ => false) (physicalSingle b k trial ψ)

/-- A proved full-state pure-output estimate is inherited by the literal
entire circuit with exactly the same error. -/
theorem pipelineCircuit_pure_error (b m k : ℕ) (trial : Layered (b+1+k)) (ψ : QState (b+1+k))
    (target : EuclideanSpace ℂ (Bits b))
    (clean : EuclideanSpace ℂ (Retained (Bits b) (Bits k) m)) (ε : ℝ)
    (h : ‖completeState (fun _ => false) (physicalSingle b k trial ψ)-
      CoherentProjection.tensorState target clean‖ ≤ ε) :
    ‖(WithLp.toLp 2 (runLayered (pipelineCircuit b m k trial) (parallelInitial b m k ψ)-
      basisEmbedding (abstractEmbedding b m k) (CoherentProjection.tensorState target clean)) :
        EuclideanSpace ℂ (Bits (width P m+(m+1)*b+m*k)))‖ ≤ ε := by
  rw [pipelineCircuit_complete,basisEmbedding_error]
  exact h

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end P2MDyadicModule135

/- Helper module Solutions.RegevBridgeCoherentJunkReindex. -/
section P2MDyadicModule136

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentRejection

open CoherentProjection

open scoped BigOperators

variable {O J K : Type*} [Fintype O] [Fintype J] [Fintype K] [DecidableEq O] {m : ℕ}

def retainedJunkEquiv (e : J ≃ K) : Retained O J m ≃ Retained O K m where
  toFun x := (x.1,fun i => ((x.2 i).1,e (x.2 i).2))
  invFun x := (x.1,fun i => ((x.2 i).1,e.symm (x.2 i).2))
  left_inv x := by simp only [Equiv.symm_apply_apply,Prod.eta]
  right_inv x := by simp only [Equiv.apply_symm_apply,Prod.eta]

def relabelSingle (e : J ≃ K) (single : Bool → O → J → ℂ) : Bool → O → K → ℂ :=
  fun b o k => single b o (e.symm k)

theorem completeState_relabel (e : J ≃ K) (zero : O) (single : Bool → O → J → ℂ)
    (x : O×Retained O K m) :
    completeState zero (relabelSingle e single) x=
      completeState zero single (x.1,(retainedJunkEquiv e).symm x.2) := by
  classical
  cases hf : firstSuccess x.2.1 with
  | none => simp [completeState,swappedState,selectedSwap,hf,initialState,relabelSingle,retainedJunkEquiv]
  | some i =>
    simp only [completeState,swappedState,selectedSwap,hf,swapEquiv_apply,swapOutput,
      initialState,relabelSingle,retainedJunkEquiv,Equiv.symm_mk,Equiv.coe_fn_mk]
    split_ifs
    · apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j=i
      · subst j;simp only [Function.update_self]
      · simp only [Function.update_of_ne hj]
    · rfl

noncomputable def relabelJunk (e : J ≃ K) (clean : EuclideanSpace ℂ (Retained O J m)) :
    EuclideanSpace ℂ (Retained O K m) := WithLp.toLp 2 (fun x => clean ((retainedJunkEquiv e).symm x))

theorem relabelJunk_norm (e : J ≃ K) (clean : EuclideanSpace ℂ (Retained O J m)) :
    ‖relabelJunk e clean‖=‖clean‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,relabelJunk]
  exact Fintype.sum_equiv (retainedJunkEquiv e).symm _ _ (by intro x;rfl)

/-- Repacking the complete junk register changes neither the pure-output
factorization nor its full-state error. -/
theorem completeState_relabel_error (e : J ≃ K) (zero : O) (single : Bool → O → J → ℂ)
    (target : EuclideanSpace ℂ O) (clean : EuclideanSpace ℂ (Retained O J m)) :
    ‖completeState zero (relabelSingle e single)-InfoLossLAR.WorstCase.CoherentProjection.tensorState target (relabelJunk e clean)‖=
      ‖completeState zero single-InfoLossLAR.WorstCase.CoherentProjection.tensorState target clean‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl O) (retainedJunkEquiv e).symm)
  intro x
  simp only [PiLp.sub_apply,completeState_relabel,InfoLossLAR.WorstCase.CoherentProjection.tensorState,relabelJunk,Equiv.prodCongr_apply,Equiv.refl_apply]
  rfl

end InfoLossLAR.WorstCase.CoherentRejection

end P2MDyadicModule136

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPipeline. -/
section P2MDyadicModule137

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open QAlgorithms QAlgorithms.Complexity CoherentRejection CoherentComputeUncompute

open NativeWordLayout ControlledNativeGates FiniteGateTransport

open scoped BigOperators

/-- Pack exactly the two synthesis and two interpreter auxiliaries. -/
def packedJunk : TrialJunk ≃ Bits 4 := (qubitsAppendEquiv 2 2).symm

theorem packedTrial_coordinates (W : ℕ) (flag : Bool) (out : Bits W) (junk : Bits 4) :
    (trialCoordinates W).symm (flag,(out,packedJunk.symm junk))=
      (CoherentFirstSuccessNative.splitTrial W 4).symm (flag,(out,junk)) := by
  rw [trialCoordinates_symm]
  change Fin.append (Fin.append out (Fin.append (fun _ : Fin 1 => flag) (packedJunk.symm junk).1))
    (packedJunk.symm junk).2=Fin.append (Fin.append out (fun _ : Fin 1 => flag)) junk
  have hj : Fin.append (packedJunk.symm junk).1 (packedJunk.symm junk).2=junk :=
    (qubitsAppendEquiv 2 2).symm_apply_apply junk
  simp only [Fin.append_assoc,Function.comp_def,Fin.cast_eq_self]
  rw [hj]

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end

end P2MDyadicModule137

/- Helper module Solutions.RegevBridgeCoherentEmbeddedWeightedTrial. -/
section P2MDyadicModule138

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentEmbeddedWeightedTrial

open CoherentComputeUncompute CoherentWeightedPreparation CoherentRejection

open scoped BigOperators

variable {I W J : Type*} [Fintype I] [Fintype W] [Fintype J]
  [Nonempty I] [DecidableEq W] [DecidableEq J]

def single (e : I↪W) (w : I→ℝ) (zero : J) : Bool→W→J→ℂ :=
  fun flag work junk => basisEmbedding e (fun i => prepared w (flag,i)) work*basis zero junk

theorem flagMass_single (e : I↪W) (w : I→ℝ) (zero : J) (flag : Bool) :
    flagMass (single e w zero) flag=∑ i,‖prepared w (flag,i)‖^2 := by
  have hj : (∑ j : J,‖basis zero j‖^2)=(1 : ℝ) := by
    classical
    rw [Finset.sum_eq_single zero]
    · simp [basis]
    · intro j hj hne
      simp [basis,hne]
    · simp
  simp only [flagMass,single,norm_mul,mul_pow]
  simp_rw [←Finset.mul_sum,hj,mul_one]
  exact basisEmbedding_mass e _

theorem single_normalized (e : I↪W) (w : I→ℝ) (zero : J)
    (hw : ∀ i,0≤w i ∧ w i≤1) :
    flagMass (single e w zero) false+flagMass (single e w zero) true=1 := by
  rw [flagMass_single,flagMass_single,false_mass w (fun i => (hw i).2),true_mass w (fun i => (hw i).1)]
  ring

theorem target_normalized (e : I↪W) (w : I→ℝ) (hw : ∀ i,0≤w i) (hZ : 0<weightSum w) :
    ∑ o,‖target e w o‖^2=1 := by
  rw [target,basisEmbedding_mass]
  exact CoherentWeightedPreparation.target_normalized w hw hZ

theorem single_success (e : I↪W) (w : I→ℝ) (zero : J) (hZ : 0<weightSum w) (o : W) (j : J) :
    single e w zero true o j=successAmplitude w*target e w o*basis zero j := by
  have hp : (fun i => prepared w (true,i))=
      successAmplitude w •CoherentWeightedPreparation.target w := by
    funext i
    simpa only [Pi.smul_apply,smul_eq_mul] using success_factorization w hZ i
  unfold single target
  rw [hp,map_smul]
  rfl

theorem single_false_mass (e : I↪W) (w : I→ℝ) (zero : J) (hw : ∀ i,w i≤1) :
    flagMass (single e w zero) false=1-weightSum w/(Fintype.card I : ℝ) := by
  rw [flagMass_single,false_mass w hw]

/-- The complete physical output/work embedding preserves the pure
weighted success target, all failed trials and every auxiliary. -/
theorem actual_copies_pure (e : I↪W) (w : I→ℝ) (zeroJ : J) (zeroW : W)
    (hw : ∀ i,0≤w i ∧ w i≤1) (hZ : 0<weightSum w)
    (actual : Bool→W→J→ℂ) (ha : flagMass actual false+flagMass actual true=1)
    (δ : ℝ) (he : ‖singleVector actual-singleVector (single e w zeroJ)‖≤δ)
    (m : ℕ) (hm : m≠0) :
    ∃ clean : EuclideanSpace ℂ (Retained W J m),‖clean‖=1 ∧
      ‖completeState (m:=m) zeroW actual-
        CoherentProjection.tensorState (WithLp.toLp 2 (target e w)) clean‖≤
        (m : ℝ)*δ+2*Real.sqrt ((1-weightSum w/(Fintype.card I : ℝ))^m) := by
  have hcard : (0 : ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hp0 : 0<weightSum w/(Fintype.card I : ℝ) := div_pos hZ hcard
  have hp1 : weightSum w/(Fintype.card I : ℝ)≤1 := by
    have hn : 0≤flagMass (single e w zeroJ) false := by
      unfold flagMass
      exact Finset.sum_nonneg (fun o _ => Finset.sum_nonneg (fun j _ => sq_nonneg (‖single e w zeroJ false o j‖)))
    rw [single_false_mass e w zeroJ (fun i => (hw i).2)] at hn
    linarith
  exact completeState_approx_pure zeroW actual (single e w zeroJ) ha
    (single_normalized e w zeroJ hw) δ he (successAmplitude w) (target e w) (basis zeroJ)
    (single_success e w zeroJ hZ) (target_normalized e w (fun i => (hw i).1) hZ)
    _ hp0 hp1 hm (single_false_mass e w zeroJ (fun i => (hw i).2))

end InfoLossLAR.WorstCase.CoherentEmbeddedWeightedTrial

end

end P2MDyadicModule138

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingTrial. -/
section P2MDyadicModule139

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

def initial (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :=
  initializeAux (Builder.inputMap request hr a slots word K
    (initWithReference (r:=2) (Preparation.proposalInitial K)))

def idealPhysical (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (s : ℝ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K) :=
  initializeAux (Builder.inputMap request hr a slots word K
    (applyDependentReference (fun tape => idealMap (NativeCoherentAcceptanceError.realIdeal
      (capacityWeight (request word).1 s K hK tape)) 2) (Preparation.proposalInitial K)))

def idealSingle (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (s : ℝ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K) :=
  regroupTrial (idealPhysical request hr a slots word K s hK)

theorem prepared_value (K : ℕ) (w : Bits K→ℝ) :
    applyDependentReference (fun t => NativeCoherentAcceptanceError.realIdeal (w t))
      (Preparation.proposalInitial K)=
      (fun x => prepared w (oneBitEquiv x.1,x.2)) := by
  funext x
  change (∑ b : Bits 1,(NativeCoherentAcceptanceError.realIdeal (w x.2)) x.1 b*
    Preparation.proposalInitial K (b,x.2))=∑ b : Bool,
      AcceptanceRotation.ideal (w x.2) (oneBitEquiv x.1) b*CoherentWeightedPreparation.initial (b,x.2)
  exact Fintype.sum_equiv oneBitEquiv _ _ (by intro b;rfl)

theorem idealSingle_value (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (s : ℝ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K)
    (flag : Bool) (work : Bits (workSize request hr a slots K)) (junk : TrialJunk) :
    idealSingle request hr a slots word K s hK flag work junk=
      if junk=((fun _ => false),(fun _ => false)) then
        ∑ tape : Bits K,prepared (capacityWeight (request word).1 s K hK) (flag,tape)*
          basis (workTicket request hr a slots word K tape) work else 0 := by
  unfold idealSingle idealPhysical regroupTrial
  rw [dependent_ideal,prepared_value,trialCoordinates_symm]
  simp only [initializeAux,Builder.inputMap,NativeWordCoherent.inputMap,LinearMap.comp_apply,embedInputs,
    LinearMap.coe_mk,AddHom.coe_mk,assembleMap,Fin.append_left,Fin.append_right,
    initWithReference,qubitsAppendEquiv,Equiv.coe_fn_mk,oneBitEquiv,Fin.zero_eta,Fin.isValue,
    Finset.sum_apply,tensor,Function.comp_apply]
  by_cases h1 : junk.1=(fun _ => false) <;> by_cases h2 : junk.2=(fun _ => false) <;>
    simp [h1,h2,Prod.ext_iff,workTicket,workSize]
  all_goals rfl

theorem idealSingle_embedded (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (s : ℝ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K) :
    idealSingle request hr a slots word K s hK=
      CoherentEmbeddedWeightedTrial.single (workEmbedding request hr a slots word K)
        (capacityWeight (request word).1 s K hK) ((fun _ => false),(fun _ => false)) := by
  funext flag work junk
  rw [idealSingle_value]
  simp only [CoherentEmbeddedWeightedTrial.single,basisEmbedding,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,workEmbedding,basis]
  by_cases hj : junk=((fun _ => false),(fun _ => false)) <;> simp [hj]

def actualPhysical (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) :=
  runLayered (physicalCircuit request hr a b slots K budget) (initial request hr a slots word K)

def actualSingle (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) :=
  regroupTrial (actualPhysical request hr a b slots word K budget)

theorem initial_norm (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    stateNorm (initial request hr a slots word K)=1 := by
  unfold initial
  change ‖(WithLp.toLp 2 (initializeAux _) : EuclideanSpace ℂ _)‖=1
  rw [initializeAux_norm]
  change stateNorm (NativeWordCoherent.inputMap _ _ _ _ _ _ _)=1
  rw [NativeWordCoherent.inputMap_norm _ _ _ _ _ _ (encoded_length slots word)
    (encoded_injective slots word K),initWithReference_norm,Preparation.proposalInitial_norm]

theorem actualSingle_normalized (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) :
    flagMass (actualSingle request hr a b slots word K budget) false+
      flagMass (actualSingle request hr a b slots word K budget) true=1 := by
  have hn : ‖singleVector (actualSingle request hr a b slots word K budget)‖=1 := by
    rw [actualSingle,regroupTrial_norm]
    change ‖(WithLp.toLp 2 (runLayered _ _) : EuclideanSpace ℂ _)‖=1
    have he := (circuitIsometry (physicalCircuit request hr a b slots K budget)).norm_map
      (WithLp.toLp 2 (initial request hr a slots word K))
    change stateNorm (runLayered _ (initial request hr a slots word K))=stateNorm (initial request hr a slots word K) at he
    exact he.trans (initial_norm request hr a slots word K)
  have hs := congrArg (fun x : ℝ => x^2) hn
  simp only [EuclideanSpace.norm_sq_eq,singleVector,Fintype.sum_prod_type,Fintype.sum_bool,one_pow] at hs
  have heq : flagMass (actualSingle request hr a b slots word K budget) true+
      flagMass (actualSingle request hr a b slots word K budget) false=1 := by
    simpa only [flagMass,Fintype.sum_prod_type] using hs
  linarith

def error (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) : ℝ :=
  180*(((wordBound request hr a).eval (2*slots.length+1+K) : ℕ) : ℝ)/((budget.length : ℝ)+1)+
    (5/(((request word).2.length : ℝ)+1)+2*Real.sqrt (1/(2 : ℝ)^((request word).1.2.2.length)))

theorem exists_accuracy :
    ∃ synthesis interpreter : ℕ,0 < synthesis ∧ 0 < interpreter ∧
      ∀ (slots : List Unit) (word : Str) (s : ℝ) (budget : List Unit)
        (h : 2*word.length+1 ≤ slots.length) (K : ℕ)
        (hK : Nat.size (intervalCount (request word).1) ≤ K),
        s^2=(variance (request word).1 : ℝ) →
        ‖singleVector (actualSingle request hr synthesis interpreter slots word K budget)-
          singleVector (idealSingle request hr synthesis slots word K s hK)‖≤
          error request hr synthesis slots word K budget := by
  obtain ⟨a,ha,h⟩:=Builder.exists_physicalCircuit_accuracy request hr
  obtain ⟨b,hb,hphase⟩:=ControlledNativeGates.exists_parameter
  refine ⟨a,b,ha,hb,?_⟩
  intro slots word s budget hh K hK hs
  have hh := h b hphase slots word s budget hh K hK hs (Preparation.proposalInitial K)
  rw [Preparation.proposalInitial_norm,mul_one] at hh
  change ‖singleVector (regroupTrial _)-singleVector (regroupTrial _)‖≤_
  rw [regroupTrial_sub,regroupTrial_norm]
  exact hh

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Trial

end

end P2MDyadicModule139

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingPure. -/
section P2MDyadicModule140

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

/-- Every parameter of the native request is computed from the retained
original binary public word. The same two fixed synthesis exponents work
for every word, both public capacities, and every later accuracy budget. -/
theorem exists_actual_copies_pure :
    ∃ synthesis interpreter : ℕ,0 < synthesis ∧ 0 < interpreter ∧
      ∀ (slots : List Unit) (word : Str) (s : ℝ) (budget : List Unit),
        2*word.length+1 ≤ slots.length →
        ∀ (K : ℕ) (hK : Nat.size (intervalCount (request word).1) ≤ K),
        1 ≤ s → s^2=(variance (request word).1 : ℝ) → 2 ≤ (request word).1.2.1.length →
        ∀ m : ℕ,m≠0 →
        ∃ clean : EuclideanSpace ℂ (Retained (Bits (workSize request hr synthesis slots K)) TrialJunk m),
          ‖clean‖=1 ∧
          ‖completeState (m:=m) (fun _ => false) (actualSingle request hr synthesis interpreter slots word K budget)-
            CoherentProjection.tensorState (embeddedTarget request hr synthesis slots word K s hK) clean‖ ≤
            (m : ℝ)*error request hr synthesis slots word K budget+
              2*Real.exp (-(m : ℝ)/(112*((request word).1.2.1.length : ℝ))) := by
  obtain ⟨a,b,ha,hb,haccuracy⟩:=exists_accuracy request hr
  refine ⟨a,b,ha,hb,?_⟩
  intro slots word s budget hslots K hK hs hsquare hfactor m hm
  have hp:=successProbability_bounds (request word).1 s hs hsquare hfactor
  have hp0 : 0 < successProbability (request word).1 s :=
    (by positivity : (0 : ℝ) < 1/(56*((request word).1.2.1.length : ℝ))).trans_le hp.1
  have hcard : (0 : ℝ) < Fintype.card (Bits K) := by exact_mod_cast Fintype.card_pos
  have hZ : 0 < weightSum (capacityWeight (request word).1 s K hK) := by
    have hdiv : 0 < weightSum (capacityWeight (request word).1 s K hK)/(Fintype.card (Bits K) : ℝ) := by
      rw [capacity_success_probability]
      exact hp0
    simpa only [div_mul_cancel₀ _ (ne_of_gt hcard)] using mul_pos hdiv hcard
  have herr:=haccuracy slots word s budget hslots K hK hsquare
  rw [idealSingle_embedded] at herr
  obtain ⟨clean,hn,hclose⟩:=CoherentEmbeddedWeightedTrial.actual_copies_pure
    (workEmbedding request hr a slots word K) (capacityWeight (request word).1 s K hK)
    ((fun _ => false),(fun _ => false)) (fun _ => false)
    (fun tape => weight_bounds (request word).1 s _) hZ
    (actualSingle request hr a b slots word K budget) (actualSingle_normalized request hr a b slots word K budget)
    (error request hr a slots word K budget) herr m hm
  rw [capacity_success_probability] at hclose
  refine ⟨clean,hn,?_⟩
  have hexp:=failure_sqrt_exp (successProbability (request word).1 s)
    (1/(56*((request word).1.2.1.length : ℝ))) hp.2 hp.1 m
  have heq : -(m : ℝ)*(1/(56*((request word).1.2.1.length : ℝ)))/2=
      -(m : ℝ)/(112*((request word).1.2.1.length : ℝ)) := by ring
  rw [heq] at hexp
  exact hclose.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2)))

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Trial

end

end P2MDyadicModule140

/- Helper module Solutions.RegevBridgeCoherentParallelInitialPreparation. -/
section P2MDyadicModule141

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

private theorem basisEmbedding_basis {I W : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (e : I↪W) (i : I) : basisEmbedding e (basis i)=basis (e i) := by
  classical
  simp only [basisEmbedding,basis,LinearMap.coe_mk,AddHom.coe_mk]
  simp

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

theorem parallelInitial_regroup (b m k : ℕ) (ψ : QState (b+1+k)) :
    parallelInitial b m k ψ=basisEmbedding (copyEmbedding b m k) (repeatState m (WithLp.toLp 2 ψ)) := by
  unfold parallelInitial
  rw [initializedWires_copies]
  apply congrArg (basisEmbedding (copyEmbedding b m k))
  funext copies
  simp only [CoherentParallelTrials.initial_product,Equiv.apply_symm_apply,repeatState]

theorem parallelInitial_basis (b m k : ℕ) (bits : Bits (b+1+k)) :
    parallelInitial b m k (basis bits)=basis (copyEncoding b m k (fun _ => bits)) := by
  rw [parallelInitial_regroup,repeatState_basis]
  change basisEmbedding (copyEmbedding b m k) (basis (fun _ : Fin m => bits))=_
  exact basisEmbedding_basis (copyEmbedding b m k) (fun _ : Fin m => bits)

variable {f : Str→Str} (program : PolyProgram id id f)

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative.InitialNative

end

end P2MDyadicModule141

/- Helper module Solutions.RegevBridgeCoherentWideGaussianPaddingPipeline. -/
section P2MDyadicModule142

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

theorem fixedProposal_prepares (words : Str→List ℕ) (hw : Poly words) (p : Polynomial ℕ)
    (headerBits : Str) (H K : ℕ) (hH : headerBits.length=H) :
    runLayered (fixedProposalCircuit words hw p H K)
      (basis (fun i => TM2Boolean.wordExtension (headerBits++List.ofFn (fun _ : Fin K => false)) i.val))=
      initializeAux (NativeWordCoherent.inputMap words hw p (H+K) 3 (fun tape : Bits K => headerBits++List.ofFn tape)
        (initWithReference (r:=2) (Preparation.proposalInitial K))) := by
  subst H
  exact Preparation.actual_hadamard_prepares words hw p headerBits K

def proposalCircuit (a : ℕ) (slots : List Unit) (_word : Str) (K : ℕ) :
    Layered (Trial.workSize request hr a slots K+1+4) :=
  fixedProposalCircuit (gateWord request a) (gateWord_poly request hr a) (wordBound request hr a)
    (2*slots.length+1) K

def initialBasis (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    Bits (Trial.workSize request hr a slots K+1+4) :=
  fun i => TM2Boolean.wordExtension (encoded slots word (fun _ : Fin K => false)) i.val

theorem proposalCircuit_prepares (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    runLayered (proposalCircuit request hr a slots word K) (basis (initialBasis request hr a slots word K))=
      Trial.initial request hr a slots word K := by
  exact fixedProposal_prepares (gateWord request a) (gateWord_poly request hr a) (wordBound request hr a)
    (Preparation.builderHeader slots word) (2*slots.length+1) K (Preparation.builderHeader_length slots word)

/-- Actual H preparation followed by the genuine native interpreter. Its
layout uses the two public capacities, never the computed active length. -/
def trialCircuit (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) :=
  proposalCircuit request hr a slots word K++physicalCircuit request hr a b slots K budget

theorem physicalSingle_prepared (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) :
    physicalSingle (Trial.workSize request hr a slots K) 4 (trialCircuit request hr a b slots word K budget)
      (basis (initialBasis request hr a slots word K))=
      relabelSingle packedJunk (Trial.actualSingle request hr a b slots word K budget) := by
  funext flag out junk
  unfold physicalSingle trialCircuit
  rw [runLayered,List.foldl_append]
  change runLayered (physicalCircuit request hr a b slots K budget)
    (runLayered (proposalCircuit request hr a slots word K) (basis (initialBasis request hr a slots word K))) _=_
  rw [proposalCircuit_prepares]
  unfold relabelSingle Trial.actualSingle regroupTrial Trial.actualPhysical
  rw [packedTrial_coordinates]

/-- The literal complete finite-gate rejection circuit, including its own
H preparation, consumes an ordinary basis state with all auxiliary bits zero. -/
def circuit (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) (m : ℕ) :=
  pipelineCircuit (Trial.workSize request hr a slots K) m 4 (trialCircuit request hr a b slots word K budget)

def basisInput (a : ℕ) (slots : List Unit) (word : Str) (K m : ℕ) :=
  copyEncoding (Trial.workSize request hr a slots K) m 4 (fun _ => initialBasis request hr a slots word K)

/-- The output contains the literal retained public header and the full
fixed K-bit ticket. The clean factor contains every unselected row, success
flag, synthesis/interpreter auxiliary, and first-success machine register. -/
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
  obtain ⟨a,b,ha,hb,h⟩:=Trial.exists_actual_copies_pure request hr
  refine ⟨a,b,ha,hb,?_⟩
  intro slots word s budget hslots K hK hs hsquare hfactor m hm
  obtain ⟨clean,hn,hc⟩:=h slots word s budget hslots K hK hs hsquare hfactor m hm
  refine ⟨relabelJunk packedJunk clean,(relabelJunk_norm packedJunk clean).trans hn,?_⟩
  change ‖(WithLp.toLp 2 (runLayered (pipelineCircuit _ _ _ _) (basis (copyEncoding _ _ _ _))-
    basisEmbedding _ _) : EuclideanSpace ℂ _)‖ ≤ _
  rw [←InitialNative.parallelInitial_basis]
  apply pipelineCircuit_pure_error
  rw [physicalSingle_prepared,completeState_relabel_error]
  exact hc

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Pipeline

end

end P2MDyadicModule142

/- Helper module RawTicketProof. -/
section P2MDyadicModule143

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.RegisteredTrial

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent NativeWordLayout

open QAlgorithms.Papers.Independent.Renew46.P12

open CoherentWeightedPreparation CoherentComputeUncompute ControlledNativeGates CoherentRejection

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Builder

noncomputable section

variable (request : Str→PointRequest×List Unit) (hp : ∀ a : ℕ, Poly (Builder.gateWord request a))

theorem _root_.solution (request : Str → PointRequest × List Unit) (hr : Poly request) (hp : ∀ a : ℕ, Poly (Builder.gateWord request a)) : contract request hp := by
  exact Builder.Pipeline.exists_pure_from_basis request hr

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.RegisteredTrial

end P2MDyadicModule143

#print axioms solution
