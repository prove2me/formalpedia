-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier.signed_qft_joint
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:39:57.554263+00:00
-- url     : https://prove2.me/submissions/c05f61fa-6e69-4208-8e90-52ff12cf85a7

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_NativeSparsePrefix_02
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
import Definitions.Def_InfoLossLAR_RuntimeBundle_01
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Mathlib
import Theorems.Thm_CliffordTApprox_Ancilla_main_result
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_ShorAlgorithms_QFT_qft_circuit_eq
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral

set_option linter.all false

namespace AFT
end AFT

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace GridReadout.Axis
end GridReadout.Axis

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute
end InfoLossLAR.WorstCase.CoherentComputeUncompute

namespace InfoLossLAR.WorstCase.CoherentDecoder
end InfoLossLAR.WorstCase.CoherentDecoder

namespace InfoLossLAR.WorstCase.CoherentProjection
end InfoLossLAR.WorstCase.CoherentProjection

namespace InfoLossLAR.WorstCase.ControlledNativeGates
end InfoLossLAR.WorstCase.ControlledNativeGates

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

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

namespace InfoLossLAR.WorstCase.NativeDualQuotient
end InfoLossLAR.WorstCase.NativeDualQuotient

namespace InfoLossLAR.WorstCase.NativeQFTPlan
end InfoLossLAR.WorstCase.NativeQFTPlan

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile
end InfoLossLAR.WorstCase.NativeQFTPlanCompile

namespace InfoLossLAR.WorstCase.QuantumXorOracle
end InfoLossLAR.WorstCase.QuantumXorOracle

namespace InfoLossLAR.WorstCase.RegevSearch
end InfoLossLAR.WorstCase.RegevSearch

namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT
end InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT

namespace InfoLossLARNativeSupplements.h1076ff82614707e5.AFT
end InfoLossLARNativeSupplements.h1076ff82614707e5.AFT

namespace InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT
end InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT

namespace InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT
end InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT

namespace InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT
end InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT

namespace InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT
end InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT

namespace InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT
end InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT

namespace InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT
end InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT

namespace InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT
end InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT

namespace InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT
end InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT

namespace InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT
end InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT

namespace InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT
end InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT

namespace InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT
end InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT

namespace InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT
end InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT

namespace InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT
end InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT

namespace InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT
end InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT

namespace InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT
end InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT

namespace InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT
end InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT

namespace InfoLossLARNativeSupplements.h90032182500c2e77.AFT
end InfoLossLARNativeSupplements.h90032182500c2e77.AFT

namespace InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT
end InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT

namespace InfoLossLARNativeSupplements.ha562531658b7642e.AFT
end InfoLossLARNativeSupplements.ha562531658b7642e.AFT

namespace InfoLossLARNativeSupplements.had468f01f375d910.AFT
end InfoLossLARNativeSupplements.had468f01f375d910.AFT

namespace InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT
end InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT

namespace InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT
end InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT

namespace InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT
end InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT

namespace InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT
end InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT

namespace InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT
end InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT

namespace InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT
end InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT

namespace InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT
end InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT

namespace InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT
end InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT

namespace InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT
end InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT

namespace InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT
end InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT

namespace Integration9_9
end Integration9_9

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

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

/- Helper module Solutions.RegevBridgeGaussianLatticeTransport. -/
section P2MDyadicModule1

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

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeGaussianLatticeScaling. -/
section P2MDyadicModule2

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

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeGaussianCosetGeometry. -/
section P2MDyadicModule3

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

theorem pairing_basis {Index : Type*} [Fintype Index]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (nearest : dual lattice) (value : lattice) :
    pairing lattice nearest value=∑ index,basis.equivFun value index*pairing lattice nearest (basis index) := by
  have h := congrArg (pairing lattice nearest) (basis.sum_repr value)
  rw [map_sum] at h
  simp only [map_smul,smul_eq_mul,Module.Basis.equivFun_apply] at h ⊢
  exact h.symm

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

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeGaussianCosetPartition. -/
section P2MDyadicModule4

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

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule5

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

theorem publicCoordinates_coefficient_point (q : ℕ)
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (value : Fin dimension → ℤ) :
    CosetGeometry.publicCoordinates q (inputLattice basis hdet) (integerBasis basis hdet)
      ((integerBasis basis hdet).equivFun.symm value)=(fun index => (value index : ZMod q)) := by
  unfold CosetGeometry.publicCoordinates
  rw [LinearEquiv.apply_symm_apply]

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeIntegerDualCoordinates. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

instance dual_input_discrete (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    DiscreteTopology (dual (inputLattice basis hdet)) := by
  rw [dual_lattice_eq_span]
  infer_instance

instance dual_input_full_rank (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    IsZLattice ℝ (dual (inputLattice basis hdet)) := by
  constructor
  rw [dual_lattice_eq_span]
  exact ZSpan.span_top (dualRealBasis basis hdet)

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeGaussianPoissonSeries. -/
section P2MDyadicModule7

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

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeLatticeGaussianSummable. -/
section P2MDyadicModule8

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

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeFiniteLatticeFourier. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier

open scoped BigOperators

noncomputable section

/-- The actual tensor-product finite Fourier character on the coordinate
quotient of a rank-n lattice by its integer modulus. -/
def character {dimension modulus : ℕ} [NeZero modulus] (first second : Fin dimension → ZMod modulus) : ℂ :=
  ∏ index,ZMod.stdAddChar (first index*second index)

theorem character_add_right {dimension modulus : ℕ} [NeZero modulus]
    (source first second : Fin dimension → ZMod modulus) :
    character source (first+second)=character source first*character source second := by
  simp only [character,Pi.add_apply,mul_add,AddChar.map_add_eq_mul,Finset.prod_mul_distrib]

theorem character_norm {dimension modulus : ℕ} [NeZero modulus] (source frequency : Fin dimension → ZMod modulus) :
    ‖character source frequency‖=1 := by
  simp only [character,norm_prod,ZMod.stdAddChar_apply,Circle.norm_coe,Finset.prod_const_one]

theorem scalar_character_sum (modulus : ℕ) [NeZero modulus] (frequency : ZMod modulus) :
    (∑ source : ZMod modulus,ZMod.stdAddChar (source*frequency))=
      if frequency=0 then (modulus : ℂ) else 0 := by
  by_cases hfrequency : frequency=0
  · simp only [hfrequency,mul_zero,AddChar.map_zero_eq_one,Finset.sum_const,Finset.card_univ,
      ZMod.card,nsmul_eq_mul,mul_one,if_true]
  · rw [if_neg hfrequency]
    simpa only [AddChar.mulShift_apply,mul_comm] using AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar modulus hfrequency)

/-- Exact character orthogonality keeps the whole finite quotient; no
single-coordinate marginal uniformity is substituted for this identity. -/
theorem character_sum {dimension modulus : ℕ} [NeZero modulus]
    (frequency : Fin dimension → ZMod modulus) :
    (∑ source : Fin dimension → ZMod modulus,character source frequency)=
      if frequency=0 then (modulus : ℂ)^dimension else 0 := by
  classical
  unfold character
  have hproduct := Fintype.prod_sum (fun index : Fin dimension => fun value : ZMod modulus =>
    ZMod.stdAddChar (value*frequency index))
  rw [←hproduct]
  simp only [scalar_character_sum modulus]
  by_cases hfrequency : frequency=0
  · subst frequency
    simp only [Pi.zero_apply,if_true,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  · rw [if_neg hfrequency]
    obtain ⟨index,hindex⟩ := Function.ne_iff.mp hfrequency
    apply Finset.prod_eq_zero (Finset.mem_univ index)
    exact if_neg hindex

/-- An unnormalized finite DFT. The physical QFT contributes the usual
positive inverse-square-root cardinal factor to this exact amplitude. -/
def transform {dimension modulus : ℕ} [NeZero modulus] (amplitude : (Fin dimension → ZMod modulus) → ℂ)
    (frequency : Fin dimension → ZMod modulus) : ℂ :=
  ∑ source,character source (-frequency)*amplitude source

/-- Absolute convergence survives multiplication by the exact characters. -/
theorem summable_character_series {Index : Type*} {dimension modulus : ℕ} [NeZero modulus]
    (coefficient : Index → ℂ) (hsummable : Summable coefficient)
    (frequency : Index → (Fin dimension → ZMod modulus)) (source : Fin dimension → ZMod modulus) :
    Summable (fun index => coefficient index*character source (frequency index)) := by
  apply Summable.of_norm_bounded hsummable.norm
  intro index
  rw [norm_mul,character_norm,mul_one]

/-- Finite Fourier transformation of a genuine absolutely convergent
periodic Fourier series selects the entire matching residue fiber. -/
theorem transform_character_series {Index : Type*} {dimension modulus : ℕ} [NeZero modulus]
    (coefficient : Index → ℂ) (hsummable : Summable coefficient)
    (residue : Index → (Fin dimension → ZMod modulus)) (target : Fin dimension → ZMod modulus) :
    transform (fun source => ∑' index,coefficient index*character source (residue index)) target=
      (modulus : ℂ)^dimension*∑' index,if residue index=target then coefficient index else 0 := by
  classical
  unfold transform
  simp_rw [←tsum_mul_left]
  have hsum (source : Fin dimension → ZMod modulus) :
      Summable (fun index => character source (-target)*(coefficient index*character source (residue index))) :=
    (summable_character_series coefficient hsummable residue source).mul_left _
  rw [←Summable.tsum_finsetSum (fun source (_ : source ∈ Finset.univ) => hsum source)]
  have hinner (index : Index) :
      (∑ source : Fin dimension → ZMod modulus,
        character source (-target)*(coefficient index*character source (residue index)))=
        (modulus : ℂ)^dimension*(if residue index=target then coefficient index else 0) := by
    calc
      _ = coefficient index*∑ source : Fin dimension → ZMod modulus,
          character source ((residue index)-target) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source _
        rw [sub_eq_add_neg,character_add_right]
        ring
      _ = _ := by
        rw [character_sum]
        by_cases hequal : residue index=target <;> simp [hequal,sub_eq_zero,mul_comm]
  simp only [hinner,tsum_mul_left]

end

end InfoLossLAR.WorstCase.FiniteLatticeFourier

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeLatticeFourierCoordinates. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier

open GaussianProjection.CosetGeometry RegevLWE.GaussConv

open scoped BigOperators FourierTransform

noncomputable section

private theorem stdAddChar_sum {Index : Type*} {modulus : ℕ} [NeZero modulus]
    (set : Finset Index) (value : Index → ZMod modulus) :
    ZMod.stdAddChar (∑ index ∈ set,value index)=∏ index ∈ set,ZMod.stdAddChar (value index) := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert index set hnot ih =>
    rw [Finset.sum_insert hnot,Finset.prod_insert hnot,AddChar.map_add_eq_mul,ih]

/-- The coordinate quotient character is exactly the complex exponential
on original integral coordinate representatives, for every modulus. -/
theorem character_intCast {dimension modulus : ℕ} [NeZero modulus]
    (first second : Fin dimension → ℤ) :
    character (fun index => (first index : ZMod modulus)) (fun index => (second index : ZMod modulus))=
      Complex.exp ((2 : ℂ)*(Real.pi : ℂ)*Complex.I*((∑ index,first index*second index : ℤ) : ℂ)/(modulus : ℂ)) := by
  calc
    _ = ∏ index,ZMod.stdAddChar ((first index*second index : ℤ) : ZMod modulus) := by
      simp only [character,Int.cast_mul]
    _ = ZMod.stdAddChar ((∑ index,first index*second index : ℤ) : ZMod modulus) := by
      exact (stdAddChar_sum Finset.univ (fun index => ((first index*second index : ℤ) : ZMod modulus))).symm.trans
        (congrArg ZMod.stdAddChar (Int.cast_sum _ _).symm)
    _ = _ := ZMod.stdAddChar_coe _

variable {dimension : ℕ}

theorem gridPoint_inner (modulus : ℕ) [NeZero modulus]
    (lattice : Submodule ℤ (CoordinateSpace (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (color : Fin dimension → ZMod modulus)
    (frequency : dual lattice) :
    inner ℝ (gridPoint modulus lattice basis color) (frequency : CoordinateSpace (dimension:=dimension))=
      (((∑ index,((color index).val : ℤ)*pairing lattice frequency (basis index)) : ℤ) : ℝ)/(modulus : ℝ) := by
  rw [gridPoint,real_inner_smul_left,real_inner_comm,
    ←pairing_spec lattice frequency (GaussianProjection.CosetGeometry.lift modulus lattice basis color),
    pairing_basis lattice basis frequency (GaussianProjection.CosetGeometry.lift modulus lattice basis color)]
  simp only [GaussianProjection.CosetGeometry.lift,LinearEquiv.apply_symm_apply]
  rw [div_eq_mul_inv]
  ring

/-- Pairing the genuine fine-grid point with a genuine dual lattice point
produces exactly the finite Fourier character of its residue coordinates. -/
theorem gridPoint_fourierChar (modulus : ℕ) [NeZero modulus]
    (lattice : Submodule ℤ (CoordinateSpace (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (color : Fin dimension → ZMod modulus)
    (frequency : dual lattice) :
    (𝐞 (inner ℝ (gridPoint modulus lattice basis color) (frequency : CoordinateSpace (dimension:=dimension))) : ℂ)=
      character color (secretCoordinates modulus lattice basis frequency) := by
  have hfirst : (fun index => (((color index).val : ℤ) : ZMod modulus))=color := by
    funext index
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  have h := character_intCast (modulus:=modulus) (fun index => ((color index).val : ℤ))
    (fun index => pairing lattice frequency (basis index))
  rw [hfirst] at h
  change character color (secretCoordinates modulus lattice basis frequency)=_ at h
  rw [h,gridPoint_inner,Real.fourierChar_apply]
  congr 1
  push_cast
  ring

end

end InfoLossLAR.WorstCase.FiniteLatticeFourier

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeGaussianFiniteFourier. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier

open GaussianPoissonSeries GaussianProjection.CosetGeometry RegevLWE.GaussConv

open scoped BigOperators FourierTransform

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- Multiplication by the public scalar normalization commutes with the
literal finite Fourier transform. -/
theorem transform_const_mul (constant : ℂ) (amplitude : (Fin dimension → ZMod modulus) → ℂ)
    (target : Fin dimension → ZMod modulus) :
    transform (fun color => constant*amplitude color) target=constant*transform amplitude target := by
  unfold transform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro color _
  ring

/-- The complete unphased dual Gaussian has absolutely summable complex
coefficients. This statement makes no smoothing or tail approximation. -/
theorem summable_dual_gaussian (lattice : Submodule ℤ (CoordinateSpace (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0<width) :
    Summable (fun frequency : dual lattice => (rho (1/width) (frequency : CoordinateSpace (dimension:=dimension)) : ℂ)) := by
  simpa using GaussianPoissonSeries.summable_dual_series lattice width hwidth 0

/-- Exact finite Fourier amplitudes of the actual fine-grid periodized
lattice Gaussian. The selected expression contains every dual lattice
point having the target residue, with its genuine Gaussian coefficient. -/
theorem periodized_gaussian_transform
    (lattice : Submodule ℤ (CoordinateSpace (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width : ℝ) (hwidth : 0<width)
    (target : Fin dimension → ZMod modulus) :
    transform (fun color => periodizedGaussian lattice width (gridPoint modulus lattice basis color)) target=
      (ZLattice.covolume lattice : ℂ)⁻¹*((modulus : ℂ)^dimension*
        ∑' frequency : dual lattice,if secretCoordinates modulus lattice basis frequency=target then
          (width : ℂ)^dimension*(rho (1/width) (frequency : CoordinateSpace (dimension:=dimension)) : ℂ) else 0) := by
  classical
  let coefficient : dual lattice → ℂ := fun frequency =>
    (width : ℂ)^dimension*(rho (1/width) (frequency : CoordinateSpace (dimension:=dimension)) : ℂ)
  have hsum : Summable coefficient := (summable_dual_gaussian lattice width hwidth).mul_left _
  have hsource : (fun color : Fin dimension → ZMod modulus =>
      periodizedGaussian lattice width (gridPoint modulus lattice basis color))=
      (fun color => (ZLattice.covolume lattice : ℂ)⁻¹*
        ∑' frequency : dual lattice,coefficient frequency*character color (secretCoordinates modulus lattice basis frequency)) := by
    funext color
    rw [periodized_poisson lattice width hwidth]
    simp only [gridPoint_fourierChar,coefficient]
  rw [hsource,transform_const_mul,transform_character_series coefficient hsum]

end

end InfoLossLAR.WorstCase.FiniteLatticeFourier

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeLatticeGaussianMass. -/
section P2MDyadicModule12

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

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgePeriodizedTailBound. -/
section P2MDyadicModule13

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- Full nonnegative fiber sums on an arbitrary finite quotient. -/
def fiberMass {Index Color : Type*} [DecidableEq Color]
    (quotient : Index → Color) (weight : Index → ℝ) (color : Color) : ℝ :=
  ∑' point,if quotient point=color then weight point else 0

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeNativeGaussianSmoothing. -/
section P2MDyadicModule14

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

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgePrimalDualCoordinates. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection.CosetGeometry GaussianPoissonSeries

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- The original lattice is identified with its genuine Euclidean double
dual, retaining exactly the original physical vector. -/
def primalDoubleDualEquiv (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0) :
    inputLattice basis hdet ≃ dual (dual (inputLattice basis hdet)) where
  toFun point := ⟨point.val,by rw [dual_dual_input];exact point.property⟩
  invFun point := ⟨point.val,by simpa only [dual_dual_input basis hdet] using point.property⟩
  left_inv point := by apply Subtype.ext;rfl
  right_inv point := by apply Subtype.ext;rfl

theorem primalDoubleDualEquiv_coe (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (point : inputLattice basis hdet) :
    (primalDoubleDualEquiv basis hdet point : Space (dimension:=dimension))=point := rfl

theorem dualIntegerBasis_coe (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (index : Fin dimension) :
    (dualIntegerBasis basis hdet index : Space (dimension:=dimension))=dualRealBasis basis hdet index := by
  rw [dualIntegerBasis,Module.Basis.map_apply,Pi.basisFun_apply]
  change dualCoordinates basis hdet (Pi.single index 1)=_
  simp [dualCoordinates_apply,Pi.single_apply]

/-- Original-basis coefficients are exactly the pairings against the
actual dual columns, rather than coordinates in a newly chosen basis. -/
theorem primal_inner_dual (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (point : inputLattice basis hdet) (index : Fin dimension) :
    inner ℝ (point : Space (dimension:=dimension)) (dualRealBasis basis hdet index)=
      ((integerBasis basis hdet).repr point index : ℝ) := by
  have hinner (column : Fin dimension) :
      inner ℝ (realBasis basis hdet column) (dualRealBasis basis hdet index)=if column=index then 1 else 0 := by
    rw [real_inner_comm]
    exact LinearMap.BilinForm.apply_dualBasis_left inner_nondegenerate (realBasis basis hdet) index column
  calc
    _=inner ℝ (∑ column,((realBasis basis hdet).repr (point : Space (dimension:=dimension)) column) •
        realBasis basis hdet column) (dualRealBasis basis hdet index) := by rw [Module.Basis.sum_repr]
    _=((realBasis basis hdet).repr (point : Space (dimension:=dimension)) index) := by
      rw [sum_inner]
      simp only [real_inner_smul_left,hinner,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _=_ := (Module.Basis.restrictScalars_repr_apply ℤ (realBasis basis hdet) point index).symm

/-- Under quantum Fourier sampling on the dual basis, the frequency
residue is literally the original lattice coefficient residue. -/
theorem primal_secret_eq_public (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (modulus : ℕ) (point : inputLattice basis hdet) :
    secretCoordinates modulus (dual (inputLattice basis hdet)) (dualIntegerBasis basis hdet)
      (primalDoubleDualEquiv basis hdet point)=
      publicCoordinates modulus (inputLattice basis hdet) (integerBasis basis hdet) point := by
  funext index
  change ((pairing (dual (inputLattice basis hdet)) (primalDoubleDualEquiv basis hdet point)
    (dualIntegerBasis basis hdet index) : ℤ) : ZMod modulus)=_
  congr 1
  apply Int.cast_injective (α:=ℝ)
  rw [pairing_spec,primalDoubleDualEquiv_coe,dualIntegerBasis_coe,primal_inner_dual]
  rfl

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeLatticeResidueFiber. -/
section P2MDyadicModule16

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

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeDualInputGaussianFourier. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier

open GaussianPoissonSeries IntegerBasis GaussianProjection.CosetGeometry RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- For the actual dual input lattice, the selected Fourier fiber is a
coset of the original input lattice, with original coefficient residues. -/
theorem primal_gaussian_residue_fiber
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (width : ℝ) (hwidth : 0 < width) (target : Fin dimension → ZMod modulus) :
    (∑' frequency : dual (dual (inputLattice basis hdet)),
      if secretCoordinates modulus (dual (inputLattice basis hdet)) (dualIntegerBasis basis hdet) frequency=target then
        (rho (1/width) (frequency : CoordinateSpace (dimension:=dimension)) : ℂ) else 0)=
      periodizedGaussian (modulusLattice modulus (inputLattice basis hdet)) (1/width)
        (GaussianProjection.CosetGeometry.lift modulus (inputLattice basis hdet) (integerBasis basis hdet) target) := by
  classical
  rw [←(primalDoubleDualEquiv basis hdet).tsum_eq]
  simp_rw [primal_secret_eq_public,primalDoubleDualEquiv_coe]
  have hs : Summable (fun frequency : inputLattice basis hdet =>
      (rho (1/width) (frequency : CoordinateSpace (dimension:=dimension)) : ℂ)) := by
    simpa only [Function.comp_def,primalDoubleDualEquiv_coe] using
      (primalDoubleDualEquiv basis hdet).summable_iff.mpr
        (summable_dual_gaussian (dual (inputLattice basis hdet)) width hwidth)
  rw [tsum_residue_fiber modulus (inputLattice basis hdet) (integerBasis basis hdet) _ hs]
  unfold periodizedGaussian
  apply tsum_congr
  intro point
  change (rho (1/width) ((point : CoordinateSpace (dimension:=dimension))+
    (GaussianProjection.CosetGeometry.lift modulus (inputLattice basis hdet) (integerBasis basis hdet) target : CoordinateSpace (dimension:=dimension))) : ℂ)=_
  rw [add_comm]

/-- The exact DGS Fourier identity in the direction actually used by
Regev: dual-grid amplitudes become original-lattice coset amplitudes. -/
theorem dual_input_periodized_gaussian_transform
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (width : ℝ) (hwidth : 0 < width) (target : Fin dimension → ZMod modulus) :
    transform (fun color => periodizedGaussian (dual (inputLattice basis hdet)) width
      (gridPoint modulus (dual (inputLattice basis hdet)) (dualIntegerBasis basis hdet) color)) target=
      (ZLattice.covolume (dual (inputLattice basis hdet)) : ℂ)⁻¹*
        ((modulus : ℂ)^dimension*((width : ℂ)^dimension*
          periodizedGaussian (modulusLattice modulus (inputLattice basis hdet)) (1/width)
            (GaussianProjection.CosetGeometry.lift modulus (inputLattice basis hdet) (integerBasis basis hdet) target))) := by
  rw [periodized_gaussian_transform (dual (inputLattice basis hdet)) (dualIntegerBasis basis hdet) width hwidth]
  congr 2
  rw [←primal_gaussian_residue_fiber basis hdet width hwidth target,←tsum_mul_left]
  apply tsum_congr
  intro frequency
  split_ifs <;> simp

end

end InfoLossLAR.WorstCase.FiniteLatticeFourier

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeLatticeResidueFiberReal. -/
section P2MDyadicModule18

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

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeFineGridGaussian. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- The true Euclidean point on the fine input lattice L/modulus. -/
def fineGridPoint (point : Space (dimension:=dimension)) : Space (dimension:=dimension) :=
  (modulus : ℝ)⁻¹ • point

def fineGridWeight (width : ℝ) (point : Space (dimension:=dimension)) : ℝ :=
  rho width (fineGridPoint (modulus:=modulus) point)

theorem fineGridWeight_eq_rho (width : ℝ) (hwidth : 0<width) (point : Space (dimension:=dimension)) :
    fineGridWeight (modulus:=modulus) width point=rho ((modulus : ℝ)*width) point := by
  exact rho_dilation_inverse (modulus : ℝ) width (by exact_mod_cast NeZero.pos modulus) hwidth point

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

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeCoherentProjection. -/
section P2MDyadicModule20

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentProjection

open scoped BigOperators

theorem normalized_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : v≠0) : ‖normalized v‖=1 := by
  rw [normalized,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

end InfoLossLAR.WorstCase.CoherentProjection

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeGaussianPureComparison. -/
section P2MDyadicModule21

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open CoherentProjection

noncomputable section

theorem normalized_smul_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (scalar : ℝ) (hscalar : 0<scalar) (value : E) : normalized (scalar • value)=normalized value := by
  rw [normalized,normalized,norm_smul,Real.norm_eq_abs,abs_of_pos hscalar,smul_smul,mul_inv_rev,
    mul_assoc,inv_mul_cancel₀ hscalar.ne',mul_one]

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeFiniteGaussianStates. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- Exact quotient amplitudes are the actual complex lattice-periodized
Gaussian series already used by the finite Fourier identity. -/
theorem periodizedState_apply (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width : ℝ) (color : Fin dimension → ZMod modulus) :
    periodizedState (modulus:=modulus) lattice basis width color=
      periodizedGaussian lattice width (FiniteLatticeFourier.gridPoint modulus lattice basis color) :=
  (periodized_eq_rhoCoset lattice width _).symm

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeDualInputFourierState. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier

open GaussianPoissonSeries IntegerBasis GaussianProjection.CosetGeometry RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- Complete finite-register Fourier amplitude vector, before its global
physical cardinal normalization. -/
def transformState (state : EuclideanSpace ℂ (Fin dimension → ZMod modulus)) :
    EuclideanSpace ℂ (Fin dimension → ZMod modulus) :=
  WithLp.toLp 2 (transform state)

/-- The apparent modulus-original-lattice coset is exactly the fine-grid
periodization at the reciprocal Fourier width. -/
theorem primal_coset_reciprocal_width
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (width : ℝ) (hwidth : 0 < width) (target : Fin dimension → ZMod modulus) :
    periodizedGaussian (modulusLattice modulus (inputLattice basis hdet)) (1/width)
      (GaussianProjection.CosetGeometry.lift modulus (inputLattice basis hdet) (integerBasis basis hdet) target)=
      periodizedState (modulus:=modulus) (inputLattice basis hdet) (integerBasis basis hdet)
        (1/((modulus : ℝ)*width)) target := by
  have hmodulus : (0 : ℝ) < modulus := by exact_mod_cast NeZero.pos modulus
  rw [periodized_eq_rhoCoset]
  change (rhoCoset (1/width) (modulusLattice modulus (inputLattice basis hdet))
    (GaussianProjection.CosetGeometry.lift modulus (inputLattice basis hdet) (integerBasis basis hdet) target) : ℂ)=_
  have hshift : (GaussianProjection.CosetGeometry.lift modulus (inputLattice basis hdet)
      (integerBasis basis hdet) target : CoordinateSpace (dimension:=dimension))=
      (modulus : ℝ) • gridPoint modulus (inputLattice basis hdet) (integerBasis basis hdet) target := by
    rw [gridPoint,smul_smul,mul_inv_cancel₀ hmodulus.ne',one_smul]
  have hscale := rhoCoset_dilation_scale (inputLattice basis hdet) (modulus : ℝ)
    (1/((modulus : ℝ)*width)) hmodulus (by positivity)
    (gridPoint modulus (inputLattice basis hdet) (integerBasis basis hdet) target)
  have hw : (modulus : ℝ)*(1/((modulus : ℝ)*width))=1/width := by field_simp
  rw [hw,←hshift] at hscale
  exact congrArg (fun value : ℝ => (value : ℂ)) hscale

/-- Exact full finite-register Gaussian Fourier image in the actual DGS
direction, with a strictly positive scalar that disappears on normalization. -/
theorem dual_input_transformState
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (width : ℝ) (hwidth : 0 < width) :
    transformState (periodizedState (modulus:=modulus) (dual (inputLattice basis hdet))
      (dualIntegerBasis basis hdet) width)=
      ((ZLattice.covolume (dual (inputLattice basis hdet)))⁻¹*
        (modulus : ℝ)^dimension*width^dimension) •
      periodizedState (modulus:=modulus) (inputLattice basis hdet) (integerBasis basis hdet)
        (1/((modulus : ℝ)*width)) := by
  ext target
  change transform _ target=_
  have hinput : (periodizedState (modulus:=modulus) (dual (inputLattice basis hdet)) (dualIntegerBasis basis hdet) width).ofLp=
      (fun color => periodizedGaussian (dual (inputLattice basis hdet)) width
        (gridPoint modulus (dual (inputLattice basis hdet)) (dualIntegerBasis basis hdet) color)) := by
    funext color
    exact periodizedState_apply _ _ _ _
  rw [hinput,dual_input_periodized_gaussian_transform basis hdet width hwidth,
    primal_coset_reciprocal_width basis hdet width hwidth]
  simp only [PiLp.smul_apply,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

/-- The exact normalized Gaussian Fourier output is the normalized
original-grid Gaussian at reciprocal width. -/
theorem dual_input_normalized_transformState
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (width : ℝ) (hwidth : 0 < width) :
    CoherentProjection.normalized (transformState (periodizedState (modulus:=modulus)
      (dual (inputLattice basis hdet)) (dualIntegerBasis basis hdet) width))=
      CoherentProjection.normalized (periodizedState (modulus:=modulus)
        (inputLattice basis hdet) (integerBasis basis hdet) (1/((modulus : ℝ)*width))) := by
  rw [dual_input_transformState basis hdet width hwidth]
  apply normalized_smul_pos
  exact mul_pos (mul_pos (inv_pos.mpr (ZLattice.covolume_pos _ MeasureTheory.volume))
    (pow_pos (by exact_mod_cast NeZero.pos modulus) dimension)) (pow_pos hwidth dimension)

end

end InfoLossLAR.WorstCase.FiniteLatticeFourier

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeHybrid. -/
section P2MDyadicModule24

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentDecoder

open scoped BigOperators

/-- Sequential isometric evolution, including the complete retained workspace. -/
def evolve {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (step : ℕ → E →ₗᵢ[ℂ] E) : ℕ → E → E
  | 0, state => state
  | count+1, state => step count (evolve step count state)

end InfoLossLAR.WorstCase.CoherentDecoder

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeHybridMeasurement. -/
section P2MDyadicModule25

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

end P2MDyadicModule25

/- Helper module Fiber. -/
section P2MDyadicModule26

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout

open InfoLossLAR.WorstCase

open GaussianPoissonSeries CoherentDecoder CoherentProjection

theorem norm_event {F : Type*} [Fintype F] (v : EuclideanSpace ℂ F) (E : F → Prop) :
    bornEvent E (normalized v) = (∑ c, if E c then ‖v c‖^2 else 0) / ‖v‖^2 := by
  unfold bornEvent
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : E c
  · simp only [h, if_true]
    change ‖(‖v‖⁻¹ : ℝ) • v c‖^2 = _
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg v),mul_pow,inv_pow]
    ring
  · simp [h]

end GridReadout

end P2MDyadicModule26

/- Helper module FourierReadout. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout

open InfoLossLAR.WorstCase GaussianPoissonSeries IntegerBasis RegevLWE.GaussConv

open CoherentDecoder CoherentProjection FiniteLatticeFourier

noncomputable section

variable {n M : ℕ} [NeZero M]

def idealOutput (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) :
    EuclideanSpace ℂ (Fin n → ZMod M) :=
  normalized (transformState (periodizedState (modulus:=M) (dual (inputLattice B hB))
    (dualIntegerBasis B hB) (1 / (Real.sqrt 2 * r))))

theorem normalized_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : ‖normalized v‖ ≤ 1 := by
  by_cases hv : v=0
  · simp [hv,normalized]
  · exact (normalized_norm _ hv).le

end

end GridReadout

end P2MDyadicModule27

/- Helper module PublicBound. -/
section P2MDyadicModule28

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout

open InfoLossLAR.WorstCase GaussianPoissonSeries IntegerBasis RegevLWE.GaussConv RegevSearch

open CoherentDecoder CoherentProjection FiniteLatticeFourier

noncomputable section

variable {n M : ℕ} [NeZero M]

theorem reference_eq (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) (hr : 0<r)
    (T : Finset (Fin n → ℤ)) :
    bornEvent (fun c : Fin n → ZMod M => (fun i => (c i).valMinAbs) ∈ T) (idealOutput B hB r) =
      fourierEvent B r M T := by
  unfold idealOutput
  rw [dual_input_normalized_transformState B hB _ (by positivity)]
  let w : ℝ := 1 / ((M:ℝ)*(1/(Real.sqrt 2*r)))
  have hM : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hw : 0<w := by dsimp [w]; positivity
  have hwidth : (M:ℝ)*w=Real.sqrt 2*r := by dsimp [w]; field_simp
  let e := (integerBasis B hB).equivFun.symm.toEquiv
  have hpoint (c : Fin n → ZMod M) :
      ‖periodizedState (inputLattice B hB) (integerBasis B hB) w c‖^2 = (gridFiberAmplitude B r M c)^2 := by
    change ‖(rhoCoset w (inputLattice B hB) (gridPoint M (inputLattice B hB) (integerBasis B hB) c) : ℂ)‖^2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,←fineGrid_fiberMass _ _ _ hw]
    congr 1
    unfold fiberMass gridFiberAmplitude
    rw [←e.tsum_eq (fun x : inputLattice B hB => if GaussianProjection.CosetGeometry.publicCoordinates M (inputLattice B hB) (integerBasis B hB) x = c then
      fineGridWeight (modulus:=M) w (x:EuclideanSpace ℝ (Fin n)) else 0)]
    apply tsum_congr
    intro z
    have hcoords := publicCoordinates_coefficient_point M B hB z
    change GaussianProjection.CosetGeometry.publicCoordinates M _ _ (e z) = _ at hcoords
    rw [hcoords,fineGridWeight_eq_rho w hw,hwidth]
    change (if _ then rho _ ((integerBasis B hB).equivFun.symm z : EuclideanSpace ℝ (Fin n)) else 0) = _
    rw [coefficient_point]
    split_ifs <;> rfl
  rw [norm_event, EuclideanSpace.norm_sq_eq]
  unfold fourierEvent
  simp_rw [show 1 / ((M:ℝ)*(1/(Real.sqrt 2*r))) = w by rfl, hpoint]

end

end GridReadout

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeFiniteGateTransport. -/
section P2MDyadicModule29

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

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeFiniteGateAlphabet. -/
section P2MDyadicModule30

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

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

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeFiniteGateNativeAlgebra. -/
section P2MDyadicModule31

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

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

theorem leRational_correct (x : RealPair) (bound : ℚ) :
    leRational x bound=true ↔ evalReal x≤bound := by
  rw [leRational,nonnegReal_correct,evalReal_sub]
  simp only [evalReal,Rat.cast_zero,zero_mul,add_zero]
  constructor <;> intro h <;> linarith

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeControlledPhase. -/
section P2MDyadicModule32

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

theorem controlledPhase_angle {n : ℕ} (angle : ℝ)
    (i j : Fin n) (hij : i≠j) (ψ : QState n) :
    cnotState i j hij (apply1 (phaseMatrix (phaseValue angle)⁻¹) j
      (cnotState i j hij (apply1 (phaseMatrix (phaseValue angle)) j
        (apply1 (phaseMatrix (phaseValue angle)) i ψ))))=
      controlledPhase (phaseValue (2*angle)) i j ψ := by
  have hz : phaseValue angle≠0 := Complex.exp_ne_zero _
  simpa only [phaseValue_sq] using controlledPhase_decomposition (phaseValue angle) hz i j hij ψ

noncomputable def pullQFTState {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ) : QState n := fun bits => ψ (finBits bits)

theorem qft_twoBit_phase {n : ℕ} (d : ℕ) (i j : Fin n)
    (ψ : (Fin n → Fin 2) → ℂ) (bits : Fin n → Fin 2) :
    ShorAlgorithms.QFT.applyTwoBit (ShorAlgorithms.QFT.Smat d) i j ψ bits=
      ψ bits*(if bits i=1 ∧ bits j=1 then phaseValue (Real.pi/2^d) else 1) := by
  classical
  simp only [ShorAlgorithms.QFT.applyTwoBit,ShorAlgorithms.QFT.Smat,
    Matrix.diagonal_apply,Prod.mk.injEq,ite_and,mul_ite,mul_zero,Finset.sum_ite_eq,
    Finset.mem_univ,if_true,Function.update_eq_self,phaseValue]
  simp [Finset.sum_ite_irrel]

theorem pullQFT_S {n : ℕ} (i j : Fin n) (ψ : (Fin n → Fin 2) → ℂ) :
    pullQFTState (ShorAlgorithms.QFT.applyGate (.S i j) ψ)=
      controlledPhase (phaseValue (Real.pi/2^(j.val-i.val))) i j (pullQFTState ψ) := by
  funext bits
  rw [pullQFTState,ShorAlgorithms.QFT.applyGate,qft_twoBit_phase]
  simp only [controlledPhase,pullQFTState,finBits]
  by_cases hi : bits i=true <;> by_cases hj : bits j=true <;> simp [hi,hj,Bool.and_eq_true,mul_comm]

/-- The imported exact QFT controlled phase now has an explicit three-phase,
two-CNOT decomposition under the Boolean state convention used by the target
machine model. -/
theorem pullQFT_S_decomposition {n : ℕ} (i j : Fin n) (hij : i≠j)
    (ψ : (Fin n → Fin 2) → ℂ) :
    pullQFTState (ShorAlgorithms.QFT.applyGate (.S i j) ψ)=
      cnotState i j hij (apply1 (phaseMatrix (phaseValue (Real.pi/2^(j.val-i.val)/2))⁻¹) j
        (cnotState i j hij (apply1 (phaseMatrix (phaseValue (Real.pi/2^(j.val-i.val)/2))) j
          (apply1 (phaseMatrix (phaseValue (Real.pi/2^(j.val-i.val)/2))) i (pullQFTState ψ))))) := by
  rw [pullQFT_S,controlledPhase_angle]
  congr 1
  congr 1
  ring

theorem finBits_update {n : ℕ} (bits : Bits n) (i : Fin n) (value : Bool) :
    finBits (Function.update bits i value)=Function.update (finBits bits) i (if value then 1 else 0) := by
  funext j
  by_cases hji : j=i
  · subst j;simp [finBits]
  · simp [finBits,Function.update_of_ne hji]

theorem pullQFT_R {n : ℕ} (i : Fin n) (ψ : (Fin n → Fin 2) → ℂ) :
    pullQFTState (ShorAlgorithms.QFT.applyGate (.R i) ψ)=
      apply1 hMat i (pullQFTState ψ) := by
  funext bits
  simp only [pullQFTState,ShorAlgorithms.QFT.applyGate,ShorAlgorithms.QFT.applyOneBit,
    Fin.sum_univ_two,apply1,Fintype.sum_bool,finBits_update]
  by_cases hi : bits i=true
  · simp [ShorAlgorithms.QFT.Rmat,hMat,finBits,hi,Complex.ofReal_inv,mul_comm,add_comm]
  · have hf : bits i=false := Bool.eq_false_iff.mpr hi
    simp [ShorAlgorithms.QFT.Rmat,hMat,finBits,hf,Complex.ofReal_inv,mul_comm,add_comm]

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgePhaseTaylor. -/
section P2MDyadicModule33

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

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeNativePhaseTaylor. -/
section P2MDyadicModule34

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

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeQFTPhaseCircuit. -/
section P2MDyadicModule35

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity

/-- A semantic intermediate circuit. Phase angles are not executable real
inputs; the later finite-gate compiler must produce rational approximants. -/
inductive PhaseInstruction (n : ℕ) where
  | h (i : Fin n)
  | phase (angle : ℝ) (i : Fin n)
  | cnot (i j : Fin n) (hij : i≠j)

noncomputable def PhaseInstruction.apply {n : ℕ} : PhaseInstruction n → QState n → QState n
  | .h i => apply1 hMat i
  | .phase angle i => apply1 (phaseMatrix (phaseValue angle)) i
  | .cnot i j hij => cnotState i j hij

noncomputable def runPhases {n : ℕ} (circuit : List (PhaseInstruction n)) (ψ : QState n) : QState n :=
  circuit.foldl (fun state gate => gate.apply state) ψ

noncomputable def qftGatePhases {n : ℕ} : ShorAlgorithms.QFT.Gate n → List (PhaseInstruction n)
  | .R i => [.h i]
  | .S i j =>
    let angle := Real.pi/2^(j.val-i.val)
    if hij : i=j then [.phase angle i] else
      [.phase (angle/2) i,.phase (angle/2) j,.cnot i j hij,.phase (-angle/2) j,.cnot i j hij]

theorem phaseValue_neg (angle : ℝ) : phaseValue (-angle)=(phaseValue angle)⁻¹ := by
  simp only [phaseValue,Complex.ofReal_neg,neg_mul,Complex.exp_neg]

theorem qftGatePhases_semantics {n : ℕ} (gate : ShorAlgorithms.QFT.Gate n)
    (ψ : (Fin n → Fin 2) → ℂ) :
    runPhases (qftGatePhases gate) (pullQFTState ψ)=pullQFTState (ShorAlgorithms.QFT.applyGate gate ψ) := by
  cases gate with
  | R i => simpa only [qftGatePhases,runPhases,List.foldl_cons,List.foldl_nil,PhaseInstruction.apply]
      using (pullQFT_R i ψ).symm
  | S i j =>
    by_cases hij : i=j
    · subst j
      funext bits
      simp [qftGatePhases,runPhases,PhaseInstruction.apply,pullQFT_S,phaseMatrix_apply,controlledPhase]
    · simp only [qftGatePhases,dif_neg hij,runPhases,List.foldl_cons,List.foldl_nil,PhaseInstruction.apply]
      rw [neg_div,phaseValue_neg]
      exact (pullQFT_S_decomposition i j hij ψ).symm

noncomputable def qftPhases (n : ℕ) : List (PhaseInstruction n) :=
  (ShorAlgorithms.QFT.qftGates n).flatMap qftGatePhases

theorem qftPhases_semantics (n : ℕ) (ψ : (Fin n → Fin 2) → ℂ) :
    runPhases (qftPhases n) (pullQFTState ψ)=
      pullQFTState (ShorAlgorithms.QFT.runCircuit (ShorAlgorithms.QFT.qftGates n) ψ) := by
  have h (gates : List (ShorAlgorithms.QFT.Gate n)) (state : (Fin n → Fin 2) → ℂ) :
      runPhases (gates.flatMap qftGatePhases) (pullQFTState state)=
        pullQFTState (ShorAlgorithms.QFT.runCircuit gates state) := by
    induction gates generalizing state with
    | nil => rfl
    | cons gate rest ih =>
      simp only [List.flatMap_cons,runPhases,List.foldl_append]
      rw [show List.foldl (fun state gate => PhaseInstruction.apply gate state) (pullQFTState state)
        (qftGatePhases gate)=pullQFTState (ShorAlgorithms.QFT.applyGate gate state)
        from qftGatePhases_semantics gate state]
      exact ih _
  exact h _ _

theorem qftGatePhases_length {n : ℕ} (gate : ShorAlgorithms.QFT.Gate n) :
    (qftGatePhases gate).length≤5 := by
  cases gate with
  | R i => norm_num [qftGatePhases]
  | S i j => simp only [qftGatePhases];split <;> norm_num

private theorem flatMap_length_bound {α β : Type*} (items : List α) (f : α → List β)
    (bound : ℕ) (h : ∀ item∈items,(f item).length≤bound) :
    (items.flatMap f).length≤bound*items.length := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have hh := h item (by simp)
    have ht := ih (by intro item hi;exact h item (by simp [hi]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem qftPhases_length (n : ℕ) : (qftPhases n).length≤5*(n*(n+1)) := by
  have hbase : (ShorAlgorithms.QFT.qftGates n).length≤(n+1)*n := by
    unfold ShorAlgorithms.QFT.qftGates
    have h := flatMap_length_bound (List.finRange n).reverse
      (fun j => (((List.finRange n).reverse.filter fun k => decide (j<k)).map
        (fun k => ShorAlgorithms.QFT.Gate.S j k))++[ShorAlgorithms.QFT.Gate.R j]) (n+1) (by
          intro j _
          have hf := List.length_filter_le (fun k : Fin n => decide (j<k)) (List.finRange n).reverse
          simp only [List.length_reverse,List.length_finRange] at hf
          simp only [List.length_append,List.length_map,List.length_singleton]
          omega)
    simpa only [List.length_reverse,List.length_finRange] using h
  have h := flatMap_length_bound (ShorAlgorithms.QFT.qftGates n) qftGatePhases 5
    (by intro gate _;exact qftGatePhases_length gate)
  exact h.trans (Nat.mul_le_mul_left 5 (by simpa only [Nat.mul_comm] using hbase))

/-- The complete intermediate circuit has the imported Fourier amplitudes,
including the explicit bit reversal of the output register. -/
theorem qftPhases_basis (n : ℕ) (input : Fin n → Fin 2) (output : Bits n) :
    runPhases (qftPhases n) (pullQFTState (ShorAlgorithms.QFT.basisState input)) output=
      ((Real.sqrt (2^n) : ℝ) : ℂ)⁻¹ *
        Complex.exp (2*Real.pi*Complex.I*(ShorAlgorithms.QFT.bitsVal input : ℂ)*
          (ShorAlgorithms.QFT.bitsVal (ShorAlgorithms.QFT.bitRev (finBits output)) : ℂ)/2^n) := by
  rw [qftPhases_semantics,ShorAlgorithms.QFT.qft_circuit_eq]
  rfl

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeNativeQFTPlanSemantics. -/
section P2MDyadicModule36

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.NativeQFTPlan

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

/-- Proof-side semantic decoding of a finite native request. Invalid tags,
addresses or CNOT coincidences are rejected; actual plans never reject. -/
noncomputable def decode (n : ℕ) (code : Instruction) : Option (PhaseInstruction n) :=
  if code.1=0 then
    if hi : code.2.1<n then some (.h ⟨code.2.1,hi⟩) else none
  else if code.1=1 then
    if hi : code.2.1<n then some (.phase (NativePhaseTaylor.targetAngle code.2.2.2) ⟨code.2.1,hi⟩) else none
  else if code.1=2 then
    if hi : code.2.1<n then
      if hj : code.2.2.1<n then
        if hne : code.2.1≠code.2.2.1 then
          some (.cnot ⟨code.2.1,hi⟩ ⟨code.2.2.1,hj⟩
            (by intro he;exact hne (congrArg Fin.val he)))
        else none
      else none
    else none
  else none

@[simp] theorem decode_h {n : ℕ} (i : Fin n) : decode n (hCode i.val)=some (.h i) := by
  simp [decode,hCode,i.isLt]

@[simp] theorem decode_phase {n : ℕ} (i : Fin n) (r : NativePhaseTaylor.QFTRequest) :
    decode n (phaseCode i.val r)=some (.phase (NativePhaseTaylor.targetAngle r) i) := by
  simp [decode,phaseCode,i.isLt]

@[simp] theorem decode_cnot {n : ℕ} (i j : Fin n) (hne : i≠j) :
    decode n (cnotCode i.val j.val)=some (.cnot i j hne) := by
  have hv : i.val≠j.val := fun he => hne (Fin.ext he)
  simp [decode,cnotCode,i.isLt,j.isLt,hv]

def gatePlan (input : Input) {n : ℕ} : ShorAlgorithms.QFT.Gate n → List Instruction
  | .R i => [hCode i.val]
  | .S i j => interaction (input,(i.val,j.val))

theorem request_target_positive (input : Input) (i j : Fin input.1.length) :
    NativePhaseTaylor.targetAngle (request input (j.val-i.val) false)=
      (Real.pi/(2:ℝ)^(j.val-i.val))/2 := by
  have hg : j.val-i.val ≤ input.1.length := (Nat.sub_le _ _).trans j.isLt.le
  simp only [NativePhaseTaylor.targetAngle,request,List.length_take,Nat.min_eq_left hg,Bool.false_eq_true,if_false]
  rw [pow_succ,div_mul_eq_div_div]

theorem request_target_negative (input : Input) (i j : Fin input.1.length) :
    NativePhaseTaylor.targetAngle (request input (j.val-i.val) true)=
      -(Real.pi/(2:ℝ)^(j.val-i.val))/2 := by
  have hg : j.val-i.val ≤ input.1.length := (Nat.sub_le _ _).trans j.isLt.le
  simp only [NativePhaseTaylor.targetAngle,request,List.length_take,Nat.min_eq_left hg,if_true]
  rw [pow_succ,div_mul_eq_div_div,neg_div]

/-- Every five-item native interaction has exactly the established controlled
phase decomposition. The subtraction and unary take are proved untruncated. -/
theorem interaction_decode (input : Input) (i j : Fin input.1.length) (hlt : i<j) :
    (interaction (input,(i.val,j.val))).filterMap (decode input.1.length)=
      qftGatePhases (ShorAlgorithms.QFT.Gate.S i j) := by
  have hne : i≠j := ne_of_lt hlt
  simp only [interaction,List.filterMap_cons,List.filterMap_nil,
    decode_phase,decode_cnot i j hne,request_target_positive,request_target_negative,
    qftGatePhases,dif_neg hne]

theorem range_eq_finRange (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

theorem indices_eq (input : Input) :
    indices input=(List.finRange input.1.length).reverse.map Fin.val := by
  simp only [indices,List.map_reverse,←range_eq_finRange]

/-- The executable Nat schedule is the original Shor gate schedule with each
gate replaced by its finite request list, in exactly the same order. -/
theorem current_reference (input : Input) :
    current input=(ShorAlgorithms.QFT.qftGates input.1.length).flatMap (gatePlan input) := by
  unfold current
  rw [indices_eq,List.flatMap_map]
  unfold ShorAlgorithms.QFT.qftGates
  rw [List.flatMap_assoc]
  apply congrArg (fun f : Fin input.1.length → List Instruction =>
    (List.finRange input.1.length).reverse.flatMap f)
  funext i
  simp only [rowPlan,indices_eq,List.filter_map,List.flatMap_map,List.flatMap_append,
    List.flatMap_singleton,gatePlan,Function.comp_apply]
  rfl

def gateValid {n : ℕ} : ShorAlgorithms.QFT.Gate n → Prop
  | .R _ => True
  | .S i j => i<j

/-- Every controlled phase actually occurring in Shor's schedule has its
strictly increasing wire pair, as required by the native five-item plan. -/
theorem shor_gate_valid {n : ℕ} (gate : ShorAlgorithms.QFT.Gate n)
    (hgate : gate∈ShorAlgorithms.QFT.qftGates n) :
    gateValid gate := by
  cases gate with
  | R i => trivial
  | S i j =>
    simp only [ShorAlgorithms.QFT.qftGates,List.mem_flatMap,List.mem_append,
      List.mem_map,List.mem_singleton,List.mem_filter,decide_eq_true_eq] at hgate
    obtain ⟨row,hrow,hgate⟩ := hgate
    rcases hgate with hgate | hgate
    · obtain ⟨column,⟨hcolumn,hlt⟩,he⟩ := hgate
      obtain ⟨rfl,rfl⟩ := ShorAlgorithms.QFT.Gate.S.inj he
      exact hlt
    · cases hgate

theorem current_semantics (input : Input) :
    (current input).filterMap (decode input.1.length)=qftPhases input.1.length := by
  have hsem (gates : List (ShorAlgorithms.QFT.Gate input.1.length)) :
      (∀ gate∈gates,gateValid gate) →
      (gates.flatMap (gatePlan input)).filterMap (decode input.1.length)=gates.flatMap qftGatePhases := by
    induction gates with
    | nil => intro _;rfl
    | cons gate rest ih =>
      intro hv
      simp only [List.flatMap_cons,List.filterMap_append]
      rw [ih (by intro g hg;exact hv g (by simp [hg]))]
      congr 1
      cases gate with
      | R i => simp [gatePlan,qftGatePhases]
      | S i j => exact interaction_decode input i j (hv (.S i j) (by simp))
  rw [current_reference]
  exact hsem _ (fun gate hg => shor_gate_valid gate hg)

end InfoLossLAR.WorstCase.NativeQFTPlan

end

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeNativeQFTPlanValid. -/
section P2MDyadicModule37

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.NativeQFTPlan

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

theorem gatePlan_decode (input : Input) (gate : ShorAlgorithms.QFT.Gate input.1.length)
    (hv : gateValid gate) :
    (gatePlan input gate).filterMap (decode input.1.length)=qftGatePhases gate := by
  cases gate with
  | R i => simp [gatePlan,qftGatePhases]
  | S i j => exact interaction_decode input i j hv

theorem gatePlan_length (input : Input) (gate : ShorAlgorithms.QFT.Gate input.1.length)
    (hv : gateValid gate) : (gatePlan input gate).length=(qftGatePhases gate).length := by
  cases gate with
  | R i => simp [gatePlan,qftGatePhases]
  | S i j =>
    have hne : i≠j := ne_of_lt hv
    simp [gatePlan,interaction,qftGatePhases,hne]

/-- No valid gate plan loses an instruction during semantic decoding. -/
theorem gatePlan_decode_some (input : Input) (gate : ShorAlgorithms.QFT.Gate input.1.length)
    (hv : gateValid gate) (code : Instruction) (hc : code∈gatePlan input gate) :
    ∃ instruction,decode input.1.length code=some instruction := by
  have hlen : ((gatePlan input gate).filterMap (decode input.1.length)).length=(gatePlan input gate).length :=
    (congrArg List.length (gatePlan_decode input gate hv)).trans (gatePlan_length input gate hv).symm
  cases he : decode input.1.length code with
  | none =>
    have hh := List.length_filterMap_lt_length_iff_exists.mpr ⟨code,hc,he⟩
    omega
  | some instruction => exact ⟨instruction,rfl⟩

/-- Every emitted request has a valid tag and wire address, and every CNOT
has distinct wires. In particular filterMap never silently removes a request. -/
theorem current_decode_some (input : Input) (code : Instruction) (hc : code∈current input) :
    ∃ instruction,decode input.1.length code=some instruction := by
  rw [current_reference] at hc
  obtain ⟨gate,hgate,hc⟩ := List.mem_flatMap.mp hc
  exact gatePlan_decode_some input gate (shor_gate_valid gate hgate) code hc

private theorem filterMap_length_of_some {A B : Type} (f : A → Option B) (items : List A)
    (hs : ∀ item∈items,∃ output,f item=some output) : (items.filterMap f).length=items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨output,he⟩ := hs item (by simp)
    simp only [List.filterMap_cons,he,List.length_cons]
    exact congrArg Nat.succ (ih (fun a ha => hs a (by simp [ha])))

theorem current_length_eq (input : Input) : (current input).length=(qftPhases input.1.length).length := by
  have hl := filterMap_length_of_some (decode input.1.length) (current input) (current_decode_some input)
  have he := congrArg List.length (current_semantics input)
  exact hl.symm.trans he

theorem current_length (input : Input) :
    (current input).length ≤ 5*(input.1.length*(input.1.length+1)) := by
  rw [current_length_eq]
  exact qftPhases_length _

end InfoLossLAR.WorstCase.NativeQFTPlan

end

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeFiniteGateNativeCoefficients. -/
section P2MDyadicModule38

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

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeFiniteGateNativeMatrix. -/
section P2MDyadicModule39

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

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

theorem sumAt_eval (indices : List Bits) (f : Bits→Scalar) :
    eval (sumAt indices f)=(indices.map (fun i => eval (f i))).sum := by
  induction indices with
  | nil => simp [sumAt]
  | cons i rest ih => simpa [sumAt,List.foldr_cons,eval_add] using congrArg (fun z => eval (f i)+z) ih

noncomputable def evalMatrix (m : NativeMatrix) : Matrix Bits Bits ℂ := fun r c => eval (m r c)

theorem eval_matrixMul (first second : NativeMatrix) :
    evalMatrix (matrixMul first second)=evalMatrix first*evalMatrix second := by
  funext r c
  simp only [evalMatrix,matrixMul,sumAt_eval,eval_mul]
  rw [←List.sum_toFinset _ basis_nodup,basis_toFinset]
  rfl

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeFiniteGateNativeEnumeration. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

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

theorem searchSlots_length (a : ℕ) (budget : List Unit) :
    (searchSlots a budget).length=13^(a+1)*(budget.length+1)^(4*a) := by
  simp [searchSlots]

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

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeFiniteGateNativeGates. -/
section P2MDyadicModule41

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

theorem nativeGate_eq (code : ℕ) :
    nativeGate code=letterNative (FiniteGateNativeEnumeration.letterOfCode code) := by
  unfold nativeGate gateTable FiniteGateNativeEnumeration.letterOfCode
  rw [List.getElem?_map]
  cases alphabet[code]? <;> rfl

theorem eval_nativeGate (code : ℕ) :
    evalMatrix (nativeGate code)=
      QAlgorithms.embedOp (FiniteGateNativeEnumeration.letterOfCode code).toGate.gate.mat
        (FiniteGateNativeEnumeration.letterOfCode code).toGate.wires := by
  rw [nativeGate_eq,eval_letterNative]

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeFiniteGateNativeWord. -/
section P2MDyadicModule42

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

attribute [local irreducible] matrixMul nativeGate maxSteps evalStep

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeFiniteGateNativePredicate. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

section P2MDyadicModule43

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

theorem accepts_correct (first second : NativeMatrix) (tolerance : ℚ) (ht : 0≤tolerance) :
    accepts first second tolerance=true ↔
      QAlgorithms.frobNorm (initializedNative first-initializedNative second)≤tolerance := by
  rw [accepts,leRational_correct,rectangleError_eval,Rat.cast_pow]
  exact sq_le_sq₀ (norm_nonneg _) (by exact_mod_cast ht)

attribute [local irreducible] accepts rectangleError leRational

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeFiniteGateNativeCompiler. -/
section P2MDyadicModule44

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

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeFiniteGateNativeGuarantee. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

section P2MDyadicModule45

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

attribute [local irreducible] compileWord nativeCompile compilerTolerance

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

end P2MDyadicModule45

/- Helper module Solutions.RegevBridgePhaseTarget. -/
section P2MDyadicModule46

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

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeInitializedTarget. -/
section P2MDyadicModule47

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

end P2MDyadicModule47

/- Helper module Solutions.RegevBridgeNativePhaseGates. -/
section P2MDyadicModule48

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

end P2MDyadicModule48

/- Helper module Solutions.RegevBridgeNativeQFTPlanCompile. -/
section P2MDyadicModule49

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeQFTPlan FiniteGateTransport FiniteGateNative

@[simp] theorem compileCode_tag (a : ℕ) (budget : List Unit) (code : NativeQFTPlan.Instruction) :
    (compileCode a (budget,code)).1=code.1 := rfl

@[simp] theorem compileCode_first (a : ℕ) (budget : List Unit) (code : NativeQFTPlan.Instruction) :
    (compileCode a (budget,code)).2.1=code.2.1 := rfl

@[simp] theorem compileCode_second (a : ℕ) (budget : List Unit) (code : NativeQFTPlan.Instruction) :
    (compileCode a (budget,code)).2.2.1=code.2.2.1 := rfl

/-- Automatic local precision changes no ideal phase: only the public
unary gap and sign determine its exact target. -/
theorem automatic_ideal_eq (budget : List Unit) (request : NativePhaseTaylor.QFTRequest) :
    NativePhaseGates.ideal (NativePhaseGates.request (budget,(request.1.2.1,request.2)))=
      NativePhaseGates.ideal request := rfl

/-- One absolute compiler exponent works for every plan and every accuracy
budget. The exact original plan phase is approximated, with all output
ancilla leakage included in the initialized Frobenius error. -/
theorem exists_phase_accuracy :
    ∃ a : ℕ,0<a ∧ ∀ budget : List Unit, ∀ code : NativeQFTPlan.Instruction, code.1=1 →
      (compileCode a (budget,code)).2.2.2∈FiniteGateNativeEnumeration.search a budget ∧
      QAlgorithms.frobNorm
        (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
          (matrix (FiniteGateNativeEnumeration.interpreted (compileCode a (budget,code)).2.2.2))-
          QAlgorithms.Papers.Independent.Renew46.P12.idealMap (NativePhaseGates.ideal code.2.2.2) 2)≤
            5/((budget.length : ℝ)+1) := by
  obtain ⟨a,ha,haccuracy⟩ := NativePhaseGates.exists_automatic_accuracy
  refine ⟨a,ha,?_⟩
  intro budget code hphase
  have he := haccuracy (automaticInput (budget,code))
  simpa only [compileCode,if_pos hphase,automaticInput,automatic_ideal_eq] using he

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeAncillaReuse. -/
section P2MDyadicModule50

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentDecoder

open scoped BigOperators

/-- Exact ideal evolution preserves the data norm at every prefix. -/
theorem evolve_norm {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (step : ℕ → E →ₗᵢ[ℂ] E) (count : ℕ) (state : E) :
    ‖evolve step count state‖=‖state‖ := by
  induction count with
  | zero => rfl
  | succ count ih => rw [evolve,(step count).norm_map,ih]

/-- One fixed ancilla workspace may be reused by every approximate unitary.
The local guarantee is required only on the ideal embedStated subspace. All
actual leakage and correlations remain in F throughout the execution. -/
theorem evolve_reusing_ancilla_error
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (embedState : E →ₗᵢ[ℂ] F) (actual : ℕ → F →ₗᵢ[ℂ] F)
    (ideal : ℕ → E →ₗᵢ[ℂ] E) (error : ℕ → ℝ)
    (hlocal : ∀ index state,‖actual index (embedState state)-embedState (ideal index state)‖≤
      error index*‖state‖) (count : ℕ) (state : E) :
    ‖evolve actual count (embedState state)-embedState (evolve ideal count state)‖≤
      (∑ index∈Finset.range count,error index)*‖state‖ := by
  induction count with
  | zero => simp [evolve]
  | succ count ih =>
    rw [evolve,evolve,Finset.sum_range_succ,add_mul]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (actual count (evolve actual count (embedState state)))
      (actual count (embedState (evolve ideal count state)))
      (embedState (ideal count (evolve ideal count state)))
    have hiso :
        ‖actual count (evolve actual count (embedState state))-
          actual count (embedState (evolve ideal count state))‖=
        ‖evolve actual count (embedState state)-embedState (evolve ideal count state)‖ := by
      rw [←map_sub,(actual count).norm_map]
    rw [hiso] at htri
    have he := hlocal count (evolve ideal count state)
    rw [evolve_norm] at he
    exact htri.trans (add_le_add ih he)

/-- The usual linear circuit-size loss, with the same physical ancillas
reused after every approximate operation. -/
theorem evolve_reusing_ancilla_uniform
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (embedState : E →ₗᵢ[ℂ] F) (actual : ℕ → F →ₗᵢ[ℂ] F)
    (ideal : ℕ → E →ₗᵢ[ℂ] E) (error : ℝ)
    (hlocal : ∀ index state,‖actual index (embedState state)-embedState (ideal index state)‖≤
      error*‖state‖) (count : ℕ) (state : E) :
    ‖evolve actual count (embedState state)-embedState (evolve ideal count state)‖≤
      (count : ℝ)*error*‖state‖ := by
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
    evolve_reusing_ancilla_error embedState actual ideal (fun _ => error) hlocal count state

end InfoLossLAR.WorstCase.CoherentDecoder

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeNativeQFTPlanIsometry. -/
section P2MDyadicModule51

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open scoped BigOperators

noncomputable def phaseInstructionLinearMap {n : ℕ} (instruction : PhaseInstruction n) :
    QState n →ₗ[ℂ] QState n where
  toFun := instruction.apply
  map_add' ψ φ := by
    funext x
    cases instruction <;>
      simp [PhaseInstruction.apply,apply1,cnotState,mul_add,Finset.sum_add_distrib]
  map_smul' z ψ := by
    funext x
    cases instruction <;>
      simp [PhaseInstruction.apply,apply1,cnotState,mul_left_comm,←Finset.mul_sum]

theorem phaseInstruction_mass {n : ℕ} (instruction : PhaseInstruction n) (ψ : QState n) :
    (∑ x : Bits n,Complex.normSq (instruction.apply ψ x))=∑ x : Bits n,Complex.normSq (ψ x) := by
  cases instruction with
  | h i => exact apply1_mass hMat i ψ hMat_mass
  | cnot i j hne => exact cnotState_mass i j hne ψ
  | phase angle i =>
    apply Finset.sum_congr rfl
    intro x _
    simp only [PhaseInstruction.apply,phaseMatrix_apply,Complex.normSq_mul]
    have hphase : Complex.normSq (if x i then phaseValue angle else 1)=1 := by
      cases x i <;> simp [Complex.normSq_eq_norm_sq,phaseValue_norm]
    rw [hphase,one_mul]

theorem phaseInstruction_norm {n : ℕ} (instruction : PhaseInstruction n) (ψ : QState n) :
    ‖(WithLp.toLp 2 (instruction.apply ψ) : EuclideanSpace ℂ (Bits n))‖=
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits n))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  simpa only [Complex.normSq_eq_norm_sq] using phaseInstruction_mass instruction ψ

/-- The exact QFT instruction is a genuine isometry on the entire data
register, including arbitrary entanglement between its wires. -/
noncomputable def phaseInstructionIsometry {n : ℕ} (instruction : PhaseInstruction n) :
    EuclideanSpace ℂ (Bits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bits n) where
  toFun ψ := WithLp.toLp 2 (instruction.apply (WithLp.ofLp ψ))
  map_add' ψ φ := by
    apply WithLp.ofLp_injective
    simpa only [WithLp.ofLp_add,WithLp.ofLp_toLp,phaseInstructionLinearMap,
      LinearMap.coe_mk,AddHom.coe_mk] using
        (phaseInstructionLinearMap instruction).map_add (WithLp.ofLp ψ) (WithLp.ofLp φ)
  map_smul' z ψ := by
    apply WithLp.ofLp_injective
    simpa only [WithLp.ofLp_smul,WithLp.ofLp_toLp,phaseInstructionLinearMap,
      LinearMap.coe_mk,AddHom.coe_mk,RingHom.id_apply] using
        (phaseInstructionLinearMap instruction).map_smul z (WithLp.ofLp ψ)
  norm_map' ψ := by
    change ‖(WithLp.toLp 2 (instruction.apply (WithLp.ofLp ψ)) : EuclideanSpace ℂ (Bits n))‖=‖ψ‖
    simpa only [WithLp.toLp_ofLp] using phaseInstruction_norm instruction (WithLp.ofLp ψ)

@[simp] theorem phaseInstructionIsometry_apply {n : ℕ} (instruction : PhaseInstruction n)
    (ψ : EuclideanSpace ℂ (Bits n)) :
    phaseInstructionIsometry instruction ψ=WithLp.toLp 2 (instruction.apply (WithLp.ofLp ψ)) := rfl

/-- Actual finite native words act isometrically on the full retained register. -/
noncomputable def wordIsometry {n : ℕ} (word : List (Letter n)) :
    EuclideanSpace ℂ (Bits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bits n) :=
  circuitIsometry [instructions word]

@[simp] theorem wordIsometry_apply {n : ℕ} (word : List (Letter n)) (ψ : EuclideanSpace ℂ (Bits n)) :
    wordIsometry word ψ=WithLp.toLp 2 (runLayer (instructions word) (WithLp.ofLp ψ)) := rfl

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeFiniteGateError. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

section P2MDyadicModule52

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

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeFiniteGateEntangledError. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

section P2MDyadicModule53

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

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeWireRelocation. -/
section P2MDyadicModule54

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

end P2MDyadicModule54

/- Helper module Solutions.RegevBridgeInitializedRelocation. -/
section P2MDyadicModule55

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

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeFreshPhaseRelocation. -/
section P2MDyadicModule56

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

end P2MDyadicModule56

/- Helper module Solutions.RegevBridgeNativeQFTPlanRealization. -/
section P2MDyadicModule57

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

/-- The entire data state is retained; exactly two additional wires start at zero. -/
noncomputable def initializeAuxIsometry {n : ℕ} :
    EuclideanSpace ℂ (Bits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bits (n+2)) where
  toFun ψ := WithLp.toLp 2 (initializeAux (WithLp.ofLp ψ))
  map_add' ψ φ := by
    apply WithLp.ofLp_injective
    simpa only [WithLp.ofLp_add,WithLp.ofLp_toLp,initializeAuxLinearMap,
      LinearMap.coe_mk,AddHom.coe_mk] using
        (initializeAuxLinearMap (n:=n)).map_add (WithLp.ofLp ψ) (WithLp.ofLp φ)
  map_smul' z ψ := by
    apply WithLp.ofLp_injective
    simpa only [WithLp.ofLp_smul,WithLp.ofLp_toLp,initializeAuxLinearMap,
      LinearMap.coe_mk,AddHom.coe_mk,RingHom.id_apply] using
        (initializeAuxLinearMap (n:=n)).map_smul z (WithLp.ofLp ψ)
  norm_map' ψ := by
    change ‖(WithLp.toLp 2 (initializeAux (WithLp.ofLp ψ)) : EuclideanSpace ℂ (Bits (n+2)))‖=‖ψ‖
    simpa only [WithLp.toLp_ofLp] using initializeAux_norm (WithLp.ofLp ψ)

@[simp] theorem initializeAuxIsometry_apply {n : ℕ} (ψ : EuclideanSpace ℂ (Bits n)) :
    initializeAuxIsometry ψ=WithLp.toLp 2 (initializeAux (WithLp.ofLp ψ)) := rfl

/-- Equivalent proof-side presentation using the already verified semantic decoder. -/
noncomputable def codeWord (a : ℕ) (budget : List Unit) (n : ℕ) (code : NativeQFTPlan.Instruction) :
    List (Letter (n+2)) :=
  match NativeQFTPlan.decode n code with
  | none => []
  | some (.h i) => [.h (i.castAdd 2)]
  | some (.cnot i j hne) => [.cnot (i.castAdd 2) (j.castAdd 2)
      (by intro h;exact hne (Fin.castAdd_inj.mp h))]
  | some (.phase _ i) =>
      (FiniteGateNativeEnumeration.interpreted (compileCode a (budget,code)).2.2.2).map
        (Letter.relocate (freshPhaseWires i))

/-- Physical realization depends only on the finite compiled block. -/
theorem codeWord_eq_physicalBlock (a : ℕ) (budget : List Unit) (n : ℕ)
    (code : NativeQFTPlan.Instruction) :
    codeWord a budget n code=physicalBlock n (compileCode a (budget,code)) := by
  unfold codeWord physicalBlock NativeQFTPlan.decode
  simp only [compileCode_tag,compileCode_first,compileCode_second]
  split_ifs <;> rfl

noncomputable def idealCode (n : ℕ) (code : NativeQFTPlan.Instruction) :
    EuclideanSpace ℂ (Bits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bits n) :=
  match NativeQFTPlan.decode n code with
  | none => LinearIsometry.id
  | some gate => phaseInstructionIsometry gate

theorem decode_phase_tag {n : ℕ} {code : NativeQFTPlan.Instruction} {angle : ℝ} {i : Fin n}
    (h : NativeQFTPlan.decode n code=some (.phase angle i)) :
    code.1=1 ∧ angle=NativePhaseTaylor.targetAngle code.2.2.2 := by
  unfold NativeQFTPlan.decode at h
  split_ifs at h <;> simp_all

/-- A local initialized-map bound becomes a full-state bound on arbitrary
entangled data. This statement does not reset or discard the two ancillas. -/
theorem code_local_error (a : ℕ) (budget : List Unit) (n : ℕ)
    (haccuracy : ∀ code : NativeQFTPlan.Instruction,code.1=1 →
      frobNorm (QAlgorithms.Papers.Independent.Renew46.P12.initializedMap (n:=1) (w:=2)
        (matrix (FiniteGateNativeEnumeration.interpreted (compileCode a (budget,code)).2.2.2))-
        QAlgorithms.Papers.Independent.Renew46.P12.idealMap (NativePhaseGates.ideal code.2.2.2) 2)≤
          5/((budget.length : ℝ)+1))
    (code : NativeQFTPlan.Instruction) (ψ : EuclideanSpace ℂ (Bits n)) :
    ‖wordIsometry (codeWord a budget n code) (initializeAuxIsometry ψ)-
      initializeAuxIsometry (idealCode n code ψ)‖≤5/((budget.length : ℝ)+1)*‖ψ‖ := by
  have heps : 0≤5/((budget.length : ℝ)+1)*‖ψ‖ := by positivity
  unfold codeWord idealCode
  generalize he : NativeQFTPlan.decode n code=decoded
  cases decoded with
  | none => simpa [wordIsometry_apply,initializeAuxIsometry_apply,instructions,runLayer] using heps
  | some gate =>
    cases gate with
    | h i =>
      simpa [wordIsometry_apply,phaseInstructionIsometry_apply,initializeAuxIsometry_apply,
        instructions,runLayer,Letter.toInstr,Instr.apply,PhaseInstruction.apply,
        initializeAux_apply1] using heps
    | cnot i j hij =>
      simpa [wordIsometry_apply,phaseInstructionIsometry_apply,initializeAuxIsometry_apply,
        instructions,runLayer,Letter.toInstr,Instr.apply,PhaseInstruction.apply,
        initializeAux_cnot] using heps
    | phase angle i =>
      obtain ⟨htag,hangle⟩ := decode_phase_tag he
      have hh := fresh_phase_word_error i
        (FiniteGateNativeEnumeration.interpreted (compileCode a (budget,code)).2.2.2)
        (phaseValue angle) (5/((budget.length : ℝ)+1))
        (by simpa only [hangle,NativePhaseGates.ideal] using haccuracy code htag) (WithLp.ofLp ψ)
      simpa only [wordIsometry_apply,initializeAuxIsometry_apply,phaseInstructionIsometry_apply,
        PhaseInstruction.apply,WithLp.ofLp_toLp,←WithLp.toLp_sub,WithLp.toLp_ofLp] using hh

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end

end P2MDyadicModule57

/- Helper module Solutions.RegevBridgeNativeQFTPlanGlobal. -/
section P2MDyadicModule58

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentDecoder

open scoped BigOperators

theorem physicalWord_codes (a : ℕ) (x : Input) :
    physicalWord a x=(plan x).flatMap (codeWord a x.2 x.1.length) := by
  simp only [physicalWord,current,List.flatMap_map,Function.comp_def]
  apply congrArg (fun f : NativeQFTPlan.Instruction → List (Letter (x.1.length+2)) => (plan x).flatMap f)
  funext code
  exact (codeWord_eq_physicalBlock a x.2 x.1.length code).symm

/-- A generic link between indexed isometric evolution and an ordinary finite
instruction list. Values beyond the list are never evaluated. -/
theorem evolve_list {α E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (codes : List α) (fallback : α) (interpret : α → E →ₗᵢ[ℂ] E) (ψ : E) :
    evolve (fun index => interpret (codes[index]?.getD fallback)) codes.length ψ=
      codes.foldl (fun state code => interpret code state) ψ := by
  have hevolve (count : ℕ) :
      evolve (fun index => interpret (codes[index]?.getD fallback)) count ψ=
        (List.range count).foldl (fun state index => interpret (codes[index]?.getD fallback) state) ψ := by
    induction count with
    | zero => rfl
    | succ count ih => simp only [evolve,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
  rw [hevolve]
  have hcodes : (List.range codes.length).map (fun index => codes[index]?.getD fallback)=codes := by
    apply List.ext_getElem
    · simp
    · intro index hleft hright
      simp only [List.length_map,List.length_range] at hleft
      simp [List.getElem?_eq_getElem,hleft]
  have hf := congrArg (fun list : List α => list.foldl (fun state code => interpret code state) ψ) hcodes
  simpa only [List.foldl_map] using hf

theorem fold_words (a : ℕ) (budget : List Unit) (n : ℕ)
    (codes : List NativeQFTPlan.Instruction) (ψ : EuclideanSpace ℂ (Bits (n+2))) :
    codes.foldl (fun state code => wordIsometry (codeWord a budget n code) state) ψ=
      WithLp.toLp 2 (runLayer (instructions (codes.flatMap (codeWord a budget n))) (WithLp.ofLp ψ)) := by
  induction codes generalizing ψ with
  | nil => simp [runLayer,instructions]
  | cons code rest ih =>
    rw [List.foldl_cons,ih]
    simp only [List.flatMap_cons,instructions,List.map_append,runLayer,List.foldl_append,
      wordIsometry_apply,WithLp.ofLp_toLp]

theorem fold_ideal (n : ℕ) (codes : List NativeQFTPlan.Instruction) (ψ : EuclideanSpace ℂ (Bits n)) :
    codes.foldl (fun state code => idealCode n code state) ψ=
      WithLp.toLp 2 (runPhases (codes.filterMap (NativeQFTPlan.decode n)) (WithLp.ofLp ψ)) := by
  induction codes generalizing ψ with
  | nil => simp [runPhases]
  | cons code rest ih =>
    rw [List.foldl_cons,ih]
    cases he : NativeQFTPlan.decode n code with
    | none => simp [List.filterMap_cons,he,idealCode]
    | some gate => simp [List.filterMap_cons,he,idealCode,phaseInstructionIsometry_apply,runPhases]

/-- One fixed finite-gate compiler exponent approximates the exact QFT on
arbitrary entangled data. The actual execution retains its complete state
and reuses the same two ancillas, including all accumulated leakage. -/
theorem exists_global_accuracy :
    ∃ a : ℕ,0<a ∧ ∀ x : Input,∀ ψ : QState x.1.length,
      ‖(WithLp.toLp 2 (runLayer (instructions (physicalWord a x)) (initializeAux ψ)-
          initializeAux (runPhases (qftPhases x.1.length) ψ)) :
            EuclideanSpace ℂ (Bits (x.1.length+2)))‖≤
        (25*(x.1.length : ℝ)*((x.1.length : ℝ)+1)/((x.2.length : ℝ)+1))*
          ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits x.1.length))‖ := by
  obtain ⟨a,ha,haccuracy⟩ := exists_phase_accuracy
  refine ⟨a,ha,?_⟩
  intro x ψ
  let codes := plan x
  let actual : ℕ → EuclideanSpace ℂ (Bits (x.1.length+2)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits (x.1.length+2)) :=
    fun index => wordIsometry (codeWord a x.2 x.1.length (codes[index]?.getD (NativeQFTPlan.hCode 0)))
  let ideal : ℕ → EuclideanSpace ℂ (Bits x.1.length) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits x.1.length) :=
    fun index => idealCode x.1.length (codes[index]?.getD (NativeQFTPlan.hCode 0))
  have hh := evolve_reusing_ancilla_uniform (initializeAuxIsometry (n:=x.1.length)) actual ideal
    (5/((x.2.length : ℝ)+1))
    (fun index state => code_local_error a x.2 x.1.length
      (fun code hc => (haccuracy x.2 code hc).2) _ state)
    codes.length (WithLp.toLp 2 ψ)
  have haFold := evolve_list codes (NativeQFTPlan.hCode 0)
    (fun code => wordIsometry (codeWord a x.2 x.1.length code))
    (initializeAuxIsometry (WithLp.toLp 2 ψ))
  have hiFold := evolve_list codes (NativeQFTPlan.hCode 0)
    (idealCode x.1.length) (WithLp.toLp 2 ψ)
  change ‖evolve _ _ _-initializeAuxIsometry (evolve _ _ _)‖≤_ at hh
  rw [haFold,hiFold,fold_words,fold_ideal] at hh
  simp only [initializeAuxIsometry_apply,WithLp.ofLp_toLp,←WithLp.toLp_sub] at hh
  have hsemantic : codes.filterMap (NativeQFTPlan.decode x.1.length)=qftPhases x.1.length :=
    NativeQFTPlan.current_semantics (x.1,[],[])
  rw [hsemantic,←physicalWord_codes] at hh
  apply hh.trans
  have hl : (codes.length : ℝ)≤5*((x.1.length : ℝ)*((x.1.length : ℝ)+1)) := by
    exact_mod_cast NativeQFTPlan.current_length (x.1,[],[])
  have heps : 0≤5/((x.2.length : ℝ)+1) := by positivity
  have hprod := mul_le_mul_of_nonneg_right hl heps
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ (5*((x.1.length : ℝ)*((x.1.length : ℝ)+1)))*(5/((x.2.length : ℝ)+1)) := hprod
    _ = _ := by ring

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end

end P2MDyadicModule58

/- Helper module AxisFourier. -/
section P2MDyadicModule59

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

noncomputable section

variable {b : ℕ}

def reverse (b : ℕ) : Equiv.Perm (Bits b) where
  toFun z := fun i => z i.rev
  invFun z := fun i => z i.rev
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp

def frequency (b : ℕ) : Bits b ≃ ZMod (2^b) :=
  ((reverse b).trans (binary b)).trans (Equiv.neg _)

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

theorem char_phase (x y : Bits b) :
    ZMod.stdAddChar (binary b x * -frequency b y) =
    Complex.exp (2*Real.pi*Complex.I*(ShorAlgorithms.QFT.bitsVal (finBits x):ℂ)*
      (ShorAlgorithms.QFT.bitsVal (ShorAlgorithms.QFT.bitRev (finBits y)):ℂ)/2^b) := by
  change ZMod.stdAddChar (binary b x * - -binary b (reverse b y)) = _
  rw [neg_neg,binary_cast,binary_cast]
  let a := ShorAlgorithms.QFT.bitsVal (finBits x)
  let d := ShorAlgorithms.QFT.bitsVal (ShorAlgorithms.QFT.bitRev (finBits y))
  change ZMod.stdAddChar ((a:ZMod (2^b))*(d:ZMod (2^b))) = Complex.exp (2*Real.pi*Complex.I*(a:ℂ)*(d:ℂ)/2^b)
  have hc : (a:ZMod (2^b))*(d:ZMod (2^b)) = ((a*d : ℤ) : ZMod (2^b)) := by push_cast; rfl
  rw [hc,ZMod.stdAddChar_coe]
  push_cast
  ring_nf

def phaseMap {b : ℕ} : List (PhaseInstruction b) → EuclideanSpace ℂ (Bits b) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bits b)
  | [] => LinearIsometry.id
  | g :: gs => (phaseMap gs).comp (phaseInstructionIsometry g)

theorem phaseMap_apply (gs : List (PhaseInstruction b)) (v : EuclideanSpace ℂ (Bits b)) :
    (phaseMap gs v).ofLp = runPhases gs v.ofLp := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih => exact ih (phaseInstructionIsometry g v)

def delta (x : Bits b) : EuclideanSpace ℂ (Bits b) := WithLp.toLp 2 (fun y => if y=x then 1 else 0)

theorem delta_expansion (v : EuclideanSpace ℂ (Bits b)) : v = ∑ x, (v x) • delta x := by
  ext y
  simp [delta,WithLp.ofLp_sum,apply_ite,smul_eq_mul,Finset.sum_ite_eq]

theorem delta_pull (x : Bits b) : (delta x).ofLp = pullQFTState (ShorAlgorithms.QFT.basisState (finBits x)) := by
  funext y
  change (if y=x then (1:ℂ) else 0) = if finBits y=finBits x then 1 else 0
  have he : finBits y=finBits x ↔ y=x := (binaryFin b).injective.eq_iff
  simp [he]

theorem axis_kernel (v : EuclideanSpace ℂ (Bits b)) (y : Bits b) :
    (phaseMap (qftPhases b) v) y =
      ((Real.sqrt (2^b):ℂ))⁻¹ * ∑ x : Bits b, ZMod.stdAddChar (binary b x * -frequency b y) * v x := by
  have hentry (x : Bits b) : (phaseMap (qftPhases b) (delta x)) y =
      ((Real.sqrt (2^b):ℂ))⁻¹ * ZMod.stdAddChar (binary b x * -frequency b y) := by
    rw [phaseMap_apply,delta_pull,qftPhases_basis,char_phase]
  conv_lhs => rw [delta_expansion v,map_sum]
  simp only [map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,hentry]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end

end GridReadout.Axis

end P2MDyadicModule59

/- Helper module AxisError. -/
section P2MDyadicModule60

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

noncomputable section

variable {b d : ℕ}

def localKernel {R : Type*} (u : Bits b × R → ℂ) (p : Bits b × R) : ℂ :=
  ((Real.sqrt (2^b):ℂ))⁻¹ * ∑ x : Bits b, ZMod.stdAddChar (binary b x * -frequency b p.1) * u (x,p.2)

def cost (x : Input) : ℝ := 25*(x.1.length:ℝ)*((x.1.length:ℝ)+1)/((x.2.length:ℝ)+1)

theorem cost_nonneg (x : Input) : 0≤cost x := by unfold cost; positivity

theorem one_axis_entangled : ∃ a : ℕ, 0<a ∧ ∀ (x : Input) (R : Type) [Fintype R] (u : Bits x.1.length × R → ℂ),
    let act := fun p : Bits (x.1.length+2) × R => runLayer (instructions (physicalWord a x))
      (initializeAux (fun i => u (i,p.2))) p.1
    ‖(WithLp.toLp 2 (act - initWithReference (r:=2) (localKernel u)) : EuclideanSpace ℂ _)‖ ≤
      cost x * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ _)‖ := by
  obtain ⟨a,ha,h⟩ := exists_global_accuracy
  refine ⟨a,ha,?_⟩
  intro x R _ u
  dsimp only
  have hslice (z : R) : runPhases (qftPhases x.1.length) (fun j => u (j,z)) =
      (fun i => localKernel u (i,z)) := by
    funext i
    have h' := axis_kernel (WithLp.toLp 2 (fun j => u (j,z))) i
    simpa only [phaseMap_apply,WithLp.ofLp_toLp,localKernel] using h'
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (cost_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,norm_sq_slices,norm_sq_slices,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have he := pow_le_pow_left₀ (norm_nonneg _) (h x (fun j => u (j,z))) 2
  rw [mul_pow,hslice] at he
  exact he

theorem one_axis_relocated : ∃ a : ℕ, 0<a ∧ ∀ (x : Input) {d : ℕ}
    (w : Fin (x.1.length+2) ↪ Fin d) (u : Bits x.1.length × OutsideBits w → ℂ),
    ‖(WithLp.toLp 2 (runLayer (instructions ((physicalWord a x).map (Letter.relocate w)))
      (unsplitState w (initWithReference (r:=2) u)) -
      unsplitState w (initWithReference (r:=2) (localKernel u))) : EuclideanSpace ℂ _)‖ ≤
      cost x * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ _)‖ := by
  obtain ⟨a,ha,h⟩ := one_axis_entangled
  refine ⟨a,ha,?_⟩
  intro x d w u
  rw [←splitState_norm w]
  have hs : splitState w (runLayer (instructions ((physicalWord a x).map (Letter.relocate w)))
      (unsplitState w (initWithReference (r:=2) u)) - unsplitState w (initWithReference (r:=2) (localKernel u))) =
      splitState w (runLayer (instructions ((physicalWord a x).map (Letter.relocate w)))
      (unsplitState w (initWithReference (r:=2) u))) - initWithReference (r:=2) (localKernel u) := by
    funext p
    change _ - (splitState w (unsplitState w (initWithReference (r:=2) (localKernel u)))) p = _
    rw [split_unsplit]
    rfl
  rw [hs,relocate_word_split,split_unsplit]
  have hm : applyWithReference (matrix (physicalWord a x)) (initWithReference (r:=2) u) =
      fun p : Bits (x.1.length+2) × OutsideBits w => runLayer (instructions (physicalWord a x)) (initializeAux (fun i => u (i,p.2))) p.1 := by
    funext p
    exact congrFun (matrix_mulVec (physicalWord a x) (initializeAux (fun i => u (i,p.2)))) p.1
  rw [hm]
  exact h x _ u

end

end GridReadout.Axis

end P2MDyadicModule60

/- Helper module Tensor. -/
section P2MDyadicModule61

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

open FiniteLatticeFourier

noncomputable section

variable {b n : ℕ}

def scalar (b : ℕ) (x y : Bits b) : ℂ :=
  ((Real.sqrt (2^b):ℂ))⁻¹ * ZMod.stdAddChar (binary b x * -frequency b y)

def part (S : Finset (Fin n)) (v : Rows b n → ℂ) (y : Rows b n) : ℂ :=
  ∑ x : Rows b n, (∏ j : Fin n, if j∈S then scalar b (x j) (y j) else if x j=y j then 1 else 0) * v x

theorem part_empty (v : Rows b n → ℂ) : part ∅ v = v := by
  funext y
  unfold part
  rw [Fintype.sum_eq_single y]
  · simp
  · intro x hxy
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    simp only [Finset.notMem_empty,if_false]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi),zero_mul]

theorem part_insert (S : Finset (Fin n)) (i : Fin n) (hi : i∉S) (v : Rows b n → ℂ) (y : Rows b n) :
    (∑ t : Bits b, scalar b t (y i)*part S v (Function.update y i t)) = part (insert i S) v y := by
  unfold part
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_eq_single (x i)]
  · rw [←mul_assoc]
    congr 1
    rw [←Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ←Finset.mul_prod_erase Finset.univ (fun j => if j∈insert i S then scalar b (x j) (y j) else if x j=y j then 1 else 0) (Finset.mem_univ i)]
    simp only [hi,if_false,Function.update_self,if_true,one_mul,Finset.mem_insert_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [Finset.mem_insert,hji]
  · intro t ht
    have hz : (∏ j : Fin n, if j∈S then scalar b (x j) (Function.update y i t j) else if x j=Function.update y i t j then 1 else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi,ht.symm]
    rw [hz,zero_mul,mul_zero]

def rowOutput (b n : ℕ) : Rows b n ≃ (Fin n → ZMod (2^b)) := Equiv.piCongrRight fun _ => frequency b

theorem part_full (u : (Fin n → ZMod (2^b)) → ℂ) (y : Rows b n) :
    part Finset.univ (fun x => u (rowInput b n x)) y =
      ((Real.sqrt (2^b):ℂ))⁻¹^n * transform u (rowOutput b n y) := by
  classical
  unfold part
  simp only [Finset.mem_univ,if_true,scalar,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  unfold transform
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (rowInput b n)
  intro x
  change _ = _ * ((∏ j : Fin n, ZMod.stdAddChar (binary b (x j) * -frequency b (y j))) * _)
  ring

end

end GridReadout.Axis

end P2MDyadicModule61

/- Helper module Wires. -/
section P2MDyadicModule62

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

noncomputable section

variable {n b : ℕ}

private theorem disjoint_wires {m k : ℕ} (i : Fin m) (j : Fin k) : i.castAdd k ≠ j.natAdd m := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem outside {i j : Fin n} (hji : j≠i) (k : Fin b) : dataWire j k ∉ Set.range (wires b i) := by
  rintro ⟨p,hp⟩
  induction p using Fin.addCases with
  | left t =>
    change Fin.append _ _ _ = _ at hp
    simp only [Fin.append_left,dataWire,Fin.castAdd_inj,Equiv.apply_eq_iff_eq,Prod.mk.injEq] at hp
    exact hji hp.1.symm
  | right t =>
    change Fin.append _ _ _ = _ at hp
    simp only [Fin.append_right,auxWire,dataWire] at hp
    exact disjoint_wires _ _ hp.symm

def localRows (i : Fin n) (t : Bits b) (r : OutsideBits (wires b i)) : Rows b n :=
  fun j => if hj : j=i then t else fun k => r ⟨dataWire j k,outside hj k⟩

theorem localRows_eq (i : Fin n) (y : Bits (n*b+2)) (t : Bits b) :
    localRows i t ((wireBitsEquiv (wires b i) y).2) = Function.update (rows y) i t := by
  funext j
  by_cases hj : j=i <;> simp [localRows,hj] <;> rfl

theorem slice_init (i : Fin n) (u : Rows b n → ℂ) :
    unsplitState (wires b i) (initWithReference (r:=2) (fun p => u (localRows i p.1 p.2))) = liftRows u := by
  funext y
  have hrow : (qubitsAppendEquiv b 2 (wireBitsEquiv (wires b i) y).1).1 = rows y i := by
    funext k; change y (Fin.append _ _ (k.castAdd 2)) = _; rw [Fin.append_left];rfl
  have hanc : (qubitsAppendEquiv b 2 (wireBitsEquiv (wires b i) y).1).2 = anc n b y := by
    funext k; change y (Fin.append _ _ (k.natAdd b)) = _; rw [Fin.append_right];rfl
  unfold unsplitState initWithReference liftRows
  simp only [hanc,hrow,localRows_eq,Function.update_eq_self]
  rfl

theorem slice_after (S : Finset (Fin n)) (i : Fin n) (hi : i∉S) (u : Rows b n → ℂ) :
    unsplitState (wires b i) (initWithReference (r:=2) (localKernel (fun p => part S u (localRows i p.1 p.2)))) =
    liftRows (part (insert i S) u) := by
  rw [←slice_init i]
  congr 2
  funext p
  rcases p with ⟨z,r⟩
  unfold localKernel
  rw [Finset.mul_sum]
  have hz : localRows i z r i = z := by simp [localRows]
  have hnew (t : Bits b) : localRows i t r = Function.update (localRows i z r) i t := by
    funext j
    by_cases hj : j=i <;> simp [localRows,hj]
  rw [←part_insert S i hi]
  apply Finset.sum_congr rfl
  intro t _
  rw [← hnew t, hz]
  unfold scalar
  ring

end

end GridReadout.Axis

end P2MDyadicModule62

/- Helper module GridNorm. -/
section P2MDyadicModule63

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

theorem localKernel_norm {R : Type} [Fintype R] (v : Bits b×R → ℂ) :
    ‖(WithLp.toLp 2 (localKernel v) : EuclideanSpace ℂ _)‖ = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ _)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_slices,norm_sq_slices]
  apply Finset.sum_congr rfl
  intro r _
  let u := (WithLp.toLp 2 (fun i => v (i,r)) : EuclideanSpace ℂ _)
  have he : (WithLp.toLp 2 (fun i => localKernel v (i,r)) : EuclideanSpace ℂ _) = phaseMap (qftPhases b) u := by
    ext y
    exact (axis_kernel u y).symm
  rw [he,LinearIsometry.norm_map]

theorem scattered_norm (i : Fin n) (f : Bits b×OutsideBits (wires b i) → ℂ) :
    ‖(WithLp.toLp 2 (unsplitState (wires b i) (initWithReference (r:=2) f)) : EuclideanSpace ℂ _)‖ =
      ‖(WithLp.toLp 2 f : EuclideanSpace ℂ _)‖ := by
  rw [←splitState_norm (wires b i),split_unsplit,initWithReference_norm]

theorem part_norm (S : Finset (Fin n)) (v : Rows b n → ℂ) :
    ‖(WithLp.toLp 2 (liftRows (part S v)) : EuclideanSpace ℂ _)‖ = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ _)‖ := by
  induction S using Finset.induction_on with
  | empty => rw [part_empty,liftNorm]
  | insert i S hi ih =>
    rw [←slice_after S i hi,scattered_norm,localKernel_norm,←scattered_norm i, slice_init,ih]

end

end GridReadout.Axis

end P2MDyadicModule63

/- Helper module Circuit. -/
section P2MDyadicModule64

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

noncomputable section

set_option maxHeartbeats 1600000 in
theorem all_axes : ∃ a : ℕ, 0<a ∧ ∀ (x : Input) {n : ℕ} (v : Rows x.1.length n → ℂ)
    (u : EuclideanSpace ℂ (Bits (n*x.1.length+2))),
    ‖circuitIsometry (circuit a x (List.finRange n)) u -
      (WithLp.toLp 2 (liftRows (part Finset.univ v)) : EuclideanSpace ℂ _)‖ ≤
      ‖u - (WithLp.toLp 2 (liftRows v) : EuclideanSpace ℂ _)‖ +
      (n:ℝ)*cost x*‖(WithLp.toLp 2 v : EuclideanSpace ℂ _)‖ := by
  obtain ⟨a,ha,h⟩ := one_axis_relocated
  refine ⟨a,ha,?_⟩
  intro x n v u
  let F (s : Finset (Fin n)) := (WithLp.toLp 2 (liftRows (part s v)) : EuclideanSpace ℂ _)
  let N := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ _)‖
  have step (s : Finset (Fin n)) (i : Fin n) (hi : i∉s) :
      ‖wordIsometry (word a x i) (F s) - F (insert i s)‖ ≤ cost x*N := by
    have he := h x (wires x.1.length i) (fun p => part s v (localRows i p.1 p.2))
    rw [slice_init, slice_after s i hi,←scattered_norm i,slice_init,part_norm] at he
    exact he
  have run (l : List (Fin n)) (hl : l.Nodup) (s : Finset (Fin n)) (hs : ∀ i ∈ l, i ∉ s)
      (u : EuclideanSpace ℂ (Bits (n*x.1.length+2))) :
      ‖circuitIsometry (circuit a x l) u - F (s∪l.toFinset)‖ ≤
      ‖u-F s‖+(l.length:ℝ)*cost x*N := by
    induction l generalizing s u with
    | nil => simp [circuit,F,circuitIsometry,runLayered]
    | cons i l ih =>
      have hlo := List.nodup_cons.mp hl
      have hi := hs i (by simp)
      let u' := wordIsometry (word a x i) u
      have hfirst : ‖u'-F (insert i s)‖ ≤ ‖u-F s‖+cost x*N := by
        have hu : ‖u'-wordIsometry (word a x i) (F s)‖=‖u-F s‖ :=
          (congrArg norm ((wordIsometry (word a x i)).map_sub u (F s))).symm.trans
            ((wordIsometry (word a x i)).norm_map _)
        calc
          _ ≤ ‖u'-wordIsometry (word a x i) (F s)‖+‖wordIsometry (word a x i) (F s)-F (insert i s)‖ := by
            simpa only [dist_eq_norm] using dist_triangle u' (wordIsometry (word a x i) (F s)) (F (insert i s))
          _ ≤ _ := add_le_add hu.le (step s i hi)
      have he := ih hlo.2 (insert i s) (fun j hj hm => by
        rcases Finset.mem_insert.mp hm with rfl|hm
        · exact hlo.1 hj
        · exact hs j (by simp [hj]) hm) u'
      have hfin : s ∪ (i::l).toFinset = insert i s ∪ l.toFinset := by ext; simp
      rw [hfin]
      change ‖circuitIsometry (circuit a x l) u' - _‖ ≤ _
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at *
      linarith
  have hh := run (List.finRange n) (List.nodup_finRange _) ∅ (by simp) u
  have hull : (List.finRange n).toFinset = Finset.univ := by ext; simp
  simpa only [hull,Finset.empty_union,List.length_finRange,F,part_empty,N] using hh

end

end GridReadout.Axis

end P2MDyadicModule64

/- Helper module Outcome. -/
section P2MDyadicModule65

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

theorem reindex_born {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (v : EuclideanSpace ℂ Y) (E : Y→Prop) :
    bornEvent (fun x => E (e x)) (reindex e v) = bornEvent E v :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem part_linear {S : Finset (Fin n)} (a : ℝ) (v : EuclideanSpace ℂ (Rows b n)) :
    (WithLp.toLp 2 (part S (a • v).ofLp) : EuclideanSpace ℂ _) = a • (WithLp.toLp 2 (part S v.ofLp) : EuclideanSpace ℂ _) := by
  ext y
  change (∑ x, _ * ((a:ℂ)*v x)) = (a:ℂ)*(∑ x, _ * v x)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem final_identification (r : EuclideanSpace ℂ (Fin n → ZMod (2^b))) :
    WithLp.toLp 2 (part Finset.univ (inputState r).ofLp) =
      reindex (rowOutput b n) (normalized (transformState r)) := by
  let u := reindex (rowInput b n) r
  let c : ℝ := (Real.sqrt (2^b))⁻¹ ^ n
  have hc : 0<c := by dsimp [c]; positivity
  have he : (WithLp.toLp 2 (part Finset.univ u.ofLp) : EuclideanSpace ℂ _) = c • reindex (rowOutput b n) (transformState r) := by
    ext y
    have hs := part_full r.ofLp y
    change _ = (c:ℂ) * transform r.ofLp (rowOutput b n y)
    simpa only [u,reindex,WithLp.ofLp_toLp,c,Complex.ofReal_pow,Complex.ofReal_inv] using hs
  have hnorm := part_norm (Finset.univ : Finset (Fin n)) u.ofLp
  rw [liftNorm] at hnorm
  change ‖WithLp.toLp 2 (part Finset.univ u.ofLp)‖=‖u‖ at hnorm
  change WithLp.toLp 2 (part Finset.univ (‖u‖⁻¹ • u).ofLp) = _
  rw [part_linear,←hnorm]
  change normalized (WithLp.toLp 2 (part Finset.univ u.ofLp)) = _
  rw [he,normalized_smul_pos _ hc,normalized_reindex]

def encodedOutput (n b : ℕ) (p : Bits (n*b+2)) : Str :=
  encVec encI (fun i => (rowOutput b n (rows p) i).valMinAbs)

private theorem pref {z w : Fin n → ℤ} (h : encVec encI z <+: encVec encI w) : z=w := by
  obtain ⟨s,hs⟩ := h
  let read := Integration9_9.TM2NativeAffineEncoding.readVector
  have hit (v : Fin n → ℤ) (s : Str) : (read (encVec encI v ++ s)).2 = List.ofFn v := by
    rw [show read = Integration9_9.TM2NativeAffineEncoding.readVector from rfl,Integration9_9.TM2NativeAffineEncoding.readVector_append]
  have hz := hit z s
  rw [hs] at hz
  exact List.ofFn_inj.mp (hz.symm.trans (by simpa using hit w []))

theorem output_iff (p : Bits (n*b+2)) (T : Finset (Fin n → ℤ)) :
    (∃ z ∈ T, encVec encI z <+: encodedOutput n b p) ↔ (fun i => (rowOutput b n (rows p) i).valMinAbs)∈T := by
  constructor
  · rintro ⟨z,hz,hp⟩
    rw [←pref hp]; exact hz
  · intro h; exact ⟨_,h,⟨[],List.append_nil _⟩⟩

theorem prepared_event : ∃ a : ℕ, 0<a ∧ ∀ (x : Input) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) (hr : 0<r)
    (u : EuclideanSpace ℂ (Bits (n*x.1.length+2))) (hu : ‖u‖=1) (T : Finset (Fin n → ℤ)),
    let ideal := inputState (dualInput (b:=x.1.length) B hB r)
    let out := circuitIsometry (circuit a x (List.finRange n)) u
    |bornEvent (fun p => ∃ z∈T, encVec encI z <+: encodedOutput n x.1.length p) out -
      RegevSearch.fourierEvent B r (2^x.1.length) T| ≤
      2*(‖u - (WithLp.toLp 2 (liftRows ideal.ofLp) : EuclideanSpace ℂ _)‖ + (n:ℝ)*cost x) := by
  obtain ⟨a,ha,h⟩ := all_axes
  refine ⟨a,ha,?_⟩
  intro x n B hB r hr u hu T
  let v := inputState (dualInput (b:=x.1.length) B hB r)
  let out := circuitIsometry (circuit a x (List.finRange n)) u
  let ref := (WithLp.toLp 2 (liftRows (part Finset.univ v.ofLp)) : EuclideanSpace ℂ _)
  let E (z : Fin n → ZMod (2^x.1.length)) := (fun i => (z i).valMinAbs) ∈ T
  let event (p : Bits (n*x.1.length+2)) := E (rowOutput x.1.length n (rows p))
  have hev : (fun p => ∃ z∈T, encVec encI z <+: encodedOutput n x.1.length p) = event := by
    funext p; exact propext (output_iff p T)
  have he : bornEvent event ref = RegevSearch.fourierEvent B r (2^x.1.length) T := by
    change bornEvent (fun p => E (rowOutput _ _ (rows p))) (WithLp.toLp 2 (liftRows _)) = _
    rw [liftBorn (fun z => E (rowOutput x.1.length n z)) (part Finset.univ v.ofLp),final_identification (dualInput (b:=x.1.length) B hB r),reindex_born]
    exact reference_eq B hB r hr T
  have hv : ‖v‖ ≤ 1 := normalized_norm_le _
  have hnr : ‖ref‖ ≤ 1 := (part_norm Finset.univ v.ofLp).le.trans hv
  have hout : ‖out‖=1 := ((circuitIsometry _).norm_map _).trans hu
  have hd := h x v.ofLp u
  change ‖out-ref‖ ≤ ‖u-WithLp.toLp 2 (liftRows v.ofLp)‖ + (n:ℝ)*cost x*‖v‖ at hd
  have hm := mul_le_mul_of_nonneg_left hv (mul_nonneg (Nat.cast_nonneg n) (cost_nonneg x))
  change |bornEvent _ out - _| ≤ _
  rw [hev,←he]
  have hbound := (bornEvent_error_le event out ref).trans (mul_le_mul_of_nonneg_left
    (by linarith : ‖out‖+‖ref‖≤2) (norm_nonneg _))
  linarith

end

end GridReadout.Axis

end P2MDyadicModule65

/- Helper module Cost. -/
section P2MDyadicModule66

set_option autoImplicit false

namespace GridReadout.Axis

open InfoLossLAR.WorstCase NativeQFTPlanCompile FiniteGateTransport

noncomputable section

theorem precision_bound (x : Input) (n k : ℕ)
    (h : precision n x.1.length k ≤ x.2.length) :
    2*(n:ℝ)*cost x ≤ 1/(4*((k:ℝ)+1)) := by
  have hh : 200*(n:ℝ)*(x.1.length:ℝ)*((x.1.length:ℝ)+1)*((k:ℝ)+1) ≤ x.2.length := by exact_mod_cast h
  unfold cost
  rw [←mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end

end GridReadout.Axis

end P2MDyadicModule66

/- Helper module SignedProgram. -/
section P2MDyadicModule67

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 QMCNumericRuntime

noncomputable section

theorem powTwo_id (s : Str) : powTwo s = 2^s.length := by
  induction s with
  | nil => decide
  | cons a l ih =>
    simpa only [powTwo,List.map_cons,List.cons_append,bitValue,Bool.toNat_false,zero_add,List.length_cons,pow_succ,mul_comm] using congrArg (fun t => 2*t) ih

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

theorem signedRow_correct {b : ℕ} (t : Bits b) : signedRow (List.ofFn t) = (frequency b t).valMinAbs := by
  let v := ShorAlgorithms.QFT.bitsVal (finBits (reverse b t))
  have hv : v < 2^b := by
    have hf := (finFunctionFinEquiv (finBits (reverse b t))).isLt
    simpa [v,ShorAlgorithms.QFT.bitsVal,Nat.mul_comm] using hf
  have ht : (List.ofFn t).reverse = List.ofFn (reverse b t) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp [List.getElem_reverse,reverse,Fin.rev]
      congr 1; apply Fin.ext; dsimp; omega
  have hc : frequency b t = -(v:ZMod (2^b)) := congrArg Neg.neg (binary_cast (reverse b t))
  unfold signedRow
  rw [powTwo_id,List.length_ofFn,ht,tape_value]
  change (if 2*v < 2^b then -(v:ℤ) else ((2^b:ℕ):ℤ)-(v:ℤ)) = _
  symm
  apply (ZMod.valMinAbs_spec _ _).mpr
  have hv' : (v:ℤ)<((2^b:ℕ):ℤ) := by exact_mod_cast hv
  by_cases hs : 2*v<2^b
  · rw [if_pos hs]
    have hs' : 2*(v:ℤ)<((2^b:ℕ):ℤ) := by exact_mod_cast hs
    refine ⟨?_,by omega,by omega⟩
    simpa using hc
  · rw [if_neg hs]
    have hs' : ((2^b:ℕ):ℤ) ≤ 2*(v:ℤ) := by exact_mod_cast (Nat.le_of_not_gt hs)
    refine ⟨?_,by omega,by omega⟩
    rw [hc, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, zero_sub]

theorem rowSlices_correct {n b : ℕ} (nt bt : List Unit) (hn : nt.length=n) (hb : bt.length=b) (p : Bits (n*b+2)) :
    rowSlices (nt,bt,List.ofFn p) = List.ofFn (fun i : Fin n => List.ofFn (rows p i)) := by
  apply List.ext_getElem
  · simp [rowSlices,hn]
  · intro i hi hj
    have hin : i<n := by simpa [rowSlices,hn] using hi
    simp only [rowSlices,List.getElem_map,List.getElem_range,hb,List.getElem_ofFn]
    apply List.ext_getElem
    · have hsize := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hin)
      simp only [Nat.succ_mul] at hsize
      simp [List.length_take,List.length_drop,List.length_ofFn];omega
    · intro j h₁ h₂
      simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn,rows,dataWire]
      congr 1
      apply Fin.ext
      simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem encodeSlices_correct {n b : ℕ} (nt bt : List Unit) (hn : nt.length=n) (hb : bt.length=b) (p : Bits (n*b+2)) :
    encodeSlices (nt,bt,List.ofFn p) = encodedOutput n b p := by
  rw [encodeSlices,rowSlices_correct _ _ hn hb p,List.map_ofFn]
  change TM2NativeAffineEmitter.serializeVector (List.ofFn (fun i => signedRow (List.ofFn (rows p i)))) = _
  simp_rw [signedRow_correct]
  simp [TM2NativeAffineEmitter.serializeVector,LARPlatformEncoding.serializeBinaryWords,
    encodedOutput,encVec,encL,List.map_ofFn,List.flatMap_def,rowOutput]

end

end GridReadout.Axis

end P2MDyadicModule67

/- Helper module FinalPhysical. -/
section P2MDyadicModule68

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

open RegevSearch RegevSketch

noncomputable section

theorem encoded_prepared_event : ∃ a : ℕ, 0<a ∧ ∀ (nt : List Unit) (x : Input)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (hB : B.det≠0)
    (r : ℝ) (_hr : 0<r) (k : ℕ) (_hprec : precision nt.length x.1.length k ≤ x.2.length)
    (u : EuclideanSpace ℂ (Bits (nt.length*x.1.length+2))) (_hu : ‖u‖=1),
    let exact := inputState (dualInput (b:=x.1.length) B hB r)
    let out := circuitIsometry (circuit a x (List.finRange nt.length)) u
    let emitted := fun p => encodeSlices (nt,x.1,List.ofFn p)
    bornEvent (fun p => ∃ z : Fin nt.length → ℤ, encVec encI z <+: emitted p) out = 1 ∧
    ∀ T : Finset (Fin nt.length → ℤ),
    |bornEvent (fun p => ∃ z ∈ T, encVec encI z <+: emitted p) out - fourierEvent B r (2^x.1.length) T| ≤
      2*‖u-(WithLp.toLp 2 (liftRows exact.ofLp) : EuclideanSpace ℂ _)‖ + 1/(4*((k:ℝ)+1)) := by
  obtain ⟨a,ha,h⟩ := prepared_event
  refine ⟨a,ha,?_⟩
  intro nt x B hB r hr k hprec u hu
  let n := nt.length
  let out := circuitIsometry (circuit a x (List.finRange nt.length)) u
  have hout : ‖out‖=1 := ((circuitIsometry _).norm_map _).trans hu
  have hs (p : Bits (nt.length*x.1.length+2)) :
      encodeSlices (nt,x.1,List.ofFn p) = encodedOutput nt.length x.1.length p := encodeSlices_correct nt x.1 rfl rfl p
  dsimp only
  simp_rw [hs]
  constructor
  · have hv (p : Bits (nt.length*x.1.length+2)) :
        ∃ z : Fin nt.length → ℤ, encVec encI z <+: encodedOutput nt.length x.1.length p :=
      ⟨_,[],List.append_nil _⟩
    change (∑ p : Bits (nt.length*x.1.length+2), if ∃ z : Fin nt.length → ℤ, encVec encI z <+: encodedOutput nt.length x.1.length p then ‖out p‖^2 else 0)=1
    simp only [hv,if_true,← EuclideanSpace.norm_sq_eq,hout,one_pow]
  · intro T
    have he := h x B hB r hr u hu T
    have hp := precision_bound x nt.length k hprec
    linarith

end

end GridReadout.Axis

end P2MDyadicModule68

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule69

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

end P2MDyadicModule69

/- Helper module Solutions.RegevBridgeQuantumXorError. -/
section P2MDyadicModule70

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

end P2MDyadicModule70

/- Helper module FullSpaceBorn. -/
section P2MDyadicModule71

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

end P2MDyadicModule71

/- Helper module QFTJunk. -/
section P2MDyadicModule72

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

/-- The signed QFT readout remains correct on the full physical state carrying
an independent unit residue/garbage register in the reference. The actual
input can have arbitrary entanglement, charged by its joint norm distance. -/
theorem _root_.solution : ∃ a : ℕ, 0<a ∧ ∀ (nt : List Unit) (x : Input) (γ : ℕ)
    (B : Matrix (Fin nt.length) (Fin nt.length) ℤ) (hB : B.det≠0) (r : ℝ), 0<r →
    ∀ (k : ℕ), precision nt.length x.1.length k ≤ x.2.length →
    ∀ (v : QState (nt.length*x.1.length+2)) (_hv : stateNorm v=1) (junk : QState γ) (_hj : stateNorm junk=1)
      (actual : QState (nt.length*x.1.length+2+γ)) (_ha : stateNorm actual = 1),
    let G := circuit a x (List.finRange nt.length)
    let u := WithLp.toLp 2 (runLayered (leftCircuit (m:=γ) G) actual)
    let emitted := fun p : Bits (nt.length*x.1.length+2+γ) => encodeSlices (nt,x.1,List.ofFn (leftRegister p : Bits (nt.length*x.1.length+2)))
    let ideal := inputState (dualInput (b:=x.1.length) B hB r)
    bornEvent (fun p => ∃ z : Fin nt.length → ℤ, encVec encI z <+: emitted p) u = 1 ∧
    ∀ T : Finset (Fin nt.length → ℤ),
      |bornEvent (fun p => ∃ z ∈ T, encVec encI z <+: emitted p) u - fourierEvent B r (2^x.1.length) T| ≤
        2*stateNorm (actual-tensorState v junk)+2*stateNorm (v-liftRows ideal.ofLp)+1/(4*((k:ℝ)+1)) := by
  obtain ⟨a,ha,hread⟩ := encoded_prepared_event
  refine ⟨a,ha,?_⟩
  intro nt x γ B hB r hr k hk v hv junk hj actual hactual
  let G := circuit a x (List.finRange nt.length)
  let emit (p : Bits (nt.length*x.1.length+2)) := encodeSlices (nt,x.1,List.ofFn p)
  have hprod : stateNorm (tensorState v junk) = 1 := by
    have hp := tensorState_mass v junk
    have wn {t : ℕ} (w : QState t) : (∑ p, ‖w p‖^2) = stateNorm w^2 := (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 w)).symm
    simp only [wn,hv,hj,one_pow,mul_one] at hp
    nlinarith [show 0 ≤ stateNorm (tensorState v junk) from norm_nonneg _]
  dsimp only
  constructor
  · have valid (p : Bits (nt.length*x.1.length+2+γ)) : ∃ z : Fin nt.length → ℤ, encVec encI z <+: emit (leftRegister p) := by
      unfold emit
      rw [encodeSlices_correct nt x.1 rfl rfl]
      exact ⟨_,[],List.append_nil _⟩
    change (∑ p, if ∃ z : Fin nt.length → ℤ, encVec encI z <+: emit (leftRegister p) then ‖runLayered (leftCircuit G) actual p‖^2 else 0) = 1
    simp only [valid,ite_true]
    rw [show (∑ p, ‖runLayered (leftCircuit (m:=γ) G) actual p‖^2) = stateNorm (runLayered (leftCircuit (m:=γ) G) actual)^2 from (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 _)).symm]
    rw [show stateNorm (runLayered (leftCircuit (m:=γ) G) actual) = stateNorm actual from (circuitIsometry _).norm_map _,hactual,one_pow]
  · intro T
    let E (p : Bits (nt.length*x.1.length+2)) := ∃ z ∈ T, encVec encI z <+: emit p
    have h := PaddedDecoder.born_after (leftCircuit (m:=γ) G) actual (tensorState v junk) hactual hprod (fun p => E (leftRegister p))
    rw [leftCircuit_tensor,marginal_product _ _ hj] at h
    have h2 := (hread nt x B hB r hr k hk (WithLp.toLp 2 v) hv).2 T
    let actualP := bornEvent (fun p => E (leftRegister p)) (WithLp.toLp 2 (runLayered (leftCircuit (m:=γ) G) actual))
    let idealP := bornEvent E (WithLp.toLp 2 (runLayered G v))
    let targetP := fourierEvent B r (2^x.1.length) T
    let d := stateNorm (v-liftRows (inputState (dualInput (b:=x.1.length) B hB r)).ofLp)
    change |actualP-idealP| ≤ _ at h
    change |idealP-targetP| ≤ 2*d + 1/(4*((k:ℝ)+1)) at h2
    change |actualP-targetP| ≤ 2*stateNorm (actual-tensorState v junk)+2*d+1/(4*((k:ℝ)+1))
    exact (abs_sub_le actualP idealP targetP).trans ((add_le_add h h2).trans (le_of_eq (add_assoc _ _ _).symm))

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule72
#print axioms solution
