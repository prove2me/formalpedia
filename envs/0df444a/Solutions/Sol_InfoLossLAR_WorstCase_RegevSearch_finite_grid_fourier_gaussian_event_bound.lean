-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.finite_grid_fourier_gaussian_event_bound
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:34:23.141908+00:00
-- url     : https://prove2.me/submissions/9eb74f82-9b2a-4c38-a08d-87dfc113419c

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_P2M_Util
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Mathlib
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic

set_option linter.all false
section LocalPoissonProof0

open FourierTransform

open RegevLWE.GaussConv in
theorem recoveredProof_1ead56eea0d84288bdc592f9fdccd41b {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (c w : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin n) => (rhoShift σ c x : ℂ)) w =
      Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ c w : ℝ))) * (σ : ℂ) ^ n *
        (rho (1 / σ) w : ℂ) := by
  set g : EuclideanSpace ℝ (Fin n) → ℂ :=
    fun v => Complex.exp (-((Real.pi : ℂ) / (σ : ℂ) ^ 2) * (‖v‖ : ℂ) ^ 2) with hg
  have key : (fun x : EuclideanSpace ℝ (Fin n) => (rhoShift σ c x : ℂ)) =
      g ∘ (fun v => v + (-c)) := by
    funext x
    simp only [Function.comp_apply, hg, rhoShift, rho, Complex.ofReal_exp]
    congr 1
    rw [← sub_eq_add_neg]
    push_cast
    ring
  have htr := VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) g (-c)
  rw [key]
  change VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume
    (innerₗ (EuclideanSpace ℝ (Fin n))) (g ∘ fun v => v + -c) w = _
  rw [htr]
  change (Real.fourierChar (innerₗ (EuclideanSpace ℝ (Fin n)) (-c) w)) • 𝓕 g w = _
  have hb : 0 < ((Real.pi : ℂ) / (σ : ℂ) ^ 2).re := by
    rw [show ((Real.pi : ℂ) / (σ : ℂ) ^ 2) = ((Real.pi / σ ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    positivity
  rw [hg, fourier_gaussian_innerProductSpace hb, finrank_euclideanSpace_fin]
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hσ.ne'
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e1 : (Real.pi : ℂ) / ((Real.pi : ℂ) / (σ : ℂ) ^ 2) = ((σ ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp
  have e2 : ((σ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) = (σ : ℂ) ^ n := by
    rw [show ((n : ℂ) / 2) = ((n / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.rpow_two, ← Real.rpow_mul hσ.le,
      show (2 : ℝ) * (n / 2) = n by ring, Real.rpow_natCast]
    push_cast; rfl
  have e3 : Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / ((Real.pi : ℂ) / (σ : ℂ) ^ 2)) =
      (rho (1 / σ) w : ℂ) := by
    simp only [rho, Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
  have hi : innerₗ (EuclideanSpace ℝ (Fin n)) (-c) w = -inner ℝ c w := by
    simp [inner_neg_left]
  rw [e1, e2, e3, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hi]
  rw [← mul_assoc]
  congr 2
  push_cast
  ring_nf


open FourierTransform
namespace RegevLWE.GaussConv

theorem fourier_rhoShift {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (c w : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin n) => (rhoShift σ c x : ℂ)) w =
      Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ c w : ℝ))) * (σ : ℂ) ^ n *
        (rho (1 / σ) w : ℂ) := by p2m_exact_reverting @recoveredProof_1ead56eea0d84288bdc592f9fdccd41b

end RegevLWE.GaussConv


end LocalPoissonProof0
section LocalPoissonProof2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq

set_option autoImplicit false

open scoped SchwartzMap ContDiff

namespace WsC
namespace GS

open Real

noncomputable section

variable (ι : Type) [Fintype ι]

def q : EuclideanSpace ℝ ι → ℝ := fun x => (-Real.pi) * ‖x‖ ^ 2

def gR : EuclideanSpace ℝ ι → ℝ := Real.exp ∘ q ι

def gC : EuclideanSpace ℝ ι → ℂ := Complex.ofRealLI ∘ gR ι

theorem q_hasTemperateGrowth : (q ι).HasTemperateGrowth := by
  unfold q
  fun_prop

theorem q_contDiff : ContDiff ℝ ∞ (q ι) := (q_hasTemperateGrowth ι).1

theorem gR_contDiff : ContDiff ℝ ∞ (gR ι) := Real.contDiff_exp.comp (q_contDiff ι)

theorem gC_contDiff : ContDiff ℝ ∞ (gC ι) :=
  Complex.ofRealCLM.contDiff.comp (gR_contDiff ι)

theorem norm_iteratedFDeriv_exp (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp t‖ = Real.exp t := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

theorem gR_bound (n : ℕ) : ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x,
    ‖iteratedFDeriv ℝ n (gR ι) x‖ ≤ C * (1 + ‖x‖) ^ k * Real.exp (q ι x) := by
  obtain ⟨k, C₀, hC₀, hq⟩ := (q_hasTemperateGrowth ι).norm_iteratedFDeriv_le_uniform n
  refine ⟨k * n, (Nat.factorial n : ℝ) * (1 + C₀) ^ n, by positivity, fun x => ?_⟩
  set D : ℝ := (1 + C₀) * (1 + ‖x‖) ^ k with hD
  have h1x : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by simp [norm_nonneg])
  have hD1 : 1 ≤ D := by
    rw [hD]
    nlinarith
  have hbound : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i Real.exp (q ι x)‖ ≤ Real.exp (q ι x) := by
    intro i _
    rw [norm_iteratedFDeriv_exp]
  have hgrowth : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (q ι) x‖ ≤ D ^ i := by
    intro i hi hin
    calc ‖iteratedFDeriv ℝ i (q ι) x‖ ≤ C₀ * (1 + ‖x‖) ^ k := hq i hin x
      _ ≤ D := by rw [hD]; nlinarith
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
  have := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := q ι) Real.contDiff_exp (q_contDiff ι)
    (mod_cast le_top) x hbound hgrowth
  calc ‖iteratedFDeriv ℝ n (gR ι) x‖ ≤ (Nat.factorial n : ℝ) * Real.exp (q ι x) * D ^ n := this
    _ = (Nat.factorial n : ℝ) * (1 + C₀) ^ n * (1 + ‖x‖) ^ (k * n) * Real.exp (q ι x) := by
      rw [hD, mul_pow, ← pow_mul]; ring

theorem poly_gauss_le (M : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ M * Real.exp ((-Real.pi) * r ^ 2) ≤ Real.exp 2 * (Nat.factorial M : ℝ) := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have h1 : (-Real.pi) * r ^ 2 ≤ 2 - (1 + r) := by nlinarith [sq_nonneg (r - 1 / 6)]
  have h2 : (1 + r) ^ M / (Nat.factorial M : ℝ) ≤ Real.exp (1 + r) := Real.pow_div_factorial_le_exp (x := 1 + r) (hx := by linarith) (n := M)
  have hM : (0 : ℝ) < (Nat.factorial M : ℝ) := by positivity
  rw [div_le_iff₀ hM] at h2
  calc (1 + r) ^ M * Real.exp ((-Real.pi) * r ^ 2)
      ≤ (Real.exp (1 + r) * (Nat.factorial M : ℝ)) * Real.exp (2 - (1 + r)) := by
        apply mul_le_mul h2 (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (by positivity)
    _ = Real.exp 2 * (Nat.factorial M : ℝ) := by
        rw [mul_assoc, mul_comm ((Nat.factorial M : ℝ) : ℝ), ← mul_assoc, ← Real.exp_add]
        ring_nf

theorem gC_decay (m n : ℕ) : ∃ C : ℝ, ∀ x, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (gC ι) x‖ ≤ C := by
  obtain ⟨k, C, hC, hb⟩ := gR_bound ι n
  refine ⟨C * (Real.exp 2 * (Nat.factorial (m + k) : ℝ)), fun x => ?_⟩
  have hiso : ‖iteratedFDeriv ℝ n (gC ι) x‖ = ‖iteratedFDeriv ℝ n (gR ι) x‖ :=
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left (gR_contDiff ι).contDiffAt (mod_cast le_top)
  rw [hiso]
  have hxm : ‖x‖ ^ m ≤ (1 + ‖x‖) ^ m :=
    pow_le_pow_left₀ (norm_nonneg x) (by linarith [norm_nonneg x]) m
  have hpg := poly_gauss_le (m + k) ‖x‖ (norm_nonneg x)
  calc ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (gR ι) x‖
      ≤ (1 + ‖x‖) ^ m * (C * (1 + ‖x‖) ^ k * Real.exp (q ι x)) :=
        mul_le_mul hxm (hb x) (norm_nonneg _) (by positivity)
    _ = C * ((1 + ‖x‖) ^ (m + k) * Real.exp ((-Real.pi) * ‖x‖ ^ 2)) := by
        rw [q, pow_add]; ring
    _ ≤ C * (Real.exp 2 * (Nat.factorial (m + k) : ℝ)) := mul_le_mul_of_nonneg_left hpg hC

def gauss : 𝓢(EuclideanSpace ℝ ι, ℂ) where
  toFun := gC ι
  smooth' := gC_contDiff ι
  decay' := gC_decay ι

theorem gauss_apply (x : EuclideanSpace ℝ ι) :
    gauss ι x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) := by
  show gC ι x = _
  simp [gC, gR, q, neg_mul]

theorem main : ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x : EuclideanSpace ℝ ι,
    g x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) :=
  ⟨gauss ι, gauss_apply ι⟩

end

end WsC.GS

theorem recoveredProof_84828ab0a41c59af8a18396ec2a0d8f2 (ι : Type) [Fintype ι] :
    ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x : EuclideanSpace ℝ ι,
      g x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) := by
  exact WsC.GS.main ι

end S_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
end P2MW
export P2MW.S_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (recoveredProof_84828ab0a41c59af8a18396ec2a0d8f2)


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped SchwartzMap
theorem SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (ι : Type) [Fintype ι] :
    ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x : EuclideanSpace ℝ ι,
      g x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) := by p2m_exact_reverting @recoveredProof_84828ab0a41c59af8a18396ec2a0d8f2

end LocalPoissonProof2
section LocalPoissonProof3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open MeasureTheory Real Complex Set TopologicalSpace Topology Submodule WithLp
open scoped FourierTransform InnerProductSpace

noncomputable section

namespace PiPoissonSummation

variable {d : Type*} [Fintype d]

def intVec (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)

def piFourierIntegral (f : (d → ℝ) → ℂ) (ξ : d → ℝ) : ℂ :=
  ∫ v, f v * (𝐞 (-∑ i, v i * ξ i) : ℂ) ∂(volume : Measure (d → ℝ))

theorem coe_basisFun_equivFun_symm (n : d → ℤ) :
    ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.symm n :
        span ℤ (Set.range (Pi.basisFun ℝ d))) : d → ℝ) = intVec n := by
  classical
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, SetLike.val_smul, Module.Basis.restrictScalars_apply,
    Pi.basisFun_apply]
  ext j
  simp only [intVec, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [zsmul_eq_mul]

theorem finrank_span_basisFun :
    Module.finrank ℤ (span ℤ (Set.range (Pi.basisFun ℝ d)) : Submodule ℤ (d → ℝ))
      = Fintype.card d :=
  Module.finrank_eq_card_basis ((Pi.basisFun ℝ d).restrictScalars ℤ)

theorem summable_norm_intVec_inv_pow {N : ℕ} (hN : Fintype.card d < N) :
    Summable fun n : d → ℤ => ‖intVec (d := d) n‖⁻¹ ^ N := by
  have hfin : Module.finrank ℤ
      (span ℤ (Set.range (Pi.basisFun ℝ d)) : Submodule ℤ (d → ℝ)) < N := by
    rw [finrank_span_basisFun]; exact hN
  have hL : Summable fun z : span ℤ (Set.range (Pi.basisFun ℝ d)) => ‖(z : d → ℝ)‖⁻¹ ^ N :=
    ZLattice.summable_norm_pow_inv (span ℤ (Set.range (Pi.basisFun ℝ d))) N hfin
  have := ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.toEquiv.symm.summable_iff
    (f := fun z : span ℤ (Set.range (Pi.basisFun ℝ d)) => ‖(z : d → ℝ)‖⁻¹ ^ N))).mpr hL
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv_symm]
  congr 2
  exact congrArg norm (coe_basisFun_equivFun_symm n)

theorem summable_norm_schwartz_intVec (g : SchwartzMap (d → ℝ) ℂ) :
    Summable fun n : d → ℤ => ‖(g : (d → ℝ) → ℂ) (intVec n)‖ := by
  set N := Fintype.card d + 1
  have hsum := summable_norm_intVec_inv_pow (d := d) (N := N) (Nat.lt_succ_self _)
  refine Summable.of_norm_bounded_eventually
    (g := fun n : d → ℤ => SchwartzMap.seminorm ℝ N 0 g * ‖intVec (d := d) n‖⁻¹ ^ N)
    (hsum.mul_left _) ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (s := {(0 : d → ℤ)}) (Set.finite_singleton _) ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hn ⊢
  by_contra hne
  apply hn
  have hne0 : intVec (d := d) n ≠ 0 := by
    intro h; apply hne; ext i
    have := congrFun h i
    simpa [intVec] using this
  have hpos : (0 : ℝ) < ‖intVec (d := d) n‖ ^ N := pow_pos (norm_pos_iff.mpr hne0) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ g N (intVec n)
  rw [norm_norm, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact hdecay

abbrev euclideanToPi : EuclideanSpace ℝ d ≃L[ℝ] (d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)

theorem piFourierIntegral_eq_fourier_euclidean (h : SchwartzMap (d → ℝ) ℂ) (ξ : d → ℝ) :
    piFourierIntegral (⇑h) ξ
      = (𝓕 (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h)
            : EuclideanSpace ℝ d → ℂ)) (toLp 2 ξ) := by
  unfold piFourierIntegral
  rw [Real.fourier_eq]
  rw [← MeasurePreserving.integral_comp (PiLp.volume_preserving_ofLp d)
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    Circle.smul_def, smul_eq_mul]
  have hinner : ∑ i, (ofLp v) i * ξ i = ⟪v, toLp 2 ξ⟫_ℝ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [← hinner, mul_comm]
  rfl

theorem summable_piFourierIntegral_schwartz_intVec (h : SchwartzMap (d → ℝ) ℂ) :
    Summable fun m : d → ℤ => piFourierIntegral (⇑h) (intVec m) := by
  let h' : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h
  let g' : SchwartzMap (EuclideanSpace ℝ d) ℂ := 𝓕 h'
  let g : SchwartzMap (d → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)).symm g'
  have hg : ∀ ξ : d → ℝ, piFourierIntegral (⇑h) ξ = g ξ := fun ξ => by
    rw [piFourierIntegral_eq_fourier_euclidean h ξ]
    simp only [g, g', h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  simp_rw [hg]
  exact (summable_norm_schwartz_intVec g).of_norm

end PiPoissonSummation

section LatticeSummable

open PiPoissonSummation LinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]

theorem recoveredProof_68ff81d81ce955e789860a101c021bfa
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : SchwartzMap V ℂ) (t : V) :
    Summable fun y : LinearMap.BilinForm.dualSubmodule B.flip L =>
      VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ) := by
  classical

  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let bZ : Module.Basis ι ℤ L := Module.Free.chooseBasis ℤ L
  let b : Module.Basis ι ℝ V := bZ.ofZLatticeBasis ℝ L

  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv
  have hA : ∀ v : ι → ℝ, A v = ∑ i, v i • b i := fun v => by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_symm_apply]

  let h : SchwartzMap (ι → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A f
  have hh : ∀ v, h v = f (A v) := fun v => by
    simp only [h, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

  set ν : MeasureTheory.Measure V := Measure.map A volume with hν_def
  haveI : ν.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  set c : NNReal := Measure.addHaarScalarFactor μ ν with hc_def
  have hμν : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν

  let bd : Module.Basis ι ℝ V := B.flip.dualBasis hB.flip b
  have hbd : ∀ i j, B (b j) (bd i) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB.flip b i j
    simpa only [bd, LinearMap.BilinForm.flip_apply] using this
  have hLd : LinearMap.BilinForm.dualSubmodule B.flip L = span ℤ (Set.range bd) := by
    rw [← bZ.ofZLatticeBasis_span ℝ L]
    exact LinearMap.BilinForm.dualSubmodule_span_of_basis B.flip hB.flip b
  let ψ : (ι → ℤ) ≃ LinearMap.BilinForm.dualSubmodule B.flip L :=
    ((bd.restrictScalars ℤ).equivFun.symm.toEquiv).trans (LinearEquiv.ofEq _ _ hLd.symm).toEquiv
  have hψ : ∀ k : ι → ℤ, ((ψ k : _) : V) = ∑ i, (k i : ℝ) • bd i := fun k => by
    simp only [ψ, Equiv.trans_apply, LinearEquiv.coe_toEquiv, LinearEquiv.coe_ofEq_apply]
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, Module.Basis.restrictScalars_apply]
    exact (Int.cast_smul_eq_zsmul ℝ (k i) _).symm

  have hpair : ∀ (v : ι → ℝ) (k : ι → ℤ),
      B (A v) (∑ i, (k i : ℝ) • bd i) = ∑ i, v i * (k i : ℝ) := fun v k => by
    rw [hA]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hbd, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

  have hterm : ∀ k : ι → ℤ,
      VectorFourier.fourierIntegral 𝐞 μ B f (ψ k) = (c : ℝ) • piFourierIntegral h (intVec k) := by
    intro k
    have h1 : piFourierIntegral h (intVec k)
        = ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (A v) := by
      unfold piFourierIntegral
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [hh, hψ, hpair, intVec]
    have h2 : ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (A v)
        = ∫ w, f w * (𝐞 (-(B w (ψ k))) : ℂ) ∂ν := by
      have := MeasurableEmbedding.integral_map A.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (μ := volume)
      simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at this
      rw [hν_def, this]
    rw [VectorFourier.fourierIntegral, hμν, integral_smul_nnreal_measure, NNReal.smul_def, h1, h2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Circle.smul_def, smul_eq_mul, mul_comm]

  let h' : SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := ι)) h
  let g' : SchwartzMap (EuclideanSpace ℝ ι) ℂ := 𝓕 h'
  let g : SchwartzMap (ι → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := ι)).symm g'
  have hg : ∀ ξ : ι → ℝ, piFourierIntegral (⇑h) ξ = g ξ := fun ξ => by
    rw [piFourierIntegral_eq_fourier_euclidean h ξ]
    simp only [g, g', h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl

  have hsum : Summable fun k : ι → ℤ =>
      ‖VectorFourier.fourierIntegral 𝐞 μ B f (ψ k) * (𝐞 (B t (ψ k)) : ℂ)‖ := by
    have := (summable_norm_schwartz_intVec g).mul_left (c : ℝ)
    refine this.congr fun k => ?_
    rw [norm_mul, Circle.norm_coe, mul_one, hterm, hg, norm_smul, Real.norm_of_nonneg c.coe_nonneg]
  refine Summable.of_norm ?_
  exact (ψ.summable_iff (f := fun y : LinearMap.BilinForm.dualSubmodule B.flip L =>
    ‖VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ)‖)).mp hsum

end LatticeSummable

end

end S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
end P2MW
export P2MW.S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule (recoveredProof_68ff81d81ce955e789860a101c021bfa)


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform SchwartzMap
theorem ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : 𝓢(V, ℂ)) (t : V) :
    Summable fun y : LinearMap.BilinForm.dualSubmodule B.flip L =>
      VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ) := by p2m_exact_reverting @recoveredProof_68ff81d81ce955e789860a101c021bfa

end LocalPoissonProof3
section LocalPoissonProof4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open MeasureTheory Real Complex Set TopologicalSpace Topology Submodule WithLp
open scoped FourierTransform InnerProductSpace

noncomputable section

namespace PiPoissonSummation

variable {d : Type*} [Fintype d]

def intVec (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)

def periodize (f : (d → ℝ) → ℂ) (x : d → ℝ) : ℂ :=
  ∑' n : d → ℤ, f (x + intVec n)

theorem periodize_add_intVec (f : (d → ℝ) → ℂ) (x : d → ℝ) (m : d → ℤ) :
    periodize f (x + intVec m) = periodize f x := by
  unfold periodize
  have hstep : ∀ n : d → ℤ,
      f (x + intVec m + intVec n) = f (x + intVec ((Equiv.addLeft m) n)) := fun n => by
    congr 1
    unfold intVec
    ext i; simp only [Equiv.coe_addLeft, Pi.add_apply]; push_cast; ring
  rw [tsum_congr hstep, (Equiv.addLeft m).tsum_eq (fun n : d → ℤ => f (x + intVec n))]

def toUnitAddTorus : (d → ℝ) → UnitAddTorus d := fun x i => (x i : UnitAddCircle)

def piFourierIntegral (f : (d → ℝ) → ℂ) (ξ : d → ℝ) : ℂ :=
  ∫ v, f v * (𝐞 (-∑ i, v i * ξ i) : ℂ) ∂(volume : Measure (d → ℝ))

theorem toUnitAddTorus_add_intVec (x : d → ℝ) (n : d → ℤ) :
    toUnitAddTorus (x + intVec n) = toUnitAddTorus x := by
  funext i
  simp only [toUnitAddTorus, intVec, Pi.add_apply]
  have : ((n i : ℝ) : UnitAddCircle) = 0 := by
    exact_mod_cast (AddCircle.coe_eq_zero_iff 1 (x := (n i : ℝ))).mpr ⟨n i, by simp⟩
  rw [AddCircle.coe_add, this, add_zero]

theorem mFourier_toUnitAddTorus (m : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier m (toUnitAddTorus x) = (𝐞 (∑ i, (m i : ℝ) * x i) : ℂ) := by
  simp only [toUnitAddTorus, UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

section FourierCoeff

def negCharCM (m : d → ℤ) : C((d → ℝ), ℂ) :=
  (UnitAddTorus.mFourier (-m)).comp
    ⟨toUnitAddTorus, continuous_pi fun i =>
      (AddCircle.continuous_mk' 1).comp (continuous_apply i)⟩

theorem norm_negCharCM (m : d → ℤ) (x : d → ℝ) : ‖negCharCM m x‖ = 1 := by
  simp only [negCharCM, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    UnitAddTorus.mFourier, norm_prod]
  simp only [fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem negCharCM_add_intVec (m : d → ℤ) (x : d → ℝ) (n : d → ℤ) :
    negCharCM m (x + intVec n) = negCharCM m x := by
  simp only [negCharCM, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    toUnitAddTorus_add_intVec]

theorem negCharCM_eq_fourierChar (m : d → ℤ) (x : d → ℝ) :
    negCharCM m x = (𝐞 (-∑ i, x i * (m i : ℝ)) : ℂ) := by
  simp only [negCharCM, ContinuousMap.comp_apply, ContinuousMap.coe_mk, toUnitAddTorus,
    UnitAddTorus.mFourier, Pi.neg_apply, fourier_coe_apply, Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem pi_Ioc_ae_eq_pi_Ico :
    {x : d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
      =ᵐ[(volume : Measure (d → ℝ))]
    Set.pi Set.univ (fun _ : d => Set.Ico (0 : ℝ) 1) := by
  have h1 : {x : d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
      = Set.pi Set.univ (fun _ : d => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [h1]
  exact (Measure.univ_pi_Ioc_ae_eq_Icc).trans (Measure.univ_pi_Ico_ae_eq_Icc).symm

theorem coe_basisFun_equivFun_symm (n : d → ℤ) :
    ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.symm n :
        span ℤ (Set.range (Pi.basisFun ℝ d))) : d → ℝ) = intVec n := by
  classical
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, SetLike.val_smul, Module.Basis.restrictScalars_apply,
    Pi.basisFun_apply]
  ext j
  simp only [intVec, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [zsmul_eq_mul]

theorem mFourierCoeff_eq_piFourierIntegral (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (hf_int : Integrable (⇑f) (volume : Measure (d → ℝ)))
    (F : C(UnitAddTorus d, ℂ))
    (hF : ∀ x : d → ℝ, F (toUnitAddTorus x) = periodize f x)
    (m : d → ℤ) :
    UnitAddTorus.mFourierCoeff F m = piFourierIntegral f (intVec m) := by
  classical

  set e : C((d → ℝ), ℂ) := negCharCM m with he_def
  let cubeIoc : Set (d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
  let cubeIcc : Set (d → ℝ) := Set.Icc (0 : d → ℝ) 1
  have hcubeIoc_meas : MeasurableSet cubeIoc :=
    MeasurableSet.univ_pi' fun _ => measurableSet_Ioc
  have hcubeIcc_compact : IsCompact cubeIcc := isCompact_Icc
  have hcubeIoc_sub : cubeIoc ⊆ cubeIcc := fun x hx =>
    ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  have hcubeIoc_vol : (volume : Measure (d → ℝ)) cubeIoc = 1 := by
    have : cubeIoc = Set.pi Set.univ (fun _ : d => Set.Ioc (0 : ℝ) 1) := by
      ext x; simp [cubeIoc]
    rw [this]
    simp [volume_pi, Measure.pi_pi, Real.volume_Ioc]
  have hcubeIoc_vol' : (volume : Measure (d → ℝ)).real cubeIoc = 1 := by
    simp [Measure.real, hcubeIoc_vol]

  let G : (d → ℤ) → C((d → ℝ), ℂ) := fun n => e * f.comp (ContinuousMap.addRight (intVec n))
  have hG_eq : ∀ n x, G n x = e x * f (x + intVec n) := fun n x => rfl

  have hG_intOn : ∀ n, IntegrableOn (G n) cubeIoc volume := fun n =>
    ((G n).continuous.continuousOn.integrableOn_compact hcubeIcc_compact).mono_set hcubeIoc_sub

  let hK : Compacts (d → ℝ) := ⟨cubeIcc, hcubeIcc_compact⟩
  have neK : ∀ n x, ‖G n x‖ = ‖f (x + intVec n)‖ := fun n x => by
    rw [hG_eq, norm_mul, norm_negCharCM, one_mul]
  have hG_sum_int : Summable fun n => ∫ x in cubeIoc, ‖G n x‖ := by
    refine (hf hK).of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_)
    calc ∫ x in cubeIoc, ‖G n x‖
        ≤ ∫ _ in cubeIoc, ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict hK‖ := by
          refine setIntegral_mono_on (hG_intOn n).norm
            (integrableOn_const (by rw [hcubeIoc_vol]; exact ENNReal.one_ne_top))
            hcubeIoc_meas (fun x hx => ?_)
          rw [neK]
          have h := ((f.comp (ContinuousMap.addRight (intVec n))).restrict hK
            ).norm_coe_le_norm ⟨x, hcubeIoc_sub hx⟩
          simpa only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
            ContinuousMap.coe_addRight] using h
      _ = ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict hK‖ := by
          rw [setIntegral_const, hcubeIoc_vol', one_smul]

  have hef_int : Integrable (fun v => e v * f v) volume :=
    hf_int.bdd_mul (c := 1) e.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => (norm_negCharCM m x).le)

  haveI : VAddInvariantMeasure ↥(span ℤ (Set.range ⇑(Pi.basisFun ℝ d))) (d → ℝ) volume :=
    inferInstanceAs (VAddInvariantMeasure
      (span ℤ (Set.range ⇑(Pi.basisFun ℝ d))).toAddSubgroup (d → ℝ) volume)
  have hFD := ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ d) (volume : Measure (d → ℝ))
  rw [ZSpan.fundamentalDomain_pi_basisFun] at hFD
  let φ : (d → ℤ) ≃ ↥(span ℤ (Set.range ⇑(Pi.basisFun ℝ d))) :=
    (((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun).symm.toEquiv
  have hφ : ∀ n : d → ℤ, (↑(φ n) : d → ℝ) = intVec n := fun n =>
    coe_basisFun_equivFun_symm n

  calc UnitAddTorus.mFourierCoeff F m
      = ∫ x in cubeIoc, UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle))
          • F (fun i => x i) := by
        rw [UnitAddTorus.mFourierCoeff_eq_integral F m 0]
        congr 1
        · ext x; simp [cubeIoc]
    _ = ∫ x in cubeIoc, e x * periodize (⇑f) x := by
        refine setIntegral_congr_fun hcubeIoc_meas fun x _ => ?_
        rw [smul_eq_mul, ← hF x]
        rfl
    _ = ∫ x in cubeIoc, ∑' n : d → ℤ, G n x := by
        refine setIntegral_congr_fun hcubeIoc_meas fun x _ => ?_
        simp only [hG_eq, periodize, ← tsum_mul_left]
    _ = ∑' n : d → ℤ, ∫ x in cubeIoc, G n x := by
        rw [← integral_tsum_of_summable_integral_norm hG_intOn hG_sum_int]
    _ = ∑' n : d → ℤ, ∫ x in cubeIoc, (fun v => e v * f v) (x + intVec n) := by
        refine tsum_congr fun n => setIntegral_congr_fun hcubeIoc_meas fun x _ => ?_
        rw [hG_eq, ← negCharCM_add_intVec m x n]
    _ = ∑' n : d → ℤ, ∫ x in Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1),
          (fun v => e v * f v) (x + intVec n) := by
        exact tsum_congr fun n => setIntegral_congr_set pi_Ioc_ae_eq_pi_Ico
    _ = ∑' g : ↥(span ℤ (Set.range ⇑(Pi.basisFun ℝ d))),
          ∫ x in Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1),
          (fun v => e v * f v) (g +ᵥ x) := by
        rw [← φ.tsum_eq]
        refine tsum_congr fun n => setIntegral_congr_fun
          (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun x _ => ?_
        congr 1
        show x + intVec n = (↑(φ n) : d → ℝ) + x
        rw [hφ, add_comm]
    _ = ∫ v, e v * f v := by
        exact (hFD.integral_eq_tsum'' (fun v => e v * f v) hef_int).symm
    _ = piFourierIntegral (⇑f) (intVec m) := by
        unfold piFourierIntegral intVec
        congr 1
        ext v
        rw [mul_comm, negCharCM_eq_fourierChar]

end FourierCoeff

theorem isOpenQuotientMap_toUnitAddTorus :
    IsOpenQuotientMap (toUnitAddTorus (d := d)) := by
  have h : toUnitAddTorus (d := d) = Pi.map (fun _ : d => ((↑·) : ℝ → UnitAddCircle)) := by
    ext x i; rfl
  rw [h]
  exact IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem toUnitAddTorus_surjective : Function.Surjective (toUnitAddTorus (d := d)) :=
  (isOpenQuotientMap_toUnitAddTorus (d := d)).surjective

theorem toUnitAddTorus_eq_iff (x y : d → ℝ) :
    toUnitAddTorus x = toUnitAddTorus y ↔ ∃ n : d → ℤ, y = x + intVec n := by
  constructor
  · intro hxy
    have hcoord : ∀ i, ∃ k : ℤ, y i - x i = k := fun i => by
      have hi0 : (y i : AddCircle (1:ℝ)) - (x i : AddCircle (1:ℝ)) = 0 :=
        sub_eq_zero.mpr (congrFun hxy i).symm
      have hi : ((y i - x i : ℝ) : AddCircle (1:ℝ)) = 0 := by
        rwa [AddCircle.coe_sub]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp hi
      exact ⟨k, by rw [← hk]; simp⟩
    refine ⟨fun i => (hcoord i).choose, ?_⟩
    ext i
    have := (hcoord i).choose_spec
    simp only [intVec, Pi.add_apply]
    linarith [this]
  · rintro ⟨n, rfl⟩
    exact (toUnitAddTorus_add_intVec x n).symm

theorem periodize_eq_of_toUnitAddTorus_eq (f : (d → ℝ) → ℂ) {x y : d → ℝ}
    (hxy : toUnitAddTorus x = toUnitAddTorus y) :
    periodize f x = periodize f y := by
  obtain ⟨n, rfl⟩ := (toUnitAddTorus_eq_iff x y).mp hxy
  exact (periodize_add_intVec f x n).symm

private def localPeriodSummable (f : C((d → ℝ), ℂ)) : Prop :=
  ∀ K : Compacts (d → ℝ), Summable fun n : d → ℤ =>
    ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict (K : Set (d → ℝ))‖

section PeriodizeLift

set_option maxHeartbeats 16000000

def periodizeCM (f : C((d → ℝ), ℂ))
    (hf : localPeriodSummable f) :
    C((d → ℝ), ℂ) :=
  ∑' n : d → ℤ, f.comp (ContinuousMap.addRight (intVec n))

theorem periodizeCM_apply (f : C((d → ℝ), ℂ))
    (hf : localPeriodSummable f)
    (x : d → ℝ) :
    periodizeCM f hf x = periodize (⇑f) x := by
  have hsum : Summable (fun n : d → ℤ => f.comp (ContinuousMap.addRight (intVec n))) :=
    ContinuousMap.summable_of_locally_summable_norm hf
  unfold periodizeCM periodize
  rw [← ContinuousMap.tsum_apply hsum x]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight]

def periodizeLiftFun (f : C((d → ℝ), ℂ))
    (hf : localPeriodSummable f) :
    UnitAddTorus d → ℂ :=
  fun z => periodizeCM f hf (Function.surjInv toUnitAddTorus_surjective z)

theorem periodizeLiftFun_toUnitAddTorus (f : C((d → ℝ), ℂ))
    (hf : localPeriodSummable f)
    (x : d → ℝ) :
    periodizeLiftFun f hf (toUnitAddTorus x) = periodize (⇑f) x := by
  have hfib : toUnitAddTorus (Function.surjInv toUnitAddTorus_surjective
      (toUnitAddTorus (d := d) x)) = toUnitAddTorus x :=
    Function.surjInv_eq toUnitAddTorus_surjective (toUnitAddTorus x)
  calc periodizeLiftFun f hf (toUnitAddTorus x)
      = periodizeCM f hf (Function.surjInv toUnitAddTorus_surjective (toUnitAddTorus x)) := rfl
    _ = periodize (⇑f) (Function.surjInv toUnitAddTorus_surjective (toUnitAddTorus x)) :=
        periodizeCM_apply f hf _
    _ = periodize (⇑f) x := periodize_eq_of_toUnitAddTorus_eq (⇑f) hfib

def periodizeLift (f : C((d → ℝ), ℂ))
    (hf : localPeriodSummable f) :
    C(UnitAddTorus d, ℂ) where
  toFun := periodizeLiftFun f hf
  continuous_toFun := by
    rw [(isOpenQuotientMap_toUnitAddTorus (d := d)).isQuotientMap.continuous_iff]
    have hcomp : periodizeLiftFun f hf ∘ toUnitAddTorus = ⇑(periodizeCM f hf) := by
      ext x
      rw [Function.comp_apply, periodizeLiftFun_toUnitAddTorus f hf x, periodizeCM_apply f hf]
    rw [hcomp]
    exact (periodizeCM f hf).continuous

theorem periodizeLift_toUnitAddTorus (f : C((d → ℝ), ℂ))
    (hf : localPeriodSummable f)
    (x : d → ℝ) :
    periodizeLift f hf (toUnitAddTorus x) = periodize (⇑f) x :=
  periodizeLiftFun_toUnitAddTorus f hf x

end PeriodizeLift

theorem periodize_eq_tsum_piFourierIntegral (f : C((d → ℝ), ℂ))
    (hf : localPeriodSummable f)
    (hf_int : Integrable (⇑f) (volume : Measure (d → ℝ)))
    (hFf : Summable fun m : d → ℤ => piFourierIntegral f (intVec m))
    (x : d → ℝ) :
    periodize f x
      = ∑' m : d → ℤ, piFourierIntegral f (intVec m)
          * UnitAddTorus.mFourier m (toUnitAddTorus x) := by
  set F := periodizeLift f hf
  rw [← periodizeLift_toUnitAddTorus f hf x]
  have hcoeff : ∀ m, UnitAddTorus.mFourierCoeff F m = piFourierIntegral f (intVec m) :=
    mFourierCoeff_eq_piFourierIntegral f hf hf_int F (periodizeLift_toUnitAddTorus f hf)
  have hsum : Summable (UnitAddTorus.mFourierCoeff F) := by
    refine hFf.congr fun m => ?_
    exact (hcoeff m).symm
  have := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (toUnitAddTorus x)).tsum_eq
  rw [← this]
  refine tsum_congr fun m => ?_
  rw [hcoeff m, smul_eq_mul]

section Schwartz

theorem finrank_span_basisFun :
    Module.finrank ℤ (span ℤ (Set.range (Pi.basisFun ℝ d)) : Submodule ℤ (d → ℝ))
      = Fintype.card d :=
  Module.finrank_eq_card_basis ((Pi.basisFun ℝ d).restrictScalars ℤ)

theorem summable_norm_intVec_inv_pow {N : ℕ} (hN : Fintype.card d < N) :
    Summable fun n : d → ℤ => ‖intVec (d := d) n‖⁻¹ ^ N := by
  have hfin : Module.finrank ℤ
      (span ℤ (Set.range (Pi.basisFun ℝ d)) : Submodule ℤ (d → ℝ)) < N := by
    rw [finrank_span_basisFun]; exact hN
  have hL : Summable fun z : span ℤ (Set.range (Pi.basisFun ℝ d)) => ‖(z : d → ℝ)‖⁻¹ ^ N :=
    ZLattice.summable_norm_pow_inv (span ℤ (Set.range (Pi.basisFun ℝ d))) N hfin
  have := ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.toEquiv.symm.summable_iff
    (f := fun z : span ℤ (Set.range (Pi.basisFun ℝ d)) => ‖(z : d → ℝ)‖⁻¹ ^ N))).mpr hL
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv_symm]
  congr 2
  exact congrArg norm (coe_basisFun_equivFun_symm n)

theorem summable_norm_schwartz_intVec (g : SchwartzMap (d → ℝ) ℂ) :
    Summable fun n : d → ℤ => ‖(g : (d → ℝ) → ℂ) (intVec n)‖ := by
  set N := Fintype.card d + 1
  have hsum := summable_norm_intVec_inv_pow (d := d) (N := N) (Nat.lt_succ_self _)
  refine Summable.of_norm_bounded_eventually
    (g := fun n : d → ℤ => SchwartzMap.seminorm ℝ N 0 g * ‖intVec (d := d) n‖⁻¹ ^ N)
    (hsum.mul_left _) ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (s := {(0 : d → ℤ)}) (Set.finite_singleton _) ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hn ⊢
  by_contra hne
  apply hn
  have hne0 : intVec (d := d) n ≠ 0 := by
    intro h; apply hne; ext i
    have := congrFun h i
    simpa [intVec] using this
  have hpos : (0 : ℝ) < ‖intVec (d := d) n‖ ^ N := pow_pos (norm_pos_iff.mpr hne0) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ g N (intVec n)
  rw [norm_norm, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact hdecay

theorem one_add_norm_intVec_le {R : ℝ} (hR : 0 ≤ R) {x : d → ℝ}
    (hx : x ∈ Metric.closedBall (0 : d → ℝ) R) (n : d → ℤ) :
    1 + ‖intVec (d := d) n‖ ≤ (1 + R) * (1 + ‖x + intVec n‖) := by
  have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have h1 : ‖intVec (d := d) n‖ ≤ ‖x‖ + ‖x + intVec n‖ := by
    calc ‖intVec (d := d) n‖ = ‖x + intVec n - x‖ := by ring_nf
      _ ≤ ‖x + intVec n‖ + ‖x‖ := norm_sub_le _ _
      _ = ‖x‖ + ‖x + intVec n‖ := add_comm _ _
  calc 1 + ‖intVec (d := d) n‖
      ≤ 1 + (R + ‖x + intVec n‖) := by linarith [h1, hxR]
    _ ≤ (1 + R) * (1 + ‖x + intVec n‖) := by
        have h2 : 0 ≤ ‖x + intVec (d := d) n‖ := norm_nonneg _
        nlinarith

theorem summable_one_add_norm_intVec_inv_pow {N : ℕ} (hN : Fintype.card d < N) :
    Summable fun n : d → ℤ => (1 + ‖intVec (d := d) n‖)⁻¹ ^ N := by
  have hsum := summable_norm_intVec_inv_pow (d := d) hN
  refine Summable.of_norm_bounded_eventually (g := fun n => ‖intVec (d := d) n‖⁻¹ ^ N) hsum ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (s := {(0 : d → ℤ)}) (Set.finite_singleton _) ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hn ⊢
  by_contra hne
  apply hn
  have hne0 : intVec (d := d) n ≠ 0 := by
    intro h; apply hne; ext i
    have := congrFun h i
    simpa [intVec] using this
  have h1 : (1 + ‖intVec (d := d) n‖)⁻¹ ^ N ≤ ‖intVec (d := d) n‖⁻¹ ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    exact inv_anti₀ (norm_pos_iff.mpr hne0) (by linarith [norm_nonneg (intVec (d := d) n)])
  rw [Real.norm_of_nonneg (by positivity)]
  exact h1

theorem summable_norm_restrict_schwartz_comp_addRight
    (h : SchwartzMap (d → ℝ) ℂ) (K : Compacts (d → ℝ)) :
    Summable fun n : d → ℤ =>
      ‖(h.toContinuousMap.comp (ContinuousMap.addRight (intVec n))).restrict K‖ := by
  classical
  set N := Fintype.card d + 1

  set C := (2:ℝ)^N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h
    with hC_def
  have hC_nonneg : 0 ≤ C := mul_nonneg (by positivity) (apply_nonneg _ _)

  have hKbdd : Bornology.IsBounded (K : Set (d → ℝ)) := K.2.isBounded
  obtain ⟨R, hR_nonneg, hKR⟩ : ∃ R ≥ 0, (K : Set (d → ℝ)) ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hKR⟩ := hKbdd.subset_closedBall 0
    exact ⟨max R 0, le_max_right _ _,
      hKR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hsum := summable_one_add_norm_intVec_inv_pow (d := d) (N := N) (Nat.lt_succ_self _)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (hsum.mul_left (C * (1 + R)^N))
  have hbound : ∀ x ∈ (K : Set (d → ℝ)),
      ‖h (x + intVec n)‖ ≤ C * (1 + R)^N * (1 + ‖intVec (d := d) n‖)⁻¹ ^ N := by
    intro x hxK
    have hxR := hKR hxK
    have hdecay := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0))
      (k := N) (n := 0) le_rfl le_rfl h (x + intVec n)
    rw [norm_iteratedFDeriv_zero] at hdecay
    have huni := one_add_norm_intVec_le hR_nonneg hxR n
    have hpos : (0:ℝ) < (1 + ‖x + intVec (d := d) n‖)^N := pow_pos (by positivity) _
    have hpos' : (0:ℝ) < (1 + ‖intVec (d := d) n‖)^N := pow_pos (by positivity) _
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos']
    calc ‖h (x + intVec n)‖ * (1 + ‖intVec (d := d) n‖) ^ N
        ≤ ‖h (x + intVec n)‖ * ((1 + R) * (1 + ‖x + intVec n‖)) ^ N := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact pow_le_pow_left₀ (by positivity) huni N
      _ = (1 + R)^N * (‖h (x + intVec n)‖ * (1 + ‖x + intVec n‖) ^ N) := by
          rw [mul_pow]; ring
      _ ≤ (1 + R)^N * C := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [mul_comm]
          exact hdecay
      _ = C * (1 + R)^N := mul_comm _ _
  refine (ContinuousMap.norm_le _ ?_).mpr ?_
  · exact mul_nonneg (mul_nonneg hC_nonneg (by positivity)) (by positivity)
  · rintro ⟨x, hxK⟩
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight]
    exact hbound x hxK

abbrev euclideanToPi : EuclideanSpace ℝ d ≃L[ℝ] (d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)

theorem piFourierIntegral_eq_fourier_euclidean (h : SchwartzMap (d → ℝ) ℂ) (ξ : d → ℝ) :
    piFourierIntegral (⇑h) ξ
      = (𝓕 (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h)
            : EuclideanSpace ℝ d → ℂ)) (toLp 2 ξ) := by
  unfold piFourierIntegral
  rw [Real.fourier_eq]
  rw [← MeasurePreserving.integral_comp (PiLp.volume_preserving_ofLp d)
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    Circle.smul_def, smul_eq_mul]
  have hinner : ∑ i, (ofLp v) i * ξ i = ⟪v, toLp 2 ξ⟫_ℝ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [← hinner, mul_comm]
  rfl

theorem summable_piFourierIntegral_schwartz_intVec (h : SchwartzMap (d → ℝ) ℂ) :
    Summable fun m : d → ℤ => piFourierIntegral (⇑h) (intVec m) := by
  let h' : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h
  let g' : SchwartzMap (EuclideanSpace ℝ d) ℂ := 𝓕 h'
  let g : SchwartzMap (d → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)).symm g'
  have hg : ∀ ξ : d → ℝ, piFourierIntegral (⇑h) ξ = g ξ := fun ξ => by
    rw [piFourierIntegral_eq_fourier_euclidean h ξ]
    simp only [g, g', h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  simp_rw [hg]
  exact (summable_norm_schwartz_intVec g).of_norm

theorem SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral
    (h : SchwartzMap (d → ℝ) ℂ) (x : d → ℝ) :
    ∑' n : d → ℤ, h (x + intVec n)
      = ∑' m : d → ℤ, piFourierIntegral h (intVec m) * (𝐞 (∑ i, (m i : ℝ) * x i) : ℂ) := by
  have := PiPoissonSummation.periodize_eq_tsum_piFourierIntegral h.toContinuousMap
    (summable_norm_restrict_schwartz_comp_addRight h) h.integrable
    (summable_piFourierIntegral_schwartz_intVec h) x
  simp only [periodize, mFourier_toUnitAddTorus] at this ⊢
  exact this

theorem SchwartzMap.tsum_intVec_eq_tsum_piFourierIntegral (h : SchwartzMap (d → ℝ) ℂ) :
    ∑' n : d → ℤ, h (intVec n) = ∑' m : d → ℤ, piFourierIntegral h (intVec m) := by
  have := PiPoissonSummation.SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral h 0
  simpa using this

end Schwartz

end PiPoissonSummation

end

section Euclidean
open PiPoissonSummation

theorem recoveredProof_1709ca6f9d1252d4a35ef056ec487361
    {ι : Type*} [Fintype ι] (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (x : EuclideanSpace ℝ ι) :
    ∑' n : ι → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : ι → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) *
        (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (n i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) := by

  set h : SchwartzMap (ι → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := ι)).symm f with hh
  have hh_apply : ∀ v : ι → ℝ, h v = f (toLp 2 v) := fun v => by
    simp only [hh, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  have hback : SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := ι)) h = f := by
    ext v
    simp only [hh, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  have key := PiPoissonSummation.SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral h (ofLp x)

  have hL : ∀ n : ι → ℤ, h (ofLp x + intVec n) = f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) := by
    intro n
    rw [hh_apply, WithLp.toLp_add, WithLp.toLp_ofLp]
    rfl

  have hR : ∀ m : ι → ℤ, piFourierIntegral (⇑h) (intVec m)
      = 𝓕 f (WithLp.toLp 2 (fun i ↦ (m i : ℝ))) := by
    intro m
    rw [piFourierIntegral_eq_fourier_euclidean h (intVec m), hback]
    rfl
  have hχ : ∀ m : ι → ℤ, (𝐞 (∑ i, (m i : ℝ) * (ofLp x) i) : ℂ)
      = (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (m i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) := by
    intro m
    congr 2
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  simp only [hL, hR, hχ] at key
  exact key

end Euclidean

end S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace
end P2MW
export P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace (recoveredProof_1709ca6f9d1252d4a35ef056ec487361)


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform InnerProductSpace SchwartzMap
theorem SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace
    {ι : Type*} [Fintype ι] (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    ∑' n : ι → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : ι → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) *
        (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (n i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) := by p2m_exact_reverting @recoveredProof_1709ca6f9d1252d4a35ef056ec487361

end LocalPoissonProof4
section LocalPoissonProof5

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open MeasureTheory Real Complex Set TopologicalSpace Topology Submodule WithLp
open scoped FourierTransform InnerProductSpace

noncomputable section

namespace PiPoissonSummation

variable {d : Type*} [Fintype d]

def intVec (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)

def piFourierIntegral (f : (d → ℝ) → ℂ) (ξ : d → ℝ) : ℂ :=
  ∫ v, f v * (𝐞 (-∑ i, v i * ξ i) : ℂ) ∂(volume : Measure (d → ℝ))

abbrev euclideanToPi : EuclideanSpace ℝ d ≃L[ℝ] (d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)

theorem piFourierIntegral_eq_fourier_euclidean (h : SchwartzMap (d → ℝ) ℂ) (ξ : d → ℝ) :
    piFourierIntegral (⇑h) ξ
      = (𝓕 (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h)
            : EuclideanSpace ℝ d → ℂ)) (toLp 2 ξ) := by
  unfold piFourierIntegral
  rw [Real.fourier_eq]
  rw [← MeasurePreserving.integral_comp (PiLp.volume_preserving_ofLp d)
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    Circle.smul_def, smul_eq_mul]
  have hinner : ∑ i, (ofLp v) i * ξ i = ⟪v, toLp 2 ξ⟫_ℝ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [← hinner, mul_comm]
  rfl

theorem SchwartzMap.tsum_intVec_eq_tsum_piFourierIntegral (h : SchwartzMap (d → ℝ) ℂ) :
    ∑' n : d → ℤ, h (intVec n) = ∑' m : d → ℤ, piFourierIntegral h (intVec m) := by
  set f : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h with hf
  have key := _root_.SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace f 0
  simp only [zero_add, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at key
  have hL : ∀ n : d → ℤ, f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) = h (intVec n) := fun n => by
    simp only [hf, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  have hR : ∀ m : d → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = piFourierIntegral h (intVec m) :=
    fun m => by rw [piFourierIntegral_eq_fourier_euclidean h (intVec m)]; rfl
  simp only [hL, hR] at key
  exact key

theorem SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral (h : SchwartzMap (d → ℝ) ℂ)
    (x : d → ℝ) :
    ∑' n : d → ℤ, h (x + intVec n)
      = ∑' m : d → ℤ, piFourierIntegral h (intVec m) * (𝐞 (∑ i, (m i : ℝ) * x i) : ℂ) := by
  set f : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h with hf
  have key := _root_.SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace f (toLp 2 x)
  have hL : ∀ n : d → ℤ, f (toLp 2 x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) = h (x + intVec n) :=
    fun n => by
    simp only [hf, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ← WithLp.toLp_add]
    rfl
  have hR : ∀ m : d → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = piFourierIntegral h (intVec m) :=
    fun m => by rw [piFourierIntegral_eq_fourier_euclidean h (intVec m)]; rfl
  have hχ : ∀ m : d → ℤ,
      (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (m i : ℝ)) : EuclideanSpace ℝ d), toLp 2 x⟫_ℝ : ℂ)
        = (𝐞 (∑ i, (m i : ℝ) * x i) : ℂ) := by
    intro m
    congr 2
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  simp only [hL, hR, hχ] at key
  exact key

end PiPoissonSummation

section LatticeTranslate

open PiPoissonSummation LinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]

theorem recoveredProof_183e4373e21954389be2930ff79780e8
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : SchwartzMap V ℂ) (t : V) :
    ∑' x : L, f (t + x) =
      (ZLattice.covolume L μ : ℂ)⁻¹ *
        ∑' y : LinearMap.BilinForm.dualSubmodule B.flip L,
          VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ) := by
  classical

  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let bZ : Module.Basis ι ℤ L := Module.Free.chooseBasis ℤ L
  let b : Module.Basis ι ℝ V := bZ.ofZLatticeBasis ℝ L
  have hb : ∀ i, b i = (bZ i : V) := fun i => bZ.ofZLatticeBasis_apply ℝ L i

  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv
  have hA : ∀ v : ι → ℝ, A v = ∑ i, v i • b i := fun v => by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_symm_apply]
  have hA_intVec : ∀ n : ι → ℤ, A (intVec n) = ((bZ.equivFun.symm n : L) : V) := fun n => by
    rw [hA, Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, hb]
    exact Int.cast_smul_eq_zsmul ℝ (n i) _

  set s : ι → ℝ := A.symm t with hs
  have ht : t = A s := (A.apply_symm_apply t).symm

  let h : SchwartzMap (ι → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A f
  have hh : ∀ v, h v = f (A v) := fun v => by
    simp only [h, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

  have hLHS : ∑' x : L, f (t + x) = ∑' n : ι → ℤ, h (s + intVec n) := by
    rw [← bZ.equivFun.symm.toEquiv.tsum_eq]
    refine tsum_congr fun n => ?_
    rw [hh, A.map_add, ← ht, hA_intVec]
    rfl

  have hP : ∑' n : ι → ℤ, h (s + intVec n)
      = ∑' m : ι → ℤ, piFourierIntegral h (intVec m) * (𝐞 (∑ i, (m i : ℝ) * s i) : ℂ) :=
    PiPoissonSummation.SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral h s

  set ν : MeasureTheory.Measure V := Measure.map A volume with hν_def
  haveI : ν.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  set c : NNReal := Measure.addHaarScalarFactor μ ν with hc_def
  have hμν : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν

  have hνF : ν (ZSpan.fundamentalDomain b) = 1 := by
    rw [hν_def, Measure.map_apply A.continuous.measurable (ZSpan.fundamentalDomain_measurableSet b),
      ← A.image_symm_eq_preimage]
    have : (A.symm : V → ι → ℝ) '' ZSpan.fundamentalDomain b
        = ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) := by
      rw [show ((A.symm : V → ι → ℝ)) = ⇑(b.equivFun : V ≃ₗ[ℝ] ι → ℝ) from rfl,
        ZSpan.map_fundamentalDomain]
      congr 1
      ext i j
      simp [Module.Basis.map_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [this, ZSpan.fundamentalDomain_pi_basisFun]
    simp [volume_pi, Measure.pi_pi, Real.volume_Ico]
  have hμF : μ (ZSpan.fundamentalDomain b) = c := by
    rw [hμν, Measure.smul_apply, hνF, ENNReal.smul_def, smul_eq_mul, mul_one]
  have hcov : ZLattice.covolume L μ = μ.real (ZSpan.fundamentalDomain b) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain bZ μ)
  have hc : (c : ℝ) = ZLattice.covolume L μ := by
    rw [hcov, Measure.real, hμF, ENNReal.coe_toReal]
  have hc_ne : (c : ℝ) ≠ 0 := by rw [hc]; exact ZLattice.covolume_ne_zero L μ

  let bd : Module.Basis ι ℝ V := B.flip.dualBasis hB.flip b
  have hbd : ∀ i j, B (b j) (bd i) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB.flip b i j
    simpa only [bd, LinearMap.BilinForm.flip_apply] using this
  have hLd : LinearMap.BilinForm.dualSubmodule B.flip L = span ℤ (Set.range bd) := by
    rw [← bZ.ofZLatticeBasis_span ℝ L]
    exact LinearMap.BilinForm.dualSubmodule_span_of_basis B.flip hB.flip b
  let ψ : (ι → ℤ) ≃ LinearMap.BilinForm.dualSubmodule B.flip L :=
    ((bd.restrictScalars ℤ).equivFun.symm.toEquiv).trans (LinearEquiv.ofEq _ _ hLd.symm).toEquiv
  have hψ : ∀ k : ι → ℤ, ((ψ k : _) : V) = ∑ i, (k i : ℝ) • bd i := fun k => by
    simp only [ψ, Equiv.trans_apply, LinearEquiv.coe_toEquiv, LinearEquiv.coe_ofEq_apply]
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, Module.Basis.restrictScalars_apply]
    exact (Int.cast_smul_eq_zsmul ℝ (k i) _).symm

  have hpair : ∀ (v : ι → ℝ) (k : ι → ℤ),
      B (A v) (∑ i, (k i : ℝ) • bd i) = ∑ i, v i * (k i : ℝ) := fun v k => by
    rw [hA]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hbd, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

  have hterm : ∀ k : ι → ℤ, piFourierIntegral h (intVec k)
      = ((ZLattice.covolume L μ : ℝ) : ℂ)⁻¹ * VectorFourier.fourierIntegral 𝐞 μ B f (ψ k) := by
    intro k
    have h1 : piFourierIntegral h (intVec k)
        = ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (A v) := by
      unfold piFourierIntegral
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [hh, hψ, hpair, intVec]
    have h2 : ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (A v)
        = ∫ w, f w * (𝐞 (-(B w (ψ k))) : ℂ) ∂ν := by
      have := MeasurableEmbedding.integral_map A.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (μ := volume)
      simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at this
      rw [hν_def, this]
    have h3 : VectorFourier.fourierIntegral 𝐞 μ B f (ψ k)
        = (c : ℝ) • ∫ w, f w * (𝐞 (-(B w (ψ k))) : ℂ) ∂ν := by
      rw [VectorFourier.fourierIntegral, hμν, integral_smul_nnreal_measure, NNReal.smul_def]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [Circle.smul_def, smul_eq_mul, mul_comm]
    rw [h1, h2, h3, ← hc, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hc_ne, Complex.ofReal_one, one_mul]

  have hphase : ∀ k : ι → ℤ,
      (𝐞 (∑ i, (k i : ℝ) * s i) : ℂ) = (𝐞 (B t (ψ k)) : ℂ) := fun k => by
    rw [ht, hψ, hpair]
    congr 2
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

  rw [hLHS, hP, ← ψ.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [hterm, hphase, mul_assoc]

end LatticeTranslate

end

end S_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
end P2MW
export P2MW.S_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral (recoveredProof_183e4373e21954389be2930ff79780e8)


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform SchwartzMap
theorem ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : 𝓢(V, ℂ)) (t : V) :
    ∑' x : L, f (t + x) =
      (ZLattice.covolume L μ : ℂ)⁻¹ *
        ∑' y : LinearMap.BilinForm.dualSubmodule B.flip L,
          VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ) := by p2m_exact_reverting @recoveredProof_183e4373e21954389be2930ff79780e8

end LocalPoissonProof5


namespace AFT
end AFT

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.CoherentDecoder
end InfoLossLAR.WorstCase.CoherentDecoder

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport
end InfoLossLAR.WorstCase.GaussianLatticeTransport

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

/- Helper module Solutions.RegevBridgeGaussianLatticeTransport. -/
section P2MDyadicModule0

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

end P2MDyadicModule0

/- Helper module Solutions.RegevBridgeGaussianLatticeScaling. -/
section P2MDyadicModule1

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

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeGaussianCosetGeometry. -/
section P2MDyadicModule2

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

/-- Canonical input-basis representative of each public residue vector. -/
def lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) : lattice :=
  basis.equivFun.symm (fun index => ((color index).val : ℤ))

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

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeGaussianCosetPartition. -/
section P2MDyadicModule3

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

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule4

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

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeGaussianPoissonSeries. -/
section P2MDyadicModule5

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

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeLatticeGaussianSummable. -/
section P2MDyadicModule6

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

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeLatticeGaussianCosetSummable. -/
section P2MDyadicModule7

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

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeLatticeFourierCoordinates. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier

open GaussianProjection.CosetGeometry RegevLWE.GaussConv

open scoped BigOperators FourierTransform

noncomputable section

variable {dimension : ℕ}

abbrev CoordinateSpace := EuclideanSpace ℝ (Fin dimension)

/-- The actual fine-lattice point represented by one quotient color in
L/modulus, using the original integral basis and no arbitrary section. -/
def gridPoint (modulus : ℕ) [NeZero modulus]
    (lattice : Submodule ℤ (CoordinateSpace (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (color : Fin dimension → ZMod modulus) :
    CoordinateSpace (dimension:=dimension) :=
  (modulus : ℝ)⁻¹ • (GaussianProjection.CosetGeometry.lift modulus lattice basis color : CoordinateSpace (dimension:=dimension))

end

end InfoLossLAR.WorstCase.FiniteLatticeFourier

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeGaussianFiniteFourier. -/
section P2MDyadicModule9

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

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeLatticeGaussianMass. -/
section P2MDyadicModule10

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

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeLatticeGaussianCosetMax. -/
section P2MDyadicModule11

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

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeLatticeGaussianTail. -/
section P2MDyadicModule12

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

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeLatticeGaussianSeparation. -/
section P2MDyadicModule14

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

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeLatticeResidueFiber. -/
section P2MDyadicModule15

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

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeLatticeResidueFiberReal. -/
section P2MDyadicModule16

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

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeFineGridGaussian. -/
section P2MDyadicModule17

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

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgePeriodizedTruncation. -/
section P2MDyadicModule18

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

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeFineGridGaussianTail. -/
section P2MDyadicModule19

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

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeFineGridInjectivity. -/
section P2MDyadicModule20

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

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeFineGridSquareMass. -/
section P2MDyadicModule21

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

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeTruncatedFiberNorm. -/
section P2MDyadicModule22

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

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeFineGridTruncatedNorm. -/
section P2MDyadicModule23

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

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeCoherentProjection. -/
section P2MDyadicModule24

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentProjection

open scoped BigOperators

noncomputable def normalized {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : E :=
  ‖v‖⁻¹ • v

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

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeGaussianPureComparison. -/
section P2MDyadicModule25

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

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeFiniteGaussianStates. -/
section P2MDyadicModule26

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- Actual complete periodized Gaussian amplitudes on the finite quotient,
before their physical global norm is removed. -/
def periodizedState (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width : ℝ) :
    EuclideanSpace ℂ (Fin dimension → ZMod modulus) :=
  WithLp.toLp 2 (fun color => (rhoCoset width lattice
    (FiniteLatticeFourier.gridPoint modulus lattice basis color) : ℂ))

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

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeFineGridNormalization. -/
section P2MDyadicModule27

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

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeHybridMeasurement. -/
section P2MDyadicModule28

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentDecoder

open scoped BigOperators

noncomputable section

/-- Retain the amplitudes in a final classical measurement event. -/
def retainEvent {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : EuclideanSpace ℂ α :=
  open Classical in WithLp.toLp 2 (fun value => if event value then state value else 0)

/-- Unnormalized Born mass, so the error statement also covers intermediate
states before normalization has separately been established. -/
def bornEvent {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : ℝ :=
  open Classical in ∑ value,if event value then ‖state value‖^2 else 0

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

end P2MDyadicModule28

/- Helper module Fiber. -/
section P2MDyadicModule29

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout

open InfoLossLAR.WorstCase

open GaussianPoissonSeries CoherentDecoder CoherentProjection

theorem event_fiber {A F : Type*} [Fintype F] [DecidableEq F] (q : A → F) (w : A → ℝ)
    (hs : Summable w) (hp : ∀ a, 0 ≤ w a) (E : F → Prop) :
    (∑ c, if E c then fiberMass q w c else 0) = ∑' a, if E (q a) then w a else 0 := by
  classical
  let g (a : A) := if E (q a) then w a else 0
  have h (c : F) : (if E c then fiberMass q w c else 0) = fiberMass q g c := by
    by_cases hc : E c
    · rw [if_pos hc]
      apply tsum_congr
      intro a
      by_cases he : q a=c <;> simp [g,he,hc]
    · rw [if_neg hc]
      symm
      unfold fiberMass
      have hz (a : A) : (if q a=c then g a else 0) = 0 := by
        by_cases he : q a=c <;> simp [g,he,hc]
      simp only [hz,tsum_zero]
  simp_rw [h]
  exact sum_fiberMass q g (summable_filtered_nonnegative w hs hp _) (by intro a; dsimp [g]; split <;> simp [hp])

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

theorem condition_error {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hb : 0 < b) (hd : 0 ≤ d) (hab : a ≤ b) (hcd : c ≤ d) :
    |a/b - (a+c)/(b+d)| ≤ d/(b+d) := by
  have hbd : 0 < b+d := by linarith
  have hden : 0 < b*(b+d) := mul_pos hb hbd
  have he : a/b - (a+c)/(b+d) = (a*d-b*c)/(b*(b+d)) := by
    field_simp
    ring
  rw [he, abs_div,abs_of_pos hden, div_le_div_iff₀ hden hbd]
  have h : |a*d-b*c| ≤ b*d := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg ha hd,mul_nonneg hb.le hc,
      mul_le_mul_of_nonneg_right hab hd, mul_le_mul_of_nonneg_left hcd hb.le]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_right h hbd.le

end GridReadout

end P2MDyadicModule29

/- Helper module Condition. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout

open InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

variable {A : Type*}

def mass (w : A → ℝ) (E : A → Prop) : ℝ := ∑' a, if E a then w a else 0

theorem mass_nonneg (w : A → ℝ) (hp : ∀ a, 0 ≤ w a) (E : A → Prop) : 0 ≤ mass w E :=
  tsum_nonneg fun a => by split <;> simp_all

theorem mass_mono (w : A → ℝ) (hs : Summable w) (hp : ∀ a, 0 ≤ w a) {E F : A → Prop}
    (h : ∀ a, E a → F a) : mass w E ≤ mass w F := by
  apply Summable.tsum_le_tsum _ (summable_filtered_nonnegative w hs hp E)
    (summable_filtered_nonnegative w hs hp F)
  intro a
  by_cases he : E a
  · simp [he,h a he]
  · simp [he]; split <;> simp [hp]

theorem mass_split (w : A → ℝ) (hs : Summable w) (hp : ∀ a, 0 ≤ w a) (E K : A → Prop) :
    mass w E = mass w (fun a => K a ∧ E a) + mass w (fun a => ¬K a ∧ E a) := by
  unfold mass
  trans (∑' a : A, ((if K a ∧ E a then w a else 0) + (if ¬K a ∧ E a then w a else 0)))
  · apply tsum_congr
    intro a
    by_cases he : E a <;> by_cases hk : K a <;> simp [he,hk]
  rw [(summable_filtered_nonnegative w hs hp (fun a => K a ∧ E a)).tsum_add
    (summable_filtered_nonnegative w hs hp (fun a => ¬K a ∧ E a))]
  congr 1 <;> (apply tsum_congr; intro a; split_ifs <;> simp_all)

theorem prob_cut (w : A → ℝ) (hs : Summable w) (hp : ∀ a, 0 ≤ w a) (K E : A → Prop)
    (τ : ℝ) (ht : τ<1) (htotal : 0 < ∑' a, w a) (hbig : (1-τ)*(∑' a, w a) ≤ mass w K) :
    |mass w (fun a => K a ∧ E a)/mass w K - mass w E/(∑' a, w a)| ≤ τ := by
  have hb := lt_of_lt_of_le (mul_pos (sub_pos.mpr ht) htotal) hbig
  have h₁ := mass_split w hs hp E K
  have h₂ := mass_split w hs hp (fun _ => True) K
  simp only [and_true] at h₂
  have hone : mass w (fun _ => True) = ∑' a, w a := by simp [mass]
  rw [hone] at h₂
  have hd := mass_nonneg w hp (fun a => ¬K a)
  have h₃ := condition_error (mass_nonneg w hp (fun a => K a ∧ E a))
    (mass_nonneg w hp (fun a => ¬K a ∧ E a)) hb hd
    (mass_mono w hs hp fun a h => h.1) (mass_mono w hs hp fun a h => h.1)
  rw [←h₁, ←h₂] at h₃
  apply h₃.trans
  rw [div_le_iff₀ htotal]
  nlinarith [h₂,hbig]

end

end GridReadout

end P2MDyadicModule30

/- Helper module CoeffMass. -/
section P2MDyadicModule31

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout

open InfoLossLAR.WorstCase IntegerBasis GaussianPoissonSeries RegevLWE.GaussConv

noncomputable section

variable {n : ℕ}

theorem coeff_mass_event (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (r : ℝ) (T : Finset (Fin n → ℤ)) :
    mass (fun x : inputLattice B hB => rho r (x : EuclideanSpace ℝ (Fin n)))
      (fun x => (integerBasis B hB).equivFun x ∈ T) / rhoCoset r (inputLattice B hB) 0 =
    ∑ z ∈ T, RegevSketch.coefficientMass B r z := by
  let e := (integerBasis B hB).equivFun.symm.toEquiv
  have hp (z : Fin n → ℤ) : rho r (e z : EuclideanSpace ℝ (Fin n)) = rhoInt r (B.mulVec z) := by
    change rho r ((integerBasis B hB).equivFun.symm z : EuclideanSpace ℝ (Fin n)) = _
    rw [coefficient_point]
    rfl
  have hden : rhoCoset r (inputLattice B hB) 0 = ∑' z : Fin n → ℤ, rhoInt r (B.mulVec z) := by
    simp only [rhoCoset,add_zero]
    rw [← e.tsum_eq (fun x : inputLattice B hB => rho r (x : EuclideanSpace ℝ (Fin n)))]
    exact tsum_congr hp
  unfold RegevSketch.coefficientMass
  rw [hden, ← Finset.sum_div]
  congr 1
  unfold mass
  trans ∑' x : inputLattice B hB, if (integerBasis B hB).equivFun x ∈ T then rho r (x : EuclideanSpace ℝ (Fin n)) else 0
  · apply tsum_congr; intro x; split_ifs <;> rfl
  rw [← e.tsum_eq (fun x : inputLattice B hB => if (integerBasis B hB).equivFun x ∈ T then rho r (x : EuclideanSpace ℝ (Fin n)) else 0)]
  have hx (z : Fin n → ℤ) : (integerBasis B hB).equivFun (e z) = z := LinearEquiv.apply_symm_apply _ _
  simp_rw [hx,hp]
  rw [tsum_eq_sum (s:=T) (fun z hz => if_neg hz)]
  simp

end

end GridReadout

end P2MDyadicModule31

/- Helper module Cofactor. -/
section P2MDyadicModule32

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout

open InfoLossLAR.WorstCase IntegerBasis

noncomputable section

variable {n M : ℕ} [NeZero M]

def cofactorSum (B : Matrix (Fin n) (Fin n) ℤ) : ℕ := ∑ i, ∑ j, (B.adjugate i j).natAbs

theorem coord_le_norm (B : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) (i : Fin n) :
    |((B.mulVec z i : ℤ) : ℝ)| ≤ ‖latVec B z‖ := PiLp.norm_apply_le (p:=2) (latVec B z) i

theorem coefficient_bound (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (z : Fin n → ℤ) (i : Fin n) :
    |(z i : ℝ)| ≤ (cofactorSum B : ℝ) * ‖latVec B z‖ := by
  have hid : B.adjugate.mulVec (B.mulVec z) = B.det • z := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hi := congrFun hid i
  change (∑ j, B.adjugate i j * B.mulVec z j) = B.det * z i at hi
  have hd : (1:ℤ) ≤ |B.det| := by have := abs_pos.mpr hB; omega
  have hd' : (1:ℝ) ≤ |(B.det:ℝ)| := by exact_mod_cast hd
  have hrow : (∑ j, (B.adjugate i j).natAbs) ≤ cofactorSum B :=
    Finset.single_le_sum (f:=fun a => ∑ j, (B.adjugate a j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  calc
    |(z i:ℝ)| ≤ |(B.det:ℝ)| * |(z i:ℝ)| := le_mul_of_one_le_left (abs_nonneg _) hd'
    _ = |((∑ j, B.adjugate i j * B.mulVec z j : ℤ) : ℝ)| := by rw [hi,Int.cast_mul,abs_mul]
    _ ≤ ∑ j, (|(B.adjugate i j : ℝ)| * |(B.mulVec z j : ℝ)|) := by
      push_cast
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => (B.adjugate i j : ℝ) * (B.mulVec z j : ℝ)) Finset.univ
    _ ≤ ∑ j, (|(B.adjugate i j : ℝ)| * ‖latVec B z‖) := by
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (coord_le_norm B z j) (abs_nonneg _)
    _ = (↑(∑ j, (B.adjugate i j).natAbs) : ℝ) * ‖latVec B z‖ := by
      rw [←Finset.sum_mul, Nat.cast_sum]
      simp only [Nat.cast_natAbs,Int.cast_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hrow) (norm_nonneg _)

def safeRadius (B : Matrix (Fin n) (Fin n) ℤ) : ℝ := 1 / (2*((cofactorSum B:ℝ)+1))

theorem safeRadius_pos (B : Matrix (Fin n) (Fin n) ℤ) : 0 < safeRadius B := by unfold safeRadius; positivity

theorem signed_recover (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (z : Fin n → ℤ)
    (hshort : ‖GaussianPoissonSeries.fineGridPoint (modulus:=M) (latVec B z)‖ < safeRadius B) :
    (fun i => ((z i : ZMod M).valMinAbs)) = z := by
  have hM : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  rw [GaussianPoissonSeries.norm_fineGridPoint, safeRadius, div_lt_div_iff₀ hM (by positivity)] at hshort
  funext i
  have hz := coefficient_bound B hB z i
  have hsmall : 2*|(z i:ℝ)| < M := by nlinarith [norm_nonneg (latVec B z)]
  have hint : 2*|z i| < (M:ℤ) := by exact_mod_cast hsmall
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_, ?_⟩ <;> rcases abs_cases (z i) with ⟨h,h'⟩ | ⟨h,h'⟩ <;> omega

theorem separated (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) :
    ∀ x : inputLattice B hB, x≠0 → 2*safeRadius B ≤ ‖(x : Space (dimension:=n))‖ := by
  intro x hx
  let z := (integerBasis B hB).equivFun x
  have hv := coefficient_point B hB z
  simp only [z,LinearEquiv.symm_apply_apply] at hv
  have hvec : B.mulVec z ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    rw [hv]
    change WithLp.toLp 2 (fun j => ((B.mulVec z j : ℤ) : ℝ)) = 0
    simp [h]; rfl
  obtain ⟨j,hj⟩ : ∃ j, B.mulVec z j ≠ 0 := by simpa only [Function.ne_iff, Pi.zero_apply] using hvec
  have h1 : (1 : ℤ) ≤ |B.mulVec z j| := by have := abs_pos.mpr hj; omega
  have h' := coord_le_norm B z j
  rw [hv]
  have h1' : (1 : ℝ) ≤ |(B.mulVec z j:ℝ)| := by exact_mod_cast h1
  let A := (cofactorSum B : ℝ)
  have hA : 0≤A := Nat.cast_nonneg _
  have hr : 2*(1/(2*(A+1))) ≤ 1 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  exact hr.trans (h1'.trans h')

end

end GridReadout

end P2MDyadicModule32

/- Helper module Truncate. -/
section P2MDyadicModule33

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace GridReadout

open InfoLossLAR.WorstCase GaussianPoissonSeries CoherentDecoder CoherentProjection

open GaussianProjection.CosetGeometry RegevLWE.GaussConv

noncomputable section

variable {n M : ℕ} [NeZero M]

theorem truncated_event (L : Submodule ℤ (GaussianPoissonSeries.Space (dimension:=n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin n) ℤ L) (w R : ℝ) (hw : 0<w) (hR : 0≤R) (hn : 0<n)
    (hscale : (n:ℝ)*w^2 ≤ R^2)
    (hsep : ∀ x : L, x≠0 → 2*R ≤ ‖(x : GaussianPoissonSeries.Space (dimension:=n))‖)
    (E : (Fin n → ZMod M) → Prop) (A : L → Prop)
    (hmatch : ∀ x : L, ‖fineGridPoint (modulus:=M) (x : GaussianPoissonSeries.Space (dimension:=n))‖<R →
      (E (publicCoordinates M L b x) ↔ A x)) :
    |bornEvent E (normalized (truncatedState (modulus:=M) L b w R)) -
      mass (fun x : L => rho ((M:ℝ)*(w/Real.sqrt 2)) (x : GaussianPoissonSeries.Space (dimension:=n))) A /
      rhoCoset ((M:ℝ)*(w/Real.sqrt 2)) L 0| ≤ (1/4:ℝ)^n := by
  let W (x : L) := fineGridWeight (modulus:=M) w (x : GaussianPoissonSeries.Space (dimension:=n))
  let K (x : L) := ‖fineGridPoint (modulus:=M) (x : GaussianPoissonSeries.Space (dimension:=n))‖<R
  let q := publicCoordinates M L b
  have hp (x : L) : 0 ≤ (W x)^2 := sq_nonneg _
  have hs : Summable (fun x => (W x)^2) := summable_fineGridWeight_square L w hw
  have hkeep := summable_filtered_nonnegative _ hs hp K
  have hx (x : L) : (W x)^2 = rho ((M:ℝ)*(w/Real.sqrt 2)) (x : GaussianPoissonSeries.Space (dimension:=n)) := by
    exact (rho_square _ _).trans (fineGridWeight_eq_rho (w/Real.sqrt 2) (by positivity) (x : GaussianPoissonSeries.Space (dimension:=n)))
  have hM : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have htotal : (∑' x : L, (W x)^2) = rhoCoset ((M:ℝ)*(w/Real.sqrt 2)) L 0 := by simp [hx,rhoCoset]
  have hpos : 0 < ∑' x : L,(W x)^2 := htotal ▸ rhoCoset_zero_pos L _ (by positivity)
  have hnorm := truncatedState_norm_sq (modulus:=M) L b w R hw hsep
  change ‖truncatedState (modulus:=M) L b w R‖^2 = mass (fun x => (W x)^2) K at hnorm
  have heach (c : Fin n → ZMod M) : ‖truncatedState (modulus:=M) L b w R c‖^2 =
      fiberMass q (fun x => if K x then (W x)^2 else 0) c := by
    change ‖(truncatedAmplitude (modulus:=M) L b w R c : ℂ)‖^2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact truncated_fiber_square q W K (fineGrid_quotient_injective L b R hsep) c
  have hsum : (∑ c, if E c then ‖truncatedState (modulus:=M) L b w R c‖^2 else 0) =
      mass (fun x => (W x)^2) (fun x => K x ∧ A x) := by
    simp_rw [heach]
    rw [event_fiber q _ hkeep (fun x => by split <;> simp [hp]) E]
    apply tsum_congr
    intro x
    by_cases hk : K x
    · have he := hmatch x hk
      change E (q x) ↔ A x at he
      by_cases ha : A x <;> simp [hk,ha,he]
    · simp [hk]
  rw [norm_event, hsum, hnorm]
  have hbig := truncatedState_norm_sq_lower (modulus:=M) L b w R hw hR hscale hsep
  rw [hnorm,←htotal] at hbig
  have hτ : (1/4:ℝ)^n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
  have herr := prob_cut (fun x => (W x)^2) hs hp K A _ hτ hpos hbig
  have hm : mass (fun x => (W x)^2) A =
      mass (fun x : L => rho ((M:ℝ)*(w/Real.sqrt 2)) (x : GaussianPoissonSeries.Space (dimension:=n))) A := by simp [mass,hx]
  rwa [hm,htotal] at herr

end

end GridReadout

end P2MDyadicModule33

/- Helper module FourierReadout. -/
section P2MDyadicModule34

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout

open InfoLossLAR.WorstCase GaussianPoissonSeries IntegerBasis RegevLWE.GaussConv

open CoherentDecoder CoherentProjection FiniteLatticeFourier

noncomputable section

variable {n M : ℕ} [NeZero M]

def gridError (n : ℕ) : ℝ := 4*Real.sqrt (2*(1/2:ℝ)^n)+(1/4:ℝ)^n

theorem normalized_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : ‖normalized v‖ ≤ 1 := by
  by_cases hv : v=0
  · simp [hv,normalized]
  · exact (normalized_norm _ hv).le

end

end GridReadout

end P2MDyadicModule34

/- Helper module PrimalBound. -/
section P2MDyadicModule35

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout

open InfoLossLAR.WorstCase GaussianPoissonSeries IntegerBasis RegevLWE.GaussConv RegevSearch

open CoherentDecoder CoherentProjection FiniteLatticeFourier

noncomputable section

variable {n M : ℕ} [NeZero M]

theorem primal_reference_eq (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) (hr : 0<r)
    (T : Finset (Fin n → ℤ)) :
    bornEvent (fun c : Fin n → ZMod M => (fun i => (c i).valMinAbs) ∈ T) (normalized (periodizedState (modulus:=M) (inputLattice B hB) (integerBasis B hB) (1 / ((M:ℝ)*(1/(Real.sqrt 2*r)))))) =
      fourierEvent B r M T := by
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

theorem primal_fourier_event (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) (hr : 0<r)
    (hn : 0<n) (hscale : (n:ℝ) * (1 / ((M:ℝ) * (1 / (Real.sqrt 2 * r))))^2 ≤ (safeRadius B)^2)
    (T : Finset (Fin n → ℤ)) :
    |bornEvent (fun c : Fin n → ZMod M => (fun i => (c i).valMinAbs) ∈ T) (normalized (periodizedState (modulus:=M) (inputLattice B hB) (integerBasis B hB) (1 / ((M:ℝ)*(1/(Real.sqrt 2*r)))))) -
      ∑ z ∈ T, RegevSketch.coefficientMass B r z| ≤ gridError n := by
  let E (c : Fin n → ZMod M) := (fun i => (c i).valMinAbs) ∈ T
  let A (x : inputLattice B hB) := (integerBasis B hB).equivFun x ∈ T
  let width := 1 / (Real.sqrt 2 * r)
  let w := 1 / ((M:ℝ) * width)
  have hM : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hwidth : 0<width := by dsimp [width]; positivity
  have hw : 0<w := by dsimp [w]; positivity
  have heq : (M:ℝ)*(w/Real.sqrt 2) = r := by dsimp [w,width]; field_simp
  have hmatch (x : inputLattice B hB) (hk : ‖fineGridPoint (modulus:=M) (x : EuclideanSpace ℝ (Fin n))‖ < safeRadius B) :
      E (GaussianProjection.CosetGeometry.publicCoordinates M (inputLattice B hB) (integerBasis B hB) x) ↔ A x := by
    let z := (integerBasis B hB).equivFun x
    have hx := coefficient_point B hB z
    rw [show (integerBasis B hB).equivFun.symm z=x from LinearEquiv.symm_apply_apply _ _] at hx
    rw [hx] at hk
    change (fun i => ((z i : ZMod M).valMinAbs)) ∈ T ↔ z ∈ T
    rw [signed_recover B hB z hk]
  have hcut := truncated_event (inputLattice B hB) (integerBasis B hB) w (safeRadius B) hw (safeRadius_pos B).le hn
    hscale (separated B hB) E A hmatch
  rw [heq, coeff_mass_event B hB r T] at hcut
  let v := periodizedState (modulus:=M) (inputLattice B hB) (integerBasis B hB) w
  let u := truncatedState (modulus:=M) (inputLattice B hB) (integerBasis B hB) w (safeRadius B)
  have hdist : ‖normalized v-normalized u‖ ≤ 2*Real.sqrt (2*(1/2:ℝ)^n) :=
    normalized_periodized_truncated_close (inputLattice B hB) (integerBasis B hB) w _ hw (safeRadius_pos _) hn hscale (separated B hB)
  have hn2 : ‖normalized v‖+‖normalized u‖ ≤ 2 := by linarith [normalized_norm_le v,normalized_norm_le u]
  have herr := (bornEvent_error_le E (normalized v) (normalized u)).trans
    (mul_le_mul hdist hn2 (by positivity) (by positivity))
  have htri := abs_sub_le (bornEvent E (normalized v)) (bornEvent E (normalized u)) (∑ z ∈ T, RegevSketch.coefficientMass B r z)
  change |bornEvent E (normalized u) - _| ≤ _ at hcut
  change |bornEvent E (normalized v) - _| ≤ _
  unfold gridError
  linarith

theorem primal_adequate_scale (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (hr : 0<r) (hM : gridAdequate B r M) :
    (n:ℝ) * (1 / ((M:ℝ) * (1 / (Real.sqrt 2 * r))))^2 ≤ (safeRadius B)^2 := by
  have hMpos : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hroot : Real.sqrt (n:ℝ) ≤ n+1 := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith [sq_nonneg (n:ℝ)]⟩
  have h2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hb : (4:ℝ) * ((cofactorSum B:ℝ)+1) * ((n:ℝ)+1) * ((⌈r⌉₊:ℝ)+1) ≤ M := by exact_mod_cast hM
  have hw : 1 / ((M:ℝ)*(1/(Real.sqrt 2*r))) = Real.sqrt 2*r/M := by field_simp
  rw [hw,← Real.sq_sqrt (Nat.cast_nonneg n), ←mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  unfold safeRadius
  rw [← mul_div_assoc,div_le_div_iff₀ hMpos (by positivity)]
  have hc := Nat.le_ceil r
  have he := mul_le_mul hroot (mul_le_mul h2 (le_trans hc (by linarith : (⌈r⌉₊:ℝ)≤(⌈r⌉₊:ℝ)+1)) hr.le (by norm_num : (0:ℝ)≤2))
    (mul_nonneg (Real.sqrt_nonneg _) hr.le) (by positivity : (0:ℝ)≤n+1)
  calc
    _ ≤ (((n:ℝ)+1)*(2*((⌈r⌉₊:ℝ)+1)))*(2*((cofactorSum B:ℝ)+1)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = 4 * ((cofactorSum B:ℝ)+1) * ((n:ℝ)+1) * ((⌈r⌉₊:ℝ)+1) := by ring
    _ ≤ _ := by simpa using hb

theorem operational_bound (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (r : ℝ) (hr : 0<r)
    (hn : 0<n) (hM : gridAdequate B r M) (T : Finset (Fin n → ℤ)) :
    |fourierEvent B r M T - ∑ z ∈ T, RegevSketch.coefficientMass B r z| ≤ gridError n := by
  rw [←primal_reference_eq B hB r hr T]
  exact primal_fourier_event B hB r hr hn (primal_adequate_scale B r hr hM) T

end

end GridReadout

end P2MDyadicModule35

/- Helper module Solution. -/
section P2MDyadicModule36

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSearch

open scoped BigOperators

theorem solution {n M : ℕ} [NeZero M] (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (r : ℝ) (hr : 0<r) (hn : 0<n) (hM : gridAdequate B r M) (T : Finset (Fin n → ℤ)) :
    |fourierEvent B r M T - ∑ z ∈ T, RegevSketch.coefficientMass B r z| ≤
      4*Real.sqrt (2*(1/2:ℝ)^n)+(1/4:ℝ)^n := GridReadout.operational_bound B hB r hr hn hM T

end P2MDyadicModule36
