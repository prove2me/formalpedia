-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.poisson_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:24.06625+00:00
-- url     : https://prove2.me/submissions/a4f2f084-e0ec-4965-b8bd-f7be694a4d10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierProdSingleCoordinateFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExpStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumRingEqSumIdealCosetsTsumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeThetaKernelPoissonSummation
import Theorems.Thm_GlobalTheory_HeckePoisson_fourier_gauss
import Theorems.Thm_GlobalTheory_HeckePoisson_norm_toLp_half
import Theorems.Thm_GlobalTheory_HeckePoisson_gauss_dil_bound
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_T_fourier_comp_coordDilationByHalfExp
import Theorems.Thm_GlobalTheory_T_gaussianHarmonicProductKernel_continuous_bounded
import Theorems.Thm_GlobalTheory_exp_neg_mul_norm_add_sq_le
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq
import Theorems.Thm_GlobalTheory_tsum_poisson_lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
open GlobalTheory GlobalTheory.HeckePoisson
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckePoisson
theorem _root_.solution (L : Submodule ℤ (EuclideanSpace ℂ I)) [DiscreteTopology L] [IsZLattice ℝ L]
    (n : I → ℤ) (y : I → ℝ) (u : EuclideanSpace ℂ I) :
    Summable (fun l : GlobalTheory.dualLattice L => ‖gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2))‖) ∧
    ∑' x : L, gauss n (dil y (WithLp.ofLp ((x : EuclideanSpace ℂ I) + u))) =
      ((ZLattice.covolume L : ℝ) : ℂ)⁻¹ * ((Real.exp (-∑ i, y i) : ℂ) * kappa n) *
        ∑' l : GlobalTheory.dualLattice L, Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u⟫ : ℝ) : ℂ)) *
          gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2)) := by
  set f : EuclideanSpace ℂ I → ℂ := fun w => gauss n (dil y (WithLp.ofLp w)) with hf
  have hF : ∀ l : EuclideanSpace ℂ I, 𝓕 f l =
      (Real.exp (-∑ i, y i) : ℂ) * kappa n * gauss n (dil (-y) (fun i => l i / 2)) := by
    intro l
    have h := GlobalTheory.T.fourier_comp_coordDilationByHalfExp I (fun w => gauss n (WithLp.ofLp w)) y l
    rw [hf, h, fourier_gauss, mul_assoc]
    congr 3
    funext i
    simp only [dil]
    ring
  obtain ⟨C, a, hC0, ha, hC⟩ := gauss_dil_bound n y
  obtain ⟨C', a', hC0', ha', hC'⟩ := gauss_dil_bound n (-y)
  have hcont : Continuous f := by
    have h1 := (GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded I n).1
    have h2 : Continuous (fun w : EuclideanSpace ℂ I => (WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I)) := by
      unfold dil; fun_prop
    have h3 := h1.comp h2
    simpa only [Function.comp_def, WithLp.ofLp_toLp, hf] using h3
  have hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (v : EuclideanSpace ℂ I), ‖v‖ ≤ R → ‖f (x + v)‖ ≤ g x := by
    intro R
    refine ⟨fun x => C * (Real.exp (a * R ^ 2) * Real.exp (-(a / 2) * ‖(x : EuclideanSpace ℂ I)‖ ^ 2)),
      ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left _).mul_left _, fun x v hv => ?_⟩
    exact (hC _).trans (mul_le_mul_of_nonneg_left (GlobalTheory.exp_neg_mul_norm_add_sq_le ha.le _ hv) hC0)
  have hG : Summable (fun l : GlobalTheory.dualLattice L => ‖gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2))‖) := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
      ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq (GlobalTheory.dualLattice L) (div_pos ha' (by norm_num : (0:ℝ) < 4))).mul_left C')
    have h := hC' (WithLp.toLp 2 (fun i => (l : EuclideanSpace ℂ I) i / 2))
    rw [norm_toLp_half] at h
    refine h.trans_eq ?_
    congr 2
    ring
  have hs : Summable fun l : GlobalTheory.dualLattice L => ‖𝓕 f l‖ := by
    simp only [hF, norm_mul]
    exact hG.mul_left _
  refine ⟨hG, ?_⟩
  have hP := GlobalTheory.tsum_poisson_lattice L hcont hdom hs u
  simp only [hf] at hP
  rw [hP, Complex.real_smul, Complex.ofReal_inv, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  rw [smul_eq_mul, (hF l : 𝓕 (fun w : EuclideanSpace ℂ I => gauss n (dil y (WithLp.ofLp w))) l = _)]
  ring
end GlobalTheory.HeckePoisson
