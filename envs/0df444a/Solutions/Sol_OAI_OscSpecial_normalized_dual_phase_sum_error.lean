-- Prove2me | solution 1 for OAI.OscSpecial.normalized_dual_phase_sum_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:30:47.011951+00:00
-- url     : https://prove2.me/submissions/e8f8afe3-7cb5-4635-a30c-34776ae482b5

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_OscSpecial_dual_phase_term_error
import Theorems.Thm_OAI_GaussianMoment_gaussian_moment_term_bound
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_OscSpecial_phaseBoundConstant_pos
import Theorems.Thm_OAI_OscSpecial_r_pos
import Theorems.Thm_OAI_RankTwoPoisson_eis_gauss_summable
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
private theorem dualQ_nonneg (z : ℤ × ℤ) : 0 ≤ dualQ z := by
  unfold dualQ
  nlinarith [sq_nonneg ((z.1 : ℝ) + (z.2 : ℝ)), sq_nonneg (z.1 : ℝ),
    sq_nonneg (z.2 : ℝ)]
private theorem phaseA_nonneg {a b : ℝ} (hq : 0 ≤ q a b) :
    0 ≤ phaseA a b := by
  unfold phaseA
  positivity
private theorem dualRealGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualRealGauss t) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss t (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable ht)
  convert hE.norm using 1
  funext z
  dsimp [dualRealGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  congr 1
  dsimp [dualQ, RankTwoPoisson.eisQ]
  push_cast
  ring
private theorem dualMoment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => dualQ z * dualRealGauss t z) := by
  have hmaj : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * dualRealGauss (t / 2) z) :=
    (dualRealGauss_summable (half_pos ht)).mul_left _
  apply hmaj.of_nonneg_of_le
  · intro z
    exact mul_nonneg (dualQ_nonneg z) (Real.exp_pos _).le
  · intro z
    have h := GaussianMoment.gaussian_moment_term_bound
      (dualQ z) (Real.pi * t) (dualQ_nonneg z) (mul_pos Real.pi_pos ht)
    convert h using 1 <;> dsimp [dualRealGauss] <;> ring_nf
private theorem dualAmp_eq_realGauss (η a b : ℝ) (z : ℤ × ℤ) :
    dualAmp η a b z = dualRealGauss (η * q a b / (4 * r η a b)) z := rfl
private theorem dualAmp_norm_var (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualVarTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le
private theorem dualAmp_norm_fixed (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualFixedTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualFixedTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le
private theorem dualAmp_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualAmp η a b) := by
  have hr : 0 < r η a b := r_pos hη hq
  have ht : 0 < η * q a b / (4 * r η a b) := by positivity
  convert dualRealGauss_summable ht using 1
  funext z
  exact dualAmp_eq_realGauss η a b z
private theorem dualVar_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualVarTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_var η a b z))
private theorem dualFixed_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualFixedTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_fixed η a b z))
private theorem dualAmp_le_small {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2)
    (z : ℤ × ℤ) :
    dualAmp η a b z ≤ dualRealGauss (η * q a b / 8) z := by
  have hr : 0 < r η a b := r_pos hη hq
  have hp : 0 < η * q a b := mul_pos hη hq
  have ht : η * q a b / 8 ≤ η * q a b / (4 * r η a b) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (by positivity : 0 < 4 * r η a b)).2
    nlinarith [mul_le_mul_of_nonneg_left hrle hp.le]
  dsimp [dualAmp, dualRealGauss]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right ht
    (mul_nonneg Real.pi_pos.le (dualQ_nonneg z))
  nlinarith [hm]
private theorem phaseErrorConstant_nonneg {a b : ℝ} (hq : 0 < q a b) :
    0 ≤ phaseErrorConstant a b := by
  unfold phaseErrorConstant
  exact mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
    (phaseBoundConstant_pos a b).le) (phaseA_nonneg hq.le)
open scoped Topology
open Filter
end OscSpecial
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT
end ActualEisensteinCubic
open Filter
open scoped Topology
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.OscSpecial
namespace OAI.OscSpecial
theorem _root_.solution {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2) :
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ ≤
      phaseErrorConstant a b * η ^ 3 *
        (∑' z : ℤ × ℤ,
          dualQ z * dualRealGauss (η * q a b / 8) z) := by
  let t : ℝ := η * q a b / 8
  have ht : 0 < t := by dsimp [t]; positivity
  have hK : 0 ≤ phaseErrorConstant a b := phaseErrorConstant_nonneg hq
  have hpoint (z : ℤ × ℤ) :
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        (phaseErrorConstant a b * η ^ 2) *
          (dualQ z * dualRealGauss t z) := by
    have hbase := dual_phase_term_error hη hq z
    have hamp := dualAmp_le_small hη hq hrle z
    have hfac : 0 ≤
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
          (phaseBoundConstant_pos a b).le) (dualQ_nonneg z))
        (mul_nonneg (phaseA_nonneg hq.le) (sq_nonneg η))
    have hmul := mul_le_mul_of_nonneg_right hamp hfac
    dsimp [t, phaseErrorConstant]
    calc
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        dualAmp η a b z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := hbase
      _ ≤ dualRealGauss (η * q a b / 8) z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by nlinarith [hmul]
      _ = ((Real.pi / 2 * phaseBoundConstant a b * phaseA a b) * η ^ 2) *
          (dualQ z * dualRealGauss (η * q a b / 8) z) := by ring
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (phaseErrorConstant a b * η ^ 2) *
        (dualQ z * dualRealGauss t z)) :=
    (dualMoment_summable ht).mul_left _
  have hnorm : Summable (fun z : ℤ × ℤ =>
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
    hmajor.of_nonneg_of_le (fun z => norm_nonneg _) hpoint
  have hsum := norm_tsum_le_tsum_norm hnorm
  have htsum := Summable.tsum_le_tsum hpoint hnorm hmajor
  have hvar := dualVar_summable hη hq
  have hfixed := dualFixed_summable hη hq
  calc
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ =
      η * ‖(∑' z : ℤ × ℤ, (dualVarTerm η a b z - dualFixedTerm η a b z))‖ := by
        rw [hvar.tsum_sub hfixed]
    _ ≤ η * (∑' z : ℤ × ℤ,
          ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
      mul_le_mul_of_nonneg_left hsum hη.le
    _ ≤ η * (∑' z : ℤ × ℤ,
          (phaseErrorConstant a b * η ^ 2) *
            (dualQ z * dualRealGauss t z)) :=
      mul_le_mul_of_nonneg_left htsum hη.le
    _ = phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ, dualQ z * dualRealGauss (η * q a b / 8) z) := by
      rw [tsum_mul_left]
      dsimp [t]
      ring
end OAI.OscSpecial
