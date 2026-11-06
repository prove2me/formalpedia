-- Prove2me | solution 1 for OAI.RankTwoEisShift.shifted_eisenstein_gaussian_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:24.766401+00:00
-- url     : https://prove2.me/submissions/e318d918-9d4a-45cc-b236-7856bb8402a5

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Theorems.Thm_OAI_RankTwoAffine_affine_gaussian_poisson
import Theorems.Thm_OAI_RankTwoEisShift_dualPhase_norm
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_RankTwoPoisson_eis_gauss_summable
import Theorems.Thm_OAI_RankTwoPoisson_real_gauss_summable
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
namespace RankTwoComplex
open Real
end RankTwoComplex
namespace GaussianShiftedPartition
open ActualEisensteinCubic ConcreteTraceCRT ConcreteBreveE
end GaussianShiftedPartition
namespace RankTwoAffine
open RankTwoComplex
end RankTwoAffine
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace RankTwoEisShift
private theorem shifted_eq_affine (t x y : ℝ) (m n : ℤ) :
    shifted t x y (m,n) =
      C t x y * RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) (m,n) := by
  dsimp [shifted, C, Q, RankTwoAffine.binaryGaussian, A, B, D, U, V]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
private theorem schur_eis {t : ℝ} (ht : 0 < t) :
    RankTwoComplex.schur (A t) (B t) (D t) = (((3 * t) / 4 : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [RankTwoComplex.schur, A, B, D]
  push_cast
  field_simp [ht0]
  ring
private theorem schur_eis_pos {t : ℝ} (ht : 0 < t) :
    0 < (RankTwoComplex.schur (A t) (B t) (D t)).re := by
  rw [schur_eis ht]
  have h : 0 < 3 * t / 4 := by positivity
  simpa using h
private theorem shifted_dual_term {t : ℝ} (ht : 0 < t) (x y : ℝ) (k l : ℤ) :
    C t x y *
      RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,l) =
      RankTwoPoisson.eisGauss (4 / (3 * t)) (k,-l) * dualPhase k l x y := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [C, Q, RankTwoAffine.dualGaussian, RankTwoPoisson.eisGauss,
    RankTwoPoisson.eisQ, dualPhase, A, B, D, U, V]
  rw [show RankTwoComplex.schur (t : ℂ) ((-t / 2 : ℝ) : ℂ) (t : ℂ) =
      (((3 * t) / 4 : ℝ) : ℂ) from schur_eis ht]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring
private theorem shifted_real_gauss_summable {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * ((n : ℝ) + y) ^ 2)) := by
  have ht2 : 0 < t / 2 := by positivity
  have hbase := RankTwoPoisson.real_gauss_summable ht2
  have hmaj : Summable (fun n : ℤ =>
      Real.exp (Real.pi * t * y ^ 2) *
        Real.exp (-Real.pi * (t / 2) * (n : ℝ) ^ 2)) :=
    hbase.mul_left _
  refine hmaj.of_norm_bounded ?_
  intro n
  have hs : (n : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((n : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) + 2 * y)]
  have hm := mul_le_mul_of_nonneg_left hs (mul_pos Real.pi_pos ht).le
  have he : -Real.pi * t * ((n : ℝ) + y) ^ 2 ≤
      Real.pi * t * y ^ 2 + -Real.pi * (t / 2) * (n : ℝ) ^ 2 := by
    nlinarith [hm]
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add] using
    (Real.exp_le_exp.mpr he)
private theorem middlePhase_norm (k n : ℤ) (x y : ℝ) :
    ‖middlePhase k n x y‖ = 1 := by
  simp [middlePhase, Complex.norm_exp, Complex.mul_re]
private theorem shifted_middle_term {t : ℝ} (ht : 0 < t) (x y : ℝ) (k n : ℤ) :
    C t x y *
      RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,n) =
      RankTwoPoisson.cg ((t⁻¹ : ℝ) : ℂ) k *
        Complex.exp (((-Real.pi * (3 * t / 4) * ((n : ℝ) + y) ^ 2 : ℝ) : ℂ)) *
        middlePhase k n x y := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [C, Q, RankTwoAffine.firstGaussian, RankTwoPoisson.cg,
    middlePhase, A, B, D, U, V]
  rw [show RankTwoComplex.schur (t : ℂ) ((-t / 2 : ℝ) : ℂ) (t : ℂ) =
      (((3 * t) / 4 : ℝ) : ℂ) from schur_eis ht]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring
private theorem middle_norm {t : ℝ} (ht : 0 < t) (x y : ℝ) (k n : ℤ) :
    ‖C t x y *
      RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,n)‖ =
      Real.exp (-Real.pi * t⁻¹ * (k : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * t / 4) * ((n : ℝ) + y) ^ 2) := by
  rw [shifted_middle_term ht]
  simp [ middlePhase_norm, RankTwoPoisson.cg, Complex.norm_exp,
    ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc]
private theorem affine_middle_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have ht3 : 0 < 3 * t / 4 := by positivity
  have h1 := RankTwoPoisson.real_gauss_summable htinv
  have h2 := shifted_real_gauss_summable ht3 y
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * t⁻¹ * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * t / 4) * ((z.2 : ℝ) + y) ^ 2)) :=
    h1.mul_of_nonneg h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hCmid : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    refine hmaj.of_norm_bounded ?_
    intro z
    rw [middle_norm ht]
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have h := hCmid.mul_left (C t x y)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h
private theorem affine_dual_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have htd : 0 < 4 / (3 * t) := by positivity
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable htd)
  have hCdual : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    refine hE.norm.of_norm_bounded ?_
    intro z
    rw [shifted_dual_term ht]
    simp [ dualPhase_norm]
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have h := hCdual.mul_left (C t x y)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h
private theorem shifted_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (shifted t x y) := by
  have ht4 : 0 < t / 4 := by positivity
  have h1 := RankTwoPoisson.real_gauss_summable ht4
  have hbase : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 4) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (Real.pi * t * (x ^ 2 + y ^ 2) / 2) *
        (Real.exp (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2) *
         Real.exp (-Real.pi * (t / 4) * (z.2 : ℝ) ^ 2))) :=
    hbase.mul_left _
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq : (((z.1 : ℝ) + x) ^ 2 + ((z.2 : ℝ) + y) ^ 2) / 2 ≤
      Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) := by
    dsimp [Q]
    nlinarith [sq_nonneg (((z.1 : ℝ) + x) - ((z.2 : ℝ) + y))]
  have hm : (z.1 : ℝ) ^ 2 / 2 - x ^ 2 ≤ ((z.1 : ℝ) + x) ^ 2 := by
    nlinarith [sq_nonneg ((z.1 : ℝ) + 2 * x)]
  have hn : (z.2 : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((z.2 : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((z.2 : ℝ) + 2 * y)]
  have hl : ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 4 -
      (x ^ 2 + y ^ 2) / 2 ≤ Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) := by
    nlinarith [hq, hm, hn]
  have hpt : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hl hpt
  have he : -Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) ≤
      Real.pi * t * (x ^ 2 + y ^ 2) / 2 +
        (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2 +
         -Real.pi * (t / 4) * (z.2 : ℝ) ^ 2) := by
    nlinarith [hmul]
  simpa [shifted, Complex.norm_exp, Real.exp_add, mul_assoc] using
    (Real.exp_le_exp.mpr he)
private theorem affine_original_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have hS := shifted_summable ht x y
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have hCA : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) :=
    hS.congr (fun z => shifted_eq_affine t x y z.1 z.2)
  have h := hCA.mul_left (C t x y)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h
end RankTwoEisShift
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
open OAI.RankTwoEisShift
namespace OAI.RankTwoEisShift
theorem _root_.solution {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    (∑' z : ℤ × ℤ, shifted t x y z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2) *
            dualPhase z.1 z.2 x y := by
  have ha : 0 < (A t).re := by simpa [A] using ht
  have hδ := schur_eis_pos ht
  have hO := affine_original_summable ht x y
  have hM := affine_middle_summable ht x y
  have hD := affine_dual_summable ht x y
  let pref : ℂ :=
    (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ))
  have haff :
      (∑' z : ℤ × ℤ,
        RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) =
      pref * (∑' z : ℤ × ℤ,
        RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    have h := RankTwoAffine.affine_gaussian_poisson ha hδ hO hM hD
    rw [schur_eis ht] at h
    exact h
  calc
    (∑' z : ℤ × ℤ, shifted t x y z) =
        C t x y * (∑' z : ℤ × ℤ,
          RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      exact shifted_eq_affine t x y z.1 z.2
    _ = C t x y * (pref * (∑' z : ℤ × ℤ,
          RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z)) := by
      rw [haff]
    _ = pref * (∑' z : ℤ × ℤ,
          C t x y * RankTwoAffine.dualGaussian (A t) (B t) (D t)
            (U t x y) (V t x y) z) := by
      rw [tsum_mul_left]
      ring
    _ = pref * (∑' z : ℤ × ℤ,
          RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2) *
            dualPhase z.1 z.2 x y) := by
      congr 1
      apply tsum_congr
      intro z
      exact shifted_dual_term ht x y z.1 z.2
end OAI.RankTwoEisShift
