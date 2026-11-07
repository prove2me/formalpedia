-- Prove2me | solution 1 for OAI.DyadicTransfer.expAnnularTest_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:58.224131+00:00
-- url     : https://prove2.me/submissions/e7627fbc-31c1-4031-9ace-6c93a92b2f44

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open OAI.DyadicTransfer
namespace OAI.DyadicTransfer
theorem _root_.solution (φ : ℝ → ℂ) (D : ℝ) (k : ℕ)
    (hD : 0 < D) (M : ℝ) (hM : ∀ y : ℝ, ‖annularCutoff φ y‖ ≤ M)
    {y : ℝ} (hy : 1 / 2 ≤ y) :
    ‖expAnnularTest φ D k y‖ ≤
      M * Real.exp (-((2 : ℝ) ^ k / D) / 2) := by
  let t : ℝ := (2 : ℝ) ^ k / D
  have ht : 0 ≤ t := div_nonneg (by positivity) hD.le
  have harg : -(t * y) ≤ -t / 2 := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hy)]
  have hexp : Real.exp (-(t * y)) ≤ Real.exp (-t / 2) :=
    Real.exp_le_exp.mpr harg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM y)
  calc
    ‖expAnnularTest φ D k y‖ = ‖annularCutoff φ y‖ * Real.exp (-(t * y)) := by
      rw [expAnnularTest, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      simp [t]
    _ ≤ M * Real.exp (-(t * y)) :=
      mul_le_mul_of_nonneg_right (hM y) (Real.exp_pos _).le
    _ ≤ M * Real.exp (-t / 2) := mul_le_mul_of_nonneg_left hexp hM0
    _ = M * Real.exp (-((2 : ℝ) ^ k / D) / 2) := rfl
end OAI.DyadicTransfer
