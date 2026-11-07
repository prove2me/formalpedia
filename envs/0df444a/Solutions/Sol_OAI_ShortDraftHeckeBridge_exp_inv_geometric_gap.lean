-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.exp_inv_geometric_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:40.99167+00:00
-- url     : https://prove2.me/submissions/a3a53483-4e2d-4441-a0ec-c2e26568890d

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution (D : ℝ) (hD : 1 ≤ D) :
    1 / (D * (1 - Real.exp (-D⁻¹))) ≤ 2 := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hden : 0 < D + 1 := by linarith
  have hx : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hbase : 0 < 1 + D⁻¹ := by positivity
  have hexp : 1 + D⁻¹ ≤ Real.exp D⁻¹ := by
    linarith [Real.add_one_le_exp D⁻¹]
  have he : Real.exp (-D⁻¹) ≤ (1 + D⁻¹)⁻¹ := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hbase hexp
  have hrew : (1 + D⁻¹)⁻¹ = D / (D + 1) := by
    field_simp
  rw [hrew] at he
  have hhalf : (1 / 2 : ℝ) ≤ D * (1 - Real.exp (-D⁻¹)) := by
    calc
      (1 / 2 : ℝ) ≤ D / (D + 1) := by
        apply (le_div_iff₀ hden).2
        nlinarith
      _ = D * (1 - D / (D + 1)) := by
        field_simp
        ring
      _ ≤ D * (1 - Real.exp (-D⁻¹)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left he 1) hDpos.le
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  norm_num at h ⊢
  exact h
end OAI.ShortDraftHeckeBridge
