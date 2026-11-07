-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.sixth_power_rows_in_rowNormDisk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:17.788436+00:00
-- url     : https://prove2.me/submissions/4461556d-9281-4221-a5b5-fe7f570f8252

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ConcretePrimeRowBridge_mem_rowNormDisk
import Theorems.Thm_OAI_ActualEisensteinCubic_principal_absNorm_pow


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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    {β : Type*} (selected : Finset β) (p : β → O)
    (D H : ℕ) (hD : 1 ≤ D)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H) :
    selected.image (fun i => p i ^ 6) ⊆ rowNormDisk H := by
  classical
  intro u hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  rw [mem_rowNormDisk]
  have hpNorm : Ideal.absNorm (Ideal.span {p i}) ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff).not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (hp i hi))
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hupper : (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) ≤
      (D : ℝ) ^ (11 / 10 : ℝ) := by
    calc
      (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) =
          (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ 6 := by
            exact_mod_cast ActualEisensteinCubic.principal_absNorm_pow (p i) 6
      _ ≤ ((D : ℝ) ^ (11 / 60 : ℝ)) ^ 6 := by
        gcongr
        exact hnormupper i hi
      _ = (D : ℝ) ^ (11 / 10 : ℝ) := by
        rw [← Real.rpow_mul_natCast hDpos.le (11 / 60 : ℝ) 6]
        congr 1
        norm_num
  constructor
  · rw [ActualEisensteinCubic.principal_absNorm_pow]
    exact pow_pos (Nat.pos_of_ne_zero hpNorm) 6
  · exact (Nat.le_floor hupper).trans hH
end OAI.ConcretePrimeRowBridge
