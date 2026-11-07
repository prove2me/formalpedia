-- Prove2me | solution 1 for OAI.NormFiberCRT.ideal_eq_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:06.863363+00:00
-- url     : https://prove2.me/submissions/7c209cb6-2ec4-405c-b580-fd2b0faf3941

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
open OAI.NormFiberCRT
namespace OAI.NormFiberCRT
theorem _root_.solution (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    I = (I ⊔ Ideal.span {(m : O)}) * (I ⊔ Ideal.span {(n : O)}) := by
  let A : Ideal O := Ideal.span {(m : O)}
  let B : Ideal O := Ideal.span {(n : O)}
  have hcast : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
  have hAB : A ⊔ B = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (m : O) (n : O)).mpr hcast)
  have hmnmem : ((m * n : ℕ) : O) ∈ I := by
    simpa only [hI] using Ideal.absNorm_mem I
  have hABle : A * B ≤ I := by
    change Ideal.span {(m : O)} * Ideal.span {(n : O)} ≤ I
    rw [Ideal.span_singleton_mul_span_singleton]
    exact (Ideal.span_singleton_le_iff_mem I).mpr (by simpa using hmnmem)
  have hJcop : (I ⊔ A) ⊔ (I ⊔ B) = ⊤ := by
    calc
      (I ⊔ A) ⊔ (I ⊔ B) = I ⊔ (A ⊔ B) := by ac_rfl
      _ = ⊤ := by rw [hAB, sup_top_eq]
  apply le_antisymm
  · rw [Ideal.mul_eq_inf_of_coprime hJcop]
    exact le_inf le_sup_left le_sup_left
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right hABle)
end OAI.NormFiberCRT
