-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.ideals_isRelPrime_of_norms_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:53:14.850534+00:00
-- url     : https://prove2.me/submissions/6a91c20f-4326-4da0-9c84-fce467d51fd4

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    IsRelPrime I J := by
  have hcast : IsCoprime ((Ideal.absNorm I : ℕ) : O)
      ((Ideal.absNorm J : ℕ) : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime h).map (Int.castRingHom O)
  obtain ⟨a, b, hab⟩ := hcast
  apply IsCoprime.isRelPrime
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨a * (Ideal.absNorm I : O),
    I.mul_mem_left a (Ideal.absNorm_mem I),
    b * (Ideal.absNorm J : O),
    J.mul_mem_left b (Ideal.absNorm_mem J), hab⟩
end OAI.ShortDraftHeckeBridge
