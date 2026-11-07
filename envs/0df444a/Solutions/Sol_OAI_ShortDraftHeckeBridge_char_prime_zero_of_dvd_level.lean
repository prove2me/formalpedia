-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.char_prime_zero_of_dvd_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:06.281733+00:00
-- url     : https://prove2.me/submissions/5ba37917-e368-4c5e-b706-d3f98ec8b742

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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hd : p ∣ q) :
    χ p = 0 := by
  have hnot : ¬ IsCoprime (p : ℤ) (q : ℕ) := by
    intro hc
    have hn : p.Coprime q := by
      simpa [Int.isCoprime_iff_nat_coprime] using hc
    exact (hp.coprime_iff_not_dvd.mp hn) hd
  simpa using (DirichletCharacter.apply_eq_zero_iff χ (p : ℤ)).mpr hnot
end OAI.ShortDraftHeckeBridge
