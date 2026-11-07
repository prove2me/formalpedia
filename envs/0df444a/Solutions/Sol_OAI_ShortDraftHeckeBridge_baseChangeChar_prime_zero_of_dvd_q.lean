-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.baseChangeChar_prime_zero_of_dvd_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:14:26.874123+00:00
-- url     : https://prove2.me/submissions/7b2650e8-f49a-430a-8d5b-689699eb88d2

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_ShortDraftHeckeBridge_char_prime_zero_of_dvd_level

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
    baseChangeChar χ p = 0 := by
  have hd' : p ∣ q * 3 := dvd_mul_of_dvd_left hd 3
  exact char_prime_zero_of_dvd_level (baseChangeChar χ) hp hd'
end OAI.ShortDraftHeckeBridge
