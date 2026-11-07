-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberCoeff_eq_pairAF_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:00.426819+00:00
-- url     : https://prove2.me/submissions/4a9eee33-5e59-4ff4-93a6-6320be7e5274

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_ShortDraftHeckeBridge_chiMinusThree_mod_one
import Theorems.Thm_OAI_ShortDraftHeckeBridge_chiMinusThree_mod_two
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeChar_prime_apply
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeChar_three
import Theorems.Thm_OAI_ShortDraftHeckeBridge_local_inert_p
import Theorems.Thm_OAI_ShortDraftHeckeBridge_local_ramified_three
import Theorems.Thm_OAI_ShortDraftHeckeBridge_local_split_p
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairAF_prime


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
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    normFiberCoeff (baseChangeWeight χ) p =
      pairAF χ (baseChangeChar χ) p := by
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hcase : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have heq : p = 3 := by
      rcases (Nat.dvd_prime hp).1 hdiv with h1' | h3
      · norm_num at h1'
      · exact h3.symm
    subst p
    rw [local_ramified_three χ,
      pairAF_prime χ (baseChangeChar χ) (by decide),
      baseChangeChar_three χ]
    ring_nf
  · rw [local_split_p χ hp h1, pairAF_prime χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_one p h1]
    ring
  · rw [local_inert_p χ hp h2, pairAF_prime χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_two p h2]
    ring
end OAI.ShortDraftHeckeBridge
