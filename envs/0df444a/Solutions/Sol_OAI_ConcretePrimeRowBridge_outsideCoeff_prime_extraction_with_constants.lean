-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.outsideCoeff_prime_extraction_with_constants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:27:31.182114+00:00
-- url     : https://prove2.me/submissions/c677f0da-b772-443c-8242-00b1de0c375d

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ConcretePrimeRowBridge_outsideCoeff_prime_extraction_from_MS

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
open ShortDraftHeckeBridge FiniteSFactor
open ShortDraftHeckeBridge FiniteSFactor Filter
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (eta : ℝ) (Cmean Ccount : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (heta : 0 ≤ eta)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : Ccount * (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
      (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        Cmean * (D : ℝ) ^ ((21 / 10 : ℝ) + ε))
    (hmeanAbsorb : Cmean ≤ (D : ℝ) ^ eta)
    (hcountAbsorb : 1 ≤ Ccount * (D : ℝ) ^ eta) :
    ‖∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n * W n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + (ε + eta)) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hcount' :
      (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) ≤
        (selected.card : ℝ) := by
    calc
      (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) =
          1 * (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) := by ring
      _ ≤ (Ccount * (D : ℝ) ^ eta) *
          (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) :=
            mul_le_mul_of_nonneg_right hcountAbsorb
              (Real.rpow_nonneg hDpos.le _)
      _ = Ccount * (D : ℝ) ^ ((11 / 60 : ℝ) - ε) := by
            rw [mul_assoc, ← Real.rpow_add hDpos]
            congr 1
            ring_nf
      _ ≤ (selected.card : ℝ) := hcount
  have hmean' :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + (ε + eta)) := by
    calc
      _ ≤ Cmean * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
      _ ≤ (D : ℝ) ^ eta * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) :=
          mul_le_mul_of_nonneg_right hmeanAbsorb
            (Real.rpow_nonneg hDpos.le _)
      _ = (D : ℝ) ^ ((21 / 10 : ℝ) + (ε + eta)) := by
          rw [← Real.rpow_add hDpos]
          congr 1
          ring
  exact outsideCoeff_prime_extraction_from_MS χ W S hSbad hW selected p
    D H (ε + eta) hD (add_nonneg hε heta) hp hprime hinj
    hnormlower hnormupper hH hcount' hmean'
end OAI.ConcretePrimeRowBridge
