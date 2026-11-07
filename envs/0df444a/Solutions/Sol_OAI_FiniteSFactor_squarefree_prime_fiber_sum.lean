-- Prove2me | solution 1 for OAI.FiniteSFactor.squarefree_prime_fiber_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:01.679071+00:00
-- url     : https://prove2.me/submissions/e2a1ff71-8834-40f7-a6ad-2cfef385af34

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_FiniteSFactor_mem_goodFiber
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
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
namespace FiniteSFactor
private theorem pick_spec (P : Ideal O) (hP : Prime P) (m : ℕ)
    (I : Ideal O) (hI : I ∈ badFiber P m) :
    IsRelPrime P (pick P hP m I hI) ∧ I = P * pick P hP m I hI := by
  unfold pick
  exact Classical.choose_spec (extract_prime_of_squarefree
    ((mem_badFiber.mp hI).2.1.ne_zero) hP
    (mem_badFiber.mp hI).2.1 (mem_badFiber.mp hI).2.2)
open scoped Classical
open scoped Classical
end FiniteSFactor
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
namespace DyadicTransfer
end DyadicTransfer
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
namespace FiniteSFactor
end FiniteSFactor
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
open OAI.FiniteSFactor
namespace OAI.FiniteSFactor
theorem _root_.solution (P : Ideal O) (hP : Prime P)
    (m : ℕ) (w : Ideal O → ℂ) :
    (∑ I ∈ badFiber P m, w I) =
      ∑ J ∈ goodFiber P m, w (P * J) := by
  classical
  have hPnorm : Ideal.absNorm P ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff).not.mpr hP.ne_zero
  refine Finset.sum_bij' (pick P hP m) (fun J _ => P * J) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    have hinfo := pick_spec P hP m I hI
    have hJnorm : Ideal.absNorm (pick P hP m I hI) = m := by
      have hInorm := (mem_badFiber.mp hI).1
      rw [hinfo.2, map_mul] at hInorm
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hPnorm) hInorm
    have hJsq : Squarefree (pick P hP m I hI) := by
      have hsqI := (mem_badFiber.mp hI).2.1
      rw [hinfo.2] at hsqI
      exact hsqI.of_mul_right
    have hJnot : ¬P ∣ pick P hP m I hI :=
      hP.irreducible.isRelPrime_iff_not_dvd.mp hinfo.1
    exact mem_goodFiber.mpr ⟨hJnorm, hJsq, hJnot⟩
  · intro J hJ
    have hJnorm := (mem_goodFiber.mp hJ).1
    have hJsq := (mem_goodFiber.mp hJ).2.1
    have hJnot := (mem_goodFiber.mp hJ).2.2
    have hsq : Squarefree (P * J) :=
      squarefree_mul_iff.mpr ⟨hP.irreducible.isRelPrime_iff_not_dvd.mpr hJnot,
        hP.irreducible.squarefree, hJsq⟩
    exact mem_badFiber.mpr ⟨by rw [map_mul, hJnorm], hsq, dvd_mul_right P J⟩
  · intro I hI
    exact (pick_spec P hP m I hI).2.symm
  · intro J hJ
    have hPJ : P * J ∈ badFiber P m := by
      have hJnorm := (mem_goodFiber.mp hJ).1
      have hJsq := (mem_goodFiber.mp hJ).2.1
      have hJnot := (mem_goodFiber.mp hJ).2.2
      exact mem_badFiber.mpr ⟨by rw [map_mul, hJnorm],
        squarefree_mul_iff.mpr ⟨hP.irreducible.isRelPrime_iff_not_dvd.mpr hJnot,
          hP.irreducible.squarefree, hJsq⟩, dvd_mul_right P J⟩
    have hchosen := (pick_spec P hP m (P * J) hPJ).2
    exact (mul_left_cancel₀ hP.ne_zero hchosen).symm
  · intro I hI
    exact congrArg w (pick_spec P hP m I hI).2
end OAI.FiniteSFactor
