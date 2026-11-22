-- Prove2me | solution 1 for LongGapsBetweenPrimes.integerAverage_residues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:24.366835+00:00
-- url     : https://prove2.me/submissions/6374c2d0-fb5c-4ff0-aa6a-8ae414b3e6e6

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
open scoped Fin.CommRing
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : Squarefree P)
    (f : ((p : PrimeIndex P) → Fin p.val) → ℝ) :
    integerAverage P (fun n => f (residueVector P n)) = Finset.expect Finset.univ f := by
  classical
  let : NeZero P := ⟨hP.ne_zero⟩
  let (p : PrimeIndex P) : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : PrimeIndex P => Nat.Coprime p.val q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.property)
      (Nat.prime_of_mem_primeFactors q.property)).mpr (fun h => hpq (Subtype.ext h))
  have hprod : (∏ p : PrimeIndex P, p.val) = P :=
    (Finset.prod_subtype (F := inferInstanceAs (Fintype (PrimeIndex P)))
      P.primeFactors (fun _ => Iff.rfl) id).symm.trans (Nat.prod_primeFactors_of_squarefree hP)
  let e : Fin P ≃+* ((p : PrimeIndex P) → Fin p.val) :=
    (ZMod.finEquiv P).trans <| (ZMod.ringEquivCongr hprod.symm).trans <|
      (ZMod.prodEquivPi (fun p : PrimeIndex P => p.val) hcop).trans <|
        RingEquiv.piCongrRight (fun p => (ZMod.finEquiv p.val).symm)
  have he (n : Fin P) : e n = residueVector P n.val := by
    calc
      e n = e (Nat.cast n.val : Fin P) := congrArg e (Fin.cast_val_eq_self n).symm
      _ = (Nat.cast n.val : (p : PrimeIndex P) → Fin p.val) := map_natCast e n.val
      _ = residueVector P n.val := rfl
  have h := Fintype.expect_equiv e.toEquiv
    (fun n : Fin P => f (residueVector P n.val)) f (fun n => congrArg f (he n).symm)
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin] at h
  rw [Fin.sum_univ_eq_sum_range (fun n => f (residueVector P n)) P] at h
  simpa only [integerAverage, Fintype.expect_eq_sum_div_card] using h
end LongGapsBetweenPrimes
