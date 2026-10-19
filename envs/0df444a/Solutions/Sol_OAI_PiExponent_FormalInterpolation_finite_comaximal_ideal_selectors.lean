-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_comaximal_ideal_selectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:45:54.691576+00:00
-- url     : https://prove2.me/submissions/fc85aa78-3710-4203-bd51-338a715c90d3

import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators


theorem solution
    {R : Type} [CommRing R] {K : Nat} (I : Fin K → Ideal R)
    (hI : ∀ j k : Fin K, j ≠ k → I j ⊔ I k = ⊤) :
    ∃ E : Fin K → R, ∀ j k : Fin K,
      E k - (if j = k then 1 else 0) ∈ I j := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime I) := by
    intro j k hjk
    exact Ideal.isCoprime_iff_sup_eq.mpr (hI j k hjk)
  have hsurj := Ideal.quotientInfToPiQuotient_surj hcop
  choose y hy using fun k : Fin K => hsurj (fun j => Ideal.Quotient.mk (I j) (if j = k then 1 else 0))
  refine ⟨fun k => Quotient.out (y k), fun j k => ?_⟩
  have h := congrFun (hy k) j
  rw [← Ideal.Quotient.eq]
  rw [← h]
  conv_rhs => rw [← Quotient.out_eq (y k)]
  rfl

