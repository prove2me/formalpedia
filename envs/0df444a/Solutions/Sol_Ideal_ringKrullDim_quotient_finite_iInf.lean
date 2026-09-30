-- Prove2me | solution 1 for Ideal.ringKrullDim_quotient_finite_iInf
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T07:07:58.109642+00:00
-- url     : https://prove2.me/submissions/580969ea-3f01-4980-8b35-74e8f0d58dce

import Mathlib


set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace Ideal
variable {R ι : Type*} [CommRing R]

theorem quotient_dimension_antitone {I J : Ideal R} (h : I ≤ J) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  exact Order.krullDim_le_of_strictMono
    (fun q => ⟨q.val, h.trans q.property⟩) (fun _ _ hlt => hlt)

/-- Every chain of primes above a finite intersection lies above one
of its factors, so its dimension is the supremum of their dimensions. -/
theorem ringKrullDim_quotient_finite_iInf [Finite ι] (A : ι → Ideal R) :
    ringKrullDim (R ⧸ ⨅ i, A i) = ⨆ i, ringKrullDim (R ⧸ A i) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · rw [ringKrullDim_quotient, Order.krullDim]
    refine iSup_le fun c => ?_
    have hhead : (⨅ i, A i) ≤ c.head.val.asIdeal := c.head.property
    have hfinite : (⨅ i, A i) ≤ c.head.val.asIdeal ↔
        ∃ i, A i ≤ c.head.val.asIdeal := by
      simpa only [Finset.inf_univ_eq_iInf, Finset.mem_univ, true_and] using
        c.head.val.isPrime.inf_le' (s := Finset.univ) (f := A)
    obtain ⟨i, hi⟩ := hfinite.mp hhead
    let d : LTSeries (PrimeSpectrum.zeroLocus (R := R) (A i)) :=
      { length := c.length
        toFun := fun j => ⟨(c j).val, hi.trans (c.monotone (Fin.zero_le j))⟩
        step := fun j => c.step j }
    have hlen : (c.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ A i) := by
      rw [ringKrullDim_quotient]
      exact Order.LTSeries.length_le_krullDim d
    exact hlen.trans (le_iSup (fun i => ringKrullDim (R ⧸ A i)) i)
  · exact iSup_le fun i => quotient_dimension_antitone (iInf_le A i)

end Ideal

end

theorem solution
    {R ι : Type*} [CommRing R] [Finite ι] (A : ι → Ideal R) :
    ringKrullDim (R ⧸ ⨅ i, A i) = ⨆ i, ringKrullDim (R ⧸ A i) := by
  exact Ideal.ringKrullDim_quotient_finite_iInf A
