-- Prove2me | solution 1 for Nullstellensatz.nullstellensatz
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:48:11.890732+00:00
-- url     : https://prove2.me/submissions/b42cf12e-04b3-44a1-ac1d-46bba7454b05

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem aux_nss_mem_radical {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k)) (p : MvPolynomial (Fin n) k)
    (hp : ∀ a : Fin n → K, (∀ f ∈ J, aeval a f = 0) → aeval a p = 0) :
    p ∈ J.radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) J]
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro a ha
  exact hp a ((MvPolynomial.mem_zeroLocus_iff).1 ha)

end Nullstellensatz

open Nullstellensatz
open MvPolynomial

theorem solution {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k)) (p : MvPolynomial (Fin n) k)
    (hp : ∀ a : Fin n → K, (∀ f ∈ J, aeval a f = 0) → aeval a p = 0) :
    ∃ r : ℕ, p ^ r ∈ J :=
  aux_nss_mem_radical J p hp
