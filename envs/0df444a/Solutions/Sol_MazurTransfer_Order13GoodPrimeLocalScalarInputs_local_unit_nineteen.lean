-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeLocalScalarInputs.local_unit_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T03:31:37.017184+00:00
-- url     : https://prove2.me/submissions/bc9cb02b-a22f-4328-b14c-eab78fcd1ff3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME selected local Picard law is commutative and
nineteen is invertible in the actual coefficient ring at other primes.
Named downstream consumer: finite flat etale local scalar nineteen and
the SAME integral norm factors.
-/
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps

noncomputable section
open MazurTransfer.Order13LocalIntegralCoefficientMaps

theorem solution (q : ℕ) [Fact q.Prime] (hne : q ≠ 19) : IsUnit (19 : LocalRing q) := by
  have h : (19 : ℤ) ∈ (primeIdeal q).primeCompl := by
    change (19 : ℤ) ∉ Ideal.span {(q : ℤ)}
    rw [Ideal.mem_span_singleton]
    intro hd
    have hnat : q ∣ 19 := Int.natCast_dvd_natCast.mp hd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp hnat with hq | hq
    · exact (Fact.out : q.Prime).ne_one hq
    · exact hne hq
  simpa only [map_ofNat] using IsLocalization.map_units (LocalRing q) ⟨19, h⟩

#print axioms solution
