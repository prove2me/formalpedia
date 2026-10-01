-- Prove2me | solution 1 for LiouvilleDiffAlg.ratFunc_residue_not_reg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:43:00.488589+00:00
-- url     : https://prove2.me/submissions/14f753af-da28-4202-9f9f-4fbc5b80936c

import Mathlib

open scoped Differential
open Polynomial

theorem solution {K : Type*} [Field K] {p q : K[X]} (hp : Irreducible p)
    (hpq : ¬ p ∣ q) {c : K} (hc : c ≠ 0) :
    ¬ ∃ a b : K[X], ¬ p ∣ b ∧ algebraMap K (RatFunc K) c * (algebraMap K[X] (RatFunc K) q / algebraMap K[X] (RatFunc K) p) * algebraMap K[X] (RatFunc K) b = algebraMap K[X] (RatFunc K) a := by
  rintro ⟨a, b, hb, h⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hι0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hp0
  have hκ : algebraMap K (RatFunc K) c = algebraMap K[X] (RatFunc K) (C c) := by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K) c, Polynomial.algebraMap_eq]
  have h2 : algebraMap K[X] (RatFunc K) (C c * q * b) = algebraMap K[X] (RatFunc K) (a * p) := by
    rw [map_mul, map_mul, map_mul, ← hκ, ← h]
    field_simp
  have h3 := (IsFractionRing.injective K[X] (RatFunc K)) h2
  have hd : p ∣ C c * q * b := ⟨a, by rw [h3]; ring⟩
  have hpr := hp.prime
  rcases hpr.dvd_or_dvd hd with h4 | h4
  · rcases hpr.dvd_or_dvd h4 with h5 | h5
    · exact hp.not_isUnit (isUnit_of_dvd_unit h5 (isUnit_C.2 (Ne.isUnit hc)))
    · exact hpq h5
  · exact hb h4
