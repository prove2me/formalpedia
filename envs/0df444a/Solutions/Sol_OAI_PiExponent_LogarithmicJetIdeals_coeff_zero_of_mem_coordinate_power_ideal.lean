-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_zero_of_mem_coordinate_power_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:24:40.675866+00:00
-- url     : https://prove2.me/submissions/f14de62c-ed45-4936-940e-acf8fa0842b2

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (degree : Fin (m + 1) -> Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex)
    (h : S ∈ Ideal.span (Set.range (fun k : Fin (m + 1) =>
      (MvPowerSeries.X k : MvPowerSeries (Fin (m + 1)) Complex) ^ (degree k + 1))))
    (e : Fin (m + 1) -> Nat)
    (he : (k : Fin (m + 1)) -> e k <= degree k) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S = 0 := by
  classical
  rcases Ideal.mem_span_range_iff_exists_fun.mp h with ⟨c, hc⟩
  rw [← hc, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial]
  apply if_neg
  intro hle
  have hcoord : degree k + 1 ≤ e k := by
    simpa using hle k
  exact Nat.not_succ_le_self (degree k) (hcoord.trans (he k))