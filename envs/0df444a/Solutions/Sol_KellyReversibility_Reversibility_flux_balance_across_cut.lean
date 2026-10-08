-- Prove2me | solution 1 for KellyReversibility.Reversibility.flux_balance_across_cut
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:59:39.915071+00:00
-- url     : https://prove2.me/submissions/3aa036d0-6358-4f50-b82d-27cdf54f7554

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

set_option autoImplicit false

open KellyReversibility.Reversibility in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibrium π q) (A : Finset S) :
    ∑ j ∈ A, ∑ k ∈ Aᶜ, π j * q j k = ∑ j ∈ A, ∑ k ∈ Aᶜ, π k * q k j := by
  have h : ∀ j, ∑ k, π j * q j k = ∑ k, π k * q k j := fun j => by
    rw [← Finset.mul_sum]
    have := hπ.2.2 j
    simpa [tsum_fintype] using this
  have h2 : ∀ j, ∑ k ∈ A, π j * q j k + ∑ k ∈ Aᶜ, π j * q j k
      = ∑ k ∈ A, π k * q k j + ∑ k ∈ Aᶜ, π k * q k j := fun j => by
    rw [Finset.sum_add_sum_compl, Finset.sum_add_sum_compl]
    exact h j
  have h3 := Finset.sum_congr rfl (fun j (_ : j ∈ A) => h2 j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h3
  have h4 : ∑ j ∈ A, ∑ k ∈ A, π j * q j k = ∑ j ∈ A, ∑ k ∈ A, π k * q k j :=
    Finset.sum_comm
  linarith
