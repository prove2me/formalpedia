-- Prove2me | solution 1 for MarkovMixing.stationary_pos_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:23.235193+00:00
-- url     : https://prove2.me/submissions/5e211945-67ea-4467-88d1-0c282fc5aaaf

import Mathlib
import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_pow_entry_nonneg
import Theorems.Thm_MarkovMixing_vecMul_pow

-- carved verbatim out of submission b36a2a77-0ed1-410e-b982-dafb4dc643a6, lines 536-552

section
open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    have := hπ.1.2
    linarith
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have h2 : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  have := mul_pos hy ht
  linarith

end
