-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_simplex_downward_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:39:10.363991+00:00
-- url     : https://prove2.me/submissions/5e5b7671-e81b-4fe7-bf64-718e9956b659

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} {n : Nat} (v : Fin (m + 1) → Real) (R : Fin n → Real)
    (hR : ∀ i, 0 < R i) (a : Fin (m + 1) → Nat)
    (ha : a ∈ OAI.PiExponent.strictWeightedSimplex v (∑ i, R i))
    (i : Fin n) (b : Fin (m + 1) → Nat) (hba : b ≤ a)
    (hb : ∑ j, v j * (b j : Real) < R i) :
    b ∈ OAI.PiExponent.strictWeightedSimplex v (R i) := by
  classical
  have hRiSum : R i ≤ ∑ k, R k := by
    exact Finset.single_le_sum (fun k hk => (hR k).le) (Finset.mem_univ i)
  have hSumPos : 0 < ∑ k, R k := (hR i).trans_le hRiSum
  simp only [OAI.PiExponent.strictWeightedSimplex, Finset.mem_filter] at ha ⊢
  simp only [OAI.PiExponent.realWeightedSimplex, Fintype.mem_piFinset,
    Finset.mem_filter] at ha ⊢
  constructor
  · constructor
    · intro j
      by_cases hv : 0 < v j
      · have hterms : ∀ k, 0 ≤ v k * (b k : Real) := by
          intro k
          by_cases hk : 0 < v k
          · exact mul_nonneg hk.le (Nat.cast_nonneg _)
          · have hk' : v k ≤ 0 := le_of_not_gt hk
            have hfloor : ⌊(∑ t, R t) / v k⌋₊ = 0 := by
              rw [Nat.floor_eq_zero]
              have hquot : (∑ t, R t) / v k ≤ 0 := div_nonpos_of_nonneg_of_nonpos hSumPos.le hk'
              linarith
            have hAk : a k < ⌊(∑ t, R t) / v k⌋₊ + 1 := Finset.mem_range.mp (ha.1.1 k)
            have hak0 : a k = 0 := by simpa [hfloor] using hAk
            have hbk0 : b k = 0 := le_antisymm (by simpa [hak0] using hba k) (Nat.zero_le _)
            simp [hbk0]
        have hterm : v j * (b j : Real) ≤ ∑ k, v k * (b k : Real) :=
          Finset.single_le_sum (fun k hk => hterms k) (Finset.mem_univ j)
        have hlt : v j * (b j : Real) < R i := lt_of_le_of_lt hterm hb
        have hbdiv : (b j : Real) < R i / v j := (lt_div_iff₀ hv).2 (by nlinarith)
        have hfloor : (b j : Nat) < ⌊R i / v j⌋₊ + 1 := by
          have hcast : (b j : Real) < (↑(⌊R i / v j⌋₊) : Real) + 1 :=
            hbdiv.trans (Nat.lt_floor_add_one (R i / v j))
          exact_mod_cast hcast
        exact Finset.mem_range.mpr hfloor
      · have hv' : v j ≤ 0 := le_of_not_gt hv
        have hfloor : ⌊(∑ t, R t) / v j⌋₊ = 0 := by
          rw [Nat.floor_eq_zero]
          have hquot : (∑ t, R t) / v j ≤ 0 := div_nonpos_of_nonneg_of_nonpos hSumPos.le hv'
          linarith
        have hAj : a j < ⌊(∑ t, R t) / v j⌋₊ + 1 := Finset.mem_range.mp (ha.1.1 j)
        have ha0 : a j = 0 := by simpa [hfloor] using hAj
        have hb0 : b j = 0 := le_antisymm (by simpa [ha0] using hba j) (Nat.zero_le _)
        simp [hb0]
    · exact le_of_lt hb
  · exact hb