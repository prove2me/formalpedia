-- Prove2me | solution 1 for MDPComplexity.Discounted.sigma_cost_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:56:41.966935+00:00
-- url     : https://prove2.me/submissions/f959ff00-28da-4c39-ac33-308496d9d87e

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model

open MDPComplexity.Discounted
open Finset

theorem solution {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S)
    (P : M.Sigma s₀) (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    P.cost β = ∑ t ∈ range P.j, β ^ t * P.arcCost t +
      β ^ P.j / (1 - β ^ (P.N - P.j)) * ∑ t ∈ range (P.N - P.j), β ^ t * P.arcCost (P.j + t) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  set L := P.N - P.j with hLdef
  have hL : 0 < L := by have := P.j_lt; omega
  haveI : NeZero L := ⟨hL.ne'⟩
  set C : ℝ := ∑ r ∈ range P.N, |P.arcCost r| with hC
  have hidx : ∀ t, P.arcIdx t < P.N := by
    intro t
    unfold DetMDP.Sigma.arcIdx
    have := P.j_lt
    split_ifs with h
    · omega
    · have := Nat.mod_lt (t - P.j) (show 0 < P.N - P.j from hL); omega
  have hbound : ∀ r, r < P.N → |P.arcCost r| ≤ C := by
    intro r hr
    exact Finset.single_le_sum (f := fun r => |P.arcCost r|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 hr)
  have hgeo : Summable (fun t : ℕ => β ^ t * C) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).mul_right C
  have hsumm : ∀ g : ℕ → ℕ, (∀ t, g t < P.N) → Summable (fun t : ℕ => β ^ t * P.arcCost (g t)) := by
    intro g hg
    refine Summable.of_norm_bounded hgeo ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hbound _ (hg t)) (pow_pos hβ0 t).le
  have hf := hsumm _ hidx
  unfold DetMDP.Sigma.cost
  rw [← hf.sum_add_tsum_nat_add P.j]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    simp [DetMDP.Sigma.arcIdx, ht]
  · have hshift : ∀ u, P.arcIdx (u + P.j) = P.j + u % L := by
      intro u
      unfold DetMDP.Sigma.arcIdx
      rw [if_neg (by omega)]
      congr 2; omega
    simp only [hshift, pow_add]
    have hg2 : ∀ u, P.j + u % L < P.N := by
      intro u; have := Nat.mod_lt u hL; omega
    have e1 : (fun u => β ^ u * β ^ P.j * P.arcCost (P.j + u % L)) =
        fun u => β ^ P.j * (β ^ u * P.arcCost (P.j + u % L)) := by
      funext u; ring
    rw [e1, tsum_mul_left]
    set A := ∑ t ∈ range L, β ^ t * P.arcCost (P.j + t) with hA
    have hs2 := hsumm (fun u => P.j + u % L) hg2
    -- reindex by u = q * L + r
    have hre : ∑' u, β ^ u * P.arcCost (P.j + u % L) = ∑' q : ℕ, (β ^ L) ^ q * A := by
      rw [← (Nat.divModEquiv L).symm.tsum_eq]
      have hs3 : Summable (fun p : ℕ × Fin L =>
          β ^ ((Nat.divModEquiv L).symm p) * P.arcCost (P.j + ((Nat.divModEquiv L).symm p) % L)) :=
        (Nat.divModEquiv L).symm.summable_iff.2 hs2
      rw [hs3.tsum_prod' (fun q => (hasSum_fintype _).summable)]
      congr 1
      funext q
      rw [tsum_fintype, hA, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [Nat.divModEquiv_symm_apply]
      have : (q * L + (r : ℕ)) % L = r := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
      rw [this, show β ^ (q * L + (r : ℕ)) = (β ^ L) ^ q * β ^ (r : ℕ) by
        rw [pow_add, mul_comm q L, pow_mul]]
      ring
    rw [hre, tsum_mul_right, tsum_geometric_of_lt_one (pow_nonneg hβ0.le _)
      (pow_lt_one₀ hβ0.le hβ1 hL.ne')]
    ring
