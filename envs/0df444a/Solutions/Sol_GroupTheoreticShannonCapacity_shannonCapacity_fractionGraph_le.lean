-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:44.248534+00:00
-- url     : https://prove2.me/submissions/c455583a-b2f6-4df5-8ad7-834a60a284a6

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_strongPower_fractionGraph_le

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (p q : ℕ) [NeZero p] (hq : 0 < q) (hpq : q ≤ p) :
    shannonCapacity (fractionGraph p q) ≤ (p : ℝ) / q := by
  -- The proof uses the fractional clique cover bound:
  -- If G has a fractional clique cover of weight w, then Θ(G) ≤ w.
  --
  -- For E_{p/q}^⊠(n+1), the "product arcs" form a clique cover:
  -- - Product arc: for each start ∈ (ZMod p)^(n+1), the arc is
  --   {(start₁ + j₁, ..., start_{n+1} + j_{n+1}) : 0 ≤ jₖ < q}
  -- - There are p^(n+1) product arcs, each is a clique
  -- - Each vertex is in exactly q^(n+1) product arcs
  -- - Weight 1/q^(n+1) per arc gives coverage weight 1 per vertex
  -- - Total weight = p^(n+1) / q^(n+1) = (p/q)^(n+1)
  --
  -- By the fractional clique cover bound:
  --   α(E_{p/q}^⊠(n+1)) ≤ (p/q)^(n+1)
  --
  -- Taking (n+1)-th root: α^(1/(n+1)) ≤ p/q
  simp only [shannonCapacity]
  apply ciSup_le
  intro n
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
  have hp_pos : (0 : ℝ) < p := by
    have : 0 < p := NeZero.pos p
    exact_mod_cast this
  have hpq_pos : (0 : ℝ) < (p : ℝ) / q := div_pos hp_pos hq_pos
  -- Key claim: α(E_{p/q}^⊠(n+1)) ≤ (p/q)^(n+1)
  have hbound := independenceNumber_strongPower_fractionGraph_le p q hq hpq n
  -- Now take (n+1)-th root
  have hn_pos : (0 : ℝ) < n + 1 := by positivity
  calc ((strongPower (fractionGraph p q) (n + 1)).indepNum : ℝ) ^ (1 / (n + 1 : ℝ))
      ≤ (((p : ℝ) / q) ^ (n + 1)) ^ (1 / (n + 1 : ℝ)) := by
          apply Real.rpow_le_rpow
          · exact Nat.cast_nonneg _
          · exact hbound
          · positivity
    _ = (p : ℝ) / q := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpq_pos)]
          simp only [Nat.cast_add, Nat.cast_one, mul_one_div, div_self (ne_of_gt hn_pos)]
          exact Real.rpow_one _
end GroupTheoreticShannonCapacity
