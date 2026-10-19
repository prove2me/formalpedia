-- Prove2me | solution 1 for IntMul.Kappa.kappa_bound_of_linear_overhead
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:53:43.082878+00:00
-- url     : https://prove2.me/submissions/41f49616-bc98-4273-ac58-06e9ac8fca62

import Definitions.Def_IntMul_MultitapeModel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul

theorem solution
    (κ c d : ℝ) (hκ : κ ≤ 1) (hc : 0 < c) (hd : 0 ≤ d)
    (M : MultitapeTM)
    (hcorrect : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, MultipliesAt M n T)
    (n₀ : ℕ)
    (hcost : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
      MultipliesAt M n
        (c * ((n : ℝ) * ((lg n : ℝ) ^ (1 - κ))) + d * n)) :
    KappaBound κ := by
  change MulTimeBound (fun n : ℕ =>
    (n : ℝ) * ((lg n : ℝ) ^ (1 - κ)))
  refine ⟨M, hcorrect, c + d, by linarith, n₀, ?_⟩
  intro n hn hn1 x y hx hy
  obtain ⟨t, ht, hout⟩ := hcost n hn hn1 x y hx hy
  refine ⟨t, ?_, hout⟩
  have hbase_nat : 1 ≤ lg n := le_max_right (Nat.clog 2 n) 1
  have hbase : (1 : ℝ) ≤ (lg n : ℝ) := by
    exact_mod_cast hbase_nat
  have hexp : 0 ≤ (1 : ℝ) - κ := by linarith
  have hp : (1 : ℝ) ≤ ((lg n : ℝ) ^ (1 - κ)) :=
    Real.one_le_rpow hbase hexp
  have hnon : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hn_le : (n : ℝ) ≤ (n : ℝ) * ((lg n : ℝ) ^ (1 - κ)) := by
    calc
      (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * ((lg n : ℝ) ^ (1 - κ)) :=
        mul_le_mul_of_nonneg_left hp hnon
  have hlin :
      d * (n : ℝ) ≤ d * ((n : ℝ) * ((lg n : ℝ) ^ (1 - κ))) :=
    mul_le_mul_of_nonneg_left hn_le hd
  calc
    (t : ℝ) ≤ c * ((n : ℝ) * ((lg n : ℝ) ^ (1 - κ))) + d * n := ht
    _ ≤ c * ((n : ℝ) * ((lg n : ℝ) ^ (1 - κ))) +
        d * ((n : ℝ) * ((lg n : ℝ) ^ (1 - κ))) :=
      add_le_add_right hlin _
    _ = (c + d) * ((n : ℝ) * ((lg n : ℝ) ^ (1 - κ))) := by ring
