-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_product_bound_explicit
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:50:49.722137+00:00
-- url     : https://prove2.me/submissions/a04eeea5-6317-4748-bc21-98af36f549e7

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open Filter
open scoped Topology BigOperators

/-- Eventually, the product of the box side lengths `⌈H / w i⌉₊ + 1` is bounded by
`(∏ (1 / w i + 2)) * (H + 1) ^ (m + 1)`. -/
theorem solution {m : ℕ} (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∀ᶠ H : ℝ in atTop,
      (∏ i : Fin (m + 1), ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ)) ≤
        (∏ i : Fin (m + 1), (1 / w i + 2)) * (H + 1) ^ (m + 1) := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  have hbound : ∀ i : Fin (m + 1),
      ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ) ≤ (1 / w i + 2) * (H + 1) := by
    intro i
    have hwpos : 0 < w i := hw i
    have hx : 0 ≤ H / w i := div_nonneg hH hwpos.le
    have hceil : ((⌈H / w i⌉₊ : ℕ) : ℝ) < H / w i + 1 := Nat.ceil_lt_add_one hx
    have hcast : ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ) = ((⌈H / w i⌉₊ : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    have hpos1 : (0 : ℝ) ≤ 1 / w i := by positivity
    have hpos2 : (0 : ℝ) ≤ H := hH
    have hmain : (1 / w i + 2) * (H + 1) = H / w i + 1 / w i + 2 * H + 2 := by
      ring
    rw [hmain]
    linarith
  calc (∏ i : Fin (m + 1), ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ))
      ≤ ∏ i : Fin (m + 1), ((1 / w i + 2) * (H + 1)) := by
        apply Finset.prod_le_prod
        · intro i _
          positivity
        · intro i _
          exact hbound i
    _ = (∏ i : Fin (m + 1), (1 / w i + 2)) * (H + 1) ^ (m + 1) := by
        rw [Finset.prod_mul_distrib]
        congr 1
        simp
