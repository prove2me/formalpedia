-- Prove2me | solution 1 for NonmonotoneLS.RLinear.costQ_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T19:50:55.149132+00:00
-- url     : https://prove2.me/submissions/b5b2c40d-e4a9-4aa2-aed2-48d701af0fa4

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter
open NonmonotoneLS.RLinear

/-- Eq. (2.15) (p. 1048): if `η_k ∈ [0, η_max]` for all `k` and `η_max < 1`, then
`Q_{k+1} ≤ 1 + ∑_{j=0}^{k} η_max^{j+1} ≤ 1/(1 - η_max)`. -/
theorem solution (η : ℕ → ℝ) (ηmax : ℝ)
    (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) ηmax)
    (hηmax : ηmax < 1) (k : ℕ) :
    NonmonotoneLS.Shared.costQ η (k + 1) ≤
        1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ∧
      1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ≤
        1 / (1 - ηmax) := by
  -- `hη 0` pins `0 ≤ η 0 ≤ ηmax`, so the bound is nonnegative.
  have hηmax0 : 0 ≤ ηmax := (hη 0).1.trans (hη 0).2
  -- Stronger invariant: `Q_n` is nonnegative and dominated by the partial
  -- geometric sum carrying one more term than the `n` factors actually used.
  have hQ : ∀ n : ℕ,
      0 ≤ NonmonotoneLS.Shared.costQ η n ∧
        NonmonotoneLS.Shared.costQ η n ≤
          ∑ i ∈ Finset.range (n + 1), ηmax ^ i := by
    intro n
    induction n with
    | zero =>
        -- `Q_0 = 1` and the one-term sum is `ηmax ^ 0 = 1`.
        simp [NonmonotoneLS.Shared.costQ]
    | succ n ih =>
        have hηn0 : 0 ≤ η n := (hη n).1
        have hηn_le : η n ≤ ηmax := (hη n).2
        have hmul : η n * NonmonotoneLS.Shared.costQ η n ≤
            ηmax * (∑ i ∈ Finset.range (n + 1), ηmax ^ i) :=
          mul_le_mul hηn_le ih.2 ih.1 hηmax0
        constructor
        · -- Nonnegativity of `Q_{n+1} = η n * Q n + 1`.
          simp only [NonmonotoneLS.Shared.costQ]
          exact add_nonneg (mul_nonneg hηn0 ih.1) zero_le_one
        · -- `geom_sum_succ` with `n + 1` absorbs the added `+ 1`.
          simp only [NonmonotoneLS.Shared.costQ]
          rw [geom_sum_succ]
          -- The goal adds `1` on the right, so use `add_le_add_left` rather
          -- than `add_le_add_right`, which would add it on the left.
          exact add_le_add_left hmul 1
  -- Bridge the theorem's shifted sum to the standard finite geometric sum.
  -- `sum_range_succ'` peels the *first* term, so it lands the `ηmax ^ 0 = 1`
  -- on the right; `add_comm` moves it where the statement writes it.
  have hshift : 1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) =
      ∑ i ∈ Finset.range ((k + 1) + 1), ηmax ^ i := by
    have hs :=
      Finset.sum_range_succ' (fun i : ℕ => ηmax ^ i) (k + 1)
    -- `hs : ∑ i ∈ range (k+1+1), ηmax ^ i = (∑ i ∈ range (k+1), ηmax ^ (i+1)) + ηmax ^ 0`
    simpa only [pow_zero, add_comm] using hs.symm
  refine ⟨?_, ?_⟩
  · -- First conjunct: the invariant at `n = k + 1`.
    rw [hshift]
    exact (hQ (k + 1)).2
  · -- Second conjunct: the `Ico`-form geometric bound, which needs only
    -- `Field` + `LinearOrder` + `IsStrictOrderedRing` (unlike `geom_sum_of_lt_one`,
    -- which additionally demands a `CanonicallyOrderedAdd ℝ` instance that does
    -- not exist). `Nat.Ico_zero_eq_range` turns `Ico 0 N` into `range N`.
    rw [hshift]
    have hbound :
        (∑ i ∈ Finset.Ico 0 ((k + 1) + 1), ηmax ^ i) ≤
          ηmax ^ 0 / (1 - ηmax) :=
      geom_sum_Ico_le_of_lt_one hηmax0 hηmax
    -- `ηmax ^ 0` becomes `1`, which is exactly the `1 / (1 - ηmax)` the goal
    -- states, so no further normalisation is needed.
    rw [Nat.Ico_zero_eq_range, pow_zero] at hbound
    exact hbound
