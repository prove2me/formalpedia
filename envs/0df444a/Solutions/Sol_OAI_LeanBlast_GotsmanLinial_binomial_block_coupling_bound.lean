-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.binomial_block_coupling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:05:03.005477+00:00
-- url     : https://prove2.me/submissions/bb176f95-a34b-40b3-92bf-d7e9d9382bab

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/BlockCoupling.lean:L62-L133
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.binomial_block_coupling_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_finite_one_sided_coupling_bound
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sum_choose_centered_sq_range

-- ---- from OAI.Combinatorics.GotsmanLinial.BinomialMoments ----
namespace OAI

/-!
Exact finite moments of the symmetric binomial weights. These identities provide
the grading multiplicities and the variance used in the finite coupling estimate.
No probabilistic assumptions or measures enter the statements.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

/-- The normalizing denominator is positive, also when `n = 0`. -/
theorem binomialDenominator_pos (n : ℕ) : 0 < (2 : ℝ) ^ n :=
  pow_pos (by norm_num) n

theorem binomialDenominator_ne_zero (n : ℕ) : (2 : ℝ) ^ n ≠ 0 :=
  ne_of_gt (binomialDenominator_pos n)

/-- The real sum of one row of Pascal's triangle. -/
theorem sum_choose_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = (2 : ℝ) ^ n := by
  exact_mod_cast Nat.sum_range_choose n

/-- The same total mass on the grading-index type. -/
theorem sum_choose (n : ℕ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ)) = (2 : ℝ) ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℝ))]
  exact sum_choose_range n

theorem sum_choose_centered_sq (n : ℕ) :
    (∑ k : Fin (n + 1),
      (n.choose k.val : ℝ) * ((k.val : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (n.choose k : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2)]
  exact sum_choose_centered_sq_range n

theorem sum_binomialWeight (n : ℕ) : (∑ k : Fin (n + 1), binomialWeight n k) = 1 := by
  unfold binomialWeight
  rw [← Finset.sum_div, sum_choose, div_self (binomialDenominator_ne_zero n)]

theorem binomialWeight_variance (n : ℕ) :
    (∑ k : Fin (n + 1), binomialWeight n k * ((k.val : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) / 4 := by
  unfold binomialWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_choose_centered_sq]
  field_simp [binomialDenominator_ne_zero n]

/-- The binomial coefficients are invariant under reflection about `n/2`. -/
theorem choose_reflect (n : ℕ) (k : Fin (n + 1)) :
    n.choose (n - k.val) = n.choose k.val :=
  Nat.choose_symm (Nat.le_of_lt_succ k.isLt)

theorem choose_rev (n : ℕ) (k : Fin (n + 1)) :
    n.choose k.rev.val = n.choose k.val := by
  simpa only [Fin.val_rev, Nat.add_sub_add_right] using choose_reflect n k

theorem binomialWeight_rev (n : ℕ) (k : Fin (n + 1)) :
    binomialWeight n k.rev = binomialWeight n k := by
  simp only [binomialWeight, choose_rev]

theorem index_rev_real (n : ℕ) (k : Fin (n + 1)) :
    (k.rev.val : ℝ) = (n : ℝ) - (k.val : ℝ) := by
  rw [Fin.val_rev, Nat.add_sub_add_right, Nat.cast_sub (Nat.le_of_lt_succ k.isLt)]

/-- Reflecting a binomial index preserves every real finite expectation. -/
theorem binomialWeight_reflect (n : ℕ) (φ : ℝ → ℝ) :
    (∑ k : Fin (n + 1), binomialWeight n k * φ ((n : ℝ) - (k.val : ℝ))) =
      ∑ k : Fin (n + 1), binomialWeight n k * φ (k.val : ℝ) := by
  have h := Equiv.sum_comp (Fin.revPerm (n := n + 1))
    (fun k : Fin (n + 1) => binomialWeight n k * φ (k.val : ℝ))
  change (∑ k : Fin (n + 1), binomialWeight n k.rev * φ (k.rev.val : ℝ)) = _ at h
  simpa only [binomialWeight_rev, index_rev_real] using h

/-- Standard deviation corresponding to the preceding finite variance identity. -/
theorem binomialSigma_sq (n : ℕ) : (Real.sqrt (n : ℝ) / 2) ^ 2 = (n : ℝ) / 4 := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  norm_num

theorem binomialSigma_nonneg (n : ℕ) : 0 ≤ Real.sqrt (n : ℝ) / 2 :=
  div_nonneg (Real.sqrt_nonneg _) (by norm_num)

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.BlockCoupling ----
namespace OAI

/-!
# The finite block coupling

Normalize a nonnegative matrix of block masses, identify its two binomial
marginals, and reflect its first index.  The low-degree block vanishing gives
the one-sided displacement bound required by the finite coupling lemma.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

theorem normalizedPairWeight_nonneg {α β : Type*}
    (B : α → β → ℝ) (Z : ℝ) (hB : ∀ r s, 0 ≤ B r s) (hZ : 0 ≤ Z)
    (t : α × β) : 0 ≤ normalizedPairWeight B Z t :=
  div_nonneg (hB t.1 t.2) hZ

/-- First-coordinate expectations are computed from the row sums. -/
theorem normalizedPairWeight_expect_fst {α β : Type*} [Fintype α] [Fintype β]
    (B : α → β → ℝ) (Z : ℝ) (φ : α → ℝ) :
    (∑ t : α × β, normalizedPairWeight B Z t * φ t.1) =
      ∑ r : α, ((∑ s : β, B r s) / Z) * φ r := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp only [normalizedPairWeight]
  rw [← Finset.sum_mul, ← Finset.sum_div]

/-- Second-coordinate expectations are computed from the column sums. -/
theorem normalizedPairWeight_expect_snd {α β : Type*} [Fintype α] [Fintype β]
    (B : α → β → ℝ) (Z : ℝ) (φ : β → ℝ) :
    (∑ t : α × β, normalizedPairWeight B Z t * φ t.2) =
      ∑ s : β, ((∑ r : α, B r s) / Z) * φ s := by
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro s _
  simp only [normalizedPairWeight]
  rw [← Finset.sum_mul, ← Finset.sum_div]

/-- Finite masses with binomial row and column sums, supported above the
anti-diagonal `r+s=n-d`, have the required centered quadratic bound. -/
theorem binomial_block_coupling_bound
    (n d : ℕ) (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hB : ∀ r s, 0 ≤ B r s)
    (hrow : ∀ r, (∑ s : Fin (n + 1), B r s) = (n.choose r.val : ℝ))
    (hcol : ∀ s, (∑ r : Fin (n + 1), B r s) = (n.choose s.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → B r s = 0) :
    (∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ((s.val : ℝ) + (r.val : ℝ) - (n : ℝ)) ^ 2 * B r s) ≤
        4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  let w : Fin (n + 1) × Fin (n + 1) → ℝ :=
    normalizedPairWeight B ((2 : ℝ) ^ n)
  let U : Fin (n + 1) × Fin (n + 1) → ℝ := fun t => (t.2.val : ℝ)
  let V : Fin (n + 1) × Fin (n + 1) → ℝ :=
    fun t => (n : ℝ) - (t.1.val : ℝ)
  have hU (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (U t)) =
        ∑ s : Fin (n + 1), binomialWeight n s * φ (s.val : ℝ) := by
    simpa only [w, U, hcol, binomialWeight] using
      normalizedPairWeight_expect_snd B ((2 : ℝ) ^ n)
        (fun s => φ (s.val : ℝ))
  have hV (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (V t)) =
        ∑ r : Fin (n + 1),
          binomialWeight n r * φ ((n : ℝ) - (r.val : ℝ)) := by
    simpa only [w, V, hrow, binomialWeight] using
      normalizedPairWeight_expect_fst B ((2 : ℝ) ^ n)
        (fun r => φ ((n : ℝ) - (r.val : ℝ)))
  have hw : ∀ t, 0 ≤ w t :=
    normalizedPairWeight_nonneg B _ hB (binomialDenominator_pos n).le
  have hprob : (∑ t, w t) = 1 := by
    have h := hU (fun _ => 1)
    simpa only [mul_one, sum_binomialWeight] using h
  have hsame : ∀ φ : ℝ → ℝ,
      (∑ t, w t * φ (U t)) = ∑ t, w t * φ (V t) := by
    intro φ
    rw [hU, hV, binomialWeight_reflect]
  have hvariance :
      (∑ t, w t * (U t - (n : ℝ) / 2) ^ 2) =
        (Real.sqrt (n : ℝ) / 2) ^ 2 := by
    rw [hU (fun z => (z - (n : ℝ) / 2) ^ 2)]
    rw [binomialWeight_variance, binomialSigma_sq]
  have hstep : ∀ t, w t ≠ 0 → V t - U t ≤ (d : ℝ) := by
    rintro ⟨r, s⟩ ht
    have hnonzero : B r s ≠ 0 := by
      intro hz
      exact ht (by simp only [w, normalizedPairWeight, hz, zero_div])
    have hnat : n - d ≤ r.val + s.val :=
      Nat.le_of_not_gt (fun hlt => hnonzero (hvanish r s hlt))
    have hnat' : n ≤ r.val + s.val + d := by omega
    have hreal : (n : ℝ) ≤ (r.val : ℝ) + (s.val : ℝ) + (d : ℝ) := by
      exact_mod_cast hnat'
    dsimp only [U, V]
    linarith
  have hbound := finite_one_sided_coupling_bound w U V
    ((n : ℝ) / 2) (Real.sqrt (n : ℝ) / 2) (d : ℝ)
    hw hprob hsame (binomialSigma_nonneg n) (Nat.cast_nonneg d) hvariance hstep
  calc
    _ = (2 : ℝ) ^ n * (∑ t, w t * (U t - V t) ^ 2) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [w, U, V, normalizedPairWeight]
      field_simp [binomialDenominator_ne_zero n]
      ring
    _ ≤ (2 : ℝ) ^ n * (8 * (d : ℝ) * (Real.sqrt (n : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hbound (binomialDenominator_pos n).le
    _ = 4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by ring

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.binomial_block_coupling_bound := @_root_.OAI.LeanBlast.GotsmanLinial.binomial_block_coupling_bound
