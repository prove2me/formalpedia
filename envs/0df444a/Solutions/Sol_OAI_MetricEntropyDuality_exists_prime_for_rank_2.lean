-- Prove2me | solution 2 for OAI.MetricEntropyDuality.exists_prime_for_rank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:46:55.652583+00:00
-- url     : https://prove2.me/submissions/75ee866f-08f7-4ddc-b416-a9a392f1770d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/PrimeChoice.lean:L77-L100
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.exists_prime_for_rank. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport

-- ---- from OAI.Analysis.MetricEntropy.FormDimension ----
namespace OAI

universe uK

/-!
# Dimension of symmetric-form coefficients

The coefficients of a symmetric `j`-linear form on an `r`-dimensional space
are indexed by multisets of `j` basis vectors. Their number gives the
dimension of the coefficient space and hence its cardinality over a finite field.
-/

namespace MetricEntropyDuality

/-- Positive ambient dimension gives a nonempty coefficient index set. -/
theorem formDimension_pos {r j : ℕ} (hr : 0 < r) : 0 < formDimension r j := by
  exact Nat.choose_pos (Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_left hr))

end MetricEntropyDuality

end OAI

-- ---- from OAI.Analysis.MetricEntropy.Parameters ----
namespace OAI

/-!
# Parameters fixed before the prime is chosen

These are the literal accuracy, pivot-slot, direction-count and encoding-cost
parameters of the construction. The radius and rank are genuinely available
for every proposed comparison constant. Their existence does not depend on
the eventual field size.
-/

noncomputable section

namespace MetricEntropyDuality

theorem accuracy_pos {a : ℝ} (ha : 1 ≤ a) : 0 < accuracy a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  unfold accuracy
  positivity

theorem pivotSlots_pos {θ : ℝ} (hθ : 0 < θ) : 0 < pivotSlots θ := by
  apply Nat.ceil_pos.mpr
  exact one_div_pos.mpr hθ

theorem compressionRadius_pos (a : ℝ) : 0 < compressionRadius a :=
  Nat.succ_pos _

theorem directionCount_pos {r h : ℕ} {θ : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hθ : 0 < θ) :
    0 < directionCount r h θ := by
  apply Nat.ceil_pos.mpr
  have hD : (0 : ℝ) < formDimension r h := Nat.cast_pos.mpr (formDimension_pos hr)
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  positivity

theorem encodingCost_pos {h u : ℕ} {θ : ℝ}
    (hh : 0 < h) (hθ : 0 < θ) (hu : 0 < u) : 0 < encodingCost h θ u := by
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hsR : (0 : ℝ) < pivotSlots θ := Nat.cast_pos.mpr (pivotSlots_pos hθ)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ u := by positivity
  have hquot : 0 < (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ :=
    div_pos (mul_pos hsR hpow) hθ
  have hlog : 0 < Real.log (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) :=
    Real.log_pos (by linarith)
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (Nat.succ_le_of_lt hu)
  exact add_pos_of_nonneg_of_pos (Real.log_nonneg hu1)
    (mul_pos (mul_pos (mul_pos hhR hsR) hpow) hlog)

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.PrimeChoice ----
namespace OAI

/-!
# Choosing the prime after the finite parameters

The field size is chosen after the dimension,
direction count, and encoding cost. Infinitude of primes permits all these
bounds to be imposed simultaneously, without any upper bound on the prime.
-/

noncomputable section

namespace MetricEntropyDuality

/-- A natural prime exceeds every prescribed real bound. -/
theorem exists_prime_gt_real (bound : ℝ) :
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  exact ⟨p, hp, hn.trans_le (Nat.cast_le.mpr hnp)⟩

/-- All parameters, including the encoding cost, precede the choice of prime. -/
theorem exists_prime_after_parameters (h u D : ℕ) (C B bound : ℝ) :
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) ∧ h < p ∧
      h ^ 2 * u ^ (2 * h) < p ∧ Real.exp (B * C / (D : ℝ)) < (p : ℝ) := by
  obtain ⟨p, hp, hall⟩ := exists_prime_gt_real
    (max (max bound (h : ℝ))
      (max ((h ^ 2 * u ^ (2 * h) : ℕ) : ℝ) (Real.exp (B * C / (D : ℝ)))))
  obtain ⟨hleft, hright⟩ := max_lt_iff.mp hall
  obtain ⟨hbound, hh⟩ := max_lt_iff.mp hleft
  obtain ⟨hsize, hexp⟩ := max_lt_iff.mp hright
  exact ⟨p, hp, hbound, Nat.cast_lt.mp hh, Nat.cast_lt.mp hsize, hexp⟩

theorem prime_log_pos {p : ℕ} (hp : p.Prime) : 0 < Real.log (p : ℝ) := by
  apply Real.log_pos
  simpa only [Nat.cast_one] using
    (Nat.cast_lt.mpr hp.one_lt : ((1 : ℕ) : ℝ) < (p : ℝ))

/-- The exponential lower bound on the prime absorbs the fixed encoding cost. -/
theorem prime_choice_entropy_lt {p D : ℕ} (hD : 0 < D)
    {B C : ℝ} (hchoice : Real.exp (B * C / (D : ℝ)) < (p : ℝ)) :
    B * C < (D : ℝ) * Real.log (p : ℝ) := by
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hlog := Real.log_lt_log (Real.exp_pos (B * C / (D : ℝ))) hchoice
  rw [Real.log_exp] at hlog
  exact (div_lt_iff₀' hDreal).mp hlog

/-- Positivity of the encoding cost is not needed for this comparison. -/
theorem prime_choice_encoding_ratio_lt {p D : ℕ} (hp : p.Prime) (hD : 0 < D)
    {B C : ℝ} (hB : 0 < B)
    (hchoice : Real.exp (B * C / (D : ℝ)) < (p : ℝ)) :
    2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B := by
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  apply (div_lt_div_iff₀ (mul_pos hDreal (prime_log_pos hp)) hB).mpr
  have hbudget := prime_choice_entropy_lt hD hchoice
  calc
    (2 * C) * B = 2 * (B * C) := by rw [mul_assoc, mul_comm C B]
    _ < 2 * ((D : ℝ) * Real.log (p : ℝ)) :=
      mul_lt_mul_of_pos_left hbudget zero_lt_two

/-- A single prime satisfies the finite construction and entropy bounds. -/
theorem exists_prime_with_entropy_budget (h u D : ℕ) (C B bound : ℝ)
    (hD : 0 < D) (hB : 0 < B) :
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) ∧ h < p ∧
      h ^ 2 * u ^ (2 * h) < p ∧ Real.exp (B * C / (D : ℝ)) < (p : ℝ) ∧
      0 < Real.log (p : ℝ) ∧ B * C < (D : ℝ) * Real.log (p : ℝ) ∧
      2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B := by
  obtain ⟨p, hp, hbound, hh, hsize, hexp⟩ :=
    exists_prime_after_parameters h u D C B bound
  exact ⟨p, hp, hbound, hh, hsize, hexp, prime_log_pos hp,
    prime_choice_entropy_lt hD hexp, prime_choice_encoding_ratio_lt hp hD hB hexp⟩

/-- The finite parameters are all fixed before the prime.
The caller may impose any additional real lower bound on the prime. -/
theorem exists_prime_for_rank {a : ℝ} (ha : 1 ≤ a) {r : ℕ} (hr : 0 < r)
    (B bound : ℝ) (hB : 0 < B) :
    let h := compressionRadius a
    let D := formDimension r h
    let u := directionCount r h (accuracy a)
    let C := encodingCost h (accuracy a) u
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) ∧ h < p ∧
      h ^ 2 * u ^ (2 * h) < p ∧ Real.exp (B * C / (D : ℝ)) < (p : ℝ) ∧
      0 < Real.log (p : ℝ) ∧ B * C < (D : ℝ) * Real.log (p : ℝ) ∧
      2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B ∧ 0 < C := by
  let h := compressionRadius a
  let D := formDimension r h
  let u := directionCount r h (accuracy a)
  let C := encodingCost h (accuracy a) u
  have hh : 0 < h := compressionRadius_pos a
  have hθ := accuracy_pos ha
  have hD : 0 < D := formDimension_pos (j := h) hr
  have hu : 0 < u := directionCount_pos hr hh hθ
  have hC : 0 < C := encodingCost_pos hh hθ hu
  obtain ⟨p, hp, hbound, hhp, hsize, hexp, hlog, hbudget, hratio⟩ :=
    exists_prime_with_entropy_budget h u D C B bound hD hB
  exact ⟨p, hp, hbound, hhp, hsize, hexp, hlog, hbudget, hratio, hC⟩

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.exists_prime_for_rank := @_root_.OAI.MetricEntropyDuality.exists_prime_for_rank
