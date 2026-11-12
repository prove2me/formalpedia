-- Prove2me | solution 1 for OAI.PerfectCompleteness.Theorem11.exists_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:27:38.873748+00:00
-- url     : https://prove2.me/submissions/dd74a829-eb9e-456b-ad6e-e39fde1d7b63

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_PerfectCompleteness
import Definitions.Def_OAIQ252P018
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedActualBounds_coarseVariation_le_pairedVariation
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedContradiction_meeting_lt_gamma
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedInverseBound_expectedMeeting_ge_gamma
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedMeetingEquality_meeting_probability_eq_expectedMeeting
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedPair_exists_pair
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedUpperProbability_pairedVariation_le
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedUsefulMass_useful_probability_ge_of_reserve
import Theorems.Thm_OAI_PerfectCompleteness_StoppedProjectedUsefulProbability_original_probability_eq_usefulProbability

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]
end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_TwoResponseCollisionLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.UpperParameterScalars

noncomputable section

theorem exists_rows_upward (minimum r : Nat) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ℓ : Nat, minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      ∀ ℓ' : Nat, ℓ ≤ ℓ' → 1 / (2 : ℝ) ^ (ℓ' - r) < ρ / 8 := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (show 0 < ρ / 8 by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  let ℓ := r + k + minimum + 1
  refine ⟨ℓ, by dsimp [ℓ]; omega, by dsimp [ℓ]; omega,
    by dsimp [ℓ]; omega, ?_⟩
  intro ℓ' hℓ'
  have hkℓ : k ≤ ℓ' - r := by dsimp [ℓ] at hℓ'; omega
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hkℓ
  simpa only [div_pow, one_pow] using hp.trans_lt hk

theorem exists_rows (minimum r : Nat) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ℓ : Nat, minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      1 / (2 : ℝ) ^ (ℓ - r) < ρ / 8 := by
  obtain ⟨ℓ, hmin, hr, hpos, hbound⟩ := exists_rows_upward minimum r hρ
  exact ⟨ℓ, hmin, hr, hpos, hbound ℓ le_rfl⟩

theorem exists_rows_rhoPred (minimum r : Nat) {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) :
    ∃ ℓ : Nat, minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      1 / (2 : ℝ) ^ (ℓ - r) < rhoPred κ α / 8 :=
  exists_rows minimum r (rhoPred_pos hκ hα)

theorem exists_repeats_upward {h₀ τ : ℝ} (hh : 0 < h₀) (hτ : 0 < τ) :
    ∃ R : Nat, 6 ≤ R ∧ ∀ R' : Nat, R ≤ R' →
      (7 / 8 : ℝ) ^ R' ≤ min (h₀ / 2) (τ ^ 2 / 2) := by
  have htarget : 0 < min (h₀ / 2) (τ ^ 2 / 2) := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one htarget
    (by norm_num : (7 / 8 : ℝ) < 1)
  refine ⟨k + 6, by omega, ?_⟩
  intro R hR
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 7 / 8)
    (by norm_num : (7 / 8 : ℝ) ≤ 1) (show k ≤ R by omega)
  exact hp.trans hk.le

theorem exists_repeats {h₀ τ : ℝ} (hh : 0 < h₀) (hτ : 0 < τ) :
    ∃ R : Nat, 6 ≤ R ∧ (7 / 8 : ℝ) ^ R ≤ min (h₀ / 2) (τ ^ 2 / 2) := by
  obtain ⟨R, hR, hbound⟩ := exists_repeats_upward hh hτ
  exact ⟨R, hR, hbound R le_rfl⟩

theorem exists_upper_repeats {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α)
    (r ℓ : Nat) :
    ∃ R : Nat, 6 ≤ R ∧ (7 / 8 : ℝ) ^ R ≤
      min (h r ℓ / 2) (tau κ α r ℓ ^ 2 / 2) :=
  exists_repeats (h_pos r ℓ) (tau_pos hκ hα r ℓ)

end
end PerfectCompleteness.UpperParameterScalars

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CoordinateReplacementLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.CubicErrorBounds

theorem pow_sub_one_le_twice {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1)
    (n : Nat) (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n - 1 ≤ 2 * ((n : ℝ) * x) := by
  have hbern := one_add_mul_le_pow (a := -x) (by linarith : (-2 : ℝ) ≤ -x) n
  have hprod : (1 + x) ^ n * (1 - x) ^ n ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (by nlinarith) (by nlinarith)
  have hA : 0 ≤ (1 + x) ^ n := pow_nonneg (by linarith) _
  have hmul := mul_le_mul_of_nonneg_left hbern hA
  simp only [← sub_eq_add_neg, mul_neg] at hmul
  have hbound : (1 + x) ^ n * (1 - (n : ℝ) * x) ≤ 1 := by
    nlinarith
  have hA2 : (1 + x) ^ n ≤ 2 := by nlinarith
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  nlinarith

theorem cube_exponent_identity {m : Nat} (hm : 0 < m) (L : ℝ) :
    ((m ^ 3 : Nat) : ℝ) * (L ^ 2 / (m : ℝ) ^ 4) = L ^ 2 / m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp

theorem sparse_cube_bound {m : Nat} (hm : 0 < m) (L : ℝ)
    (hsmall : L ^ 2 / (m : ℝ) ≤ 1 / 2) :
    (1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1 ≤ 2 * L ^ 2 / m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow : (m : ℝ) ≤ (m : ℝ) ^ 4 := by nlinarith [sq_nonneg ((m : ℝ) ^ 2 - 1)]
  have hx : L ^ 2 / (m : ℝ) ^ 4 ≤ 1 := by
    have h := div_le_div_of_nonneg_left (sq_nonneg L) hmpos hpow
    linarith
  have h := pow_sub_one_le_twice (by positivity) hx (m ^ 3)
    (by simpa only [cube_exponent_identity hm] using hsmall)
  simpa only [cube_exponent_identity hm, mul_div_assoc] using h

theorem posterior_cube_bound {m : Nat} (hm : 2 ≤ m) {L : ℝ} (hL : 0 ≤ L) :
    2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) ≤ 4 * L / (m : ℝ) ^ 2 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hsqpos : (0 : ℝ) < (m : ℝ) ^ 2 := by linarith
  have hfrac : (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ hsqpos).2
    linarith
  have hden : (0 : ℝ) < 1 - 1 / (m : ℝ) ^ 2 := by linarith
  apply (le_div_iff₀ hsqpos).2
  rw [mul_assoc, div_mul_eq_mul_div, ← mul_div_assoc]
  apply (div_le_iff₀ hden).2
  have heq : 2 * ((1 / (m : ℝ) ^ 2) * L * (m : ℝ) ^ 2) = 2 * L := by
    field_simp
  nlinarith [mul_nonneg hL (sub_nonneg.mpr hfrac)]

end PerfectCompleteness.CubicErrorBounds



namespace PerfectCompleteness.CubicErrorSchedule

open CubicErrorBounds

theorem power_mul_growth_le_one {b : ℝ} (hb : 0 ≤ b) (_ : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : ℝ) * (1 - b)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hstep : b * (1 + ((n : ℝ) + 1) * (1 - b)) ≤
        1 + (n : ℝ) * (1 - b) := by nlinarith [mul_nonneg hn (sq_nonneg (1-b))]
    have hprod := mul_le_mul_of_nonneg_left hstep (pow_nonneg hb n)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem clean_cube_bound {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1)
    {m : Nat} (hm : 0 < m) :
    (1 - c / (m : ℝ) ^ 2) ^ (m ^ 3) ≤ 1 / (1 + c * m) := by
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hfrac : c / (m : ℝ) ^ 2 ≤ 1 := (div_le_one (by positivity)).2 (hc'.trans hsq)
  have h := power_mul_growth_le_one (by linarith : 0 ≤ 1-c/(m:ℝ)^2)
    (by have := div_nonneg hc (sq_nonneg (m:ℝ)); linarith : 1-c/(m:ℝ)^2 ≤ 1) (m^3)
  have heq : 1 + ((m ^ 3 : Nat) : ℝ) * (1-(1-c/(m:ℝ)^2)) = 1+c*m := by
    push_cast
    field_simp
    ring
  rw [heq] at h
  exact (le_div_iff₀ (by positivity)).2 h

theorem exists_cube_errors_lt {L c ε : ℝ} (hL : 0 ≤ L)
    (hc : 0 < c) (hc' : c ≤ 1) (hε : 0 < ε) :
    ∃ m : Nat, 2 ≤ m ∧
      Real.sqrt (L ^ 2 / (m : ℝ) ^ 3) / 2 < ε ∧
      Real.sqrt ((1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1) / 2 < ε ∧
      2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) < ε ∧
      (1 - c / (m : ℝ) ^ 2) ^ (m ^ 3) < ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt
    (2 + 2 * L ^ 2 + 2 * L ^ 2 / ε ^ 2 + 4 * L / ε + 1 / (c * ε))
  have hs : 0 ≤ 2 * L ^ 2 / ε ^ 2 := by positivity
  have hp : 0 ≤ 4 * L / ε := by positivity
  have hd : 0 ≤ 1 / (c * ε) := by positivity
  have hm2r : (2 : ℝ) < m := by nlinarith [sq_nonneg L]
  have hm2 : 2 ≤ m := by exact_mod_cast hm2r.le
  have hm0 : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by positivity
  have hsmall : L ^ 2 / (m : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hmr).2
    nlinarith
  have hlarge : 2 * L ^ 2 / ε ^ 2 < (m : ℝ) := by nlinarith [sq_nonneg L]
  have hvar : 2 * L ^ 2 / (m : ℝ) < ε ^ 2 := by
    apply (div_lt_iff₀ hmr).2
    have h := (div_lt_iff₀ (sq_pos_of_pos hε)).1 hlarge
    nlinarith
  have hm3 : (m : ℝ) ≤ (m : ℝ)^3 := by nlinarith [sq_nonneg ((m : ℝ)-1)]
  have hidden : L ^ 2 / (m : ℝ)^3 < ε ^ 2 := by
    have h := div_le_div_of_nonneg_left (sq_nonneg L) hmr hm3
    have hn : 0 ≤ L^2/(m:ℝ) := by positivity
    rw [mul_div_assoc] at hvar
    linarith
  have sparse : (1+L^2/(m:ℝ)^4)^(m^3)-1 < ε^2 :=
    (sparse_cube_bound hm0 L hsmall).trans_lt hvar
  have hsqrt {x : ℝ} (hx : x < ε^2) : Real.sqrt x / 2 < ε := by
    have h := (Real.sqrt_lt' hε).2 hx
    linarith
  refine ⟨m, hm2, hsqrt hidden, hsqrt sparse, ?_, ?_⟩
  · apply (posterior_cube_bound hm2 hL).trans_lt
    have hlarge : 4*L/ε < (m:ℝ) := by nlinarith [sq_nonneg L]
    have hsq : (m:ℝ) ≤ (m:ℝ)^2 := by nlinarith
    apply (div_le_div_of_nonneg_left (by positivity : 0≤4*L) hmr hsq).trans_lt
    apply (div_lt_iff₀ hmr).2
    have h := (div_lt_iff₀ hε).1 hlarge
    nlinarith
  · apply (clean_cube_bound hc.le hc' hm0).trans_lt
    have hlarge : 1/(c*ε) < (m:ℝ) := by nlinarith [sq_nonneg L]
    have h := (div_lt_iff₀ (mul_pos hc hε)).1 hlarge
    apply (div_lt_iff₀ (by positivity : 0 < 1+c*m)).2
    nlinarith

end PerfectCompleteness.CubicErrorSchedule

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_AscendingBranchingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.BucketSampler.directionZero_isEmpty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.AscendingBranching

open scoped BigOperators Classical

noncomputable section

theorem exists_prior_sequence {P : (n : Nat) → (Fin n → Nat) → Nat → Prop}
    (h : ∀ n prior, ∃ x, P n prior x) :
    ∃ values : Nat → Nat, ∀ n, P n (fun i => values i.val) (values n) := by
  let pick := fun n prior => Classical.choose (h n prior)
  let step := fun n (previous : ∀ m, m < n → Nat) =>
    pick n (fun i => previous i.val i.isLt)
  let values : Nat → Nat := fun n => Nat.strongRecOn n step
  refine ⟨values, fun n => ?_⟩
  have hrec : values n = pick n (fun i => values i.val) :=
    Nat.strongRecOn_eq step n
  rw [hrec]
  exact Classical.choose_spec (h n (fun i => values i.val))

theorem exists_ascending_cubes
    (L c : (n : Nat) → (Fin n → Nat) → ℝ)
    (hL : ∀ n prior, 0 ≤ L n prior)
    (hc : ∀ n prior, 0 < c n prior)
    (hc' : ∀ n prior, c n prior ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ size : Nat → Nat, ∀ n,
      CubeErrors (L n (fun i => size i.val ^ 3))
        (c n (fun i => size i.val ^ 3)) ε (size n) := by
  apply exists_prior_sequence (P := fun n prior size =>
    CubeErrors (L n (fun i => prior i ^ 3)) (c n (fun i => prior i ^ 3)) ε size)
  intro n prior
  exact CubicErrorSchedule.exists_cube_errors_lt
    (hL n (fun i => prior i ^ 3))
    (hc n (fun i => prior i ^ 3))
    (hc' n (fun i => prior i ^ 3)) hε

theorem exists_common_accuracy {I : Type*} [Fintype I]
    (tolerance : I → ℝ) (positive : ∀ i, 0 < tolerance i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε < tolerance i := by
  have hfinite : ∀ S : Finset I, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε < tolerance i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a S ha ih =>
      obtain ⟨ε, hε, hsmall⟩ := ih
      refine ⟨min ε (tolerance a) / 2, div_pos (lt_min hε (positive a)) (by norm_num), ?_⟩
      intro i hi
      have hhalf : min ε (tolerance a) / 2 < min ε (tolerance a) := by
        have := lt_min hε (positive a)
        linarith
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hhalf.trans_le (min_le_right _ _)
      · exact (hhalf.trans_le (min_le_left _ _)).trans (hsmall i hi)
  obtain ⟨ε, hε, hsmall⟩ := hfinite Finset.univ
  exact ⟨ε, hε, fun i => hsmall i (Finset.mem_univ i)⟩

end
end PerfectCompleteness.AscendingBranching



namespace PerfectCompleteness.DescendingRows

open scoped BigOperators Classical
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier
open UpperParameterScalars

noncomputable section

variable {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)

theorem exists_rows (r minimum : Nat) :
    ∃ rows : Nat → Nat, ∀ n,
      minimum ≤ rows n ∧ r ≤ rows n ∧ 1 ≤ rows n ∧
        1 / (2 : ℝ) ^ (rows n - r) < rhoPred κ α / 8 ∧
        ∀ i : Fin n, (lowerChoice hκ hα hη r (rows i.val)).minimumRows ≤ rows n := by
  apply AscendingBranching.exists_prior_sequence (P := fun n prior ℓ =>
    minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      1 / (2 : ℝ) ^ (ℓ - r) < rhoPred κ α / 8 ∧
      ∀ i : Fin n, (lowerChoice hκ hα hη r (prior i)).minimumRows ≤ ℓ)
  intro n prior
  let required := fun i : Fin n => (lowerChoice hκ hα hη r (prior i)).minimumRows
  obtain ⟨ℓ, hmin, hr, hpos, hsmall⟩ :=
    exists_rows_rhoPred (minimum + ∑ i, required i) r hκ hα
  refine ⟨ℓ, (Nat.le_add_right _ _).trans hmin, hr, hpos, hsmall, ?_⟩
  intro i
  have hi : required i ≤ ∑ j, required j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (required j)) (Finset.mem_univ i)
  exact hi.trans ((Nat.le_add_left _ _).trans hmin)

end
end PerfectCompleteness.DescendingRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.InitialParameters

open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

theorem epsilon_lt_one {δ : ℚ} (hδ : δ < 1) : epsilon δ < 1 := by
  have : (δ : ℝ) < 1 := by exact_mod_cast hδ
  unfold epsilon
  linarith

theorem exists_initial {δ : ℚ} (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ depth r : Nat, 2 ≤ depth ∧ 4 ≤ (depth : ℝ) * epsilon δ ∧
      1 ≤ r ∧ ∃ α : ℝ, 0 < α ∧ α < 1 ∧
        MatrixLevelBridge.levelCutoffConstant r α + RankLevelFilter.node (r + 1) <
          inverse δ / 2 := by
  have hε := epsilon_pos hδ
  have hε' := epsilon_lt_one hδ'
  obtain ⟨depth, hdepth⟩ := exists_nat_gt (4 / epsilon δ + 2)
  have hd2 : (2 : ℝ) < depth := by
    have := div_pos (by norm_num : (0 : ℝ) < 4) hε
    linarith
  have hd : 2 ≤ depth := by exact_mod_cast hd2.le
  have hmul : 4 ≤ (depth : ℝ) * epsilon δ := by
    have hdiv : 4 / epsilon δ < (depth : ℝ) := by linarith
    exact ((div_lt_iff₀ hε).mp hdiv).le
  obtain ⟨r, hr, α, hα, hα', hcut⟩ :=
    MatrixInverseConstants.exists_cutoff_density
      (show 0 < inverse δ / 2 by have := inverse_pos hδ; positivity)
  exact ⟨depth, r, hd, hmul, hr, α, hα, hα', hcut⟩

end
end PerfectCompleteness.InitialParameters

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_KeyFiniteness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalEdges.coarsen_evaluateLabel _root_.OAI.PerfectCompleteness.CanonicalEdges.restore_coarsen _root_.OAI.PerfectCompleteness.CanonicalKeyShape.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalKeyShape.transport_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_decode _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_symm_val _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport
open scoped BigOperators

variable {n : Nat} {Y : Type*}

theorem card_answer (signs : SourceClause.Triple) : Nat.card (Answer signs) = 7 := by
  simpa only [Nat.card_fin] using Nat.card_congr (answerEquivFinSeven signs)

theorem card_slotDomain_le_seven (s : Slot) : Nat.card s.Domain ≤ 7 := by
  cases s with
  | clause occurrence variableIDs signs => exact (card_answer signs).le
  | bit variableID =>
      change Nat.card Bool ≤ 7
      simp

theorem card_assignment_le_seven_pow (slots : Fin n → Slot) :
    Nat.card (Assignment slots) ≤ 7 ^ n := by
  change Nat.card (∀ i : Fin n, (slots i).Domain) ≤ _
  rw [Nat.card_pi]
  calc
    (∏ i : Fin n, Nat.card (slots i).Domain) ≤ ∏ _i : Fin n, (7 : Nat) :=
      Finset.prod_le_prod' (fun i _ => card_slotDomain_le_seven (slots i))
    _ = 7 ^ n := by simp

end PerfectCompleteness.CanonicalKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionOrderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TreeCardinality

open TreeSourceSpaces HierarchicalArrays
open scoped BigOperators

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem domain_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (Domain slots) ≤ domainBound branch n t := by
  change Nat.card (∀ leaf, LeafDomain slots leaf) ≤ _
  rw [Nat.card_pi]
  calc
    _ ≤ ∏ _leaf : RecursiveSpaces.Slots branch n, (7 ^ t : Nat) :=
      Finset.prod_le_prod' (fun leaf _ =>
        CanonicalKeys.card_assignment_le_seven_pow (slots leaf))
    _ = domainBound branch n t := by simp [domainBound]

theorem subspace_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (V : Submodule F2 (Domain slots → F2)) :
    Nat.card V ≤ functionBound branch n t := by
  calc
    Nat.card V ≤ Nat.card (Domain slots → F2) :=
      Nat.card_le_card_of_injective (fun f : V => f.val) Subtype.val_injective
    _ = 2 ^ Nat.card (Domain slots) := by rw [Nat.card_fun, Nat.card_zmod]
    _ ≤ functionBound branch n t :=
      pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 2) (domain_card_le slots)

theorem H_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (H slots) ≤ functionBound branch n t :=
  subspace_card_le slots (H slots)

theorem square_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (PointwiseSpaces.squareSpace (H slots)) ≤ functionBound branch n t :=
  subspace_card_le slots (PointwiseSpaces.squareSpace (H slots))

theorem arrays_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    Nat.card (Arrays slots rows) ≤ arraysBound branch n t rows := by
  change Nat.card (∀ node : Nodes branch n,
    Fin (rows (Nodes.height node)) → H (nodeSlots slots node)) ≤ _
  rw [Nat.card_pi]
  apply Finset.prod_le_prod'
  intro node _
  rw [Nat.card_fun, Nat.card_fin]
  exact pow_le_pow_left₀ (Nat.zero_le _) (H_card_le (nodeSlots slots node)) _

end
end PerfectCompleteness.TreeCardinality


namespace PerfectCompleteness.ChildBlockCardinality

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem card_le (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (Raw calls rows slots) ≤ bound branch n t calls rows := by
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
  exact Nat.mul_le_mul
    (pow_le_pow_left₀ (Nat.zero_le _) (TreeCardinality.square_card_le slots) calls)
    (TreeCardinality.arrays_card_le slots rows)

theorem bound_pos (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    0 < bound branch n t calls rows :=
  lt_of_lt_of_le (Nat.card_pos (α := Raw calls rows slots)) (card_le calls rows slots)

end
end PerfectCompleteness.ChildBlockCardinality


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceOddListsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOddLists

open SourceClause OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem exists_alphabet_budget (s t : Nat) :
    ∃ L : Nat, 0 < L ∧ alphabetLog s t ≤ L := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (alphabetLog s t) 0)
  refine ⟨L, ?_, (le_max_left _ _).trans hL.le⟩
  have hpos : (0 : ℝ) < L := (le_max_right _ _).trans_lt hL
  exact_mod_cast hpos

end
end PerfectCompleteness.SourceOddLists



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedRows
attribute [-instance] _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedRows

open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

theorem exists_plan {δ : ℚ} (hδ : 0 < δ) (hδ' : δ < 1) : Nonempty (Plan δ) := by
  obtain ⟨depth, r, hd, hmass, hr, α, hα, hα', hspectral⟩ :=
    exists_initial hδ hδ'
  obtain ⟨rows, hrows⟩ := DescendingRows.exists_rows
    (useful_pos hδ) hα (inverse_pos hδ) r 1
  have hreps : ∀ ℓ : Nat, ∃ R : Nat, 6 ≤ R ∧ (7 / 8 : ℝ) ^ R ≤
      min (h r ℓ / 2) (tau (useful δ) α r ℓ ^ 2 / 2) :=
    fun ℓ => exists_upper_repeats (useful_pos hδ) hα r ℓ
  choose repeats hrepeats using hreps
  exact ⟨{
    depth := depth
    depth_ge := hd
    depth_mass := hmass
    order := r
    order_pos := hr
    density := α
    density_pos := hα
    density_lt := hα'
    spectral := hspectral
    rootFirstRows := rows
    rows_order := fun k => (hrows k).2.1
    rows_pos := fun k => (hrows k).2.2.1
    rows_correction := fun k => (hrows k).2.2.2.1
    repeatCount := repeats
    repeats_min := fun ℓ => (hrepeats ℓ).1
    repeats_error := fun ℓ => (hrepeats ℓ).2
    lowerRequirements := fun _ k => (hrows k).2.2.2.2 }⟩

end
end PerfectCompleteness.FixedRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TreeShapeBounds

open TreeCardinality HierarchicalArrays
open scoped BigOperators

theorem slots_card_eq_leafCount (branch : Nat → Nat) (n : Nat) :
    Fintype.card (RecursiveSpaces.Slots branch n) = leafCount branch n := by
  induction n with
  | zero =>
      change Fintype.card Unit = 1
      simp
  | succ n ih =>
      change Fintype.card (Fin (branch n) × RecursiveSpaces.Slots branch n) =
        branch n * leafCount branch n
      rw [Fintype.card_prod, Fintype.card_fin, ih]

theorem domainBound_eq (branch : Nat → Nat) (n t : Nat) :
    domainBound branch n t = domainCountBound branch n t := by
  simp only [domainBound, domainCountBound, slots_card_eq_leafCount]

theorem functionBound_eq (branch : Nat → Nat) (n t : Nat) :
    functionBound branch n t = functionCountBound branch n t := by
  rw [functionBound, functionCountBound, domainBound_eq]

@[simp] theorem domainBound_zero (branch : Nat → Nat) (t : Nat) :
    domainBound branch 0 t = 7 ^ t := by
  rw [domainBound_eq]
  simp [domainCountBound, leafCount]

@[simp] theorem functionBound_zero (branch : Nat → Nat) (t : Nat) :
    functionBound branch 0 t = 2 ^ (7 ^ t) := by
  rw [functionBound, domainBound_zero]

theorem arraysBound_succ (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :
    arraysBound branch (n + 1) t rows =
      functionBound branch (n + 1) t ^ rows (n + 1) *
        arraysBound branch n t rows ^ branch n := by
  change (∏ node : Unit ⊕ (Fin (branch n) × Nodes branch n),
      functionBound branch (Nodes.height (branch := branch) (n := n + 1) node) t ^
        rows (Nodes.height (branch := branch) (n := n + 1) node)) = _
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fintype.prod_unique]
  change (functionBound branch (n + 1) t ^ rows (n + 1)) *
      (∏ _j : Fin (branch n), arraysBound branch n t rows) =
    (functionBound branch (n + 1) t ^ rows (n + 1)) *
      arraysBound branch n t rows ^ branch n
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem arraysBound_eq (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :
    arraysBound branch n t rows = arrayCountBound branch n t rows := by
  induction n with
  | zero => exact arraysBound_zero branch t rows
  | succ n ih =>
      rw [arraysBound_succ, ih, functionBound_eq]
      rfl

theorem leafCount_congr {branch branch' : Nat → Nat} (n : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    leafCount branch n = leafCount branch' n := by
  revert hbranch
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hbranch
      have hlow : ∀ k < n, branch k = branch' k :=
        fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))
      simp only [leafCount, hbranch n (Nat.lt_succ_self n), ih hlow]

theorem domainCountBound_congr {branch branch' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    domainCountBound branch n t = domainCountBound branch' n t := by
  simp only [domainCountBound, leafCount_congr n hbranch]

theorem functionCountBound_congr {branch branch' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    functionCountBound branch n t = functionCountBound branch' n t := by
  rw [functionCountBound, functionCountBound, domainCountBound_congr n t hbranch]

theorem arrayCountBound_congr {branch branch' rows rows' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k)
    (hrows : ∀ k ≤ n, rows k = rows' k) :
    arrayCountBound branch n t rows = arrayCountBound branch' n t rows' := by
  revert hbranch hrows
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
      intro hbranch hrows
      have hlow : ∀ k < n, branch k = branch' k :=
        fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hrowsLow : ∀ k ≤ n, rows k = rows' k :=
        fun k hk => hrows k (Nat.le_trans hk (Nat.le_succ n))
      simp only [arrayCountBound, functionCountBound_congr (n + 1) t hbranch,
        hrows (n + 1) le_rfl, ih hlow hrowsLow, hbranch n (Nat.lt_succ_self n)]

theorem functionBound_congr {branch branch' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    functionBound branch n t = functionBound branch' n t := by
  rw [functionBound_eq, functionBound_eq]
  exact functionCountBound_congr n t hbranch

theorem arraysBound_congr {branch branch' rows rows' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k)
    (hrows : ∀ k ≤ n, rows k = rows' k) :
    arraysBound branch n t rows = arraysBound branch' n t rows' := by
  rw [arraysBound_eq, arraysBound_eq]
  exact arrayCountBound_congr n t hbranch hrows

end PerfectCompleteness.TreeShapeBounds


namespace PerfectCompleteness.ChildBlockCardinality

theorem shape_bound_pos (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) :
    0 < bound branch n t calls rows :=
  bound_pos calls rows (fun _ _ => MixedSupport.Slot.bit 0)

theorem bound_congr {branch branch' : Nat → Nat} (n t calls : Nat)
    {rows rows' : Nat → Nat} (hbranch : ∀ k < n, branch k = branch' k)
    (hrows : ∀ k ≤ n, rows k = rows' k) :
    bound branch n t calls rows = bound branch' n t calls rows' := by
  unfold bound
  rw [TreeShapeBounds.functionBound_congr n t hbranch,
    TreeShapeBounds.arraysBound_congr n t hbranch hrows]


open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

end PerfectCompleteness.ChildBlockCardinality


namespace PerfectCompleteness.FixedBranching

open AscendingBranching ChildBlockCardinality

noncomputable section

theorem cleanRate_pos {cost : Nat} (hcost : 0 < cost) {L : ℝ} (hL : 0 < L) :
    0 < cleanRate cost L := by
  have : (0 : ℝ) < cost := by exact_mod_cast hcost
  unfold cleanRate
  positivity

theorem cleanRate_le_one {cost : Nat} (hcost : 0 < cost) {L : ℝ} (hL : 1 ≤ L) :
    cleanRate cost L ≤ 1 := by
  have hc : (1 : ℝ) ≤ cost := by exact_mod_cast hcost
  have hp : (1 : ℝ) ≤ (cost : ℝ) * L := by nlinarith
  unfold cleanRate
  apply (div_le_one (by positivity)).2
  nlinarith

theorem exists_branching (t cost : Nat) (rows calls : Nat → Nat)
    (hcost : 0 < cost) {ε : ℝ} (hε : 0 < ε) :
    ∃ size : Nat → Nat, ∀ n,
      CubeErrors (bound (fun k => size k ^ 3) n t (calls n) rows : ℝ)
        (cleanRate cost (bound (fun k => size k ^ 3) n t (calls n) rows : ℝ)) ε (size n) := by
  let L := fun n (prior : Fin n → Nat) => (bound (extend prior) n t (calls n) rows : ℝ)
  have hL : ∀ n prior, 0 < L n prior := by
    intro n prior
    dsimp [L]
    exact_mod_cast shape_bound_pos (extend prior) n t (calls n) rows
  have hL1 : ∀ n prior, 1 ≤ L n prior := by
    intro n prior
    dsimp [L]
    exact_mod_cast Nat.succ_le_of_lt (shape_bound_pos (extend prior) n t (calls n) rows)
  obtain ⟨size, hsize⟩ := exists_ascending_cubes L
    (fun n prior => cleanRate cost (L n prior))
    (fun n prior => (hL n prior).le)
    (fun n prior => cleanRate_pos hcost (hL n prior))
    (fun n prior => cleanRate_le_one hcost (hL1 n prior)) hε
  refine ⟨size, fun n => ?_⟩
  have hbound : bound (extend (fun i : Fin n => size i.val ^ 3)) n t (calls n) rows =
      bound (fun k => size k ^ 3) n t (calls n) rows := by
    apply bound_congr n t (calls n)
    · intro k hk
      simp only [extend, dite_eq_left hk]
    · intro k hk
      rfl
  simpa only [L, hbound] using hsize n

end
end PerfectCompleteness.FixedBranching


namespace PerfectCompleteness.FixedSourceBranching

open FixedRows AscendingBranching ChildBlockCardinality

noncomputable section

variable {δ : ℚ} (plan : Plan δ) (hδ : 0 < δ)

theorem exists_source_branching (calls : Nat → Nat) {ε : ℝ} (hε : 0 < ε) :
    ∃ cost : Nat, 0 < cost ∧
      SourceOddLists.alphabetLog (cutoff plan hδ) (sourceLength plan hδ) ≤ cost ∧
      ∃ size : Nat → Nat, ∀ n,
        CubeErrors
          (bound (fun k => size k ^ 3) n (sourceLength plan hδ) (calls n) (rows plan) : ℝ)
          (FixedBranching.cleanRate cost
            (bound (fun k => size k ^ 3) n (sourceLength plan hδ) (calls n) (rows plan) : ℝ))
          ε (size n) := by
  obtain ⟨cost, hcost, hbudget⟩ :=
    SourceOddLists.exists_alphabet_budget (cutoff plan hδ) (sourceLength plan hδ)
  obtain ⟨size, hsize⟩ := FixedBranching.exists_branching
    (sourceLength plan hδ) cost (rows plan) calls hcost hε
  exact ⟨cost, hcost, hbudget, size, hsize⟩

end
end PerfectCompleteness.FixedSourceBranching

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalAdviceExperimentLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalUsefulFamily

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

theorem useful_probability_eq_mean (outer : FiniteDistribution O) (κ : ℝ)
    (upperEvent : (o : O) → Ω o → Bool) :
    (originalLaw S outer).probability (usefulEvent S κ upperEvent) =
      outer.expectation (fun o => (S o).original.probability
        (fun x => usefulEvent S κ upperEvent ⟨o, x⟩)) :=
  CompletionSoundness.sigmaLaw_probability outer (fun o => (S o).original)
    (usefulEvent S κ upperEvent)

end
end PerfectCompleteness.HierarchicalUsefulFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CommonAccuracy
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CommonAccuracy

open FixedRows InitialParameters UpperParameterScalars

noncomputable section

variable {δ : ℚ} (plan : Plan δ)

theorem tolerance_pos (hδ : 0 < δ) (j : Nat) : 0 < tolerance plan j := by
  have hε := epsilon_pos hδ
  have hc := simultaneous_pos hδ
  have hq := q_pos (inverse_pos hδ) plan.order (rows plan j)
  have hγ := gamma_pos (useful_pos hδ) plan.density_pos (inverse_pos hδ)
    plan.order (rows plan j)
  have hα := plan.density_pos
  unfold tolerance
  positivity

theorem exists_accuracy (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j ≤ plan.depth,
      ε < epsilon δ ^ 2 / 40 ∧
      ε < simultaneous δ ^ 2 / 160 ∧
      ε < plan.density * q (inverse δ) plan.order (rows plan j) / 160 ∧
      ε < gamma (useful δ) plan.density (inverse δ) plan.order (rows plan j) ^ 2 / 640 ∧
      ε < gamma (useful δ) plan.density (inverse δ) plan.order (rows plan j) / 40 := by
  obtain ⟨ε, hε, hsmall⟩ := AscendingBranching.exists_common_accuracy
    (fun j : Fin (plan.depth + 1) => tolerance plan j.val)
    (fun j => tolerance_pos plan hδ j.val)
  refine ⟨ε, hε, fun j hj => ?_⟩
  have h := hsmall ⟨j, Nat.lt_succ_of_le hj⟩
  simpa only [tolerance, lt_min_iff] using h

end
end PerfectCompleteness.CommonAccuracy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedCallBudgetLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedParameters

open FixedRows AscendingBranching

noncomputable section

theorem exists_parameters {δ : ℚ} (hδ : 0 < δ) (hδ' : δ < 1) :
    Nonempty (Parameters δ hδ) := by
  obtain ⟨plan⟩ := exists_plan hδ hδ'
  obtain ⟨accuracy, haccuracy, hsmall⟩ := CommonAccuracy.exists_accuracy plan hδ
  obtain ⟨cost, hcost, hcostBound, size, hsize⟩ :=
    FixedSourceBranching.exists_source_branching plan hδ
      (fun _ => calls plan) haccuracy
  refine ⟨{
    plan := plan
    accuracy := accuracy
    accuracy_pos := haccuracy
    accuracy_small := ?_
    alphabetCost := cost
    alphabetCost_pos := hcost
    alphabetCost_bound := hcostBound
    cubeSize := size
    cube_errors := hsize }⟩
  intro j hj
  simpa only [CommonAccuracy.tolerance, lt_min_iff] using hsmall j hj

end
end PerfectCompleteness.FixedParameters

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_PreliminaryOutputLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedPreliminaryValue

open FixedParameters FixedRows FixedPreliminaryGame

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem exists_optimal_strategy (input : List Bool) :
    ∃ strategy : Strategy p input,
      (game p input).success strategy = value p input := by
  let F := PreliminarySampler.family (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
  let : Fintype (HierarchicalGame.LeftVertex F) := Fintype.ofFinite _
  let : Fintype (HierarchicalGame.RightVertex F) := Fintype.ofFinite _
  let : ∀ x, Fintype (HierarchicalGame.LeftLabel F x) := fun _ => Fintype.ofFinite _
  let : ∀ y, Fintype (HierarchicalGame.RightLabel F y) := fun _ => Fintype.ofFinite _
  exact (game p input).exists_optimal_strategy

theorem value_lt_of_strategy_lt (input : List Bool) (bound : ℝ)
    (hbound : ∀ strategy : Strategy p input, (game p input).success strategy < bound) :
    value p input < bound := by
  obtain ⟨strategy, hs⟩ := exists_optimal_strategy p input
  rw [← hs]
  exact hbound strategy

theorem value_le_of_no_large_strategy (input : List Bool) (bound : ℝ)
    (hbound : ∀ strategy : Strategy p input, ¬bound ≤ (game p input).success strategy) :
    value p input ≤ bound :=
  le_of_lt (value_lt_of_strategy_lt p input bound (fun strategy =>
    lt_of_not_ge (hbound strategy)))

end
end PerfectCompleteness.FixedPreliminaryValue


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedProjectedUsefulProbability
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedUsefulProbability

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (κ : ℝ)

local notation "S" => StoppedProjectedExperiment.experiment clauses rows repeats hupper hij
  designated hbranch hrows flag σ

variable (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local instance nativeRowSpaceFintype_r9b0c6b_1 :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _
local instance backgroundFintype_r9b0c6b_1 (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)
local instance rowSpaceFintype_r9b0c6b_1 (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) := Fintype.ofFinite _
theorem usefulMass_eq_original
    (outer : FiniteDistribution (StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))) :
    HierarchicalBucketFamily.usefulMass S κ outer
      (fun o => StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated
        hrows o hbranch flag)
      (fun o => StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
      (fun o => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
      (fun o => StoppedProjectedBuckets.rows_positive rows hupper hrows o) =
      (HierarchicalUsefulFamily.originalLaw S outer).probability
        (HierarchicalUsefulFamily.usefulEvent S κ
          (StoppedProjectedUsefulEvent.upperEvent clauses rows repeats hupper hij designated
            hbranch hrows flag σ)) := by
  have hmean := FiniteDistribution.expectation_congr outer (fun context =>
    (original_probability_eq_usefulProbability clauses rows repeats hupper hij designated
      hbranch hrows flag σ κ context).symm)
  exact hmean.trans (HierarchicalUsefulFamily.useful_probability_eq_mean S outer κ
    (StoppedProjectedUsefulEvent.upperEvent clauses rows repeats hupper hij designated
      hbranch hrows flag σ)).symm

end
end PerfectCompleteness.StoppedProjectedUsefulProbability

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedActualBounds
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedActualBounds

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (strategy : FixedPreliminaryGame.Strategy parameters input)

theorem usefulMass_ge
    (hreserve : InitialParameters.simultaneous δ + 2 * parameters.accuracy ≤
      (StoppedSharedSampler.stoppedLaw
        (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k)
        (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).probability
          (StoppedSharedEvents.pair (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
            strategy (Nat.succ_le_of_lt i.isLt)
            (fun k _ => FixedParameters.branch_pos parameters k) i j)) :
    InitialParameters.simultaneous δ / 2 ≤
      FixedStoppedInverseBound.usefulMass parameters i j hij input strategy := by
  have heq := StoppedProjectedUsefulProbability.usefulMass_eq_original
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (InitialParameters.useful δ) (FixedStoppedInverseBound.outerLaw parameters j input)
  change FixedStoppedInverseBound.usefulMass parameters i j hij input strategy =
    (FixedStoppedUsefulMass.originalLaw parameters i j hij input
      (FixedStoppedPhysicalLaw.designated parameters i) strategy).probability
        (HierarchicalUsefulFamily.usefulEvent
          (FixedStoppedUsefulMass.experiment parameters i j hij input
            (FixedStoppedPhysicalLaw.designated parameters i) strategy)
          (InitialParameters.useful δ)
          (FixedStoppedUsefulMass.upperEvent parameters i j hij input
            (FixedStoppedPhysicalLaw.designated parameters i) strategy)) at heq
  rw [heq]
  exact FixedStoppedUsefulMass.useful_probability_ge_of_reserve parameters i j hij input
    (FixedStoppedPhysicalLaw.designated parameters i) strategy hreserve

end
end PerfectCompleteness.FixedStoppedActualBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedStoppedUpperProbability
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedUpperProbability

noncomputable section

attribute [local instance] FixedStoppedDecoderLaw.sampleFintype
  UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (strategy : FixedPreliminaryGame.Strategy parameters input)

theorem meeting_ge_gamma
    (hreserve : InitialParameters.simultaneous δ + 2 * parameters.accuracy ≤
      (StoppedSharedSampler.stoppedLaw
        (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k)
        (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))).probability
          (StoppedSharedEvents.pair (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
            strategy (Nat.succ_le_of_lt i.isLt)
            (fun k _ => FixedParameters.branch_pos parameters k) i j)) :
    FixedRankContradiction.gamma parameters (j.val + 1) ≤
      (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.meeting parameters i j hij input) := by
  have hpaired := pairedVariation_le parameters i j hij input strategy
  have hmass := FixedStoppedActualBounds.usefulMass_ge parameters i j hij input strategy hreserve
  have hcoarse :=
    (FixedStoppedActualBounds.coarseVariation_le_pairedVariation parameters i j hij input strategy).trans
      hpaired
  have hupper := FixedStoppedInverseBound.expectedMeeting_ge_gamma
    parameters i j hij input strategy hmass hpaired hcoarse
  exact hupper.trans_eq
    (FixedStoppedMeetingEquality.meeting_probability_eq_expectedMeeting
      parameters i j hij input strategy).symm

end
end PerfectCompleteness.FixedStoppedUpperProbability

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedPreliminarySoundness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedPreliminarySoundness

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)

theorem no_large_strategy (input : List Bool)
    (unsat : ¬ BinaryLanguage.language input)
    (strategy : FixedPreliminaryGame.Strategy parameters input)
    (hsuccess : InitialParameters.epsilon δ ≤
      (FixedPreliminaryGame.game parameters input).success strategy) : False := by
  obtain ⟨i, j, hij, hreserve⟩ := FixedStoppedPair.exists_pair parameters input strategy hsuccess
  have hupper := FixedStoppedUpperProbability.meeting_ge_gamma
    parameters i j hij input strategy hreserve
  have hsmall := FixedStoppedContradiction.meeting_lt_gamma
    parameters i j hij input strategy unsat
  exact (not_lt_of_ge hupper) hsmall

end
end PerfectCompleteness.FixedPreliminarySoundness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Theorem11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.Theorem11

noncomputable section

theorem preliminary_value_le {δ : ℚ} {hδ : 0 < δ}
    (parameters : FixedParameters.Parameters δ hδ) (input : List Bool)
    (unsat : ¬BinaryLanguage.language input) :
    FixedPreliminaryGame.value parameters input ≤ InitialParameters.epsilon δ :=
  FixedPreliminaryValue.value_le_of_no_large_strategy parameters input
    (InitialParameters.epsilon δ) (fun strategy hsuccess =>
      FixedPreliminarySoundness.no_large_strategy parameters input unsat strategy hsuccess)

theorem exists_reduction_oai (δ : ℚ) (positive : 0 < δ) (less_than_one : δ < 1) :
    Nonempty (BinaryGapReduction δ) := by
  obtain ⟨parameters⟩ := FixedParameters.exists_parameters positive less_than_one
  exact ⟨FixedBinaryGapReduction.ofPreliminarySoundness parameters
    (preliminary_value_le parameters)⟩

end
end PerfectCompleteness.Theorem11

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.Theorem11.exists_reduction_oai := @OAI.PerfectCompleteness.Theorem11.exists_reduction_oai
