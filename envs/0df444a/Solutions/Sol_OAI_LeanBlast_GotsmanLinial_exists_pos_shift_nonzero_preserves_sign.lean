-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.exists_pos_shift_nonzero_preserves_sign
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:13:15.051797+00:00
-- url     : https://prove2.me/submissions/e3c73869-c51b-4a5f-91b2-24c66fb4424e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/SignParity.lean:L56-L82
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.exists_pos_shift_nonzero_preserves_sign. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity

-- ---- from OAI.Combinatorics.GotsmanLinial.SignParity ----
namespace OAI

/-!
# Removing threshold zeros and turning sensitive edges into constant-sign edges

All graph pairs are ordered. The cube coordinates are the real
signs encoded by `Bool` in the public statement.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

private theorem exists_pos_lt_finset {α : Type*} (s : Finset α) (a : α → ℝ)
    (ha : ∀ x ∈ s, 0 < a x) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ε < a x := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by norm_num, by simp⟩
  | @insert x s hx ih =>
      intro ha
      obtain ⟨ε, hε, hεa⟩ := ih (fun y hy => ha y (Finset.mem_insert_of_mem hy))
      have hax : 0 < a x := ha x (Finset.mem_insert_self x s)
      refine ⟨min ε (a x / 2), lt_min hε (by linarith), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (hεa y hy)

/-- A positive constant removes all zeros of a real function on a finite set
without changing its threshold signs, including the convention `sign(0)=1`. -/
theorem exists_pos_shift_nonzero_preserves_sign {α : Type*} [Fintype α]
    (v : α → ℝ) : ∃ ε : ℝ, 0 < ε ∧ (∀ x, v x + ε ≠ 0) ∧
      (∀ x, thresholdSign (v x + ε) = thresholdSign (v x)) := by
  classical
  let a : α → ℝ := fun x => if v x < 0 then -v x else 1
  have ha : ∀ x ∈ (Finset.univ : Finset α), 0 < a x := by
    intro x _
    by_cases hx : v x < 0
    · simp [a, hx, neg_pos.mpr hx]
    · simp [a, hx]
  obtain ⟨ε, hε, hεa⟩ := exists_pos_lt_finset Finset.univ a ha
  have hneg : ∀ x, v x < 0 → v x + ε < 0 := by
    intro x hx
    have he : ε < -v x := by simpa [a, hx] using hεa x (Finset.mem_univ x)
    linarith
  refine ⟨ε, hε, ?_, ?_⟩
  · intro x
    by_cases hx : v x < 0
    · exact ne_of_lt (hneg x hx)
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (le_of_not_gt hx) hε)
  · intro x
    by_cases hx : v x < 0
    · simp [thresholdSign, not_le.mpr hx, not_le.mpr (hneg x hx)]
    · have hv : 0 ≤ v x := le_of_not_gt hx
      simp [thresholdSign, hv, add_nonneg hv hε.le]

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.exists_pos_shift_nonzero_preserves_sign := @_root_.OAI.LeanBlast.GotsmanLinial.exists_pos_shift_nonzero_preserves_sign
