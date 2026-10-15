-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:22:41.045449+00:00
-- url     : https://prove2.me/submissions/5c52f5a4-c4c3-40f3-9d73-aa3d77bfbd24

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Main.lean:L121-L125
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_LeanBlast_GotsmanLinial_gotsmanLinialStatement) verbatim and is proved by it.
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WalshDimensions
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WeightedGrading
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_GradingShift
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_exists_pos_shift_nonzero_preserves_sign
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_polynomialThreshold_averageSensitivity_le_of_nonzero

-- ---- from OAI.Combinatorics.GotsmanLinial.PolynomialDegree ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Polynomial degree and the Walsh filtration

The polynomial lemmas concern real multilinear
`MvPolynomial`s. Restriction to the cube is justified by an explicit monomial
expansion rather than assumed as an alternate polynomial representation.
-/

open scoped BigOperators symmDiff

namespace LeanBlast.GotsmanLinial

noncomputable section

variable {n d : ℕ}

/-- Adding a constant preserves the multilinearity condition. -/
theorem IsMultilinear.add_C {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (c : ℝ) : IsMultilinear (p + MvPolynomial.C c) := by
  classical
  intro m hm i
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hm | hm
  · exact hp m hm i
  · have hm0 : m = 0 := by
      by_cases hc : c = 0
      · simp [hc] at hm
      · simpa [MvPolynomial.support_C, hc] using hm
    simp [hm0]

/-- Adding a constant cannot violate an existing total-degree upper bound. -/
theorem totalDegree_add_C_le {p : MvPolynomial (Fin n) ℝ}
    (hd : p.totalDegree ≤ d) (c : ℝ) :
    (p + MvPolynomial.C c).totalDegree ≤ d := by
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le hd (by simp))

end

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.SignParity ----
namespace OAI

/-!
# Removing threshold zeros and turning sensitive edges into constant-sign edges

All graph pairs are ordered. The cube coordinates are the real
signs encoded by `Bool` in the public statement.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

/-- The zero-removal reduction preserves multilinearity, the degree bound,
and the entire threshold function. -/
theorem exists_nonzero_polynomial_same_threshold {n d : ℕ}
    {p : MvPolynomial (Fin n) ℝ} (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin n) ℝ,
      IsMultilinear q ∧ q.totalDegree ≤ d ∧
        (∀ x : Cube n, polynomialValue q x ≠ 0) ∧
        polynomialThreshold q = polynomialThreshold p := by
  obtain ⟨ε, _hε, hnonzero, hsign⟩ :=
    exists_pos_shift_nonzero_preserves_sign (polynomialValue p)
  refine ⟨p + MvPolynomial.C ε, hp.add_C ε, totalDegree_add_C_le hd ε, ?_, ?_⟩
  · intro x
    simpa only [polynomialValue_add_C] using hnonzero x
  · funext x
    simpa only [polynomialThreshold, polynomialValue_add_C] using hsign x

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.Main ----
namespace OAI

/-!
# Assembly of the Gotsman--Linial average-sensitivity bound

The first lemmas are explicitly conditional assembly bridges. The final
theorems discharge their matrix and counting hypotheses using the concrete
weighted Boolean-cube grading and a sign-preserving constant perturbation.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

/-- Every real multilinear polynomial of degree at most `d` has average
sensitivity at most `8*d*sqrt(n)`, including cube zeros under `sign(0)=1`.
The argument in fact covers all natural `n` and `d`. -/
theorem polynomialThreshold_averageSensitivity_le {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  obtain ⟨q, hq, hqd, hqnz, hqf⟩ := exists_nonzero_polynomial_same_threshold hp hd
  rw [← hqf]
  exact polynomialThreshold_averageSensitivity_le_of_nonzero q hq hqd hqnz

/-- The average-sensitivity bound for `1 ≤ d ≤ n`, without auxiliary
construction hypotheses. -/
theorem gotsmanLinialStatement : GotsmanLinialStatement := by
  intro n d _ _ _ p hp hd
  exact polynomialThreshold_averageSensitivity_le p hp hd

end LeanBlast.GotsmanLinial

end OAI

-- ---- mission target ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators

theorem solution : GotsmanLinialStatement := by
  first
    | exact OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement
    | (apply OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement <;> assumption)
    | (intros; apply OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement <;> assumption)
