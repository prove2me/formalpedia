-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.polynomialValue_mem_fourierSpace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:08:19.539986+00:00
-- url     : https://prove2.me/submissions/47af0687-fa71-4e2e-b1a7-081d36de54d9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean:L92-L106
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.polynomialValue_mem_fourierSpace. The node keeps its source
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

/-- Every exponent occurring in a supported multilinear monomial is one. -/
theorem IsMultilinear.exponent_eq_one {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) {m : Fin n →₀ ℕ} (hm : m ∈ p.support)
    {i : Fin n} (hi : i ∈ m.support) : m i = 1 := by
  exact Nat.le_antisymm (hp m hm i)
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

/-- A supported monomial has no more variables than the polynomial's total
degree. This estimate does not require multilinearity. -/
theorem monomial_support_card_le_totalDegree {p : MvPolynomial (Fin n) ℝ}
    {m : Fin n →₀ ℕ} (hm : m ∈ p.support) : m.support.card ≤ p.totalDegree := by
  calc
    m.support.card = ∑ _i ∈ m.support, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hm

/-- Faithful evaluation of a multilinear polynomial as products over
the supports of its monomials. -/
theorem polynomialValue_eq_multilinear_expansion {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (x : Cube n) :
    polynomialValue p x =
      ∑ m ∈ p.support, p.coeff m * ∏ i ∈ m.support, cubeCoord x i := by
  classical
  unfold polynomialValue
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hp.exponent_eq_one hm hi, pow_one]

/-- The same faithful expansion, with values regarded as complex numbers. -/
theorem polynomialValue_walsh_expansion {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (x : Cube n) :
    (polynomialValue p x : ℂ) =
      ∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) * walshChar m.support x := by
  rw [polynomialValue_eq_multilinear_expansion hp]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, walshChar]

/-- A character of degree at most `d` belongs to the corresponding filtration. -/
theorem walshChar_mem_fourierSpace {S : Finset (Fin n)} (hS : S.card ≤ d) :
    walshChar S ∈ fourierSpace n d :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- The exact polynomial bridge into the complex Walsh filtration. -/
theorem polynomialValue_mem_fourierSpace {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    (fun x => (polynomialValue p x : ℂ)) ∈ fourierSpace n d := by
  classical
  have hsum : (∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) • walshChar m.support) ∈
      fourierSpace n d := by
    apply Submodule.sum_mem
    intro m hm
    exact Submodule.smul_mem _ _
      (walshChar_mem_fourierSpace ((monomial_support_card_le_totalDegree hm).trans hd))
  convert hsum using 1
  ext x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    polynomialValue_walsh_expansion hp x

end

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators symmDiff


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.polynomialValue_mem_fourierSpace := @_root_.OAI.LeanBlast.GotsmanLinial.polynomialValue_mem_fourierSpace
