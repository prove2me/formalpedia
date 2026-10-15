-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.fourierSpace_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:09:43.542974+00:00
-- url     : https://prove2.me/submissions/0bdd14ce-1356-4e71-bffb-700517f02c68

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean:L125-L150
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.fourierSpace_mul. The node keeps its source
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

/-- A character of degree at most `d` belongs to the corresponding filtration. -/
theorem walshChar_mem_fourierSpace {S : Finset (Fin n)} (hS : S.card ≤ d) :
    walshChar S ∈ fourierSpace n d :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- The filtration is multiplicative. The symmetric difference of two index
sets has cardinality at most the sum of their cardinalities. -/
theorem fourierSpace_mul {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpace n s) :
    a * b ∈ fourierSpace n (r + s) := by
  classical
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
      obtain ⟨S, hS, rfl⟩ := ha
      obtain ⟨T, hT, rfl⟩ := hb
      have hST : (S ∆ T).card ≤ r + s :=
        (Finset.card_le_card Finset.symmDiff_subset_union).trans
          ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT))
      convert walshChar_mem_fourierSpace hST using 1
      ext x
      exact walshChar_mul S T x
  | zero_left b hb => simp
  | zero_right a ha => simp
  | add_left a b c _ _ _ ha hb =>
      simpa only [add_mul] using (fourierSpace n (r + s)).add_mem ha hb
  | add_right a b c _ _ _ ha hb =>
      simpa only [mul_add] using (fourierSpace n (r + s)).add_mem ha hb
  | smul_left c a b _ _ hab =>
      simpa only [smul_mul_assoc] using (fourierSpace n (r + s)).smul_mem c hab
  | smul_right c a b _ _ hab =>
      simpa only [mul_smul_comm] using (fourierSpace n (r + s)).smul_mem c hab

end

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators symmDiff


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.fourierSpace_mul := @_root_.OAI.LeanBlast.GotsmanLinial.fourierSpace_mul
