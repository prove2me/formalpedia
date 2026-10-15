-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.sum_mul_eq_zero_of_fourier_separated
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:12:36.245583+00:00
-- url     : https://prove2.me/submissions/23126649-523e-4f98-b862-9e7f89fe4c0f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean:L201-L228
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.sum_mul_eq_zero_of_fourier_separated. The node keeps its source
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
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

/-- Low and high Fourier support with a strict gap have zero counting pairing.
There is no conjugation in this formulation because Walsh characters are real;
it applies directly to the product appearing in the weighted proof. -/
theorem sum_mul_eq_zero_of_fourier_separated {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpaceFrom n s) (hrs : r < s) :
    (∑ x : Cube n, a x * b x) = 0 := by
  classical
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
      obtain ⟨S, hS, rfl⟩ := ha
      obtain ⟨T, hT, rfl⟩ := hb
      have hne : S ≠ T := by
        intro h
        subst T
        exact (not_lt_of_ge (hT.trans hS)) hrs
      simpa only [star_walshChar, ite_eq_right hne] using walshChar_orthogonality S T
  | zero_left b hb => simp
  | zero_right a ha => simp
  | add_left a b c _ _ _ ha hb =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, hb, add_zero]
  | add_right a b c _ _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  | smul_left c a b _ _ hab =>
      simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_zero] using
        congrArg (fun z : ℂ => c * z) hab
  | smul_right c a b _ _ hab =>
      simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum, mul_zero] using
        congrArg (fun z : ℂ => c * z) hab

end

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators symmDiff


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.sum_mul_eq_zero_of_fourier_separated := @_root_.OAI.LeanBlast.GotsmanLinial.sum_mul_eq_zero_of_fourier_separated
