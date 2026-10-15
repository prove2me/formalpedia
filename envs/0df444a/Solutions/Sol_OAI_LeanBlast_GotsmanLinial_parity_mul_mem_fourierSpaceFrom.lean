-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.parity_mul_mem_fourierSpaceFrom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:11:08.328952+00:00
-- url     : https://prove2.me/submissions/9e51f4b7-f2b7-444c-9b8d-b798dd4f530d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean:L179-L199
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.parity_mul_mem_fourierSpaceFrom. The node keeps its source
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

-- ---- from OAI.Combinatorics.GotsmanLinial.Walsh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Walsh characters of the Boolean cube

The characters are the real sign monomials, regarded as complex-valued
functions.  Counting orthogonality proves linear independence; the cardinality
comparison then gives a basis.  The degree filtration and its dimensions are
constructed from this concrete basis.
-/

noncomputable section

open scoped BigOperators symmDiff
open Finset Submodule Module

namespace LeanBlast.GotsmanLinial

theorem walshChar_univ_mul {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar Finset.univ x * walshChar S x = walshChar (Finset.univ \ S) x := by
  rw [walshChar_mul]
  congr 1
  ext i
  simp [Finset.mem_symmDiff]

end LeanBlast.GotsmanLinial

end

end OAI

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

theorem walshChar_mem_fourierSpaceFrom {S : Finset (Fin n)} (hS : d ≤ S.card) :
    walshChar S ∈ fourierSpaceFrom n d :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- Full parity complements character index sets, taking low degree `d` to
Fourier support in degrees at least `n - d`. -/
theorem parity_mul_mem_fourierSpaceFrom {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n d) :
    (fun x => walshChar Finset.univ x * a x) ∈ fourierSpaceFrom n (n - d) := by
  classical
  change walshChar Finset.univ * a ∈ fourierSpaceFrom n (n - d)
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨S, hS, rfl⟩ := ha
      have hSc : n - d ≤ (Finset.univ \ S).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simpa using Nat.sub_le_sub_left hS n
      convert walshChar_mem_fourierSpaceFrom hSc using 1
      ext x
      exact walshChar_univ_mul S x
  | zero => simp
  | add a b _ _ ha hb =>
      simpa only [mul_add] using (fourierSpaceFrom n (n - d)).add_mem ha hb
  | smul c a _ ha =>
      simpa only [mul_smul_comm] using (fourierSpaceFrom n (n - d)).smul_mem c ha

end

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators symmDiff


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.parity_mul_mem_fourierSpaceFrom := @_root_.OAI.LeanBlast.GotsmanLinial.parity_mul_mem_fourierSpaceFrom
