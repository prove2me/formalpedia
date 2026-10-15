-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.adjacent_iff_hammingDist_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:14:36.351376+00:00
-- url     : https://prove2.me/submissions/7d2d0d0d-a387-4e63-a7e5-23e8973914b7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/SignParity.lean:L118-L141
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.adjacent_iff_hammingDist_eq_one. The node keeps its source
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

-- ---- from OAI.Combinatorics.GotsmanLinial.Statement ----
namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

theorem flip_apply_ne {n : ℕ} (i : Fin n) (x : Cube n) (j : Fin n) (h : j ≠ i) :
    flip i x j = x j := by
  simp [flip, h]

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

/-- The flip definition of adjacency agrees with Hamming distance one. -/
theorem adjacent_iff_hammingDist_eq_one {n : ℕ} (x y : Cube n) :
    CubeAdjacent x y ↔ hammingDist x y = 1 := by
  classical
  constructor
  · rintro ⟨i, rfl⟩
    exact hammingDist_flip i x
  · intro hxy
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hxy
    refine ⟨i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      have hmem : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by rw [hi]; simp
      have hneq : x i ≠ y i := (Finset.mem_filter.mp hmem).2
      rw [flip_apply_same]
      cases hx : x i <;> cases hy : y i <;> simp_all
    · have heq : x j = y j := by
        by_contra hneq
        have hmem : j ∈ Finset.univ.filter (fun j => x j ≠ y j) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hneq⟩
        rw [hi] at hmem
        exact hj (Finset.mem_singleton.mp hmem)
      rw [flip_apply_ne i x j hj, heq]

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.adjacent_iff_hammingDist_eq_one := @_root_.OAI.LeanBlast.GotsmanLinial.adjacent_iff_hammingDist_eq_one
