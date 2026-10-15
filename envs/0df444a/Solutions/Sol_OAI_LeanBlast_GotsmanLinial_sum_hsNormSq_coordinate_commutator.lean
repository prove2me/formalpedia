-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.sum_hsNormSq_coordinate_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:07:40.196647+00:00
-- url     : https://prove2.me/submissions/ef2a0ead-d45f-4c52-a73f-f43d49c6c736

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/CubeOperators.lean:L61-L81
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.sum_hsNormSq_coordinate_commutator. The node keeps its source
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

-- ---- from OAI.Combinatorics.GotsmanLinial.CubeOperators ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Coordinate commutators and Hamming-distance energy

The coordinate sign matrices are the actual diagonal operators of the Boolean
cube. The identities here turn their Hilbert--Schmidt and entry estimates into
the energy estimates used by the edge-recovery argument.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {n : ℕ}

/-- In the point basis, a coordinate commutator records the difference of the
two endpoint signs. -/
theorem coordinate_commutator_apply
    (M : Matrix (Cube n) (Cube n) ℂ) (i : Fin n) (x y : Cube n) :
    (M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y =
      (((cubeCoord y i - cubeCoord x i : ℝ) : ℂ)) * M x y := by
  simp only [coordinateSignMatrix, signMatrix, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.ofReal_sub]
  ring

/-- Squaring a coordinate difference gives four exactly on the coordinates
where the Boolean endpoints differ. -/
theorem coordinate_commutator_sq_norm
    (M : Matrix (Cube n) (Cube n) ℂ) (i : Fin n) (x y : Cube n) :
    ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 =
      (if x i ≠ y i then (4 : ℝ) else 0) * ‖M x y‖ ^ 2 := by
  rw [coordinate_commutator_apply, norm_mul, mul_pow]
  congr 1
  cases hx : x i <;> cases hy : y i <;> norm_num [cubeCoord, hx, hy]

/-- Summing the squared entries over coordinates counts Hamming distance. -/
theorem sum_coordinate_commutator_sq_norm
    (M : Matrix (Cube n) (Cube n) ℂ) (x y : Cube n) :
    (∑ i : Fin n,
      ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2) =
      4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
  classical
  simp_rw [coordinate_commutator_sq_norm, ite_mul, zero_mul]
  calc
    (∑ i : Fin n, if x i ≠ y i then 4 * ‖M x y‖ ^ 2 else 0) =
        ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), 4 * ‖M x y‖ ^ 2 := by
      rw [Finset.sum_filter]
    _ = (hammingDist x y : ℝ) * (4 * ‖M x y‖ ^ 2) := by
      simp [hammingDist, nsmul_eq_mul]
    _ = 4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by ring

/-- The total coordinate-commutator energy is four times the distance-weighted
entry energy. -/
theorem sum_hsNormSq_coordinate_commutator
    (M : Matrix (Cube n) (Cube n) ℂ) :
    (∑ i : Fin n, hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M)) =
      4 * ∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
  classical
  simp only [hsNormSq]
  calc
    (∑ i : Fin n, ∑ x : Cube n, ∑ y : Cube n,
        ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2) =
        ∑ x : Cube n, ∑ y : Cube n, ∑ i : Fin n,
          ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x : Cube n, ∑ y : Cube n,
        4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
      simp_rw [sum_coordinate_commutator_sq_norm]
    _ = 4 * ∑ x : Cube n, ∑ y : Cube n,
        (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
      simp only [Finset.mul_sum, mul_assoc]

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.sum_hsNormSq_coordinate_commutator := @_root_.OAI.LeanBlast.GotsmanLinial.sum_hsNormSq_coordinate_commutator
