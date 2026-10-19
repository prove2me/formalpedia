-- Prove2me | solution 1 for OAI.NCHitting.exists_nonzero_divisible_minor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:23:03.5096+00:00
-- url     : https://prove2.me/submissions/b388a2b7-0078-4f7c-96ed-1dfa4e0845f5

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/MinorFactor.lean:L15-L38
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.exists_nonzero_divisible_minor. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis

-- ---- from OAI.Algebra.FormulaHitting.Minors ----
namespace OAI

noncomputable section

namespace NCHitting

open Matrix Finset Polynomial

variable {R : Type*} [CommRing R]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

theorem det_rectangular_mul (A : Matrix I J R) (B : Matrix J I R) :
    (A * B).det = ∑ f : I → J, (A.submatrix id f).det * ∏ i, B (f i) i := by
  classical
  calc
    (A * B).det = ∑ f : I → J, ∑ σ : Equiv.Perm I,
        (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
        Finset.prod_mul_distrib, Finset.sum_mul, mul_assoc]

theorem exists_minor_ne_zero_of_mul_det_ne_zero (A : Matrix I J R)
    (B : Matrix J I R) (h : (A * B).det ≠ 0) :
    ∃ f : I → J, (A.submatrix id f).det ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply h
  simp [det_rectangular_mul, hn]

end NCHitting

end

end OAI

-- ---- from OAI.Algebra.FormulaHitting.MinorFactor ----
namespace OAI

noncomputable section

namespace NCHitting

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R]
variable {K I : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

theorem exists_nonzero_divisible_minor
    (Z H : Matrix K I R) (G : Matrix I I R) (D W : Matrix K K R)
    (C : Matrix K I R) (E : Matrix I K R)
    (hG : IsUnit G) (hD : D.det ≠ 0) (hW : W.det ≠ 0)
    (hZG : Z * G = D * H) (hHC : H = W * C) (hHE : W = H * E) :
    ∃ f : K → I, (Z.submatrix id f).det ≠ 0 ∧ W.det ∣ (Z.submatrix id f).det := by
  classical
  have hprod : Z * (G * E) = D * W := by
    rw [← Matrix.mul_assoc, hZG, Matrix.mul_assoc, ← hHE]
  have hprod0 : (Z * (G * E)).det ≠ 0 := by
    rw [hprod, Matrix.det_mul]
    exact mul_ne_zero hD hW
  obtain ⟨f, hf⟩ := exists_minor_ne_zero_of_mul_det_ne_zero Z (G * E) hprod0
  refine ⟨f, hf, ?_⟩
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hZ : Z = (D * W) * (C * G⁻¹) := by
    calc
      Z = (Z * G) * G⁻¹ := (Matrix.mul_nonsing_inv_cancel_right G Z hGdet).symm
      _ = (D * W) * (C * G⁻¹) := by rw [hZG, hHC]; simp only [Matrix.mul_assoc]
  have hsub : Z.submatrix id f = (D * W) * ((C * G⁻¹).submatrix id f) := by
    rw [hZ]
    rfl
  rw [hsub, Matrix.det_mul, Matrix.det_mul]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open Matrix


theorem solution : type_of% @_root_.OAI.NCHitting.exists_nonzero_divisible_minor := @_root_.OAI.NCHitting.exists_nonzero_divisible_minor
