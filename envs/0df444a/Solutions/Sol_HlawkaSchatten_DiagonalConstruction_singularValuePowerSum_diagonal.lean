-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.singularValuePowerSum_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-29T01:46:37.498447+00:00
-- url     : https://prove2.me/submissions/3f8db73d-b956-43f1-85c2-c96f82707e65

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_DiagonalNorm
import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_HermitianSpectral
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Diagonal operators and coordinate power sums

This connects the coordinate proof to the singular-value Schatten norm
used in the publication boundary. The Gram operator has the coordinate
basis as an eigenbasis, with eigenvalues equal to squared entry norms.
-/


open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem diagonalOperator_adjoint (d : ι → ℂ) :
    (diagonalOperator d).adjoint = diagonalOperator (fun i ↦ star (d i)) := by
  unfold diagonalOperator
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  split_ifs with h <;> simp_all

@[simp]
theorem diagonalOperator_apply (d : ι → ℂ) (x : EuclideanSpace ℂ ι) (i : ι) :
    diagonalOperator d x i = d i * x i := by
  exact Matrix.mulVec_diagonal d (WithLp.ofLp x) i

theorem diagonalOperator_apply_basis (d : ι → ℂ) (i : ι) :
    diagonalOperator d (EuclideanSpace.basisFun ι ℂ i) =
      d i • EuclideanSpace.basisFun ι ℂ i := by
  ext j
  simp [EuclideanSpace.basisFun_apply]
  split_ifs with h <;> simp_all

theorem diagonalOperator_gram (d : ι → ℂ) :
    (diagonalOperator d).adjoint.comp (diagonalOperator d) =
      diagonalOperator (fun i ↦ (‖d i‖ ^ 2 : ℝ)) := by
  rw [diagonalOperator_adjoint]
  ext x i
  simp only [LinearMap.comp_apply, diagonalOperator_apply]
  rw [← mul_assoc]
  congr 1
  exact Complex.normSq_eq_conj_mul_self.symm.trans
    (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq (d i)))

theorem solution {p : ℝ} (hp : 0 < p) (d : ι → ℂ) :
    singularValuePowerSum p (diagonalOperator d) = ∑ i, ‖d i‖ ^ p := by
  rw [singularValuePowerSum_eq_re_trace_gramFunctionalCalculus hp,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun ι ℂ), Complex.re_sum]
  apply Fintype.sum_congr
  intro i
  rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul
    (fun y ↦ y ^ (p / 2)) _ _ _ (‖d i‖ ^ 2)
    (by rw [diagonalOperator_gram, diagonalOperator_apply_basis])]
  rw [inner_smul_right, (EuclideanSpace.basisFun ι ℂ).inner_eq_one, mul_one,
    Complex.ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring
