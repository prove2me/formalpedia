-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.schattenPNorm_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-29T02:09:27.044796+00:00
-- url     : https://prove2.me/submissions/9c30fb62-2d78-4414-b144-3ebaba22c687

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_DiagonalNorm
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_singularValuePowerSum_diagonal
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

theorem solution {p : ℝ} (hp : 0 < p) (d : ι → ℂ) :
    schattenPNorm p (diagonalOperator d) = lpNorm p d := by
  rw [schattenPNorm, singularValuePowerSum_diagonal hp]
  rfl
