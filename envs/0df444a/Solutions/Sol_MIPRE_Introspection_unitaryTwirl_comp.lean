-- Prove2me | solution 1 for MIPRE.Introspection.unitaryTwirl_comp
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:56.348934+00:00
-- url     : https://prove2.me/submissions/79d4afb1-0cfa-41d4-9db2-d077597cfb91

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ComposedTwirl.lean (solution of MIPRE.Introspection.unitaryTwirl_comp);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix
variable {dA dB I J A : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I] [Fintype J] [Fintype A]
theorem _root_.solution (μ : I → ℝ) (ν : J → ℝ)
    (U : I → Matrix dA dA ℂ) (V : J → Matrix dA dA ℂ) (M : Matrix dA dA ℂ) :
    unitaryTwirl ν V (unitaryTwirl μ U M) =
      unitaryTwirl (fun p : I × J => μ p.1 * ν p.2) (fun p => V p.2 * U p.1) M := by
  classical
  simp only [unitaryTwirl, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Finset.smul_sum, smul_smul, Fintype.sum_prod_type,
    Matrix.conjTranspose_mul, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (ν j : ℂ) (μ i : ℂ)]
  congr 1
  noncomm_ring
end MIPRE.Introspection
