-- Prove2me | solution 1 for MIPRE.SeededGame.quantumValue_ge_of_oracular
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:29.982203+00:00
-- url     : https://prove2.me/submissions/872c53e8-8f6a-44bc-9090-212fced0e125

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (solution of MIPRE.SeededGame.quantumValue_ge_of_oracular);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Theorems.Thm_MIPRE_SeededGame_tensorSound_value_ge

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SeededGame
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
variable (S)
theorem _root_.solution {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < quantumValue S.oracular.toGame) :
    1 - 24 * √ε ≤ quantumValue S.toGame := by
  by_cases hε1 : ε ≤ 1
  · by_contra hcon
    rw [not_le] at hcon
    have hall : ∀ N : TensorProductStrategy S.oracular.toGame, N.value ≤ 1 - ε := by
      intro N
      by_contra hN
      rw [not_le] at hN
      have h1 := tensorSound_value_ge N hε.le hε1 hN.le
      have h2 : (S.tensorSound N).value ≤ quantumValue S.toGame :=
        le_ciSup (TensorProductStrategy.bddAbove_range_value _) (S.tensorSound N)
      linarith
    have h3 : quantumValue S.oracular.toGame ≤ 1 - ε := Real.iSup_le hall (by linarith)
    linarith
  · rw [not_le] at hε1
    have h1 : 1 < √ε := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt zero_le_one hε1
    have h2 := quantumValue_nonneg S.toGame
    linarith
end MIPRE.SeededGame
