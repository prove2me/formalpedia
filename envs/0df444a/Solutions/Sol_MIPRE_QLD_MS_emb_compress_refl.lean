-- Prove2me | solution 1 for MIPRE.QLD.MS.emb_compress_refl
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:48.024992+00:00
-- url     : https://prove2.me/submissions/4ccb327b-b3ce-4177-b427-74c41f1d8546

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (solution of MIPRE.QLD.MS.emb_compress_refl);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Anticomm

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem repPOVM_eq (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r) (k : PV) :
    repPOVM MA c k
      = ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k},
          ((MA (Sum.inl c)).mats d).val := rfl
end
end MIPRE.QLD.MS

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.MS
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}
theorem _root_.solution (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    (emb dA)ᴴ * (refl D c j * emb dA)
      = ∑ d : layout.Answer, csgn c j (rep c d) • ((MA (Sum.inl c)).mats d).val := by
  classical
  have hstep : (emb dA)ᴴ * (refl D c j * emb dA)
      = ∑ k : PV, csgn c j k • repPOVM MA c k := by
    rw [refl, pvmObs, Matrix.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, D.compress c k]
  rw [hstep]
  have hfib : ∀ k : PV, csgn c j k • repPOVM MA c k
      = ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k},
          csgn c j (rep c d) • ((MA (Sum.inl c)).mats d).val := by
    intro k
    rw [repPOVM_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [(Finset.mem_filter.mp hd).2]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hfib k]
  exact Finset.sum_fiberwise (univ : Finset layout.Answer) (rep c)
    fun d => csgn c j (rep c d) • ((MA (Sum.inl c)).mats d).val
end MIPRE.QLD.MS
