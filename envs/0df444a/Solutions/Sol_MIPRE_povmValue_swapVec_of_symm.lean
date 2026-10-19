-- Prove2me | solution 1 for MIPRE.povmValue_swapVec_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:38:38.948008+00:00
-- url     : https://prove2.me/submissions/30b06fb1-0346-4fae-b595-9377f924f965

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Swap.lean (solution of MIPRE.povmValue_swapVec_of_symm);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Swap
import Theorems.Thm_MIPRE_bornProb_swapVec

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
theorem _root_.solution {G : Game X X A A} (ψ : dA × dB → ℂ)
    (MA : X → POVM A dA) (MB : X → POVM A dB)
    (hμ : ∀ x y, G.μ x y = G.μ y x) (hD : ∀ x y a b, G.D x y a b = G.D y x b a) :
    povmValue G (swapVec ψ) MB MA = povmValue G ψ MA MB := by
  classical
  have hterm : ∀ x y : X, G.μ x y * condWin G (swapVec ψ) MB MA x y
      = G.μ y x * condWin G ψ MA MB y x := by
    intro x y
    have hcw : condWin G (swapVec ψ) MB MA x y = condWin G ψ MA MB y x := by
      have h : ∀ a b : A,
          (if G.D x y a b then (1 : ℝ) else 0)
              * bornProb (swapVec ψ) (((MB x).mats a).val) (((MA y).mats b).val)
            = (if G.D y x b a then (1 : ℝ) else 0)
              * bornProb ψ (((MA y).mats b).val) (((MB x).mats a).val) := by
        intro a b
        rw [bornProb_swapVec, hD x y a b]
      rw [condWin, condWin, Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        Finset.sum_congr rfl fun b (_ : b ∈ univ) => h a b]
      exact Finset.sum_comm
    rw [hμ x y, hcw]
  rw [povmValue, povmValue, Finset.sum_congr rfl fun x (_ : x ∈ univ) =>
    Finset.sum_congr rfl fun y (_ : y ∈ univ) => hterm x y]
  exact Finset.sum_comm
end MIPRE
