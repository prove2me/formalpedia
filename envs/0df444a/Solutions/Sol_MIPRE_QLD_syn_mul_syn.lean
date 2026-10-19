-- Prove2me | solution 1 for MIPRE.QLD.syn_mul_syn
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:36:44.013268+00:00
-- url     : https://prove2.me/submissions/95a16a19-cb82-435d-b5a1-17ad39c48447

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapState.lean (solution of MIPRE.QLD.syn_mul_syn);
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
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Definitions.Def_MIPRE_Background_QLD_SwapState
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem _root_.solution {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w)
    (v v' : n → F) (a a' : F) :
    syn w v a * syn w v' a'
      = ∑ e ∈ univ.filter fun e => dotF e v = a ∧ dotF e v' = a', proj w e := by
  classical
  rw [syn, syn, Finset.sum_mul]
  have hterm : ∀ e ∈ univ.filter fun e : n → F => dotF e v = a,
      (proj w e * ∑ e' ∈ univ.filter fun e' : n → F => dotF e' v' = a', proj w e')
        = if dotF e v' = a' then proj w e else 0 := by
    intro e _
    rw [Finset.mul_sum]
    by_cases hs : dotF e v' = a'
    · rw [if_pos hs,
        Finset.sum_eq_single e
          (fun e' _ he' => by rw [proj_mul_proj hw, if_neg fun hh => he' hh.symm])
          fun hmem => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hs⟩) hmem,
        proj_mul_proj hw, if_pos rfl]
    · rw [if_neg hs]
      refine Finset.sum_eq_zero fun e' he' => ?_
      refine (proj_mul_proj hw e e').trans (if_neg fun hh : e = e' => hs ?_)
      rw [hh]
      exact (Finset.mem_filter.mp he').2
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.filter_filter]
end MIPRE.QLD
