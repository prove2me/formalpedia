-- Prove2me | solution 1 for MIPRE.sum_bornProb_le_map
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:45:41.811468+00:00
-- url     : https://prove2.me/submissions/81d5ae00-bc8e-47d8-9746-e4070af9783b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Expanded.lean (solution of MIPRE.sum_bornProb_le_map);
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
import Definitions.Def_MIPRE_Foundations_Expanded
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_kronecker_sum_right
import Theorems.Thm_MIPRE_sum_kronecker_left

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem sum_quadForm {N ι : Type*} [Fintype N] (ψ : N → ℂ) (s : Finset ι)
    (f : ι → Matrix N N ℂ) :
    star ψ ⬝ᵥ ((∑ i ∈ s, f i) *ᵥ ψ) = ∑ i ∈ s, star ψ ⬝ᵥ ((f i) *ᵥ ψ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
theorem bornProb_sum_sum {ι : Type*} (ψ : dA × dB → ℂ) (s t : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) (∑ j ∈ t, B j)
      = ∑ i ∈ s, ∑ j ∈ t, bornProb ψ (A i) (B j) := by
  classical
  simp only [bornProb]
  rw [sum_kronecker_left, sum_quadForm ψ _ _, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kronecker_sum_right, sum_quadForm ψ _ _, Complex.re_sum]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ψ : dA × dB → ℂ) (P : POVM ι dA) (Q : POVM ι dB) (f : ι → κ) :
    ∑ i, bornProb ψ ((P.mats i).val) ((Q.mats i).val)
      ≤ ∑ k, bornProb ψ (((P.map f).mats k).val) (((Q.map f).mats k).val) := by
  classical
  have hfib : ∀ k : κ, bornProb ψ (((P.map f).mats k).val) (((Q.map f).mats k).val)
      = ∑ i ∈ univ.filter fun i => f i = k, ∑ j ∈ univ.filter fun j => f j = k,
          bornProb ψ ((P.mats i).val) ((Q.mats j).val) := by
    intro k
    rw [show (((P.map f).mats k).val)
        = ∑ i ∈ univ.filter fun i => f i = k, ((P.mats i).val) from
      AddSubmonoidClass.coe_finsetSum _ _,
      show (((Q.map f).mats k).val)
        = ∑ j ∈ univ.filter fun j => f j = k, ((Q.mats j).val) from
      AddSubmonoidClass.coe_finsetSum _ _, bornProb_sum_sum]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hfib k]
  have hdiag : ∀ k : κ, ∑ i ∈ univ.filter fun i => f i = k,
        bornProb ψ ((P.mats i).val) ((Q.mats i).val)
      ≤ ∑ i ∈ univ.filter fun i => f i = k, ∑ j ∈ univ.filter fun j => f j = k,
          bornProb ψ ((P.mats i).val) ((Q.mats j).val) := by
    intro k
    refine Finset.sum_le_sum fun i hi => ?_
    exact Finset.single_le_sum
      (fun j _ => bornProb_nonneg ψ (P.posSemidef i) (Q.posSemidef j)) hi
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun k (_ : k ∈ univ) => hdiag k)
  exact (Finset.sum_fiberwise (univ : Finset ι) f
    (fun i => bornProb ψ ((P.mats i).val) ((Q.mats i).val))).symm
end MIPRE
