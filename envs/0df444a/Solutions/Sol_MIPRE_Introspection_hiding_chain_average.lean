-- Prove2me | solution 1 for MIPRE.Introspection.hiding_chain_average
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:38.358587+00:00
-- url     : https://prove2.me/submissions/ac77baec-0172-47b2-baf9-b55470f9f616

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingTests.lean (solution of MIPRE.Introspection.hiding_chain_average);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
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
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Theorems.Thm_MIPRE_sq_sum_le_card_mul_sum_sq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateVec_sum {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    stateVec ψ (∑ i ∈ s, f i) = ∑ i ∈ s, stateVec ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, stateVec_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateNorm ψ M :=
  norm_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dA] in
/-- Pushing a sum inside a deviation costs the number of terms. -/
theorem stateSqNorm_sum_le {κ : Type*} [Fintype κ] (ψ : dA × dB → ℂ) (f : κ → Matrix dA dA ℂ) :
    stateSqNorm ψ (∑ k, f k) ≤ (Fintype.card κ : ℝ) * ∑ k, stateSqNorm ψ (f k) := by
  have h1 : stateNorm ψ (∑ k, f k) ≤ ∑ k, stateNorm ψ (f k) := by
    rw [stateNorm, stateVec_sum]
    exact le_trans (norm_sum_le _ _) (le_of_eq rfl)
  calc stateSqNorm ψ (∑ k, f k) = stateNorm ψ (∑ k, f k) ^ 2 := rfl
    _ ≤ (∑ k, stateNorm ψ (f k)) ^ 2 := pow_le_pow_left₀ (stateNorm_nonneg ψ _) h1 2
    _ ≤ (Fintype.card κ : ℝ) * ∑ k, stateNorm ψ (f k) ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ fun k => stateNorm_nonneg ψ _
    _ = (Fintype.card κ : ℝ) * ∑ k, stateSqNorm ψ (f k) := rfl
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {X Y A B C J H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Telescoping the consecutive differences of a finite operator chain. -/
theorem operator_chain_telescope (P : ℕ → Matrix H H ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (P i - P (i + 1))) = P 0 - P n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; abel
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {X Y A B C J H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- A chain of `n` hiding levels costs `n` times the sum of its squared edge errors. -/
theorem stateSqNorm_hiding_chain (ψ : H × K → ℂ) (P : ℕ → Matrix H H ℂ) (n : ℕ) :
    stateSqNorm ψ (P 0 - P n) ≤
      (n : ℝ) * ∑ i ∈ Finset.range n, stateSqNorm ψ (P i - P (i + 1)) := by
  have h := stateSqNorm_sum_le ψ (fun i : Fin n => P i.val - P (i.val + 1))
  rw [Fin.sum_univ_eq_sum_range (fun i => P i - P (i + 1)) n,
    Fin.sum_univ_eq_sum_range (fun i => stateSqNorm ψ (P i - P (i + 1))) n,
    operator_chain_telescope, Fintype.card_fin] at h
  exact h
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {X Y A B C J H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
theorem _root_.solution (ψ : H × K → ℂ) (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (P : ℕ → J → C → Matrix H H ℂ) (n : ℕ) (δ : ℕ → ℝ)
    (hstep : ∀ i < n, (∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z)) ≤ δ i) :
    (∑ j, D j * ∑ z, stateSqNorm ψ (P 0 j z - P n j z)) ≤
      (n : ℝ) * ∑ i ∈ Finset.range n, δ i := by
  calc
    _ ≤ ∑ j, D j * ∑ z, (n : ℝ) * ∑ i ∈ Finset.range n,
        stateSqNorm ψ (P i j z - P (i + 1) j z) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hD j)
      exact Finset.sum_le_sum fun z _ => stateSqNorm_hiding_chain ψ (fun i => P i j z) n
    _ = (n : ℝ) * ∑ i ∈ Finset.range n,
        ∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z) := by
      simp_rw [← Finset.mul_sum, mul_left_comm (b := (n : ℝ))]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_comm (s := (univ : Finset C)) (t := Finset.range n), Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)) (Nat.cast_nonneg n)
end MIPRE.Introspection
