-- Prove2me | solution 1 for MIPRE.Introspection.composed_twirl_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:16.541453+00:00
-- url     : https://prove2.me/submissions/d63aacb5-193d-4c4a-9b30-fe97a9e791e8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ComposedTwirl.lean (solution of MIPRE.Introspection.composed_twirl_dist_le);
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
import Theorems.Thm_MIPRE_Introspection_two_sided_commutation_avg
import Theorems.Thm_MIPRE_Introspection_unitaryTwirl_comp
import Theorems.Thm_MIPRE_Introspection_unitaryTwirl_outcome_dist_le

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix
variable {dA dB I J A : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I] [Fintype J] [Fintype A]
theorem _root_.solution (μ : I → ℝ) (ν : J → ℝ)
    (hμ0 : ∀ i, 0 ≤ μ i) (hν0 : ∀ j, 0 ≤ ν j)
    (hμ1 : ∑ i, μ i = 1) (hν1 : ∑ j, ν j = 1)
    (ψ : dA × dB → ℂ) (M : POVM A dA)
    (U : I → Matrix dA dA ℂ) (V : J → Matrix dA dA ℂ) (W : J → Matrix dB dB ℂ)
    (hUsa : ∀ i, (U i)ᴴ = U i) (hUid : ∀ i, U i * U i = 1)
    (hVsa : ∀ j, (V j)ᴴ = V j) (hVid : ∀ j, V j * V j = 1)
    (hW : ∀ j, (W j)ᴴ * W j = 1) (hmirror : ∀ j, xSqNorm ψ (V j) (W j) = 0) :
    (∑ a, stateSqNorm ψ
      (unitaryTwirl ν V (unitaryTwirl μ U (M.mats a).val) - (M.mats a).val)) ≤
      4 * (∑ i, μ i * ∑ a, stateSqNorm ψ ((M.mats a).val * U i - U i * (M.mats a).val)) +
      4 * (∑ j, ν j * ∑ a, stateSqNorm ψ ((M.mats a).val * V j - V j * (M.mats a).val)) := by
  classical
  have hprob : (∑ p : I × J, μ p.1 * ν p.2) = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hν1, mul_one]
    exact hμ1
  have hprod (p : I × J) : (V p.2 * U p.1)ᴴ * (V p.2 * U p.1) = 1 := by
    rw [Matrix.conjTranspose_mul, hUsa, hVsa, mul_assoc,
      ← mul_assoc (V p.2), hVid, one_mul, hUid]
  have hJ := unitaryTwirl_outcome_dist_le (fun _ : Unit => (1 : ℝ)) (by simp)
    (fun _ (p : I × J) => μ p.1 * ν p.2) (fun _ p => mul_nonneg (hμ0 p.1) (hν0 p.2))
    (fun _ => hprob) (fun _ p => V p.2 * U p.1) (fun _ p => hprod p) ψ
    (fun _ a => (M.mats a).val)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul,
    Matrix.conjTranspose_mul, hUsa, hVsa] at hJ
  have hC := two_sided_commutation_avg (fun _ : Unit => (1 : ℝ)) (by simp)
    (fun _ => μ) (fun _ => ν) (fun _ => hμ0) (fun _ => hν0)
    (fun _ => hμ1) (fun _ => hν1) ψ (fun _ => M) (fun _ => U) (fun _ => V) (fun _ => W)
    (fun _ i => by rw [hUsa, hUid]) (fun _ => hW)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, hmirror, mul_zero,
    Finset.sum_const_zero, add_zero] at hC
  simp_rw [unitaryTwirl_comp]
  refine hJ.trans ?_
  simpa only [Fintype.sum_prod_type, mul_assoc, Finset.mul_sum] using hC
end MIPRE.Introspection
