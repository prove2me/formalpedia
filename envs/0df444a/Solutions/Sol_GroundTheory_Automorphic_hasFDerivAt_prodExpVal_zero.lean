-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFDerivAt_prodExpVal_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:45:55.740086+00:00
-- url     : https://prove2.me/submissions/6d4fde9e-151b-4f44-942c-f9fbca942540

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_prodExpVal_succ
import Theorems.Thm_P2M_GroundTheory_Automorphic_prodExpVal_zero__e9258f5d17f4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} (X : Fin d → 𝔸) :
    HasFDerivAt (prodExpVal X)
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i)) 0 := by
  induction d with
  | zero =>
    have e : prodExpVal X = fun _ => 1 := funext fun t => by simp [prodExpVal]
    rw [e]
    refine (hasFDerivAt_const (1 : 𝔸) (0 : Fin 0 → ℝ)).congr_fderiv ?_
    ext t; simp
  | succ d ih =>
    have e : prodExpVal X = fun t => exp (t 0 • X 0) *
        prodExpVal (fun i => X i.succ) (fun i => t i.succ) := funext (prodExpVal_succ X)
    rw [e]
    have hA : HasFDerivAt (fun t : Fin (d + 1) → ℝ => exp (t 0 • X 0))
        ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0 := by
      have hL : HasFDerivAt (fun t : Fin (d + 1) → ℝ => t 0 • X 0)
          ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0 :=
        ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)).hasFDerivAt
      have hE : HasFDerivAt (exp : 𝔸 → 𝔸) (1 : 𝔸 →L[ℝ] 𝔸) ((0 : Fin (d + 1) → ℝ) 0 • X 0) := by
        have : (0 : Fin (d + 1) → ℝ) 0 • X 0 = 0 := by simp
        rw [this]; exact hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
      exact (hE.comp (0 : Fin (d + 1) → ℝ) hL).congr_fderiv (by ext t; simp)
    let T : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
    have hB : HasFDerivAt (fun t : Fin (d + 1) → ℝ =>
        prodExpVal (fun i => X i.succ) (fun i => t i.succ))
        ((∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i.succ)).comp T)
        0 := by
      have h0 : T 0 = 0 := map_zero T
      have := (ih (fun i => X i.succ))
      rw [← h0] at this
      exact this.comp (0 : Fin (d + 1) → ℝ) (T.hasFDerivAt)
    refine (hA.mul' hB).congr_fderiv ?_
    ext t
    simp [T, Fin.sum_univ_succ, prodExpVal_zero']
    rw [add_comm]
end GroundTheory.Automorphic
