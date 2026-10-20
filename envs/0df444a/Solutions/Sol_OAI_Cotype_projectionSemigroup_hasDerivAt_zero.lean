-- Prove2me | solution 1 for OAI.Cotype.projectionSemigroup_hasDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:48:34.345007+00:00
-- url     : https://prove2.me/submissions/a68b9775-06b6-4c4a-831b-51fd2b51c28f

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum

open OAI OAI.Cotype
open scoped BigOperators
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
theorem h50c_deriv {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] : ∀ (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
    (∀ i j, Commute (P i) (P j)) →
    HasDerivAt (projectionSemigroup P) (projectionLinearCoefficient P) 0 := by
  intro m
  induction m with
  | zero =>
    intro P _
    have : projectionSemigroup P = fun _ => 1 := by funext r; rfl
    rw [this]
    have h0 : projectionLinearCoefficient P = 0 := by simp [projectionLinearCoefficient]
    rw [h0]; exact hasDerivAt_const _ _
  | succ m ih =>
    intro P hc
    have hfun : projectionSemigroup P =
        (fun r : ℝ => P 0 + r • (1 - P 0)) * projectionSemigroup (fun i => P i.succ) := by
      funext r; rfl
    have hA : HasDerivAt (fun r : ℝ => P 0 + r • (1 - P 0)) (1 - P 0) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).smul_const (1 - P 0)).const_add (P 0)
      simpa using this
    have ht := ih (fun i => P i.succ) (fun i j => hc i.succ j.succ)
    rw [hfun]
    refine (hA.mul ht).congr_deriv ?_
    symm
    simp only [zero_smul, add_zero]
    rw [projectionSemigroup_zero]
    have e0 : (1 - P 0) * projectionSubset P (fun j => decide (j ≠ 0)) =
        (1 - P 0) * projectionProduct (fun i => P i.succ) := by
      simp [projectionSubset, projectionProduct]
    have e1 : ∀ k : Fin m, (1 - P k.succ) * projectionSubset P (fun j => decide (j ≠ k.succ)) =
        P 0 * ((1 - P k.succ) * projectionSubset (fun i => P i.succ) (fun j => decide (j ≠ k))) := by
      intro k
      have hcomm : Commute (P 0) (1 - P k.succ) := (Commute.one_right _).sub_right (hc 0 k.succ)
      rw [← mul_assoc, hcomm.eq, mul_assoc]
      congr 1
      simp [projectionSubset, projectionProduct, (Fin.succ_ne_zero k).symm]
    rw [projectionLinearCoefficient, Fin.sum_univ_succ, e0]
    simp only [e1, projectionLinearCoefficient, Finset.mul_sum]

theorem solution {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (P j)) :
    HasDerivAt (projectionSemigroup P) (projectionLinearCoefficient P) 0 := by
  exact h50c_deriv m P hc

