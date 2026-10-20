-- Prove2me | solution 1 for OAI.Cotype.projectionSubset_union
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:41:17.919961+00:00
-- url     : https://prove2.me/submissions/72e53f17-a468-42bc-b708-f57bac34806a

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem t_union {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (ε η : Cube n) :
    projectionSubset P ε * projectionSubset P η =
      projectionSubset P (fun i => ε i || η i) := by
  induction n with
  | zero => simp [projectionSubset, projectionProduct]
  | succ n ih =>
    simp only [projectionSubset] at ih ⊢
    simp only [projectionProduct]
    have hcomm : Commute (projectionProduct (fun i : Fin n => if ε i.succ then P i.succ else 1))
        (if η 0 then P 0 else 1) := by
      apply projectionProduct_commute
      intro i
      split_ifs
      · exact hc _ _
      · exact Commute.one_right _
      · exact Commute.one_left _
      · exact Commute.one_left _
    have ih' := ih (fun i => P i.succ) (fun i => hp _) (fun i j => hc _ _)
      (fun i => ε i.succ) (fun i => η i.succ)
    rw [show ∀ a b c d : X →L[ℝ] X, a * b * (c * d) = a * (b * c) * d from fun a b c d => by
      simp only [mul_assoc], hcomm.eq]
    rw [show ∀ a b c d : X →L[ℝ] X, a * (c * b) * d = (a * c) * (b * d) from fun a b c d => by
      simp only [mul_assoc]]
    rw [ih']
    congr 1
    by_cases h1 : ε 0 = true <;> by_cases h2 : η 0 = true <;> simp [h1, h2, hp]

theorem solution {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (ε η : Cube n) :
    projectionSubset P ε * projectionSubset P η =
      projectionSubset P (fun i => ε i || η i) := by
  exact t_union P hp hc ε η

