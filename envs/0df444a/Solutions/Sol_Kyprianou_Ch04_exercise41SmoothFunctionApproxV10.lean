-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SmoothFunctionApproxV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:48:17.910575+00:00
-- url     : https://prove2.me/submissions/7db3807c-fca4-4834-943a-72abf601cf63

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41RampSequenceV11
import Theorems.Thm_Kyprianou_Ch04_exercise41SmoothJoinDerivV11
import Theorems.Thm_Kyprianou_Ch04_exercise41SmoothJoinValueV11
import Theorems.Thm_Kyprianou_Ch04_exercise41SmoothJoinDerivLimitV11
import Theorems.Thm_Kyprianou_Ch04_exercise41SmoothJoinBoundV11
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (fLeft fRight : ℝ → ℝ)
    (hC1Left : ContDiff ℝ 1 fLeft) (hC1Right : ContDiff ℝ 1 fRight) :
    let G := fun x : ℝ => if x < 0 then fLeft x - fLeft 0
        else if 0 < x then fRight x - fRight 0 else 0
    let D := fun x : ℝ => if x < 0 then deriv fLeft x
        else if 0 < x then deriv fRight x else 0
    ∃ g : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (g n)) ∧
      (∀ x, Tendsto (fun n => g n x) atTop (𝓝 (G x))) ∧
      (∀ x, Tendsto (fun n => deriv (g n) x) atTop (𝓝 (D x))) ∧
      (∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        ∀ n x, |x| ≤ R → ‖deriv (g n) x‖ ≤ K) := by
  obtain ⟨p,hp,hP,hlim,hD,hDl⟩ := exercise41RampSequenceV11
  let g : ℕ → ℝ → ℝ := fun n x => fLeft (-p n (-x)) - fLeft 0 +
    fRight (p n x) - fRight 0
  have hg (n : ℕ) := exercise41SmoothJoinDerivV11 fLeft fRight
    hC1Left hC1Right (p n) (hp n)
  have hd (n : ℕ) (x : ℝ) : deriv (g n) x =
      deriv fLeft (-p n (-x)) * deriv (p n) (-x) +
      deriv fRight (p n x) * deriv (p n) x := (hg n).2 x
  refine ⟨g,fun n => (hg n).1,?_,?_,?_⟩
  · exact exercise41SmoothJoinValueV11 fLeft fRight hC1Left hC1Right p hlim
  · intro x
    simp only [hd]
    exact exercise41SmoothJoinDerivLimitV11 fLeft fRight hC1Left hC1Right p hlim hDl x
  · intro R hR
    obtain ⟨K,hK,hbound⟩ := exercise41SmoothJoinBoundV11 fLeft fRight
      hC1Left hC1Right p hP hD R hR
    exact ⟨K,hK,fun n x hx => by rw [hd]; exact hbound n x hx⟩
