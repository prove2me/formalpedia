-- Prove2me | solution 1 for Kyprianou.Ch05.killedMarkedEventAtClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:16:18.540616+00:00
-- url     : https://prove2.me/submissions/c3a4754b-0d82-4e8f-9950-f98e7598838d

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Omega : Type} (Y Yleft : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (x : ℝ) (hx : 0 < x) (w : Omega) (A B : Set ℝ) (hBp : B ⊆ Icc (0 : ℝ) x)
    (hz : Y 0 w = 0)
    (T : ENNReal)
    (hclock : (strictUpcrossing Y death x w : ENNReal) =
      if T < (death w : ENNReal) then T else ⊤)
    (hleft : ∀ t : NNReal, 0 < t → Yleft t w = Function.leftLim (fun s => Y s w) t) :
    (PassageFinite Y death x w ∧ 0 < passageOvershoot Y death x w ∧
      passageOvershoot Y death x w ∈ A ∧ passageUndershoot Y Yleft death x w ∈ B) ↔
      ((0 < T.toNNReal ∧ Y T.toNNReal w > x ∧
        Function.leftLim (fun s => Y s w) T.toNNReal ∈ Icc (0 : ℝ) x ∧
        Y T.toNNReal w - x ∈ A ∧
        x - Function.leftLim (fun s => Y s w) T.toNNReal ∈ B) ∧
        T < (death w : ENNReal)) := by
  classical
  by_cases hd : T < (death w : ENNReal)
  · have hf : T ≠ ⊤ := ne_of_lt (hd.trans_le le_top)
    have hk : (strictUpcrossing Y death x w : ENNReal) = T := by rwa [if_pos hd] at hclock
    have hfin : PassageFinite Y death x w := by
      unfold PassageFinite
      intro h
      exact hf (hk.symm.trans h)
    have ht : passageFiniteTime Y death x w = T.toNNReal :=
      congrArg ENNReal.toNNReal hk
    simp only [hfin,true_and,hd,and_true,passageOvershoot,passageUndershoot,ht]
    constructor
    · rintro ⟨ho,hA,hB⟩
      have hp : 0 < T.toNNReal := by
        by_contra! hn
        have he : T.toNNReal = 0 := le_antisymm hn bot_le
        rw [he,hz] at ho
        linarith
      rw [hleft _ hp] at hB
      have hb := hBp hB
      exact ⟨hp,by linarith,⟨by linarith [hb.2],by linarith [hb.1]⟩,hA,hB⟩
    · rintro ⟨hp,ho,_,hA,hB⟩
      rw [hleft _ hp]
      exact ⟨by linarith,hA,hB⟩
  · have hk : (strictUpcrossing Y death x w : ENNReal) = ⊤ := by rwa [if_neg hd] at hclock
    have hn : ¬ PassageFinite Y death x w := by
      intro h
      exact h hk
    simp [hn,hd]
