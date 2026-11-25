-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46StrictPassagePathKernelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:48:37.75311+00:00
-- url     : https://prove2.me/submissions/78cac04c-90e1-416e-9bfc-41a3206a0e72

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_eq_correctedUpTime
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Joint Borel strict passage kernel on the coordinate path space. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) :
    ∃ K : Real × (NNReal → Real) → WithTop NNReal, Measurable K ∧
      ∀ x : Real, 0 < x → ∀ w : Omega,
        K (x, fun t => L.X t w) = Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w := by
  classical
  let tau : Nat → NNReal := fun j =>
    ((Nat.unpair j).2 : NNReal) * (((((Nat.unpair j).1 + 1) : Nat) : NNReal)⁻¹)
  let K : Real × (NNReal → Real) → ℝ≥0∞ := fun z =>
    ⨅ j : Nat, if z.1 < z.2 (tau j) then (tau j : ℝ≥0∞) else ⊤
  refine ⟨K, ?_, ?_⟩
  · apply Measurable.iInf
    intro j
    exact Measurable.ite
      (measurableSet_lt measurable_fst ((measurable_pi_apply (tau j)).comp measurable_snd))
      measurable_const measurable_const
  · intro x hx w
    rw [Kyprianou.Ch03.firstHittingIoi_eq_correctedUpTime P G L x hx w]
    have h := (chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
      L (fun _ => 0) w x 0).1
    unfold twoSidedExitUpTimeCorrected
    change K (x, fun t => L.X t w) = _
    let e : ℝ≥0∞ ≃o WithTop NNReal :=
      { toFun := fun z => z
        invFun := fun z => z
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := by intros; rfl }
    have h' := congrArg e h.symm
    simp only [iInf_subtype, zero_add, L.X_zero, sub_zero, sub_self, sub_zero] at h'
    exact h' 
