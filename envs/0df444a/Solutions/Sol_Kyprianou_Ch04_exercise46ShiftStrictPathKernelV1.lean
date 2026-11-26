-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ShiftStrictPathKernelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:38:31.75307+00:00
-- url     : https://prove2.me/submissions/0b9f88c9-f9e7-4cbc-b777-1b7a4463ae35

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_eq_correctedUpTime
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) :
    ∃ K : Real × (NNReal → Real) → WithTop NNReal, Measurable K ∧
      (∀ x : Real, 0 < x → ∀ w,
        K (x,fun t => L.X t w) = Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w) ∧
      (∀ (w : Omega) (s : NNReal) (x : Real),
        K (x,fun u => L.X (s+u) w - L.X s w) =
          ⨅ u : NNReal, if x < L.X (s+u) w - L.X s w
            then (u : WithTop NNReal) else ⊤) := by
  classical
  let tau : Nat → NNReal := fun j =>
    ((Nat.unpair j).2 : NNReal) * (((((Nat.unpair j).1 + 1) : Nat) : NNReal)⁻¹)
  let K : Real × (NNReal → Real) → ENNReal := fun z =>
    ⨅ j : Nat, if z.1 < z.2 (tau j) then (tau j : ENNReal) else ⊤
  have hK : Measurable K := by
    apply Measurable.iInf
    intro j
    exact Measurable.ite
      (measurableSet_lt measurable_fst ((measurable_pi_apply (tau j)).comp measurable_snd))
      measurable_const measurable_const
  have hKshift (w : Omega) (s : NNReal) (x : Real) :
      K (x,fun u => L.X (s+u) w - L.X s w) =
        ⨅ u : NNReal, if x < L.X (s+u) w - L.X s w then
          (u : WithTop NNReal) else ⊤ := by
    have h := (chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
      L (fun _ => 0) w x s).1
    have he : K (x,fun u => L.X (s+u) w - L.X s w) =
        (⨅ u : NNReal, ⨅ (_ : x < L.X (s+u) w - L.X s w), (u : ENNReal)) := by
      simpa only [iInf_subtype,sub_zero] using h.symm
    change K (x,fun u => L.X (s+u) w - L.X s w) =
      (⨅ u : NNReal, if x < L.X (s+u) w - L.X s w then (u : ENNReal) else ⊤)
    rw [he]
    apply iInf_congr
    intro u
    by_cases hu : x < L.X (s+u) w - L.X s w
    · rw [iInf_pos hu,if_pos hu]
    · rw [iInf_neg hu,if_neg hu]
  have hKx (x : Real) (hx : 0 < x) (w : Omega) :
      K (x,fun t => L.X t w) = Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w := by
    rw [Kyprianou.Ch03.firstHittingIoi_eq_correctedUpTime P G L x hx w]
    unfold twoSidedExitUpTimeCorrected
    have h := (chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
      L (fun _ => 0) w x 0).1
    let e : ENNReal ≃o WithTop NNReal :=
      {toFun := fun z => z, invFun := fun z => z, left_inv := fun _ => rfl,
       right_inv := fun _ => rfl, map_rel_iff' := by intros; rfl}
    have h' := congrArg e h.symm
    simp only [iInf_subtype,zero_add,L.X_zero,sub_zero,sub_self,sub_zero] at h'
    exact h'
  exact ⟨K,hK,hKx,hKshift⟩
