-- Prove2me | solution 1 for Kyprianou.Ch04.strictSublevelStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:08:15.032548+00:00
-- url     : https://prove2.me/submissions/0ad91594-1002-42da-808f-275ba5fbecc1

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Right-continuity upgrades strict sublevel measurability to a stopping time. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hRC : F.IsRightContinuous) (tau : Omega → WithTop NNReal)
    (hlt : ∀ s : NNReal, MeasurableSet[F s] {w | tau w < (s : WithTop NNReal)}) :
    IsStoppingTime F tau := by
  intro t
  apply hRC.RC t
  rw [Filtration.rightCont_eq_of_neBot_nhdsGT]
  refine MeasurableSpace.measurableSet_iInf.mpr fun j => ?_
  refine MeasurableSpace.measurableSet_iInf.mpr fun htj => ?_
  obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt (tsub_pos_of_lt htj)
  have hbound (n : ℕ) :
      1 / (((n + n0 : ℕ) : NNReal) + 1) ≤ 1 / ((n0 : NNReal) + 1) := by
    gcongr
    exact_mod_cast Nat.le_add_left n0 n
  have he (w : Omega) : tau w ≤ (t : WithTop NNReal) ↔
      ∀ n : ℕ, tau w <
        ((t + 1 / (((n + n0 : ℕ) : NNReal) + 1) : NNReal) : WithTop NNReal) := by
    constructor
    · intro h n
      exact h.trans_lt (WithTop.coe_lt_coe.mpr (lt_add_of_pos_right _ (by positivity)))
    · intro h
      by_contra hn
      have hn' := lt_of_not_ge hn
      generalize hh : tau w = z at *
      induction z using WithTop.recTopCoe with
      | top => exact (not_lt_of_ge le_top) (h 0)
      | coe c =>
        obtain ⟨k,hk⟩ := exists_nat_one_div_lt (tsub_pos_of_lt (WithTop.coe_lt_coe.mp hn'))
        have hk' : 1 / (((k + n0 : ℕ) : NNReal) + 1) ≤ 1 / ((k : NNReal) + 1) := by
          gcongr
          exact_mod_cast Nat.le_add_right k n0
        exact (not_lt_of_ge ((lt_tsub_iff_left.mp (hk'.trans_lt hk)).le))
          (WithTop.coe_lt_coe.mp (h k))
  rw [show {w | tau w ≤ (t : WithTop NNReal)} =
    ⋂ n : ℕ, {w | tau w < ((t + 1 / (((n + n0 : ℕ) : NNReal) + 1) : NNReal) : WithTop NNReal)} from
      Set.ext fun w => by simpa only [Set.mem_setOf_eq, Set.mem_iInter] using he w]
  refine MeasurableSet.iInter fun n => ?_
  exact F.mono ((lt_tsub_iff_left.mp ((hbound n).trans_lt hn0)).le) _ (hlt _)
