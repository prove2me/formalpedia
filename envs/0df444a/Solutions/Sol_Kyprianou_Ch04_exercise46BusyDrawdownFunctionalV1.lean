-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyDrawdownFunctionalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:45:17.39803+00:00
-- url     : https://prove2.me/submissions/1f9b27de-7cb5-4330-882a-78a69493e2fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_countable_drawdown_test_measurable_fresh_shifted
import Theorems.Thm_Kyprianou_Ch04_exercise46RawSupEqualsRunningSupV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) :
    ∃ D : NNReal → (NNReal → Real) → Real,
      Measurable (fun z : NNReal × (NNReal → Real) => D z.1 z.2) ∧
      (∀ w t, D t (fun u => L.X u w) =
        sSup ((fun u => L.X u w) '' Iic t) - L.X t w) ∧
      (∀ w s t, let Y : NNReal → Real := fun u => L.X (s+u) w - L.X s w
        D t Y = sSup (Y '' Iic t) - Y t) := by
  classical
  let samples : Nat → NNReal := fun j =>
    ((Nat.unpair j).2 : NNReal) * (((((Nat.unpair j).1 + 1) : Nat) : NNReal)⁻¹)
  let H : NNReal → (NNReal → Real) → ENNReal := fun t f =>
    Filter.limsup (fun n : Nat =>
      let r : NNReal := (Nat.ceil ((t : Real) * (2 : Real) ^ n) : NNReal) / (2 : NNReal) ^ n
      ENNReal.ofReal (Real.exp (-(1 : Real) * ((⨆ i : Nat,
        if samples i ≤ r then ENNReal.ofReal (f (samples i)) else 0).toReal - f r)))) atTop
  have h := avram_ws01e_b_actual_countable_drawdown_test_measurable_fresh_shifted L 1
  change Measurable (fun z : NNReal × (NNReal → Real) => H z.1 z.2) ∧ _ at h
  let D : NNReal → (NNReal → Real) → Real := fun t f => -Real.log (H t f).toReal
  have hlog (x : Real) : -Real.log (ENNReal.ofReal (Real.exp (-1 * x))).toReal = x := by
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
    ring
  refine ⟨D, (Real.measurable_log.comp (ENNReal.measurable_toReal.comp h.1)).neg, ?_, ?_⟩
  · intro w t
    change -Real.log (H t (fun u => L.X u w)).toReal = _
    rw [show H t (fun u => L.X u w) =
      ENNReal.ofReal (Real.exp (-1 * (runningSup L t w - L.X t w))) from h.2.1 w t,
      hlog, Kyprianou.Ch04.exercise46RawSupEqualsRunningSupV1 P G L w t]
  · intro w s t
    dsimp only
    change -Real.log (H t (fun u => L.X (s+u) w - L.X s w)).toReal = _
    have he := h.2.2 w s t
    change H t (fun u => L.X (s+u) w - L.X s w) = _ at he
    rw [he, hlog]
    have hi : Icc (0 : NNReal) t = Iic t := by ext u; simp
    rw [hi]
