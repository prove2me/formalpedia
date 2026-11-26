-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstArrivalLinearPrefixV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:43:47.466054+00:00
-- url     : https://prove2.me/submissions/120f131b-88bd-4a3c-bcb8-41e4149e87c4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_BV_finite_activity_jump_sum_exact
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (a : Omega → NNReal)
    (hBefore : ∀ᵐ w ∂P, ∀ u : NNReal, 0 < u → u < a w →
      L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u) :
    ∀ᵐ w ∂P, (∀ s : NNReal, s < a w → L.X s w = (s : Real)) ∧
      (∀ s : NNReal, L.X s w ≤ (s : Real)) := by
  have hAll := ae_all_iff.mpr (fun n : Nat =>
    avram_bva20_original_BV_finite_activity_jump_sum_exact L hBV hFinite
      ((n+1 : Nat) : NNReal) (by positivity))
  filter_upwards [hAll, bv_drift_deficit_ae_monotone_all_times L hBV, hBefore]
    with w hpath hm hb
  constructor
  · intro s hs
    obtain ⟨n, hn⟩ := exists_nat_gt s
    have he := hpath n s (hn.le.trans (by exact_mod_cast Nat.le_succ n))
    have hz (u : NNReal) : (if 0 < u ∧ u ≤ s then
        Function.leftLim (fun z : NNReal => L.X z w) u - L.X u w else 0) = 0 := by
      split
      · rename_i hu
        rw [hb u hu.1 (hu.2.trans_lt hs), sub_self]
      · rfl
    simp_rw [hz, tsum_zero, hDrift, mul_one, sub_eq_zero] at he
    exact he.symm
  · intro s
    have h := hm (show (0 : NNReal) ≤ s from zero_le)
    simpa [hDrift, L.X_zero, sub_nonneg] using h
