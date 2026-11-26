-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyStartsNonemptyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:48:50.033657+00:00
-- url     : https://prove2.me/submissions/c6c78aae-06de-4f89-a2d3-855a4ffb25c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstPhysicalJumpExistsV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstPhysicalJumpBusyStartV1
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_BV_finite_activity_jump_sum_exact
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (hRate : 0 < (L.ν (Iio (0 : Real))).toReal)
    (Wleft : NNReal → Omega → Real)
    (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto
        (fun s : NNReal => sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w))) :
    let B : Omega → Set NNReal := fun w =>
      {t | 0 < t ∧ Wleft t w = 0 ∧
        0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}
    ∀ᵐ w ∂P, (B w).Nonempty := by
  dsimp only
  have hAll := ae_all_iff.mpr (fun n : Nat =>
    avram_bva20_original_BV_finite_activity_jump_sum_exact L hBV hFinite
      ((n+1 : Nat) : NNReal) (by positivity))
  filter_upwards [hAll, bv_drift_deficit_ae_monotone_all_times L hBV, hWLeft,
    Kyprianou.Ch04.exercise46FirstPhysicalJumpExistsV1 P G L hBV hFinite hRate]
    with w hpath hm hw hj
  obtain ⟨t, ht, hJump, hBefore⟩ := hj
  have hBound (s : NNReal) : L.X s w ≤ (s : Real) := by
    have h := hm (show (0 : NNReal) ≤ s from zero_le)
    simpa [hDrift, L.X_zero, sub_nonneg] using h
  have hPrefix (s : NNReal) (hs : s < t) : L.X s w = (s : Real) := by
    obtain ⟨n, hn⟩ := exists_nat_gt s
    have he := hpath n s (hn.le.trans (by exact_mod_cast Nat.le_succ n))
    have hz (u : NNReal) : (if 0 < u ∧ u ≤ s then
        Function.leftLim (fun z : NNReal => L.X z w) u - L.X u w else 0) = 0 := by
      split
      · rename_i hu
        rw [hBefore u hu.1 (hu.2.trans_lt hs), sub_self]
      · rfl
    simp_rw [hz, tsum_zero, hDrift, mul_one, sub_eq_zero] at he
    exact he.symm
  have h := Kyprianou.Ch04.exercise46FirstPhysicalJumpBusyStartV1
    P G L hDrift w t ht hJump hPrefix hBound (Wleft t w) (hw t ht)
  exact ⟨t, ht, h.1, h.2⟩
