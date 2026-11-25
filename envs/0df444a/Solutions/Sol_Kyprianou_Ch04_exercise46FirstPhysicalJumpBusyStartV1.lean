-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstPhysicalJumpBusyStartV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:13:18.889639+00:00
-- url     : https://prove2.me/submissions/7b5abd97-e4e8-42eb-a262-ad518747592e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (hDrift : L.drift = 1)
    (w : Omega) (t : NNReal) (ht : 0 < t)
    (hJump : L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t)
    (hPrefix : ∀ s : NNReal, s < t → L.X s w = (s : Real))
    (hBound : ∀ s : NNReal, L.X s w ≤ (s : Real))
    (Wleft : Real)
    (hLeft : Tendsto
      (fun s : NNReal => sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w)
      (nhdsWithin t (Iio t)) (nhds Wleft)) :
    Wleft = 0 ∧ 0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w := by

  haveI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hzero : ∀ s : NNReal, s < t →
      sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w = 0 := by
    intro s hs
    have heq : sSup ((fun u : NNReal => L.X u w) '' Iic s) = L.X s w := by
      apply le_antisymm
      · have hne : (((fun u : NNReal => L.X u w) '' Iic s) : Set Real).Nonempty :=
          ⟨L.X s w, s, mem_Iic.mpr le_rfl, rfl⟩
        apply csSup_le hne
        rintro x ⟨u, hu, rfl⟩
        change L.X u w ≤ L.X s w
        rw [hPrefix u (lt_of_le_of_lt hu hs), hPrefix s hs]
        exact_mod_cast hu
      · apply le_csSup
        · use (s : Real)
          rintro x ⟨u, hu, rfl⟩
          exact (hBound u).trans (by exact_mod_cast hu)
        · exact ⟨s, mem_Iic.mpr le_rfl, rfl⟩
    rw [heq, sub_self]
  have hevent : (fun s : NNReal =>
      sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w) =ᶠ[nhdsWithin t (Iio t)]
      (fun _ => (0 : Real)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hzero s hs
  have hz : Wleft = 0 := tendsto_nhds_unique hLeft
    (tendsto_const_nhds.congr' hevent.symm)
  have hlim := (avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 t
  have hgt : ∀ᶠ s in nhdsWithin t (Iio t), L.X t w < L.X s w :=
    hlim.eventually (Ioi_mem_nhds hJump)
  obtain ⟨s, hs, hslt⟩ := (hgt.and self_mem_nhdsWithin).exists
  have hb : BddAbove ((fun u : NNReal => L.X u w) '' Iic t) := by
    use (t : Real)
    rintro x ⟨u, hu, rfl⟩
    exact (hBound u).trans (by exact_mod_cast hu)
  refine ⟨hz, sub_pos.mpr (hs.trans_le (le_csSup hb ?_))⟩
  exact ⟨s, hslt.le, rfl⟩
