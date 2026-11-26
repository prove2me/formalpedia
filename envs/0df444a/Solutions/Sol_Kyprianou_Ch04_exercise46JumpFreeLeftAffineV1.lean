-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46JumpFreeLeftAffineV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:16:58.896033+00:00
-- url     : https://prove2.me/submissions/3dd5f41c-98d5-45d1-b5d1-64a1c4b4240f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46FiniteSetLeftGapV1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤) :
    ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      ∃ s : NNReal, s < t ∧ ∀ u : NNReal, s < u → u ≤ t →
        Function.leftLim (fun v : NNReal => L.X v w) u =
          L.X s w + ((u : Real) - (s : Real)) := by
  have hAll := ae_all_iff.mpr (fun n : Nat =>
    avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only L hBV hFinite
      ((n+1 : Nat) : NNReal) (by positivity))
  filter_upwards [hAll,
    avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae L hBV hFinite]
    with w hpath hloc
  intro t ht
  obtain ⟨s,hst,hgap⟩ := Kyprianou.Ch04.exercise46FiniteSetLeftGapV1 _ (hloc t) t ht
  refine ⟨s,hst,?_⟩
  intro u hsu hut
  letI : (nhdsWithin u (Iio u)).NeBot := nhdsLT_neBot_of_exists_lt ⟨s,hsu⟩
  have hlocal : (fun v : NNReal => L.X v w) =ᶠ[nhdsWithin u (Iio u)]
      (fun v => L.X s w + ((v : Real) - (s : Real))) := by
    filter_upwards [Ioo_mem_nhdsLT hsu] with v hv
    obtain ⟨n,hn⟩ := exists_nat_gt t
    have hd := hpath n s v hv.1.le
      ((hv.2.le.trans hut).trans (hn.le.trans (by exact_mod_cast Nat.le_succ n))) (by
        intro z hz
        by_contra hne
        exact hgap z ⟨hz.2.trans (hv.2.le.trans hut),
          zero_le.trans_lt hz.1,hne⟩ hz.1 (hz.2.trans_lt (hv.2.trans_le hut)))
    rw [hDrift, mul_one, mul_one] at hd
    linarith
  have hc : Continuous (fun v : NNReal => L.X s w + ((v : Real) - (s : Real))) :=
    continuous_const.add (NNReal.continuous_coe.sub continuous_const)
  have hlim := (avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 u
  exact tendsto_nhds_unique hlim
    ((hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hlocal.symm)
