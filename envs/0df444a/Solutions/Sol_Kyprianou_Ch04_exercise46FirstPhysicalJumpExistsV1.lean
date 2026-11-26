-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstPhysicalJumpExistsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:47:26.94487+00:00
-- url     : https://prove2.me/submissions/02c0b5ba-ba37-48d6-96b9-dde8facf9832

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_source_jumps_interval_probability
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (hBV : L.BoundedVariation)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (hRate : 0 < (L.ν (Iio (0 : Real))).toReal) :
    ∀ᵐ w ∂P, ∃ t : NNReal, 0 < t ∧
      L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t ∧
      ∀ u : NNReal, 0 < u → u < t →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u := by

  letI : IsProbabilityMeasure P := L.isProbability
  have hSome : ∀ᵐ w ∂P, ∃ u : NNReal, 0 < u ∧
      L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0 := by
    rw [ae_iff, ← measureReal_eq_zero_iff]
    apply le_antisymm _ measureReal_nonneg
    have hle (n : Nat) :
        P.real {w | ¬ ∃ u : NNReal, 0 < u ∧
          L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0} ≤
        Real.exp (-((n : Real) * (L.ν (Iio (0 : Real))).toReal)) := by
      have he := avram_wave4_04a_bv_actual_no_source_jumps_interval_probability
        L hBV hFinite 0 (n : NNReal) zero_le
      rw [tsub_zero, NNReal.coe_natCast] at he
      rw [← he]
      refine measureReal_mono ?_ (measure_ne_top P _)
      intro w hw u hu
      by_contra hne
      exact hw ⟨u, hu.1, hne⟩
    have hlim : Tendsto
        (fun n : Nat => Real.exp (-((n : Real) * (L.ν (Iio (0 : Real))).toReal)))
        atTop (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      simpa only [← mul_neg] using
        (tendsto_mul_const_atBot_of_neg (neg_neg_of_pos hRate)).2
          (tendsto_natCast_atTop_atTop (R := Real))
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hle)
  filter_upwards [hSome,
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
      L hFinite.ne] with w hw hf
  obtain ⟨u, hu, hne⟩ := hw
  let S : Set NNReal := {v | 0 < v ∧ v ≤ u ∧
    L.X v w - Function.leftLim (fun z : NNReal => L.X z w) v ≠ 0}
  obtain ⟨t, ht, hmin⟩ := Set.exists_min_image S id (hf u)
    ⟨u, hu, le_rfl, hne⟩
  have hle := L.noPosJumps w t _ ht.1 ((avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 t)
  refine ⟨t, ht.1, lt_of_le_of_ne hle (sub_ne_zero.mp ht.2.2), ?_⟩
  intro v hv hvt
  by_contra h
  have hvS : v ∈ S := ⟨hv, hvt.le.trans ht.2.1, sub_ne_zero.mpr h⟩
  exact (not_le_of_gt hvt) (hmin v hvS)
