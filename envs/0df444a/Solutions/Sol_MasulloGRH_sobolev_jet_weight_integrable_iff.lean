-- Prove2me | solution 1 for MasulloGRH.sobolev_jet_weight_integrable_iff
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:26:01.900821+00:00
-- url     : https://prove2.me/submissions/6f7cabfb-1502-42c2-b076-9081035c7125

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic
set_option autoImplicit false
open MeasureTheory Set Filter Topology

private theorem tail_integrable_iff (m : ℕ) (s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun x : ℝ => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)) (Ioi 1) ↔
      (2 * (m : ℝ) + 1 < s) := by
  let w : ℝ → ℝ := fun x => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)
  let g : ℝ → ℝ := fun x => x ^ (2 * (m : ℝ) - s)
  let C : ℝ := (2 : ℝ) ^ (s / 2)
  have hC : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  have hwcont : Continuous w := by
    apply Continuous.div (by fun_prop) (by fun_prop (disch := linarith))
    intro x
    exact ne_of_gt (Real.rpow_pos_of_pos (by positivity : 0 < 1 + x ^ 2) _)
  have hwmeas : AEStronglyMeasurable w (volume.restrict (Ioi 1)) := hwcont.aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi 1)) := by
    dsimp [g]
    fun_prop
  have hcomp (x : ℝ) (hx : 1 < x) : 0 ≤ w x ∧ 0 ≤ g x ∧ w x ≤ g x ∧ g x ≤ C * w x := by
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
    have hbase : 0 < 1 + x ^ 2 := by positivity
    have hs0 : 0 ≤ s / 2 := by linarith
    have hb : 0 < x ^ s := Real.rpow_pos_of_pos hx0 _
    have hd : 0 < (1 + x ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos hbase _
    have hn : 0 ≤ x ^ (2 * m) := pow_nonneg hx0.le _
    have hpow : (x ^ 2) ^ (s / 2) = x ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    have hl : x ^ s ≤ (1 + x ^ 2) ^ (s / 2) := by
      rw [← hpow]
      exact Real.rpow_le_rpow hx2.le (by linarith) hs0
    have hu : (1 + x ^ 2) ^ (s / 2) ≤ C * x ^ s := by
      calc (1 + x ^ 2) ^ (s / 2) ≤ (2 * x ^ 2) ^ (s / 2) :=
          Real.rpow_le_rpow hbase.le (by nlinarith) hs0
        _ = C * x ^ s := by rw [Real.mul_rpow (by norm_num) hx2.le, hpow]
    have hg : g x = x ^ (2 * m) / x ^ s := by
      dsimp [g]
      rw [Real.rpow_sub hx0]
      congr 1
      norm_cast
    rw [hg]
    refine ⟨div_nonneg hn hd.le, div_nonneg hn hb.le, ?_, ?_⟩
    · exact div_le_div_of_nonneg_left hn hb hl
    · calc x ^ (2 * m) / x ^ s = w x * ((1 + x ^ 2) ^ (s / 2) / x ^ s) := by
            dsimp [w]
            field_simp
          _ ≤ w x * C := mul_le_mul_of_nonneg_left ((div_le_iff₀ hb).mpr hu) (div_nonneg hn hd.le)
          _ = C * w x := mul_comm _ _
  have hiff : IntegrableOn w (Ioi 1) ↔ IntegrableOn g (Ioi 1) := by
    constructor
    · intro h
      apply (h.const_mul C).mono' hgmeas
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hcomp x hx).2.1]
      exact (hcomp x hx).2.2.2
    · intro h
      apply h.mono' hwmeas
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hcomp x hx).1]
      exact (hcomp x hx).2.2.1
  change IntegrableOn w (Ioi 1) ↔ _
  rw [hiff]
  change IntegrableOn (fun x : ℝ => x ^ (2 * (m : ℝ) - s)) (Ioi 1) ↔ _
  rw [integrableOn_Ioi_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith


theorem solution (m : ℕ) (s : ℝ) (hs : 1 < s) :
    Integrable (fun x : ℝ => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)) ↔
      (2 * (m : ℝ) + 1 < s) := by
  let w : ℝ → ℝ := fun x => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)
  constructor
  · intro h
    exact (tail_integrable_iff m s hs).mp h.integrableOn
  · intro h
    have hpos : IntegrableOn w (Ioi 1) := (tail_integrable_iff m s hs).mpr h
    have hwcont : Continuous w := by
      apply Continuous.div (by fun_prop) (by fun_prop (disch := linarith))
      intro x
      exact ne_of_gt (Real.rpow_pos_of_pos (by positivity : 0 < 1 + x ^ 2) _)
    have hmid : IntegrableOn w (Icc (-1) 1) := hwcont.continuousOn.integrableOn_compact isCompact_Icc
    have hneg : IntegrableOn w (Iio (-1)) := by
      have hh := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hpos
      simpa [Function.comp_def, w, neg_pow, pow_mul] using hh
    have hu : Iio (-1 : ℝ) ∪ Icc (-1) 1 ∪ Ioi 1 = univ := by
      ext x
      simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
      rcases lt_or_ge x (-1) with hx | hx
      · exact Or.inl (Or.inl hx)
      · rcases le_or_gt x 1 with hx' | hx'
        · exact Or.inl (Or.inr ⟨hx, hx'⟩)
        · exact Or.inr hx'
    have hh := (hneg.union hmid).union hpos
    rw [hu, integrableOn_univ] at hh
    exact hh

example : ¬ Integrable (fun x : ℝ => x ^ 2 / (1 + x ^ 2) ^ ((3 : ℝ) / 2)) := by
  have h := solution 1 3 (by norm_num)
  norm_num at h
  exact h
