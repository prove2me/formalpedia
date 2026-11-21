-- Prove2me | solution 1 for MasulloGRH.sobolev_jet_haar_integrable_iff
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:04:43.338344+00:00
-- url     : https://prove2.me/submissions/d3d27425-f93c-4abc-8c53-1169d615024f

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.JacobianOneDim
set_option autoImplicit false
open MeasureTheory Set Filter Topology

private theorem tail_integrable_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
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


private theorem real_weight_nonneg (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
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

private theorem real_weight_all (m : ℕ) (s : ℝ) :
    Integrable (fun x : ℝ => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)) ↔
      (2 * (m : ℝ) + 1 < s) := by
  by_cases hs : 0 ≤ s
  · exact real_weight_nonneg m s hs
  have hsneg : s < 0 := lt_of_not_ge hs
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  constructor
  · intro h
    have hi : Integrable (fun x : ℝ => x ^ (2 * m)) := by
      apply h.mono' (by fun_prop)
      filter_upwards [] with x
      have hn : 0 ≤ x ^ (2 * m) := by rw [pow_mul]; positivity
      have hd : 0 < (1 + x ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
      have hden : (1 + x ^ 2) ^ (s / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact (le_div_iff₀ hd).mpr (mul_le_of_le_one_right hn hden)
    have hzero : Integrable (fun x : ℝ => x ^ (2 * m) / (1 + x ^ 2) ^ ((0 : ℝ) / 2)) := by
      simpa using hi
    have hbad := (real_weight_nonneg m 0 le_rfl).mp hzero
    linarith
  · intro h
    linarith

theorem solution (m : ℕ) (s : ℝ)  :
    IntegrableOn (fun t : ℝ => t⁻¹ *
      ((Real.log t) ^ (2 * m) / (1 + (Real.log t) ^ 2) ^ (s / 2))) (Ioi 0) ↔
      2 * (m : ℝ) + 1 < s := by
  let w : ℝ → ℝ := fun x => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)
  let g : ℝ → ℝ := fun t => t⁻¹ * w (Real.log t)
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g
  have hweight : (fun x => |Real.exp x| • g (Real.exp x)) = w := by
    funext x
    simp [g, Real.log_exp, abs_of_pos (Real.exp_pos x), smul_eq_mul]
  rw [Set.image_univ, Real.range_exp, hweight, integrableOn_univ] at hchange
  exact hchange.trans (real_weight_all m s)
