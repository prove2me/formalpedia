-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_scale_positive_from_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:19:13.224994+00:00
-- url     : https://prove2.me/submissions/53ee2929-9ba7-41e7-b7d1-7491cf746b8a

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecialFunctions.Exp
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem exponent_above_normalized_root
    (ψ : ℝ → ℝ) (q : ℝ) (w : ℝ → ℝ) (hw : IsQScale ψ q w)
    (β : ℝ) (hβ : 0 ≤ β) (hr : Phi ψ q < β) : q < ψ β := by
  obtain ⟨hroot, _, hn, _, _, htr⟩ := hw
  have hpos : 0 ≤ (ψ β - q)⁻¹ := by
    rw [← (htr β hβ hr).2]
    exact integral_nonneg (fun x => mul_nonneg (Real.exp_pos _).le (hn x))
  refine lt_of_le_of_ne (sub_nonneg.mp (inv_nonneg.mp hpos)) ?_
  intro he
  exact hr.not_ge (hroot.2.2 β ⟨hβ, he.symm⟩)

private theorem upper_laplace_tail_of_zero
    (ψ : ℝ → ℝ) (q : ℝ) (w : ℝ → ℝ) (hw : IsQScale ψ q w)
    (a : ℝ) (ha : 0 < a) (hwa : w a = 0)
    (b β : ℝ) (hb : 0 ≤ b) (hr : Phi ψ q < b) (hβ : b ≤ β) :
    (ψ β - q)⁻¹ ≤ Real.exp (-(β - b) * a) * (ψ b - q)⁻¹ := by
  obtain ⟨_, _, hnon, _, hmono, htr⟩ := hw
  have hi := (htr b hb hr).1
  have hi' : Integrable (fun x : ℝ => Real.exp (-b * x) * w x) (volume.restrict (Ioi 0)) := hi
  rw [← (htr β (hb.trans hβ) (hr.trans_le hβ)).2, ← (htr b hb hr).2, ← integral_const_mul]
  apply integral_mono_ae (htr β (hb.trans hβ) (hr.trans_le hβ)).1 (hi'.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hx
  by_cases hxa : x ≤ a
  · have hzero : w x = 0 := le_antisymm
      ((hmono (mem_Ici.mpr hxpos.le) (mem_Ici.mpr ha.le) hxa).trans_eq hwa) (hnon x)
    simp [hzero]
  · have harg : -β * x ≤ -(β - b) * a + -b * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr (le_of_not_ge hxa))]
    rw [← mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) (hnon x)

private theorem quadratic_times_exp_neg_tendsto
    (a C : ℝ) (ha : 0 < a) :
    Tendsto (fun β : ℝ => C * β ^ 2 * Real.exp (-(β * a))) atTop (nhds 0) := by
  have harg : Tendsto (fun β : ℝ => a * β) atTop atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos ha).2 tendsto_id
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp harg
  have hscaled := ht.const_mul (C / a ^ 2)
  have hfun : (fun β : ℝ => (C / a ^ 2) * ((a * β) ^ 2 * Real.exp (-(a * β)))) =
      fun β : ℝ => C * β ^ 2 * Real.exp (-(β * a)) := by
    funext β
    rw [mul_comm a β]
    field_simp [ha.ne'] <;> ring
  simpa only [Function.comp_def, hfun, mul_zero] using hscaled

theorem solution
    (ψ : ℝ → ℝ) (q : ℝ) (w : ℝ → ℝ) (hw : IsQScale ψ q w)
    (K : ℝ) (hK : 0 ≤ K) (hgrowth : ∀ β : ℝ, 1 ≤ β → ψ β ≤ K * β ^ 2)
    (a : ℝ) (ha : 0 < a) :
    0 < w a := by
  by_contra! hn
  have hwa : w a = 0 := le_antisymm hn (hw.2.2.1 a)
  let b : ℝ := max 1 (Phi ψ q + 1)
  have hb : 1 ≤ b := le_max_left _ _
  have hr : Phi ψ q < b := (lt_add_of_pos_right _ zero_lt_one).trans_le (le_max_right _ _)
  let m : ℝ := (ψ b - q)⁻¹
  have hm : 0 < m := inv_pos.mpr (sub_pos.mpr
    (exponent_above_normalized_root ψ q w hw b (zero_le_one.trans hb) hr))
  have hbound : ∀ᶠ β : ℝ in atTop, 1 ≤ (m * K * Real.exp (b * a)) * β ^ 2 * Real.exp (-(β * a)) := by
    filter_upwards [eventually_ge_atTop b] with β hβ
    have hg := hgrowth β (hb.trans hβ)
    have hδ := sub_pos.mpr (exponent_above_normalized_root ψ q w hw β
      (zero_le_one.trans (hb.trans hβ)) (hr.trans_le hβ))
    have ht := upper_laplace_tail_of_zero ψ q w hw a ha hwa b β (zero_le_one.trans hb) hr hβ
    have hprod := mul_le_mul_of_nonneg_right ht hδ.le
    rw [inv_mul_cancel₀ hδ.ne'] at hprod
    calc
      1 ≤ Real.exp (-(β - b) * a) * m * (ψ β - q) := hprod
      _ ≤ Real.exp (-(β - b) * a) * m * (K * β ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hw.1.1]) (mul_nonneg (Real.exp_pos _).le hm.le)
      _ = _ := by
        rw [show -(β - b) * a = b * a + -(β * a) by ring, Real.exp_add]
        ring
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1))
    (ge_of_tendsto (quadratic_times_exp_neg_tendsto a (m * K * Real.exp (b * a)) ha) hbound)
