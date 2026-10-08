-- Prove2me | solution 1 for LostSalesOldNew.LeadTime.q_recursion
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:21:28.422008+00:00
-- url     : https://prove2.me/submissions/38b2a280-5685-4d74-86d5-6f430ac52208

import Mathlib
import Definitions.Def_LostSalesOldNew_LeadTime_Model

open MeasureTheory
open LostSalesOldNew.LeadTime LostSalesOldNew.StateReduction

private lemma int_after {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (l : ℕ) (x : Ω → Fin (l+1) → ℝ) (ds : Ω → Fin l → ℝ)
    (hx : ∀ i, Integrable (fun ω => x ω i) μ)
    (hd : ∀ i, Integrable (fun ω => ds ω i) μ) :
    Integrable (fun ω => yAfter l (x ω) (ds ω)) μ := by
  induction l with
  | zero => exact hx 0
  | succ l ih =>
    apply ih (fun ω => shift (x ω) (ds ω 0)) (fun ω => Fin.tail (ds ω))
    · intro i
      by_cases hi : (i : ℕ) = 0
      · simp only [shift, hi, if_true]
        exact (((hx 0).sub (hd 0)).sup (integrable_const 0)).add (hx i.succ)
      · simpa [shift, hi] using hx i.succ
    · intro i
      exact hd i.succ

private lemma int_q0 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hmean : Integrable (fun d : ℝ => d) D) (y : Ω → ℝ) (hy : Integrable y μ) :
    Integrable (fun ω => q0 K D (y ω)) μ := by
  have hpos := ((hy.comp_fst D).sub (hmean.comp_snd μ)).sup (integrable_const 0)
  have hneg := ((hmean.comp_snd μ).sub (hy.comp_fst D)).sup (integrable_const 0)
  exact ((hy.const_mul K.c).add (hpos.integral_prod_left.const_mul K.h)).add
    (hneg.integral_prod_left.const_mul K.p)

private lemma int_cost (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hmean : Integrable (fun d : ℝ => d) D) (l : ℕ) (x : Fin (l+1) → ℝ) :
    Integrable (fun ds => q0 K D (yAfter l x ds)) (Measure.pi fun _ : Fin l => D) := by
  apply int_q0 _ K D hmean _
  apply int_after _ l (fun _ => x) id
  · intro i
    exact integrable_const _
  · intro i
    exact (measurePreserving_eval (fun _ : Fin l => D) i).integrable_comp_of_integrable hmean

theorem solution (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : LostSalesOldNew.StateReduction.IsDemand D) (hmean : Integrable (fun d : ℝ => d) D)
    (l : ℕ) (x : Fin (l + 2) → ℝ) :
    qL K D (l + 1) x = K.γ * ∫ d, qL K D l (LostSalesOldNew.StateReduction.shift x d) ∂D := by
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (l+1) => D) 0).symm
  have hi := he.integrable_comp_of_integrable (int_cost K D hmean (l+1) x)
  simp only [Function.comp_def] at hi
  unfold qL
  rw [← he.integral_comp']
  rw [integral_prod _ hi]
  simp only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero, yAfter, Fin.cons_zero, Fin.tail_cons, cast_eq]
  rw [pow_succ, integral_const_mul]
  ring

#print axioms solution
