-- Prove2me | solution 1 for IncInfoDebt.FallenAngel.d24_integral
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:19:00.87618+00:00
-- url     : https://prove2.me/submissions/96d49840-7421-46ca-8f6a-d098d1d052be

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

open MeasureTheory ProbabilityTheory Set Real

local notation "μG" => gaussianReal 0 1

lemma N_eq (x : ℝ) : IncInfoDebt.FallenAngel.N x = (μG).real (Iic x) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_Iic (fun t _ => gaussianPDFReal_nonneg _ _ _))]
  show (1 / Real.sqrt (2 * Real.pi)) * ∫ z in Iic x, Real.exp (-z ^ 2 / 2) = _
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Iic (fun z _ => ?_)
  simp [gaussianPDFReal]

lemma sym (t : ℝ) : (μG).real (Iic (-t)) = (μG).real (Ici t) := by
  have h : (μG).map (fun x => -x) = μG := by rw [gaussianReal_map_neg, neg_zero]
  rw [← h, measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic, h]
  congr 2; ext x; simp

lemma second_moment_pos : ∫ x, (max x 0) ^ 2 ∂μG = 1 / 2 := by
  have hm2 : MemLp (fun x : ℝ => x) 2 μG := by
    exact memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)
  have hint2 : Integrable (fun x : ℝ => x ^ 2) μG := hm2.integrable_sq
  have hsq : ∫ x, x ^ 2 ∂μG = 1 := by
    have h := variance_of_integral_eq_zero (μ := μG) (X := id) measurable_id.aemeasurable
      integral_id_gaussianReal
    rw [variance_id_gaussianReal] at h
    simpa using h.symm
  have hpos_int : Integrable (fun x : ℝ => (max x 0) ^ 2) μG :=
    hint2.mono' (by fun_prop) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rcases le_total x 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg x]
      · rw [max_eq_left h]))
  have hneg_int : Integrable (fun x : ℝ => (max (-x) 0) ^ 2) μG :=
    hint2.mono' (by fun_prop) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rcases le_total (-x) 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg x]
      · rw [max_eq_left h, neg_sq]))
  have hsplit : (fun x : ℝ => x ^ 2) = fun x => (max x 0) ^ 2 + (max (-x) 0) ^ 2 := by
    funext x
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -x)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith : -x ≤ 0)]; ring
  have hsymm : ∫ x, (max (-x) 0) ^ 2 ∂μG = ∫ x, (max x 0) ^ 2 ∂μG := by
    have h : (μG).map (fun x => -x) = μG := by rw [gaussianReal_map_neg, neg_zero]
    conv_rhs => rw [← h]
    rw [integral_map (by fun_prop) (by fun_prop)]
  rw [hsplit, integral_add hpos_int hneg_int, hsymm] at hsq
  linarith

theorem solution :
    (∫ α in Set.Ioi (0 : ℝ), α * IncInfoDebt.FallenAngel.N (-α)) = (1 / 4 : ℝ) := by
  -- rewrite the integrand as a tail probability
  have hint_eq : ∀ α : ℝ, α * IncInfoDebt.FallenAngel.N (-α) = α * (μG).real (Ici α) := by
    intro α; rw [N_eq, sym]
  simp_rw [hint_eq]
  -- layer cake with g(t) = t and f = x⁺
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul (μG) (f := fun x : ℝ => max x 0)
    (g := fun t : ℝ => t) (ae_of_all _ (fun x => le_max_right x 0)) (by fun_prop)
    (fun t _ => (continuous_id).intervalIntegrable 0 t) (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => le_of_lt ht))
  have hleft : ∀ x : ℝ, (∫ t in (0 : ℝ)..max x 0, t) = (max x 0) ^ 2 / 2 := by
    intro x; rw [integral_id]; ring
  simp_rw [hleft] at hlc
  have hset : ∀ t ∈ Ioi (0 : ℝ), (μG) {a : ℝ | t ≤ max a 0} * ENNReal.ofReal t
      = ENNReal.ofReal (t * (μG).real (Ici t)) := by
    intro t ht
    have : {a : ℝ | t ≤ max a 0} = Ici t := by
      ext a; simp only [mem_setOf_eq, mem_Ici, le_max_iff]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (not_le.mpr ht)
      · exact Or.inl
    rw [this, ENNReal.ofReal_mul (le_of_lt ht), measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
      mul_comm]
  rw [setLIntegral_congr_fun measurableSet_Ioi hset] at hlc
  -- back to real integrals
  have hmeas : AEStronglyMeasurable (fun α : ℝ => α * (μG).real (Ici α)) (volume.restrict (Ioi 0)) := by
    have hanti : Antitone (fun α : ℝ => (μG).real (Ici α)) :=
      fun a b hab => measureReal_mono (Ici_subset_Ici.mpr hab)
    exact (measurable_id.mul hanti.measurable).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun α : ℝ => α * (μG).real (Ici α) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => mul_nonneg (le_of_lt ht) measureReal_nonneg)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, ← hlc]
  have hpos_int : Integrable (fun x : ℝ => (max x 0) ^ 2 / 2) μG := by
    have hm2 : MemLp (fun x : ℝ => x) 2 μG := by
      exact memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)
    refine (hm2.integrable_sq.div_const 2).mono' (by fun_prop) (ae_of_all _ (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases le_total x 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg x]
    · rw [max_eq_left h]
  rw [← ofReal_integral_eq_lintegral_ofReal hpos_int (ae_of_all _ (fun x => by positivity)),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => by positivity)), integral_div, second_moment_pos]
  norm_num
