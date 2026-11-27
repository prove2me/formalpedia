-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:41.603892+00:00
-- url     : https://prove2.me/submissions/c466136e-80ca-48e3-be93-d2cfc28e9a9d

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution (α : Fin 2 → ℝ) (β : ℝ) (hβ : 0 < β) (lam : Fin 2 → ℝ)
    (hlam : ∀ j, 0 < lam j) (h12 : α 0 + 1 / lam 0 ≤ α 1 + 1 / lam 1) :
    (∃! p₂ : ℝ, 0 < lam 0 + β * lam 0 * lam 1 * p₂ ∧
        β * lam 1 * p₂ = 1 + lam 1 * (α 1 - α 0) -
          Real.log ((lam 0 + β * lam 0 * lam 1 * p₂) / (lam 0 + lam 1))) ∧
      ∀ p₂ : ℝ, 0 < lam 0 + β * lam 0 * lam 1 * p₂ →
        β * lam 1 * p₂ = 1 + lam 1 * (α 1 - α 0) -
          Real.log ((lam 0 + β * lam 0 * lam 1 * p₂) / (lam 0 + lam 1)) →
        -- the bounds on p̂₂
        (1 / (β * lam 0) ≤ p₂ ∧ p₂ ≤ 1 / (β * lam 1) + (α 1 - α 0) / β) ∧
        -- the unique Nash equilibrium
        IsPriceNE α β lam ![1 / (β * lam 1), p₂] ∧
        (∀ p, IsPriceNE α β lam p → p = ![1 / (β * lam 1), p₂]) ∧
        -- market shares and revenues
        choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 0 =
          lam 0 / (lam 0 + β * lam 0 * lam 1 * p₂) ∧
        firmRevenue α β lam ![1 / (β * lam 1), p₂] 0 =
          1 / (β * lam 1) * (lam 0 / (lam 0 + β * lam 0 * lam 1 * p₂)) ∧
        choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 1 =
          β * lam 0 * lam 1 * p₂ / (lam 0 + β * lam 0 * lam 1 * p₂) ∧
        firmRevenue α β lam ![1 / (β * lam 1), p₂] 1 =
          β * lam 0 * lam 1 * p₂ ^ 2 / (lam 0 + β * lam 0 * lam 1 * p₂) ∧
        -- the final comparisons
        util α β ![1 / (β * lam 1), p₂] 0 ≤ util α β ![1 / (β * lam 1), p₂] 1 ∧
        p₂ * choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 0 =
          1 / (β * lam 1) * choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 1 ∧
        (firmRevenue α β lam ![1 / (β * lam 1), p₂] 1 ≤
            firmRevenue α β lam ![1 / (β * lam 1), p₂] 0 ↔ p₂ ≤ 1 / (β * lam 1)) ∧
        (p₂ ≤ 1 / (β * lam 1) ↔
          choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 1 ≤
            choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 0) := by
              haveI : ∀ j, IsProbabilityMeasure (expMeasure (lam j)) := fun j => isProbabilityMeasure_expMeasure (hlam j)
              have hform : ∀ (u : Fin 2 → ℝ) (m : Fin 2), choiceProb u lam m = G u lam m - lam m / Lsum u lam m * ∑ k ∈ strictlyWorse u m, choiceProb u lam k := by
                intro u
                set K : ℝ → ℝ := fun t => Real.exp (-(∑ k, lam k * max (u k - t) 0)) with hK
                have hexpIci : ∀ (r c : ℝ), 0 < r →
                    expMeasure r (Set.Ici c) = ENNReal.ofReal (Real.exp (-(r * max c 0))) := by
                  intro r c hr
                  haveI := isProbabilityMeasure_expMeasure hr
                  have hsing : expMeasure r {c} = 0 := by
                    show (volume.withDensity (gammaPDF 1 r)) {c} = 0
                    exact (withDensity_absolutelyContinuous _ _) (Real.volume_singleton)
                  have h1 : expMeasure r (Set.Ici c) = 1 - expMeasure r (Set.Iic c) := by
                    rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
                    congr 1
                    exact measure_congr (Iio_ae_eq_Iic' hsing)
                  rw [h1, ← ofReal_cdf, cdf_expMeasure_eq hr]
                  split_ifs with hc
                  · rw [max_eq_left hc]
                    have : 0 ≤ 1 - Real.exp (-(r * c)) := by
                      have : Real.exp (-(r * c)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
                      linarith
                    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ this]
                    congr 1; ring
                  · rw [max_eq_right (by linarith)]
                    simp
                have hQ : ∀ i, choiceProb u lam i = lam i * ∫ t in Set.Iio (u i), K t := by
                  intro i
                  have e := measurePreserving_piFinSuccAbove (fun j => expMeasure (lam j)) i
                  set T : Set (ℝ × (Fin 1 → ℝ)) :=
                    {p | ∀ k, u (i.succAbove k) - p.2 k ≤ u i - p.1} with hT
                  have hS : {z : Fin (1 + 1) → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i} =
                      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' T := by
                    ext z
                    simp only [Set.mem_setOf_eq, Set.mem_preimage, hT]
                    rw [Fin.forall_iff_succAbove i]
                    simp [MeasurableEquiv.piFinSuccAbove, Fin.succAbove_ne]
                    exact Iff.rfl
                  have hTm : MeasurableSet T := by
                    rw [hT]
                    simp only [Set.setOf_forall]
                    refine MeasurableSet.iInter fun k => ?_
                    exact measurableSet_le (by fun_prop) (by fun_prop)
                  have hslice : ∀ x : ℝ, Prod.mk x ⁻¹' T =
                      Set.pi Set.univ (fun k => Set.Ici (u (i.succAbove k) - u i + x)) := by
                    intro x; ext y
                    simp only [Set.mem_preimage, hT, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
                      Set.mem_Ici, true_implies]
                    refine forall_congr' fun k => ?_
                    constructor <;> intro h <;> linarith
                  set h : ℝ → ℝ := fun x => ∏ k, Real.exp (-(lam (i.succAbove k) *
                      max (u (i.succAbove k) - u i + x) 0)) with hh
                  have hmeas : errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i} =
                      ∫⁻ x, ENNReal.ofReal (h x) ∂(expMeasure (lam i)) := by
                    rw [hS, errorLaw, e.measure_preimage_equiv, Measure.prod_apply hTm]
                    refine lintegral_congr fun x => ?_
                    rw [hslice, Measure.pi_pi, hh, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
                    refine Finset.prod_congr rfl fun k _ => ?_
                    rw [hexpIci _ _ (hlam _)]
                  set Gt : ℝ → ℝ := Set.indicator (Set.Iic (u i)) (fun t => lam i * K t) with hGt
                  have hGt_nn : ∀ t, 0 ≤ Gt t := by
                    intro t; rw [hGt, Set.indicator_apply]
                    split_ifs
                    · exact mul_nonneg (hlam i).le (Real.exp_pos _).le
                    · exact le_rfl
                  have hpt : ∀ x, exponentialPDF (lam i) x * ENNReal.ofReal (h x) =
                      ENNReal.ofReal (Gt (u i - x)) := by
                    intro x
                    rw [exponentialPDF_eq, ← ENNReal.ofReal_mul (by
                      split_ifs
                      · exact mul_nonneg (hlam i).le (Real.exp_pos _).le
                      · exact le_rfl)]
                    congr 1
                    rw [hGt, Set.indicator_apply]
                    simp only [Set.mem_Iic, sub_le_self_iff]
                    split_ifs with hx
                    · have e1 : ∀ k, u (i.succAbove k) - (u i - x) = u (i.succAbove k) - u i + x :=
                        fun k => by ring
                      have e2 : u i - (u i - x) = x := by ring
                      rw [hh, hK]
                      simp only [e1, e2, max_eq_left hx, Fin.sum_univ_succAbove _ i]
                      rw [neg_add, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum]; ring
                    · simp
                  have hmeas2 : errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i} =
                      ∫⁻ x, ENNReal.ofReal (Gt (u i - x)) := by
                    rw [hmeas]
                    show ∫⁻ x, ENNReal.ofReal (h x) ∂(volume.withDensity (exponentialPDF (lam i))) = _
                    have hm : Measurable (exponentialPDF (lam i)) := (measurable_exponentialPDFReal _).ennreal_ofReal
                    have hhm : Measurable (fun x => ENNReal.ofReal (h x)) :=
                      (Continuous.measurable (by rw [hh]; fun_prop)).ennreal_ofReal
                    rw [lintegral_withDensity_eq_lintegral_mul _ hm hhm]
                    exact lintegral_congr fun x => hpt x
                  have hGtm : Measurable Gt := by
                    rw [hGt]
                    exact (Continuous.measurable (by fun_prop)).indicator measurableSet_Iic
                  have hm2 : AEStronglyMeasurable (fun x => Gt (u i - x)) volume :=
                    (hGtm.comp (measurable_id.const_sub _)).aestronglyMeasurable
                  rw [choiceProb, hmeas2, ← integral_eq_lintegral_of_nonneg_ae
                    (Filter.Eventually.of_forall fun x => hGt_nn _) hm2,
                    integral_sub_left_eq_self (fun t => Gt t) volume (u i), hGt,
                    integral_indicator measurableSet_Iic, integral_const_mul, integral_Iic_eq_integral_Iio]
                set Λ := ∑ k, lam k with hΛdef
                set C := ∑ k, lam k * u k with hC
                have hΛ : 0 < Λ := Finset.sum_pos (fun k _ => hlam k) Finset.univ_nonempty
                have hKpos : ∀ t, 0 < K t := fun t => Real.exp_pos _
                have hKcont : Continuous K := by rw [hK]; fun_prop
                have hKbound : ∀ t, K t ≤ Real.exp (-C) * Real.exp (Λ * t) := by
                  intro t
                  rw [← Real.exp_add]
                  apply Real.exp_le_exp.mpr
                  have h1 : ∑ k, lam k * (u k - t) ≤ ∑ k, lam k * max (u k - t) 0 :=
                    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hlam k).le
                  have h2 : ∑ k, lam k * (u k - t) = C - Λ * t := by
                    simp only [hC, hΛdef, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
                  linarith
                have hKint : ∀ c, IntegrableOn K (Set.Iic c) := by
                  intro c
                  have hE := (integrableOn_exp_mul_Iic hΛ c).const_mul (Real.exp (-C))
                  refine hE.mono' hKcont.aestronglyMeasurable.restrict ?_
                  exact Filter.Eventually.of_forall fun t => by
                    rw [Real.norm_eq_abs, abs_of_pos (hKpos t)]; exact hKbound t
                set R : ℝ → ℝ := fun t => ∑ k, Set.indicator (Set.Iio (u k)) (fun t => lam k * K t) t with hR
                have hRk : ∀ c k, IntegrableOn (Set.indicator (Set.Iio (u k)) (fun t => lam k * K t)) (Set.Iic c) :=
                  fun c k => ((hKint c).const_mul (lam k)).indicator measurableSet_Iio
                have hRint : ∀ c, IntegrableOn R (Set.Iic c) := by
                  intro c
                  exact integrable_finset_sum _ fun k _ => hRk c k
                have hmaxd : ∀ (a t : ℝ), HasDerivWithinAt (fun s => max (a - s) 0)
                    (if t < a then -1 else 0) (Set.Ioi t) t := by
                  intro a t
                  split_ifs with ht
                  · have : HasDerivAt (fun s => a - s) (-1) t := by simpa using (hasDerivAt_id t).const_sub a
                    refine (this.congr_of_eventuallyEq ?_).hasDerivWithinAt
                    filter_upwards [gt_mem_nhds ht] with s hs
                    exact max_eq_left (by linarith)
                  · refine (hasDerivWithinAt_const t (Set.Ioi t) (0:ℝ)).congr (fun s hs => ?_) ?_
                    · exact max_eq_right (by simp only [Set.mem_Ioi] at hs; linarith)
                    · exact max_eq_right (by linarith)
                have hKd : ∀ t, HasDerivWithinAt K (R t) (Set.Ioi t) t := by
                  intro t
                  have hs : HasDerivWithinAt (fun s => ∑ k, lam k * max (u k - s) 0)
                      (∑ k, lam k * (if t < u k then -1 else 0)) (Set.Ioi t) t :=
                    HasDerivWithinAt.fun_sum fun k _ => (hmaxd (u k) t).const_mul (lam k)
                  have := hs.neg.exp
                  convert this using 1
                  · funext x; simp [hK]
                  rw [hR]
                  simp only [Set.indicator_apply, Set.mem_Iio, Pi.neg_apply]
                  show _ = K t * _
                  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
                  refine Finset.sum_congr rfl fun k _ => ?_
                  split_ifs <;> ring
                have hFTC : ∀ b, ∫ t in Set.Iic b, R t = K b := by
                  intro b
                  have h1 := intervalIntegral_tendsto_integral_Iic (μ := volume) b (hRint b) Filter.tendsto_id
                  have hK0 : Filter.Tendsto K Filter.atBot (nhds 0) := by
                    have hE : Filter.Tendsto (fun t => Real.exp (-C) * Real.exp (Λ * t)) Filter.atBot
                        (nhds (Real.exp (-C) * 0)) :=
                      (Real.tendsto_exp_atBot.comp (Filter.tendsto_id.const_mul_atBot hΛ)).const_mul _
                    rw [mul_zero] at hE
                    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE
                      (fun t => (hKpos t).le) hKbound
                  have h2 : Filter.Tendsto (fun a => K b - K a) Filter.atBot (nhds (K b - 0)) :=
                    tendsto_const_nhds.sub hK0
                  rw [sub_zero] at h2
                  have h3 : Filter.Tendsto (fun a => ∫ t in a..b, R t) Filter.atBot (nhds (K b)) := by
                    refine h2.congr' ?_
                    filter_upwards [Filter.eventually_le_atBot b] with a ha
                    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ha hKcont.continuousOn
                      (fun x _ => hKd x)
                      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mpr
                        ((hRint b).mono_set Set.Ioc_subset_Iic_self))]
                  exact tendsto_nhds_unique h1 h3
                set I : ℝ → ℝ := fun x => ∫ t in Set.Iio x, K t with hI
                have hQ' : ∀ k, choiceProb u lam k = lam k * I (u k) := hQ
                have hL : ∀ m, Lsum u lam m = ∑ k, if u m ≤ u k then lam k else 0 := by
                  intro m; simp only [Lsum, better, betterThan, Finset.sum_filter]
                have hLpos : ∀ m, 0 < Lsum u lam m := by
                  intro m; unfold Lsum
                  exact Finset.sum_pos (fun k _ => hlam k) ⟨m, by simp [better, betterThan]⟩
                have hSW : ∀ m, ∑ k ∈ strictlyWorse u m, choiceProb u lam k =
                    ∑ k, if u k < u m then lam k * I (u k) else 0 := by
                  intro m; simp only [strictlyWorse, Finset.sum_filter, hQ']
                have hrel : ∀ m, K (u m) = Lsum u lam m * I (u m) +
                    ∑ k, if u k < u m then lam k * I (u k) else 0 := by
                  intro m
                  rw [← hFTC, integral_Iic_eq_integral_Iio, hR, integral_finset_sum _
                    (fun k _ => (hRk (u m) k).mono_set Set.Iio_subset_Iic_self)]
                  simp only [setIntegral_indicator measurableSet_Iio, hL, Finset.sum_mul, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun k _ => ?_
                  by_cases hk : u k < u m
                  · rw [if_pos hk, if_neg (not_le.mpr hk), Set.inter_eq_right.mpr (Set.Iio_subset_Iio hk.le),
                      integral_const_mul]; ring
                  · rw [if_neg hk, if_pos (not_lt.mp hk),
                      Set.inter_eq_left.mpr (Set.Iio_subset_Iio (not_lt.mp hk)), integral_const_mul]; ring
                have hG : ∀ m, G u lam m = lam m / Lsum u lam m * K (u m) := by
                  intro m
                  have : ∑ k ∈ better u m, lam k * (u k - u m) = ∑ k, lam k * max (u k - u m) 0 := by
                    rw [better, betterThan, Finset.sum_filter]
                    refine Finset.sum_congr rfl fun k _ => ?_
                    split_ifs with hk
                    · rw [max_eq_left (by linarith)]
                    · rw [max_eq_right (by linarith)]; ring
                  rw [G, this]
                have hmain : ∀ m, choiceProb u lam m =
                    G u lam m - lam m / Lsum u lam m * ∑ k ∈ strictlyWorse u m, choiceProb u lam k := by
                  intro m
                  have hl := hLpos m
                  rw [hQ', hG, hSW, hrel m]
                  field_simp
                  ring
                exact hmain
              clear this
              have hl0 := hlam 0
              have hl1 := hlam 1
              have hLpos : 0 < lam 0 + lam 1 := by linarith
              have hQlo : ∀ u : Fin 2 → ℝ, u 0 ≤ u 1 →
                  choiceProb u lam 0 = lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * (u 1 - u 0))) ∧
                  choiceProb u lam 1 = 1 - lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * (u 1 - u 0))) := by
                intro u h
                have e0 := hform u 0
                have e1 := hform u 1
                simp only [G, Lsum, better, betterThan, strictlyWorse, Finset.sum_filter, Fin.sum_univ_two] at e0 e1
                have h0 : choiceProb u lam 0 = lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * (u 1 - u 0))) := by
                  rw [e0]; simp [h, not_lt.mpr h]
                refine ⟨h0, ?_⟩
                rcases h.lt_or_eq with hlt | heq
                · rw [e1]; simp [hlt, not_le.mpr hlt, h0]
                  field_simp
                · rw [e1]; simp [heq]
                  field_simp; ring
              have hQhi : ∀ u : Fin 2 → ℝ, u 1 ≤ u 0 →
                  choiceProb u lam 1 = lam 1 / (lam 0 + lam 1) * Real.exp (-(lam 0 * (u 0 - u 1))) ∧
                  choiceProb u lam 0 = 1 - lam 1 / (lam 0 + lam 1) * Real.exp (-(lam 0 * (u 0 - u 1))) := by
                intro u h
                have e0 := hform u 0
                have e1 := hform u 1
                simp only [G, Lsum, better, betterThan, strictlyWorse, Finset.sum_filter, Fin.sum_univ_two] at e0 e1
                have h1 : choiceProb u lam 1 = lam 1 / (lam 0 + lam 1) * Real.exp (-(lam 0 * (u 0 - u 1))) := by
                  rw [e1]; simp [h, not_lt.mpr h]
                refine ⟨h1, ?_⟩
                rcases h.lt_or_eq with hlt | heq
                · rw [e0]; simp [hlt, not_le.mpr hlt, h1]
                  field_simp
                · rw [e0]; simp [heq]
                  field_simp; ring
              clear hform
              have hR0 : ∀ (p : Fin 2 → ℝ) (q P1 : ℝ), p 1 = P1 → firmRevenue α β lam (Function.update p 0 q) 0 =
                  if α 0 - β * q ≤ α 1 - β * P1 then
                    q * (lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * ((α 1 - β * P1 - α 0) + β * q))))
                  else q * (1 - lam 1 / (lam 0 + lam 1) *
                    Real.exp (-(lam 0 * ((α 0 - α 1 + β * P1) - β * q)))) := by
                intro p q P1 hP1; subst hP1
                have hu0 : util α β (Function.update p 0 q) 0 = α 0 - β * q := by simp [util]
                have hu1 : util α β (Function.update p 0 q) 1 = α 1 - β * p 1 := by simp [util]
                unfold firmRevenue
                rw [Function.update_self]
                split_ifs with h
                · rw [(hQlo _ (by rw [hu0, hu1]; exact h)).1, hu0, hu1]
                  congr 4; ring
                · rw [(hQhi _ (by rw [hu0, hu1]; linarith)).2, hu0, hu1]
                  congr 5; ring
              have hR1 : ∀ (p : Fin 2 → ℝ) (q P0 : ℝ), p 0 = P0 → firmRevenue α β lam (Function.update p 1 q) 1 =
                  if α 0 - β * P0 ≤ α 1 - β * q then
                    q * (1 - lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * ((α 1 - α 0 + β * P0) - β * q))))
                  else q * (lam 1 / (lam 0 + lam 1) *
                    Real.exp (-(lam 0 * ((α 0 - β * P0 - α 1) + β * q)))) := by
                intro p q P0 hP0; subst hP0
                have hu0 : util α β (Function.update p 1 q) 0 = α 0 - β * p 0 := by simp [util]
                have hu1 : util α β (Function.update p 1 q) 1 = α 1 - β * q := by simp [util]
                unfold firmRevenue
                rw [Function.update_self]
                split_ifs with h
                · rw [(hQlo _ (by rw [hu0, hu1]; exact h)).2, hu0, hu1]
                  congr 5; ring
                · rw [(hQhi _ (by rw [hu0, hu1]; linarith)).1, hu0, hu1]
                  congr 4; ring
              have hdA : ∀ K r c q : ℝ, HasDerivAt (fun q => q * (K * Real.exp (-(r * (c + β * q)))))
                  (K * Real.exp (-(r * (c + β * q))) * (1 - r * β * q)) q := by
                intro K r c q
                have h1 : HasDerivAt (fun q => -(r * (c + β * q))) (-(r * β)) q := by
                  have := ((hasDerivAt_id q).const_mul (-(r * β))).const_add (-(r * c))
                  have e : (fun q => -(r * (c + β * q))) = fun x => -(r * c) + -(r * β) * id x := by
                    funext x; simp; ring
                  rw [e]; convert this using 1 <;> first | rfl | ring
                have h3 := (hasDerivAt_id q).mul ((h1.exp).const_mul K)
                convert h3 using 1
                all_goals first | rfl | (simp only [id_eq, id]; ring) | (simp; ring)
              have hdB : ∀ K r c q : ℝ, HasDerivAt (fun q => q * (1 - K * Real.exp (-(r * (c - β * q)))))
                  (1 - K * Real.exp (-(r * (c - β * q))) * (1 + r * β * q)) q := by
                intro K r c q
                have h1 : HasDerivAt (fun q => -(r * (c - β * q))) (r * β) q := by
                  have := ((hasDerivAt_id q).const_mul (r * β)).const_add (-(r * c))
                  have e : (fun q => -(r * (c - β * q))) = fun x => -(r * c) + (r * β) * id x := by
                    funext x; simp; ring
                  rw [e]; convert this using 1 <;> first | rfl | ring
                have h3 := (hasDerivAt_id q).mul (((h1.exp).const_mul K).const_sub 1)
                convert h3 using 1
                all_goals first | rfl | (simp only [id_eq, id]; ring) | (simp; ring)
              have hRt : ∀ (F G : ℝ → ℝ) (F' a b : ℝ), a < b → HasDerivAt G F' a →
                  (∀ x ∈ Set.Icc a b, F x = G x) → (∀ x ∈ Set.Icc a b, F x ≤ F a) → F' ≤ 0 := by
                intro F G F' a b hab hG hFG hmax
                have hmaxG : IsMaxOn G (Set.Icc a b) a := fun x hx => by
                  show G x ≤ G a
                  rw [← hFG x hx, ← hFG a ⟨le_rfl, hab.le⟩]; exact hmax x hx
                have hy : b - a ∈ posTangentConeAt (Set.Icc a b) a :=
                  sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab.le ▸ Set.Subset.rfl)
                have := hmaxG.localize.hasFDerivWithinAt_nonpos hG.hasDerivWithinAt.hasFDerivWithinAt hy
                simp at this
                nlinarith
              have hLt : ∀ (F G : ℝ → ℝ) (F' a b : ℝ), a < b → HasDerivAt G F' b →
                  (∀ x ∈ Set.Icc a b, F x = G x) → (∀ x ∈ Set.Icc a b, F x ≤ F b) → 0 ≤ F' := by
                intro F G F' a b hab hG hFG hmax
                have hmaxG : IsMaxOn G (Set.Icc a b) b := fun x hx => by
                  show G x ≤ G b
                  rw [← hFG x hx, ← hFG b ⟨hab.le, le_rfl⟩]; exact hmax x hx
                have hy : a - b ∈ posTangentConeAt (Set.Icc a b) b :=
                  sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab.le])
                have := hmaxG.localize.hasFDerivWithinAt_nonpos hG.hasDerivWithinAt.hasFDerivWithinAt hy
                simp at this
                nlinarith
              obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, ∀ x, φ x = β * lam 1 * x +
                  Real.log ((lam 0 + β * lam 0 * lam 1 * x) / (lam 0 + lam 1)) - (1 + lam 1 * (α 1 - α 0)) :=
                ⟨_, fun x => rfl⟩
              have hb01 : 0 < β * lam 0 * lam 1 := by positivity
              have hφmono : ∀ x y, 0 < lam 0 + β * lam 0 * lam 1 * x → x < y → φ x < φ y := by
                intro x y hx hxy
                rw [hφ, hφ]
                have h1 : β * lam 1 * x < β * lam 1 * y := mul_lt_mul_of_pos_left hxy (mul_pos hβ hl1)
                have h2 : lam 0 + β * lam 0 * lam 1 * x < lam 0 + β * lam 0 * lam 1 * y := by
                  have := mul_lt_mul_of_pos_left hxy hb01; linarith
                have h3 : Real.log ((lam 0 + β * lam 0 * lam 1 * x) / (lam 0 + lam 1)) <
                    Real.log ((lam 0 + β * lam 0 * lam 1 * y) / (lam 0 + lam 1)) :=
                  Real.log_lt_log (div_pos hx hLpos) (div_lt_div_of_pos_right h2 hLpos)
                linarith
              have heqφ : ∀ x, (β * lam 1 * x = 1 + lam 1 * (α 1 - α 0) -
                  Real.log ((lam 0 + β * lam 0 * lam 1 * x) / (lam 0 + lam 1))) ↔ φ x = 0 := by
                intro x; rw [hφ]; constructor <;> intro h <;> linarith
              have h12' : 1 / lam 0 - 1 / lam 1 ≤ α 1 - α 0 := by linarith
              have hpLU : 1 / (β * lam 0) ≤ 1 / (β * lam 1) + (α 1 - α 0) / β := by
                have e1 : 1 / (β * lam 0) = (1 / lam 0) / β := by field_simp
                have e2 : 1 / (β * lam 1) = (1 / lam 1) / β := by field_simp
                rw [e1, e2, ← add_div]
                exact div_le_div_of_nonneg_right (by linarith) hβ.le
              have hpLpos : 0 < 1 / (β * lam 0) := by positivity
              have hApos : ∀ x, 1 / (β * lam 0) ≤ x → 0 < lam 0 + β * lam 0 * lam 1 * x := by
                intro x hx; have := mul_pos hb01 (lt_of_lt_of_le hpLpos hx); linarith
              have hφL : φ (1 / (β * lam 0)) ≤ 0 := by
                have hApL : lam 0 + β * lam 0 * lam 1 * (1 / (β * lam 0)) = lam 0 + lam 1 := by
                  field_simp
                rw [hφ, hApL, div_self hLpos.ne', Real.log_one]
                have e1 : β * lam 1 * (1 / (β * lam 0)) = lam 1 / lam 0 := by field_simp
                rw [e1]
                have e2 : lam 1 / lam 0 - 1 = lam 1 * (1 / lam 0 - 1 / lam 1) := by field_simp
                linarith [mul_le_mul_of_nonneg_left h12' hl1.le]
              have hφU : 0 ≤ φ (1 / (β * lam 1) + (α 1 - α 0) / β) := by
                rw [hφ]
                have e1 : β * lam 1 * (1 / (β * lam 1) + (α 1 - α 0) / β) = 1 + lam 1 * (α 1 - α 0) := by
                  field_simp
                have e2 : lam 0 + lam 1 ≤ lam 0 + β * lam 0 * lam 1 * (1 / (β * lam 1) + (α 1 - α 0) / β) := by
                  have e3 : β * lam 0 * lam 1 * (1 / (β * lam 1) + (α 1 - α 0) / β) =
                      lam 0 * (1 + lam 1 * (α 1 - α 0)) := by rw [← e1]; ring
                  rw [e3]
                  have h4 := mul_le_mul_of_nonneg_left h12' (mul_pos hl0 hl1).le
                  have e : lam 0 * lam 1 * (1 / lam 0 - 1 / lam 1) = lam 1 - lam 0 := by field_simp
                  linarith
                have : 0 ≤ Real.log ((lam 0 + β * lam 0 * lam 1 * (1 / (β * lam 1) + (α 1 - α 0) / β)) /
                    (lam 0 + lam 1)) := Real.log_nonneg (by rw [le_div_iff₀ hLpos]; linarith)
                linarith
              have hexist : ∃ x ∈ Set.Icc (1 / (β * lam 0)) (1 / (β * lam 1) + (α 1 - α 0) / β), φ x = 0 := by
                have hφeq : φ = fun x => β * lam 1 * x +
                    Real.log ((lam 0 + β * lam 0 * lam 1 * x) / (lam 0 + lam 1)) - (1 + lam 1 * (α 1 - α 0)) :=
                  funext hφ
                have hcont : ContinuousOn φ (Set.Icc (1 / (β * lam 0)) (1 / (β * lam 1) + (α 1 - α 0) / β)) := by
                  rw [hφeq]
                  refine ContinuousOn.sub (ContinuousOn.add (by fun_prop) (ContinuousOn.log (by fun_prop)
                    (fun x hx => (div_pos (hApos x hx.1) hLpos).ne'))) continuousOn_const
                obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hpLU hcont ⟨hφL, hφU⟩
                exact ⟨x, hx, hx0⟩
              have hbounds : ∀ x, 0 < lam 0 + β * lam 0 * lam 1 * x → φ x = 0 →
                  1 / (β * lam 0) ≤ x ∧ x ≤ 1 / (β * lam 1) + (α 1 - α 0) / β := by
                intro x hx h0; constructor
                · by_contra hc; push Not at hc; have := hφmono x _ hx hc; linarith
                · by_contra hc; push Not at hc; have := hφmono _ x (hApos _ hpLU) hc; linarith
              have huniq : ∀ x y, 0 < lam 0 + β * lam 0 * lam 1 * x → 0 < lam 0 + β * lam 0 * lam 1 * y →
                  φ x = 0 → φ y = 0 → x = y := by
                intro x y hx hy h1 h2; rcases lt_trichotomy x y with h|h|h
                · have := hφmono x y hx h; linarith
                · exact h
                · have := hφmono y x hy h; linarith
              refine ⟨?_, ?_⟩
              · obtain ⟨x, hx, hx0⟩ := hexist
                exact ⟨x, ⟨hApos x hx.1, (heqφ x).2 hx0⟩,
                  fun y hy => huniq y x hy.1 (hApos x hx.1) ((heqφ y).1 hy.2) hx0⟩
              intro p₂ hpos heq
              have hφ0 := (heqφ p₂).1 heq
              obtain ⟨hb1, hb2⟩ := hbounds p₂ hpos hφ0
              clear hφmono hφL hφU hexist hbounds heqφ hpLU hApos
              have hp2pos : 0 < p₂ := lt_of_lt_of_le hpLpos hb1
              set A := lam 0 + β * lam 0 * lam 1 * p₂ with hA
              have hβp0 : β * (1 / (β * lam 1)) = 1 / lam 1 := by field_simp
              have hβp2 : β * p₂ ≤ 1 / lam 1 + (α 1 - α 0) := by
                have := mul_le_mul_of_nonneg_left hb2 hβ.le
                have e : β * (1 / (β * lam 1) + (α 1 - α 0) / β) = 1 / lam 1 + (α 1 - α 0) := by field_simp
                linarith
              have hu0 : util α β ![1 / (β * lam 1), p₂] 0 = α 0 - 1 / lam 1 := by
                show α 0 - β * (1 / (β * lam 1)) = _; rw [hβp0]
              have hu1 : util α β ![1 / (β * lam 1), p₂] 1 = α 1 - β * p₂ := rfl
              have hle : α 0 - 1 / lam 1 ≤ α 1 - β * p₂ := by linarith
              have hEA : Real.exp (-(lam 1 * ((α 1 - β * p₂) - (α 0 - 1 / lam 1)))) = (lam 0 + lam 1) / A := by
                have e : lam 1 * (1 / lam 1) = 1 := by field_simp
                have : -(lam 1 * ((α 1 - β * p₂) - (α 0 - 1 / lam 1))) = -Real.log (A / (lam 0 + lam 1)) := by
                  linear_combination heq - e
                rw [this, Real.exp_neg, Real.exp_log (div_pos hpos hLpos), inv_div]
              have hQ := hQlo (util α β ![1 / (β * lam 1), p₂]) (by rw [hu0, hu1]; exact hle)
              rw [hu0, hu1, hEA] at hQ
              have hQ0 : choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 0 = lam 0 / A := by
                rw [hQ.1]; field_simp
              have hQ1 : choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 1 = β * lam 0 * lam 1 * p₂ / A := by
                rw [hQ.2]; field_simp; ring
              have hRv0 : firmRevenue α β lam ![1 / (β * lam 1), p₂] 0 = 1 / (β * lam 1) * (lam 0 / A) := by
                show (1 / (β * lam 1)) * choiceProb _ lam 0 = _; rw [hQ0]
              have hRv1 : firmRevenue α β lam ![1 / (β * lam 1), p₂] 1 = β * lam 0 * lam 1 * p₂ ^ 2 / A := by
                show p₂ * choiceProb _ lam 1 = _; rw [hQ1]; ring
              have hiff : p₂ ≤ 1 / (β * lam 1) ↔ β * lam 1 * p₂ ≤ 1 := by
                rw [le_div_iff₀ (by positivity)]; constructor <;> intro h <;> linarith
              have hb1p : 0 < β * lam 1 * p₂ := by positivity
              have hNE : IsPriceNE α β lam ![1 / (β * lam 1), p₂] := by
                clear huniq hφ0 hQ hdA hdB hRt hLt hφ hpLpos hb01 hQ0 hQ1 hu0 hu1 hiff hb1 hb2 heq
                have hB1 : ∀ q, 0 ≤ q → q * (1 - lam 0 / (lam 0 + lam 1) *
                    Real.exp (-(lam 1 * (α 1 - α 0 + 1 / lam 1 - β * q)))) ≤ β * lam 0 * lam 1 * p₂ ^ 2 / A := by
                  intro q hq
                  obtain ⟨w, hw⟩ : ∃ w, w = Real.exp (-(lam 1 * β * (p₂ - q))) := ⟨_, rfl⟩
                  have hsplit : Real.exp (-(lam 1 * (α 1 - α 0 + 1 / lam 1 - β * q))) =
                      (lam 0 + lam 1) / A * w := by
                    rw [hw, ← hEA, ← Real.exp_add]; congr 1; ring
                  rw [hsplit]
                  have hw1 : 1 - lam 1 * β * (p₂ - q) ≤ w := by
                    rw [hw]; have := Real.add_one_le_exp (-(lam 1 * β * (p₂ - q))); linarith only [this]
                  have key : (lam 1 * β * q) * (1 + β * lam 1 * p₂ - w) ≤ (β * lam 1 * p₂) * (β * lam 1 * p₂) := by
                    have hy : 1 - w ≤ lam 1 * β * (p₂ - q) := by linarith only [hw1]
                    have hMy : 0 ≤ lam 1 * β * q := by positivity
                    have h5 := mul_le_mul_of_nonneg_left hy hMy
                    calc (lam 1 * β * q) * (1 + β * lam 1 * p₂ - w)
                        = (lam 1 * β * q) * (β * lam 1 * p₂) + (lam 1 * β * q) * (1 - w) := by ring
                      _ ≤ (lam 1 * β * q) * (β * lam 1 * p₂) + (lam 1 * β * q) * (lam 1 * β * (p₂ - q)) := by
                          linarith only [h5]
                      _ = (β * lam 1 * p₂) * (β * lam 1 * p₂) - (lam 1 * β * (p₂ - q)) * (lam 1 * β * (p₂ - q)) := by
                          ring
                      _ ≤ (β * lam 1 * p₂) * (β * lam 1 * p₂) := by
                          linarith only [mul_self_nonneg (lam 1 * β * (p₂ - q))]
                  have e : β * lam 0 * lam 1 * p₂ ^ 2 / A - q * (1 - lam 0 / (lam 0 + lam 1) * ((lam 0 + lam 1) / A * w)) =
                      lam 0 * ((β * lam 1 * p₂) * (β * lam 1 * p₂) - (lam 1 * β * q) * (1 + β * lam 1 * p₂ - w)) /
                        (lam 1 * β * A) := by
                    field_simp
                    rw [hA]; ring
                  have : 0 ≤ lam 0 * ((β * lam 1 * p₂) * (β * lam 1 * p₂) - (lam 1 * β * q) * (1 + β * lam 1 * p₂ - w)) /
                        (lam 1 * β * A) :=
                    div_nonneg (mul_nonneg hl0.le (by linarith only [key])) (mul_pos (mul_pos hl1 hβ) hpos).le
                  linarith only [e, this]
                refine ⟨fun i => ?_, fun i q hq => ?_⟩
                · fin_cases i
                  · show 0 ≤ 1 / (β * lam 1); positivity
                  · show 0 ≤ p₂; linarith only [hp2pos]
                · fin_cases i
                  · show firmRevenue α β lam (Function.update ![1 / (β * lam 1), p₂] 0 q) 0 ≤
                      firmRevenue α β lam ![1 / (β * lam 1), p₂] 0
                    rw [hR0 _ q p₂ rfl, hRv0]
                    split_ifs with h
                    · have hsplit : Real.exp (-(lam 1 * (α 1 - β * p₂ - α 0 + β * q))) =
                          (lam 0 + lam 1) / A * Real.exp (1 - lam 1 * β * q) := by
                        rw [← hEA, ← Real.exp_add]; congr 1; field_simp; ring
                      have ht : lam 1 * β * q * Real.exp (1 - lam 1 * β * q) ≤ 1 := by
                        have h1 := Real.add_one_le_exp (lam 1 * β * q - 1)
                        have h2 : Real.exp (lam 1 * β * q - 1) * Real.exp (1 - lam 1 * β * q) = 1 := by
                          rw [← Real.exp_add]; simp
                        have h3 := Real.exp_pos (1 - lam 1 * β * q)
                        have h4 := mul_le_mul_of_nonneg_right (by linarith only [h1] : lam 1 * β * q ≤ Real.exp (lam 1 * β * q - 1)) h3.le
                        linarith only [h4, h2]
                      rw [hsplit]
                      have e : q * (lam 0 / (lam 0 + lam 1) * ((lam 0 + lam 1) / A * Real.exp (1 - lam 1 * β * q))) =
                          lam 0 / A * (q * Real.exp (1 - lam 1 * β * q)) := by field_simp
                      rw [e, mul_comm (1 / (β * lam 1))]
                      apply mul_le_mul_of_nonneg_left _ (div_pos hl0 hpos).le
                      rw [le_div_iff₀ (by positivity)]; linarith only [ht]
                    · obtain ⟨a, ha⟩ : ∃ a, a = α 0 - α 1 + β * p₂ := ⟨_, rfl⟩
                      obtain ⟨s, hs⟩ : ∃ s, s = α 0 - α 1 + β * p₂ - β * q := ⟨_, rfl⟩
                      obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(lam 0 * s)) := ⟨_, rfl⟩
                      rw [← hs, ← hE]
                      have hs0 : 0 < s := by rw [hs]; push Not at h; linarith only [h]
                      have hE1 : E ≤ 1 := by rw [hE]; exact Real.exp_le_one_iff.mpr (by have := mul_pos hl0 hs0; linarith only [this])
                      have hE2 : 1 - lam 0 * s ≤ E := by
                        rw [hE]; have := Real.add_one_le_exp (-(lam 0 * s)); linarith only [this]
                      have haL : a * lam 1 ≤ 1 := by
                        have : a ≤ 1 / lam 1 := by rw [ha]; linarith only [hβp2]
                        have := mul_le_mul_of_nonneg_right this hl1.le
                        rwa [div_mul_cancel₀ _ hl1.ne'] at this
                      have hβq : β * q = a - s := by rw [ha, hs]; ring
                      have ha0 : s ≤ a := by have := mul_nonneg hβ.le hq; linarith only [this, hβq]
                      have claim1 : (a - s) * ((lam 0 + lam 1) - lam 1 * E) ≤ a * lam 0 := by
                        have h1 : a * lam 1 * (1 - E) ≤ a * lam 1 * (lam 0 * s) :=
                          mul_le_mul_of_nonneg_left (by linarith only [hE2]) (mul_nonneg (by linarith only [ha0, hs0]) hl1.le)
                        have h2 : a * lam 1 * (lam 0 * s) ≤ 1 * (lam 0 * s) :=
                          mul_le_mul_of_nonneg_right haL (by positivity)
                        have h3 : 0 ≤ s * lam 1 * (1 - E) := by
                          have : 0 ≤ 1 - E := by linarith only [hE1]
                          positivity
                        linarith only [h1, h2, h3]
                      have hEA' : Real.exp (lam 1 * a - 1) = (lam 0 + lam 1) / A := by
                        rw [← hEA]; congr 1; rw [ha]; field_simp; ring
                      have hLa : lam 1 * a ≤ (lam 0 + lam 1) / A := by
                        rw [← hEA']; have := Real.add_one_le_exp (lam 1 * a - 1); linarith only [this]
                      have hLa2 : a * lam 1 * A ≤ lam 0 + lam 1 := by
                        rw [le_div_iff₀ hpos] at hLa; linarith only [hLa]
                      have hq' : q = (a - s) / β := by field_simp; linarith only [hβq]
                      calc q * (1 - lam 1 / (lam 0 + lam 1) * E)
                          = (a - s) * ((lam 0 + lam 1) - lam 1 * E) / (β * (lam 0 + lam 1)) := by
                            rw [hq']; field_simp
                        _ ≤ a * lam 0 / (β * (lam 0 + lam 1)) :=
                            div_le_div_of_nonneg_right claim1 (by positivity)
                        _ ≤ 1 / (β * lam 1) * (lam 0 / A) := by
                            have key : 1 / (β * lam 1) * (lam 0 / A) - a * lam 0 / (β * (lam 0 + lam 1)) =
                                lam 0 * ((lam 0 + lam 1) - a * lam 1 * A) / (β * lam 1 * A * (lam 0 + lam 1)) := by
                              field_simp
                            have : 0 ≤ lam 0 * ((lam 0 + lam 1) - a * lam 1 * A) /
                                (β * lam 1 * A * (lam 0 + lam 1)) :=
                              div_nonneg (mul_nonneg hl0.le (by linarith only [hLa2]))
                                (mul_pos (mul_pos (mul_pos hβ hl1) hpos) hLpos).le
                            linarith only [key, this]
                  · show firmRevenue α β lam (Function.update ![1 / (β * lam 1), p₂] 1 q) 1 ≤
                      firmRevenue α β lam ![1 / (β * lam 1), p₂] 1
                    rw [hR1 _ q (1 / (β * lam 1)) rfl, hRv1]
                    split_ifs with h <;> rw [hβp0] at *
                    · exact hB1 q hq
                    · push Not at h
                      obtain ⟨b, hb⟩ : ∃ b, b = α 1 - α 0 + 1 / lam 1 := ⟨_, rfl⟩
                      have hbL : 1 ≤ b * lam 0 := by
                        have : 1 / lam 0 ≤ b := by rw [hb]; linarith only [h12]
                        have := mul_le_mul_of_nonneg_right this hl0.le
                        rwa [div_mul_cancel₀ _ hl0.ne'] at this
                      have hb0 : 0 < b := by
                        by_contra hc; push Not at hc
                        have := mul_le_mul_of_nonneg_right hc hl0.le; linarith only [this, hbL]
                      obtain ⟨v, hv⟩ : ∃ v, v = α 0 - 1 / lam 1 - α 1 + β * q := ⟨_, rfl⟩
                      have hv0 : 0 < v := by rw [hv]; linarith only [h]
                      rw [← hv]
                      have hβq : β * q = b + v := by rw [hb, hv]; ring
                      have claim : β * q * Real.exp (-(lam 0 * v)) ≤ b := by
                        have h1 := Real.add_one_le_exp (lam 0 * v)
                        have h2 : Real.exp (lam 0 * v) * Real.exp (-(lam 0 * v)) = 1 := by
                          rw [← Real.exp_add]; simp
                        have h3 := Real.exp_pos (-(lam 0 * v))
                        have h4 : β * q ≤ b * Real.exp (lam 0 * v) := by
                          have h6 := mul_le_mul_of_nonneg_left h1 hb0.le
                          have h7 := mul_le_mul_of_nonneg_right hbL hv0.le
                          rw [hβq]; linarith only [h6, h7]
                        have h5 : b * Real.exp (lam 0 * v) * Real.exp (-(lam 0 * v)) = b := by
                          rw [mul_assoc, h2, mul_one]
                        have h8 := mul_le_mul_of_nonneg_right h4 h3.le
                        linarith only [h8, h5]
                      have hb1' := hB1 (b / β) (by positivity)
                      have e1 : α 1 - α 0 + 1 / lam 1 - β * (b / β) = 0 := by rw [hb]; field_simp; ring
                      rw [e1] at hb1'
                      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hb1'
                      refine le_trans ?_ hb1'
                      have e2 : b / β * (1 - lam 0 / (lam 0 + lam 1)) = lam 1 / (lam 0 + lam 1) * (b / β) := by
                        field_simp; ring
                      rw [e2, mul_left_comm]
                      apply mul_le_mul_of_nonneg_left _ (by positivity)
                      rw [le_div_iff₀ hβ]; linarith only [claim]
              have huniqNE : ∀ p, IsPriceNE α β lam p → p = ![1 / (β * lam 1), p₂] := by
                have hfin : ∀ P1, 0 < P1 → φ P1 = 0 → P1 = p₂ := fun P1 h1 h2 =>
                  huniq P1 p₂ (by have := mul_pos hb01 h1; linarith only [this, hl0]) hpos h2 hφ0
                clear hNE hQ hEA hQ0 hQ1 hRv0 hRv1 hiff hu0 hu1 hpLpos hb1 hb2 heq hβp0 hβp2 hle hb1p h12' huniq hφ0 hpos hb01 hp2pos
                intro p hp
                obtain ⟨hnn, hdev⟩ := hp
                obtain ⟨P0, hP0⟩ : ∃ P0, p 0 = P0 := ⟨_, rfl⟩
                obtain ⟨P1, hP1⟩ : ∃ P1, p 1 = P1 := ⟨_, rfl⟩
                have hF0 : ∀ x, 0 ≤ x → firmRevenue α β lam (Function.update p 0 x) 0 ≤
                    firmRevenue α β lam (Function.update p 0 P0) 0 := by
                  intro x hx; rw [← hP0, Function.update_eq_self]; exact hdev 0 x hx
                have hF1 : ∀ x, 0 ≤ x → firmRevenue α β lam (Function.update p 1 x) 1 ≤
                    firmRevenue α β lam (Function.update p 1 P1) 1 := by
                  intro x hx; rw [← hP1, Function.update_eq_self]; exact hdev 1 x hx
                have hl1L : lam 1 / (lam 0 + lam 1) < 1 := (div_lt_one hLpos).2 (by linarith only [hl0])
                have hl0L : lam 0 / (lam 0 + lam 1) < 1 := (div_lt_one hLpos).2 (by linarith only [hl1])
                have hpos0 : 0 < P0 := by
                  rcases (hnn 0).lt_or_eq with h | h
                  · rwa [hP0] at h
                  exfalso
                  have hz : firmRevenue α β lam (Function.update p 0 P0) 0 = 0 := by
                    rw [← hP0, ← h]; unfold firmRevenue; rw [Function.update_self, zero_mul]
                  have h1 := hF0 1 zero_le_one
                  rw [hz, hR0 p 1 P1 hP1] at h1
                  split_ifs at h1 with h'
                  · have := mul_pos (div_pos hl0 hLpos) (Real.exp_pos (-(lam 1 * (α 1 - β * P1 - α 0 + β * 1))))
                    linarith only [h1, this]
                  · have hE : Real.exp (-(lam 0 * (α 0 - α 1 + β * P1 - β * 1))) ≤ 1 :=
                      Real.exp_le_one_iff.mpr (by have := mul_pos hl0 (by linarith only [not_le.1 h'] : 0 < α 0 - α 1 + β * P1 - β * 1); linarith only [this])
                    have := mul_le_of_le_one_right (div_pos hl1 hLpos).le hE
                    linarith only [h1, this, hl1L]
                have hpos1 : 0 < P1 := by
                  rcases (hnn 1).lt_or_eq with h | h
                  · rwa [hP1] at h
                  exfalso
                  have hz : firmRevenue α β lam (Function.update p 1 P1) 1 = 0 := by
                    rw [← hP1, ← h]; unfold firmRevenue; rw [Function.update_self, zero_mul]
                  have h1 := hF1 1 zero_le_one
                  rw [hz, hR1 p 1 P0 hP0] at h1
                  split_ifs at h1 with h'
                  · have hE : Real.exp (-(lam 1 * (α 1 - α 0 + β * P0 - β * 1))) ≤ 1 :=
                      Real.exp_le_one_iff.mpr (by have := mul_nonneg hl1.le (by linarith only [h'] : 0 ≤ α 1 - α 0 + β * P0 - β * 1); linarith only [this])
                    have := mul_le_of_le_one_right (div_pos hl0 hLpos).le hE
                    linarith only [h1, this, hl0L]
                  · have := mul_pos (div_pos hl1 hLpos) (Real.exp_pos (-(lam 0 * (α 0 - β * P0 - α 1 + β * 1))))
                    linarith only [h1, this]
                by_cases hcase : α 0 - β * P0 ≤ α 1 - β * P1
                · -- firm 0 is the low firm: λ₁ β P0 = 1
                  have hK0 := mul_pos (div_pos hl0 hLpos) (Real.exp_pos (-(lam 1 * (α 1 - β * P1 - α 0 + β * P0))))
                  have d0R := hRt (fun x => firmRevenue α β lam (Function.update p 0 x) 0)
                    (fun q => q * (lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * ((α 1 - β * P1 - α 0) + β * q)))))
                    _ P0 (P0 + 1) (lt_add_one P0) (hdA _ _ _ P0)
                    (fun x hx => by
                      beta_reduce
                      rw [hR0 p x P1 hP1, if_pos (by have := mul_le_mul_of_nonneg_left hx.1 hβ.le; linarith only [this, hcase])])
                    (fun x hx => hF0 x (by linarith only [hx.1, hpos0]))
                  have hge : 1 ≤ lam 1 * β * P0 := by
                    have := nonpos_of_mul_nonpos_right d0R hK0
                    linarith only [this]
                  have hle1 : lam 1 * β * P0 ≤ 1 := by
                    rcases hcase.lt_or_eq with hlt | heq'
                    · obtain ⟨δ, hδ⟩ : ∃ δ, δ = (α 1 - β * P1 - (α 0 - β * P0)) / (2 * β) := ⟨_, rfl⟩
                      have hβδ : β * δ = (α 1 - β * P1 - (α 0 - β * P0)) / 2 := by rw [hδ]; field_simp
                      have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (sub_pos.2 hlt) (mul_pos two_pos hβ)
                      have d0L := hLt (fun x => firmRevenue α β lam (Function.update p 0 x) 0)
                        (fun q => q * (lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * ((α 1 - β * P1 - α 0) + β * q)))))
                        _ (max (P0 / 2) (P0 - δ)) P0 (max_lt (by linarith only [hpos0]) (by linarith only [hδ0])) (hdA _ _ _ P0)
                        (fun x hx => by
                          beta_reduce
                          have h1 := (max_le_iff.1 hx.1).2
                          have := mul_le_mul_of_nonneg_left h1 hβ.le
                          rw [hR0 p x P1 hP1, if_pos (by rw [mul_sub] at this; linarith only [this, hβδ, hlt])])
                        (fun x hx => hF0 x (by linarith only [(max_le_iff.1 hx.1).1, hpos0]))
                      have := nonneg_of_mul_nonneg_right d0L hK0
                      linarith only [this]
                    · have d0L := hLt (fun x => firmRevenue α β lam (Function.update p 0 x) 0)
                        (fun q => q * (1 - lam 1 / (lam 0 + lam 1) * Real.exp (-(lam 0 * ((α 0 - α 1 + β * P1) - β * q)))))
                        _ 0 P0 hpos0 (hdB _ _ _ P0)
                        (fun x hx => by
                          beta_reduce
                          rw [hR0 p x P1 hP1]
                          split_ifs with h
                          · have := mul_le_mul_of_nonneg_left hx.2 hβ.le
                            have e1 : α 1 - β * P1 - α 0 + β * x = 0 := by linarith only [this, h, heq']
                            have e2 : α 0 - α 1 + β * P1 - β * x = 0 := by linarith only [this, h, heq']
                            rw [e1, e2]; simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
                            congr 1; field_simp; ring
                          · rfl)
                        (fun x hx => hF0 x hx.1)
                      have e2 : α 0 - α 1 + β * P1 - β * P0 = 0 := by linarith only [heq']
                      rw [e2, mul_zero, neg_zero, Real.exp_zero, mul_one] at d0L
                      have h3 : lam 1 / (lam 0 + lam 1) * (1 + lam 0 * β * P0) * (lam 0 + lam 1) =
                          lam 1 * (1 + lam 0 * β * P0) := by field_simp
                      have h4 := mul_le_mul_of_nonneg_right (by linarith only [d0L] : lam 1 / (lam 0 + lam 1) *
                        (1 + lam 0 * β * P0) ≤ 1) hLpos.le
                      rw [h3, one_mul] at h4
                      have h5 : lam 0 * (lam 1 * β * P0) ≤ lam 0 * 1 := by linarith only [h4]
                      exact le_of_mul_le_mul_left h5 hl0
                  have hP0v : lam 1 * β * P0 = 1 := le_antisymm hle1 hge
                  -- firm 1 is the high firm: first-order condition
                  obtain ⟨X, hX⟩ : ∃ X, X = -(lam 1 * ((α 1 - α 0 + β * P0) - β * P1)) := ⟨_, rfl⟩
                  have d1L := hLt (fun x => firmRevenue α β lam (Function.update p 1 x) 1)
                    (fun q => q * (1 - lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * ((α 1 - α 0 + β * P0) - β * q)))))
                    _ 0 P1 hpos1 (hdB _ _ _ P1)
                    (fun x hx => by
                      beta_reduce
                      rw [hR1 p x P0 hP0, if_pos (by have := mul_le_mul_of_nonneg_left hx.2 hβ.le; linarith only [this, hcase])])
                    (fun x hx => hF1 x hx.1)
                  have hD1 : 1 - lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * ((α 1 - α 0 + β * P0) - β * P1))) *
                      (1 + lam 1 * β * P1) ≤ 0 := by
                    rcases hcase.lt_or_eq with hlt | heq'
                    · obtain ⟨δ, hδ⟩ : ∃ δ, δ = (α 1 - β * P1 - (α 0 - β * P0)) / (2 * β) := ⟨_, rfl⟩
                      have hβδ : β * δ = (α 1 - β * P1 - (α 0 - β * P0)) / 2 := by rw [hδ]; field_simp
                      have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (sub_pos.2 hlt) (mul_pos two_pos hβ)
                      exact hRt (fun x => firmRevenue α β lam (Function.update p 1 x) 1)
                        (fun q => q * (1 - lam 0 / (lam 0 + lam 1) * Real.exp (-(lam 1 * ((α 1 - α 0 + β * P0) - β * q)))))
                        _ P1 (P1 + δ) (by linarith only [hδ0]) (hdB _ _ _ P1)
                        (fun x hx => by
                          beta_reduce
                          have := mul_le_mul_of_nonneg_left hx.2 hβ.le
                          rw [hR1 p x P0 hP0, if_pos (by rw [mul_add] at this; linarith only [this, hβδ, hlt])])
                        (fun x hx => hF1 x (by linarith only [hx.1, hpos1]))
                    · have d1R := hRt (fun x => firmRevenue α β lam (Function.update p 1 x) 1)
                        (fun q => q * (lam 1 / (lam 0 + lam 1) * Real.exp (-(lam 0 * ((α 0 - β * P0 - α 1) + β * q)))))
                        _ P1 (P1 + 1) (lt_add_one P1) (hdA _ _ _ P1)
                        (fun x hx => by
                          beta_reduce
                          rw [hR1 p x P0 hP0]
                          split_ifs with h
                          · have := mul_le_mul_of_nonneg_left hx.1 hβ.le
                            have e1 : α 1 - α 0 + β * P0 - β * x = 0 := by linarith only [this, h, heq']
                            have e2 : α 0 - β * P0 - α 1 + β * x = 0 := by linarith only [this, h, heq']
                            rw [e1, e2]; simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
                            congr 1; field_simp; ring
                          · rfl)
                        (fun x hx => hF1 x (by linarith only [hx.1, hpos1]))
                      have e1 : α 1 - α 0 + β * P0 - β * P1 = 0 := by linarith only [heq']
                      have e2 : α 0 - β * P0 - α 1 + β * P1 = 0 := by linarith only [heq']
                      rw [e2, mul_zero, neg_zero, Real.exp_zero, mul_one] at d1R
                      rw [e1, mul_zero, neg_zero, Real.exp_zero, mul_one]
                      have h3 : 1 - lam 0 / (lam 0 + lam 1) * (1 + lam 1 * β * P1) =
                          lam 1 / (lam 0 + lam 1) * (1 - lam 0 * β * P1) := by field_simp; ring
                      rw [h3]; exact d1R
                  have hFOC : lam 0 / (lam 0 + lam 1) * Real.exp X * (1 + lam 1 * β * P1) = 1 := by
                    rw [hX]; linarith only [d1L, hD1]
                  have hEX : Real.exp X * ((lam 0 + β * lam 0 * lam 1 * P1) / (lam 0 + lam 1)) = 1 := by
                    rw [← hFOC]; ring
                  have hlog : Real.log ((lam 0 + β * lam 0 * lam 1 * P1) / (lam 0 + lam 1)) = -X := by
                    rw [eq_inv_of_mul_eq_one_right hEX, ← Real.exp_neg, Real.log_exp]
                  have hφP1 : φ P1 = 0 := by
                    rw [hφ, hlog, hX]; linarith only [hP0v]
                  have hP1v : P1 = p₂ := hfin P1 hpos1 hφP1
                  have hP0v' : P0 = 1 / (β * lam 1) := by
                    rw [eq_div_iff (by positivity)]; linarith only [hP0v]
                  funext i
                  fin_cases i
                  · show p 0 = 1 / (β * lam 1); rw [hP0, hP0v']
                  · show p 1 = p₂; rw [hP1, hP1v]
                · -- firm 1 strictly low: impossible
                  exfalso
                  push Not at hcase
                  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (α 0 - β * P0 - (α 1 - β * P1)) / (2 * β) := ⟨_, rfl⟩
                  have hβδ : β * δ = (α 0 - β * P0 - (α 1 - β * P1)) / 2 := by rw [hδ]; field_simp
                  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (sub_pos.2 hcase) (mul_pos two_pos hβ)
                  have hK1 := mul_pos (div_pos hl1 hLpos) (Real.exp_pos (-(lam 0 * (α 0 - β * P0 - α 1 + β * P1))))
                  have d1L := hLt (fun x => firmRevenue α β lam (Function.update p 1 x) 1)
                    (fun q => q * (lam 1 / (lam 0 + lam 1) * Real.exp (-(lam 0 * ((α 0 - β * P0 - α 1) + β * q)))))
                    _ (max (P1 / 2) (P1 - δ)) P1 (max_lt (by linarith only [hpos1]) (by linarith only [hδ0])) (hdA _ _ _ P1)
                    (fun x hx => by
                      beta_reduce
                      have h1 := (max_le_iff.1 hx.1).2
                      have := mul_le_mul_of_nonneg_left h1 hβ.le
                      rw [hR1 p x P0 hP0, if_neg (by rw [mul_sub] at this; linarith only [this, hβδ, hcase])])
                    (fun x hx => hF1 x (by linarith only [(max_le_iff.1 hx.1).1, hpos1]))
                  have h1 : lam 0 * β * P1 ≤ 1 := by
                    have := nonneg_of_mul_nonneg_right d1L hK1
                    linarith only [this]
                  have d0R := hRt (fun x => firmRevenue α β lam (Function.update p 0 x) 0)
                    (fun q => q * (1 - lam 1 / (lam 0 + lam 1) * Real.exp (-(lam 0 * ((α 0 - α 1 + β * P1) - β * q)))))
                    _ P0 (P0 + δ) (by linarith only [hδ0]) (hdB _ _ _ P0)
                    (fun x hx => by
                      beta_reduce
                      have := mul_le_mul_of_nonneg_left hx.2 hβ.le
                      rw [hR0 p x P1 hP1, if_neg (by rw [mul_add] at this; linarith only [this, hβδ, hcase])])
                    (fun x hx => hF0 x (by linarith only [hx.1, hpos0]))
                  have hE : Real.exp (-(lam 0 * (α 0 - α 1 + β * P1 - β * P0))) ≤ 1 :=
                    Real.exp_le_one_iff.mpr (by
                      have := mul_pos hl0 (by linarith only [hcase] : 0 < α 0 - α 1 + β * P1 - β * P0); linarith only [this])
                  have h2 : 0 ≤ 1 + lam 0 * β * P0 := by positivity
                  have h3 := mul_le_mul_of_nonneg_right
                    (mul_le_of_le_one_right (div_pos hl1 hLpos).le hE) h2
                  have h4 : 1 ≤ lam 1 / (lam 0 + lam 1) * (1 + lam 0 * β * P0) := by linarith only [d0R, h3]
                  have h5 := mul_le_mul_of_nonneg_right h4 hLpos.le
                  have h6 : lam 1 / (lam 0 + lam 1) * (1 + lam 0 * β * P0) * (lam 0 + lam 1) =
                      lam 1 * (1 + lam 0 * β * P0) := by field_simp
                  rw [h6, one_mul] at h5
                  have h7 : lam 0 * 1 ≤ lam 0 * (lam 1 * β * P0) := by linarith only [h5]
                  have h8 := le_of_mul_le_mul_left h7 hl0
                  -- β P0 ≥ 1/λ₁ and β P1 ≤ 1/λ₀
                  have h9 : 1 / lam 1 ≤ β * P0 := by
                    rw [div_le_iff₀ hl1]; linarith only [h8]
                  have h10 : β * P1 ≤ 1 / lam 0 := by
                    rw [le_div_iff₀ hl0]; linarith only [h1]
                  linarith only [h9, h10, h12, hcase]
              refine ⟨⟨hb1, hb2⟩, hNE, huniqNE, hQ0, hRv0, hQ1, hRv1, by rw [hu0, hu1]; exact hle, ?_, ?_, ?_⟩
              · rw [hQ0, hQ1]; field_simp
              · have key : 1 / (β * lam 1) * (lam 0 / A) - β * lam 0 * lam 1 * p₂ ^ 2 / A =
                    lam 0 * (1 - β * lam 1 * p₂) * (1 + β * lam 1 * p₂) / (β * lam 1 * A) := by
                  field_simp; ring
                rw [hRv0, hRv1, hiff, ← sub_nonneg, key, le_div_iff₀ (by positivity), zero_mul]
                constructor
                · intro h; by_contra hc; push Not at hc
                  have := mul_neg_of_pos_of_neg (mul_pos hl0 (by linarith : (0:ℝ) < 1 + β * lam 1 * p₂))
                    (by linarith : 1 - β * lam 1 * p₂ < 0)
                  linarith
                · intro h; exact mul_nonneg (mul_nonneg hl0.le (sub_nonneg.2 h)) (by linarith only [hb1p])
              · rw [hQ0, hQ1, div_le_div_iff_of_pos_right hpos, hiff]
                constructor
                · intro h
                  have := mul_le_mul_of_nonneg_left h hl0.le
                  linarith
                · intro h
                  have h' : lam 0 * (β * lam 1 * p₂) ≤ lam 0 * 1 := by linarith
                  exact le_of_mul_le_mul_left h' hl0
