-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:43.787195+00:00
-- url     : https://prove2.me/submissions/59380e0b-957b-470b-91be-c847354d4842

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i j : Fin n) (hadj : Adjacent u i j) :
    (u i < u j →
        choiceProb u lam j =
          G u lam j - lam j / Lsum u lam j * ∑ k ∈ worse u i, choiceProb u lam k) ∧
      choiceProb u lam j =
        G u lam j - lam j / Lsum u lam j * ∑ k ∈ strictlyWorse u j, choiceProb u lam k ∧
      choiceProb u lam j =
        G u lam j - lam j * Lsum u lam i / (lam i * Lsum u lam j) * G u lam i +
          lam j / lam i * choiceProb u lam i := by
            obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
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
            haveI : ∀ j, IsProbabilityMeasure (expMeasure (lam j)) :=
              fun j => isProbabilityMeasure_expMeasure (hlam j)
            have hQ : ∀ i, choiceProb u lam i = lam i * ∫ t in Set.Iio (u i), K t := by
              intro i
              have e := measurePreserving_piFinSuccAbove (fun j => expMeasure (lam j)) i
              set T : Set (ℝ × (Fin n' → ℝ)) :=
                {p | ∀ k, u (i.succAbove k) - p.2 k ≤ u i - p.1} with hT
              have hS : {z : Fin (n' + 1) → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i} =
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
            refine ⟨fun hij => ?_, hmain j, ?_⟩
            · have hset : strictlyWorse u j = worse u i := by
                ext k
                simp only [strictlyWorse, worse, Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro hk
                  by_contra hc
                  push_neg at hc
                  exact hadj.2.2 ⟨k, fun h => by subst h; linarith, fun h => by subst h; linarith, hc, hk⟩
                · intro hk; linarith
              rw [hmain j, hset]
            · have hij := hadj.2.1
              have hdiff : (∑ k, if u k < u j then lam k * I (u k) else 0) -
                  (∑ k, if u k < u i then lam k * I (u k) else 0) =
                  (Lsum u lam i - Lsum u lam j) * I (u i) := by
                rw [hL i, hL j, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                have hk : u k < u i ∨ u k = u i ∨ u j ≤ u k := by
                  by_cases hki : k = i
                  · right; left; rw [hki]
                  by_cases hkj : k = j
                  · right; right; rw [hkj]
                  rcases lt_trichotomy (u k) (u i) with h | h | h
                  · left; exact h
                  · right; left; exact h
                  · right; right; by_contra hc; push_neg at hc; exact hadj.2.2 ⟨k, hki, hkj, h, hc⟩
                rcases hk with h | h | h
                · split_ifs <;> first | (exfalso; linarith) | ring
                · simp only [h]
                  split_ifs <;> first | (exfalso; linarith) | ring
                · split_ifs <;> first | (exfalso; linarith) | ring
              have hS : (∑ k, if u k < u j then lam k * I (u k) else 0) =
                  (∑ k, if u k < u i then lam k * I (u k) else 0) +
                  (Lsum u lam i - Lsum u lam j) * I (u i) := by linarith
              have hli := hLpos i
              have hlj := hLpos j
              have hlami := hlam i
              have hlamj := hlam j
              rw [hQ' j, hQ' i, hG j, hG i, hrel j, hrel i, hS]
              field_simp
              ring
