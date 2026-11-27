-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:06.714944+00:00
-- url     : https://prove2.me/submissions/6ac303f0-a341-42de-b065-b07112a8070f

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (α lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) :
    -- (a) Monotonicity and Positivity
    ((∀ u, 0 < tau u lam i) ∧ Continuous (fun u => tau u lam i) ∧
      (∀ (u : Fin n → ℝ) (x : ℝ), (∀ j, j ≠ i → x ≤ u j) →
          tau (Function.update u i x) lam i = 1 / (Ltot lam - lam i)) ∧
      (∀ (u : Fin n → ℝ) (x : ℝ), 1 / (Ltot lam - lam i) ≤ tau (Function.update u i x) lam i) ∧
      (∀ u : Fin n → ℝ, StrictMonoOn (fun x => tau (Function.update u i x) lam i)
          {x | (∃ j, j ≠ i ∧ u j < x) ∧ x ≤ α i})) ∧
    -- (b) First-order Condition
    (∀ u : Fin n → ℝ,
      (∃! x : ℝ, α i - x = tau (Function.update u i x) lam i) ∧
        ∃! x : ℝ, x ≤ α i ∧ α i - x = tau (Function.update u i x) lam i) ∧
    -- (c) Independence from Higher Ideal Utilities
    (∀ u v : Fin n → ℝ, v i = u i → (∀ j, u j < u i → v j = u j) →
      (∀ j, j ≠ i → u i ≤ u j → u i ≤ v j) → tau v lam i = tau u lam i) ∧
    -- (d) Crossover Points
    (∀ (u : Fin n → ℝ) (j : Fin n), j ≠ i → u i = u j →
      (tau u lam i ≤ tau u lam j ↔ lam i ≤ lam j) ∧
        (tau u lam i < tau u lam j ↔ lam i < lam j)) := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          have hP : ∀ k, IsProbabilityMeasure (expMeasure (lam k)) :=
            fun k => isProbabilityMeasure_expMeasure (hlam k)
          have hS : ∀ r : ℝ, 0 < r → ∀ c : ℝ,
              expMeasure r (Set.Ici c) = ENNReal.ofReal (Real.exp (-(r * max c 0))) := by
            intro r hr c
            haveI := isProbabilityMeasure_expMeasure hr
            have hac : expMeasure r ≪ volume := withDensity_absolutelyContinuous _ _
            have h0 : expMeasure r {c} = 0 := hac (Real.volume_singleton)
            have h1 : expMeasure r (Set.Ici c) = expMeasure r (Set.Ioi c) := by
              apply le_antisymm
              · calc expMeasure r (Set.Ici c) ≤ expMeasure r (Set.Ioi c ∪ {c}) := by
                      apply measure_mono
                      intro x hx
                      rcases eq_or_lt_of_le (Set.mem_Ici.1 hx) with h | h
                      · right; exact h.symm
                      · left; exact h
                  _ ≤ expMeasure r (Set.Ioi c) + expMeasure r {c} := measure_union_le _ _
                  _ = expMeasure r (Set.Ioi c) := by rw [h0, add_zero]
              · exact measure_mono Set.Ioi_subset_Ici_self
            have h2 : expMeasure r (Set.Ioi c) = 1 - expMeasure r (Set.Iic c) := by
              rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
            rw [h1, h2, ← ofReal_cdf, cdf_expMeasure_eq hr]
            split_ifs with hc
            · rw [max_eq_left hc]
              have he : Real.exp (-(r * c)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
              rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
              congr 1; ring
            · rw [max_eq_right (by linarith)]
              simp
          have hkey : ∀ (i : Fin (m + 1)) (u : Fin (m + 1) → ℝ),
              errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
                = ENNReal.ofReal (lam i) * ∫⁻ w in Set.Iic (u i),
                    ENNReal.ofReal (Real.exp (-(∑ k, lam k * max (u k - w) 0))) := by
            intro i u
            set H : ℝ → ℝ := fun w => Real.exp (-(∑ k, lam k * max (u k - w) 0)) with hH
            have hHc : Continuous H := by
              simp only [hH]; fun_prop
            show _ = ENNReal.ofReal (lam i) * ∫⁻ w in Set.Iic (u i), ENNReal.ofReal (H w)
            have hmp := measurePreserving_piFinSuccAbove (fun k => expMeasure (lam k)) i
            set B : Set (ℝ × (Fin m → ℝ)) :=
              {p | ∀ j, u (i.succAbove j) - p.2 j ≤ u i - p.1} with hB
            have hBm : MeasurableSet B := by
              simp only [hB, Set.setOf_forall]
              exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
            have hA : {z : Fin (m + 1) → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
                = (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' B := by
              ext z
              simp only [Set.mem_setOf_eq, Set.mem_preimage, hB, MeasurableEquiv.piFinSuccAbove_apply]
              rw [Fin.forall_iff_succAbove i]
              simp [Fin.succAbove_ne]
              exact Iff.rfl
            have h1 : errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
                = ((expMeasure (lam i)).prod (Measure.pi fun j => expMeasure (lam (i.succAbove j)))) B := by
              rw [hA, errorLaw]
              exact hmp.measure_preimage hBm.nullMeasurableSet
            rw [h1, Measure.prod_apply hBm]
            have hsec : ∀ t : ℝ, Prod.mk t ⁻¹' B
                = Set.univ.pi (fun j => Set.Ici (u (i.succAbove j) - u i + t)) := by
              intro t; ext y
              simp only [hB, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
                Set.mem_Ici]
              constructor
              · intro h j; linarith [h j]
              · intro h j; linarith [h j]
            have hF : ∀ t : ℝ, (Measure.pi fun j => expMeasure (lam (i.succAbove j))) (Prod.mk t ⁻¹' B)
                = ∏ j, ENNReal.ofReal (Real.exp (-(lam (i.succAbove j) *
                    max (u (i.succAbove j) - u i + t) 0))) := by
              intro t
              rw [hsec, Measure.pi_pi]
              exact Finset.prod_congr rfl fun j _ => hS _ (hlam _) _
            simp_rw [hF]
            have hmeasF : Measurable fun t : ℝ => ∏ j, ENNReal.ofReal (Real.exp (-(lam (i.succAbove j) *
                    max (u (i.succAbove j) - u i + t) 0))) := by
              apply Finset.measurable_prod
              intro j _
              apply ENNReal.measurable_ofReal.comp
              apply Continuous.measurable
              fun_prop
            rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
              (show Measurable (gammaPDF 1 (lam i)) from
                (measurable_gammaPDFReal 1 (lam i)).ennreal_ofReal) hmeasF]
            have hind : Measurable ((Set.Iic (u i)).indicator fun w => ENNReal.ofReal (H w)) :=
              (ENNReal.measurable_ofReal.comp hHc.measurable).indicator measurableSet_Iic
            calc ∫⁻ t, (gammaPDF 1 (lam i) * fun t => ∏ j, ENNReal.ofReal (Real.exp (-(lam (i.succAbove j) *
                    max (u (i.succAbove j) - u i + t) 0)))) t
                = ∫⁻ t, ENNReal.ofReal (lam i) *
                    (Set.Iic (u i)).indicator (fun w => ENNReal.ofReal (H w)) (u i - t) := by
                  apply lintegral_congr
                  intro t
                  show exponentialPDF (lam i) t * _ = _
                  rcases le_or_gt 0 t with ht | ht
                  · rw [exponentialPDF_of_nonneg ht, Set.indicator_of_mem (by simp [ht])]
                    beta_reduce
                    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
                      ← ENNReal.ofReal_mul (by have := hlam i; positivity),
                      ← ENNReal.ofReal_mul (hlam i).le]
                    congr 1
                    rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
                    simp only [hH]
                    congr 2
                    rw [Fin.sum_univ_succAbove _ i]
                    have e1 : ∀ k, u k - (u i - t) = u k - u i + t := fun k => by ring
                    simp only [e1, sub_self, zero_add, max_eq_left ht]
                    rw [neg_add, ← Finset.sum_neg_distrib]
                  · rw [exponentialPDF_of_neg ht, Set.indicator_of_notMem (by simp; linarith)]
                    simp
              _ = ENNReal.ofReal (lam i) * ∫⁻ w in Set.Iic (u i), ENNReal.ofReal (H w) := by
                  rw [lintegral_const_mul _ (show Measurable fun t => (Set.Iic (u i)).indicator
                      (fun w => ENNReal.ofReal (H w)) (u i - t) from hind.comp (measurable_const.sub measurable_id)),
                    lintegral_sub_left_eq_self (fun w => (Set.Iic (u i)).indicator
                      (fun w => ENNReal.ofReal (H w)) w) (u i),
                    lintegral_indicator measurableSet_Iic]
          -- the kernel d(a,t)
          obtain ⟨dd, hdd⟩ : ∃ dd : ℝ → ℝ → ℝ, ∀ a t, dd a t = max (a + t) 0 - max a 0 :=
            ⟨_, fun _ _ => rfl⟩
          have hd0 : ∀ a t, 0 ≤ t → 0 ≤ dd a t := by
            intro a t ht; rw [hdd]; simp only [max_def]; split_ifs <;> linarith
          have hdt : ∀ a t, 0 ≤ t → dd a t ≤ t := by
            intro a t ht; rw [hdd]; simp only [max_def]; split_ifs <;> linarith
          have hdeq : ∀ a t, 0 ≤ a → 0 ≤ t → dd a t = t := by
            intro a t ha ht; rw [hdd]; simp only [max_def]; split_ifs <;> linarith
          have hdmono : ∀ a b t, b ≤ a → 0 ≤ t → dd b t ≤ dd a t := by
            intro a b t hab ht; rw [hdd, hdd]; simp only [max_def]; split_ifs <;> linarith
          have hdstrict : ∀ a b t, b < a → b < 0 → 0 < b + t → dd b t < dd a t := by
            intro a b t hab hb ht; rw [hdd, hdd]; simp only [max_def]; split_ifs <;> linarith
          have hdpos : ∀ a t, 0 < t → 0 < a + t → 0 < dd a t := by
            intro a t ht hat; rw [hdd]; simp only [max_def]; split_ifs <;> linarith
          -- the integrand and R
          obtain ⟨Ig, hIg⟩ : ∃ Ig : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ → ℝ,
              ∀ v j t, Ig v j t = Real.exp (-(∑ k, lam k * dd (v k - v j) t)) := ⟨_, fun _ _ _ => rfl⟩
          obtain ⟨R, hR⟩ : ∃ R : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ,
              ∀ v j, R v j = ∫ t in Set.Ioi 0, Ig v j t := ⟨_, fun _ _ => rfl⟩
          have hLt : Ltot lam = ∑ k, lam k := rfl
          have hIgc : ∀ v j, Continuous (Ig v j) := by
            intro v j
            have : Ig v j = fun t => Real.exp (-(∑ k, lam k * (max (v k - v j + t) 0 - max (v k - v j) 0))) :=
              funext fun t => by rw [hIg]; simp only [hdd]
            rw [this]; fun_prop
          have hIgpos : ∀ v j t, 0 < Ig v j t := fun v j t => by rw [hIg]; exact Real.exp_pos _
          have hsumlow : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (t : ℝ), 0 ≤ t → lam j * t ≤ ∑ k, lam k * dd (v k - v j) t := by
            intro v j t ht
            have := Finset.single_le_sum (f := fun k => lam k * dd (v k - v j) t)
              (fun k _ => mul_nonneg (hlam k).le (hd0 _ _ ht)) (Finset.mem_univ j)
            simp only [sub_self] at this
            rwa [hdeq 0 t le_rfl ht] at this
          have hsumup : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (t : ℝ), 0 ≤ t → ∑ k, lam k * dd (v k - v j) t ≤ Ltot lam * t := by
            intro v j t ht
            rw [hLt, Finset.sum_mul]
            exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hdt _ _ ht) (hlam k).le
          have hIgup : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (t : ℝ), 0 ≤ t → Ig v j t ≤ Real.exp (-lam j * t) := by
            intro v j t ht
            rw [hIg]; apply Real.exp_le_exp.2; linarith [hsumlow v j t ht]
          have hIglow : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (t : ℝ), 0 ≤ t → Real.exp (-Ltot lam * t) ≤ Ig v j t := by
            intro v j t ht
            rw [hIg]; apply Real.exp_le_exp.2; linarith [hsumup v j t ht]
          have hIgint : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)), IntegrableOn (Ig v j) (Set.Ioi 0) := by
            intro v j
            refine (exp_neg_integrableOn_Ioi 0 (hlam j)).mono' (hIgc v j).aestronglyMeasurable ?_
            refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
            rw [Real.norm_eq_abs, abs_of_pos (hIgpos v j t)]
            exact hIgup v j t (le_of_lt ht)
          haveI : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.2 hn
          have hstrict : ∀ (f g : ℝ → ℝ) (c : ℝ), 0 ≤ c → IntegrableOn f (Set.Ioi 0) →
              IntegrableOn g (Set.Ioi 0) → (∀ t, 0 < t → f t ≤ g t) → (∀ t, c < t → f t < g t) →
              ∫ t in Set.Ioi 0, f t < ∫ t in Set.Ioi 0, g t := by
            intro f g c hc hf hg hle hlt
            rw [← sub_pos, ← integral_sub hg hf]
            rw [setIntegral_pos_iff_support_of_nonneg_ae (f := fun a => g a - f a) _ (hg.sub hf)]
            · calc (0 : ENNReal) < volume (Set.Ioi c) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
                _ ≤ volume (Function.support (fun a => g a - f a) ∩ Set.Ioi 0) := measure_mono fun t ht => ⟨by
                      simp only [Function.mem_support]; exact (sub_pos.2 (hlt t ht)).ne',
                    lt_of_le_of_lt hc ht⟩
            · exact (ae_restrict_iff' measurableSet_Ioi).2
                (Filter.Eventually.of_forall fun t ht => sub_nonneg.2 (hle t ht))
          have hexpint : ∀ b : ℝ, 0 < b → ∫ t in Set.Ioi (0:ℝ), Real.exp (-b * t) = 1 / b := by
            intro b hb
            have := integral_exp_mul_Ioi (a := -b) (by linarith) 0
            rw [this, mul_zero, Real.exp_zero, neg_div_neg_eq]
          have hLpos : 0 < Ltot lam := by
            rw [hLt]; exact Finset.sum_pos (fun k _ => hlam k) Finset.univ_nonempty
          have hLi : 0 < Ltot lam - lam i := by
            obtain ⟨k, hk⟩ := exists_ne i
            have h1 := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ i)
            have h2 := Finset.single_le_sum (s := Finset.univ.erase i) (f := lam)
              (fun k' _ => (hlam k').le) (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
            have := hlam k
            rw [hLt]; linarith
          have hRlow : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)), 1 / Ltot lam ≤ R v j := by
            intro v j; rw [hR, ← hexpint _ hLpos]
            exact setIntegral_mono_on (exp_neg_integrableOn_Ioi 0 hLpos) (hIgint v j) measurableSet_Ioi
              (fun t ht => hIglow v j t (le_of_lt ht))
          have hRpos : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)), 0 < R v j := fun v j =>
            lt_of_lt_of_le (by positivity) (hRlow v j)
          have hRup : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)), R v j < 1 / lam j := by
            intro v j
            obtain ⟨k, hk⟩ := exists_ne j
            rw [hR, ← hexpint _ (hlam j)]
            apply hstrict _ _ (max (v j - v k) 0) (le_max_right _ _) (hIgint v j)
              (exp_neg_integrableOn_Ioi 0 (hlam j)) (fun t ht => hIgup v j t ht.le)
            intro t ht
            have ht0 : 0 < t := lt_of_le_of_lt (le_max_right _ _) ht
            have hkt : 0 < (v k - v j) + t := by have := le_max_left (v j - v k) 0; linarith
            rw [hIg]; apply Real.exp_lt_exp.2
            have h1 := Finset.add_sum_erase Finset.univ (fun k' => lam k' * dd (v k' - v j) t)
              (Finset.mem_univ j)
            have h2 := Finset.single_le_sum (s := Finset.univ.erase j)
              (f := fun k' => lam k' * dd (v k' - v j) t)
              (fun k' _ => mul_nonneg (hlam k').le (hd0 _ _ ht0.le)) (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
            have h3 := mul_pos (hlam k) (hdpos _ _ ht0 hkt)
            simp only [sub_self, hdeq 0 t le_rfl ht0.le] at h1
            nlinarith
          have hRlt1 : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)), lam j * R v j < 1 := by
            intro v j; have := hRup v j; rw [lt_div_iff₀ (hlam j)] at this; linarith
          have hRcont : ∀ j : Fin (m + 1), Continuous (fun v => R v j) := by
            intro j
            have : (fun v => R v j) = fun v => ∫ t in Set.Ioi 0, Ig v j t := funext fun v => hR v j
            rw [this]
            refine continuous_of_dominated (bound := fun t => Real.exp (-lam j * t))
              (fun v => (hIgc v j).aestronglyMeasurable) (fun v => ?_)
              (exp_neg_integrableOn_Ioi 0 (hlam j)) (Filter.Eventually.of_forall fun t => ?_)
            · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
                rw [Real.norm_eq_abs, abs_of_pos (hIgpos v j t)]; exact hIgup v j t (le_of_lt ht))
            · have : (fun v => Ig v j t) = fun v : Fin (m + 1) → ℝ =>
                  Real.exp (-(∑ k, lam k * (max (v k - v j + t) 0 - max (v k - v j) 0))) :=
                funext fun v => by rw [hIg]; simp only [hdd]
              rw [this]; fun_prop
          have hsumle : ∀ (u : Fin (m + 1) → ℝ) (x y t : ℝ), x ≤ y → 0 ≤ t →
              ∑ k, lam k * dd (Function.update u i y k - Function.update u i y i) t ≤
                ∑ k, lam k * dd (Function.update u i x k - Function.update u i x i) t := by
            intro u x y t hxy ht
            apply Finset.sum_le_sum; intro k _
            apply mul_le_mul_of_nonneg_left _ (hlam k).le
            by_cases hk : k = i
            · rw [hk]; simp
            · simp only [Function.update_self, Function.update_of_ne hk]
              exact hdmono _ _ _ (by linarith) ht
          have hRmono : ∀ (u : Fin (m + 1) → ℝ) (x y : ℝ), x ≤ y →
              R (Function.update u i x) i ≤ R (Function.update u i y) i := by
            intro u x y hxy
            rw [hR, hR]
            refine setIntegral_mono_on (hIgint _ _) (hIgint _ _) measurableSet_Ioi fun t ht => ?_
            rw [hIg, hIg]; apply Real.exp_le_exp.2; apply neg_le_neg
            exact hsumle u x y t hxy (le_of_lt ht)
          have hRsmono : ∀ (u : Fin (m + 1) → ℝ) (x y : ℝ) (j : Fin (m + 1)), j ≠ i → u j < y → x < y →
              R (Function.update u i x) i < R (Function.update u i y) i := by
            intro u x y j hj hjy hxy
            rw [hR, hR]
            apply hstrict _ _ (y - u j) (by linarith) (hIgint _ _) (hIgint _ _)
            · intro t ht
              rw [hIg, hIg]; apply Real.exp_le_exp.2; apply neg_le_neg
              exact hsumle u x y t hxy.le (le_of_lt ht)
            · intro t ht
              have ht0 : 0 < t := by linarith
              rw [hIg, hIg]; apply Real.exp_lt_exp.2; apply neg_lt_neg
              apply Finset.sum_lt_sum
              · intro k _
                apply mul_le_mul_of_nonneg_left _ (hlam k).le
                by_cases hk : k = i
                · rw [hk]; simp
                · simp only [Function.update_self, Function.update_of_ne hk]
                  exact hdmono _ _ _ (by linarith) ht0.le
              · refine ⟨j, Finset.mem_univ j, ?_⟩
                simp only [Function.update_self, Function.update_of_ne hj]
                exact mul_lt_mul_of_pos_left (hdstrict _ _ _ (by linarith) (by linarith) (by linarith))
                  (hlam j)
          have hRmin : ∀ (u : Fin (m + 1) → ℝ) (x : ℝ), (∀ j, j ≠ i → x ≤ u j) →
              R (Function.update u i x) i = 1 / Ltot lam := by
            intro u x hx
            rw [hR, ← hexpint _ hLpos]
            refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
            rw [hIg]; congr 1
            rw [neg_mul, hLt, Finset.sum_mul]; congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            congr 1
            by_cases hk : k = i
            · rw [hk]; simp only [Function.update_self, sub_self]; exact hdeq 0 t le_rfl (le_of_lt ht)
            · simp only [Function.update_self, Function.update_of_ne hk]
              exact hdeq _ _ (by linarith [hx k hk]) (le_of_lt ht)
          have hτ : ∀ (j : Fin (m + 1)) (v : Fin (m + 1) → ℝ), tau v lam j = R v j / (1 - lam j * R v j) := by
            intro j v
            obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, ∀ w, E w = Real.exp (lam j * w -
                ∑ k ∈ Finset.univ.erase j, lam k * max (v k - w) 0) := ⟨_, fun _ => rfl⟩
            have hEc : Continuous E := by
              have : E = fun w => Real.exp (lam j * w -
                  ∑ k ∈ Finset.univ.erase j, lam k * max (v k - w) 0) := funext hE
              rw [this]; fun_prop
            have hEpos : ∀ w, 0 < E w := fun w => by rw [hE]; exact Real.exp_pos _
            have hEint : ∀ a, IntegrableOn E (Set.Iic a) := by
              intro a
              refine (integrableOn_exp_mul_Iic (hlam j) a).mono' hEc.aestronglyMeasurable
                (Filter.Eventually.of_forall fun w => ?_)
              rw [Real.norm_eq_abs, abs_of_pos (hEpos w), hE]
              apply Real.exp_le_exp.2
              have : 0 ≤ ∑ k ∈ Finset.univ.erase j, lam k * max (v k - w) 0 :=
                Finset.sum_nonneg fun k _ => mul_nonneg (hlam k).le (le_max_right _ _)
              linarith
            obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ x, F x = ∫ w in Set.Iic x, E w := ⟨_, fun _ => rfl⟩
            have hFd : ∀ x, HasDerivAt F (E x) x := by
              intro x
              have : F = fun y => F 0 + ∫ w in (0:ℝ)..y, E w := funext fun y => by
                rw [hF, hF, ← intervalIntegral.integral_Iic_sub_Iic (hEint 0) (hEint y)]; ring
              rw [this]
              exact ((hEc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _
            have hQ : ∀ x, choiceProb (Function.update v j x) lam j =
                lam j * (Real.exp (-(lam j * x)) * F x) := by
              intro x
              rw [choiceProb, hkey, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hlam j).le,
                Function.update_self]
              congr 1
              rw [← integral_eq_lintegral_of_nonneg_ae
                (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
                (by apply Continuous.aestronglyMeasurable; fun_prop)]
              rw [hF, ← integral_const_mul]
              refine setIntegral_congr_fun measurableSet_Iic fun w hw => ?_
              rw [hE, ← Real.exp_add]; congr 1
              have h1 := Finset.add_sum_erase Finset.univ
                (fun k => lam k * max (Function.update v j x k - w) 0) (Finset.mem_univ j)
              have hs : ∑ k ∈ Finset.univ.erase j, lam k * max (Function.update v j x k - w) 0 =
                  ∑ k ∈ Finset.univ.erase j, lam k * max (v k - w) 0 :=
                Finset.sum_congr rfl fun k hk => by
                  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
              simp only [Function.update_self, max_eq_left (sub_nonneg.2 (Set.mem_Iic.1 hw))] at h1
              rw [hs] at h1
              linear_combination h1
            have hderiv : partialU (fun w => choiceProb w lam j) j v =
                lam j * (Real.exp (-(lam j * v j)) * (E (v j) - lam j * F (v j))) := by
              unfold partialU
              have : (fun t => choiceProb (Function.update v j t) lam j) =
                  fun t => lam j * (Real.exp (-(lam j * t)) * F t) := funext hQ
              simp only [this]
              apply HasDerivAt.deriv
              have h1 : HasDerivAt (fun t => Real.exp (-(lam j * t)))
                  (Real.exp (-(lam j * v j)) * (-(lam j * 1))) (v j) :=
                ((hasDerivAt_id' (v j)).const_mul (lam j)).neg.exp
              exact ((h1.mul (hFd (v j))).const_mul (lam j)).congr_deriv (by ring)
            have hFR : F (v j) = E (v j) * R v j := by
              have s1 : ∫ t in Set.Ioi (0:ℝ), E (v j - t) = ∫ s in Set.Iic (0:ℝ), E (v j + s) := by
                have := integral_comp_neg_Ioi (0:ℝ) (fun s => E (v j + s))
                rw [neg_zero] at this
                rw [← this]; simp only [sub_eq_add_neg]
              have s2 : ∫ s in Set.Iic (0:ℝ), E (v j + s) = ∫ w in Set.Iic (v j), E w := by
                rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic,
                  ← integral_add_right_eq_self (fun w => (Set.Iic (v j)).indicator E w) (v j)]
                congr 1; funext s
                by_cases hs : s ≤ 0
                · rw [Set.indicator_of_mem (Set.mem_Iic.2 hs),
                    Set.indicator_of_mem (Set.mem_Iic.2 (by linarith)), add_comm]
                · rw [Set.indicator_of_notMem (by simpa using hs),
                    Set.indicator_of_notMem (by simp; linarith)]
              rw [hF, ← s2, ← s1, hR, ← integral_const_mul]
              refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
              have ht0 : (0:ℝ) ≤ t := le_of_lt ht
              rw [hE, hE, hIg, ← Real.exp_add]; congr 1
              have h1 := Finset.add_sum_erase Finset.univ (fun k => lam k * dd (v k - v j) t)
                (Finset.mem_univ j)
              simp only [sub_self, hdeq 0 t le_rfl ht0] at h1
              have hs : ∑ k ∈ Finset.univ.erase j, lam k * dd (v k - v j) t =
                  ∑ k ∈ Finset.univ.erase j, lam k * max (v k - (v j - t)) 0 -
                    ∑ k ∈ Finset.univ.erase j, lam k * max (v k - v j) 0 := by
                rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
                rw [hdd, ← mul_sub]; congr 3; ring
              rw [hs] at h1
              linear_combination -h1
            have hv : choiceProb v lam j = lam j * (Real.exp (-(lam j * v j)) * F (v j)) := by
              have := hQ (v j); rwa [Function.update_eq_self] at this
            rw [tau, hderiv, hv, hFR]
            have hE0 := hEpos (v j)
            have hl := hlam j
            have he := Real.exp_pos (-(lam j * v j))
            rw [show E (v j) - lam j * (E (v j) * R v j) = E (v j) * (1 - lam j * R v j) by ring]
            rw [mul_div_mul_left _ _ hl.ne', mul_div_mul_left _ _ he.ne', mul_div_mul_left _ _ hE0.ne']
          have hφ : ∀ r s : ℝ, 0 < r → r ≤ s → lam i * s < 1 →
              r / (1 - lam i * r) ≤ s / (1 - lam i * s) := by
            intro r s hr hrs hs
            have h1 : 0 < 1 - lam i * s := by linarith
            have h2 : 0 < 1 - lam i * r := by nlinarith [hlam i]
            rw [div_le_div_iff₀ h2 h1]; nlinarith [hlam i]
          have hφs : ∀ r s : ℝ, 0 < r → r < s → lam i * s < 1 →
              r / (1 - lam i * r) < s / (1 - lam i * s) := by
            intro r s hr hrs hs
            have h1 : 0 < 1 - lam i * s := by linarith
            have h2 : 0 < 1 - lam i * r := by nlinarith [hlam i]
            rw [div_lt_div_iff₀ h2 h1]; nlinarith [hlam i]
          have hτpos : ∀ (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)), 0 < tau v lam j := by
            intro v j; rw [hτ]; exact div_pos (hRpos v j) (by linarith [hRlt1 v j])
          have hval : 1 / Ltot lam / (1 - lam i * (1 / Ltot lam)) = 1 / (Ltot lam - lam i) := by
            field_simp
          have hcont : Continuous (fun u => tau u lam i) := by
            have : (fun u => tau u lam i) = fun u => R u i / (1 - lam i * R u i) :=
              funext fun u => hτ i u
            rw [this]
            exact (hRcont i).div (continuous_const.sub (continuous_const.mul (hRcont i)))
              fun u => ne_of_gt (by linarith [hRlt1 u i])
          have hlow : ∀ (u : Fin (m + 1) → ℝ) (x : ℝ),
              1 / (Ltot lam - lam i) ≤ tau (Function.update u i x) lam i := by
            intro u x; rw [hτ, ← hval]; exact hφ _ _ (by positivity) (hRlow _ _) (hRlt1 _ _)
          have hmin : ∀ (u : Fin (m + 1) → ℝ) (x : ℝ), (∀ j, j ≠ i → x ≤ u j) →
              tau (Function.update u i x) lam i = 1 / (Ltot lam - lam i) := by
            intro u x hx; rw [hτ, hRmin u x hx, hval]
          have hmono : ∀ (u : Fin (m + 1) → ℝ) (x y : ℝ), x ≤ y →
              tau (Function.update u i x) lam i ≤ tau (Function.update u i y) lam i := by
            intro u x y hxy; rw [hτ, hτ]
            exact hφ _ _ (hRpos _ _) (hRmono u x y hxy) (hRlt1 _ _)
          have hsm : ∀ u : Fin (m + 1) → ℝ, StrictMonoOn (fun x => tau (Function.update u i x) lam i)
              {x | (∃ j, j ≠ i ∧ u j < x) ∧ x ≤ α i} := by
            intro u x _ y hy hxy
            obtain ⟨⟨j, hj, hjy⟩, _⟩ := hy
            show tau (Function.update u i x) lam i < tau (Function.update u i y) lam i
            rw [hτ, hτ]
            exact hφs _ _ (hRpos _ _) (hRsmono u x y j hj hjy hxy) (hRlt1 _ _)
          have hgc : ∀ u : Fin (m + 1) → ℝ, Continuous fun x => tau (Function.update u i x) lam i :=
            fun u => hcont.comp (continuous_const.update i continuous_id)
          have hb : ∀ u : Fin (m + 1) → ℝ,
              (∃! x : ℝ, α i - x = tau (Function.update u i x) lam i) ∧
                ∃! x : ℝ, x ≤ α i ∧ α i - x = tau (Function.update u i x) lam i := by
            intro u
            have hex : ∃ x, α i - x = tau (Function.update u i x) lam i := by
              set x0 := min (α i - 1 / (Ltot lam - lam i)) (-(∑ k, |u k|)) with hx0def
              have hx0 : ∀ j, j ≠ i → x0 ≤ u j := fun j _ => by
                have h1 : |u j| ≤ ∑ k, |u k| :=
                  Finset.single_le_sum (f := fun k => |u k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
                have := min_le_right (α i - 1 / (Ltot lam - lam i)) (-(∑ k, |u k|))
                have := neg_abs_le (u j)
                linarith
              have hpos : 0 < 1 / (Ltot lam - lam i) := by positivity
              have hm1 := min_le_left (α i - 1 / (Ltot lam - lam i)) (-(∑ k, |u k|))
              have hle : x0 ≤ α i := by linarith
              have hc : ContinuousOn (fun x => α i - x - tau (Function.update u i x) lam i)
                  (Set.Icc x0 (α i)) :=
                ((continuous_const.sub continuous_id).sub (hgc u)).continuousOn
              have hA : α i - α i - tau (Function.update u i (α i)) lam i ≤ 0 := by
                linarith [hτpos (Function.update u i (α i)) i]
              have hB : 0 ≤ α i - x0 - tau (Function.update u i x0) lam i := by
                rw [hmin u x0 hx0]; linarith
              obtain ⟨x, -, hx⟩ := intermediate_value_Icc' hle hc
                (show (0:ℝ) ∈ Set.Icc (α i - α i - tau (Function.update u i (α i)) lam i)
                  (α i - x0 - tau (Function.update u i x0) lam i) from ⟨hA, hB⟩)
              exact ⟨x, by simp only at hx; linarith⟩
            have huniq : ∀ x y, α i - x = tau (Function.update u i x) lam i →
                α i - y = tau (Function.update u i y) lam i → x = y := by
              intro x y hx hy
              rcases lt_trichotomy x y with h | h | h
              · have := hmono u x y h.le; linarith
              · exact h
              · have := hmono u y x h.le; linarith
            obtain ⟨x, hx⟩ := hex
            refine ⟨⟨x, hx, fun y hy => huniq y x hy hx⟩, ⟨x, ⟨?_, hx⟩, fun y hy => huniq y x hy.2 hx⟩⟩
            linarith [hτpos (Function.update u i x) i]
          have hc : ∀ u v : Fin (m + 1) → ℝ, v i = u i → (∀ j, u j < u i → v j = u j) →
              (∀ j, j ≠ i → u i ≤ u j → u i ≤ v j) → tau v lam i = tau u lam i := by
            intro u v hvi hlt hge
            rw [hτ, hτ]
            have : R v i = R u i := by
              rw [hR, hR]; refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
              rw [hIg, hIg]; congr 2; refine Finset.sum_congr rfl fun k _ => ?_; congr 1
              rcases lt_or_ge (u k) (u i) with hk | hk
              · rw [hlt k hk, hvi]
              · by_cases hki : k = i
                · rw [hki, sub_self, sub_self]
                · rw [hdeq _ _ (by linarith [hge k hki hk]) (le_of_lt ht),
                    hdeq _ _ (by linarith) (le_of_lt ht)]
            rw [this]
          have hd : ∀ (u : Fin (m + 1) → ℝ) (j : Fin (m + 1)), j ≠ i → u i = u j →
              (tau u lam i ≤ tau u lam j ↔ lam i ≤ lam j) ∧
                (tau u lam i < tau u lam j ↔ lam i < lam j) := by
            intro u j hj hij
            have hRe : R u i = R u j := by rw [hR, hR]; simp only [hIg, hij]
            rw [hτ, hτ, ← hRe]
            have hr := hRpos u i
            have h1 := hRlt1 u i
            have h2 := hRlt1 u j
            rw [← hRe] at h2
            constructor
            · rw [div_le_div_iff_of_pos_left hr (by linarith) (by linarith)]
              constructor <;> intro h <;> nlinarith
            · rw [div_lt_div_iff_of_pos_left hr (by linarith) (by linarith)]
              constructor <;> intro h <;> nlinarith
          exact ⟨⟨fun u => hτpos u i, hcont, hmin, hlow, hsm⟩, hb, hc, hd⟩
