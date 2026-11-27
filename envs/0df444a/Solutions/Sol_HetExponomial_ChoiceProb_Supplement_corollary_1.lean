-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:29.928893+00:00
-- url     : https://prove2.me/submissions/64bf043e-4854-4323-bc71-1ea98b703276

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i j : Fin n) :
    (choiceProb u lam i / lam i < choiceProb u lam j / lam j ↔ u i < u j) ∧
      (choiceProb u lam i / lam i = choiceProb u lam j / lam j ↔ u i = u j) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hP : ∀ k, IsProbabilityMeasure (expMeasure (lam k)) :=
          fun k => isProbabilityMeasure_expMeasure (hlam k)
        -- survival function of the exponential law
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
        set H : ℝ → ℝ := fun w => Real.exp (-(∑ k, lam k * max (u k - w) 0)) with hH
        have hHc : Continuous H := by
          simp only [hH]; fun_prop
        set Ψ : ℝ → ENNReal := fun a => ∫⁻ w in Set.Iic a, ENNReal.ofReal (H w) with hΨ
        have key : ∀ i : Fin (m + 1), errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
            = ENNReal.ofReal (lam i) * Ψ (u i) := by
          intro i
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
            _ = ENNReal.ofReal (lam i) * Ψ (u i) := by
                rw [lintegral_const_mul _ (show Measurable fun t => (Set.Iic (u i)).indicator
                    (fun w => ENNReal.ofReal (H w)) (u i - t) from hind.comp (measurable_const.sub measurable_id)),
                  lintegral_sub_left_eq_self (fun w => (Set.Iic (u i)).indicator
                    (fun w => ENNReal.ofReal (H w)) w) (u i),
                  lintegral_indicator measurableSet_Iic]
        have hfin : ∀ k : Fin (m + 1), Ψ (u k) ≠ ⊤ := by
          intro k htop
          have h := key k
          rw [htop, ENNReal.mul_top (by simpa using hlam k)] at h
          haveI : IsProbabilityMeasure (errorLaw lam) := by
            unfold errorLaw; infer_instance
          exact measure_ne_top (errorLaw lam) _ h
        have hq : ∀ k : Fin (m + 1), choiceProb u lam k / lam k = (Ψ (u k)).toReal := by
          intro k
          rw [choiceProb, key k, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hlam k).le]
          field_simp [(hlam k).ne']
        have hmono : ∀ a b : ℝ, a < b → Ψ a ≠ ⊤ → Ψ a < Ψ b := by
          intro a b hab ha
          have hsplit : Ψ b = Ψ a + ∫⁻ w in Set.Ioc a b, ENNReal.ofReal (H w) := by
            simp only [hΨ]
            rw [← lintegral_union measurableSet_Ioc (Set.Iic_disjoint_Ioc le_rfl),
              Set.Iic_union_Ioc_eq_Iic hab.le]
          rw [hsplit]
          apply ENNReal.lt_add_right ha
          intro h0
          rw [lintegral_eq_zero_iff (show Measurable fun w => ENNReal.ofReal (H w) from
            ENNReal.measurable_ofReal.comp hHc.measurable)] at h0
          rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h0
          have hvol : volume (Set.Ioc a b) = 0 := by
            rw [measure_eq_zero_iff_ae_notMem]
            filter_upwards [h0] with x hx hxs
            have := hx hxs
            simp only [Function.comp_apply, Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
            have hpos : 0 < H x := Real.exp_pos _
            linarith
          rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hvol
          linarith
        have hlt : ∀ a b : Fin (m + 1), u a < u b →
            choiceProb u lam a / lam a < choiceProb u lam b / lam b := by
          intro a b hab
          rw [hq, hq]
          exact ENNReal.toReal_strict_mono (hfin b) (hmono _ _ hab (hfin a))
        have heq : ∀ a b : Fin (m + 1), u a = u b →
            choiceProb u lam a / lam a = choiceProb u lam b / lam b := by
          intro a b hab
          rw [hq, hq, hab]
        refine ⟨⟨fun h => ?_, hlt i j⟩, ⟨fun h => ?_, heq i j⟩⟩
        · by_contra hc
          rcases lt_or_eq_of_le (not_lt.1 hc) with h' | h'
          · exact lt_asymm h (hlt j i h')
          · rw [heq j i h'] at h; exact lt_irrefl _ h
        · rcases lt_trichotomy (u i) (u j) with h' | h' | h'
          · exact absurd h (ne_of_lt (hlt i j h'))
          · exact h'
          · exact absurd h (ne_of_gt (hlt j i h'))
