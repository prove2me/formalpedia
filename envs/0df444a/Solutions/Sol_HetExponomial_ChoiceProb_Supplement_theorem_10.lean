-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:23.144627+00:00
-- url     : https://prove2.me/submissions/676dbf5f-9c23-45b3-bc9f-410d2f45811e

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) :
    (∃ (σ : Fin n ≃ Fin n) (ustar : Fin n → ℝ), IsGeneralRun α lam σ ustar) ∧
      ∀ (σ : Fin n ≃ Fin n) (ustar : Fin n → ℝ), IsGeneralRun α lam σ ustar →
        (∀ s : Fin n, 0 < s.val → ∀ i, i ∉ solvedBefore σ s.val →
            ∃! x : ℝ, α i - x = tauCond α lam (solvedBefore σ s.val) ustar i x) ∧
          IsPriceNE α β lam (eqPrices α β ustar) ∧
          ∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar := by
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
            have hQreal : ∀ (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)), choiceProb u lam i =
                lam i * ∫ w in Set.Iic (u i), Real.exp (-(∑ k, lam k * max (u k - w) 0)) := by
              intro u
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
              intro i
              rw [choiceProb, key i, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hlam i).le,
                integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)
                  hHc.aestronglyMeasurable]
            obtain ⟨T, htau, hpos, hanti, hconst, hcont, hmax⟩ :
                ∃ T : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ,
                  (∀ v i, tau v lam i = T i (fun j => v j - v i)) ∧
                  (∀ i w, 0 < T i w) ∧
                  (∀ i w w', (∀ j, j ≠ i → min (w j) 0 ≤ min (w' j) 0) → T i w' ≤ T i w) ∧
                  (∀ i w, (∀ j, j ≠ i → 0 ≤ w j) → T i w = 1 / (Ltot lam - lam i)) ∧
                  (∀ i (v : Fin (m + 1) → ℝ), Continuous (fun x : ℝ => T i (fun j => v j - x))) ∧
                  (∀ i (u : Fin (m + 1) → ℝ) (x0 : ℝ), α i - x0 = T i (fun j => u j - x0) →
                    ∀ x, x ≠ x0 → (α i - x) * choiceProb (Function.update u i x) lam i <
                      (α i - x0) * choiceProb (Function.update u i x0) lam i) := by
              -- the kernel
              set E : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ → ℝ := fun i w z =>
                Real.exp (-(∑ k ∈ Finset.univ.erase i, lam k * max (z + min (w k) 0) 0)) with hE
              set K : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ := fun i w =>
                ∫ z in Set.Ioi (0:ℝ), lam i * Real.exp (-lam i * z) * E i w z with hK
              set Hf : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ → ℝ := fun i u w =>
                Real.exp (-(∑ k ∈ Finset.univ.erase i, lam k * max (u k - w) 0)) with hHf
              have hEc : ∀ i w, Continuous (E i w) := by
                intro i w; simp only [hE]; fun_prop
              have hHfc : ∀ i u, Continuous (Hf i u) := by
                intro i u; simp only [hHf]; fun_prop
              have hE0 : ∀ i w z, 0 < E i w z := fun i w z => Real.exp_pos _
              have hH0 : ∀ i w z, 0 < Hf i w z := fun i w z => Real.exp_pos _
              have hE1 : ∀ i w z, E i w z ≤ 1 := by
                intro i w z
                simp only [hE]
                rw [Real.exp_le_one_iff, neg_nonpos]
                exact Finset.sum_nonneg fun k _ => mul_nonneg (hlam k).le (le_max_right _ _)
              have hH1 : ∀ i w z, Hf i w z ≤ 1 := by
                intro i w z
                simp only [hHf]
                rw [Real.exp_le_one_iff, neg_nonpos]
                exact Finset.sum_nonneg fun k _ => mul_nonneg (hlam k).le (le_max_right _ _)
              have hexpI : ∀ i, IntegrableOn (fun z : ℝ => lam i * Real.exp (-lam i * z)) (Set.Ioi 0) :=
                fun i => (exp_neg_integrableOn_Ioi 0 (hlam i)).const_mul _
              have hexp1 : ∀ i, ∫ z in Set.Ioi (0:ℝ), lam i * Real.exp (-lam i * z) = 1 := by
                intro i
                have := (hlam i).ne'
                rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [hlam i])]
                simp
                field_simp
              have hKI : ∀ i w, IntegrableOn (fun z : ℝ => lam i * Real.exp (-lam i * z) * E i w z)
                  (Set.Ioi 0) := by
                intro i w
                refine Integrable.mono' (hexpI i) ?_ ?_
                · have := hEc i w
                  exact Continuous.aestronglyMeasurable (by fun_prop)
                · refine Filter.Eventually.of_forall fun z => ?_
                  have h1 := hE1 i w z
                  have h0 := hE0 i w z
                  have h2 : 0 < lam i * Real.exp (-lam i * z) := mul_pos (hlam i) (Real.exp_pos _)
                  rw [Real.norm_eq_abs, abs_of_pos (mul_pos h2 h0)]
                  nlinarith
              have hK0 : ∀ i w, 0 < K i w := by
                intro i w
                simp only [hK]
                rw [setIntegral_pos_iff_support_of_nonneg_ae]
                · have : Function.support (fun z : ℝ => lam i * Real.exp (-lam i * z) * E i w z) = Set.univ := by
                    ext z
                    simp only [Function.mem_support, Set.mem_univ, iff_true]
                    exact (mul_pos (mul_pos (hlam i) (Real.exp_pos _)) (hE0 i w z)).ne'
                  rw [this]; simp
                · exact Filter.Eventually.of_forall fun z =>
                    (mul_pos (mul_pos (hlam i) (Real.exp_pos _)) (hE0 i w z)).le
                · exact hKI i w
              have hK1 : ∀ i w, K i w < 1 := by
                intro i w
                obtain ⟨j, hj⟩ : ∃ j : Fin (m + 1), j ≠ i := by
                  haveI : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.2 hn
                  exact exists_ne i
                rw [← sub_pos, ← hexp1 i]
                simp only [hK]
                rw [← integral_sub (hexpI i) (hKI i w), setIntegral_pos_iff_support_of_nonneg_ae]
                · refine lt_of_lt_of_le ?_ (measure_mono (s := Set.Ioi (max 0 (-min (w j) 0))) ?_)
                  · simp
                  · intro z hz
                    have hz0 : 0 < z := lt_of_le_of_lt (le_max_left (0:ℝ) (-min (w j) 0)) hz
                    have hz1 : 0 < z + min (w j) 0 := by
                      have := lt_of_le_of_lt (le_max_right (0:ℝ) (-min (w j) 0)) hz
                      linarith
                    refine ⟨?_, hz0⟩
                    rw [Function.mem_support]
                    have hlt : E i w z < 1 := by
                      simp only [hE]
                      rw [Real.exp_lt_one_iff, neg_lt_zero]
                      refine Finset.sum_pos' (fun k _ => mul_nonneg (hlam k).le (le_max_right _ _))
                        ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩, ?_⟩
                      exact mul_pos (hlam j) (lt_max_of_lt_left hz1)
                    have h2 : 0 < lam i * Real.exp (-lam i * z) := mul_pos (hlam i) (Real.exp_pos _)
                    have : 0 < lam i * Real.exp (-lam i * z) - lam i * Real.exp (-lam i * z) * E i w z := by
                      nlinarith
                    exact this.ne'
                · refine Filter.Eventually.of_forall fun z => ?_
                  have h2 : 0 < lam i * Real.exp (-lam i * z) := mul_pos (hlam i) (Real.exp_pos _)
                  have h1 := hE1 i w z
                  show 0 ≤ lam i * Real.exp (-lam i * z) - lam i * Real.exp (-lam i * z) * E i w z
                  nlinarith
                · exact (hexpI i).sub (hKI i w)
              have hKanti : ∀ i w w', (∀ j, j ≠ i → min (w j) 0 ≤ min (w' j) 0) → K i w' ≤ K i w := by
                intro i w w' h
                simp only [hK]
                refine setIntegral_mono (hKI i w') (hKI i w) fun z => ?_
                refine mul_le_mul_of_nonneg_left ?_ (mul_pos (hlam i) (Real.exp_pos _)).le
                simp only [hE]
                rw [Real.exp_le_exp, neg_le_neg_iff]
                refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hlam k).le
                have := h k (Finset.ne_of_mem_erase hk)
                exact max_le_max (by linarith) le_rfl
              have hLsum : ∀ i, Ltot lam - lam i = ∑ k ∈ Finset.univ.erase i, lam k := by
                intro i
                rw [Ltot, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
                ring
              have hLpos : ∀ i, 0 < Ltot lam - lam i := by
                intro i
                rw [hLsum]
                haveI : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.2 hn
                obtain ⟨j, hj⟩ := exists_ne i
                exact Finset.sum_pos (fun k _ => hlam k) ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩⟩
              have hKconst : ∀ i w, (∀ j, j ≠ i → 0 ≤ w j) → K i w = lam i / Ltot lam := by
                intro i w h
                have hL : 0 < Ltot lam := by linarith [hLpos i, hlam i]
                simp only [hK]
                have : Set.EqOn (fun z : ℝ => lam i * Real.exp (-lam i * z) * E i w z)
                    (fun z => lam i * Real.exp (-Ltot lam * z)) (Set.Ioi 0) := by
                  intro z hz
                  have hz : 0 < z := hz
                  simp only [hE]
                  have : ∑ k ∈ Finset.univ.erase i, lam k * max (z + min (w k) 0) 0
                      = (Ltot lam - lam i) * z := by
                    rw [hLsum, Finset.sum_mul]
                    refine Finset.sum_congr rfl fun k hk => ?_
                    rw [min_eq_right (h k (Finset.ne_of_mem_erase hk)), add_zero, max_eq_left hz.le]
                  rw [this, mul_assoc, ← Real.exp_add]
                  congr 2; ring
                rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
                  integral_exp_mul_Ioi (by linarith)]
                simp
                field_simp
              -- formula for Q
              have hQ0 : ∀ i (u : Fin (m + 1) → ℝ) (x : ℝ), choiceProb (Function.update u i x) lam i =
                  lam i * Real.exp (-(lam i * x)) * ∫ w in Set.Iic x, Real.exp (lam i * w) * Hf i u w := by
                intro i u x
                rw [hQreal, Function.update_self, mul_assoc, ← integral_const_mul (Real.exp (-(lam i * x)))]
                congr 1
                refine setIntegral_congr_fun measurableSet_Iic fun w hw => ?_
                have hw : w ≤ x := hw
                simp only [hHf]
                rw [← Real.exp_add, ← Real.exp_add, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
                  Function.update_self, max_eq_left (by linarith)]
                have : ∑ k ∈ Finset.univ.erase i, lam k * max (Function.update u i x k - w) 0
                    = ∑ k ∈ Finset.univ.erase i, lam k * max (u k - w) 0 := by
                  refine Finset.sum_congr rfl fun k hk => ?_
                  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
                rw [this]
                congr 1; ring
              have hgc : ∀ i u, Continuous (fun w => Real.exp (lam i * w) * Hf i u w) := by
                intro i u
                have := hHfc i u
                fun_prop
              have hgI : ∀ i u x, IntegrableOn (fun w => Real.exp (lam i * w) * Hf i u w) (Set.Iic x) := by
                intro i u x
                refine Integrable.mono' (integrableOn_exp_mul_Iic (hlam i) x)
                  (hgc i u).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
                have h1 := hH1 i u w
                have h0 := hH0 i u w
                have h2 := Real.exp_pos (lam i * w)
                rw [Real.norm_eq_abs, abs_of_pos (mul_pos h2 h0)]
                nlinarith
              have hQd : ∀ i (u : Fin (m + 1) → ℝ) (x : ℝ),
                  HasDerivAt (fun x => choiceProb (Function.update u i x) lam i)
                    (lam i * (Hf i u x - choiceProb (Function.update u i x) lam i)) x := by
                intro i u x
                have hfun : (fun x => choiceProb (Function.update u i x) lam i) = fun x =>
                    lam i * Real.exp (-(lam i * x)) * ((∫ w in Set.Iic 0, Real.exp (lam i * w) * Hf i u w) +
                      ∫ w in (0:ℝ)..x, Real.exp (lam i * w) * Hf i u w) := by
                  funext x
                  rw [hQ0, ← intervalIntegral.integral_Iic_sub_Iic (hgI i u 0) (hgI i u x)]
                  ring
                have hval := congrFun hfun x
                rw [hval, hfun]
                have d1 : HasDerivAt (fun x : ℝ => -(lam i * x)) (-(lam i * 1)) x :=
                  ((hasDerivAt_id x).const_mul (lam i)).neg
                have d2 := d1.exp.const_mul (lam i)
                have d3 : HasDerivAt (fun x => ∫ w in (0:ℝ)..x, Real.exp (lam i * w) * Hf i u w)
                    (Real.exp (lam i * x) * Hf i u x) x :=
                  intervalIntegral.integral_hasDerivAt_right ((hgc i u).intervalIntegrable _ _)
                    ((hgc i u).stronglyMeasurableAtFilter _ _) (hgc i u).continuousAt
                have d4 := d3.const_add (∫ w in Set.Iic 0, Real.exp (lam i * w) * Hf i u w)
                refine (d2.mul d4).congr_deriv ?_
                have : Real.exp (-(lam i * x)) * Real.exp (lam i * x) = 1 := by
                  rw [← Real.exp_add]; simp
                linear_combination (lam i * Hf i u x) * this
              have hQK : ∀ i (u : Fin (m + 1) → ℝ) (x : ℝ), choiceProb (Function.update u i x) lam i =
                  Hf i u x * K i (fun j => u j - x) := by
                intro i u x
                rw [hQ0, ← integral_const_mul, ← integral_indicator measurableSet_Iic,
                  ← integral_sub_left_eq_self _ _ x]
                simp only [hK]
                rw [← integral_const_mul, ← integral_Ici_eq_integral_Ioi,
                  ← integral_indicator measurableSet_Ici]
                refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
                simp only [Set.indicator_apply, Set.mem_Iic, Set.mem_Ici, sub_le_self_iff]
                split_ifs with hz
                · have key2 : Hf i u (x - z) = Hf i u x * E i (fun j => u j - x) z := by
                    simp only [hHf, hE]
                    rw [← Real.exp_add, ← neg_add, ← Finset.sum_add_distrib]
                    congr 2
                    refine Finset.sum_congr rfl fun k _ => ?_
                    rw [← mul_add]
                    congr 1
                    rcases le_total 0 (u k - x) with h | h
                    · rw [min_eq_right h, max_eq_left h, add_zero, max_eq_left hz, max_eq_left (by linarith)]
                      ring
                    · rw [min_eq_left h, max_eq_right h, zero_add]
                      congr 1; ring
                  have key3 : Real.exp (-(lam i * x)) * Real.exp (lam i * (x - z)) = Real.exp (-lam i * z) := by
                    rw [← Real.exp_add]; congr 1; ring
                  rw [key2, ← key3]; ring
                · rfl
              have hT0 : ∀ i w, 0 < K i w / (lam i * (1 - K i w)) := fun i w =>
                div_pos (hK0 i w) (mul_pos (hlam i) (sub_pos.2 (hK1 i w)))
              have hTanti : ∀ i w w', (∀ j, j ≠ i → min (w j) 0 ≤ min (w' j) 0) →
                  K i w' / (lam i * (1 - K i w')) ≤ K i w / (lam i * (1 - K i w)) := by
                intro i w w' h
                have h1 := hKanti i w w' h
                have h2 := hK1 i w
                have h3 := hK1 i w'
                have h4 := hlam i
                refine div_le_div₀ (hK0 i w).le h1 (mul_pos h4 (sub_pos.2 h2)) ?_
                exact mul_le_mul_of_nonneg_left (by linarith) h4.le
              refine ⟨fun i w => K i w / (lam i * (1 - K i w)), ?_, hT0, hTanti, ?_, ?_, ?_⟩
              · intro v i
                have h1 := hQK i v (v i)
                rw [Function.update_eq_self] at h1
                have h2 := (hQd i v (v i)).deriv
                rw [Function.update_eq_self] at h2
                rw [tau, partialU, h2, h1]
                have h3 := (hH0 i v (v i)).ne'
                have h4 := (hlam i).ne'
                have h5 : 1 - K i (fun j => v j - v i) ≠ 0 := (sub_pos.2 (hK1 i _)).ne'
                have h6 : lam i * (Hf i v (v i) - Hf i v (v i) * K i (fun j => v j - v i)) =
                  Hf i v (v i) * (lam i * (1 - K i (fun j => v j - v i))) := by ring
                rw [h6, mul_div_mul_left _ _ h3]
              · intro i w h
                have hL : 0 < Ltot lam := by linarith [hLpos i, hlam i]
                have h1 := (hLpos i).ne'
                have h2 := (hlam i).ne'
                show K i w / (lam i * (1 - K i w)) = _
                rw [hKconst i w h]
                have h3 : 1 - lam i / Ltot lam = (Ltot lam - lam i) / Ltot lam := by
                  field_simp
                rw [h3]
                field_simp
              · intro i v
                have hc : Continuous (fun x : ℝ => K i (fun j => v j - x)) := by
                  have h1 : (fun x : ℝ => K i (fun j => v j - x)) =
                      fun x => choiceProb (Function.update v i x) lam i / Hf i v x := by
                    funext x
                    rw [hQK, mul_div_cancel_left₀ _ (hH0 i v x).ne']
                  rw [h1]
                  refine Continuous.div ?_ (hHfc i v) fun x => (hH0 i v x).ne'
                  exact continuous_iff_continuousAt.2 fun x => (hQd i v x).continuousAt
                refine Continuous.div hc (continuous_const.mul (continuous_const.sub hc)) fun x => ?_
                exact (mul_pos (hlam i) (sub_pos.2 (hK1 i _))).ne'
              · intro i u x0 hx0
                have hder : ∀ x, HasDerivAt (fun x => (α i - x) * choiceProb (Function.update u i x) lam i)
                    (Hf i u x * (lam i * (1 - K i (fun j => u j - x))) * ((α i - x) -
                      K i (fun j => u j - x) / (lam i * (1 - K i (fun j => u j - x))))) x := by
                  intro x
                  have d1 : HasDerivAt (fun x : ℝ => α i - x) (-1) x := (hasDerivAt_id x).const_sub (α i)
                  refine (d1.mul (hQd i u x)).congr_deriv ?_
                  rw [hQK]
                  have h4 := (hlam i).ne'
                  have h5 : 1 - K i (fun j => u j - x) ≠ 0 := (sub_pos.2 (hK1 i _)).ne'
                  field_simp
                  ring
                have hcts : Continuous (fun x => (α i - x) * choiceProb (Function.update u i x) lam i) :=
                  continuous_iff_continuousAt.2 fun x => (hder x).continuousAt
                have hpf : ∀ x, 0 < Hf i u x * (lam i * (1 - K i (fun j => u j - x))) := fun x =>
                  mul_pos (hH0 i u x) (mul_pos (hlam i) (sub_pos.2 (hK1 i _)))
                have hmonoT : ∀ x y : ℝ, x ≤ y → K i (fun j => u j - x) / (lam i * (1 - K i (fun j => u j - x)))
                    ≤ K i (fun j => u j - y) / (lam i * (1 - K i (fun j => u j - y))) := by
                  intro x y hxy
                  exact hTanti i (fun j => u j - y) (fun j => u j - x) fun j _ =>
                    min_le_min (by linarith) le_rfl
                have hx0' : α i - x0 = K i (fun j => u j - x0) / (lam i * (1 - K i (fun j => u j - x0))) := hx0
                intro x hx
                rcases lt_or_gt_of_ne hx with h | h
                · have hm : StrictMonoOn (fun x => (α i - x) * choiceProb (Function.update u i x) lam i)
                      (Set.Iic x0) := by
                    refine strictMonoOn_of_deriv_pos (convex_Iic x0) hcts.continuousOn fun y hy => ?_
                    rw [interior_Iic] at hy
                    have hy : y < x0 := hy
                    rw [(hder y).deriv]
                    refine mul_pos (hpf y) ?_
                    have := hmonoT y x0 hy.le
                    linarith
                  exact hm h.le (le_refl x0) h
                · have hm : StrictAntiOn (fun x => (α i - x) * choiceProb (Function.update u i x) lam i)
                      (Set.Ici x0) := by
                    refine strictAntiOn_of_deriv_neg (convex_Ici x0) hcts.continuousOn fun y hy => ?_
                    rw [interior_Ici] at hy
                    have hy : x0 < y := hy
                    rw [(hder y).deriv]
                    refine mul_neg_of_pos_of_neg (hpf y) ?_
                    have := hmonoT x0 y hy.le
                    linarith
                  exact hm (le_refl x0) h.le h
            clear hQreal hS hP
            have hTcongr : ∀ i w w', (∀ j, j ≠ i → min (w j) 0 = min (w' j) 0) → T i w = T i w' :=
              fun i w w' h => le_antisymm (hanti i w' w fun j hj => (h j hj).ge)
                (hanti i w w' fun j hj => (h j hj).le)
            have hTmono : ∀ i (u : Fin (m + 1) → ℝ) (x y : ℝ), x ≤ y →
                T i (fun j => u j - x) ≤ T i (fun j => u j - y) := by
              intro i u x y hxy
              exact hanti i _ _ fun j _ => min_le_min (by linarith) le_rfl
            have hroot : ∀ i (u : Fin (m + 1) → ℝ), ∃ x, α i - x = T i (fun j => u j - x) := by
              intro i u
              have hle : α i - T i (fun j => u j - α i) ≤ α i := by linarith [hpos i (fun j => u j - α i)]
              have hc : Continuous (fun x => α i - x - T i (fun j => u j - x)) :=
                (continuous_const.sub continuous_id).sub (hcont i u)
              have := intermediate_value_Icc' hle hc.continuousOn
              obtain ⟨x, -, hx⟩ := this (show (0:ℝ) ∈ _ by
                constructor
                · simpa using (hpos i (fun j => u j - α i)).le
                · have := hTmono i u _ _ hle
                  simp only [sub_sub_cancel]
                  linarith)
              exact ⟨x, by simp only at hx; linarith⟩
            have huniq : ∀ i (u : Fin (m + 1) → ℝ) (x y : ℝ), α i - x = T i (fun j => u j - x) →
                α i - y = T i (fun j => u j - y) → x = y := by
              intro i u x y hx hy
              rcases lt_trichotomy x y with h | h | h
              · have := hTmono i u _ _ h.le
                linarith
              · exact h
              · have := hTmono i u _ _ h.le
                linarith
            have hltα : ∀ i (u : Fin (m + 1) → ℝ) (x : ℝ), α i - x = T i (fun j => u j - x) → x < α i := by
              intro i u x hx
              have := hpos i (fun j => u j - x)
              linarith
            have hM : ∀ i, α i ≤ maxAlpha α := fun i => le_ciSup (Set.finite_range α).bddAbove i
            -- Nash equilibria are the solutions of the first-order system
            have hutil : ∀ (p : Fin (m + 1) → ℝ) i q, util α β (Function.update p i q) =
                Function.update (util α β p) i (α i - β * q) := by
              intro p i q
              funext j
              by_cases h : j = i
              · subst h; simp [util]
              · simp [util, h]
            have hFR : ∀ (p : Fin (m + 1) → ℝ) i q, firmRevenue α β lam (Function.update p i q) i =
                ((α i - (α i - β * q)) * choiceProb (Function.update (util α β p) i (α i - β * q)) lam i) / β := by
              intro p i q
              rw [firmRevenue, hutil, Function.update_self]
              field_simp
              ring
            have hNE : ∀ p, IsPriceNE α β lam p ↔
                ∀ i, α i - util α β p i = T i (fun j => util α β p j - util α β p i) := by
              intro p
              constructor
              · rintro ⟨-, h⟩ i
                obtain ⟨x0, hx0⟩ := hroot i (util α β p)
                have hlt := hltα i _ _ hx0
                have hp : util α β p i = α i - β * p i := rfl
                by_cases he : util α β p i = x0
                · rw [he]; exact hx0
                · exfalso
                  have h1 := hmax i (util α β p) x0 hx0 _ he
                  have h2 := h i ((α i - x0) / β) (by
                    have : 0 < α i - x0 := by linarith
                    positivity)
                  rw [hFR] at h2
                  have h3 := hFR p i (p i)
                  rw [Function.update_eq_self] at h3
                  rw [h3, ← hp, div_le_div_iff_of_pos_right hβ] at h2
                  have h4 : α i - β * ((α i - x0) / β) = x0 := by field_simp; ring
                  rw [h4] at h2
                  linarith
              · intro h
                refine ⟨fun i => ?_, fun i q hq => ?_⟩
                · have hlt := hltα i _ _ (h i)
                  have hp : util α β p i = α i - β * p i := rfl
                  have : 0 < β * p i := by linarith
                  exact ((mul_pos_iff_of_pos_left hβ).1 this).le
                · rw [hFR]
                  have h3 := hFR p i (p i)
                  rw [Function.update_eq_self] at h3
                  have hp : util α β p i = α i - β * p i := rfl
                  rw [h3, ← hp, div_le_div_iff_of_pos_right hβ]
                  by_cases he : α i - β * q = util α β p i
                  · rw [he]
                  · exact (hmax i _ _ (h i) _ he).le
            -- uniqueness of solutions of the system
            have hsysle : ∀ u v : Fin (m + 1) → ℝ, (∀ i, α i - u i = T i (fun j => u j - u i)) →
                (∀ i, α i - v i = T i (fun j => v j - v i)) → ∀ i, u i ≤ v i := by
              intro u v hu hv
              obtain ⟨i, hi⟩ := Finite.exists_max (fun i => u i - v i)
              have h1 : T i (fun j => v j - v i) ≤ T i (fun j => u j - u i) :=
                hanti i _ _ fun j _ => min_le_min (by linarith [hi j]) le_rfl
              have h2 : u i ≤ v i := by linarith [hu i, hv i]
              intro j
              linarith [hi j]
            -- existence of a solution of the system (Tarski)
            have hsys : ∃ u : Fin (m + 1) → ℝ, ∀ i, α i - u i = T i (fun j => u j - u i) := by
              choose e he using hroot
              have hemono : ∀ i (u v : Fin (m + 1) → ℝ), (∀ j, u j ≤ v j) → e i u ≤ e i v := by
                intro i u v h
                by_contra hc
                push Not at hc
                have h1 := hTmono i u _ _ hc.le
                have h2 : T i (fun j => v j - e i v) ≤ T i (fun j => u j - e i v) :=
                  hanti i _ _ fun j _ => min_le_min (by linarith [h j]) le_rfl
                linarith [he i u, he i v]
              obtain ⟨k, hk⟩ := Finite.exists_min (fun i => α i - 1 / (Ltot lam - lam i))
              have hlow : ∀ i, α k - 1 / (Ltot lam - lam k) ≤
                  e i (fun _ => α k - 1 / (Ltot lam - lam k)) := by
                intro i
                by_contra hc
                push Not at hc
                have h1 := hconst i (fun j => (fun _ => α k - 1 / (Ltot lam - lam k)) j -
                  e i (fun _ => α k - 1 / (Ltot lam - lam k))) (fun j _ => by
                    simp only; linarith)
                have h2 := he i (fun _ => α k - 1 / (Ltot lam - lam k))
                have h3 := hk i
                simp only at h3 h1
                linarith
              have heM : ∀ i u, e i u ≤ maxAlpha α := fun i u =>
                (hltα i _ _ (he i u)).le.trans (hM i)
              set A : Set (Fin (m + 1) → ℝ) := {v | (∀ i, v i ≤ maxAlpha α) ∧ ∀ i, v i ≤ e i v} with hA
              have hAne : (fun _ => α k - 1 / (Ltot lam - lam k)) ∈ A :=
                ⟨fun i => (hlow i).trans (heM i _), hlow⟩
              have hbd : ∀ i, BddAbove ((fun v : Fin (m + 1) → ℝ => v i) '' A) := by
                intro i
                refine ⟨maxAlpha α, ?_⟩
                rintro _ ⟨v, hv, rfl⟩
                exact hv.1 i
              have hub : ∀ v ∈ A, ∀ i, v i ≤ sSup ((fun v : Fin (m + 1) → ℝ => v i) '' A) :=
                fun v hv i => le_csSup (hbd i) ⟨v, hv, rfl⟩
              set us : Fin (m + 1) → ℝ := fun i => sSup ((fun v : Fin (m + 1) → ℝ => v i) '' A) with hus
              have h1 : ∀ i, us i ≤ e i us := by
                intro i
                refine csSup_le ⟨_, ⟨_, hAne, rfl⟩⟩ ?_
                rintro _ ⟨v, hv, rfl⟩
                exact (hv.2 i).trans (hemono i v us (hub v hv))
              have h2 : (fun i => e i us) ∈ A := ⟨fun i => heM i us, fun i => hemono i _ _ h1⟩
              refine ⟨us, fun i => ?_⟩
              have h3 : us i = e i us := le_antisymm (h1 i) (hub _ h2 i)
              have h4 := he i us
              rw [← h3] at h4
              exact h4
            -- solved sets
            have hmem : ∀ (σ : Fin (m + 1) ≃ Fin (m + 1)) (t : ℕ) i,
                i ∈ solvedBefore σ t ↔ (σ.symm i).val < t := by
              intro σ t i
              simp only [solvedBefore, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨s, hs, rfl⟩
                simpa using hs
              · intro h
                exact ⟨σ.symm i, h, by simp⟩
            set W : Finset (Fin (m + 1)) → (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ :=
              fun S us j => if j ∈ S then us j else maxAlpha α with hW
            have htc : ∀ S us i x, tauCond α lam S us i x = T i (fun j => W S us j - x) := by
              intro S us i x
              rw [tauCond, htau]
              refine hTcongr i _ _ fun j hj => ?_
              simp [condVec, hW, hj]
            have hempty : ∀ (us : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (x : ℝ), x ≤ maxAlpha α →
                T i (fun j => W ∅ us j - x) = 1 / (Ltot lam - lam i) := by
              intro us i x hx
              refine hconst i _ fun j _ => ?_
              simp [hW, hx]
            have hs0 : ∀ σ : Fin (m + 1) ≃ Fin (m + 1), solvedBefore σ 0 = ∅ := by
              intro σ
              simp [solvedBefore]
            have hLpos : ∀ i, 0 < 1 / (Ltot lam - lam i) := by
              intro i
              rw [← hconst i (fun _ => 0) (fun _ _ => le_rfl)]
              exact hpos i _
            -- the first step candidates solve the conditional equation with nothing solved
            have hfirst : ∀ (us : Fin (m + 1) → ℝ) i, α i - (α i - 1 / (Ltot lam - lam i)) =
                T i (fun j => W ∅ us j - (α i - 1 / (Ltot lam - lam i))) := by
              intro us i
              rw [hempty us i _ (by linarith [hLpos i, hM i])]
              ring
            refine ⟨?_, ?_⟩
            · obtain ⟨us, hus⟩ := hsys
              set σ : Fin (m + 1) ≃ Fin (m + 1) := Tuple.sort us with hσ
              have hmono : ∀ s t, s ≤ t → us (σ s) ≤ us (σ t) := fun s t h => Tuple.monotone_sort us h
              have hlt : ∀ i, us i < maxAlpha α := fun i => (hltα i _ _ (hus i)).trans_le (hM i)
              have hge : ∀ s i, i ∉ solvedBefore σ (s : Fin (m + 1)).val → us (σ s) ≤ us i := by
                intro s i hi
                rw [hmem, not_lt] at hi
                have := hmono s (σ.symm i) hi
                simpa using this
              have hAs : ∀ s : Fin (m + 1), α (σ s) - us (σ s) =
                  T (σ s) (fun j => W (solvedBefore σ s.val) us j - us (σ s)) := by
                intro s
                rw [hus (σ s)]
                refine hTcongr _ _ _ fun j _ => ?_
                simp only [hW]
                split_ifs with hj
                · rfl
                · rw [min_eq_right (by linarith [hge s j hj]), min_eq_right (by linarith [hlt (σ s)])]
              have hBs : ∀ (s : Fin (m + 1)) i x, i ∉ solvedBefore σ s.val →
                  α i - x = T i (fun j => W (solvedBefore σ s.val) us j - x) → us (σ s) ≤ x := by
                intro s i x hi hx
                by_contra hc
                push Not at hc
                have h1 : T i (fun j => W (solvedBefore σ s.val) us j - x) = T i (fun j => us j - x) := by
                  refine hTcongr _ _ _ fun j _ => ?_
                  simp only [hW]
                  split_ifs with hj
                  · rfl
                  · rw [min_eq_right (by linarith [hlt (σ s)]), min_eq_right (by linarith [hge s j hj])]
                rw [h1] at hx
                have h2 := huniq i us _ _ hx (hus i)
                have h3 := hge s i hi
                linarith
              refine ⟨σ, us, fun s => ⟨fun h0 => ?_, fun _ => ?_⟩⟩
              · have hA' := hAs s
                have hB' := hBs s
                rw [h0, hs0] at hA' hB'
                have he : us (σ s) = α (σ s) - 1 / (Ltot lam - lam (σ s)) :=
                  huniq _ _ _ _ hA' (hfirst us (σ s))
                refine ⟨fun i => ?_, he⟩
                rw [← he]
                exact hB' i _ (by simp) (hfirst us i)
              · choose c hc using fun i => hroot i (W (solvedBefore σ s.val) us)
                have he : us (σ s) = c (σ s) := huniq _ _ _ _ (hAs s) (hc (σ s))
                refine ⟨c, fun i _ => ?_, fun i hi => ?_, he⟩
                · rw [htc]; exact hc i
                · rw [← he]; exact hBs s i _ hi (hc i)
            · intro σ us hrun
              have hAs : ∀ s : Fin (m + 1), α (σ s) - us (σ s) =
                  T (σ s) (fun j => W (solvedBefore σ s.val) us j - us (σ s)) := by
                intro s
                rcases Nat.eq_zero_or_pos s.val with h0 | h0
                · rw [h0, hs0, ((hrun s).1 h0).2]
                  exact hfirst us (σ s)
                · obtain ⟨c, hc, -, he⟩ := (hrun s).2 h0
                  rw [he, ← htc]
                  exact hc (σ s) (by rw [hmem]; simp)
              have hBs : ∀ (s : Fin (m + 1)) i x, i ∉ solvedBefore σ s.val →
                  α i - x = T i (fun j => W (solvedBefore σ s.val) us j - x) → us (σ s) ≤ x := by
                intro s i x hi hx
                rcases Nat.eq_zero_or_pos s.val with h0 | h0
                · rw [h0, hs0] at hx
                  rw [((hrun s).1 h0).2, huniq i _ _ _ hx (hfirst us i)]
                  exact ((hrun s).1 h0).1 i
                · obtain ⟨c, hc, hmin, he⟩ := (hrun s).2 h0
                  have h1 := hc i hi
                  rw [htc] at h1
                  rw [he, huniq i _ _ _ hx h1]
                  exact hmin i hi
              have hlt : ∀ i, us i < maxAlpha α := by
                intro i
                have h := hAs (σ.symm i)
                rw [σ.apply_symm_apply] at h
                exact (hltα i _ _ h).trans_le (hM i)
              have hmono : Monotone (fun s => us (σ s)) := by
                rw [Fin.monotone_iff_le_succ]
                intro s
                by_contra hc
                push Not at hc
                have h1 := hAs s.succ
                have h2 : T (σ s.succ) (fun j => W (solvedBefore σ s.succ.val) us j - us (σ s.succ)) =
                    T (σ s.succ) (fun j => W (solvedBefore σ s.castSucc.val) us j - us (σ s.succ)) := by
                  refine hTcongr _ _ _ fun j _ => ?_
                  simp only [hW, hmem, Fin.val_succ, Fin.val_castSucc]
                  rcases lt_trichotomy (σ.symm j).val s.val with h | h | h
                  · rw [if_pos (by omega), if_pos h]
                  · rw [if_pos (by omega), if_neg (by omega)]
                    have hj : j = σ s.castSucc := by
                      rw [← Equiv.symm_apply_eq]
                      exact Fin.ext h
                    rw [hj, min_eq_right (by linarith), min_eq_right (by linarith [hlt (σ s.succ)])]
                  · rw [if_neg (by omega), if_neg (by omega)]
                rw [h2] at h1
                have h3 := hBs s.castSucc (σ s.succ) _ (by rw [hmem]; simp) h1
                linarith
              have hge : ∀ s i, i ∉ solvedBefore σ (s : Fin (m + 1)).val → us (σ s) ≤ us i := by
                intro s i hi
                rw [hmem, not_lt] at hi
                have : us (σ s) ≤ us (σ (σ.symm i)) := hmono hi
                simpa using this
              have hus : ∀ i, α i - us i = T i (fun j => us j - us i) := by
                intro i
                have h := hAs (σ.symm i)
                rw [σ.apply_symm_apply] at h
                rw [h]
                refine hTcongr _ _ _ fun j _ => ?_
                simp only [hW]
                split_ifs with hj
                · rfl
                · have := hge _ j hj
                  rw [σ.apply_symm_apply] at this
                  rw [min_eq_right (by linarith [hlt i]), min_eq_right (by linarith)]
              have hutileq : util α β (eqPrices α β us) = us := by
                funext i
                simp only [util, eqPrices]
                field_simp
                ring
              refine ⟨fun s _ i _ => ?_, ?_, fun p hp => ?_⟩
              · obtain ⟨x, hx⟩ := hroot i (W (solvedBefore σ s.val) us)
                refine ⟨x, by simp only [htc]; exact hx, fun y hy => ?_⟩
                simp only [htc] at hy
                exact huniq i _ _ _ hy hx
              · rw [hNE, hutileq]
                exact hus
              · rw [hNE] at hp
                have heq : ∀ i, util α β p i = us i := fun i =>
                  le_antisymm (hsysle _ _ hp hus i) (hsysle _ _ hus hp i)
                funext i
                have h := heq i
                simp only [util] at h
                simp only [eqPrices]
                rw [← h]
                field_simp
                ring
