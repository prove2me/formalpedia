-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:58.613857+00:00
-- url     : https://prove2.me/submissions/aca6fd5a-d19e-4d14-a4f1-2568cd974503

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) :
    Continuous (fun u => choiceProb u lam i) ∧
      (∀ j, Continuous (partialU (fun v => choiceProb v lam i) j)) ∧
      ∀ (u : Fin n → ℝ) (j : Fin n),
        (j ≠ i → u i ≤ u j →
            HasDerivAt (fun t => choiceProb (Function.update u j t) lam i)
              (-(lam j * choiceProb u lam i)) (u j)) ∧
          (j = i →
            HasDerivAt (fun t => choiceProb (Function.update u j t) lam i)
              (Lsum u lam i * G u lam i - lam i * choiceProb u lam i) (u j)) ∧
          (j ≠ i → u j ≤ u i →
            HasDerivAt (fun t => choiceProb (Function.update u j t) lam i)
              (-(lam i * choiceProb u lam j)) (u j)) := by
                obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
                have hsing : ∀ (r y : ℝ), expMeasure r {y} = 0 := by
                  intro r y
                  simp only [expMeasure, gammaMeasure]
                  rw [withDensity_apply _ (measurableSet_singleton y)]
                  simp
                have hsurv : ∀ k (y : ℝ), expMeasure (lam k) (Set.Ici y) =
                    ENNReal.ofReal (Real.exp (-(lam k * max y 0))) := by
                  intro k y
                  have := isProbabilityMeasure_expMeasure (hlam k)
                  have h1 : expMeasure (lam k) (Set.Ici y) = expMeasure (lam k) (Set.Ioi y) := by
                    exact (measure_congr (Ioi_ae_eq_Ici' (hsing _ y))).symm
                  have h2 : expMeasure (lam k) (Set.Ioi y) = 1 - expMeasure (lam k) (Set.Iic y) := by
                    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
                  have h3 : expMeasure (lam k) (Set.Iic y) = ENNReal.ofReal (cdf (expMeasure (lam k)) y) := by
                    rw [cdf_eq_real, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
                  rw [h1, h2, h3, cdf_expMeasure_eq (hlam k)]
                  split_ifs with hy
                  · have h0 : 0 ≤ 1 - Real.exp (-(lam k * y)) := by
                      have := Real.exp_le_one_iff.2 (show -(lam k*y) ≤ 0 by nlinarith [hlam k]); linarith
                    rw [max_eq_left hy, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h0]
                    congr 1; ring
                  · rw [max_eq_right (le_of_not_ge hy)]; simp
                have hrep : ∀ (u : Fin (m+1) → ℝ) (i : Fin (m+1)), choiceProb u lam i =
                    lam i * ∫ s in Set.Ioi (0:ℝ), Real.exp (-(∑ k, lam k * max (u k - u i + s) 0)) := by
                  intro u i
                  have hP : ∀ k, IsProbabilityMeasure (expMeasure (lam k)) :=
                    fun k => isProbabilityMeasure_expMeasure (hlam k)
                  unfold choiceProb errorLaw
                  have hmp := measurePreserving_piFinSuccAbove (fun k => expMeasure (lam k)) i
                  set B : Set (ℝ × (Fin m → ℝ)) :=
                    {p | ∀ k, p.1 + (u (i.succAbove k) - u i) ≤ p.2 k} with hBdef
                  have hA : {z : Fin (m+1) → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i} =
                      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' B := by
                    ext z
                    simp only [Set.mem_setOf_eq, Set.mem_preimage, hBdef, MeasurableEquiv.piFinSuccAbove_apply,
                      Fin.insertNthEquiv_symm_apply, Fin.removeNth_apply]
                    constructor
                    · intro h k
                      have := h (i.succAbove k) (Fin.succAbove_ne i k)
                      linarith
                    · intro h j hj
                      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
                      have := h k
                      linarith
                  have hB : MeasurableSet B := by
                    rw [hBdef, Set.setOf_forall]
                    exact MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) (by fun_prop)
                  rw [hA, hmp.measure_preimage hB.nullMeasurableSet, Measure.prod_apply hB]
                  have hslice : ∀ x : ℝ, Prod.mk x ⁻¹' B =
                      Set.univ.pi (fun k : Fin m => Set.Ici (x + (u (i.succAbove k) - u i))) := by
                    intro x; ext w; simp [hBdef, Pi.le_def]
                  simp_rw [hslice, Measure.pi_pi, hsurv]
                  have hEnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
                      (fun s : ℝ => Real.exp (-(∑ k, lam k * max (u k - u i + s) 0))) :=
                    Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)
                  rw [integral_eq_lintegral_of_nonneg_ae hEnn (by fun_prop)]
                  rw [show ∀ X : ENNReal, lam i * X.toReal = (ENNReal.ofReal (lam i) * X).toReal from
                    fun X => by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hlam i).le]]
                  congr 1
                  rw [show expMeasure (lam i) = volume.withDensity (exponentialPDF (lam i)) from rfl]
                  have hpdfm : Measurable (exponentialPDF (lam i)) :=
                    (measurable_exponentialPDFReal (lam i)).ennreal_ofReal
                  rw [lintegral_withDensity_eq_lintegral_mul _ hpdfm (by fun_prop)]
                  rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator measurableSet_Ioi]
                  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by rw [ae_iff]; simp
                  apply lintegral_congr_ae
                  filter_upwards [hne] with x hx
                  rcases lt_or_gt_of_ne hx with hx | hx
                  · simp [exponentialPDF_of_neg hx, Set.indicator_of_notMem (show x ∉ Set.Ioi 0 from
                      fun h => absurd (Set.mem_Ioi.1 h) (not_lt.2 hx.le))]
                  · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hx)]
                    simp only [Pi.mul_apply]
                    rw [exponentialPDF_of_nonneg hx.le, ← ENNReal.ofReal_prod_of_nonneg
                      (fun k _ => (Real.exp_pos _).le), ← ENNReal.ofReal_mul (by nlinarith [hlam i, Real.exp_pos (-(lam i * x))]),
                      ← ENNReal.ofReal_mul (hlam i).le]
                    congr 1
                    rw [← Real.exp_sum, mul_assoc, ← Real.exp_add, Fin.sum_univ_succAbove _ i]
                    congr 2
                    rw [show u i - u i + x = x by ring, max_eq_left hx.le, neg_add, ← Finset.sum_neg_distrib]
                    congr 1
                    refine Finset.sum_congr rfl fun k _ => ?_
                    ring_nf
                have hshift : ∀ (f : ℝ → ℝ) (d : ℝ), ∫ s in Set.Ioi d, f s = ∫ s in Set.Ioi (0:ℝ), f (s + d) := by
                  intro f d
                  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
                    ← integral_add_right_eq_self (μ := volume) _ d]
                  congr 1; funext s
                  by_cases h : 0 < s
                  · simp [Set.indicator, h, show d < s + d by linarith]
                  · simp [Set.indicator, h, show ¬ d < s + d by intro h'; exact h (by linarith)]
                have hexpint : ∀ (r c : ℝ), 0 < r → IntegrableOn (fun s : ℝ => Real.exp (-(r * s))) (Set.Ioi c) := by
                  intro r c hr
                  have := exp_neg_integrableOn_Ioi c hr
                  simpa [neg_mul] using this
                have hJcont : ∀ (i : Fin (m+1)) (a : (Fin (m+1) → ℝ) → ℝ), Continuous a → (∀ v, a v ≤ v i) →
                    Continuous (fun v => ∫ s in Set.Ioi (0:ℝ),
                      Real.exp (-(∑ k, lam k * max (v k - a v + s) 0))) := by
                  intro i a ha hai
                  refine continuous_of_dominated (bound := fun s => Real.exp (-(lam i * s))) ?_ ?_ (hexpint _ 0 (hlam i)) ?_
                  · intro v; exact (by fun_prop : Continuous fun s : ℝ =>
                      Real.exp (-(∑ k, lam k * max (v k - a v + s) 0))).aestronglyMeasurable
                  · intro v
                    rw [ae_restrict_iff' measurableSet_Ioi]
                    refine Filter.Eventually.of_forall fun s hs => ?_
                    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                    apply Real.exp_le_exp.2
                    have h1 : lam i * max (v i - a v + s) 0 ≤ ∑ k, lam k * max (v k - a v + s) 0 :=
                      Finset.single_le_sum (f := fun k => lam k * max (v k - a v + s) 0)
                        (fun k _ => mul_nonneg (hlam k).le (le_max_right _ _)) (Finset.mem_univ i)
                    have h2 : s ≤ max (v i - a v + s) 0 := le_max_of_le_left (by linarith [hai v])
                    have h3 := mul_le_mul_of_nonneg_left h2 (hlam i).le
                    linarith
                  · exact Filter.Eventually.of_forall fun s => by fun_prop
                have hexpLip : ∀ A B R : ℝ, 0 ≤ A → 0 ≤ B →
                    |Real.exp (-(A + R)) - Real.exp (-(B + R))| ≤ Real.exp (-R) * |A - B| := by
                  intro A B R hA hB
                  have hsplitAR : ∀ X, Real.exp (-(X + R)) = Real.exp (-X) * Real.exp (-R) := by
                    intro X; rw [← Real.exp_add]; ring_nf
                  rw [hsplitAR, hsplitAR, ← sub_mul, abs_mul, abs_of_pos (Real.exp_pos (-R)), mul_comm]
                  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                  have key : ∀ X Y : ℝ, 0 ≤ X → X ≤ Y → |Real.exp (-X) - Real.exp (-Y)| ≤ |X - Y| := by
                    intro X Y hX hXY
                    have e1 : Real.exp (-Y) = Real.exp (-X) * Real.exp (X - Y) := by rw [← Real.exp_add]; ring_nf
                    have e2 := Real.add_one_le_exp (X - Y)
                    have e3 : Real.exp (X - Y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
                    have e4 : Real.exp (-X) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
                    have e5 := Real.exp_pos (-X)
                    rw [abs_of_nonneg (by rw [e1]; nlinarith), abs_of_nonpos (by linarith), e1]
                    nlinarith
                  rcases le_total A B with h | h
                  · exact key A B hA h
                  · rw [abs_sub_comm, abs_sub_comm A]; exact key B A hB h
                have hDj : ∀ (u : Fin (m+1) → ℝ) (i j : Fin (m+1)), j ≠ i →
                    HasDerivAt (fun t => ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (Function.update u j t k - u i + s) 0)))
                      (-(lam j) * ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (u k - min (u i) (u j) + s) 0))) (u j) := by
                  intro u i j hji
                  set R : ℝ → ℝ := fun s => ∑ k ∈ Finset.univ.erase j, lam k * max (u k - u i + s) 0 with hRdef
                  have hsplit : ∀ t s, ∑ k, lam k * max (Function.update u j t k - u i + s) 0 =
                      lam j * max (t - u i + s) 0 + R s := by
                    intro t s
                    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
                    simp only [Function.update_self, hRdef]
                    congr 1
                    apply Finset.sum_congr rfl
                    intro k hk
                    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
                  have hR : ∀ s, 0 < s → lam i * s ≤ R s := by
                    intro s hs
                    have h1 : lam i * max (u i - u i + s) 0 ≤ R s :=
                      Finset.single_le_sum (f := fun k => lam k * max (u k - u i + s) 0)
                        (fun k _ => mul_nonneg (hlam k).le (le_max_right _ _))
                        (Finset.mem_erase.2 ⟨hji.symm, Finset.mem_univ i⟩)
                    rw [show u i - u i + s = s by ring, max_eq_left hs.le] at h1
                    exact h1
                  have hRc : Continuous R := by rw [hRdef]; fun_prop
                  simp_rw [hsplit]
                  set F' : ℝ → ℝ := fun s => -(lam j) * ((if u i - u j < s then (1:ℝ) else 0) *
                    Real.exp (-(lam j * max (u j - u i + s) 0 + R s))) with hF'def
                  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict (Set.Ioi (0:ℝ)))
                    (F := fun t s => Real.exp (-(lam j * max (t - u i + s) 0 + R s))) (F' := F') (x₀ := u j)
                    (bound := fun s => lam j * Real.exp (-(lam i * s))) (s := Set.univ) Filter.univ_mem
                    (Filter.Eventually.of_forall fun t => (by fun_prop : Continuous fun s =>
                      Real.exp (-(lam j * max (t - u i + s) 0 + R s))).aestronglyMeasurable)
                    (by
                      refine Integrable.mono' (hexpint _ 0 (hlam i))
                        ((by fun_prop : Continuous fun s =>
                          Real.exp (-(lam j * max (u j - u i + s) 0 + R s))).aestronglyMeasurable) ?_
                      rw [ae_restrict_iff' measurableSet_Ioi]
                      refine Filter.Eventually.of_forall fun s hs => ?_
                      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                      apply Real.exp_le_exp.2
                      have := hR s hs
                      have := mul_nonneg (hlam j).le (le_max_right (u j - u i + s) 0)
                      linarith)
                    (by
                      apply Measurable.aestronglyMeasurable
                      apply Measurable.const_mul
                      apply Measurable.mul
                      · exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
                      · exact (by fun_prop : Continuous fun s =>
                          Real.exp (-(lam j * max (u j - u i + s) 0 + R s))).measurable)
                    (by
                      rw [ae_restrict_iff' measurableSet_Ioi]
                      refine Filter.Eventually.of_forall fun s hs => ?_
                      apply LipschitzOnWith.of_dist_le_mul
                      intro x _ y _
                      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs,
                        abs_of_pos (mul_pos (hlam j) (Real.exp_pos _))]
                      calc _ ≤ Real.exp (-R s) * |lam j * max (x - u i + s) 0 - lam j * max (y - u i + s) 0| :=
                            hexpLip _ _ _ (mul_nonneg (hlam j).le (le_max_right _ _))
                              (mul_nonneg (hlam j).le (le_max_right _ _))
                        _ ≤ Real.exp (-(lam i * s)) * (lam j * |x - y|) := by
                            apply mul_le_mul (Real.exp_le_exp.2 (by linarith [hR s hs])) _ (abs_nonneg _)
                              (Real.exp_pos _).le
                            rw [← mul_sub, abs_mul, abs_of_pos (hlam j)]
                            apply mul_le_mul_of_nonneg_left _ (hlam j).le
                            have := abs_max_sub_max_le_abs (x - u i + s) (y - u i + s) 0
                            rw [show x - u i + s - (y - u i + s) = x - y by ring] at this
                            exact this
                        _ = _ := by ring)
                    ((hexpint _ 0 (hlam i)).const_mul (lam j))
                    (by
                      have hne : ∀ᵐ s : ℝ, s ≠ u i - u j := by rw [ae_iff]; simp
                      refine ae_restrict_of_ae ?_
                      filter_upwards [hne] with s hs
                      rcases lt_or_gt_of_ne hs with hs | hs
                      · have hneg : u j - u i + s < 0 := by linarith
                        have hev : ∀ᶠ t in nhds (u j), t - u i + s < 0 :=
                          ((by fun_prop : Continuous fun t : ℝ => t - u i + s).tendsto (u j)).eventually
                            (gt_mem_nhds hneg)
                        have hc : HasDerivAt (fun _ : ℝ => Real.exp (-(lam j * 0 + R s))) 0 (u j) :=
                          hasDerivAt_const _ _
                        rw [hF'def]; simp only [if_neg (not_lt.2 hs.le), zero_mul, mul_zero]
                        refine hc.congr_of_eventuallyEq ?_
                        filter_upwards [hev] with t ht
                        rw [max_eq_right ht.le]
                      · have hpos : 0 < u j - u i + s := by linarith
                        have hev : ∀ᶠ t in nhds (u j), 0 < t - u i + s :=
                          ((by fun_prop : Continuous fun t : ℝ => t - u i + s).tendsto (u j)).eventually
                            (lt_mem_nhds hpos)
                        have h1 : HasDerivAt (fun t => -(lam j * (t - u i + s) + R s)) (-(lam j * 1)) (u j) :=
                          ((((hasDerivAt_id (u j)).sub_const (u i)).add_const s).const_mul (lam j)).add_const
                            (R s) |>.neg
                        have h2 := h1.exp
                        rw [hF'def]; simp only [if_pos hs, one_mul]
                        rw [max_eq_left hpos.le]
                        refine (h2.congr_of_eventuallyEq ?_).congr_deriv (by ring)
                        filter_upwards [hev] with t ht
                        rw [max_eq_left ht.le])
                  refine key.2.congr_deriv ?_
                  rw [hF'def, integral_const_mul]
                  congr 1
                  have hΦ : ∀ s, Real.exp (-(lam j * max (u j - u i + s) 0 + R s)) =
                      Real.exp (-(∑ k, lam k * max (u k - u i + s) 0)) := by
                    intro s; rw [← hsplit, Function.update_eq_self]
                  simp_rw [hΦ]
                  rcases le_total (u i) (u j) with hij | hij
                  · rw [min_eq_left hij]
                    apply setIntegral_congr_fun measurableSet_Ioi
                    intro s hs
                    simp only [if_pos (show u i - u j < s by linarith [Set.mem_Ioi.1 hs]), one_mul]
                  · rw [min_eq_right hij]
                    have h1 : ∫ s in Set.Ioi (0:ℝ), (if u i - u j < s then (1:ℝ) else 0) *
                        Real.exp (-(∑ k, lam k * max (u k - u i + s) 0)) =
                        ∫ s in Set.Ioi (u i - u j), Real.exp (-(∑ k, lam k * max (u k - u i + s) 0)) := by
                      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
                      congr 1; funext s
                      by_cases h : u i - u j < s
                      · simp [Set.indicator, h, show 0 < s by linarith]
                      · simp [Set.indicator, h]
                    rw [h1, hshift]
                    apply setIntegral_congr_fun measurableSet_Ioi
                    intro s hs
                    simp only
                    congr 3; funext k; congr 2; ring
                have hDi : ∀ (u : Fin (m+1) → ℝ) (i : Fin (m+1)),
                    HasDerivAt (fun t => ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (Function.update u i t k - Function.update u i t i + s) 0)))
                      (Real.exp (-(∑ k, lam k * max (u k - u i) 0)) - lam i * ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (u k - u i + s) 0))) (u i) := by
                  intro u i
                  set R' : ℝ → ℝ := fun w => ∑ k ∈ Finset.univ.erase i, lam k * max (u k + w) 0 with hR'def
                  set K : ℝ → ℝ := fun w => Real.exp (-(lam i * w + R' w)) with hKdef
                  have hKc : Continuous K := by rw [hKdef, hR'def]; fun_prop
                  have hR'0 : ∀ w, 0 ≤ R' w := fun w =>
                    Finset.sum_nonneg fun k _ => mul_nonneg (hlam k).le (le_max_right _ _)
                  have hKint : ∀ c, IntegrableOn K (Set.Ioi c) := by
                    intro c
                    refine Integrable.mono' (hexpint _ c (hlam i)) hKc.aestronglyMeasurable ?_
                    refine Filter.Eventually.of_forall fun w => ?_
                    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                    exact Real.exp_le_exp.2 (by linarith [hR'0 w])
                  have hident : ∀ t, ∫ s in Set.Ioi (0:ℝ),
                      Real.exp (-(∑ k, lam k * max (Function.update u i t k - Function.update u i t i + s) 0)) =
                      Real.exp (-(lam i * t)) * ∫ w in Set.Ioi (-t), K w := by
                    intro t
                    rw [hshift K (-t), ← integral_const_mul]
                    apply setIntegral_congr_fun measurableSet_Ioi
                    intro s hs
                    have hs' : 0 < s := hs
                    simp only [hKdef, hR'def]
                    rw [← Real.exp_add, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
                    simp only [Function.update_self]
                    rw [show t - t + s = s by ring, max_eq_left hs'.le]
                    congr 1
                    have : ∑ k ∈ Finset.univ.erase i, lam k * max (Function.update u i t k - t + s) 0 =
                        ∑ k ∈ Finset.univ.erase i, lam k * max (u k + (s + -t)) 0 := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
                      congr 2; ring
                    rw [this]; ring
                  have hA : ∀ t, ∫ w in Set.Ioi (-t), K w =
                      -(∫ x in (0:ℝ)..(-t), K x) + ∫ w in Set.Ioi (0:ℝ), K w := by
                    intro t
                    rw [← intervalIntegral.integral_interval_add_Ioi (hKint (-t)) (hKint 0),
                      intervalIntegral.integral_symm]
                  have hDA : HasDerivAt (fun t => -(∫ x in (0:ℝ)..(-t), K x) + ∫ w in Set.Ioi (0:ℝ), K w)
                      (K (-(u i))) (u i) := by
                    have h1 := (hKc.integral_hasStrictDerivAt 0 (-(u i))).hasDerivAt.comp (u i)
                      (hasDerivAt_neg (u i))
                    have h2 := h1.neg.add_const (∫ w in Set.Ioi (0:ℝ), K w)
                    refine h2.congr_deriv ?_
                    simp
                  have hE : HasDerivAt (fun t => Real.exp (-(lam i * t))) (Real.exp (-(lam i * u i)) * -(lam i * 1)) (u i) :=
                    (((hasDerivAt_id (u i)).const_mul (lam i)).neg).exp
                  have hP := hE.mul hDA
                  have hfun : (fun t => ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (Function.update u i t k - Function.update u i t i + s) 0))) =
                      fun t => Real.exp (-(lam i * t)) *
                        (-(∫ x in (0:ℝ)..(-t), K x) + ∫ w in Set.Ioi (0:ℝ), K w) := by
                    funext t; rw [hident, hA]
                  rw [hfun]
                  refine hP.congr_deriv ?_
                  have hJ := hident (u i)
                  rw [Function.update_eq_self, hA] at hJ
                  rw [hJ]
                  have hKu : Real.exp (-(lam i * u i)) * K (-(u i)) = Real.exp (-(∑ k, lam k * max (u k - u i) 0)) := by
                    simp only [hKdef, hR'def]
                    rw [← Real.exp_add, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
                    rw [sub_self, max_self, mul_zero, zero_add]
                    congr 1
                    simp only [← sub_eq_add_neg]
                    ring
                  rw [← hKu]; ring
                have hLG : ∀ (u : Fin (m+1) → ℝ), Lsum u lam i * G u lam i =
                    lam i * Real.exp (-(∑ k, lam k * max (u k - u i) 0)) := by
                  intro u
                  have hpos : 0 < Lsum u lam i := by
                    unfold Lsum better betterThan
                    exact Finset.sum_pos (fun j _ => hlam j) ⟨i, by simp⟩
                  unfold G
                  have hsum : ∑ j ∈ better u i, lam j * (u j - u i) = ∑ k, lam k * max (u k - u i) 0 := by
                    unfold better betterThan
                    rw [Finset.sum_filter]
                    apply Finset.sum_congr rfl
                    intro k _
                    split_ifs with h
                    · rw [max_eq_left (by linarith)]
                    · rw [max_eq_right (by linarith [not_le.1 h])]; ring
                  rw [hsum]
                  field_simp
                have hderj : ∀ (u : Fin (m+1) → ℝ) (j : Fin (m+1)), j ≠ i →
                    HasDerivAt (fun t => choiceProb (Function.update u j t) lam i)
                      (lam i * (-(lam j) * ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (u k - min (u i) (u j) + s) 0)))) (u j) := by
                  intro u j hji
                  have hf : (fun t => choiceProb (Function.update u j t) lam i) = fun t => lam i *
                      ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (Function.update u j t k - u i + s) 0)) := by
                    funext t; rw [hrep, Function.update_of_ne (Ne.symm hji)]
                  rw [hf]
                  exact (hDj u i j hji).const_mul (lam i)
                have hderi : ∀ (u : Fin (m+1) → ℝ),
                    HasDerivAt (fun t => choiceProb (Function.update u i t) lam i)
                      (lam i * (Real.exp (-(∑ k, lam k * max (u k - u i) 0)) - lam i * ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (u k - u i + s) 0)))) (u i) := by
                  intro u
                  have hf : (fun t => choiceProb (Function.update u i t) lam i) = fun t => lam i *
                      ∫ s in Set.Ioi (0:ℝ),
                        Real.exp (-(∑ k, lam k * max (Function.update u i t k - Function.update u i t i + s) 0)) := by
                    funext t; rw [hrep]
                  rw [hf]
                  exact (hDi u i).const_mul (lam i)
                refine ⟨?_, ?_, ?_⟩
                · have hf : (fun u => choiceProb u lam i) = fun u => lam i * ∫ s in Set.Ioi (0:ℝ),
                      Real.exp (-(∑ k, lam k * max (u k - u i + s) 0)) := by
                    funext u; rw [hrep]
                  rw [hf]
                  exact continuous_const.mul (hJcont i (fun v => v i) (continuous_apply i) (fun v => le_rfl))
                · intro j
                  by_cases hji : j = i
                  · subst hji
                    have hf : partialU (fun v => choiceProb v lam j) j = fun u =>
                        lam j * (Real.exp (-(∑ k, lam k * max (u k - u j) 0)) - lam j * ∫ s in Set.Ioi (0:ℝ),
                          Real.exp (-(∑ k, lam k * max (u k - u j + s) 0))) := by
                      funext u; unfold partialU; exact (hderi u).deriv
                    rw [hf]
                    have := hJcont j (fun v => v j) (continuous_apply j) (fun v => le_rfl)
                    fun_prop
                  · have hf : partialU (fun v => choiceProb v lam i) j = fun u =>
                        lam i * (-(lam j) * ∫ s in Set.Ioi (0:ℝ),
                          Real.exp (-(∑ k, lam k * max (u k - min (u i) (u j) + s) 0))) := by
                      funext u; unfold partialU; exact (hderj u j hji).deriv
                    rw [hf]
                    have := hJcont i (fun v => min (v i) (v j)) (by fun_prop) (fun v => min_le_left _ _)
                    fun_prop
                · intro u j
                  refine ⟨fun hji hij => ?_, fun hji => ?_, fun hji hij => ?_⟩
                  · refine (hderj u j hji).congr_deriv ?_
                    rw [min_eq_left hij, hrep]; ring
                  · subst hji
                    refine (hderi u).congr_deriv ?_
                    rw [hLG, hrep]; ring
                  · refine (hderj u j hji).congr_deriv ?_
                    rw [min_eq_right hij, hrep]; ring
