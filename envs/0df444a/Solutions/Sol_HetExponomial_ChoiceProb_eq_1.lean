-- Prove2me | solution 1 for HetExponomial.ChoiceProb.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:49:06.164526+00:00
-- url     : https://prove2.me/submissions/98a33111-048e-454a-885e-d9e13cefd02c

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

open MeasureTheory ProbabilityTheory

namespace HetExponomial.ChoiceProb

lemma expMeasure_Ici {r : ℝ} (hr : 0 < r) (a : ℝ) :
    expMeasure r (Set.Ici a) = ENNReal.ofReal (1 - cdfExp r a) := by
  have := isProbabilityMeasure_expMeasure hr
  have hac : expMeasure r ≪ volume := by
    unfold expMeasure gammaMeasure
    exact withDensity_absolutelyContinuous _ _
  have : NullSingletonClass (expMeasure r) := ⟨fun x => hac Real.volume_singleton⟩
  have h1 : expMeasure r (Set.Ici a) = 1 - expMeasure r (Set.Iio a) := by
    rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
  have h2 : expMeasure r (Set.Iio a) = expMeasure r (Set.Iic a) :=
    measure_congr Iio_ae_eq_Iic
  have h3 : expMeasure r (Set.Iic a) = ENNReal.ofReal (cdfExp r a) := by
    have := cdf_eq_real (expMeasure r) a
    rw [cdf_expMeasure_eq hr] at this
    rw [measureReal_def] at this
    have h4 : cdfExp r a = ((expMeasure r) (Set.Iic a)).toReal := by
      rw [← this]; unfold cdfExp; rfl
    rw [h4, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have h5 : 0 ≤ cdfExp r a := by
    unfold cdfExp; split_ifs with h
    · simp only [sub_nonneg, Real.exp_le_one_iff, Left.neg_nonpos_iff]; exact mul_nonneg hr.le h
    · exact le_rfl
  rw [h1, h2, h3, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h5]


lemma measurable_pdfExp (r : ℝ) : Measurable (pdfExp r) := by
  unfold pdfExp
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

lemma measurable_cdfExp (r : ℝ) : Measurable (cdfExp r) := by
  unfold cdfExp
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

lemma errorLaw_eq {m : ℕ} (u lam : Fin (m+1) → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin (m+1)) :
    errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i} =
      ∫⁻ x, ENNReal.ofReal (pdfExp (lam i) x) *
        ∏ j : Fin m, ENNReal.ofReal (1 - cdfExp (lam (i.succAbove j)) (u (i.succAbove j) - u i + x)) := by
  have hprob : ∀ j, IsProbabilityMeasure (expMeasure (lam j)) := fun j =>
    isProbabilityMeasure_expMeasure (hlam j)
  have hmp := measurePreserving_piFinSuccAbove (fun j => expMeasure (lam j)) i
  set T : Set (ℝ × (Fin m → ℝ)) :=
    {p | ∀ j' : Fin m, u (i.succAbove j') - p.2 j' ≤ u i - p.1} with hT
  have hTm : MeasurableSet T := by
    have : T = ⋂ j' : Fin m, {p : ℝ × (Fin m → ℝ) | u (i.succAbove j') - p.2 j' ≤ u i - p.1} := by
      ext p; simp [hT]
    rw [this]
    exact MeasurableSet.iInter fun j' => measurableSet_le (by fun_prop) (by fun_prop)
  have hS : {z : Fin (m+1) → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i} =
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' T := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hT, MeasurableEquiv.piFinSuccAbove_apply]
    constructor
    · intro h j'; exact h _ (Fin.succAbove_ne i j')
    · intro h j hj
      obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      exact h j'
  unfold errorLaw
  rw [hS, hmp.measure_preimage_equiv, Measure.prod_apply hTm]
  have hpdf : expMeasure (lam i) = volume.withDensity (fun x => ENNReal.ofReal (pdfExp (lam i) x)) := by
    unfold expMeasure gammaMeasure
    congr 1
    ext x
    have := exponentialPDF_eq (lam i) x
    unfold exponentialPDF exponentialPDFReal at this
    unfold gammaPDF
    simpa [pdfExp] using this
  have hfun : ∀ x : ℝ, (Measure.pi fun j : Fin m => expMeasure (lam (i.succAbove j)))
      (Prod.mk x ⁻¹' T) = ∏ j : Fin m,
        ENNReal.ofReal (1 - cdfExp (lam (i.succAbove j)) (u (i.succAbove j) - u i + x)) := by
    intro x
    have : Prod.mk x ⁻¹' T = Set.pi Set.univ
        (fun j' : Fin m => Set.Ici (u (i.succAbove j') - u i + x)) := by
      ext y
      simp only [hT, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Ici]
      refine forall_congr' fun j' => ?_
      constructor <;> intro h <;> linarith
    rw [this, Measure.pi_pi]
    refine Finset.prod_congr rfl fun j' _ => ?_
    exact expMeasure_Ici (hlam _) _
  simp_rw [hfun]
  rw [hpdf]
  rw [lintegral_withDensity_eq_lintegral_mul₀]
  · rfl
  · exact (measurable_pdfExp _).ennreal_ofReal.aemeasurable
  · refine Finset.measurable_prod _ (fun j' _ => ?_) |>.aemeasurable
    exact ((measurable_cdfExp _).comp (by fun_prop)).const_sub 1 |>.ennreal_ofReal


lemma one_sub_cdfExp (r a : ℝ) : 1 - cdfExp r a = Real.exp (-(r * max a 0)) := by
  unfold cdfExp
  split_ifs with h
  · rw [max_eq_left h]; ring
  · rw [max_eq_right (by linarith)]; simp

lemma pdfExp_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) : 0 ≤ pdfExp r x := by
  unfold pdfExp; split_ifs
  · positivity
  · exact le_rfl

lemma eq1_aux {m : ℕ} (u lam : Fin (m+1) → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin (m+1)) :
    choiceProb u lam i = ∫ x in Set.Ioi 0,
      (∏ j ∈ Finset.univ.erase i, (1 - cdfExp (lam j) (u j - u i + x))) * pdfExp (lam i) x := by
  set H : ℝ → ℝ := fun x => (∏ j ∈ Finset.univ.erase i, (1 - cdfExp (lam j) (u j - u i + x))) *
    pdfExp (lam i) x with hH
  have hprod : ∀ x, ∏ j ∈ Finset.univ.erase i, (1 - cdfExp (lam j) (u j - u i + x)) =
      ∏ j : Fin m, (1 - cdfExp (lam (i.succAbove j)) (u (i.succAbove j) - u i + x)) := by
    intro x
    have : Finset.univ.erase i = Finset.univ.map (Fin.succAboveEmb i) := by
      have h1 := Fin.univ_succAbove m i
      ext j
      by_cases hj : j = i
      · simp [hj]
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        simp
    rw [this, Finset.prod_map]; rfl
  have hnn : ∀ x, 0 ≤ H x := by
    intro x
    simp only [hH]
    refine mul_nonneg (Finset.prod_nonneg fun j _ => ?_) (pdfExp_nonneg (hlam i) x)
    rw [one_sub_cdfExp]; exact (Real.exp_pos _).le
  have hmeas : Measurable H := by
    simp only [hH]
    refine (Finset.measurable_prod _ (fun j _ => ?_)).mul (measurable_pdfExp _)
    exact ((measurable_cdfExp _).comp (by fun_prop)).const_sub 1
  have h1 : choiceProb u lam i = ∫ x, H x := by
    unfold choiceProb
    rw [errorLaw_eq u lam hlam i]
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hmeas.aestronglyMeasurable]
    congr 2
    funext x
    simp only [hH, hprod]
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => by rw [one_sub_cdfExp]; exact (Real.exp_pos _).le),
      ENNReal.ofReal_prod_of_nonneg (fun j _ => by rw [one_sub_cdfExp]; exact (Real.exp_pos _).le), mul_comm]
  rw [h1, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ici 0)]
  · exact integral_Ici_eq_integral_Ioi
  · intro x hx
    simp only [Set.mem_Ici, not_le] at hx
    simp [hH, pdfExp, not_le.mpr hx]

lemma eq1_second {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) :
    ∫ x in Set.Ioi 0,
      (∏ j ∈ Finset.univ.erase i, (1 - cdfExp (lam j) (u j - u i + x))) * pdfExp (lam i) x =
    ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) := by
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx : 0 < x := hx
  simp only [one_sub_cdfExp]
  rw [← Real.exp_sum, pdfExp, if_pos hx.le, mul_comm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [sub_self, zero_add, max_eq_left hx.le]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  rw [Finset.sum_neg_distrib]; ring

end HetExponomial.ChoiceProb

open HetExponomial.ChoiceProb in
theorem solution {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n) :
    choiceProb u lam i =
        ∫ z in Set.Ioi 0,
          (∏ j ∈ Finset.univ.erase i, (1 - cdfExp (lam j) (u j - u i + z))) * pdfExp (lam i) z ∧
      choiceProb u lam i =
        ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := eq1_aux u lam hlam i
  exact ⟨h, h.trans (eq1_second u lam i)⟩

