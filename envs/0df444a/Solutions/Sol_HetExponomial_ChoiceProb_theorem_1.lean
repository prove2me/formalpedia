-- Prove2me | solution 1 for HetExponomial.ChoiceProb.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:56:29.277824+00:00
-- url     : https://prove2.me/submissions/3dd9513f-2de2-4bf6-a0e1-09cb1a183739

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


lemma sum_affine {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (B : Finset (Fin n)) (z : ℝ) :
    ∑ j ∈ B, lam j * (u j - u i + z) =
      (∑ j ∈ B, lam j * (u j - u i)) + (∑ j ∈ B, lam j) * z := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma tailInt_eq {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j) (x c : ℝ)
    (hne : (betterThan u x).Nonempty) :
    tailInt u lam i x c =
      Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i))) *
        (Real.exp (-((∑ j ∈ betterThan u x, lam j) * c)) / (∑ j ∈ betterThan u x, lam j)) := by
  have hΛ : 0 < ∑ j ∈ betterThan u x, lam j := Finset.sum_pos (fun j _ => hlam j) hne
  unfold tailInt
  simp_rw [sum_affine]
  have : ∀ z : ℝ, Real.exp (-((∑ j ∈ betterThan u x, lam j * (u j - u i)) +
      (∑ j ∈ betterThan u x, lam j) * z)) =
      Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i))) *
        Real.exp ((-(∑ j ∈ betterThan u x, lam j)) * z) := by
    intro z; rw [← Real.exp_add]; congr 1; ring
  simp_rw [this]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  congr 1
  rw [neg_div_neg_eq]; congr 2; ring

lemma tail_integrableOn {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j) (x c : ℝ)
    (hne : (betterThan u x).Nonempty) :
    IntegrableOn (fun z => Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i + z)))) (Set.Ioi c) := by
  have hΛ : 0 < ∑ j ∈ betterThan u x, lam j := Finset.sum_pos (fun j _ => hlam j) hne
  simp_rw [sum_affine]
  have : ∀ z : ℝ, Real.exp (-((∑ j ∈ betterThan u x, lam j * (u j - u i)) +
      (∑ j ∈ betterThan u x, lam j) * z)) =
      Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i))) *
        Real.exp ((-(∑ j ∈ betterThan u x, lam j)) * z) := by
    intro z; rw [← Real.exp_add]; congr 1; ring
  simp_rw [this]
  exact (integrableOn_exp_mul_Ioi (by linarith) c).const_mul _

lemma sum_max_eq {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (x z : ℝ)
    (h1 : ∀ j, x ≤ u j → 0 ≤ u j - u i + z) (h2 : ∀ j, ¬ x ≤ u j → u j - u i + z ≤ 0) :
    ∑ j, lam j * max (u j - u i + z) 0 = ∑ j ∈ betterThan u x, lam j * (u j - u i + z) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => x ≤ u j)]
  have e1 : ∑ j ∈ Finset.univ.filter (fun j => x ≤ u j), lam j * max (u j - u i + z) 0 =
      ∑ j ∈ betterThan u x, lam j * (u j - u i + z) := by
    unfold betterThan
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [max_eq_left (h1 j (Finset.mem_filter.mp hj).2)]
  have e2 : ∑ j ∈ Finset.univ.filter (fun j => ¬ x ≤ u j), lam j * max (u j - u i + z) 0 = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [max_eq_right (h2 j (Finset.mem_filter.mp hj).2)]; simp
  rw [e1, e2, add_zero]

lemma level_exists {n : ℕ} (u : Fin n → ℝ) (j : Fin n) : ∃ v, level u v = u j := by
  have h1 : u j ∈ levels u := Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have h := Finset.range_orderEmbOfFin (levels u) (rfl : (levels u).card = (levels u).card)
  have h2 : u j ∈ Set.range ((levels u).orderEmbOfFin (rfl : (levels u).card = (levels u).card)) := by
    rw [h]; exact_mod_cast h1
  obtain ⟨v, hv⟩ := h2
  exact ⟨v, hv⟩

lemma exists_eq_level {n : ℕ} (u : Fin n → ℝ) (v : Fin (levels u).card) : ∃ j, u j = level u v := by
  have h := Finset.orderEmbOfFin_mem (levels u) (rfl : (levels u).card = (levels u).card) v
  have h' : level u v ∈ Finset.image u Finset.univ := h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h'
  exact ⟨j, hj⟩


/-- the summand in (16) -/
noncomputable def Tw {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (w : Fin (levels u).card) : ℝ :=
  tailInt u lam i (level u w) (u i - level u w) -
    if 0 < w.val then
      tailInt u lam i (level u w)
        (u i - level u ⟨w.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.isLt⟩)
    else 0

lemma nonempty_better {n : ℕ} (u : Fin n → ℝ) (w : Fin (levels u).card) :
    (betterThan u (level u w)).Nonempty := by
  obtain ⟨j, hj⟩ := exists_eq_level u w
  exact ⟨j, by simp [betterThan, hj]⟩

lemma g_eq_on {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (w : Fin (levels u).card) (z : ℝ)
    (hz1 : u i - level u w < z) (hz2 : ∀ p : Fin (levels u).card, p < w → z ≤ u i - level u p) :
    lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
      lam i * Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - u i + z))) := by
  congr 3
  refine sum_max_eq u lam i _ z (fun j hj => by linarith) (fun j hj => ?_)
  obtain ⟨v, hv⟩ := level_exists u j
  have hvw : v < w := by
    rw [← (level u).lt_iff_lt, hv]; exact not_le.mp hj
  have := hz2 v hvw
  rw [← hv]; linarith

lemma eq16_induct {n : ℕ} (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n)
    (k : Fin (levels u).card) :
    ∀ m : ℕ, ∀ hm : m < (levels u).card, m ≤ k.val →
      IntegrableOn (fun z => lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)))
          (Set.Ioi (u i - level u ⟨m, hm⟩)) ∧
      ∫ z in Set.Ioi (u i - level u ⟨m, hm⟩),
          lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
        lam i * ∑ w ∈ Finset.univ.filter (fun w : Fin (levels u).card => w ≤ ⟨m, hm⟩), Tw u lam i w := by
  intro m
  induction m with
  | zero =>
    intro hm _
    have hcongr : Set.EqOn (fun z => lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)))
        (fun z => lam i * Real.exp (-(∑ j ∈ betterThan u (level u ⟨0, hm⟩), lam j * (u j - u i + z))))
        (Set.Ioi (u i - level u ⟨0, hm⟩)) := by
      intro z hz
      exact g_eq_on u lam i ⟨0, hm⟩ z hz (fun p hp => absurd hp (by simp [Fin.lt_def]))
    have hint : IntegrableOn (fun z => lam i * Real.exp (-(∑ j ∈ betterThan u (level u ⟨0, hm⟩), lam j * (u j - u i + z))))
        (Set.Ioi (u i - level u ⟨0, hm⟩)) :=
      (tail_integrableOn u lam i hlam (level u ⟨0, hm⟩) (u i - level u ⟨0, hm⟩)
      (nonempty_better u ⟨0, hm⟩)).const_mul (lam i)
    refine ⟨hint.congr_fun hcongr.symm measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]
    have hfilt : Finset.univ.filter (fun w : Fin (levels u).card => w ≤ ⟨0, hm⟩) = {⟨0, hm⟩} := by
      ext w; simp [Fin.le_def, Fin.ext_iff]
    rw [hfilt, Finset.sum_singleton]
    unfold Tw tailInt
    simp
  | succ m ih =>
    intro hm hmk
    have hm' : m < (levels u).card := by omega
    obtain ⟨ihI, ihV⟩ := ih hm' (by omega)
    set w : Fin (levels u).card := ⟨m + 1, hm⟩ with hw
    set p : Fin (levels u).card := ⟨m, hm'⟩ with hp
    have hpw : p < w := by simp [hw, hp, Fin.lt_def]
    have hlev : level u p < level u w := (level u).lt_iff_lt.mpr hpw
    have hle : u i - level u w ≤ u i - level u p := by linarith
    have hcongr : Set.EqOn (fun z => lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)))
        (fun z => lam i * Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - u i + z))))
        (Set.Ioc (u i - level u w) (u i - level u p)) := by
      intro z hz
      refine g_eq_on u lam i w z hz.1 (fun q hq => ?_)
      have : q ≤ p := by simp only [hw, hp, Fin.lt_def, Fin.le_def] at hq ⊢; omega
      have : level u q ≤ level u p := (level u).le_iff_le.mpr this
      linarith [hz.2]
    have hE1 := tail_integrableOn u lam i hlam (level u w) (u i - level u w) (nonempty_better u w)
    have hE2 := tail_integrableOn u lam i hlam (level u w) (u i - level u p) (nonempty_better u w)
    have hIoc : IntegrableOn (fun z => lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)))
        (Set.Ioc (u i - level u w) (u i - level u p)) := by
      have h0 : IntegrableOn (fun z => lam i * Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - u i + z))))
          (Set.Ioi (u i - level u w)) := hE1.const_mul (lam i)
      have := h0.mono_set (fun x (hx : x ∈ Set.Ioc (u i - level u w) (u i - level u p)) => hx.1)
      exact this.congr_fun hcongr.symm measurableSet_Ioc
    have hunion : Set.Ioc (u i - level u w) (u i - level u p) ∪ Set.Ioi (u i - level u p) =
        Set.Ioi (u i - level u w) := Set.Ioc_union_Ioi_eq_Ioi hle
    refine ⟨?_, ?_⟩
    · rw [← hunion]; exact hIoc.union ihI
    · rw [← hunion, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc ihI, ihV]
      rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_const_mul]
      have hsplit : ∫ z in Set.Ioc (u i - level u w) (u i - level u p),
          Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - u i + z))) =
          tailInt u lam i (level u w) (u i - level u w) -
            tailInt u lam i (level u w) (u i - level u p) := by
        have h := setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (hE1.mono_set Set.Ioc_subset_Ioi_self) hE2
        rw [hunion] at h
        unfold tailInt
        linarith
      rw [hsplit]
      have hfilt : Finset.univ.filter (fun v : Fin (levels u).card => v ≤ w) =
          insert w (Finset.univ.filter (fun v : Fin (levels u).card => v ≤ p)) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          hw, hp, Fin.le_def, Fin.ext_iff]; omega
      have hnot : w ∉ Finset.univ.filter (fun v : Fin (levels u).card => v ≤ p) := by
        simp [hw, hp, Fin.le_def]
      rw [hfilt, Finset.sum_insert hnot]
      have hTw : Tw u lam i w = tailInt u lam i (level u w) (u i - level u w) -
            tailInt u lam i (level u w) (u i - level u p) := by
        unfold Tw
        rw [if_pos (by simp [hw])]
        have e : (⟨w.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.isLt⟩ : Fin (levels u).card) = p :=
          Fin.ext (by simp [hw, hp])
        rw [e]
      rw [hTw]; ring

theorem eq16_core {n : ℕ} (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n)
    (k : Fin (levels u).card) (hk : level u k = u i) :
    ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
      lam i * ∑ w ∈ Finset.univ.filter (fun w => w ≤ k), Tw u lam i w := by
  have := (eq16_induct u lam hlam i k k.val k.isLt le_rfl).2
  simpa [hk] using this


/-! ### Algebra for Theorem 1 -/

noncomputable def Lam {n : ℕ} (u lam : Fin n → ℝ) (x : ℝ) : ℝ := ∑ j ∈ betterThan u x, lam j

noncomputable def Rr {n : ℕ} (u lam : Fin n → ℝ) (x y : ℝ) : ℝ :=
  ∑ j ∈ betterThan u x, lam j * (u j - y)

noncomputable def Lp {n : ℕ} (u lam : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x < u j), lam j

lemma Lam_pos {n : ℕ} (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (w : Fin (levels u).card) :
    0 < Lam u lam (level u w) :=
  Finset.sum_pos (fun j _ => hlam j) (nonempty_better u w)

lemma tailInt_form {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j) (x y : ℝ)
    (hne : (betterThan u x).Nonempty) :
    tailInt u lam i x (u i - y) = Real.exp (-(Rr u lam x y)) / Lam u lam x := by
  rw [tailInt_eq u lam i hlam x _ hne, ← mul_div_assoc, ← Real.exp_add]
  unfold Rr Lam
  congr 2
  have : ∑ j ∈ betterThan u x, lam j * (u j - y) =
      ∑ j ∈ betterThan u x, lam j * (u j - u i) + (∑ j ∈ betterThan u x, lam j) * (u i - y) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]; ring

lemma B_split {n : ℕ} (u : Fin n → ℝ) (f : Fin n → ℝ) (x : ℝ) :
    ∑ j ∈ betterThan u x, f j =
      ∑ j ∈ Finset.univ.filter (fun j => u j = x), f j +
        ∑ j ∈ Finset.univ.filter (fun j => x < u j), f j := by
  rw [← Finset.sum_filter_add_sum_filter_not (betterThan u x) (fun j => x < u j)]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j; simp only [betterThan, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
    · intro h; exact ⟨h.ge, h.le⟩
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j; simp only [betterThan, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨h.le, h⟩

lemma lt_level_iff {n : ℕ} (u : Fin n → ℝ) (w w' : Fin (levels u).card) (hw : w.val + 1 = w'.val)
    (j : Fin n) : level u w < u j ↔ level u w' ≤ u j := by
  obtain ⟨v, hv⟩ := level_exists u j
  rw [← hv, (level u).lt_iff_lt, (level u).le_iff_le]
  simp only [Fin.lt_def, Fin.le_def]; omega

lemma Lp_eq_Lam {n : ℕ} (u lam : Fin n → ℝ) (w w' : Fin (levels u).card) (hw : w.val + 1 = w'.val) :
    Lp u lam (level u w) = Lam u lam (level u w') := by
  unfold Lp Lam betterThan
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j; simp [lt_level_iff u w w' hw]

lemma Rr_shift {n : ℕ} (u lam : Fin n → ℝ) (w w' : Fin (levels u).card) (hw : w.val + 1 = w'.val) :
    Rr u lam (level u w) (level u w) = Rr u lam (level u w') (level u w) := by
  unfold Rr
  rw [B_split u (fun j => lam j * (u j - level u w)) (level u w)]
  have h0 : ∑ j ∈ Finset.univ.filter (fun j => u j = level u w), lam j * (u j - level u w) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [(Finset.mem_filter.mp hj).2]; simp
  rw [h0, zero_add]
  unfold betterThan
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j; simp [lt_level_iff u w w' hw]

lemma fiber_sum {n : ℕ} (u lam : Fin n → ℝ) (w w' : Fin (levels u).card) (hw : w.val + 1 = w'.val) :
    ∑ j ∈ Finset.univ.filter (fun j => u j = level u w), lam j =
      Lam u lam (level u w) - Lam u lam (level u w') := by
  rw [← Lp_eq_Lam u lam w w' hw]
  unfold Lam Lp
  rw [B_split u lam (level u w)]
  ring


lemma Tw_zero {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j)
    (w : Fin (levels u).card) (hw : w.val = 0) :
    Tw u lam i w = Real.exp (-(Rr u lam (level u w) (level u w))) / Lam u lam (level u w) := by
  unfold Tw
  rw [if_neg (by omega), sub_zero, tailInt_form u lam i hlam _ _ (nonempty_better u w)]

lemma Tw_succ {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j)
    (w p : Fin (levels u).card) (hw : p.val + 1 = w.val) :
    Tw u lam i w = Real.exp (-(Rr u lam (level u w) (level u w))) / Lam u lam (level u w) -
      Real.exp (-(Rr u lam (level u p) (level u p))) / Lam u lam (level u w) := by
  unfold Tw
  rw [if_pos (by omega)]
  have e : (⟨w.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.isLt⟩ : Fin (levels u).card) = p :=
    Fin.ext (by simp; omega)
  rw [e, tailInt_form u lam i hlam _ _ (nonempty_better u w),
    tailInt_form u lam i hlam _ _ (nonempty_better u w), Rr_shift u lam p w hw]

lemma claimC {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j) :
    ∀ m : ℕ, ∀ hm : m < (levels u).card,
      ∑ w ∈ Finset.univ.filter (fun w : Fin (levels u).card => w ≤ ⟨m, hm⟩), Tw u lam i w =
        Real.exp (-(Rr u lam (level u ⟨m, hm⟩) (level u ⟨m, hm⟩))) / Lam u lam (level u ⟨m, hm⟩) +
        ∑ w ∈ Finset.univ.filter (fun w : Fin (levels u).card => w < ⟨m, hm⟩),
          Real.exp (-(Rr u lam (level u w) (level u w))) *
            (1 / Lam u lam (level u w) - 1 / Lp u lam (level u w)) := by
  intro m
  induction m with
  | zero =>
    intro hm
    have hfilt : Finset.univ.filter (fun w : Fin (levels u).card => w ≤ ⟨0, hm⟩) = {⟨0, hm⟩} := by
      ext w; simp [Fin.le_def, Fin.ext_iff]
    have hfilt2 : Finset.univ.filter (fun w : Fin (levels u).card => w < ⟨0, hm⟩) = ∅ := by
      ext w; simp [Fin.lt_def]
    rw [hfilt, hfilt2, Finset.sum_singleton, Finset.sum_empty, add_zero]
    exact Tw_zero u lam i hlam _ rfl
  | succ m ih =>
    intro hm
    have hm' : m < (levels u).card := by omega
    set w : Fin (levels u).card := ⟨m + 1, hm⟩ with hw
    set p : Fin (levels u).card := ⟨m, hm'⟩ with hp
    have hfilt : Finset.univ.filter (fun v : Fin (levels u).card => v ≤ w) =
        insert w (Finset.univ.filter (fun v : Fin (levels u).card => v ≤ p)) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        hw, hp, Fin.le_def, Fin.ext_iff]; omega
    have hnot : w ∉ Finset.univ.filter (fun v : Fin (levels u).card => v ≤ p) := by
      simp [hw, hp, Fin.le_def]
    have hfilt2 : Finset.univ.filter (fun v : Fin (levels u).card => v < w) =
        insert p (Finset.univ.filter (fun v : Fin (levels u).card => v < p)) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        hw, hp, Fin.lt_def, Fin.ext_iff]; omega
    have hnot2 : p ∉ Finset.univ.filter (fun v : Fin (levels u).card => v < p) := by
      simp [hp, Fin.lt_def]
    have hpw : p.val + 1 = w.val := rfl
    rw [hfilt, Finset.sum_insert hnot, hfilt2, Finset.sum_insert hnot2, ih hm',
      Tw_succ u lam i hlam w p hpw]
    have hL : Lp u lam (level u p) = Lam u lam (level u w) := Lp_eq_Lam u lam p w hpw
    rw [hL]
    ring


lemma term_fiber {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j)
    (w w' : Fin (levels u).card) (hw : w.val + 1 = w'.val) :
    ∑ j ∈ Finset.univ.filter (fun j => u j = level u w), lam i / Lplus u lam j * G u lam j =
      lam i * (Real.exp (-(Rr u lam (level u w) (level u w))) *
        (1 / Lp u lam (level u w) - 1 / Lam u lam (level u w))) := by
  have hΛ := Lam_pos u lam hlam w
  have hΛ' := Lam_pos u lam hlam w'
  rw [← Lp_eq_Lam u lam w w' hw] at hΛ'
  have hterm : ∀ j ∈ Finset.univ.filter (fun j => u j = level u w),
      lam i / Lplus u lam j * G u lam j =
        lam j * (lam i / Lp u lam (level u w) * (1 / Lam u lam (level u w)) *
          Real.exp (-(Rr u lam (level u w) (level u w)))) := by
    intro j hj
    have hj' : u j = level u w := (Finset.mem_filter.mp hj).2
    have e1 : Lplus u lam j = Lp u lam (level u w) := by
      unfold Lplus Lp strictlyBetter; rw [hj']
    have e2 : Lsum u lam j = Lam u lam (level u w) := by
      unfold Lsum Lam better; rw [hj']
    have e3 : ∑ m ∈ better u j, lam m * (u m - u j) = Rr u lam (level u w) (level u w) := by
      unfold Rr better; rw [hj']
    unfold G
    rw [e1, e2, e3]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, fiber_sum u lam w w' hw,
    ← Lp_eq_Lam u lam w w' hw]
  field_simp

lemma worse_sum {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j)
    (k : Fin (levels u).card) (hk : level u k = u i) :
    ∑ j ∈ strictlyWorse u i, lam i / Lplus u lam j * G u lam j =
      lam i * ∑ w ∈ Finset.univ.filter (fun w : Fin (levels u).card => w < k),
        Real.exp (-(Rr u lam (level u w) (level u w))) *
          (1 / Lp u lam (level u w) - 1 / Lam u lam (level u w)) := by
  choose idx hidx using level_exists u
  rw [← Finset.sum_fiberwise_of_maps_to (s := strictlyWorse u i)
    (t := Finset.univ.filter (fun w : Fin (levels u).card => w < k)) (g := idx)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hwk : w < k := (Finset.mem_filter.mp hw).2
    have hw' : w.val + 1 < (levels u).card := by
      have := hwk; simp only [Fin.lt_def] at this; have := k.isLt; omega
    rw [← term_fiber u lam i hlam w ⟨w.val + 1, hw'⟩ rfl]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [strictlyWorse, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h2⟩; rw [← hidx j, h2]
    · intro h
      have h2 : idx j = w := by
        apply (level u).injective
        rw [hidx j, h]
      refine ⟨?_, h2⟩
      rw [h, ← hk]; exact (level u).lt_iff_lt.mpr hwk
  · intro j hj
    have hj' : u j < u i := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← (level u).lt_iff_lt, hidx j, hk]; exact hj'

theorem theorem_1_core {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n) :
    choiceProb u lam i =
      G u lam i - ∑ k ∈ strictlyWorse u i, lam i / Lplus u lam k * G u lam k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : choiceProb u lam i = ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) :=
    (eq1_aux u lam hlam i).trans (eq1_second u lam i)
  obtain ⟨k, hk⟩ := level_exists u i
  rw [h1, eq16_core u lam hlam i k hk, worse_sum u lam i hlam k hk]
  have h3 := claimC u lam i hlam k.val k.isLt
  have e : (⟨k.val, k.isLt⟩ : Fin (levels u).card) = k := Fin.eta k k.isLt
  rw [e] at h3
  rw [h3]
  have hG : G u lam i = lam i * (Real.exp (-(Rr u lam (level u k) (level u k))) / Lam u lam (level u k)) := by
    unfold G Lsum Rr Lam better
    rw [hk]; ring
  rw [hG, mul_add, sub_eq_add_neg, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end HetExponomial.ChoiceProb

open HetExponomial.ChoiceProb in
theorem solution {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n) :
    choiceProb u lam i =
      G u lam i - ∑ k ∈ strictlyWorse u i, lam i / Lplus u lam k * G u lam k :=
  theorem_1_core hn u lam hlam i
