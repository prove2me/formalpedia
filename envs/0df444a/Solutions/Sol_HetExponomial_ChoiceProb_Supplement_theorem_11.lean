-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:07:16.265657+00:00
-- url     : https://prove2.me/submissions/f2697d3c-ed39-4267-93d9-cbb2be62cffc

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (hα : ∀ i j, α i + 1 / lam i ≤ α j + 1 / lam j → α i ≤ α j)
    (σ : Fin n ≃ Fin n) (hσ : Monotone (fun s => α (σ s) + 1 / lam (σ s))) :
    (∃ ustar : Fin n → ℝ, IsOnePass α lam σ ustar) ∧
      ∀ ustar : Fin n → ℝ, IsOnePass α lam σ ustar →
        (∀ s : Fin n, 0 < s.val →
            ∃! x : ℝ, α (σ s) - x = tauCond α lam (solvedBefore σ s.val) ustar (σ s) x) ∧
          IsPriceNE α β lam (eqPrices α β ustar) ∧
          (∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar) ∧
          ∀ s t : Fin n, t.val + 1 = s.val →
            ustar (σ t) ≤ ustar (σ s) ∧
              (ustar (σ t) = ustar (σ s) → α (σ s) = α (σ t) ∧ lam (σ s) = lam (σ t)) := by
                classical
                letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
                letI (j : Fin n) : IsProbabilityMeasure (expMeasure (lam j)) :=
                  isProbabilityMeasure_expMeasure (hlam j)
                have hsurv (j : Fin n) (x : ℝ) :
                    (expMeasure (lam j) (Set.Ici x)).toReal = Real.exp (-(lam j * max 0 x)) := by
                  letI : NullSingletonClass (expMeasure (lam j)) := by
                    unfold expMeasure gammaMeasure
                    infer_instance
                  rw [← measure_congr (Ioi_ae_eq_Ici (μ := expMeasure (lam j)) (a := x))]
                  rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _)]
                  rw [ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top _ _)]
                  simp only [measure_univ, ENNReal.toReal_one]
                  change 1 - (expMeasure (lam j)).real (Set.Iic x) = _
                  rw [← cdf_eq_real, cdf_expMeasure_eq (hlam j)]
                  split_ifs with hx
                  · rw [max_eq_right hx]
                    ring
                  · rw [max_eq_left (le_of_not_ge hx)]
                    simp
                have hslice (u : Fin n → ℝ) (i : Fin n) :
                    errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i} =
                      ∫⁻ z, ∏ j ∈ Finset.univ.erase i,
                        expMeasure (lam j) (Set.Ici (u j - u i + z)) ∂expMeasure (lam i) := by
                  let A : Set (Fin n → ℝ) := {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}
                  have hA : MeasurableSet A := by
                    dsimp [A]
                    simp only [Set.setOf_forall]
                    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
                      measurableSet_le (measurable_const.sub (measurable_pi_apply j))
                        (measurable_const.sub (measurable_pi_apply i))
                  let f : (Fin n → ℝ) → ENNReal := A.indicator (fun _ => 1)
                  have hf : Measurable f := measurable_const.indicator hA
                  change Measure.pi (fun j => expMeasure (lam j)) A = _
                  rw [← lintegral_indicator_one hA]
                  change (∫⁻ x, f x ∂Measure.pi (fun j => expMeasure (lam j))) = _
                  rw [lintegral_eq_lmarginal_univ (fun _ => 0),
                    lmarginal_erase f hf (Finset.mem_univ i)]
                  apply lintegral_congr
                  intro z
                  unfold lmarginal
                  let B : Set ((j : ↥(Finset.univ.erase i)) → ℝ) :=
                    Set.univ.pi (fun j => Set.Ici (u j - u i + z))
                  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ici
                  have heq : (fun y : (j : ↥(Finset.univ.erase i)) → ℝ =>
                      f (Function.updateFinset (Function.update (fun _ => 0) i z)
                        (Finset.univ.erase i) y)) = B.indicator (fun _ => 1) := by
                    funext y
                    have hm : Function.updateFinset (Function.update (fun _ => 0) i z)
                        (Finset.univ.erase i) y ∈ A ↔ y ∈ B := by
                      simp only [A, B, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Ici]
                      simp only [Function.updateFinset_def, Finset.mem_erase, Finset.mem_univ,
                        and_true, ne_eq, not_false_eq_true, Function.update_self, not_true_eq_false,
                        ↓reduceDIte]
                      constructor
                      · intro h j
                        have hj : (j : Fin n) ≠ i := (Finset.mem_erase.mp j.property).1
                        have hh := h j hj
                        simp only [dif_pos hj] at hh
                        linarith
                      · intro h j hj
                        simp only [dif_pos hj]
                        have hh := h ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
                        linarith
                    simp only [f, Set.indicator_apply, hm]
                  rw [heq, lintegral_indicator hB, lintegral_const]
                  simp only [one_mul, Measure.restrict_apply_univ]
                  change Measure.pi (fun j : ↥(Finset.univ.erase i) => expMeasure (lam j))
                    (Set.univ.pi (fun j => Set.Ici (u j - u i + z))) = _
                  rw [Measure.pi_pi]
                  simpa using (Finset.prod_coe_sort (Finset.univ.erase i)
                    (fun j => expMeasure (lam j) (Set.Ici (u j - u i + z))))
                have hprob (u : Fin n → ℝ) (i : Fin n) :
                    choiceProb u lam i = ∫ z : ℝ in Set.Ici 0,
                      lam i * Real.exp (-(lam i * z +
                        ∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - u i + z))) := by
                  let F : ℝ → ℝ := fun z => Real.exp (-(∑ j ∈ Finset.univ.erase i,
                    lam j * max 0 (u j - u i + z)))
                  have hF : Continuous F := by dsimp [F]; fun_prop
                  have hFn (z : ℝ) : 0 ≤ F z := (Real.exp_pos _).le
                  have he (z : ℝ) : (∏ j ∈ Finset.univ.erase i,
                      expMeasure (lam j) (Set.Ici (u j - u i + z))) = ENNReal.ofReal (F z) := by
                    have hs (j : Fin n) (x : ℝ) : expMeasure (lam j) (Set.Ici x) =
                        ENNReal.ofReal (Real.exp (-(lam j * max 0 x))) := by
                      rw [← hsurv j x, ENNReal.ofReal_toReal (measure_ne_top _ _)]
                    simp_rw [hs]
                    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
                    congr 1
                    simp only [F, ← Real.exp_sum, Finset.sum_neg_distrib]
                  rw [choiceProb, hslice u i]
                  simp_rw [he]
                  rw [← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hFn)
                    hF.aestronglyMeasurable]
                  change (∫ z, F z ∂volume.withDensity (exponentialPDF (lam i))) = _
                  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF (lam i))
                    (measurable_exponentialPDFReal _).ennreal_ofReal
                    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
                  rw [← integral_indicator measurableSet_Ici]
                  apply integral_congr_ae
                  filter_upwards [] with z
                  by_cases hz : 0 ≤ z
                  · rw [Set.indicator_of_mem (show z ∈ Set.Ici (0 : ℝ) from hz), exponentialPDF_of_nonneg hz,
                      ENNReal.toReal_ofReal (mul_nonneg (hlam i).le (Real.exp_pos _).le)]
                    simp only [smul_eq_mul, F]
                    rw [mul_assoc, ← Real.exp_add]
                    congr 2
                    ring
                  · rw [Set.indicator_of_notMem (show z ∉ Set.Ici (0 : ℝ) from hz), exponentialPDF_of_neg (lt_of_not_ge hz)]
                    simp
                have hsub (g : ℝ → ℝ) (x : ℝ) :
                    (∫ z : ℝ in Set.Ici 0, g (x - z)) = ∫ t : ℝ in Set.Iic x, g t := by
                  have h := (volume.measurePreserving_sub_left x).setIntegral_preimage_emb
                    (Homeomorph.subLeft x).measurableEmbedding g (Set.Iic x)
                  have he : (fun t : ℝ => x - t) ⁻¹' Set.Iic x = Set.Ici 0 := by
                    ext z
                    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
                    constructor <;> intro hz <;> linarith
                  rw [he] at h
                  exact h
                let K : (Fin n → ℝ) → Fin n → ℝ → ℝ := fun u i t =>
                  Real.exp (lam i * t - ∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - t))
                have hKcont (u : Fin n → ℝ) (i : Fin n) : Continuous (K u i) := by
                  dsimp [K]; fun_prop
                have hKint (u : Fin n → ℝ) (i : Fin n) (x : ℝ) :
                    IntegrableOn (K u i) (Set.Iic x) := by
                  refine (integrableOn_exp_mul_Iic (hlam i) x).mono'
                    (hKcont u i).aestronglyMeasurable ?_
                  filter_upwards [] with t
                  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                  apply Real.exp_le_exp.mpr
                  exact sub_le_self _ (Finset.sum_nonneg fun j _ => mul_nonneg (hlam j).le (le_max_left _ _))
                have hcum (u : Fin n → ℝ) (i : Fin n) :
                    choiceProb u lam i = lam i * Real.exp (-(lam i * u i)) *
                      ∫ t : ℝ in Set.Iic (u i), K u i t := by
                  rw [hprob u i, ← integral_const_mul, ← hsub
                    (fun t => lam i * Real.exp (-(lam i * u i)) * K u i t) (u i)]
                  apply setIntegral_congr_fun measurableSet_Ici
                  intro z hz
                  simp only [K]
                  rw [mul_assoc, ← Real.exp_add]
                  congr 2
                  have hs : (∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - (u i - z))) =
                      ∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - u i + z) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    congr 2
                    ring
                  rw [hs]
                  ring
                have hKupd (u : Fin n → ℝ) (i : Fin n) (x : ℝ) :
                    K (Function.update u i x) i = K u i := by
                  funext t
                  dsimp [K]
                  congr 2
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
                have hFTC (u : Fin n → ℝ) (i : Fin n) (x : ℝ) :
                    HasDerivAt (fun a => ∫ t : ℝ in Set.Iic a, K u i t) (K u i x) x := by
                  have he (a : ℝ) : (∫ t : ℝ in Set.Iic a, K u i t) =
                      (∫ t : ℝ in Set.Iic x, K u i t) + ∫ t : ℝ in x..a, K u i t := by
                    rw [← intervalIntegral.integral_Iic_sub_Iic (hKint u i x) (hKint u i a)]
                    ring
                  have hd := (intervalIntegral.integral_hasDerivAt_right
                    ((hKcont u i).intervalIntegrable x x)
                    (hKcont u i).stronglyMeasurable.stronglyMeasurableAtFilter
                    (hKcont u i).continuousAt).const_add (∫ t : ℝ in Set.Iic x, K u i t)
                  apply hd.congr_of_eventuallyEq
                  exact Filter.Eventually.of_forall he
                let E : (Fin n → ℝ) → Fin n → ℝ := fun u i =>
                  Real.exp (-(∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - u i)))
                have hderiv (u : Fin n → ℝ) (i : Fin n) :
                    HasDerivAt (fun x => choiceProb (Function.update u i x) lam i)
                      (lam i * (E u i - choiceProb u lam i)) (u i) := by
                  have he (x : ℝ) : choiceProb (Function.update u i x) lam i =
                      lam i * Real.exp (-(lam i * x)) * ∫ t : ℝ in Set.Iic x, K u i t := by
                    rw [hcum, Function.update_self, hKupd]
                  simp_rw [he]
                  convert (((((hasDerivAt_id (u i)).const_mul (lam i)).neg.exp).const_mul (lam i)).mul
                    (hFTC u i (u i))) using 1 <;> try rfl
                  try dsimp [E, K]
                  rw [hcum u i]
                  have he : Real.exp (-(lam i * u i)) *
                      Real.exp (lam i * u i - ∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - u i)) =
                      Real.exp (-(∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - u i))) := by
                    rw [← Real.exp_add]
                    congr 1
                    ring
                  dsimp only [K]
                  linear_combination -lam i * he
                have hmax (a z : ℝ) (hz : 0 ≤ z) :
                    max 0 (a + z) = max 0 a + max 0 (z - max 0 (-a)) := by
                  by_cases ha : 0 ≤ a
                  · rw [max_eq_right ha, max_eq_left (by linarith : -a ≤ 0), sub_zero,
                      max_eq_right (show (0 : ℝ) ≤ z from hz), max_eq_right (by linarith : 0 ≤ a + z)]
                  · rw [max_eq_left (le_of_not_ge ha), max_eq_right (by linarith : 0 ≤ -a), zero_add]
                    congr 1
                    ring
                let T : (Fin n → ℝ) → Fin n → ℝ → ℝ := fun u i z =>
                  Real.exp (-(lam i * z + ∑ j ∈ Finset.univ.erase i,
                    lam j * max 0 (z - max 0 (u i - u j))))
                let J : (Fin n → ℝ) → Fin n → ℝ := fun u i => ∫ z : ℝ in Set.Ici 0, T u i z
                have hTcont (u : Fin n → ℝ) (i : Fin n) : Continuous (T u i) := by
                  dsimp [T]; fun_prop
                have hTle (u : Fin n → ℝ) (i : Fin n) (z : ℝ) :
                    T u i z ≤ Real.exp (-(lam i * z)) := by
                  apply Real.exp_le_exp.mpr
                  have : 0 ≤ ∑ j ∈ Finset.univ.erase i, lam j * max 0 (z - max 0 (u i - u j)) :=
                    Finset.sum_nonneg fun j _ => mul_nonneg (hlam j).le (le_max_left _ _)
                  linarith
                have hTint (u : Fin n → ℝ) (i : Fin n) : IntegrableOn (T u i) (Set.Ici 0) := by
                  have hi : IntegrableOn (fun z : ℝ => Real.exp (-(lam i * z))) (Set.Ici 0) := by
                    rw [integrableOn_Ici_iff_integrableOn_Ioi]
                    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (neg_neg_of_pos (hlam i)) 0
                  apply hi.mono' (hTcont u i).aestronglyMeasurable
                  exact Filter.Eventually.of_forall fun z => by
                    have ht : 0 < T u i z := Real.exp_pos _
                    simpa only [Real.norm_eq_abs, abs_of_pos ht] using hTle u i z
                have hJprob (u : Fin n → ℝ) (i : Fin n) :
                    choiceProb u lam i = lam i * E u i * J u i := by
                  rw [hprob, ← integral_const_mul]
                  apply setIntegral_congr_fun measurableSet_Ici
                  intro z hz
                  dsimp [E, T]
                  rw [mul_assoc, ← Real.exp_add]
                  congr 2
                  have hs : (∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - u i + z)) =
                      (∑ j ∈ Finset.univ.erase i, lam j * max 0 (u j - u i)) +
                      ∑ j ∈ Finset.univ.erase i, lam j * max 0 (z - max 0 (u i - u j)) := by
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [hmax _ _ hz]
                    have he : -(u j - u i) = u i - u j := by ring
                    rw [he, mul_add]
                  rw [hs]
                  ring
                have hJpos (u : Fin n → ℝ) (i : Fin n) : 0 < J u i := by
                  apply (setIntegral_pos_iff_support_of_nonneg_ae
                    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le) (hTint u i)).mpr
                  have hs : Function.support (T u i) = Set.univ := by
                    ext z
                    exact iff_true_intro (Real.exp_pos _).ne'
                  rw [hs, Set.univ_inter]
                  simp
                have hIntLt (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
                    (hfi : IntegrableOn f (Set.Ici 0)) (hgi : IntegrableOn g (Set.Ici 0))
                    (hle : ∀ z : ℝ, 0 ≤ z → f z ≤ g z) (hstrict : ∃ z : ℝ, 0 < z ∧ f z < g z) :
                    (∫ z : ℝ in Set.Ici 0, f z) < ∫ z : ℝ in Set.Ici 0, g z := by
                  have hnon : 0 ≤ᵐ[volume.restrict (Set.Ici (0 : ℝ))] (fun z => g z - f z) := by
                    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
                    exact sub_nonneg.mpr (hle z hz)
                  have hp : 0 < ∫ z : ℝ in Set.Ici 0, (g z - f z) := by
                    apply (setIntegral_pos_iff_support_of_nonneg_ae hnon (hgi.sub hfi)).mpr
                    have ho : IsOpen ({z : ℝ | f z < g z} ∩ Set.Ioi 0) :=
                      (isOpen_lt hf hg).inter isOpen_Ioi
                    obtain ⟨z, hz, hzg⟩ := hstrict
                    have hm := ho.measure_pos (μ := volume) ⟨z, hzg, hz⟩
                    apply hm.trans_le
                    apply measure_mono
                    intro t ht
                    exact ⟨(sub_pos.mpr ht.1).ne', show 0 ≤ t from le_of_lt ht.2⟩
                  rw [integral_sub hgi hfi] at hp
                  linarith
                have hJlt (u : Fin n → ℝ) (i : Fin n) : J u i < 1 / lam i := by
                  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
                    by_cases hi : i = ⟨0, by omega⟩
                    · refine ⟨⟨1, by omega⟩, ?_⟩
                      intro he
                      have hv := congrArg Fin.val he
                      simp [hi] at hv
                    · exact ⟨⟨0, by omega⟩, Ne.symm hi⟩
                  have hgi : IntegrableOn (fun z : ℝ => Real.exp (-(lam i * z))) (Set.Ici 0) := by
                    rw [integrableOn_Ici_iff_integrableOn_Ioi]
                    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (neg_neg_of_pos (hlam i)) 0
                  have hl := hIntLt (T u i) (fun z : ℝ => Real.exp (-(lam i * z)))
                    (hTcont u i) (by fun_prop) (hTint u i) hgi (fun z _ => hTle u i z) (by
                      let z := max 0 (u i - u j) + 1
                      refine ⟨z, by dsimp [z]; positivity, ?_⟩
                      apply Real.exp_lt_exp.mpr
                      have hs : 0 < ∑ k ∈ Finset.univ.erase i, lam k * max 0 (z - max 0 (u i - u k)) := by
                        apply Finset.sum_pos'
                        · intro k hk
                          exact mul_nonneg (hlam k).le (le_max_left _ _)
                        · refine ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, ?_⟩
                          dsimp [z]
                          simp only [add_sub_cancel_left, max_eq_right zero_le_one, mul_one]
                          exact hlam j
                      linarith)
                  simp only [integral_Ici_eq_integral_Ioi] at hl
                  have he : (∫ z : ℝ in Set.Ioi 0, Real.exp (-(lam i * z))) = 1 / lam i := by
                    simpa only [neg_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, neg_neg, one_div]
                      using integral_exp_mul_Ioi (neg_neg_of_pos (hlam i)) 0
                  rw [he] at hl
                  simpa only [J, integral_Ici_eq_integral_Ioi] using hl
                have hden (u : Fin n → ℝ) (i : Fin n) : 0 < 1 - lam i * J u i := by
                  have h := (lt_div_iff₀ (hlam i)).mp (hJlt u i)
                  nlinarith
                have htau (u : Fin n → ℝ) (i : Fin n) :
                    tau u lam i = J u i / (1 - lam i * J u i) := by
                  rw [tau, partialU, (hderiv u i).deriv, hJprob]
                  have he : E u i ≠ 0 := (Real.exp_pos _).ne'
                  have hd := (hden u i).ne'
                  have hi := (hlam i).ne'
                  field_simp
                  <;> ring
                have htaupos (u : Fin n → ℝ) (i : Fin n) : 0 < tau u lam i := by
                  rw [htau]
                  exact div_pos (hJpos u i) (hden u i)
                have hJmono (u v : Fin n → ℝ) (i : Fin n)
                    (hd : ∀ j, j ≠ i → max 0 (u i - u j) ≤ max 0 (v i - v j)) : J u i ≤ J v i := by
                  apply integral_mono_ae (hTint u i) (hTint v i)
                  filter_upwards [] with z
                  apply Real.exp_le_exp.mpr
                  have hs : (∑ j ∈ Finset.univ.erase i, lam j * max 0 (z - max 0 (v i - v j))) ≤
                      ∑ j ∈ Finset.univ.erase i, lam j * max 0 (z - max 0 (u i - u j)) := by
                    apply Finset.sum_le_sum
                    intro j hj
                    apply mul_le_mul_of_nonneg_left _ (hlam j).le
                    exact max_le_max_left 0 (sub_le_sub_left (hd j (Finset.mem_erase.mp hj).1) z)
                  linarith
                have htauMono (u v : Fin n → ℝ) (i : Fin n)
                    (hd : ∀ j, j ≠ i → max 0 (u i - u j) ≤ max 0 (v i - v j)) :
                    tau u lam i ≤ tau v lam i := by
                  rw [htau, htau, div_le_div_iff₀ (hden u i) (hden v i)]
                  have hj := hJmono u v i hd
                  nlinarith
                have htauEq (u v : Fin n → ℝ) (i : Fin n)
                    (hd : ∀ j, j ≠ i → max 0 (u i - u j) = max 0 (v i - v j)) :
                    tau u lam i = tau v lam i := by
                  apply le_antisymm
                  · exact htauMono u v i (fun j hj => (hd j hj).le)
                  · exact htauMono v u i (fun j hj => (hd j hj).ge)
                have htauOwn (u : Fin n → ℝ) (i : Fin n) :
                    Monotone (fun x => tau (Function.update u i x) lam i) := by
                  intro x y hxy
                  apply htauMono
                  intro j hj
                  simp only [Function.update_self, Function.update_of_ne hj]
                  exact max_le_max_left _ (sub_le_sub_right hxy _)
                have hEcont (i : Fin n) : Continuous (fun u : Fin n → ℝ => E u i) := by
                  dsimp [E]; fun_prop
                have hQowncont (u : Fin n → ℝ) (i : Fin n) :
                    Continuous (fun x => choiceProb (Function.update u i x) lam i) := by
                  apply continuous_iff_continuousAt.mpr
                  intro x
                  have hd := (hderiv (Function.update u i x) i).continuousAt
                  simpa only [Function.update_self, Function.update_idem] using hd
                have hJowncont (u : Fin n → ℝ) (i : Fin n) :
                    Continuous (fun x => J (Function.update u i x) i) := by
                  have he (x : ℝ) : J (Function.update u i x) i =
                      choiceProb (Function.update u i x) lam i / (lam i * E (Function.update u i x) i) := by
                    rw [hJprob]
                    have hh : lam i * E (Function.update u i x) i ≠ 0 :=
                      mul_ne_zero (hlam i).ne' (Real.exp_pos _).ne'
                    exact (mul_div_cancel_left₀ _ hh).symm
                  simp_rw [he]
                  apply (hQowncont u i).div (continuous_const.mul ((hEcont i).comp ?_))
                  · intro x
                    exact mul_ne_zero (hlam i).ne' (Real.exp_pos _).ne'
                  · fun_prop
                have htauOwnCont (u : Fin n → ℝ) (i : Fin n) :
                    Continuous (fun x => tau (Function.update u i x) lam i) := by
                  simp_rw [htau]
                  exact (hJowncont u i).div
                    (continuous_const.sub (continuous_const.mul (hJowncont u i)))
                    (fun x => (hden _ _).ne')
                have hLpos : 0 < Ltot lam := by
                  unfold Ltot
                  exact Finset.sum_pos (fun j _ => hlam j) Finset.univ_nonempty
                have hLsub (i : Fin n) : 0 < Ltot lam - lam i := by
                  have hs : Ltot lam - lam i = ∑ j ∈ Finset.univ.erase i, lam j := by
                    rw [Ltot, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
                  rw [hs]
                  apply Finset.sum_pos (fun j _ => hlam j)
                  obtain ⟨j, hj⟩ := exists_ne i
                  exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
                have htauBottom (u : Fin n → ℝ) (i : Fin n) (hu : ∀ j, u i ≤ u j) :
                    tau u lam i = 1 / (Ltot lam - lam i) := by
                  have hj : J u i = 1 / Ltot lam := by
                    calc
                      J u i = ∫ z : ℝ in Set.Ici 0, Real.exp (-(Ltot lam * z)) := by
                        apply setIntegral_congr_fun measurableSet_Ici
                        intro z hz
                        dsimp [T]
                        congr 2
                        have he : (∑ j ∈ Finset.univ.erase i, lam j * max 0 (z - max 0 (u i - u j))) =
                            (Ltot lam - lam i) * z := by
                          have he : Ltot lam - lam i = ∑ j ∈ Finset.univ.erase i, lam j := by
                            rw [Ltot, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
                          rw [he, Finset.sum_mul]
                          apply Finset.sum_congr rfl
                          intro j hj
                          rw [max_eq_left (sub_nonpos.mpr (hu j)), sub_zero, max_eq_right (show (0 : ℝ) ≤ z from hz)]
                        rw [he]
                        ring
                      _ = 1 / Ltot lam := by
                        rw [integral_Ici_eq_integral_Ioi]
                        simpa only [neg_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
                          using integral_exp_mul_Ioi (neg_neg_of_pos hLpos) 0
                  rw [htau, hj]
                  have h1 := hLpos.ne'
                  have h2 := (hLsub i).ne'
                  field_simp
                  <;> ring
                have hroot (u : Fin n → ℝ) (i : Fin n) :
                    ∃! x : ℝ, α i - x = tau (Function.update u i x) lam i := by
                  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
                  let c := 1 / (Ltot lam - lam i)
                  let a := min (α i - c) (u k)
                  have hc : 0 < c := one_div_pos.mpr (hLsub i)
                  have ha : a ≤ α i := le_trans (min_le_left _ _) (sub_le_self _ hc.le)
                  have ht : tau (Function.update u i a) lam i = c := by
                    apply htauBottom
                    intro j
                    by_cases hj : j = i
                    · subst j; exact le_rfl
                    · simp only [Function.update_self, Function.update_of_ne hj]
                      exact (min_le_right _ _).trans (hmin j (Finset.mem_univ j))
                  let F : ℝ → ℝ := fun x => α i - x - tau (Function.update u i x) lam i
                  have hF : Continuous F := continuous_const.sub continuous_id |>.sub (htauOwnCont u i)
                  have hfa : 0 ≤ F a := by
                    dsimp [F]
                    rw [ht]
                    have haa : a ≤ α i - c := min_le_left _ _
                    linarith
                  have hfb : F (α i) ≤ 0 := by
                    dsimp [F]
                    have ht := htaupos (Function.update u i (α i)) i
                    linarith
                  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' ha hF.continuousOn ⟨hfb, hfa⟩
                  refine ⟨x, ?_, ?_⟩
                  · dsimp [F] at hfx
                    linarith
                  · intro y hy
                    have hx' : α i - x = tau (Function.update u i x) lam i := by
                      dsimp [F] at hfx
                      linarith
                    rcases le_total x y with hxy | hyx
                    · have ht := htauOwn u i hxy
                      linarith
                    · have ht := htauOwn u i hyx
                      linarith
                have hcondUpd (S : Finset (Fin n)) (u : Fin n → ℝ) (i : Fin n) (x y : ℝ) :
                    condVec α S u i x = Function.update (condVec α S u i y) i x := by
                  ext j
                  by_cases hj : j = i <;> simp [condVec, hj]
                have hcondRoot (S : Finset (Fin n)) (u : Fin n → ℝ) (i : Fin n) :
                    ∃! x : ℝ, α i - x = tauCond α lam S u i x := by
                  simpa only [tauCond, ← hcondUpd S u i _ 0] using hroot (condVec α S u i 0) i
                have hcondOwn (S : Finset (Fin n)) (u : Fin n → ℝ) (i : Fin n) :
                    Monotone (fun x => tauCond α lam S u i x) := by
                  simpa only [tauCond, ← hcondUpd S u i _ 0] using htauOwn (condVec α S u i 0) i
                have hcondAgree (S : Finset (Fin n)) (u v : Fin n → ℝ) (i : Fin n) (x : ℝ)
                    (h : ∀ j ∈ S, u j = v j) : tauCond α lam S u i x = tauCond α lam S v i x := by
                  unfold tauCond
                  congr 1
                  ext j
                  simp only [condVec]
                  split_ifs with hji hjS
                  · rfl
                  · exact h j hjS
                  · rfl
                have hmaxAlpha (i : Fin n) : α i ≤ maxAlpha α := by
                  exact le_ciSup (Finite.bddAbove_range α) i
                have hsolved (s : Fin n) (j : Fin n) :
                    j ∈ solvedBefore σ s.val ↔ (σ.symm j).val < s.val := by
                  simp only [solvedBefore, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · rintro ⟨a, ha, rfl⟩
                    simpa using ha
                  · intro h
                    exact ⟨σ.symm j, h, σ.apply_symm_apply j⟩
                have hTfull (u : Fin n → ℝ) (i : Fin n) (z : ℝ) (hz : 0 ≤ z) :
                    T u i z = Real.exp (-(∑ j, lam j * max 0 (z - max 0 (u i - u j)))) := by
                  dsimp [T]
                  congr 2
                  rw [← Finset.sum_erase_add Finset.univ
                    (fun j => lam j * max 0 (z - max 0 (u i - u j))) (Finset.mem_univ i)]
                  simp only [sub_self, max_self, sub_zero, max_eq_right (show (0 : ℝ) ≤ z from hz)]
                  ring
                have hJtie (u : Fin n → ℝ) (i j : Fin n) (hu : u i = u j) : J u i = J u j := by
                  apply setIntegral_congr_fun measurableSet_Ici
                  intro z hz
                  rw [hTfull u i z hz, hTfull u j z hz, hu]
                have hJpair (u : Fin n → ℝ) (i j : Fin n) (hij : j ≠ i) (hu : u i ≤ u j) :
                    J u i ≤ 1 / (lam i + lam j) := by
                  have hl : 0 < lam i + lam j := add_pos (hlam i) (hlam j)
                  have hint : IntegrableOn (fun z : ℝ => Real.exp (-((lam i + lam j) * z))) (Set.Ici 0) := by
                    rw [integrableOn_Ici_iff_integrableOn_Ioi]
                    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (neg_neg_of_pos hl) 0
                  have hm : J u i ≤ ∫ z : ℝ in Set.Ici 0, Real.exp (-((lam i + lam j) * z)) := by
                    apply integral_mono_ae (hTint u i) hint
                    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
                    apply Real.exp_le_exp.mpr
                    have hs : lam j * z ≤ ∑ k ∈ Finset.univ.erase i,
                        lam k * max 0 (z - max 0 (u i - u k)) := by
                      have hs := Finset.single_le_sum
                        (fun k (_ : k ∈ Finset.univ.erase i) => mul_nonneg (hlam k).le
                          (le_max_left 0 (z - max 0 (u i - u k))))
                        (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩)
                      simpa only [max_eq_left (sub_nonpos.mpr hu), sub_zero, max_eq_right (show (0 : ℝ) ≤ z from hz)] using hs
                    linarith
                  rw [integral_Ici_eq_integral_Ioi] at hm
                  have he : (∫ z : ℝ in Set.Ioi 0, Real.exp (-((lam i + lam j) * z))) = 1 / (lam i + lam j) := by
                    simpa only [neg_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
                      using integral_exp_mul_Ioi (neg_neg_of_pos hl) 0
                  rw [he] at hm
                  exact hm
                have htie (u : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) (hu : u i = u j) :
                    ∃ r : ℝ, lam i + lam j ≤ r ∧ tau u lam i = 1 / (r - lam i) ∧
                      tau u lam j = 1 / (r - lam j) := by
                  let r := 1 / J u i
                  have hp := hJpos u i
                  have hj := hJpair u i j hij.symm hu.le
                  have hr : lam i + lam j ≤ r := by
                    dsimp [r]
                    apply (le_div_iff₀ hp).mpr
                    have hh := (le_div_iff₀ (add_pos (hlam i) (hlam j))).mp hj
                    nlinarith
                  refine ⟨r, hr, ?_, ?_⟩
                  · rw [htau]
                    have hd := (hden u i).ne'
                    have hri : r - lam i ≠ 0 := by linarith [hlam j]
                    dsimp [r] at hri ⊢
                    field_simp
                    <;> ring
                  · rw [htau, ← hJtie u i j hu]
                    have hd : 1 - lam j * J u i ≠ 0 := by rw [hJtie u i j hu]; exact (hden u j).ne'
                    have hrj : r - lam j ≠ 0 := by linarith [hlam i]
                    dsimp [r] at hrj ⊢
                    field_simp
                    <;> ring
                have hdiff (a b r : ℝ) (ha : 0 < a) (hb : 0 < b)
                    (hr : a + b ≤ r) (hab : a ≤ b) :
                    1 / (r - b) - 1 / (r - a) ≤ 1 / a - 1 / b := by
                  have hra : 0 < r - a := by linarith
                  have hrb : 0 < r - b := by linarith
                  have hprod : a * b ≤ (r - a) * (r - b) := by
                    nlinarith [mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r - (a + b) by linarith)]
                  have hd1 : 1 / (r - b) - 1 / (r - a) = (b - a) / ((r - a) * (r - b)) := by
                    field_simp
                    <;> ring
                  have hd2 : 1 / a - 1 / b = (b - a) / (a * b) := by
                    field_simp
                    <;> ring
                  rw [hd1, hd2]
                  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hab) (mul_pos ha hb) hprod
                have hcompare (u : Fin n → ℝ) (i j : Fin n) (hu : u i = u j)
                    (ha : α i ≤ α j) (hs : α i + 1 / lam i ≤ α j + 1 / lam j) :
                    α i - tau u lam i ≤ α j - tau u lam j ∧
                      (α i - tau u lam i = α j - tau u lam j → α j = α i ∧ lam j = lam i) := by
                  by_cases hij : i = j
                  · subst j
                    exact ⟨le_rfl, fun _ => ⟨rfl, rfl⟩⟩
                  obtain ⟨r, hr, hti, htj⟩ := htie u i j hij hu
                  rw [hti, htj]
                  have hri : 0 < r - lam i := by linarith [hlam j]
                  have hrj : 0 < r - lam j := by linarith [hlam i]
                  constructor
                  · rcases le_total (lam i) (lam j) with hij | hji
                    · have hh := hdiff (lam i) (lam j) r (hlam i) (hlam j) hr hij
                      linarith
                    · have hh : 1 / (r - lam j) ≤ 1 / (r - lam i) :=
                        one_div_le_one_div_of_le hri (by linarith)
                      linarith
                  · intro heq
                    have hij : lam i ≤ lam j := by
                      by_contra! hji
                      have hh : 1 / (r - lam j) < 1 / (r - lam i) :=
                        one_div_lt_one_div_of_lt hri (by linarith)
                      linarith
                    have hh := hdiff (lam i) (lam j) r (hlam i) (hlam j) hr hij
                    have hs' : α j + 1 / lam j ≤ α i + 1 / lam i := by linarith
                    have heα : α j = α i := le_antisymm (hα j i hs') ha
                    have heτ : 1 / (r - lam i) = 1 / (r - lam j) := by linarith
                    have her : r - lam i = r - lam j := by
                      apply inv_injective
                      simpa only [one_div] using heτ
                    exact ⟨heα, by linarith⟩
                have hQpos (u : Fin n → ℝ) (i : Fin n) : 0 < choiceProb u lam i := by
                  rw [hJprob]
                  exact mul_pos (mul_pos (hlam i) (Real.exp_pos _)) (hJpos u i)
                have hDpos (u : Fin n → ℝ) (i : Fin n) :
                    0 < lam i * (E u i - choiceProb u lam i) := by
                  rw [hJprob]
                  have he : 0 < E u i := Real.exp_pos _
                  have hh := mul_pos he (hden u i)
                  nlinarith [hlam i]
                have hQtau (u : Fin n → ℝ) (i : Fin n) :
                    choiceProb u lam i = lam i * (E u i - choiceProb u lam i) * tau u lam i := by
                  rw [tau, partialU, (hderiv u i).deriv]
                  exact (mul_div_cancel₀ _ (hDpos u i).ne').symm
                have hRderiv (u : Fin n → ℝ) (i : Fin n) (x : ℝ) :
                    HasDerivAt (fun y => (α i - y) * choiceProb (Function.update u i y) lam i)
                      (lam i * (E (Function.update u i x) i - choiceProb (Function.update u i x) lam i) *
                        (α i - x - tau (Function.update u i x) lam i)) x := by
                  have hd := hderiv (Function.update u i x) i
                  simp only [Function.update_self, Function.update_idem] at hd
                  convert (((hasDerivAt_const x (α i)).sub (hasDerivAt_id x)).mul hd) using 1 <;> try rfl
                  have hh := hQtau (Function.update u i x) i
                  dsimp
                  linear_combination hh
                have hRmax (u : Fin n → ℝ) (i : Fin n) (x : ℝ)
                    (hx : α i - x = tau (Function.update u i x) lam i) :
                    IsMaxOn (fun y => (α i - y) * choiceProb (Function.update u i y) lam i) Set.univ x := by
                  apply isMaxOn_univ_of_deriv (hRderiv u i x).continuousAt
                    (fun y _ => (hRderiv u i y).differentiableAt.differentiableWithinAt)
                    (fun y _ => (hRderiv u i y).differentiableAt.differentiableWithinAt)
                  · intro y hy
                    rw [(hRderiv u i y).deriv]
                    have hm := htauOwn u i (show y ≤ x from le_of_lt hy)
                    change tau (Function.update u i y) lam i ≤ tau (Function.update u i x) lam i at hm
                    have hy' : y < x := hy
                    exact mul_nonneg (hDpos _ _).le (by linarith)
                  · intro y hy
                    rw [(hRderiv u i y).deriv]
                    have hm := htauOwn u i (show x ≤ y from le_of_lt hy)
                    change tau (Function.update u i x) lam i ≤ tau (Function.update u i y) lam i at hm
                    have hy' : x < y := hy
                    exact mul_nonpos_of_nonneg_of_nonpos (hDpos _ _).le (by linarith)
                have hutilUpd (p : Fin n → ℝ) (i : Fin n) (q : ℝ) :
                    util α β (Function.update p i q) = Function.update (util α β p) i (α i - β * q) := by
                  ext j
                  by_cases hj : j = i <;> simp [util, hj]
                have hNE (p : Fin n → ℝ) : IsPriceNE α β lam p ↔
                    ∀ i, α i - util α β p i = tau (util α β p) lam i := by
                  constructor
                  · intro hp
                    have hpPos (i : Fin n) : 0 < p i := by
                      by_contra! hh
                      have he : p i = 0 := le_antisymm hh (hp.1 i)
                      have hh := hp.2 i 1 zero_le_one
                      have hpos := hQpos (util α β (Function.update p i 1)) i
                      simp only [firmRevenue, Function.update_self, one_mul, he, zero_mul] at hh
                      linarith
                    intro i
                    let u := util α β p
                    have hualpha : u i < α i := by
                      dsimp [u, util]
                      nlinarith [mul_pos hβ (hpPos i)]
                    have hm : IsLocalMax (fun y => (α i - y) * choiceProb (Function.update u i y) lam i) (u i) := by
                      filter_upwards [eventually_lt_nhds hualpha] with y hy
                      let q := (α i - y) / β
                      have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hy.le) hβ.le
                      have hh := mul_le_mul_of_nonneg_left (hp.2 i q hq) hβ.le
                      have he : α i - β * q = y := by
                        dsimp [q]
                        field_simp
                        <;> ring
                      rw [firmRevenue, firmRevenue, Function.update_self, hutilUpd, he] at hh
                      have hu : Function.update u i (u i) = u := Function.update_eq_self i u
                      rw [hu]
                      dsimp only [u, util] at hh ⊢
                      have hqy : β * q = α i - y := by linarith [he]
                      rw [← mul_assoc, hqy] at hh
                      convert hh using 1 <;> ring
                    have hh := hm.hasDerivAt_eq_zero (hRderiv u i (u i))
                    have hu : Function.update u i (u i) = u := Function.update_eq_self i u
                    rw [hu] at hh
                    have hd := hDpos u i
                    dsimp only [u] at hh hd ⊢
                    nlinarith
                  · intro hp
                    have hpPos (i : Fin n) : 0 < p i := by
                      have ht := htaupos (util α β p) i
                      have he := hp i
                      dsimp only [util] at he
                      nlinarith
                    refine ⟨fun i => (hpPos i).le, ?_⟩
                    intro i q hq
                    let u := util α β p
                    have hu : Function.update u i (u i) = u := Function.update_eq_self i u
                    have hroot : α i - u i = tau (Function.update u i (u i)) lam i := by
                      rw [hu]
                      exact hp i
                    have hh := hRmax u i (u i) hroot (Set.mem_univ (α i - β * q))
                    change (α i - (α i - β * q)) * choiceProb (Function.update u i (α i - β * q)) lam i ≤
                      (α i - u i) * choiceProb (Function.update u i (u i)) lam i at hh
                    rw [hu] at hh
                    have he := hutilUpd p i q
                    change util α β (Function.update p i q) = Function.update u i (α i - β * q) at he
                    rw [← he] at hh
                    dsimp only [firmRevenue]
                    rw [Function.update_self]
                    apply (mul_le_mul_iff_right₀ hβ).mp
                    dsimp only [u, util] at hh
                    nlinarith
                let Step : (Fin n → ℝ) → Fin n → Prop := fun u s =>
                  (s.val = 0 → u (σ s) = α (σ s) - 1 / (Ltot lam - lam (σ s))) ∧
                  (0 < s.val → α (σ s) - u (σ s) =
                    tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)))
                have hstepAgree (u v : Fin n → ℝ) (s : Fin n) (hs : u (σ s) = v (σ s))
                    (hp : ∀ j ∈ solvedBefore σ s.val, u j = v j) : Step u s ↔ Step v s := by
                  dsimp only [Step]
                  rw [hs, hcondAgree _ u v _ _ hp]
                have hcondFresh (S : Finset (Fin n)) (u : Fin n → ℝ) (i j : Fin n) (x y : ℝ)
                    (hj : j ∉ S) : tauCond α lam S (Function.update u j y) i x = tauCond α lam S u i x := by
                  apply hcondAgree
                  intro k hk
                  have hkj : k ≠ j := by
                    intro he
                    subst k
                    exact hj hk
                  exact Function.update_of_ne hkj _ _
                have hExists : ∃ u : Fin n → ℝ, IsOnePass α lam σ u := by
                  have hpref : ∀ k : ℕ, k ≤ n → ∃ u : Fin n → ℝ, ∀ s : Fin n, s.val < k → Step u s := by
                    intro k
                    induction k with
                    | zero =>
                      intro hk
                      exact ⟨fun _ => 0, fun s hs => by omega⟩
                    | succ k ih =>
                      intro hk
                      obtain ⟨u, hu⟩ := ih (by omega)
                      let s : Fin n := ⟨k, by omega⟩
                      have hsf : σ s ∉ solvedBefore σ s.val := by
                        rw [hsolved]
                        simp
                      have hx : ∃ x : ℝ, Step (Function.update u (σ s) x) s := by
                        by_cases hk0 : k = 0
                        · refine ⟨α (σ s) - 1 / (Ltot lam - lam (σ s)), ?_⟩
                          constructor
                          · intro _
                            simp only [Function.update_self]
                          · intro hh
                            dsimp [s] at hh
                            omega
                        · obtain ⟨x, hx, _⟩ := hcondRoot (solvedBefore σ s.val) u (σ s)
                          refine ⟨x, ?_, ?_⟩
                          · intro hh
                            dsimp [s] at hh
                            contradiction
                          · intro _
                            simp only [Function.update_self]
                            rw [hcondFresh _ u (σ s) (σ s) x x hsf]
                            exact hx
                      obtain ⟨x, hx⟩ := hx
                      refine ⟨Function.update u (σ s) x, ?_⟩
                      intro t ht
                      by_cases hts : t = s
                      · simpa only [hts] using hx
                      · have htk : t.val < k := by
                          have hne : t.val ≠ k := fun he => hts (Fin.ext he)
                          omega
                        have hown : Function.update u (σ s) x (σ t) = u (σ t) := by
                          apply Function.update_of_ne
                          exact fun he => hts (σ.injective he)
                        have hprev : ∀ j ∈ solvedBefore σ t.val, Function.update u (σ s) x j = u j := by
                          intro j hj
                          apply Function.update_of_ne
                          intro he
                          subst j
                          rw [hsolved] at hj
                          simp only [Equiv.symm_apply_apply] at hj
                          dsimp [s] at hj
                          omega
                        exact (hstepAgree _ u t hown hprev).mpr (hu t htk)
                  obtain ⟨u, hu⟩ := hpref n le_rfl
                  exact ⟨u, fun s => hu s s.isLt⟩
                have hOneUnique (u v : Fin n → ℝ) (hu : IsOnePass α lam σ u) (hv : IsOnePass α lam σ v) : u = v := by
                  have heq : ∀ k : ℕ, ∀ s : Fin n, s.val = k → u (σ s) = v (σ s) := by
                    intro k
                    induction k using Nat.strong_induction_on with
                    | h k ih =>
                      intro s hs
                      by_cases h0 : s.val = 0
                      · rw [(hu s).1 h0, (hv s).1 h0]
                      · have hpos : 0 < s.val := Nat.pos_of_ne_zero h0
                        have hprev : ∀ j ∈ solvedBefore σ s.val, u j = v j := by
                          intro j hj
                          have hh := (hsolved s j).mp hj
                          have he := ih (σ.symm j).val (by omega) (σ.symm j) rfl
                          simpa only [Equiv.apply_symm_apply] using he
                        have hx := (hu s).2 hpos
                        rw [hcondAgree _ u v _ _ hprev] at hx
                        exact (hcondRoot (solvedBefore σ s.val) v (σ s)).unique hx ((hv s).2 hpos)
                  ext j
                  simpa only [Equiv.apply_symm_apply] using heq (σ.symm j).val (σ.symm j) rfl
                have hOneBelow (u : Fin n → ℝ) (hu : IsOnePass α lam σ u) (s : Fin n) :
                    u (σ s) < α (σ s) := by
                  by_cases h0 : s.val = 0
                  · rw [(hu s).1 h0]
                    exact sub_lt_self _ (one_div_pos.mpr (hLsub (σ s)))
                  · have he := (hu s).2 (Nat.pos_of_ne_zero h0)
                    have hp := htaupos (condVec α (solvedBefore σ s.val) u (σ s) (u (σ s))) (σ s)
                    change 0 < tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) at hp
                    linarith
                have hOneCond (u : Fin n → ℝ) (hu : IsOnePass α lam σ u) (s : Fin n) :
                    α (σ s) - u (σ s) = tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) := by
                  by_cases h0 : s.val = 0
                  · have hS : solvedBefore σ s.val = ∅ := by simp [solvedBefore, h0]
                    rw [hS, tauCond]
                    have hb : ∀ j, condVec α ∅ u (σ s) (u (σ s)) (σ s) ≤
                        condVec α ∅ u (σ s) (u (σ s)) j := by
                      intro j
                      by_cases hj : j = σ s
                      · subst j
                        exact le_rfl
                      · simp only [condVec, if_pos rfl, Finset.notMem_empty, if_false, if_neg hj]
                        exact (hOneBelow u hu s).le.trans (hmaxAlpha (σ s))
                    rw [htauBottom _ (σ s) hb, (hu s).1 h0]
                    ring
                  · exact (hu s).2 (Nat.pos_of_ne_zero h0)
                have hOrderParams (s t : Fin n) (hst : s ≤ t) :
                    α (σ s) ≤ α (σ t) ∧ α (σ s) + 1 / lam (σ s) ≤ α (σ t) + 1 / lam (σ t) := by
                  exact ⟨hα _ _ (hσ hst), hσ hst⟩
                have hAdj (u : Fin n → ℝ) (hu : IsOnePass α lam σ u) (s t : Fin n)
                    (hst : t.val + 1 = s.val) :
                    u (σ t) ≤ u (σ s) ∧
                      (u (σ t) = u (σ s) → α (σ s) = α (σ t) ∧ lam (σ s) = lam (σ t)) := by
                  have hts : t < s := by show t.val < s.val; omega
                  have hne : σ t ≠ σ s := fun he => (ne_of_lt hts) (σ.injective he)
                  have hM : u (σ t) ≤ maxAlpha α := (hOneBelow u hu t).le.trans (hmaxAlpha (σ t))
                  let w := condVec α (solvedBefore σ s.val) u (σ s) (u (σ t))
                  let v := condVec α (solvedBefore σ t.val) u (σ t) (u (σ t))
                  have hwt : w (σ t) = u (σ t) := by
                    have hm : σ t ∈ solvedBefore σ s.val := by rw [hsolved]; simpa using hts
                    simp only [w, condVec, if_neg hne, if_pos hm]
                  have hws : w (σ s) = u (σ t) := by simp [w, condVec]
                  have hvt : v (σ t) = u (σ t) := by simp [v, condVec]
                  have hmemb (j : Fin n) (hj : j ≠ σ t) :
                      j ∈ solvedBefore σ s.val ↔ j ∈ solvedBefore σ t.val := by
                    rw [hsolved, hsolved]
                    have hh : (σ.symm j).val ≠ t.val := by
                      intro he
                      have heq : σ.symm j = t := Fin.ext he
                      apply hj
                      simpa only [Equiv.apply_symm_apply] using congrArg σ heq
                    omega
                  have het : tau w lam (σ t) = tau v lam (σ t) := by
                    apply htauEq
                    intro j hj
                    rw [hwt, hvt]
                    by_cases hjs : j = σ s
                    · subst j
                      have hnS : σ s ∉ solvedBefore σ t.val := by
                        rw [hsolved]
                        simpa using (not_lt_of_ge hts.le)
                      rw [hws]
                      have hv : v (σ s) = maxAlpha α := by simp [v, condVec, hne.symm, hnS]
                      rw [hv, sub_self, max_self, max_eq_left (sub_nonpos.mpr hM)]
                    · have he : w j = v j := by
                        simp only [w, v, condVec, if_neg hjs, if_neg hj]
                        simp only [hmemb j hj]
                      rw [he]
                  have htFOC := hOneCond u hu t
                  change α (σ t) - u (σ t) = tau v lam (σ t) at htFOC
                  have hp := hOrderParams t s hts.le
                  have hc := hcompare w (σ t) (σ s) (hwt.trans hws.symm) hp.1 hp.2
                  rw [het] at hc
                  have hres : tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ t)) ≤
                      α (σ s) - u (σ t) := by
                    change tau w lam (σ s) ≤ _
                    linarith [hc.1]
                  have hsFOC := hOneCond u hu s
                  constructor
                  · by_contra! hh
                    have hm := hcondOwn (solvedBefore σ s.val) u (σ s) hh.le
                    change tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) ≤
                      tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ t)) at hm
                    linarith
                  · intro heq
                    apply hc.2
                    change α (σ t) - tau v lam (σ t) = α (σ s) - tau w lam (σ s)
                    have hwsFOC : α (σ s) - u (σ t) = tau w lam (σ s) := by
                      change α (σ s) - u (σ t) = tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ t))
                      simpa only [heq] using hsFOC
                    linarith
                have hOneMono (u : Fin n → ℝ) (hu : IsOnePass α lam σ u) :
                    Monotone (fun s => u (σ s)) := by
                  cases n with
                  | zero => omega
                  | succ m =>
                    apply Fin.monotone_iff_le_succ.mpr
                    intro s
                    exact (hAdj u hu s.succ s.castSucc (by simp)).1
                have hFOCMono (u : Fin n → ℝ) (hu : ∀ i, α i - u i = tau u lam i) :
                    Monotone (fun s => u (σ s)) := by
                  intro s t hst
                  by_contra! hlt
                  have hne : σ t ≠ σ s := by
                    intro he
                    rw [he] at hlt
                    exact (lt_irrefl _ hlt)
                  let w := Function.update u (σ s) (u (σ t))
                  have hwi : w (σ s) = u (σ t) := by simp [w]
                  have hwj : w (σ t) = u (σ t) := by simp [w, hne]
                  have hjtau : tau w lam (σ t) = tau u lam (σ t) := by
                    apply htauEq
                    intro j hj
                    rw [hwj]
                    by_cases hjs : j = σ s
                    · subst j
                      rw [hwi, sub_self, max_self, max_eq_left (by linarith : u (σ t) - u (σ s) ≤ 0)]
                    · simp only [w, Function.update_of_ne hjs]
                  have hmono := htauOwn u (σ s) hlt.le
                  change tau w lam (σ s) ≤ tau (Function.update u (σ s) (u (σ s))) lam (σ s) at hmono
                  rw [Function.update_eq_self] at hmono
                  have hp := hOrderParams s t hst
                  have hc := (hcompare w (σ s) (σ t) (hwi.trans hwj.symm) hp.1 hp.2).1
                  rw [hjtau] at hc
                  have his := hu (σ s)
                  have hit := hu (σ t)
                  linarith
                have hcondMatches (u : Fin n → ℝ) (hm : Monotone (fun s => u (σ s))) (s : Fin n)
                    (hM : u (σ s) ≤ maxAlpha α) :
                    tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) = tau u lam (σ s) := by
                  apply htauEq
                  intro j hj
                  have hself : condVec α (solvedBefore σ s.val) u (σ s) (u (σ s)) (σ s) = u (σ s) := by
                    simp [condVec]
                  rw [hself]
                  by_cases hjs : j ∈ solvedBefore σ s.val
                  · simp only [condVec, if_neg hj, if_pos hjs]
                  · have hsj : s ≤ σ.symm j := by
                      have hh := (hsolved s j).not.mp hjs
                      show s.val ≤ (σ.symm j).val
                      omega
                    have hul : u (σ s) ≤ u j := by simpa using hm hsj
                    simp only [condVec, if_neg hj, if_neg hjs,
                      max_eq_left (sub_nonpos.mpr hM), max_eq_left (sub_nonpos.mpr hul)]
                have hOneFOC (u : Fin n → ℝ) (hu : IsOnePass α lam σ u) :
                    ∀ i, α i - u i = tau u lam i := by
                  intro i
                  let s := σ.symm i
                  have hm := hOneMono u hu
                  have hc := hOneCond u hu s
                  rw [hcondMatches u hm s ((hOneBelow u hu s).le.trans (hmaxAlpha (σ s)))] at hc
                  simpa only [s, Equiv.apply_symm_apply] using hc
                have hFOCOne (u : Fin n → ℝ) (hu : ∀ i, α i - u i = tau u lam i) :
                    IsOnePass α lam σ u := by
                  have hm := hFOCMono u hu
                  intro s
                  have hbelow : u (σ s) < α (σ s) := by
                    have hp := htaupos u (σ s)
                    have hh := hu (σ s)
                    linarith
                  constructor
                  · intro h0
                    have hb : ∀ j, u (σ s) ≤ u j := by
                      intro j
                      have hsj : s ≤ σ.symm j := by show s.val ≤ (σ.symm j).val; omega
                      simpa only [Equiv.apply_symm_apply] using hm hsj
                    have hh := hu (σ s)
                    rw [htauBottom u (σ s) hb] at hh
                    linarith
                  · intro _
                    rw [hcondMatches u hm s (hbelow.le.trans (hmaxAlpha (σ s)))]
                    exact hu (σ s)
                have hutilEq (u : Fin n → ℝ) : util α β (eqPrices α β u) = u := by
                  ext i
                  dsimp [util, eqPrices]
                  field_simp
                  <;> ring
                refine ⟨hExists, ?_⟩
                intro u hu
                refine ⟨fun s _ => hcondRoot (solvedBefore σ s.val) u (σ s), ?_, ?_, hAdj u hu⟩
                · apply (hNE _).mpr
                  rw [hutilEq]
                  exact hOneFOC u hu
                · intro p hp
                  have hfp := (hNE p).mp hp
                  have hpu := hFOCOne (util α β p) hfp
                  have heq := hOneUnique (util α β p) u hpu hu
                  ext i
                  have hi := congrFun heq i
                  dsimp only [util] at hi
                  dsimp only [eqPrices]
                  apply (eq_div_iff hβ.ne').mpr
                  linarith
