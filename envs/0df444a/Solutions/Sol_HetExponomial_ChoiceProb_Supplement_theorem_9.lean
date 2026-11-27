-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:45.427194+00:00
-- url     : https://prove2.me/submissions/c4f09a42-9ab4-4456-a32c-476b9925a9ba

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) :
    ∃! p : Fin n → ℝ, IsPriceNE α β lam p := by
      classical
      set Φ : (Fin n → ℝ) → Fin n → ℝ → ℝ := fun u i t =>
        ∏ j, if j = i then 1 else Real.exp (-(lam j * max (u j - t) 0)) with hΦ
      set ρ : (Fin n → ℝ) → Fin n → ℝ := fun u i => ∫ s, (∏ j, if j = i then 1 else
        Real.exp (-(lam j * (max (u j - u i + s) 0 - max (u j - u i) 0)))) ∂(expMeasure (lam i))
        with hρ
      have hexp : ∀ r : ℝ, expMeasure r = volume.withDensity (exponentialPDF r) := fun r => rfl
      have hpdfm : ∀ r : ℝ, Measurable (exponentialPDF r) := fun r =>
        (measurable_exponentialPDFReal r).ennreal_ofReal
      have hpdft : ∀ r : ℝ, ∀ᵐ x ∂(volume : Measure ℝ), exponentialPDF r x < ⊤ := fun r =>
        Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
      have hpdfr : ∀ r : ℝ, 0 < r → ∀ x, (exponentialPDF r x).toReal =
          if 0 ≤ x then r * Real.exp (-(r * x)) else 0 := by
        intro r hr x
        rw [exponentialPDF_eq, ENNReal.toReal_ofReal]
        split_ifs
        · positivity
        · exact le_rfl
      have hac : ∀ r : ℝ, expMeasure r ≪ volume := fun r => by
        rw [hexp]; exact withDensity_absolutelyContinuous _ _
      have hnoatom : ∀ r : ℝ, ∀ a : ℝ, expMeasure r {a} = 0 := fun r a => hac r (by simp)
      have hnn : ∀ r : ℝ, ∀ᵐ x ∂(expMeasure r), 0 ≤ x := by
        intro r
        rw [hexp, ae_withDensity_iff (hpdfm r)]
        refine Filter.Eventually.of_forall fun x hx => ?_
        by_contra h
        exact hx (exponentialPDF_of_neg (not_le.1 h))
      have hprob : ∀ j, IsProbabilityMeasure (expMeasure (lam j)) := fun j =>
        isProbabilityMeasure_expMeasure (hlam j)
      have hIci : ∀ r : ℝ, 0 < r → ∀ c : ℝ, expMeasure r (Set.Ici c) =
          ENNReal.ofReal (Real.exp (-(r * max c 0))) := by
        intro r hr c
        have := isProbabilityMeasure_expMeasure hr
        rw [← measure_congr (Ioi_ae_eq_Ici' (hnoatom r c)), ← Set.compl_Iic,
          prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hr,
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by
            split_ifs with h
            · have : Real.exp (-(r*c)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
              linarith
            · exact le_rfl)]
        congr 1
        split_ifs with h
        · rw [max_eq_left h]; ring
        · rw [max_eq_right (by linarith)]; simp
      have hΦle : ∀ u i t, Φ u i t ≤ 1 := by
        intro u i t
        refine Finset.prod_le_one (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
        split_ifs
        · exact le_rfl
        · rw [Real.exp_le_one_iff]
          have := hlam j
          have : 0 ≤ max (u j - t) 0 := le_max_right _ _
          nlinarith
      have hΦcont : ∀ u i, Continuous (Φ u i) := by
        intro u i
        refine continuous_finsetProd _ fun j _ => ?_
        split_ifs
        · exact continuous_const
        · fun_prop
      have hQform : ∀ u i, choiceProb u lam i = ∫ s, Φ u i (u i - s) ∂(expMeasure (lam i)) := by
        intro u i
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        set S := {z : Fin (k+1) → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i} with hS
        have hSm : MeasurableSet S := by
          simp only [hS, Set.ofPred_forall]
          refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
          exact measurableSet_le (by fun_prop) (by fun_prop)
        have hmp := (measurePreserving_piFinSuccAbove (fun j => expMeasure (lam j)) i).symm
        have e1 : errorLaw lam S = ((expMeasure (lam i)).prod
            (Measure.pi fun j => expMeasure (lam (i.succAbove j))))
            ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm ⁻¹' S) :=
          (hmp.measure_preimage hSm.nullMeasurableSet).symm
        have hm2 : MeasurableSet ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm ⁻¹' S) :=
          (MeasurableEquiv.measurable _) hSm
        rw [Measure.prod_apply hm2] at e1
        have e2 : ∀ x : ℝ, Prod.mk x ⁻¹' ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm ⁻¹' S)
            = Set.univ.pi (fun j : Fin k => Set.Ici (u (i.succAbove j) - (u i - x))) := by
          intro x
          ext y
          simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ici, hS, Set.mem_ofPred_eq]
          have hsy : (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm (x, y) =
              (i.insertNth x y : Fin (k+1) → ℝ) := rfl
          rw [hsy]
          constructor
          · intro h j
            have := h (i.succAbove j) (Fin.succAbove_ne i j)
            simp only [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same] at this
            linarith
          · intro h j hj
            obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
            have := h l
            simp only [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
            linarith
        simp_rw [e2, Measure.pi_pi, hIci _ (hlam _)] at e1
        have e3 : ∀ x : ℝ, Φ u i (u i - x) =
            ∏ j : Fin k, Real.exp (-(lam (i.succAbove j) * max (u (i.succAbove j) - (u i - x)) 0)) := by
          intro x
          simp only [hΦ]
          rw [Fin.prod_univ_succAbove _ i]
          simp only [↓reduceIte, one_mul]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [if_neg (Fin.succAbove_ne i j)]
        have hΦnn : ∀ u i t, 0 ≤ Φ u i t := fun u i t =>
          Finset.prod_nonneg fun j _ => by split_ifs <;> positivity
        rw [integral_eq_lintegral_of_nonneg_ae (f := fun s => Φ u i (u i - s)) (Filter.Eventually.of_forall fun x => hΦnn _ _ _)
          ((hΦcont u i).comp (continuous_const.sub continuous_id)).aestronglyMeasurable]
        simp only [choiceProb]
        rw [e1]
        congr 1
        refine lintegral_congr fun x => ?_
        rw [e3, ENNReal.ofReal_prod_of_nonneg (fun j _ => by positivity)]
      have hΦnn : ∀ u i t, 0 ≤ Φ u i t := fun u i t =>
        Finset.prod_nonneg fun j _ => by split_ifs <;> positivity
      set E : (Fin n → ℝ) → Fin n → ℝ → ℝ := fun u i s => ∏ j, if j = i then 1 else
        Real.exp (-(lam j * (max (u j - u i + s) 0 - max (u j - u i) 0))) with hE
      have hρE : ∀ u i, ρ u i = ∫ s, E u i s ∂(expMeasure (lam i)) := fun u i => rfl
      have hEpos : ∀ u i s, 0 < E u i s := fun u i s =>
        Finset.prod_pos fun j _ => by split_ifs <;> positivity
      have hbnn : ∀ c s : ℝ, 0 ≤ s → 0 ≤ max (c + s) 0 - max c 0 := by
        intro c s hs
        simp only [max_def]; split_ifs <;> linarith
      have hbmono : ∀ c c' s : ℝ, 0 ≤ s → c ≤ c' → max (c + s) 0 - max c 0 ≤ max (c' + s) 0 - max c' 0 := by
        intro c c' s hs hc
        simp only [max_def]; split_ifs <;> linarith
      have hEle : ∀ u i s, 0 ≤ s → E u i s ≤ 1 := by
        intro u i s hs
        refine Finset.prod_le_one (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
        split_ifs
        · exact le_rfl
        · rw [Real.exp_le_one_iff]
          have := hlam j
          have := hbnn (u j - u i) s hs
          nlinarith
      have hEcont : ∀ u i, Continuous (E u i) := by
        intro u i
        refine continuous_finsetProd _ fun j _ => ?_
        split_ifs
        · exact continuous_const
        · fun_prop
      have hEint : ∀ u i, Integrable (E u i) (expMeasure (lam i)) := by
        intro u i
        refine Integrable.mono' (integrable_const (1:ℝ)) (hEcont u i).aestronglyMeasurable ?_
        filter_upwards [hnn (lam i)] with s hs
        rw [Real.norm_eq_abs, abs_of_pos (hEpos u i s)]
        exact hEle u i s hs
      have hQρ : ∀ u i, choiceProb u lam i = Φ u i (u i) * ρ u i := by
        intro u i
        rw [hQform, hρE, ← integral_const_mul]
        congr 1
        funext s
        simp only [hΦ, hE]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        split_ifs
        · simp
        · rw [← Real.exp_add]
          congr 1
          have : u j - (u i - s) = u j - u i + s := by ring
          rw [this]; ring
      have hρpos : ∀ u i, 0 < ρ u i := by
        intro u i
        rw [hρE, integral_pos_iff_support_of_nonneg (fun s => (hEpos u i s).le) (hEint u i)]
        have : Function.support (E u i) = Set.univ :=
          Set.eq_univ_of_forall fun s => (hEpos u i s).ne'
        rw [this, measure_univ]
        exact one_pos
      have hρle : ∀ u i, ρ u i ≤ 1 := by
        intro u i
        rw [hρE]
        have : ∫ s, E u i s ∂(expMeasure (lam i)) ≤ ∫ s, (1:ℝ) ∂(expMeasure (lam i)) := by
          refine integral_mono_ae (hEint u i) (integrable_const _) ?_
          filter_upwards [hnn (lam i)] with s hs
          exact hEle u i s hs
        simpa using this
      have hρmono : ∀ u w i, u i = w i → (∀ j, j ≠ i → u j ≤ w j) → ρ w i ≤ ρ u i := by
        intro u w i h1 h2
        rw [hρE, hρE]
        refine integral_mono_ae (hEint w i) (hEint u i) ?_
        filter_upwards [hnn (lam i)] with s hs
        refine Finset.prod_le_prod (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
        split_ifs with hj
        · exact le_rfl
        · rw [Real.exp_le_exp]
          have := hbmono (u j - u i) (w j - w i) s hs (by rw [h1]; linarith [h2 j hj])
          have := hlam j
          nlinarith
      have hexpint : ∀ r k : ℝ, 0 < r → 0 ≤ k →
          ∫ s, Real.exp (-(k * s)) ∂(expMeasure r) = r / (r + k) := by
        intro r k hr hk
        rw [hexp, integral_withDensity_eq_integral_toReal_smul (hpdfm r) (hpdft r)]
        have e1 : (fun x => (exponentialPDF r x).toReal • Real.exp (-(k * x))) =
            (Set.Ici (0:ℝ)).indicator (fun x => r * Real.exp ((-(r + k)) * x)) := by
          funext x
          simp only [Set.indicator_apply, Set.mem_Ici, smul_eq_mul, hpdfr r hr]
          split_ifs
          · rw [mul_assoc, ← Real.exp_add]; congr 2; ring
          · simp
        rw [e1, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
          integral_const_mul, integral_exp_mul_Ioi (by linarith)]
        simp only [mul_zero, Real.exp_zero]
        field_simp
      have hρmin : ∀ i, ∃ c, 0 < c ∧ c < 1 ∧ ∀ u, (∀ j, u i ≤ u j) → ρ u i ≤ c := by
        intro i
        obtain ⟨j0, hj0⟩ : ∃ j0, j0 ≠ i := by
          by_cases h : i.val = 0
          · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
          · exact ⟨⟨0, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
        have hl0 := hlam j0
        have hli := hlam i
        refine ⟨lam i / (lam i + lam j0), by positivity, by rw [div_lt_one (by linarith)]; linarith, ?_⟩
        intro u hu
        rw [hρE, ← hexpint (lam i) (lam j0) hli hl0.le]
        refine integral_mono_ae (hEint u i) ?_ ?_
        · refine Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop) ?_
          filter_upwards [hnn (lam i)] with s hs
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
          nlinarith
        · filter_upwards [hnn (lam i)] with s hs
          simp only [hE]
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j0), if_neg hj0]
          have h1 : (∏ x ∈ Finset.univ.erase j0, if x = i then (1:ℝ) else
              Real.exp (-(lam x * (max (u x - u i + s) 0 - max (u x - u i) 0)))) ≤ 1 := by
            refine Finset.prod_le_one (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
            split_ifs
            · exact le_rfl
            · rw [Real.exp_le_one_iff]
              have := hlam j
              have := hbnn (u j - u i) s hs
              nlinarith
          have h2 : max (u j0 - u i + s) 0 - max (u j0 - u i) 0 = s := by
            have := hu j0
            rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
          rw [h2]
          have h3 : 0 ≤ (∏ x ∈ Finset.univ.erase j0, if x = i then (1:ℝ) else
              Real.exp (-(lam x * (max (u x - u i + s) 0 - max (u x - u i) 0)))) :=
            Finset.prod_nonneg fun j _ => by split_ifs <;> positivity
          have h4 := Real.exp_pos (-(lam j0 * s))
          nlinarith
      have hΦupd : ∀ u i x t, Φ (Function.update u i x) i t = Φ u i t := by
        intro u i x t
        refine Finset.prod_congr rfl fun j _ => ?_
        split_ifs with h
        · rfl
        · rw [Function.update_of_ne h]
      have F2 : ∀ u i x, HasDerivAt (fun y => choiceProb (Function.update u i y) lam i)
          (lam i * (Φ u i x - choiceProb (Function.update u i x) lam i)) x := by
        intro u i x
        set r := lam i with hr
        have hrpos : 0 < r := hlam i
        set g : ℝ → ℝ := fun t => Real.exp (r * t) * Φ u i t with hg
        have hgcont : Continuous g :=
          (by fun_prop : Continuous fun t => Real.exp (r * t)).mul (hΦcont u i)
        have hgint : ∀ a, IntegrableOn g (Set.Iic a) := by
          intro a
          refine Integrable.mono' (integrableOn_exp_mul_Iic hrpos a)
            hgcont.aestronglyMeasurable ?_
          filter_upwards with t
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hΦnn _ _ _))]
          exact mul_le_of_le_one_right (Real.exp_pos _).le (hΦle _ _ _)
        set G : ℝ → ℝ := fun y => ∫ t in Set.Iic y, g t with hG
        have hQG : ∀ y, choiceProb (Function.update u i y) lam i = r * Real.exp (-(r * y)) * G y := by
          intro y
          rw [hQform]
          simp only [Function.update_self, hΦupd]
          rw [hexp, integral_withDensity_eq_integral_toReal_smul (hpdfm r) (hpdft r)]
          have e1 : (fun s => (exponentialPDF r s).toReal • Φ u i (y - s)) =
              fun s => (fun t => (Set.Iic y).indicator
                (fun t => r * Real.exp (-(r * y)) * g t) t) (y - s) := by
            funext s
            simp only [Set.indicator_apply, Set.mem_Iic, smul_eq_mul, hpdfr r hrpos, hg]
            by_cases h1 : 0 ≤ s
            · have h2 : y - s ≤ y := by linarith
              rw [if_pos h1, if_pos h2]
              have : Real.exp (-(r * y)) * Real.exp (r * (y - s)) = Real.exp (-(r * s)) := by
                rw [← Real.exp_add]; ring_nf
              rw [show r * Real.exp (-(r * y)) * (Real.exp (r * (y - s)) * Φ u i (y - s)) =
                r * Φ u i (y - s) * (Real.exp (-(r * y)) * Real.exp (r * (y - s))) by ring, this]
              ring
            · have h2 : ¬ (y - s ≤ y) := by intro h; exact h1 (by linarith)
              rw [if_neg h1, if_neg h2]; ring
          rw [e1, integral_sub_left_eq_self (fun t => (Set.Iic y).indicator
                (fun t => r * Real.exp (-(r * y)) * g t) t),
            integral_indicator measurableSet_Iic, integral_const_mul]
        have hGeq : ∀ y, G y = G 0 + ∫ t in (0:ℝ)..y, g t := by
          intro y
          have := intervalIntegral.integral_Iic_sub_Iic (hgint 0) (hgint y)
          simp only [hG]; linarith
        have hGd : HasDerivAt G (g x) x := by
          have h := (hgcont.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add (G 0)
          exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hGeq)
        have hfun : (fun y => choiceProb (Function.update u i y) lam i) =
            fun y => r * Real.exp (-(r * y)) * G y := funext hQG
        rw [hfun]
        have h0 : HasDerivAt (fun y : ℝ => -(r * y)) (-(r * 1)) x :=
          ((hasDerivAt_id x).const_mul r).neg
        have hE1 := h0.exp.const_mul r
        refine (hE1.mul hGd).congr_deriv ?_
        rw [hQG x]
        simp only [hg]
        have : Real.exp (-(r * x)) * Real.exp (r * x) = 1 := by rw [← Real.exp_add]; simp
        linear_combination (r * Φ u i x) * this
      have hΦpos : ∀ u i t, 0 < Φ u i t := by
        intro u i t
        exact Finset.prod_pos fun j _ => by split_ifs <;> positivity
      have hρtrans : ∀ u i c, ρ (fun j => u j + c) i = ρ u i := by
        intro u i c
        simp only [hρ]
        congr 1
        funext s
        refine Finset.prod_congr rfl fun j _ => ?_
        split_ifs
        · rfl
        · ring_nf
      -- derived facts
      have hQpos : ∀ u i, 0 < choiceProb u lam i := by
        intro u i; rw [hQρ]; exact mul_pos (hΦpos _ _ _) (hρpos _ _)
      set D : (Fin n → ℝ) → Fin n → ℝ := fun u i => lam i * (1 / ρ u i - 1) with hD
      have hDnn : ∀ u i, 0 ≤ D u i := by
        intro u i
        have h1 := hρpos u i
        have h2 := hρle u i
        have : 1 ≤ 1 / ρ u i := by rw [le_div_iff₀ h1]; linarith
        exact mul_nonneg (hlam i).le (by linarith)
      have hDmono : ∀ u w i, u i = w i → (∀ j, j ≠ i → u j ≤ w j) → D u i ≤ D w i := by
        intro u w i h1 h2
        have := hρmono u w i h1 h2
        have := hρpos w i
        have : 1 / ρ u i ≤ 1 / ρ w i := one_div_le_one_div_of_le (hρpos w i) (hρmono u w i h1 h2)
        exact mul_le_mul_of_nonneg_left (by linarith) (hlam i).le
      have hDtrans : ∀ u i c, D (fun j => u j + c) i = D u i := by
        intro u i c
        show lam i * (1 / ρ (fun j => u j + c) i - 1) = lam i * (1 / ρ u i - 1)
        rw [hρtrans]
      have hDown : ∀ u i x y, x ≤ y → D (Function.update u i y) i ≤ D (Function.update u i x) i := by
        intro u i x y hxy
        have e : D (Function.update u i y) i =
            D (fun j => Function.update u i y j + (x - y)) i := (hDtrans _ _ _).symm
        rw [e]
        apply hDmono
        · simp
        · intro j hj
          simp only [Function.update_of_ne hj]
          linarith
      have hR : ∀ u i x, HasDerivAt (fun y => (α i - y) * choiceProb (Function.update u i y) lam i)
          (choiceProb (Function.update u i x) lam i *
            ((α i - x) * D (Function.update u i x) i - 1)) x := by
        intro u i x
        have h1 : HasDerivAt (fun y : ℝ => α i - y) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub (α i)
        have hq : choiceProb (Function.update u i x) lam i = Φ u i x * ρ (Function.update u i x) i := by
          have := hQρ (Function.update u i x) i
          rwa [hΦupd, Function.update_self] at this
        have hp := hρpos (Function.update u i x) i
        refine (h1.mul (F2 u i x)).congr_deriv ?_
        show _ = choiceProb (Function.update u i x) lam i *
            ((α i - x) * (lam i * (1 / ρ (Function.update u i x) i - 1)) - 1)
        rw [hq]
        field_simp
        ring
      have hRcont : ∀ u i, Continuous (fun y => (α i - y) * choiceProb (Function.update u i y) lam i) :=
        fun u i => continuous_iff_continuousAt.2 fun x => (hR u i x).continuousAt
      have hQcont : ∀ u i, Continuous (fun y => choiceProb (Function.update u i y) lam i) :=
        fun u i => continuous_iff_continuousAt.2 fun x => (F2 u i x).continuousAt
      have hρcont : ∀ u i, Continuous (fun y => ρ (Function.update u i y) i) := by
        intro u i
        have e : (fun y => ρ (Function.update u i y) i) =
            fun y => choiceProb (Function.update u i y) lam i / Φ u i y := by
          funext y
          have hq : choiceProb (Function.update u i y) lam i = Φ u i y * ρ (Function.update u i y) i := by
            have := hQρ (Function.update u i y) i
            rwa [hΦupd, Function.update_self] at this
          rw [hq]; field_simp [(hΦpos u i y).ne']
        rw [e]
        exact (hQcont u i).div (hΦcont u i) fun y => (hΦpos u i y).ne'
      have hDcont : ∀ u i, Continuous (fun y => D (Function.update u i y) i) := by
        intro u i
        simp only [hD]
        exact continuous_const.mul (((continuous_const.div (hρcont u i)
          fun y => (hρpos _ _).ne')).sub continuous_const)
      -- price / utility conversions
      have hutil : ∀ (p : Fin n → ℝ) i q, util α β (Function.update p i q) =
          Function.update (util α β p) i (α i - β * q) := by
        intro p i q
        funext j
        by_cases h : j = i
        · subst h; simp [util]
        · simp [util, Function.update_of_ne h]
      have hrev : ∀ (p : Fin n → ℝ) i q, β * firmRevenue α β lam (Function.update p i q) i =
          (α i - (α i - β * q)) * choiceProb (Function.update (util α β p) i (α i - β * q)) lam i := by
        intro p i q
        simp only [firmRevenue, hutil, Function.update_self]
        ring
      have hrev0 : ∀ (p : Fin n → ℝ) i, β * firmRevenue α β lam p i =
          (α i - util α β p i) * choiceProb (util α β p) lam i := by
        intro p i
        simp only [firmRevenue, util]
        ring
      -- NE implies FOC
      have foc : ∀ p, IsPriceNE α β lam p → ∀ i,
          util α β p i < α i ∧ (α i - util α β p i) * D (util α β p) i = 1 := by
        intro p hp i
        set u := util α β p with hu
        have hpos : 0 < p i := by
          rcases (hp.1 i).lt_or_eq with h | h
          · exact h
          · exfalso
            have h1 := hp.2 i 1 zero_le_one
            have h2 : firmRevenue α β lam p i = 0 := by simp [firmRevenue, ← h]
            have h3 : 0 < firmRevenue α β lam (Function.update p i 1) i := by
              simp only [firmRevenue, Function.update_self, one_mul]
              exact hQpos _ _
            linarith
        have hlt : u i < α i := by simp only [hu, util]; nlinarith
        refine ⟨hlt, ?_⟩
        have hmax : IsLocalMax (fun y => (α i - y) * choiceProb (Function.update u i y) lam i) (u i) := by
          filter_upwards [Iio_mem_nhds hlt] with y hy
          have h1 := hp.2 i ((α i - y) / β) (div_nonneg (by linarith [Set.mem_Iio.1 hy]) hβ.le)
          have h2 := hrev p i ((α i - y) / β)
          have h3 := hrev0 p i
          have e : α i - β * ((α i - y) / β) = y := by field_simp; ring
          rw [e] at h2
          simp only [Function.update_eq_self]
          rw [← hu] at h2 h3
          rw [← h2, ← h3]
          exact mul_le_mul_of_nonneg_left h1 hβ.le
        have h0 := hmax.hasDerivAt_eq_zero (hR u i (u i))
        simp only [Function.update_eq_self] at h0
        have := hQpos u i
        rcases mul_eq_zero.1 h0 with h | h
        · linarith
        · linarith
      -- uniqueness core
      have key : ∀ p p', IsPriceNE α β lam p → IsPriceNE α β lam p' →
          ∀ k, util α β p' k ≤ util α β p k := by
        intro p p' hp hp' k
        set u := util α β p
        set v := util α β p'
        have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
        obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => v j - u j)
          Finset.univ_nonempty
        by_contra hk
        push Not at hk
        have hk2 : v k - u k ≤ v i - u i := hi k (Finset.mem_univ _)
        set d := v i - u i with hd
        have hdpos : 0 < d := by linarith
        have h1 : D v i ≤ D (fun j => u j + d) i := by
          apply hDmono
          · simp [hd]
          · intro j _
            have : v j - u j ≤ v i - u i := hi j (Finset.mem_univ _)
            linarith
        rw [hDtrans] at h1
        obtain ⟨hu1, hu2⟩ := foc p hp i
        obtain ⟨hv1, hv2⟩ := foc p' hp' i
        have hDu : 0 < D u i := by
          by_contra hneg
          push Not at hneg
          nlinarith [hDnn u i]
        have : v i = u i + d := by rw [hd]; ring
        nlinarith [hDnn v i]
      have hex : ∃ p, IsPriceNE α β lam p := by
        have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
        choose c hc0 hc1 hcρ using hρmin
        set δ : Fin n → ℝ := fun i => lam i * (1 / c i - 1) with hδ
        have hδpos : ∀ i, 0 < δ i := by
          intro i
          have : 1 < 1 / c i := by rw [lt_div_iff₀ (hc0 i)]; linarith [hc1 i]
          exact mul_pos (hlam i) (by linarith)
        set lo : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i => α i - 1 / δ i) with hlodef
        set hi : ℝ := Finset.univ.sup' Finset.univ_nonempty α with hhidef
        have hlo : ∀ i, lo ≤ α i - 1 / δ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
        have hhi : ∀ i, α i ≤ hi := fun i => Finset.le_sup' α (Finset.mem_univ i)
        have hlohi : lo ≤ hi := by
          obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
          have := hlo i
          have := hhi i
          have : 0 < 1 / δ i := by have := hδpos i; positivity
          linarith
        set K : (Fin n → ℝ) → Fin n → ℝ → ℝ := fun u i x => (α i - x) * D (Function.update u i x) i
          with hK
        set S : (Fin n → ℝ) → Fin n → Set ℝ := fun u i => {x | x ≤ α i ∧ 1 ≤ K u i x} with hS
        set BR : (Fin n → ℝ) → Fin n → ℝ := fun u i => sSup (S u i) with hBR
        have hKcont : ∀ u i, Continuous (K u i) := fun u i =>
          (continuous_const.sub continuous_id).mul (hDcont u i)
        have hlomem : ∀ u i, (∀ j, lo ≤ u j) → lo ∈ S u i := by
          intro u i hu
          have h1 := hlo i
          have hd := hδpos i
          refine ⟨by have : 0 < 1 / δ i := by positivity
                     linarith, ?_⟩
          have hρc : ρ (Function.update u i lo) i ≤ c i := by
            apply hcρ
            intro j
            by_cases hj : j = i
            · subst hj; exact le_rfl
            · rw [Function.update_of_ne hj, Function.update_self]; exact hu j
          have hp := hρpos (Function.update u i lo) i
          have hD1 : δ i ≤ D (Function.update u i lo) i := by
            show lam i * (1 / c i - 1) ≤ lam i * (1 / ρ (Function.update u i lo) i - 1)
            have : 1 / c i ≤ 1 / ρ (Function.update u i lo) i := one_div_le_one_div_of_le hp hρc
            exact mul_le_mul_of_nonneg_left (by linarith) (hlam i).le
          have h2 : 1 ≤ (α i - lo) * δ i := by
            have : 1 / δ i ≤ α i - lo := by linarith
            rw [div_le_iff₀ hd] at this
            linarith
          show 1 ≤ (α i - lo) * D (Function.update u i lo) i
          have : 0 ≤ α i - lo := by have : 0 < 1 / δ i := by positivity
                                    linarith
          nlinarith
        have hSbdd : ∀ u i, BddAbove (S u i) := fun u i => ⟨α i, fun x hx => hx.1⟩
        have hSclosed : ∀ u i, IsClosed (S u i) := fun u i =>
          (isClosed_le continuous_id continuous_const).inter
            (isClosed_le continuous_const (hKcont u i))
        have hBRmem : ∀ u i, (∀ j, lo ≤ u j) → BR u i ∈ S u i := fun u i hu =>
          (hSclosed u i).csSup_mem ⟨lo, hlomem u i hu⟩ (hSbdd u i)
        have hBRlo : ∀ u i, (∀ j, lo ≤ u j) → lo ≤ BR u i := fun u i hu =>
          le_csSup (hSbdd u i) (hlomem u i hu)
        have hBRhi : ∀ u i, (∀ j, lo ≤ u j) → BR u i ≤ α i := fun u i hu =>
          (hBRmem u i hu).1
        have hKanti : ∀ u i x y, x ≤ y → y ≤ α i → K u i y ≤ K u i x := by
          intro u i x y hxy hy
          show (α i - y) * D (Function.update u i y) i ≤ (α i - x) * D (Function.update u i x) i
          have h1 := hDown u i x y hxy
          have h2 := hDnn (Function.update u i y) i
          have h3 := hDnn (Function.update u i x) i
          nlinarith
        have hBRmax : ∀ u i, (∀ j, lo ≤ u j) → ∀ x, x ≤ α i →
            (α i - x) * choiceProb (Function.update u i x) lam i ≤
              (α i - BR u i) * choiceProb (Function.update u i (BR u i)) lam i := by
          intro u i hu x hx
          have hb := hBRmem u i hu
          rcases le_total x (BR u i) with hxb | hxb
          · have hmon : MonotoneOn (fun y => (α i - y) * choiceProb (Function.update u i y) lam i)
                (Set.Icc x (BR u i)) := by
              refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hRcont u i).continuousOn
                (fun y _ => (hR u i y).differentiableAt.differentiableWithinAt) ?_
              intro y hy
              rw [interior_Icc] at hy
              rw [(hR u i y).deriv]
              have := hKanti u i y (BR u i) hy.2.le hb.1
              have h2 : 1 ≤ K u i (BR u i) := hb.2
              have h3 : 0 ≤ K u i y - 1 := by linarith
              exact mul_nonneg (hQpos _ _).le h3
            exact hmon ⟨le_rfl, hxb⟩ ⟨hxb, le_rfl⟩ hxb
          · have hmon : AntitoneOn (fun y => (α i - y) * choiceProb (Function.update u i y) lam i)
                (Set.Icc (BR u i) x) := by
              refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hRcont u i).continuousOn
                (fun y _ => (hR u i y).differentiableAt.differentiableWithinAt) ?_
              intro y hy
              rw [interior_Icc] at hy
              rw [(hR u i y).deriv]
              have hyS : y ∉ S u i := fun hyS => by
                have := le_csSup (hSbdd u i) hyS
                linarith [hy.1]
              have hK : K u i y < 1 := by
                by_contra hcon
                push Not at hcon
                exact hyS ⟨by linarith [hy.2], hcon⟩
              have h3 : K u i y - 1 ≤ 0 := by linarith
              exact mul_nonpos_of_nonneg_of_nonpos (hQpos _ _).le h3
            exact hmon ⟨le_rfl, hxb⟩ ⟨hxb, le_rfl⟩ hxb
        have hBRmono : ∀ u w i, (∀ j, lo ≤ u j) → (∀ j, u j ≤ w j) → BR u i ≤ BR w i := by
          intro u w i hu huw
          refine csSup_le_csSup (hSbdd w i) ⟨lo, hlomem u i hu⟩ ?_
          intro x hx
          refine ⟨hx.1, ?_⟩
          have h1 : D (Function.update u i x) i ≤ D (Function.update w i x) i := by
            apply hDmono
            · simp
            · intro j hj
              rw [Function.update_of_ne hj, Function.update_of_ne hj]
              exact huw j
          have h2 : 1 ≤ (α i - x) * D (Function.update u i x) i := hx.2
          show 1 ≤ (α i - x) * D (Function.update w i x) i
          have : 0 ≤ α i - x := by linarith [hx.1]
          nlinarith
        haveI : Fact (lo ≤ hi) := ⟨hlohi⟩
        let F : (Fin n → Set.Icc lo hi) →o (Fin n → Set.Icc lo hi) :=
          { toFun := fun u i => ⟨BR (fun j => (u j : ℝ)) i, hBRlo _ i (fun j => (u j).2.1),
              (hBRhi _ i (fun j => (u j).2.1)).trans (hhi i)⟩
            monotone' := fun u w huw i => by
              show BR (fun j => (u j : ℝ)) i ≤ BR (fun j => (w j : ℝ)) i
              exact hBRmono _ _ i (fun j => (u j).2.1) (fun j => huw j) }
        have hfix := OrderHom.map_lfp F
        set us := OrderHom.lfp F with hus
        set ustar : Fin n → ℝ := fun j => (us j : ℝ) with hustar
        have hulo : ∀ j, lo ≤ ustar j := fun j => (us j).2.1
        have hfixi : ∀ i, BR ustar i = ustar i := fun i =>
          congrArg Subtype.val (congrFun hfix i)
        set p : Fin n → ℝ := fun i => (α i - ustar i) / β with hp
        have hup : util α β p = ustar := by
          funext j
          simp only [util, hp]
          field_simp
          ring
        refine ⟨p, ?_, ?_⟩
        · intro i
          have := hBRhi ustar i hulo
          rw [hfixi] at this
          exact div_nonneg (by linarith) hβ.le
        · intro i q hq
          have h1 := hrev p i q
          have h2 := hrev0 p i
          rw [hup] at h1 h2
          have h3 := hBRmax ustar i hulo (α i - β * q) (by nlinarith)
          rw [hfixi, Function.update_eq_self] at h3
          have : β * firmRevenue α β lam (Function.update p i q) i ≤ β * firmRevenue α β lam p i := by
            rw [h1, h2]; exact h3
          exact le_of_mul_le_mul_left this hβ
      obtain ⟨p, hp⟩ := hex
      refine ⟨p, hp, fun p' hp' => ?_⟩
      funext k
      have h1 := key p p' hp hp' k
      have h2 := key p' p hp' hp k
      simp only [util] at h1 h2
      have : β * p' k = β * p k := by linarith
      exact mul_left_cancel₀ hβ.ne' this
