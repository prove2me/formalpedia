-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:17.226851+00:00
-- url     : https://prove2.me/submissions/e55481ee-5c4c-4c3f-976f-6b0a90913384

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (u : Fin n → ℝ) :
    (∀ m, (∀ j, u j ≤ u m) →
        consumerSurplus u lam = u m - 1 / lam m * choiceProb u lam m) ∧
      ∀ i, HasDerivAt (fun t => consumerSurplus (Function.update u i t) lam)
        (choiceProb u lam i) (u i) := by
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
          have hid : ∀ r : ℝ, 0 < r → Integrable (fun x : ℝ => x) (expMeasure r) := by
            intro r hr
            rw [hexp, integrable_withDensity_iff_integrable_smul' (hpdfm r) (hpdft r)]
            have h1 := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := r)
              (by norm_num) (by norm_num) hr)
            simp only [Real.rpow_one] at h1
            rw [← integrableOn_Ici_iff_integrableOn_Ioi] at h1
            have h2 := (integrable_indicator_iff measurableSet_Ici).2 (IntegrableOn.integrable (Integrable.const_mul h1 r))
            refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
            simp only [Set.indicator_apply, Set.mem_Ici, smul_eq_mul, hpdfr r hr]
            split_ifs
            · rw [neg_mul]; ring
            · simp
          have hkey : ∀ r : ℝ, 0 < r → ∀ w : ℝ, 0 ≤ w →
              ∫ x, (min x w - 1 / r * (if x ≤ w then 1 else 0)) ∂(expMeasure r) = 0 := by
            intro r hr w hw
            rw [hexp, integral_withDensity_eq_integral_toReal_smul (hpdfm r) (hpdft r)]
            have e1 : (fun x => (exponentialPDF r x).toReal •
                (min x w - 1 / r * (if x ≤ w then (1:ℝ) else 0))) =
                (Set.Ici (0:ℝ)).indicator (fun x => r * Real.exp (-(r * x)) *
                  (min x w - 1 / r * (if x ≤ w then 1 else 0))) := by
              funext x
              simp only [Set.indicator_apply, Set.mem_Ici, smul_eq_mul, hpdfr r hr]
              split_ifs <;> simp
            rw [e1, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
              ← Set.Ioc_union_Ioi_eq_Ioi hw]
            have c1 : Set.EqOn (fun x => r * Real.exp (-(r * x)) *
                  (min x w - 1 / r * (if x ≤ w then 1 else 0)))
                  (fun x => (r * x - 1) * Real.exp (-(r * x))) (Set.Ioc 0 w) := by
              intro x hx
              simp only [min_eq_left hx.2, if_pos hx.2]
              field_simp
            have c2 : Set.EqOn (fun x => r * Real.exp (-(r * x)) *
                  (min x w - 1 / r * (if x ≤ w then 1 else 0)))
                  (fun x => (r * w) * Real.exp (-r * x)) (Set.Ioi w) := by
              intro x hx
              have hx' : w < x := hx
              simp only [min_eq_right hx'.le, if_neg (not_le.2 hx')]
              rw [neg_mul]; ring
            have i1 : IntegrableOn (fun x => (r * x - 1) * Real.exp (-(r * x))) (Set.Ioc 0 w) := by
              apply (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioc_subset_Icc_self
            have i2 : IntegrableOn (fun x => (r * w) * Real.exp (-r * x)) (Set.Ioi w) :=
              (exp_neg_integrableOn_Ioi w hr).const_mul _
            rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
              (i1.congr_fun c1.symm measurableSet_Ioc) (i2.congr_fun c2.symm measurableSet_Ioi),
              setIntegral_congr_fun measurableSet_Ioc c1, setIntegral_congr_fun measurableSet_Ioi c2,
              integral_const_mul, integral_exp_mul_Ioi (by linarith), ← intervalIntegral.integral_of_le hw]
            have d : ∀ x ∈ Set.uIcc 0 w, HasDerivAt (fun x => -x * Real.exp (-(r * x)))
                ((r * x - 1) * Real.exp (-(r * x))) x := by
              intro x _
              have h1 : HasDerivAt (fun x : ℝ => -(r * x)) (-(r * 1)) x :=
                ((hasDerivAt_id x).const_mul r).neg
              have h0 : HasDerivAt (fun x : ℝ => -x) (-1) x := (hasDerivAt_id x).neg
              exact (h0.mul h1.exp).congr_deriv (by ring)
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt d
              (Continuous.intervalIntegrable (by fun_prop) _ _)]
            field_simp
            ring_nf
          haveI hprob : ∀ j, IsProbabilityMeasure (expMeasure (lam j)) := fun j =>
            isProbabilityMeasure_expMeasure (hlam j)
          haveI hprobE : IsProbabilityMeasure (errorLaw lam) := by
            unfold errorLaw; infer_instance
          have hmeas : ∀ v : Fin n → ℝ, Measurable (fun z : Fin n → ℝ => ⨆ i, (v i - z i)) := by
            intro v
            exact Measurable.iSup (fun i => by fun_prop)
          have hbdd : ∀ v z : Fin n → ℝ, BddAbove (Set.range fun i => v i - z i) := fun v z =>
            (Set.finite_range _).bddAbove
          haveI hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
          have hevalI : ∀ i, Integrable (fun z : Fin n → ℝ => z i) (errorLaw lam) := by
            intro i
            exact (measurePreserving_eval (fun j => expMeasure (lam j)) i).integrable_comp_of_integrable
              (hid (lam i) (hlam i))
          have hint : ∀ v : Fin n → ℝ, Integrable (fun z : Fin n → ℝ => ⨆ i, (v i - z i))
              (errorLaw lam) := by
            intro v
            have hs : Integrable (fun z : Fin n → ℝ => ∑ i, |v i - z i|) (errorLaw lam) :=
              integrable_finset_sum _ fun i _ => ((integrable_const (v i)).sub (hevalI i)).abs
            refine hs.mono' (hmeas v).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
            rw [Real.norm_eq_abs, abs_le]
            have hsing : ∀ i, |v i - z i| ≤ ∑ i, |v i - z i| := fun i =>
              Finset.single_le_sum (f := fun i => |v i - z i|) (fun j _ => abs_nonneg _)
                (Finset.mem_univ i)
            constructor
            · obtain ⟨i⟩ := hne
              have h1 := le_ciSup (hbdd v z) i
              have h2 := hsing i
              have h3 := neg_abs_le (v i - z i)
              linarith
            · exact ciSup_le fun i => (le_abs_self _).trans (hsing i)
          have hSmeas : ∀ i, MeasurableSet {z : Fin n → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i} := by
            intro i
            simp only [Set.setOf_forall]
            refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
            exact measurableSet_le (by fun_prop) (by fun_prop)
          have hnnE : ∀ᵐ z ∂(errorLaw lam), ∀ j, 0 ≤ z j := by
            rw [ae_all_iff]
            intro j
            exact (measurePreserving_eval (fun j => expMeasure (lam j)) j).quasiMeasurePreserving.ae
              (hnn (lam j))
          have htie : ∀ i j, j ≠ i → ∀ᵐ z ∂(errorLaw lam), u j - z j ≠ u i - z i := by
            intro i j hij
            have hind : IndepFun (fun z : Fin n → ℝ => z j) (fun z : Fin n → ℝ => z i)
                (errorLaw lam) :=
              (iIndepFun_pi (μ := fun j => expMeasure (lam j)) (X := fun _ x => x)
                (fun _ => aemeasurable_id)).indepFun hij
            rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
              (measurable_pi_apply _).aemeasurable] at hind
            have m1 : (errorLaw lam).map (fun z : Fin n → ℝ => z j) = expMeasure (lam j) :=
              (measurePreserving_eval (fun j => expMeasure (lam j)) j).map_eq
            have m2 : (errorLaw lam).map (fun z : Fin n → ℝ => z i) = expMeasure (lam i) :=
              (measurePreserving_eval (fun j => expMeasure (lam j)) i).map_eq
            rw [m1, m2] at hind
            have hms : MeasurableSet {p : ℝ × ℝ | u j - p.1 = u i - p.2} :=
              measurableSet_eq_fun (by fun_prop) (by fun_prop)
            have h0 : ((expMeasure (lam j)).prod (expMeasure (lam i)))
                {p : ℝ × ℝ | u j - p.1 = u i - p.2} = 0 := by
              rw [Measure.measure_prod_null hms]
              refine Filter.Eventually.of_forall fun x => ?_
              refine measure_mono_null ?_ (hnoatom (lam i) (u i - u j + x))
              intro y hy
              simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
              simp only [Set.mem_singleton_iff]
              linarith
            rw [← hind, Measure.map_apply (by fun_prop) hms] at h0
            rw [ae_iff]
            simpa using h0
          refine ⟨?_, ?_⟩
          · intro m hm
            obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
            set S := {z : Fin (k+1) → ℝ | ∀ j, j ≠ m → u j - z j ≤ u m - z m} with hS
            have hf1 : Integrable (S.indicator (fun _ => (1:ℝ))) (errorLaw lam) :=
              (integrable_const (1:ℝ)).indicator (hSmeas m)
            have hQ : choiceProb u lam m = ∫ z, S.indicator (fun _ => (1:ℝ)) z ∂(errorLaw lam) := by
              rw [integral_indicator_const _ (hSmeas m)]
              simp [choiceProb, Measure.real, hS]
            set f : (Fin (k+1) → ℝ) → ℝ := fun z =>
              (u m - ⨆ i, (u i - z i)) - 1 / lam m * S.indicator (fun _ => (1:ℝ)) z with hf
            have hfint : Integrable f (errorLaw lam) :=
              ((integrable_const (u m)).sub (hint u)).sub (hf1.const_mul _)
            have hfval : ∫ z, f z ∂(errorLaw lam) =
                u m - consumerSurplus u lam - 1 / lam m * choiceProb u lam m := by
              have a1 : ∫ z, f z ∂(errorLaw lam) = (∫ z, (u m - ⨆ i, (u i - z i)) ∂(errorLaw lam)) -
                  ∫ z, 1 / lam m * S.indicator (fun _ => (1:ℝ)) z ∂(errorLaw lam) :=
                integral_sub ((integrable_const (u m)).sub (hint u)) (hf1.const_mul _)
              rw [a1, integral_sub (integrable_const (u m)) (hint u), integral_const_mul, ← hQ]
              simp [consumerSurplus]
            suffices h : ∫ z, f z ∂(errorLaw lam) = 0 by linarith
            have hmp := measurePreserving_piFinSuccAbove (fun j => expMeasure (lam j)) m
            have hmps := hmp.symm
            have e1 : ∫ z, f z ∂(errorLaw lam) =
                ∫ p, f ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) m).symm p)
                  ∂((expMeasure (lam m)).prod (Measure.pi fun j => expMeasure (lam (m.succAbove j)))) :=
              (hmps.integral_comp' f).symm
            have i1 : Integrable (fun p => f ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) m).symm p))
                ((expMeasure (lam m)).prod (Measure.pi fun j => expMeasure (lam (m.succAbove j)))) :=
              hmps.integrable_comp_of_integrable hfint
            rw [e1, integral_prod_symm _ i1]
            have hnn2 : ∀ᵐ y ∂(Measure.pi fun j => expMeasure (lam (m.succAbove j))), ∀ j, 0 ≤ y j := by
              rw [ae_all_iff]
              intro j
              exact (measurePreserving_eval (fun j => expMeasure (lam (m.succAbove j))) j).quasiMeasurePreserving.ae
                (hnn (lam (m.succAbove j)))
            rw [← integral_zero (Fin k → ℝ) ℝ (μ := Measure.pi fun j => expMeasure (lam (m.succAbove j)))]
            refine integral_congr_ae ?_
            filter_upwards [hnn2] with y hy
            haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
            have hb : BddAbove (Set.range fun j => u (m.succAbove j) - y j) :=
              (Set.finite_range _).bddAbove
            have hw : 0 ≤ u m - ⨆ j, (u (m.succAbove j) - y j) := by
              rw [sub_nonneg]
              exact ciSup_le fun j => by linarith [hy j, hm (m.succAbove j)]
            rw [← hkey (lam m) (hlam m) _ hw]
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            have hsy : (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) m).symm (x, y) =
                (m.insertNth x y : Fin (k+1) → ℝ) := rfl
            set W := ⨆ j, (u (m.succAbove j) - y j) with hW
            have hsup : (⨆ i, (u i - (m.insertNth x y : Fin (k+1) → ℝ) i)) = max (u m - x) W := by
              apply le_antisymm
              · refine ciSup_le fun i => ?_
                rcases Fin.eq_self_or_eq_succAbove m i with rfl | ⟨j, rfl⟩
                · simp
                · rw [Fin.insertNth_apply_succAbove]
                  exact (le_ciSup hb j).trans (le_max_right _ _)
              · refine max_le ?_ ?_
                · have := le_ciSup (hbdd u (m.insertNth x y : Fin (k+1) → ℝ)) m
                  simpa using this
                · refine ciSup_le fun j => ?_
                  have := le_ciSup (hbdd u (m.insertNth x y : Fin (k+1) → ℝ)) (m.succAbove j)
                  simpa using this
            have hmem : (m.insertNth x y : Fin (k+1) → ℝ) ∈ S ↔ x ≤ u m - W := by
              rw [hS, Set.mem_setOf_eq]
              constructor
              · intro h
                have : W ≤ u m - x := ciSup_le fun j => by
                  have := h (m.succAbove j) (Fin.succAbove_ne m j)
                  simpa using this
                linarith
              · intro h i hi
                rcases Fin.eq_self_or_eq_succAbove m i with rfl | ⟨j, rfl⟩
                · exact absurd rfl hi
                · have := le_ciSup hb j
                  simp only [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
                  linarith
            simp only [hsy, hf, hsup, Set.indicator_apply, hmem]
            congr 1
            rcases le_total (u m - x) W with h | h
            · rw [max_eq_right h, min_eq_right (by linarith)]
            · rw [max_eq_left h, min_eq_left (by linarith)]; ring
          · intro i
            set S := {z : Fin n → ℝ | ∀ j, j ≠ i → u j - z j ≤ u i - z i} with hS
            have hQ : choiceProb u lam i = ∫ z, S.indicator (fun _ => (1:ℝ)) z ∂(errorLaw lam) := by
              rw [integral_indicator_const _ (hSmeas i)]
              simp [choiceProb, Measure.real, hS]
            rw [hQ]
            unfold consumerSurplus
            have hmono : ∀ (z : Fin n → ℝ) (s t : ℝ), (⨆ j, (Function.update u i s j - z j)) ≤
                (⨆ j, (Function.update u i t j - z j)) + |s - t| := by
              intro z s t
              refine ciSup_le fun j => ?_
              have h1 := le_ciSup (hbdd (Function.update u i t) z) j
              by_cases hj : j = i
              · subst hj
                simp only [Function.update_self] at h1 ⊢
                linarith [le_abs_self (s - t)]
              · simp only [Function.update_of_ne hj] at h1 ⊢
                linarith [abs_nonneg (s - t)]
            refine (hasDerivAt_integral_of_dominated_loc_of_lip
              (F := fun t z => ⨆ j, (Function.update u i t j - z j)) (bound := fun _ => 1)
              (s := Set.univ) Filter.univ_mem
              (Filter.Eventually.of_forall fun t => (hmeas _).aestronglyMeasurable)
              (hint _) ((measurable_const.indicator (hSmeas i)).aestronglyMeasurable)
              (Filter.Eventually.of_forall fun z => ?_) (integrable_const _) ?_).2
            · refine LipschitzWith.lipschitzOnWith ?_
              refine LipschitzWith.of_dist_le_mul fun s t => ?_
              simp only [Real.dist_eq]
              have h1 := hmono z s t
              have h2 := hmono z t s
              rw [abs_sub_comm t s] at h2
              simp only [Real.nnabs_of_nonneg zero_le_one, Real.toNNReal_one, NNReal.coe_one, one_mul]
              rw [abs_le]
              constructor <;> linarith
            · have hall : ∀ᵐ z ∂(errorLaw lam), ∀ j, j ≠ i → u j - z j ≠ u i - z i := by
                rw [ae_all_iff]
                intro j
                by_cases hj : j = i
                · exact Filter.Eventually.of_forall fun z h => absurd hj h
                · filter_upwards [htie i j hj] with z hz _ using hz
              filter_upwards [hall] with z hz
              by_cases hzS : z ∈ S
              · rw [Set.indicator_of_mem hzS]
                have hev : ∀ᶠ t in nhds (u i), ∀ j, j ≠ i → u j - z j < t - z i := by
                  rw [Filter.eventually_all]
                  intro j
                  by_cases hj : j = i
                  · exact Filter.Eventually.of_forall fun z h => absurd hj h
                  · have hlt : u j - z j < u i - z i := lt_of_le_of_ne (hzS j hj) (hz j hj)
                    have : ∀ᶠ t in nhds (u i), u j - z j + z i < t :=
                      lt_mem_nhds (by linarith)
                    filter_upwards [this] with t ht _
                    linarith
                have hbase : HasDerivAt (fun t : ℝ => t - z i) 1 (u i) :=
                  (hasDerivAt_id (u i)).sub_const _
                refine hbase.congr_of_eventuallyEq ?_
                filter_upwards [hev] with t ht
                apply le_antisymm
                · refine ciSup_le fun j => ?_
                  by_cases hj : j = i
                  · subst hj; simp
                  · rw [Function.update_of_ne hj]; exact (ht j hj).le
                · have := le_ciSup (hbdd (Function.update u i t) z) i
                  simpa using this
              · rw [Set.indicator_of_notMem hzS]
                have : ∃ j, j ≠ i ∧ u i - z i < u j - z j := by
                  by_contra hcon
                  push Not at hcon
                  exact hzS hcon
                obtain ⟨j, hj, hlt⟩ := this
                have hle : ∀ s t : ℝ, s - z i ≤ u j - z j →
                    (⨆ j, (Function.update u i s j - z j)) ≤ ⨆ j, (Function.update u i t j - z j) := by
                  intro s t hs
                  refine ciSup_le fun l => ?_
                  by_cases hl : l = i
                  · subst hl
                    have h1 := le_ciSup (hbdd (Function.update u l t) z) j
                    simp only [Function.update_of_ne hj, Function.update_self] at h1 ⊢
                    linarith
                  · have h1 := le_ciSup (hbdd (Function.update u i t) z) l
                    simp only [Function.update_of_ne hl] at h1 ⊢
                    exact h1
                refine (hasDerivAt_const (u i) (⨆ j, (Function.update u i (u i) j - z j))).congr_of_eventuallyEq ?_
                have : ∀ᶠ t in nhds (u i), t < u j - z j + z i := gt_mem_nhds (by linarith)
                filter_upwards [this] with t ht
                exact le_antisymm (hle _ _ (by linarith)) (hle _ _ hlt.le)
