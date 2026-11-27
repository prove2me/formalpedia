-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_13
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:08.353994+00:00
-- url     : https://prove2.me/submissions/4e5af765-b7df-4847-9528-ce589f8a8161

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (hα : ∀ i j, α i + 1 / lam i ≤ α j + 1 / lam j → α i ≤ α j ∧ lam i ≤ lam j)
    (σ : Fin n ≃ Fin n) (hσ : Monotone (fun s => α (σ s) + 1 / lam (σ s))) :
    (∃ ustar : Fin n → ℝ, IsOnePass α lam σ ustar) ∧
      ∀ ustar : Fin n → ℝ, IsOnePass α lam σ ustar →
        (∀ s : Fin n, 0 < s.val →
            ∃! x : ℝ, α (σ s) - x = tauCond α lam (solvedBefore σ s.val) ustar (σ s) x) ∧
          IsPriceNE α β lam (eqPrices α β ustar) ∧
          (∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar) ∧
          Monotone (fun s => eqPrices α β ustar (σ s)) ∧
          Monotone (fun s => choiceProb (util α β (eqPrices α β ustar)) lam (σ s)) ∧
          Monotone (fun s => firmRevenue α β lam (eqPrices α β ustar) (σ s)) := by
            classical
            obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
            have horder : ∀ s t : Fin (m + 1), s ≤ t →
                α (σ s) ≤ α (σ t) ∧ lam (σ s) ≤ lam (σ t) := by
              intro s t hst
              exact hα _ _ (hσ hst)
            have hsurv : ∀ (r : ℝ), 0 < r → ∀ t : ℝ,
                (expMeasure r).real (Set.Ici t) = Real.exp (-(r * max t 0)) := by
              intro r hr t
              letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
              letI : NullSingletonClass (expMeasure r) := by
                unfold expMeasure gammaMeasure
                infer_instance
              have hset : (expMeasure r).real (Set.Ici t) =
                  (expMeasure r).real (Set.Ioi t) := by
                exact congrArg ENNReal.toReal (measure_congr Ioi_ae_eq_Ici).symm
              rw [hset, ← Set.compl_Iic, measureReal_compl measurableSet_Iic,
                probReal_univ, ← cdf_eq_real, cdf_expMeasure_eq hr]
              by_cases ht : 0 ≤ t
              · rw [if_pos ht, max_eq_left ht]
                ring
              · rw [if_neg ht, max_eq_right (le_of_not_ge ht)]
                simp
            have hprob : ∀ i, IsProbabilityMeasure (expMeasure (lam i)) :=
              fun i => isProbabilityMeasure_expMeasure (hlam i)
            letI : ∀ i, IsProbabilityMeasure (expMeasure (lam i)) := hprob
            have htotal : 0 < ∑ i, lam i := by
              apply Finset.sum_pos
              · intro i hi
                exact hlam i
              · exact Finset.univ_nonempty
            have hQint : ∀ (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)),
                choiceProb u lam i = ∫ z, ∏ j : Fin m,
                  Real.exp (-(lam (i.succAbove j) * max (u (i.succAbove j) - u i + z) 0))
                  ∂expMeasure (lam i) := by
              intro u i
              let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
              let E : Set (ℝ × (Fin m → ℝ)) :=
                {z | ∀ j, j ≠ i → u j - e.symm z j ≤ u i - e.symm z i}
              have hE : MeasurableSet E := by
                dsimp [E]
                simp only [Set.setOf_forall]
                apply MeasurableSet.iInter
                intro j
                apply MeasurableSet.iInter
                intro hj
                exact measurableSet_le (measurable_const.sub ((measurable_pi_apply j).comp e.symm.measurable))
                  (measurable_const.sub ((measurable_pi_apply i).comp e.symm.measurable))
              have hW : MeasurableSet {z : Fin (m + 1) → ℝ |
                  ∀ j, j ≠ i → u j - z j ≤ u i - z i} := by
                measurability
              change (Measure.pi (fun j => expMeasure (lam j))).real _ = _
              rw [← integral_indicator_one hW]
              rw [← (measurePreserving_piFinSuccAbove (fun j => expMeasure (lam j)) i).symm.integral_comp']
              change (∫ z, E.indicator (fun _ : ℝ × (Fin m → ℝ) => (1 : ℝ)) z
                ∂(expMeasure (lam i)).prod (Measure.pi fun j => expMeasure (lam (i.succAbove j)))) = _
              rw [integral_prod _ ((integrable_const (1 : ℝ)).indicator hE)]
              apply integral_congr_ae
              filter_upwards [] with z
              have heq : (fun w => E.indicator (fun _ : ℝ × (Fin m → ℝ) => (1 : ℝ)) (z, w)) =
                  (Set.univ.pi fun j : Fin m => Set.Ici (u (i.succAbove j) - u i + z)).indicator
                    (fun _ : Fin m → ℝ => (1 : ℝ)) := by
                funext w
                have hmem : (z, w) ∈ E ↔
                    w ∈ Set.univ.pi (fun j : Fin m => Set.Ici (u (i.succAbove j) - u i + z)) := by
                  constructor
                  · intro hz j hj
                    have hzj := hz (i.succAbove j) (Fin.succAbove_ne i j)
                    have hzj' : u (i.succAbove j) - w j ≤ u i - z := by
                      simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hzj
                    change u (i.succAbove j) - u i + z ≤ w j
                    linarith
                  · intro hw j hji
                    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hji
                    subst j
                    have hwk := hw k (Set.mem_univ _)
                    have hh : u (i.succAbove k) - w k ≤ u i - z := by
                      simp only [Set.mem_Ici] at hwk
                      linarith
                    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply] using hh
                simp only [Set.indicator, hmem]
              rw [heq]
              have hrect := integral_indicator_one
                (μ := Measure.pi fun j : Fin m => expMeasure (lam (i.succAbove j)))
                (MeasurableSet.pi Set.countable_univ (fun j : Fin m => fun _ =>
                  (measurableSet_Ici : MeasurableSet (Set.Ici (u (i.succAbove j) - u i + z)))))
              change (∫ w, (Set.univ.pi fun j : Fin m => Set.Ici
                (u (i.succAbove j) - u i + z)).indicator 1 w
                ∂(Measure.pi fun j : Fin m => expMeasure (lam (i.succAbove j)))) = _
              rw [hrect]
              simp only [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
              apply Finset.prod_congr rfl
              intro j hj
              exact hsurv _ (hlam _) _
            have hdensity : ∀ (r : ℝ), 0 < r → ∀ g : ℝ → ℝ,
                (∫ z, g z ∂expMeasure r) =
                  ∫ z in Set.Ioi 0, r * Real.exp (-(r * z)) * g z := by
              intro r hr g
              change (∫ z, g z ∂(volume.withDensity (exponentialPDF r))) = _
              rw [integral_withDensity_eq_integral_toReal_smul]
              · rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
                apply integral_congr_ae
                filter_upwards [] with z
                rw [exponentialPDF_eq, ENNReal.toReal_ofReal]
                · simp only [smul_eq_mul, Set.indicator, Set.mem_Ici]
                  split_ifs <;> simp_all
                · split_ifs
                  · exact mul_nonneg hr.le (Real.exp_pos _).le
                  · exact le_rfl
              · exact (measurable_exponentialPDFReal r).ennreal_ofReal
              · exact Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top)
            have hshift : ∀ (f : ℝ → ℝ) (a : ℝ),
                (∫ z in Set.Ioi 0, f (a - z)) = ∫ t in Set.Iic a, f t := by
              intro f a
              have hneg := integral_comp_neg_Iic 0 (fun z => f (a - z))
              simp only [neg_zero, sub_neg_eq_add] at hneg
              rw [← hneg]
              rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
              rw [← integral_add_right_eq_self (Set.Iic a |>.indicator f) a]
              apply integral_congr_ae
              filter_upwards [] with t
              simp only [Set.indicator, Set.mem_Iic, add_le_iff_nonpos_left]
              split_ifs <;> simp_all [add_comm]
            let F : (Fin (m + 1) → ℝ) → ℝ → ℝ :=
              fun u t => Real.exp (-(∑ j, lam j * max (u j - t) 0))
            have hQ : ∀ (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)),
                choiceProb u lam i = lam i * ∫ t in Set.Iic (u i), F u t := by
              intro u i
              rw [hQint, hdensity _ (hlam _)]
              rw [← hshift (F u) (u i), ← integral_const_mul]
              apply setIntegral_congr_fun measurableSet_Ioi
              intro z hz
              dsimp [F]
              rw [Fin.sum_univ_succAbove (fun j => lam j * max (u j - (u i - z)) 0) i]
              rw [show u i - (u i - z) = z by ring, max_eq_left (le_of_lt hz)]
              rw [neg_add, Real.exp_add, mul_assoc]
              congr 1
              simp_rw [← Finset.sum_neg_distrib, Real.exp_sum]
              congr 1
              apply Finset.prod_congr rfl
              intro j hj
              congr 3
              ring
            have hFc : ∀ u, Continuous (F u) := by
              intro u
              dsimp [F]
              fun_prop
            have hFpos : ∀ u t, 0 < F u t := fun u t => Real.exp_pos _
            have hFle : ∀ u t, F u t ≤ 1 := by
              intro u t
              apply Real.exp_le_one_iff.mpr
              apply neg_nonpos.mpr
              exact Finset.sum_nonneg (fun j hj => mul_nonneg (hlam j).le (le_max_right _ _))
            have hFi : ∀ u x, IntegrableOn (F u) (Set.Iic x) := by
              intro u x
              refine ((integrableOn_exp_mul_Iic (hlam 0) x).const_mul
                (Real.exp (-(lam 0 * u 0)))).mono' (hFc u).aestronglyMeasurable ?_
              filter_upwards [] with t
              rw [Real.norm_eq_abs, abs_of_pos (hFpos u t), ← Real.exp_add]
              apply Real.exp_le_exp.mpr
              have ht : lam 0 * (u 0 - t) ≤ ∑ j, lam j * max (u j - t) 0 := by
                apply le_trans (mul_le_mul_of_nonneg_left (le_max_left (u 0 - t) (0 : ℝ)) (hlam 0).le)
                exact Finset.single_le_sum (f := fun j => lam j * max (u j - t) 0)
                  (fun j hj => mul_nonneg (hlam j).le (le_max_right _ _))
                  (Finset.mem_univ 0)
              dsimp [F]
              linarith
            have htranslate : ∀ (f : ℝ → ℝ) (a : ℝ),
                (∫ t in Set.Iic 0, f (a + t)) = ∫ t in Set.Iic a, f t := by
              intro f a
              have hh := (measurePreserving_add_left (volume : Measure ℝ) a).setIntegral_preimage_emb
                (Homeomorph.addLeft a).measurableEmbedding f (Set.Iic a)
              have hs : (fun t : ℝ => a + t) ⁻¹' Set.Iic a = Set.Iic 0 := by
                ext t
                simp only [Set.mem_preimage, Set.mem_Iic, add_le_iff_nonpos_right]
              rwa [hs] at hh
            let K : (Fin (m + 1) → ℝ) → ℝ → ℝ → ℝ := fun u x t => F u (x + t) / F u x
            let R : (Fin (m + 1) → ℝ) → ℝ → ℝ := fun u x => ∫ t in Set.Iic 0, K u x t
            have hKc : ∀ u x, Continuous (K u x) := by
              intro u x
              exact ((hFc u).comp (continuous_const.add continuous_id)).div_const _
            have hKi : ∀ u x, IntegrableOn (K u x) (Set.Iic 0) := by
              intro u x
              have hh := (measurePreserving_add_left (volume : Measure ℝ) x).integrableOn_comp_preimage
                (Homeomorph.addLeft x).measurableEmbedding (f := F u) (s := Set.Iic x)
              have hi : IntegrableOn (fun t => F u (x + t)) (Set.Iic 0) := by
                have hs : (fun t : ℝ => x + t) ⁻¹' Set.Iic x = Set.Iic 0 := by
                  ext t
                  simp only [Set.mem_preimage, Set.mem_Iic, add_le_iff_nonpos_right]
                simpa only [hs, Function.comp_def] using hh.mpr (hFi u x)
              exact hi.div_const _
            have hKpos : ∀ u x t, 0 < K u x t := by
              intro u x t
              exact div_pos (hFpos _ _) (hFpos _ _)
            have hRformula : ∀ u x, R u x = (∫ t in Set.Iic x, F u t) / F u x := by
              intro u x
              dsimp [R, K]
              rw [integral_div, htranslate]
            have hKexp : ∀ u x t, K u x t =
                Real.exp (-(∑ j, lam j * (max (u j - x - t) 0 - max (u j - x) 0))) := by
              intro u x t
              dsimp [K, F]
              rw [← Real.exp_sub]
              congr 1
              simp_rw [sub_add_eq_sub_sub, mul_sub, Finset.sum_sub_distrib]
              ring
            have hmax : ∀ a b t : ℝ, a ≤ b → t ≤ 0 →
                max (a - t) 0 - max a 0 ≤ max (b - t) 0 - max b 0 := by
              intro a b t hab ht
              simp only [max_def]
              split_ifs <;> linarith
            have hKmono : ∀ u x y t, x ≤ y → t ≤ 0 → K u x t ≤ K u y t := by
              intro u x y t hxy ht
              rw [hKexp, hKexp]
              apply Real.exp_le_exp.mpr
              apply neg_le_neg
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (hmax (u j - y) (u j - x) t (by linarith) ht)
                (hlam j).le
            have hRmono : ∀ u, Monotone (R u) := by
              intro u x y hxy
              exact integral_mono_ae (hKi u x) (hKi u y)
                ((ae_restrict_iff' measurableSet_Iic).mpr
                  (Filter.Eventually.of_forall fun t ht => hKmono u x y t hxy ht))
            have hRpos : ∀ u x, 0 < R u x := by
              intro u x
              apply (integral_pos_iff_support_of_nonneg (fun t => (hKpos u x t).le) (hKi u x)).mpr
              have hs : Function.support (K u x) = Set.univ := by
                ext t
                simp only [Function.mem_support, Set.mem_univ, iff_true]
                exact ne_of_gt (hKpos u x t)
              rw [hs, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
              simp
            have hprimitive : ∀ (f : ℝ → ℝ), Continuous f →
                (∀ x, IntegrableOn f (Set.Iic x)) → ∀ x,
                HasDerivAt (fun y => ∫ t in Set.Iic y, f t) (f x) x := by
              intro f hc hi x
              have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
                (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
              have he : (fun y => ∫ t in Set.Iic y, f t) =
                  (fun y => (∫ t in (0 : ℝ)..y, f t) + ∫ t in Set.Iic 0, f t) := by
                funext y
                have hh := intervalIntegral.integral_Iic_sub_Iic (hi 0) (hi y)
                linarith
              rw [he]
              exact hd.add_const _
            let C : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ → ℝ :=
              fun u i t => Real.exp (-(∑ j : Fin m, lam (i.succAbove j) * max (u (i.succAbove j) - t) 0))
            have hCc : ∀ u i, Continuous (C u i) := by
              intro u i
              dsimp [C]
              fun_prop
            have hCpos : ∀ u i t, 0 < C u i t := fun u i t => Real.exp_pos _
            have hCle : ∀ u i t, C u i t ≤ 1 := by
              intro u i t
              apply Real.exp_le_one_iff.mpr
              apply neg_nonpos.mpr
              exact Finset.sum_nonneg (fun j hj => mul_nonneg (hlam _).le (le_max_right _ _))
            have hHc : ∀ u i, Continuous (fun t => Real.exp (lam i * t) * C u i t) := by
              intro u i
              exact (continuous_const.mul continuous_id).rexp.mul (hCc u i)
            have hHi : ∀ u i x, IntegrableOn (fun t => Real.exp (lam i * t) * C u i t) (Set.Iic x) := by
              intro u i x
              refine (integrableOn_exp_mul_Iic (hlam i) x).mono' (hHc u i).aestronglyMeasurable ?_
              filter_upwards [] with t
              rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (hCpos _ _ _))]
              exact mul_le_of_le_one_right (Real.exp_pos _).le (hCle _ _ _)
            have hupdateF : ∀ u i x t, t ≤ x →
                F (Function.update u i x) t =
                  Real.exp (-(lam i * x)) * (Real.exp (lam i * t) * C u i t) := by
              intro u i x t htx
              dsimp [F, C]
              rw [Fin.sum_univ_succAbove _ i]
              simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne i _)]
              rw [max_eq_left (sub_nonneg.mpr htx), neg_add, Real.exp_add]
              rw [show -(lam i * (x - t)) = -(lam i * x) + lam i * t by ring, Real.exp_add]
              ring
            let J : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ → ℝ :=
              fun u i x => ∫ t in Set.Iic x, Real.exp (lam i * t) * C u i t
            have hQu : ∀ u i x, choiceProb (Function.update u i x) lam i =
                lam i * (Real.exp (-(lam i * x)) * J u i x) := by
              intro u i x
              rw [hQ, Function.update_self]
              congr 1
              dsimp [J]
              rw [← integral_const_mul]
              apply setIntegral_congr_fun measurableSet_Iic
              intro t ht
              exact hupdateF u i x t ht
            have hCuF : ∀ u i, C u i (u i) = F u (u i) := by
              intro u i
              dsimp [C, F]
              rw [Fin.sum_univ_succAbove _ i]
              simp
            have hD : ∀ u i x, HasDerivAt (fun y => choiceProb (Function.update u i y) lam i)
                (lam i * (C u i x - choiceProb (Function.update u i x) lam i)) x := by
              intro u i x
              have hj : HasDerivAt (J u i) (Real.exp (lam i * x) * C u i x) x :=
                hprimitive _ (hHc u i) (hHi u i) x
              have he := (((hasDerivAt_id x).const_mul (-(lam i))).exp.mul hj).const_mul (lam i)
              have hf : (fun y => lam i * (Real.exp (-(lam i) * y) * J u i y)) =
                  (fun y => choiceProb (Function.update u i y) lam i) := by
                funext y
                rw [hQu]
                simp only [neg_mul]
              simp only [Pi.mul_apply, id_eq, mul_one] at he
              rw [hf] at he
              convert he using 1 <;> try rfl
              rw [hQu]
              have hcancel : Real.exp (-(lam i) * x) * Real.exp (lam i * x) = 1 := by
                rw [← Real.exp_add]
                simp
              simp only [id_eq, mul_one, neg_mul] at he ⊢
              simp only [neg_mul] at hcancel
              nlinarith [congrArg (fun z : ℝ => lam i * C u i x * z) hcancel]
            have hpartial : ∀ u i, partialU (fun v => choiceProb v lam i) i u =
                lam i * (F u (u i) - choiceProb u lam i) := by
              intro u i
              have hd := (hD u i (u i)).deriv
              simpa only [partialU, Function.update_eq_self, hCuF] using hd
            have hKbound : ∀ u i t, t ≤ 0 → K u (u i) t ≤ Real.exp (lam i * t) := by
              intro u i t ht
              rw [hKexp]
              apply Real.exp_le_exp.mpr
              rw [Fin.sum_univ_succAbove _ i]
              simp only [sub_self, zero_sub, max_eq_left (neg_nonneg.mpr ht), max_self, sub_zero]
              have hh : 0 ≤ ∑ j : Fin m, lam (i.succAbove j) *
                  (max (u (i.succAbove j) - u i - t) 0 - max (u (i.succAbove j) - u i) 0) := by
                apply Finset.sum_nonneg
                intro j hj
                apply mul_nonneg (hlam _).le
                apply sub_nonneg.mpr
                exact max_le_max_right 0 (by linarith)
              linarith
            have hRlt : ∀ u i, R u (u i) < 1 / lam i := by
              intro u i
              have hae : K u (u i) ≤ᵐ[volume.restrict (Set.Iic 0)]
                  (fun t => Real.exp (lam i * t)) := by
                apply (ae_restrict_iff' measurableSet_Iic).mpr
                exact Filter.Eventually.of_forall (fun t ht => hKbound u i t ht)
              have heint : (∫ t in Set.Iic 0, Real.exp (lam i * t)) = 1 / lam i := by
                rw [integral_exp_mul_Iic (hlam i)]
                simp
              have hle := integral_mono_ae (hKi u (u i)) (integrableOn_exp_mul_Iic (hlam i) 0) hae
              change R u (u i) ≤ _ at hle
              rw [heint] at hle
              refine lt_of_le_of_ne hle ?_
              intro heq
              have heqa : K u (u i) =ᵐ[volume.restrict (Set.Iic 0)] (fun t => Real.exp (lam i * t)) := by
                apply (integral_eq_iff_of_ae_le (hKi u (u i))
                  (integrableOn_exp_mul_Iic (hlam i) 0) hae).mp
                exact heq.trans heint.symm
              have heqon := Measure.eqOn_of_ae_eq (μ := volume) heqa (hKc u (u i)).continuousOn
                ((continuous_const.mul continuous_id).rexp.continuousOn)
                (show Set.Iic (0 : ℝ) ⊆ closure (interior (Set.Iic (0 : ℝ))) by
                  rw [interior_Iic, closure_Iio])
              let k : Fin m := ⟨0, by omega⟩
              let c : ℝ := min (-1) (u (i.succAbove k) - u i - 1)
              have hc0 : c ≤ 0 := le_trans (min_le_left _ _) (by norm_num)
              have hcj : c < u (i.succAbove k) - u i := by
                dsimp [c]
                have hh := min_le_right (-1 : ℝ) (u (i.succAbove k) - u i - 1)
                linarith
              have hstrict : K u (u i) c < Real.exp (lam i * c) := by
                rw [hKexp]
                apply Real.exp_lt_exp.mpr
                rw [Fin.sum_univ_succAbove _ i]
                simp only [sub_self, zero_sub, max_eq_left (neg_nonneg.mpr hc0), max_self, sub_zero]
                have hp : 0 < ∑ j : Fin m, lam (i.succAbove j) *
                    (max (u (i.succAbove j) - u i - c) 0 - max (u (i.succAbove j) - u i) 0) := by
                  apply Finset.sum_pos'
                  · intro j hj
                    apply mul_nonneg (hlam _).le
                    exact sub_nonneg.mpr (max_le_max_right 0 (by linarith))
                  · refine ⟨k, Finset.mem_univ _, mul_pos (hlam _) ?_⟩
                    rw [max_eq_left (by linarith : 0 ≤ u (i.succAbove k) - u i - c)]
                    by_cases h : 0 ≤ u (i.succAbove k) - u i
                    · rw [max_eq_left h]
                      have hcneg : c < 0 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
                      linarith
                    · rw [max_eq_right (le_of_not_ge h)]
                      linarith
                linarith
              exact (ne_of_lt hstrict) (heqon hc0)
            have hden : ∀ u i, 0 < 1 - lam i * R u (u i) := by
              intro u i
              have hh := (lt_div_iff₀ (hlam i)).mp (hRlt u i)
              nlinarith
            have hQR : ∀ u i, choiceProb u lam i = lam i * (F u (u i) * R u (u i)) := by
              intro u i
              rw [hQ, hRformula]
              field_simp [ne_of_gt (hFpos u (u i))]
            have hQpos : ∀ u i, 0 < choiceProb u lam i := by
              intro u i
              rw [hQR]
              exact mul_pos (hlam i) (mul_pos (hFpos _ _) (hRpos _ _))
            have hpartialpos : ∀ u i, 0 < partialU (fun v => choiceProb v lam i) i u := by
              intro u i
              rw [hpartial, hQR]
              have hh := mul_pos (mul_pos (hlam i) (hFpos u (u i))) (hden u i)
              nlinarith only [hh]
            have htau : ∀ u i, tau u lam i = R u (u i) / (1 - lam i * R u (u i)) := by
              intro u i
              rw [tau, hpartial, hQR]
              rw [show lam i * (F u (u i) - lam i * (F u (u i) * R u (u i))) =
                (lam i * F u (u i)) * (1 - lam i * R u (u i)) by ring]
              have hl := ne_of_gt (hlam i)
              have hf := ne_of_gt (hFpos u (u i))
              have hd := ne_of_gt (hden u i)
              field_simp [hl, hf, hd]
              <;> ring
            have htaupos : ∀ u i, 0 < tau u lam i := by
              intro u i
              rw [htau]
              exact div_pos (hRpos _ _) (hden _ _)
            have hRrelative : ∀ u v i, (∀ j, u j - u i ≤ v j - v i) →
                R v (v i) ≤ R u (u i) := by
              intro u v i hrel
              apply integral_mono_ae (hKi _ _) (hKi _ _)
              apply (ae_restrict_iff' measurableSet_Iic).mpr
              apply Filter.Eventually.of_forall
              intro t ht
              rw [hKexp, hKexp]
              apply Real.exp_le_exp.mpr
              apply neg_le_neg
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (hmax _ _ _ (hrel j) ht) (hlam j).le
            have htaurelative : ∀ u v i, (∀ j, u j - u i ≤ v j - v i) →
                tau v lam i ≤ tau u lam i := by
              intro u v i hrel
              rw [htau, htau]
              apply (div_le_div_iff₀ (hden v i) (hden u i)).mpr
              have hh := hRrelative u v i hrel
              nlinarith only [hh]
            have htaumono : ∀ u i, Monotone (fun x => tau (Function.update u i x) lam i) := by
              intro u i x y hxy
              apply htaurelative
              intro j
              by_cases hji : j = i
              · subst j
                simp
              · simp only [Function.update_self, Function.update_of_ne hji]
                linarith
            have hCupdate : ∀ u i x t, C (Function.update u i x) i t = C u i t := by
              intro u i x t
              dsimp [C]
              simp only [Function.update_of_ne (Fin.succAbove_ne i _)]
            have htauu : ∀ u i x, tau (Function.update u i x) lam i =
                choiceProb (Function.update u i x) lam i /
                  (lam i * (C u i x - choiceProb (Function.update u i x) lam i)) := by
              intro u i x
              rw [tau, hpartial, ← hCuF, Function.update_self, hCupdate]
            have htauc : ∀ u i, Continuous (fun x => tau (Function.update u i x) lam i) := by
              intro u i
              have hqc : Continuous (fun x => choiceProb (Function.update u i x) lam i) :=
                continuous_iff_continuousAt.mpr (fun x => (hD u i x).continuousAt)
              have hd : ∀ x, lam i * (C u i x - choiceProb (Function.update u i x) lam i) ≠ 0 := by
                intro x
                have hh := hpartialpos (Function.update u i x) i
                rw [hpartial, ← hCuF, Function.update_self, hCupdate] at hh
                exact ne_of_gt hh
              have he : (fun x => tau (Function.update u i x) lam i) =
                  (fun x => choiceProb (Function.update u i x) lam i /
                  (lam i * (C u i x - choiceProb (Function.update u i x) lam i))) :=
                funext (htauu u i)
              rw [he]
              exact hqc.div (continuous_const.mul ((hCc u i).sub hqc)) hd
            have hLminus : ∀ i, 0 < Ltot lam - lam i := by
              intro i
              rw [Ltot, Fin.sum_univ_succAbove _ i]
              simp only [add_sub_cancel_left]
              apply Finset.sum_pos
              · intro j hj
                exact hlam _
              · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
            have hRmin : ∀ u x, (∀ j, x ≤ u j) → R u x = 1 / Ltot lam := by
              intro u x hxmin
              dsimp [R]
              calc
                _ = ∫ t in Set.Iic 0, Real.exp (Ltot lam * t) := by
                  apply setIntegral_congr_fun measurableSet_Iic
                  intro t ht
                  have ht0 : t ≤ 0 := ht
                  rw [hKexp]
                  congr 1
                  have hh : ∀ j, max (u j - x - t) 0 - max (u j - x) 0 = -t := by
                    intro j
                    rw [max_eq_left (by linarith [hxmin j, ht0] : 0 ≤ u j - x - t),
                      max_eq_left (sub_nonneg.mpr (hxmin j))]
                    ring
                  simp_rw [hh, ← Finset.sum_mul]
                  dsimp [Ltot]
                  ring
                _ = 1 / Ltot lam := by
                  rw [integral_exp_mul_Iic (a := Ltot lam) htotal]
                  simp
            have htaumin : ∀ u i, (∀ j, u i ≤ u j) → tau u lam i = 1 / (Ltot lam - lam i) := by
              intro u i hmin
              rw [htau, hRmin u (u i) hmin]
              have hl : Ltot lam ≠ 0 := ne_of_gt htotal
              have hm : Ltot lam - lam i ≠ 0 := ne_of_gt (hLminus i)
              field_simp [hl, hm]
              <;> ring
            have hroot : ∀ (u : Fin (m + 1) → ℝ) i (a : ℝ),
                ∃! x : ℝ, a - x = tau (Function.update u i x) lam i := by
              intro u i a
              let lo : ℝ := min (a - 1 / (Ltot lam - lam i)) (⨅ j, u j)
              have hlo : lo ≤ a - 1 / (Ltot lam - lam i) := min_le_left _ _
              have hlou : ∀ j, lo ≤ u j := by
                intro j
                exact le_trans (min_le_right _ _) (ciInf_le (Set.finite_range u).bddBelow j)
              have hlomin : ∀ j, Function.update u i lo i ≤ Function.update u i lo j := by
                intro j
                by_cases hji : j = i
                · subst j
                  rfl
                · simpa only [Function.update_self, Function.update_of_ne hji] using hlou j
              have hlot : tau (Function.update u i lo) lam i = 1 / (Ltot lam - lam i) :=
                htaumin _ _ hlomin
              have hloa : lo ≤ a := le_trans hlo (sub_le_self _ (one_div_pos.mpr (hLminus i)).le)
              have hc : Continuous (fun x => a - x - tau (Function.update u i x) lam i) :=
                (continuous_const.sub continuous_id).sub (htauc u i)
              have hlof : 0 ≤ a - lo - tau (Function.update u i lo) lam i := by
                rw [hlot]
                linarith
              have hhif : a - a - tau (Function.update u i a) lam i ≤ 0 := by
                have hp := htaupos (Function.update u i a) i
                linarith
              obtain ⟨x, hxmem, hx⟩ := intermediate_value_Icc' hloa hc.continuousOn ⟨hhif, hlof⟩
              refine ⟨x, by linarith, ?_⟩
              intro y hy
              apply le_antisymm
              · by_contra h
                have hxy : x < y := lt_of_not_ge h
                have hh := htaumono u i hxy.le
                linarith
              · by_contra h
                have hyx : y < x := lt_of_not_ge h
                have hh := htaumono u i hyx.le
                linarith
            have hcondUpdate : ∀ (S : Finset (Fin (m + 1))) u i x,
                condVec α S u i x = Function.update
                  (fun j => if j ∈ S then u j else maxAlpha α) i x := by
              intro S u i x
              funext j
              by_cases hji : j = i
              · subst j
                simp [condVec]
              · simp [condVec, hji]
            have hcondRoot : ∀ (S : Finset (Fin (m + 1))) u i,
                ∃! x : ℝ, α i - x = tauCond α lam S u i x := by
              intro S u i
              simpa only [tauCond, hcondUpdate] using
                hroot (fun j => if j ∈ S then u j else maxAlpha α) i (α i)
            have hcondAgree : ∀ (S : Finset (Fin (m + 1))) u v,
                (∀ j ∈ S, u j = v j) → ∀ i x,
                tauCond α lam S u i x = tauCond α lam S v i x := by
              intro S u v he i x
              change tau (condVec α S u i x) lam i = tau (condVec α S v i x) lam i
              apply congrArg (fun w : Fin (m + 1) → ℝ => tau w lam i)
              funext j
              dsimp [condVec]
              by_cases hji : j = i
              · simp [hji]
              · by_cases hjS : j ∈ S
                · simp [hji, hjS, he j hjS]
                · simp [hji, hjS]
            have hsolved : ∀ (s : Fin (m + 1)) t,
                σ s ∈ solvedBefore σ t ↔ s.val < t := by
              intro s t
              simp [solvedBefore]
            have hexists : ∃ ustar : Fin (m + 1) → ℝ, IsOnePass α lam σ ustar := by
              have hpref : ∀ t : ℕ, t ≤ m + 1 → ∃ u : Fin (m + 1) → ℝ,
                  ∀ s : Fin (m + 1), s.val < t →
                    (s.val = 0 → u (σ s) = α (σ s) - 1 / (Ltot lam - lam (σ s))) ∧
                    (0 < s.val → α (σ s) - u (σ s) =
                      tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s))) := by
                intro t
                induction t with
                | zero =>
                  intro ht
                  exact ⟨fun _ => 0, fun s hs => by omega⟩
                | succ t ih =>
                  intro ht
                  obtain ⟨u, hu⟩ := ih (by omega)
                  let s : Fin (m + 1) := ⟨t, by omega⟩
                  obtain ⟨y, hy, hyuniq⟩ := hcondRoot (solvedBefore σ t) u (σ s)
                  let x : ℝ := if t = 0 then α (σ s) - 1 / (Ltot lam - lam (σ s)) else y
                  have hx0 : t = 0 → x = α (σ s) - 1 / (Ltot lam - lam (σ s)) := by
                    intro ht0
                    simp [x, ht0]
                  have hx1 : 0 < t → α (σ s) - x = tauCond α lam (solvedBefore σ t) u (σ s) x := by
                    intro ht0
                    simpa [x, Nat.ne_of_gt ht0] using hy
                  refine ⟨Function.update u (σ s) x, ?_⟩
                  intro r hr
                  by_cases hrs : r = s
                  · subst r
                    have hag : ∀ j ∈ solvedBefore σ s.val,
                        Function.update u (σ s) x j = u j := by
                      intro j hj
                      apply Function.update_of_ne
                      intro hji
                      subst j
                      exact (Nat.lt_irrefl s.val) ((hsolved s s.val).mp hj)
                    constructor
                    · intro hs0
                      simpa only [Function.update_self] using hx0 hs0
                    · intro hs0
                      rw [Function.update_self, hcondAgree _ _ u hag]
                      exact hx1 hs0
                  · have hrt : r.val < t := by
                      have hne : r.val ≠ t := by
                        intro he
                        apply hrs
                        apply Fin.ext
                        exact he
                      omega
                    have hsig : σ r ≠ σ s := fun he => hrs (σ.injective he)
                    have hag : ∀ j ∈ solvedBefore σ r.val,
                        Function.update u (σ s) x j = u j := by
                      intro j hj
                      apply Function.update_of_ne
                      intro hji
                      subst j
                      have hh := (hsolved s r.val).mp hj
                      change t < r.val at hh
                      omega
                    simpa only [Function.update_of_ne hsig, hcondAgree _ _ u hag] using hu r hrt
              obtain ⟨u, hu⟩ := hpref (m + 1) le_rfl
              exact ⟨u, fun s => hu s s.isLt⟩
            have htauhigh : ∀ u v i, u i = v i →
                (∀ j, u j = v j ∨ (u i ≤ u j ∧ v i ≤ v j)) → tau u lam i = tau v lam i := by
              intro u v i hown hh
              have hr : R u (u i) = R v (v i) := by
                apply setIntegral_congr_fun measurableSet_Iic
                intro t ht
                have ht0 : t ≤ 0 := ht
                rw [hKexp, hKexp]
                congr 2
                apply Finset.sum_congr rfl
                intro j hj
                congr 1
                rcases hh j with he | ⟨hu, hv⟩
                · rw [he, hown]
                · rw [max_eq_left (by linarith : 0 ≤ u j - u i - t),
                    max_eq_left (sub_nonneg.mpr hu),
                    max_eq_left (by linarith : 0 ≤ v j - v i - t),
                    max_eq_left (sub_nonneg.mpr hv)]
                  ring
              rw [htau, htau, hr]
            have hRpair : ∀ u i j, i ≠ j → u i = u j →
                R u (u i) ≤ 1 / (lam i + lam j) := by
              intro u i j hne hij
              have hsum : 0 < lam i + lam j := add_pos (hlam i) (hlam j)
              have hh : R u (u i) ≤ ∫ t in Set.Iic 0, Real.exp ((lam i + lam j) * t) := by
                apply integral_mono_ae (hKi _ _) (integrableOn_exp_mul_Iic hsum 0)
                apply (ae_restrict_iff' measurableSet_Iic).mpr
                apply Filter.Eventually.of_forall
                intro t ht
                have ht0 : t ≤ 0 := ht
                rw [hKexp]
                apply Real.exp_le_exp.mpr
                let d : Fin (m + 1) → ℝ := fun k => lam k *
                  (max (u k - u i - t) 0 - max (u k - u i) 0)
                have hd : ∀ k, 0 ≤ d k := by
                  intro k
                  apply mul_nonneg (hlam _).le
                  apply sub_nonneg.mpr
                  exact max_le_max_right 0 (by linarith [ht0])
                have hs : d i + d j ≤ ∑ k, d k := by
                  rw [← Finset.sum_pair hne]
                  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                    (fun k hk hnk => hd k)
                have hi : d i = -(lam i * t) := by
                  dsimp [d]
                  simp only [sub_self, zero_sub, max_eq_left (neg_nonneg.mpr ht0), max_self, sub_zero]
                  ring
                have hj : d j = -(lam j * t) := by
                  dsimp [d]
                  rw [← hij]
                  simp only [sub_self, zero_sub, max_eq_left (neg_nonneg.mpr ht0), max_self, sub_zero]
                  ring
                rw [hi, hj] at hs
                change -(∑ k, d k) ≤ _
                linarith
              rw [integral_exp_mul_Iic hsum] at hh
              simpa using hh
            have htauadd : ∀ u i, tau u lam i + 1 / lam i =
                1 / (lam i * (1 - lam i * R u (u i))) := by
              intro u i
              rw [htau]
              have hl : lam i ≠ 0 := ne_of_gt (hlam i)
              have hd : 1 - lam i * R u (u i) ≠ 0 := ne_of_gt (hden u i)
              have hd' : 1 - R u (u i) * lam i ≠ 0 := by simpa only [mul_comm] using hd
              field_simp [hl, hd, hd']
              <;> ring
            have htaucross : ∀ u i j, i ≠ j → u i = u j → lam i ≤ lam j →
                tau u lam j + 1 / lam j ≤ tau u lam i + 1 / lam i := by
              intro u i j hne hij hlamij
              rw [htauadd, htauadd]
              have hpair := (le_div_iff₀ (add_pos (hlam i) (hlam j))).mp (hRpair u i j hne hij)
              have hp := mul_nonneg (sub_nonneg.mpr hlamij) (show 0 ≤ 1 - (lam i + lam j) * R u (u i) by
                nlinarith only [hpair])
              have hd : lam i * (1 - lam i * R u (u i)) ≤ lam j * (1 - lam j * R u (u j)) := by
                rw [← hij]
                nlinarith only [hp]
              exact one_div_le_one_div_of_le (mul_pos (hlam i) (hden u i)) hd
            have hM : ∀ i, α i ≤ maxAlpha α := by
              intro i
              exact le_ciSup (Set.finite_range α).bddAbove i
            have hcondσ : ∀ t u (s r : Fin (m + 1)) x,
                condVec α (solvedBefore σ t) u (σ s) x (σ r) =
                  if r = s then x else if r.val < t then u (σ r) else maxAlpha α := by
              intro t u s r x
              simp only [condVec, σ.injective.eq_iff, hsolved]
            have hcondMono : ∀ S u i, Monotone (fun x => tauCond α lam S u i x) := by
              intro S u i
              simpa only [tauCond, hcondUpdate] using
                htaumono (fun j => if j ∈ S then u j else maxAlpha α) i
            have hrun : ∀ u : Fin (m + 1) → ℝ, IsOnePass α lam σ u →
                (∀ i, u i < α i) ∧ Monotone (fun s => u (σ s)) ∧
                  (∀ i, α i - u i = tau u lam i) := by
              intro u hu
              have hb : ∀ s, u (σ s) < α (σ s) := by
                intro s
                by_cases hs : s.val = 0
                · rw [(hu s).1 hs]
                  exact sub_lt_self _ (one_div_pos.mpr (hLminus _))
                · have hf := (hu s).2 (by omega)
                  have hp := htaupos (condVec α (solvedBefore σ s.val) u (σ s) (u (σ s))) (σ s)
                  change 0 < tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) at hp
                  linarith
              have hbM : ∀ s, u (σ s) ≤ maxAlpha α :=
                fun s => le_trans (hb s).le (hM _)
              have hfc : ∀ s, α (σ s) - u (σ s) =
                  tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) := by
                intro s
                by_cases hs : s.val = 0
                · have hempty : solvedBefore σ s.val = ∅ := by simp [solvedBefore, hs]
                  have hmin : ∀ j,
                      condVec α (solvedBefore σ s.val) u (σ s) (u (σ s)) (σ s) ≤
                      condVec α (solvedBefore σ s.val) u (σ s) (u (σ s)) j := by
                    intro j
                    by_cases hji : j = σ s
                    · subst j
                      rfl
                    · simp only [condVec, if_pos rfl, if_neg hji, hempty, Finset.notMem_empty, ite_false]
                      exact hbM s
                  have ht := htaumin _ (σ s) hmin
                  change tauCond α lam (solvedBefore σ s.val) u (σ s) (u (σ s)) = _ at ht
                  rw [ht, (hu s).1 hs]
                  ring
                · exact (hu s).2 (by omega)
              have hmon : Monotone (fun s => u (σ s)) := by
                apply Fin.monotone_iff_le_succ.mpr
                intro k
                let s : Fin (m + 1) := k.castSucc
                let t : Fin (m + 1) := k.succ
                have hst : s < t := Fin.castSucc_lt_succ
                have hnext : t.val = s.val + 1 := rfl
                have hne : s ≠ t := ne_of_lt hst
                let x := u (σ s)
                let v := condVec α (solvedBefore σ s.val) u (σ s) x
                let w := condVec α (solvedBefore σ t.val) u (σ t) x
                have hvs : v (σ s) = x := by simp [v, condVec]
                have hws : w (σ s) = x := by
                  simp only [w, hcondσ, if_neg hne, if_pos (show s.val < t.val from hst)]
                  rfl
                have hwt : w (σ t) = x := by simp [w, condVec]
                have heq : tau v lam (σ s) = tau w lam (σ s) := by
                  apply htauhigh v w (σ s) (hvs.trans hws.symm)
                  intro j
                  obtain ⟨r, rfl⟩ := σ.surjective j
                  by_cases hrs : r = s
                  · subst r
                    exact Or.inl (hvs.trans hws.symm)
                  · by_cases hrt : r = t
                    · subst r
                      right
                      rw [hvs, hws, hwt]
                      have htv : v (σ t) = maxAlpha α := by
                        simp only [v, hcondσ, if_neg hne.symm,
                          if_neg (show ¬t.val < s.val by omega)]
                      rw [htv]
                      exact ⟨hbM s, le_rfl⟩
                    · left
                      have hrval : r.val ≠ s.val := fun he => hrs (Fin.ext he)
                      have hiff : r.val < s.val ↔ r.val < t.val := by omega
                      simp only [v, w, hcondσ, if_neg hrs, if_neg hrt, hiff]
                have hcross := htaucross w (σ s) (σ t) (fun he => hne (σ.injective he))
                  (hws.trans hwt.symm) ((horder s t hst.le).2)
                have hscore := hσ hst.le
                have hfirst := hfc s
                change α (σ s) - x = tau v lam (σ s) at hfirst
                rw [heq] at hfirst
                have hres : tauCond α lam (solvedBefore σ t.val) u (σ t) x ≤ α (σ t) - x := by
                  change tau w lam (σ t) ≤ _
                  linarith only [hcross, hscore, hfirst]
                change x ≤ u (σ t)
                by_contra h
                have hlt : u (σ t) < x := lt_of_not_ge h
                have htm := hcondMono (solvedBefore σ t.val) u (σ t) hlt.le
                have hsecond := hfc t
                linarith only [hres, htm, hsecond, hlt]
              refine ⟨?_, hmon, ?_⟩
              · intro i
                obtain ⟨s, rfl⟩ := σ.surjective i
                exact hb s
              · intro i
                obtain ⟨s, rfl⟩ := σ.surjective i
                have heq : tau (condVec α (solvedBefore σ s.val) u (σ s) (u (σ s))) lam (σ s) =
                    tau u lam (σ s) := by
                  apply htauhigh _ u (σ s) (by simp [condVec])
                  intro j
                  obtain ⟨r, rfl⟩ := σ.surjective j
                  by_cases hrs : r = s
                  · subst r
                    left
                    simp [condVec]
                  · by_cases hlt : r.val < s.val
                    · left
                      simp only [hcondσ, if_neg hrs, if_pos hlt]
                    · right
                      have hsr : s ≤ r := by exact Fin.le_iff_val_le_val.mpr (by omega)
                      simp only [hcondσ, if_pos rfl, if_neg hrs, if_neg hlt]
                      exact ⟨hbM s, hmon hsr⟩
                have hh := hfc s
                exact hh.trans heq
            let D : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ → ℝ :=
              fun u i x => lam i * (C u i x - choiceProb (Function.update u i x) lam i)
            have hDpartial : ∀ u i x, D u i x =
                partialU (fun v => choiceProb v lam i) i (Function.update u i x) := by
              intro u i x
              rw [hpartial, ← hCuF, Function.update_self, hCupdate]
            have hDpos : ∀ u i x, 0 < D u i x := by
              intro u i x
              rw [hDpartial]
              exact hpartialpos _ _
            have hmaxFOC : ∀ u i z, α i - z = tau (Function.update u i z) lam i →
                ∀ x : ℝ, (α i - x) * choiceProb (Function.update u i x) lam i ≤
                  (α i - z) * choiceProb (Function.update u i z) lam i := by
              intro u i z hz
              let f : ℝ → ℝ := fun x => (α i - x) * choiceProb (Function.update u i x) lam i
              let df : ℝ → ℝ := fun x => -choiceProb (Function.update u i x) lam i + (α i - x) * D u i x
              have hfd : ∀ x, HasDerivAt f (df x) x := by
                intro x
                have hh := ((hasDerivAt_const x (α i)).sub (hasDerivAt_id x)).mul (hD u i x)
                convert hh using 1 <;> try rfl
                dsimp [df, D]
                ring
              have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hfd x).continuousAt)
              have hleft : ∀ x, x ≤ z → 0 ≤ df x := by
                intro x hx
                have ht := htaumono u i hx
                have hres : tau (Function.update u i x) lam i ≤ α i - x := by linarith only [ht, hz, hx]
                rw [htauu] at hres
                have hmul := (div_le_iff₀ (hDpos u i x)).mp hres
                dsimp [df]
                linarith only [hmul]
              have hright : ∀ x, z ≤ x → df x ≤ 0 := by
                intro x hx
                have ht := htaumono u i hx
                have hres : α i - x ≤ tau (Function.update u i x) lam i := by linarith only [ht, hz, hx]
                rw [htauu] at hres
                have hmul := (le_div_iff₀ (hDpos u i x)).mp hres
                dsimp [df]
                linarith only [hmul]
              have hinc : MonotoneOn f (Set.Iic z) := by
                apply monotoneOn_of_deriv_nonneg (convex_Iic z) hfc.continuousOn
                  (fun x hx => (hfd x).differentiableAt.differentiableWithinAt)
                intro x hx
                rw [(hfd x).deriv]
                exact hleft x (Set.mem_Iic.mp (interior_subset hx))
              have hdec : AntitoneOn f (Set.Ici z) := by
                apply antitoneOn_of_deriv_nonpos (convex_Ici z) hfc.continuousOn
                  (fun x hx => (hfd x).differentiableAt.differentiableWithinAt)
                intro x hx
                rw [(hfd x).deriv]
                exact hright x (Set.mem_Ici.mp (interior_subset hx))
              intro x
              by_cases hx : x ≤ z
              · exact hinc hx (by simp) hx
              · exact hdec (by simp) (le_of_not_ge hx) (le_of_not_ge hx)
            have hutilupdate : ∀ (p : Fin (m + 1) → ℝ) i q,
                util α β (Function.update p i q) = Function.update (util α β p) i (α i - β * q) := by
              intro p i q
              funext j
              by_cases hji : j = i
              · subst j
                simp [util]
              · simp [util, hji]
            have hPriceD : ∀ (p : Fin (m + 1) → ℝ) i q,
                HasDerivAt (fun r => firmRevenue α β lam (Function.update p i r) i)
                  (choiceProb (Function.update (util α β p) i (α i - β * q)) lam i -
                    β * q * D (util α β p) i (α i - β * q)) q := by
              intro p i q
              have hh := (hasDerivAt_id q).mul ((hD (util α β p) i (α i - β * q)).comp q
                (((hasDerivAt_id q).const_mul β).const_sub (α i)))
              have heq : (fun r => r * choiceProb (Function.update (util α β p) i (α i - β * r)) lam i) =
                  (fun r => firmRevenue α β lam (Function.update p i r) i) := by
                funext r
                simp only [firmRevenue, Function.update_self, hutilupdate]
              change HasDerivAt
                (fun r => r * choiceProb (Function.update (util α β p) i (α i - β * r)) lam i) _ q at hh
              rw [heq] at hh
              convert hh using 1 <;> try rfl
              dsimp [D]
              ring
            have hNEiff : ∀ p : Fin (m + 1) → ℝ, IsPriceNE α β lam p ↔
                ∀ i, α i - util α β p i = tau (util α β p) lam i := by
              intro p
              constructor
              · intro hp
                have hppos : ∀ i, 0 < p i := by
                  intro i
                  by_contra h
                  have heq : p i = 0 := le_antisymm (le_of_not_gt h) (hp.1 i)
                  have hh := hp.2 i 1 zero_le_one
                  have hq := hQpos (util α β (Function.update p i 1)) i
                  simp only [firmRevenue, Function.update_self, one_mul, heq, zero_mul] at hh
                  linarith only [hh, hq]
                intro i
                have hm : IsMaxOn (fun q => firmRevenue α β lam (Function.update p i q) i) (Set.Ici 0) (p i) := by
                  intro q hq
                  change firmRevenue α β lam (Function.update p i q) i ≤
                    firmRevenue α β lam (Function.update p i (p i)) i
                  simpa only [Function.update_eq_self] using hp.2 i q hq
                have hlocal := hm.isLocalMax (Ici_mem_nhds (hppos i))
                have heq := hlocal.hasDerivAt_eq_zero (hPriceD p i (p i))
                have hui : α i - β * p i = util α β p i := rfl
                rw [hui, Function.update_eq_self] at heq
                have hmul : α i - util α β p i = β * p i := by dsimp [util]; ring
                rw [hmul, ← Function.update_eq_self (f := util α β p) (a := i), htauu]
                apply (eq_div_iff (ne_of_gt (hDpos (util α β p) i (util α β p i)))).mpr
                simpa only [Function.update_eq_self, D] using (sub_eq_zero.mp heq).symm
              · intro hf
                have hppos : ∀ i, 0 < p i := by
                  intro i
                  have hh := htaupos (util α β p) i
                  rw [← hf i] at hh
                  dsimp [util] at hh
                  nlinarith only [hh, hβ]
                refine ⟨fun i => (hppos i).le, ?_⟩
                intro i q hq
                have hz : α i - util α β p i =
                    tau (Function.update (util α β p) i (util α β p i)) lam i := by
                  simpa only [Function.update_eq_self] using hf i
                have hh := hmaxFOC (util α β p) i (util α β p i) hz (α i - β * q)
                rw [Function.update_eq_self, ← hutilupdate] at hh
                have hx : α i - (α i - β * q) = β * q := by ring
                have hpv : α i - util α β p i = β * p i := by dsimp [util]; ring
                rw [hx, hpv] at hh
                apply (mul_le_mul_iff_right₀ hβ).mp
                simpa only [firmRevenue, Function.update_self, mul_assoc] using hh
            have hFOCunique : ∀ (u v : Fin (m + 1) → ℝ),
                (∀ i, α i - u i = tau u lam i) →
                (∀ i, α i - v i = tau v lam i) → u = v := by
              have hle : ∀ (u v : Fin (m + 1) → ℝ),
                  (∀ i, α i - u i = tau u lam i) →
                  (∀ i, α i - v i = tau v lam i) → ∀ j, u j ≤ v j := by
                intro u v hu hv j
                obtain ⟨i, hi, himax⟩ := Finset.exists_max_image Finset.univ (fun k => u k - v k) Finset.univ_nonempty
                have ht : tau v lam i ≤ tau u lam i := by
                  apply htaurelative
                  intro k
                  have hh := himax k (Finset.mem_univ _)
                  linarith only [hh]
                have hui := hu i
                have hvi := hv i
                have hh := himax j (Finset.mem_univ _)
                linarith only [ht, hui, hvi, hh]
              intro u v hu hv
              exact funext (fun j => le_antisymm (hle u v hu hv j) (hle v u hv hu j))
            have hUeq : ∀ u : Fin (m + 1) → ℝ, util α β (eqPrices α β u) = u := by
              intro u
              funext i
              dsimp [util, eqPrices]
              field_simp [ne_of_gt hβ]
              <;> ring
            refine ⟨hexists, ?_⟩
            intro u hu
            obtain ⟨hb, hmon, hfc⟩ := hrun u hu
            have hNE : IsPriceNE α β lam (eqPrices α β u) := by
              apply (hNEiff _).mpr
              simpa only [hUeq] using hfc
            have huniq : ∀ p, IsPriceNE α β lam p → p = eqPrices α β u := by
              intro p hp
              have hutilEq := hFOCunique (util α β p) u ((hNEiff p).mp hp) hfc
              funext i
              have hh := congrFun hutilEq i
              dsimp [eqPrices]
              apply (eq_div_iff (ne_of_gt hβ)).mpr
              dsimp [util] at hh
              linarith only [hh]
            have hprice : Monotone (fun s => eqPrices α β u (σ s)) := by
              intro s t hst
              have hlamij := (horder s t hst).2
              have hr := hRmono u (hmon hst)
              have hp := mul_nonneg (sub_nonneg.mpr hlamij)
                (mul_nonneg (hRpos u (u (σ s))).le (hRpos u (u (σ t))).le)
              have htauij : tau u lam (σ s) ≤ tau u lam (σ t) := by
                rw [htau, htau]
                apply (div_le_div_iff₀ (hden _ _) (hden _ _)).mpr
                nlinarith only [hr, hp]
              change (α (σ s) - u (σ s)) / β ≤ (α (σ t) - u (σ t)) / β
              rw [hfc, hfc]
              exact (div_le_div_iff_of_pos_right hβ).mpr htauij
            have hprobmono : Monotone (fun s => choiceProb (util α β (eqPrices α β u)) lam (σ s)) := by
              rw [hUeq]
              intro s t hst
              change choiceProb u lam (σ s) ≤ choiceProb u lam (σ t)
              rw [hQ, hQ]
              have hA : (∫ x in Set.Iic (u (σ s)), F u x) ≤ ∫ x in Set.Iic (u (σ t)), F u x := by
                apply setIntegral_mono_set (hFi _ _)
                  (Filter.Eventually.of_forall (fun x => (hFpos u x).le))
                exact Filter.Eventually.of_forall (fun x hx => le_trans hx (hmon hst))
              exact mul_le_mul ((horder s t hst).2) hA
                (integral_nonneg (fun x => (hFpos u x).le)) (hlam _).le
            refine ⟨fun s hs => hcondRoot _ _ _, hNE, huniq, hprice, hprobmono, ?_⟩
            intro s t hst
            exact mul_le_mul (hprice hst) (hprobmono hst)
              (hQpos _ _).le (hNE.1 _)
