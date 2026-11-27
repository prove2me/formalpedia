-- Prove2me | solution 1 for HetExponomial.ChoiceProb.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:41.481058+00:00
-- url     : https://prove2.me/submissions/8cb6ee78-e282-43e8-b026-512b1c0a46f9

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

open HetExponomial
open HetExponomial.ChoiceProb
open HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem solution {n : ℕ} (hn : 2 ≤ n) (u₀ : ℝ) (u lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hu₀ : ∀ i, u₀ < u i) :
    (∀ i, choiceProbOut u₀ u lam i =
        G u lam i - ∑ k ∈ strictlyWorse u i, lam i / Lplus u lam k * G u lam k -
          lam i / Ltot lam * G0 u₀ u lam) ∧
      outsideProb u₀ u lam = G0 u₀ u lam := by
        obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, H = fun t => Real.exp (-(∑ j, lam j * max (u j - t) 0)) :=
          ⟨_, rfl⟩
        obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ → ℝ, Lb = fun t => ∑ j, if t ≤ u j then lam j else 0 := ⟨_, rfl⟩
        obtain ⟨Lq, hLq⟩ : ∃ Lq : ℝ → ℝ, Lq = fun t => ∑ j, if t < u j then lam j else 0 := ⟨_, rfl⟩
        obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, c = fun k => lam k * H (u k) / (Lb (u k) * Lq (u k)) :=
          ⟨_, rfl⟩
        obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun t => H t / Lb t - ∑ k, if u k < t then c k else 0 :=
          ⟨_, rfl⟩
        have hHcont : Continuous H := by
          rw [hH]
          exact (continuous_finsetSum _ fun j _ => continuous_const.mul
            ((continuous_const.sub continuous_id).max continuous_const)).neg.rexp
        have piece : ∀ a b, a ≤ b → (∀ j, u j < b → u j ≤ a) → 0 < Lb b →
            ∫ t in a..b, H t = (H b - H a) / Lb b := by
          intro a b hab hgap hpos
          obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
              g = fun t => ∑ j, if b ≤ u j then lam j * (t - u j) else 0 := ⟨_, rfl⟩
          have hHg : ∀ t, a ≤ t → t ≤ b → H t = Real.exp (g t) := by
            intro t hat htb
            rw [hH, hg]
            simp only
            congr 1
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs with h
            · rw [max_eq_left (by linarith)]; ring
            · rw [max_eq_right (by linarith [hgap j (not_le.1 h)])]; simp
          have hg' : ∀ t, HasDerivAt g (Lb b) t := by
            intro t
            have := HasDerivAt.fun_sum (u := Finset.univ)
              (A := fun j t => if b ≤ u j then lam j * (t - u j) else 0)
              (A' := fun j => if b ≤ u j then lam j else 0) (x := t) (fun j _ => by
                by_cases h : b ≤ u j
                · simp only [if_pos h]
                  simpa using ((hasDerivAt_id t).sub_const (u j)).const_mul (lam j)
                · simp only [if_neg h]; exact hasDerivAt_const _ _)
            rw [hg, hLb]
            convert this using 1
          have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg' t).continuousAt
          have hd : ∀ t, HasDerivAt (fun t => Real.exp (g t) / Lb b) (Real.exp (g t)) t := by
            intro t
            have h2 := ((hg' t).exp).div_const (Lb b)
            rwa [mul_div_assoc, div_self hpos.ne', mul_one] at h2
          rw [intervalIntegral.integral_congr (g := fun t => Real.exp (g t)) (fun t ht => by
            rw [Set.uIcc_of_le hab] at ht; exact hHg t ht.1 ht.2)]
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
            ((Real.continuous_exp.comp hgc).intervalIntegrable _ _)]
          rw [hHg b hab le_rfl, hHg a le_rfl hab]; ring
        have hF0 : F u₀ = H u₀ / Lb u₀ := by
          rw [hF]; simp only
          rw [Finset.sum_eq_zero (fun k _ => if_neg (not_lt.2 (hu₀ k).le)), sub_zero]
        have key : ∀ N : ℕ, ∀ b, (Finset.univ.filter fun k => u k < b).card = N → u₀ ≤ b →
            0 < Lb b → ∫ t in u₀..b, H t = F b - F u₀ := by
          intro N
          induction N using Nat.strong_induction_on with
          | _ N ih =>
          intro b hN hb hpos
          by_cases hs : (Finset.univ.filter fun k => u k < b).Nonempty
          · obtain ⟨k₀, hk₀, hk₀max⟩ := Finset.exists_max_image _ u hs
            have hab : u k₀ < b := (Finset.mem_filter.1 hk₀).2
            have hgap : ∀ k, u k < b → u k ≤ u k₀ := fun k hk =>
              hk₀max k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)
            have hcard : (Finset.univ.filter fun k => u k < u k₀).card < N := by
              rw [← hN]
              apply Finset.card_lt_card
              rw [Finset.ssubset_iff_of_subset]
              · exact ⟨k₀, hk₀, by simp⟩
              · intro k hk
                simp only [Finset.mem_filter] at hk ⊢
                exact ⟨hk.1, by linarith [hk.2]⟩
            obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j, if u j = u k₀ then lam j else 0 := ⟨_, rfl⟩
            have hM0 : 0 ≤ M := by
              rw [hM]
              exact Finset.sum_nonneg fun j _ => by
                split_ifs
                · exact (hlam j).le
                · exact le_rfl
            have hLqa : Lq (u k₀) = Lb b := by
              rw [hLq, hLb]
              refine Finset.sum_congr rfl fun j _ => ?_
              by_cases h1 : b ≤ u j
              · rw [if_pos h1, if_pos (by linarith)]
              · rw [if_neg h1, if_neg]
                intro h2
                linarith [hgap j (not_le.1 h1)]
            have hLba : Lb (u k₀) = Lq (u k₀) + M := by
              rw [hLb, hLq, hM]
              simp only
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun j _ => ?_
              by_cases h1 : u k₀ < u j
              · rw [if_pos h1.le, if_pos h1, if_neg h1.ne']; ring
              · by_cases h2 : u j = u k₀
                · rw [if_pos h2.ge, if_neg h1, if_pos h2]; ring
                · rw [if_neg (show ¬ u k₀ ≤ u j from fun h3 => h2 (le_antisymm (not_lt.1 h1) h3)),
                    if_neg h1, if_neg h2]
                  ring
            have hposa : 0 < Lb (u k₀) := by rw [hLba, hLqa]; linarith
            have hIH := ih _ hcard (u k₀) rfl (hu₀ k₀).le hposa
            have hpc := piece (u k₀) b hab.le hgap hpos
            have hsum : (∑ k, if u k < b then c k else 0) = (∑ k, if u k < u k₀ then c k else 0) +
                H (u k₀) / (Lb (u k₀) * Lq (u k₀)) * M := by
              rw [hM, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun k _ => ?_
              by_cases h1 : u k < u k₀
              · rw [if_pos (h1.trans hab), if_pos h1, if_neg h1.ne]; ring
              · by_cases h2 : u k = u k₀
                · rw [if_pos (h2 ▸ hab), if_neg h1, if_pos h2, hc]
                  simp only
                  rw [h2]; ring
                · rw [if_neg (show ¬ u k < b from fun h3 => h2 (le_antisymm (hgap k h3) (not_lt.1 h1))),
                    if_neg h1, if_neg h2]
                  ring
            rw [← intervalIntegral.integral_add_adjacent_intervals (b := u k₀)
              (hHcont.intervalIntegrable _ _) (hHcont.intervalIntegrable _ _), hIH, hpc]
            have eFb : F b = H b / Lb b - ∑ k, if u k < b then c k else 0 := by rw [hF]
            have eFa : F (u k₀) = H (u k₀) / Lb (u k₀) - ∑ k, if u k < u k₀ then c k else 0 := by
              rw [hF]
            rw [eFb, eFa, hsum, hLqa, hLba, hLqa]
            have hp2 : 0 < Lb b + M := by linarith
            field_simp
            ring
          · have hall : ∀ k, b ≤ u k := fun k => by
              by_contra h
              exact hs ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, not_le.1 h⟩⟩
            have hpc := piece u₀ b hb (fun j hj => absurd hj (not_lt.2 (hall j))) hpos
            have hL0 : Lb u₀ = Lb b := by
              rw [hLb]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [if_pos (hu₀ j).le, if_pos (hall j)]
            have eFb : F b = H b / Lb b := by
              rw [hF]; simp only
              rw [Finset.sum_eq_zero (fun k _ => if_neg (not_lt.2 (hall k))), sub_zero]
            rw [hpc, eFb, hF0, hL0]; ring
        have hLbpos : ∀ i, 0 < Lb (u i) := by
          intro i
          rw [hLb]
          have := Finset.single_le_sum (f := fun j => if u i ≤ u j then lam j else 0)
            (fun j _ => by
              split_ifs
              · exact (hlam j).le
              · exact le_rfl) (Finset.mem_univ i)
          simp only [le_refl, if_true] at this
          exact lt_of_lt_of_le (hlam i) this
        have hint : ∀ i, ∫ t in u₀..u i, H t = F (u i) - F u₀ := fun i =>
          key _ (u i) rfl (hu₀ i).le (hLbpos i)
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        haveI hprob : ∀ j, IsProbabilityMeasure (expMeasure (lam j)) := fun j =>
          isProbabilityMeasure_expMeasure (hlam j)
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
        have hIci : ∀ r : ℝ, 0 < r → ∀ c : ℝ,
            expMeasure r (Set.Ici c) = ENNReal.ofReal (Real.exp (-(r * max c 0))) := by
          intro r hr c
          haveI := isProbabilityMeasure_expMeasure hr
          have h1 : expMeasure r (Set.Ici c) = 1 - expMeasure r (Set.Iic c) := by
            rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio,
              measure_congr (Iio_ae_eq_Iic' (hnoatom r c))]
          rw [h1, ← ofReal_cdf, cdf_expMeasure_eq hr]
          split_ifs with h
          · rw [max_eq_left h, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
            · congr 1; ring
            · rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
          · rw [max_eq_right (not_le.1 h).le]; simp
        have hB : outsideProb u₀ u lam = H u₀ := by
          have : {z : Fin (m+1) → ℝ | ∀ j, u j - z j ≤ u₀} =
              Set.univ.pi (fun j => Set.Ici (u j - u₀)) := by
            ext z
            simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ici, true_implies]
            exact forall_congr' fun j => by constructor <;> intro h <;> linarith
          rw [outsideProb, errorLaw, this, Measure.pi_pi,
            Finset.prod_congr rfl (fun j _ => hIci _ (hlam j) _),
            ← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
            ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le),
            ← Real.exp_sum, hH]
          simp only
          rw [← Finset.sum_neg_distrib]
        have hA : ∀ i, choiceProbOut u₀ u lam i = lam i * ∫ t in u₀..u i, H t := by
          intro i
          set S := {z : Fin (m+1) → ℝ | u₀ ≤ u i - z i ∧ ∀ j, j ≠ i → u j - z j ≤ u i - z i} with hS
          have hSm : MeasurableSet S := by
            simp only [hS, Set.setOf_and, Set.setOf_forall]
            exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
              (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
                measurableSet_le (by fun_prop) (by fun_prop))
          set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) i with he
          set ν := Measure.pi fun j : Fin m => expMeasure (lam (i.succAbove j)) with hν
          haveI : SFinite ν := by rw [hν]; infer_instance
          have hmp := measurePreserving_piFinSuccAbove (fun j => expMeasure (lam j)) i
          have h1 : errorLaw lam S = ((expMeasure (lam i)).prod ν) (e.symm ⁻¹' S) :=
            (hmp.symm.measure_preimage hSm.nullMeasurableSet).symm
          obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = Set.indicator (Set.Iic (u i - u₀)) (fun x =>
              Real.exp (-(∑ j, lam (i.succAbove j) * max (u (i.succAbove j) - u i + x) 0))) :=
            ⟨_, rfl⟩
          have hsec : ∀ x, ν (Prod.mk x ⁻¹' (e.symm ⁻¹' S)) = ENNReal.ofReal (g x) := by
            intro x
            have hsy : ∀ y, e.symm (x, y) = (i.insertNth x y : Fin (m+1) → ℝ) := fun y => rfl
            by_cases hx : x ≤ u i - u₀
            · have hset : Prod.mk x ⁻¹' (e.symm ⁻¹' S) =
                  Set.univ.pi (fun j => Set.Ici (u (i.succAbove j) - u i + x)) := by
                ext y
                simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Ici, true_implies,
                  hS, Set.mem_setOf_eq, hsy, Fin.insertNth_apply_same]
                constructor
                · rintro ⟨_, h⟩ j
                  have := h (i.succAbove j) (Fin.succAbove_ne i j)
                  rw [Fin.insertNth_apply_succAbove] at this
                  linarith
                · intro h
                  refine ⟨by linarith, fun j hj => ?_⟩
                  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
                  rw [Fin.insertNth_apply_succAbove]
                  linarith [h j']
              rw [hset, hν, Measure.pi_pi,
                Finset.prod_congr rfl (fun j _ => hIci _ (hlam (i.succAbove j)) _),
                ← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le), ← Real.exp_sum, hg,
                Set.indicator_of_mem (Set.mem_Iic.2 hx), ← Finset.sum_neg_distrib]
            · have hset : Prod.mk x ⁻¹' (e.symm ⁻¹' S) = ∅ := by
                ext y
                simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, hsy, Fin.insertNth_apply_same,
                  Set.mem_empty_iff_false, iff_false, not_and]
                intro h
                exact absurd (by linarith) hx
              rw [hset, measure_empty, hg, Set.indicator_of_notMem (by simpa using hx),
                ENNReal.ofReal_zero]
          have hgm : Measurable g := by
            rw [hg]
            exact (Continuous.measurable (by
              exact (continuous_finsetSum _ fun j _ => continuous_const.mul
                ((continuous_const.add continuous_id).max continuous_const)).neg.rexp)).indicator
              measurableSet_Iic
          have hgnn : ∀ x, 0 ≤ g x := fun x => by
            rw [hg]; exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
          have h2 : ((expMeasure (lam i)).prod ν) (e.symm ⁻¹' S) =
              ∫⁻ x, ENNReal.ofReal (g x) ∂(expMeasure (lam i)) := by
            rw [Measure.prod_apply (hSm.preimage e.symm.measurable)]
            exact lintegral_congr fun x => hsec x
          have h3 : choiceProbOut u₀ u lam i = ∫ x, g x ∂(expMeasure (lam i)) := by
            rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgnn)
              hgm.aestronglyMeasurable, ← h2, ← h1]
            rfl
          rw [h3, hexp, integral_withDensity_eq_integral_toReal_smul (hpdfm _) (hpdft _)]
          have h4 : (fun x => (exponentialPDF (lam i) x).toReal • g x) =
              Set.indicator (Set.Icc 0 (u i - u₀)) (fun x => lam i * H (u i - x)) := by
            funext x
            rw [hpdfr _ (hlam i), hg, smul_eq_mul]
            by_cases hx0 : 0 ≤ x
            · by_cases hx1 : x ≤ u i - u₀
              · rw [if_pos hx0, Set.indicator_of_mem (Set.mem_Iic.2 hx1),
                  Set.indicator_of_mem (Set.mem_Icc.2 ⟨hx0, hx1⟩), hH]
                simp only
                rw [Fin.sum_univ_succAbove _ i, show u i - (u i - x) = x by ring,
                  max_eq_left hx0, neg_add, Real.exp_add]
                have : ∀ j, u (i.succAbove j) - u i + x = u (i.succAbove j) - (u i - x) :=
                  fun j => by ring
                simp only [this]
                ring
              · rw [Set.indicator_of_notMem (by simpa using hx1),
                  Set.indicator_of_notMem (by simp only [Set.mem_Icc, not_and, not_le]; intro; linarith)]
                simp
            · rw [if_neg hx0, zero_mul, Set.indicator_of_notMem]
              simp only [Set.mem_Icc, not_and]
              intro h; exact absurd h hx0
          rw [h4, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by linarith [hu₀ i]),
            intervalIntegral.integral_comp_sub_left (fun t => lam i * H t) (u i),
            intervalIntegral.integral_const_mul]
          simp
        have hG : ∀ k, G u lam k = lam k / Lb (u k) * H (u k) := by
          intro k
          simp only [G, Lsum, better, betterThan, Finset.sum_filter, hLb, hH]
          rw [show (∑ j, if u k ≤ u j then lam j * (u j - u k) else 0) =
              ∑ j, lam j * max (u j - u k) 0 from Finset.sum_congr rfl fun j _ => by
            split_ifs with h
            · rw [max_eq_left (by linarith)]
            · rw [max_eq_right (by linarith), mul_zero]]
        have hLp : ∀ k, Lplus u lam k = Lq (u k) := by
          intro k
          simp only [Lplus, strictlyBetter, Finset.sum_filter, hLq]
        have hLt : Ltot lam = Lb u₀ := by
          rw [hLb, Ltot]
          exact Finset.sum_congr rfl fun j _ => (if_pos (hu₀ j).le).symm
        have hG0 : G0 u₀ u lam = H u₀ := by
          rw [G0, hH]
          simp only
          rw [show (∑ j, lam j * (u j - u₀)) = ∑ j, lam j * max (u j - u₀) 0 from
            Finset.sum_congr rfl fun j _ => by rw [max_eq_left (by linarith [hu₀ j])]]
        refine ⟨fun i => ?_, by rw [hB, hG0]⟩
        rw [hA i, hint i, hG, hLt, hG0, hF0, strictlyWorse, Finset.sum_filter]
        simp only [hG, hLp]
        have eS : (∑ k, if u k < u i then lam i / Lq (u k) * (lam k / Lb (u k) * H (u k)) else 0) =
            lam i * ∑ k, if u k < u i then c k else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs
          · simp only [hc]; ring
          · ring
        have eFi : F (u i) = H (u i) / Lb (u i) - ∑ k, if u k < u i then c k else 0 := by rw [hF]
        rw [eS, eFi]
        ring
