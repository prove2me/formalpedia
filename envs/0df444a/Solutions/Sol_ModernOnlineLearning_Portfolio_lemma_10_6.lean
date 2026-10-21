-- Prove2me | solution 1 for ModernOnlineLearning.Portfolio.lemma_10_6
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:03:28.293355+00:00
-- url     : https://prove2.me/submissions/baf478b2-4362-456c-9eb6-adfd956e026c

import Definitions.Def_ModernOnlineLearning_Portfolio_Setting
import Theorems.Thm_ModernOnlineLearning_Portfolio_lemma_10_5
set_option autoImplicit false
open MeasureTheory ModernOnlineLearning.Portfolio

private lemma simplex_integrable {d : ℕ} (F : Measure (Fin d → ℝ)) [IsProbabilityMeasure F]
    (hF : F (stdSimplex ℝ (Fin d))ᶜ = 0) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f F := by
  have hae : ∀ᵐ p ∂F, p ∈ stdSimplex ℝ (Fin d) := by
    exact ae_iff.mpr hF
  have hi := hf.continuousOn.integrableOn_compact (μ := F) (isCompact_stdSimplex ℝ (Fin d))
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hi

private lemma before_eq {d : ℕ} (w : ℕ → Fin d → ℝ) (p : Fin d → ℝ) (n : ℕ) :
    wealthBefore w p (n + 1) = wealthCRP w p n := by
  simp only [wealthBefore, wealthCRP, Finset.Ico_add_one_right_eq_Icc]

private lemma wealth_integral {d T : ℕ} (F : Measure (Fin d → ℝ)) [IsProbabilityMeasure F]
    (hF : F (stdSimplex ℝ (Fin d))ᶜ = 0) (w : ℕ → Fin d → ℝ)
    (hden : ∀ t ∈ Finset.Icc 1 T, 0 < ∫ p, wealthBefore w p t ∂F) :
    portfolioWealth w (weightedPortfolio F w) T = ∫ p, wealthCRP w p T ∂F := by
  induction T with
  | zero => simp [portfolioWealth, wealthCRP]
  | succ n ih =>
    have hi : ∀ t ∈ Finset.Icc 1 n, 0 < ∫ p, wealthBefore w p t ∂F := by
      intro t ht; apply hden
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2.trans (Nat.le_succ n)⟩
    have hpos : 0 < ∫ p, wealthCRP w p n ∂F := by
      simpa only [before_eq] using hden (n + 1) (by simp)
    have hint (i : Fin d) : Integrable (fun p => w (n + 1) i * (p i * wealthCRP w p n)) F := by
      apply simplex_integrable F hF
      unfold wealthCRP
      fun_prop
    have hnum : (∫ p, wealthCRP w p (n + 1) ∂F) =
        ∑ i, w (n + 1) i * ∫ p, p i * wealthCRP w p n ∂F := by
      calc
        _ = ∫ p, ∑ i, w (n + 1) i * (p i * wealthCRP w p n) ∂F := by
          apply integral_congr_ae
          filter_upwards [] with p
          rw [wealthCRP, Finset.prod_Icc_succ_top (by omega)]
          change wealthCRP w p n * (∑ i, w (n + 1) i * p i) = _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ i, ∫ p, w (n + 1) i * (p i * wealthCRP w p n) ∂F :=
          integral_finsetSum _ (fun i _ => hint i)
        _ = _ := by simp only [integral_const_mul]
    change (∏ t ∈ Finset.Icc 1 (n + 1), ∑ i, w t i * weightedPortfolio F w t i) = _
    rw [Finset.prod_Icc_succ_top (by omega)]
    change portfolioWealth w (weightedPortfolio F w) n * _ = _
    rw [ih hi]
    simp only [weightedPortfolio, before_eq, ← mul_div_assoc, ← Finset.sum_div]
    rw [← hnum]
    field_simp

private lemma expand_wealth {d T : ℕ} (w : ℕ → Fin d → ℝ) (p : Fin d → ℝ) :
    wealthCRP w p T = ∑ j : Fin T → Fin d,
      (∏ t : Fin T, w (t.val + 1) (j t)) * sequenceMonomial j p := by
  classical
  have hind : (∏ t : Fin T, ∑ i, w (t.val + 1) i * p i) = wealthCRP w p T := by
    induction T with
    | zero => simp [wealthCRP]
    | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      simpa only [wealthCRP] using (Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1) (fun t => ∑ i, w t i * p i)).symm
  rw [← hind, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.prod_mul_distrib]
  rfl

private lemma finite_ratio {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ENNReal.ofReal (∑ i, a i) / ENNReal.ofReal (∑ i, b i) ≤
      ⨆ i, ENNReal.ofReal (a i) / ENNReal.ofReal (b i) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have h := ModernOnlineLearning.Portfolio.lemma_10_5
    (T := Fintype.card ι) (Fintype.card_pos_iff.mpr inferInstance)
    (fun i => a (e i)) (fun i => b (e i)) (fun i => ha _) (fun i => hb _)
  have he : (⨆ i : Fin (Fintype.card ι), ENNReal.ofReal (a (e i)) / ENNReal.ofReal (b (e i))) =
      ⨆ i : ι, ENNReal.ofReal (a i) / ENNReal.ofReal (b i) :=
    e.iSup_comp (g := fun i : ι => ENNReal.ofReal (a i) / ENNReal.ofReal (b i))
  rw [he] at h
  simpa only [Equiv.sum_comp] using h

theorem solution {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T)
    (F : MeasureTheory.Measure (Fin d → ℝ)) [MeasureTheory.IsProbabilityMeasure F]
    (hF : F (stdSimplex ℝ (Fin d))ᶜ = 0)
    (w : ℕ → Fin d → ℝ)
    (hw_nonneg : ∀ t ∈ Finset.Icc 1 T, ∀ i, 0 ≤ w t i)
    (hw_ne : ∀ t ∈ Finset.Icc 1 T, w t ≠ 0)
    (hden : ∀ t ∈ Finset.Icc 1 T, 0 < ∫ p, wealthBefore w p t ∂F)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    ENNReal.ofReal (wealthCRP w u T) /
        ENNReal.ofReal (portfolioWealth w (weightedPortfolio F w) T) ≤
      ⨆ j : Fin T → Fin d,
        ENNReal.ofReal (sequenceMonomial j u) /
          ENNReal.ofReal (∫ p, sequenceMonomial j p ∂F) := by
  classical
  letI : Nonempty (Fin T → Fin d) := ⟨fun _ => ⟨0, by omega⟩⟩
  let c : (Fin T → Fin d) → ℝ := fun j => ∏ t : Fin T, w (t.val + 1) (j t)
  have hc : ∀ j, 0 ≤ c j := by
    intro j
    apply Finset.prod_nonneg
    intro t ht
    exact hw_nonneg (t.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (j t)
  have hmono : ∀ j : Fin T → Fin d, ∀ p ∈ stdSimplex ℝ (Fin d), 0 ≤ sequenceMonomial j p := by
    intro j p hp
    exact Finset.prod_nonneg (fun t _ => hp.1 (j t))
  have hae : ∀ᵐ p ∂F, p ∈ stdSimplex ℝ (Fin d) := by
    exact ae_iff.mpr hF
  have hint : ∀ j : Fin T → Fin d, Integrable (fun p => sequenceMonomial j p) F := by
    intro j
    apply simplex_integrable F hF
    unfold sequenceMonomial
    fun_prop
  have hmoment : ∀ j : Fin T → Fin d, 0 ≤ ∫ p, sequenceMonomial j p ∂F := by
    intro j
    apply integral_nonneg_of_ae
    filter_upwards [hae] with p hp
    exact hmono j p hp
  have hden_expand : portfolioWealth w (weightedPortfolio F w) T =
      ∑ j : Fin T → Fin d, c j * ∫ p, sequenceMonomial j p ∂F := by
    rw [wealth_integral F hF w hden]
    calc
      _ = ∫ p, ∑ j : Fin T → Fin d, c j * sequenceMonomial j p ∂F := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun p => expand_wealth w p)
      _ = ∑ j : Fin T → Fin d, ∫ p, c j * sequenceMonomial j p ∂F :=
        integral_finsetSum _ (fun j _ => (hint j).const_mul (c j))
      _ = _ := by simp only [integral_const_mul]
  rw [hden_expand, expand_wealth]
  change ENNReal.ofReal (∑ j, c j * sequenceMonomial j u) /
    ENNReal.ofReal (∑ j, c j * ∫ p, sequenceMonomial j p ∂F) ≤ _
  refine (finite_ratio (fun j => c j * sequenceMonomial j u)
    (fun j => c j * ∫ p, sequenceMonomial j p ∂F)
    (fun j => mul_nonneg (hc j) (hmono j u hu))
    (fun j => mul_nonneg (hc j) (hmoment j))).trans ?_
  apply iSup_le
  intro j
  by_cases hz : c j = 0
  · simp only [hz, zero_mul, ENNReal.ofReal_zero, ENNReal.zero_div]
    exact zero_le
  · rw [ENNReal.ofReal_mul (hc j), ENNReal.ofReal_mul (hc j),
      ENNReal.mul_div_mul_left _ _ (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (hc j) (Ne.symm hz)))) ENNReal.ofReal_ne_top]
    exact le_iSup (fun j : Fin T → Fin d => ENNReal.ofReal (sequenceMonomial j u) /
      ENNReal.ofReal (∫ p, sequenceMonomial j p ∂F)) j


