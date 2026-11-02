-- Prove2me | solution 1 for LeviSampling.BaseStock.sampled_policy_near_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T14:16:15.926849+00:00
-- url     : https://prove2.me/submissions/38c14987-b8d5-47c8-9667-bf5bfc02b81f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow
import Definitions.Def_LeviSampling_BaseStock_Algorithm
import Definitions.Def_LeviSampling_BaseStock_AlphaPoint
import Definitions.Def_LeviSampling_BaseStock_Estimator
import Theorems.Thm_LeviSampling_BaseStock_upper_base_stock_convex
import Theorems.Thm_LeviSampling_BaseStock_upper_policy_product_bound
import Theorems.Thm_LeviSampling_BaseStock_alpha_point_relative_error
import Theorems.Thm_LeviSampling_BaseStock_stage_alpha_point


open MeasureTheory

namespace LeviSamplingAux

open LeviSampling.BaseStock

lemma nvCost_nonneg (μ : Measure ℝ) (h b y : ℝ) (hh : 0 < h) (hb : 0 < b) :
    0 ≤ nvCost μ h b y := by
  unfold nvCost
  apply integral_nonneg
  intro d
  have h1 : 0 ≤ max (y - d) 0 := le_max_right _ _
  have h2 : 0 ≤ max (d - y) 0 := le_max_right _ _
  positivity

lemma bsCost_nonneg (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i)
    (hb : ∀ i, 0 < b i) (L : ℕ → ℝ) :
    ∀ n k, T - k = n → ∀ x, 0 ≤ bsCost T μ h b L k x := by
  intro n
  induction n with
  | zero =>
    intro k hk x
    rw [bsCost]
    rw [dif_neg (by omega)]
  | succ n ih =>
    intro k hk x
    rw [bsCost]
    rw [dif_pos (by omega)]
    apply add_nonneg (nvCost_nonneg _ _ _ _ (hh k) (hb k))
    apply integral_nonneg
    intro d
    exact ih (k + 1) (by omega) _

lemma bsCost_congr (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (L L' : ℕ → ℝ) (s : ℕ)
    (hLL : ∀ m, s ≤ m → L m = L' m) :
    ∀ n k, T - k = n → s ≤ k → ∀ x, bsCost T μ h b L k x = bsCost T μ h b L' k x := by
  intro n
  induction n with
  | zero =>
    intro k hk hs x
    rw [bsCost, bsCost]
    rw [dif_neg (by omega), dif_neg (by omega)]
  | succ n ih =>
    intro k hk hs x
    rw [bsCost, bsCost]
    rw [dif_pos (by omega), dif_pos (by omega)]
    rw [hLL k hs]
    congr 1
    apply integral_congr_ae
    filter_upwards with d
    exact ih (k + 1) (by omega) (by omega) _

lemma shadowU_congr (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (L L' : ℕ → ℝ) (t : ℕ)
    (hLL : ∀ m, t < m → L m = L' m) :
    shadowU T μ h b L t = shadowU T μ h b L' t := by
  funext y
  unfold shadowU
  congr 1
  apply integral_congr_ae
  filter_upwards with d
  exact bsCost_congr T μ h b L L' (t + 1) (fun m hm => hLL m (by omega)) _ (t + 1) rfl le_rfl _

lemma optV_nonneg (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i)
    (hb : ∀ i, 0 < b i) :
    ∀ n i, T - i = n → ∀ x, 0 ≤ optV T μ h b i x := by
  intro n
  induction n with
  | zero =>
    intro i hi x
    rw [optV, dif_neg (by omega)]
  | succ n ih =>
    intro i hi x
    rw [optV, dif_pos (by omega)]
    unfold minAbove
    apply Real.iInf_nonneg
    intro y
    apply add_nonneg (nvCost_nonneg _ _ _ _ (hh i) (hb i))
    apply integral_nonneg
    intro d
    exact ih (i + 1) (by omega) _

lemma optCost_nonneg (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i)
    (hb : ∀ i, 0 < b i) : 0 ≤ optCost T μ h b := by
  unfold optCost
  apply Real.iInf_nonneg
  intro y
  unfold optU
  apply add_nonneg (nvCost_nonneg _ _ _ _ (hh 0) (hb 0))
  apply integral_nonneg
  intro d
  exact optV_nonneg T μ h b hh hb _ 1 rfl _

lemma nvCost_ge (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) (h b y : ℝ)
    (hh : 0 < h) (hb : 0 < b) :
    h * max (y - ∫ d, d ∂μ) 0 + b * max ((∫ d, d ∂μ) - y) 0 ≤ nvCost μ h b y := by
  unfold nvCost
  have hμ' : Integrable (fun d : ℝ => d) μ := hμ
  have i1 : Integrable (fun d : ℝ => y - d) μ := (integrable_const y).sub hμ
  have i2 : Integrable (fun d : ℝ => d - y) μ := hμ.sub (integrable_const y)
  have j1 : Integrable (fun d : ℝ => max (y - d) 0) μ := i1.pos_part
  have j2 : Integrable (fun d : ℝ => max (d - y) 0) μ := i2.pos_part
  rw [integral_add (j1.const_mul h) (j2.const_mul b), integral_const_mul, integral_const_mul]
  have e1 : ∫ d, (y - d) ∂μ = y - ∫ d, d ∂μ := by
    rw [integral_sub (integrable_const y) hμ']; simp
  have e2 : ∫ d, (d - y) ∂μ = (∫ d, d ∂μ) - y := by
    rw [integral_sub hμ' (integrable_const y)]; simp
  have k1 : max (y - ∫ d, d ∂μ) 0 ≤ ∫ d, max (y - d) 0 ∂μ := by
    apply max_le
    · rw [← e1]; exact integral_mono i1 j1 (fun d => le_max_left _ _)
    · exact integral_nonneg (fun d => le_max_right _ _)
  have k2 : max ((∫ d, d ∂μ) - y) 0 ≤ ∫ d, max (d - y) 0 ∂μ := by
    apply max_le
    · rw [← e2]; exact integral_mono i2 j2 (fun d => le_max_left _ _)
    · exact integral_nonneg (fun d => le_max_right _ _)
  have := mul_le_mul_of_nonneg_left k1 hh.le
  have := mul_le_mul_of_nonneg_left k2 hb.le
  linarith

lemma prod_le (T : ℕ) (hT : 1 ≤ T) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∏ _j ∈ Finset.Ico 0 T, (1 + ε / (2 * T))) ≤ 1 + ε := by
  rw [Finset.prod_const, Nat.card_Ico, Nat.sub_zero]
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 : (1 + ε / (2 * T)) ^ T ≤ (Real.exp (ε / (2 * T))) ^ T := by
    apply pow_le_pow_left₀ (by positivity)
    have := Real.add_one_le_exp (ε / (2 * T)); linarith
  have h2 : (Real.exp (ε / (2 * T))) ^ T = Real.exp (ε / 2) := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h3 : Real.exp (ε / 2) < 1 / (1 - ε / 2) :=
    Real.exp_bound_div_one_sub_of_interval' (by positivity) (by linarith)
  have h4 : 1 / (1 - ε / 2) ≤ 1 + ε := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

end LeviSamplingAux


open MeasureTheory

namespace LeviSamplingAux

open LeviSampling.BaseStock

def Good (T : ℕ) (μ : ℕ → Measure ℝ) (h b α : ℝ) (L : ℕ → ℝ) (s : ℕ) : Prop :=
  ∀ j, s ≤ j → j < T →
    (∃ r, IsShadowLevel T μ (fun _ => h) (fun _ => b) L j r ∧ r ≤ L j) ∧
      IsAlphaPoint (shadowU T μ (fun _ => h) (fun _ => b) L j) α (L j)

lemma good_congr (T : ℕ) (μ : ℕ → Measure ℝ) (h b α : ℝ) (L L' : ℕ → ℝ) (s : ℕ)
    (hLL : ∀ m, s ≤ m → L m = L' m) (hG : Good T μ h b α L s) : Good T μ h b α L' s := by
  intro j hj hjT
  have e : shadowU T μ (fun _ => h) (fun _ => b) L j = shadowU T μ (fun _ => h) (fun _ => b) L' j :=
    shadowU_congr T μ _ _ L L' j (fun m hm => hLL m (by omega))
  obtain ⟨⟨r, hr1, hr2⟩, hα⟩ := hG j hj hjT
  refine ⟨⟨r, ?_, ?_⟩, ?_⟩
  · unfold IsShadowLevel at hr1 ⊢; rw [← e]; exact hr1
  · rw [← hLL j hj]; exact hr2
  · rw [← e, ← hLL j hj]; exact hα

lemma good_cost (T : ℕ) (hT : 1 ≤ T) (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, Integrable id (μ i))
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (L : ℕ → ℝ)
    (hG : Good T μ h b (alphaStage T h b ε) L 0) :
    shadowU T μ (fun _ => h) (fun _ => b) L 0 (L 0) ≤
      (1 + ε) * optCost T μ (fun _ => h) (fun _ => b) := by
  have hL : IsUpperBaseStock T μ (fun _ => h) (fun _ => b) L 0 :=
    fun j hj hjT => (hG j hj hjT).1
  have hex : ∀ t, ∃ r, t < T → IsShadowLevel T μ (fun _ => h) (fun _ => b) L t r := by
    intro t
    by_cases ht : t < T
    · obtain ⟨r, hr, _⟩ := (hG t (Nat.zero_le _) ht).1
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h' => absurd h' ht⟩
  choose Rbar hRbar using hex
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hεt : 0 < ε / (2 * T) := by positivity
  have hεt1 : ε / (2 * T) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have key := upper_policy_product_bound T μ hμ (fun _ => h) (fun _ => b) (fun _ => hh)
    (fun _ => hb) L hL (fun _ => ε / (2 * T)) (fun _ _ => hεt.le) Rbar
    (fun t ht => (hRbar t ht).2) ?_ 0 (by omega)
  · have hopt := optCost_nonneg T μ (fun _ => h) (fun _ => b) (fun _ => hh) (fun _ => hb)
    have hp := prod_le T hT ε hε hε1
    calc shadowU T μ (fun _ => h) (fun _ => b) L 0 (L 0)
        ≤ (∏ j ∈ Finset.Ico 0 T, (1 + ε / (2 * T))) * optCost T μ (fun _ => h) (fun _ => b) :=
          key
      _ ≤ (1 + ε) * optCost T μ (fun _ => h) (fun _ => b) :=
          mul_le_mul_of_nonneg_right hp hopt
  · intro t ht
    have hcv := (hRbar t ht).1
    have hmin := (hRbar t ht).2.1
    apply alpha_point_relative_error (shadowU T μ (fun _ => h) (fun _ => b) L t) hcv (Rbar t)
      hmin h b (∫ x, x ∂(μ t)) hh hb _ (ε / (2 * T)) hεt hεt1 (L t)
    · exact (hG t (Nat.zero_le _) ht).2
    · intro y
      have h1 := nvCost_ge (μ t) (hμ t) h b y hh hb
      have h2 : nvCost (μ t) h b y ≤ shadowU T μ (fun _ => h) (fun _ => b) L t y := by
        unfold shadowU
        have : 0 ≤ ∫ d, bsCost T μ (fun _ => h) (fun _ => b) L (t + 1) (y - d) ∂(μ t) :=
          integral_nonneg (fun d => bsCost_nonneg T μ _ _ (fun _ => hh) (fun _ => hb) L _
            (t + 1) rfl _)
        linarith
      linarith

end LeviSamplingAux


open MeasureTheory

namespace LeviSamplingAux

open LeviSampling.BaseStock

lemma pi_lower {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (i : ι) (S Y : Set (∀ i, X i)) (c : ENNReal)
    (hsec : ∀ ω ∈ Y, c ≤ ν i {x | Function.update ω i x ∈ S}) :
    c * Measure.pi ν Y ≤ Measure.pi ν S := by
  set P := Measure.pi ν
  set M := toMeasurable P S with hMdef
  have hM : MeasurableSet M := measurableSet_toMeasurable P S
  have hSM : S ⊆ M := subset_toMeasurable P S
  set f : (∀ i, X i) → ENNReal := M.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hM
  set g := lmarginal ν {i} f with hg
  have hgm : Measurable g := hfm.lmarginal ν
  have hgval : ∀ ω, g ω = ν i {x | Function.update ω i x ∈ M} := by
    intro ω
    rw [hg, lmarginal_singleton]
    simp only
    have : (fun x => f (Function.update ω i x)) =
        {x | Function.update ω i x ∈ M}.indicator 1 := by
      funext x
      by_cases hx : Function.update ω i x ∈ M <;> simp [hf, hx]
    rw [this, lintegral_indicator_one]
    exact hM.preimage (measurable_update ω)
  have hPM : P M = ∫⁻ ω, g ω ∂P := by
    rw [← lintegral_indicator_one hM]
    apply lintegral_eq_of_lmarginal_eq {i} hfm hgm
    funext ω
    rw [lmarginal_singleton (f := g)]
    simp only
    have : ∀ x, g (Function.update ω i x) = g ω := fun x =>
      lmarginal_update_of_mem ν (Finset.mem_singleton_self i) f ω x
    simp_rw [this, lintegral_const, measure_univ, mul_one]
    rfl
  have hY : Y ⊆ {ω | c ≤ g ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq]
    rw [hgval]
    exact (hsec ω hω).trans (measure_mono (fun x hx => hSM hx))
  calc c * P Y ≤ c * P {ω | c ≤ g ω} := by gcongr
    _ ≤ ∫⁻ ω, g ω ∂P := mul_meas_ge_le_lintegral hgm c
    _ = P M := hPM.symm
    _ = P S := measure_toMeasurable S

lemma algLevel_update (T : ℕ) (h b ε δ : ℝ) (ω : SampleSpace T h b ε δ) (i : Fin T)
    (x : Fin (sampleSize T h b ε δ i) → Fin T → ℝ) :
    ∀ n k, T - k ≤ n → i.val < k →
      algLevel T h b ε δ (Function.update ω i x) k = algLevel T h b ε δ ω k := by
  intro n
  induction n with
  | zero =>
    intro k hk hik
    rw [algLevel, algLevel, dif_neg (by omega), dif_neg (by omega)]
  | succ n ih =>
    intro k hk hik
    by_cases hkT : k < T
    swap
    · rw [algLevel, algLevel, dif_neg hkT, dif_neg hkT]
    rw [algLevel, algLevel, dif_pos hkT, dif_pos hkT]
    have hne : (⟨k, by omega⟩ : Fin T) ≠ i := by
      intro he; rw [← he] at hik; simp at hik
    rw [Function.update_of_ne hne]
    have hL : (fun m => if _hk : k < m then algLevel T h b ε δ (Function.update ω i x) m else 0)
        = (fun m => if _hk : k < m then algLevel T h b ε δ ω m else 0) := by
      funext m
      by_cases hm : k < m
      · have hm' : k < m := hm
        rw [dif_pos hm, dif_pos hm]
        by_cases hmT : m < T
        · exact ih m (by omega) (by omega)
        · rw [algLevel, algLevel, dif_neg hmT, dif_neg hmT]
      · rw [dif_neg hm, dif_neg hm]
    rw [hL]

lemma algLevel_at (T : ℕ) (h b ε δ : ℝ) (ω : SampleSpace T h b ε δ) (i : Fin T) :
    algLevel T h b ε δ ω i = sInf {y : ℝ | alphaStage T h b ε / 2 ≤
      sampleRightDeriv T (fun _ => h) (fun _ => b)
        (fun k => if _hk : (i : ℕ) < k then algLevel T h b ε δ ω k else 0) i (ω i) y} := by
  rw [algLevel, dif_pos i.isLt]

lemma good_step (T : ℕ) (μ : ℕ → Measure ℝ) (h b α : ℝ) (L : ℕ → ℝ) (t : ℕ)
    (hG : Good T μ h b α L (t + 1))
    (hr : ∃ r, IsShadowLevel T μ (fun _ => h) (fun _ => b) L t r ∧ r ≤ L t)
    (hα : IsAlphaPoint (shadowU T μ (fun _ => h) (fun _ => b) L t) α (L t)) :
    Good T μ h b α L t := by
  intro j hj hjT
  rcases Nat.eq_or_lt_of_le hj with e | lt
  · subst e; exact ⟨hr, hα⟩
  · exact hG j lt hjT

end LeviSamplingAux


open MeasureTheory

namespace LeviSamplingAux

open LeviSampling.BaseStock

instance pathLaw_isProb (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (pathLaw T μ) := by
  unfold pathLaw; infer_instance

instance algMeasure_isProb (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h b ε δ : ℝ) : IsProbabilityMeasure (algMeasure T μ h b ε δ) := by
  unfold algMeasure; infer_instance

lemma stage_step (T : ℕ) (hT : 1 ≤ T) (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, Integrable id (μ i))
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (t : ℕ) (ht : t < T) :
    ENNReal.ofReal (1 - deltaStage T δ) *
        algMeasure T μ h b ε δ
          {ω | Good T μ h b (alphaStage T h b ε) (algLevel T h b ε δ ω) (t + 1)} ≤
      algMeasure T μ h b ε δ
          {ω | Good T μ h b (alphaStage T h b ε) (algLevel T h b ε δ ω) t} := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hmin : 0 < min b h := lt_min hb hh
  have hεT : ε / (2 * T) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hαpos : 0 < alphaStage T h b ε := by
    unfold alphaStage epsStage; positivity
  have hαh : alphaStage T h b ε ≤ 2 * h * ((T - t : ℕ) : ℝ) := by
    have hTt : (1 : ℝ) ≤ ((T - t : ℕ) : ℝ) := by
      have : 1 ≤ T - t := by omega
      exact_mod_cast this
    have h1 : alphaStage T h b ε ≤ h := by
      unfold alphaStage epsStage
      have hm : min b h ≤ h := min_le_right _ _
      have h0 : 0 ≤ ε / (2 * T) := by positivity
      calc ε / (2 * ↑T) / 3 * min b h ≤ 1 / 3 * h := by
            apply mul_le_mul (by linarith) hm hmin.le (by norm_num)
        _ ≤ h := by linarith
    nlinarith
  have hδt : 0 < deltaStage T δ := by unfold deltaStage; positivity
  have hδt1 : deltaStage T δ < 1 := by
    unfold deltaStage; rw [div_lt_one hTpos]; linarith
  unfold algMeasure
  apply pi_lower (fun s : Fin T => Measure.pi fun _ : Fin (sampleSize T h b ε δ s) => pathLaw T μ)
    (⟨t, ht⟩ : Fin T)
  intro ω hω
  set i : Fin T := ⟨t, ht⟩ with hi
  set L' : ℕ → ℝ := fun k => if _hk : t < k then algLevel T h b ε δ ω k else 0 with hL'
  have hG' : Good T μ h b (alphaStage T h b ε) L' (t + 1) :=
    good_congr T μ h b _ (algLevel T h b ε δ ω) L' (t + 1)
      (fun m hm => by simp only [hL', dif_pos (show t < m by omega)]) hω
  have hL'up : IsUpperBaseStock T μ (fun _ => h) (fun _ => b) L' (t + 1) :=
    fun j hj hjT => (hG' j hj hjT).1
  obtain ⟨r, hr⟩ := (upper_base_stock_convex T μ hμ (fun _ => h) (fun _ => b) (fun _ => hh)
    (fun _ => hb) L' t ht hL'up t le_rfl ht).2
  have hN : 2 * ((b + h) * ((T - t : ℕ) : ℝ)) ^ 2 * (1 / alphaStage T h b ε ^ 2) *
      Real.log (2 / deltaStage T δ) ≤ (sampleSize T h b ε δ t : ℝ) := by
    unfold sampleSize; exact Nat.le_ceil _
  have key := stage_alpha_point T μ hμ h b hh hb L' t ht hL'up r hr.2 (alphaStage T h b ε)
    (deltaStage T δ) hαpos hαh hδt hδt1 (sampleSize T h b ε δ t) hN
  refine key.trans (measure_mono ?_)
  intro x hx
  obtain ⟨hxα, hxr⟩ := hx
  simp only [Set.mem_setOf_eq]
  have hagree : ∀ m, t < m →
      algLevel T h b ε δ (Function.update ω i x) m = algLevel T h b ε δ ω m :=
    fun m hm => algLevel_update T h b ε δ ω i x _ m le_rfl hm
  have hLt : algLevel T h b ε δ (Function.update ω i x) t =
      sInf {y | alphaStage T h b ε / 2 ≤
        sampleRightDeriv T (fun _ => h) (fun _ => b) L' t x y} := by
    have := algLevel_at T h b ε δ (Function.update ω i x) i
    rw [Function.update_self] at this
    have hfun : (fun k => if _hk : (i : ℕ) < k then
        algLevel T h b ε δ (Function.update ω i x) k else 0) = L' := by
      funext k
      by_cases hk : t < k
      · have hk' : (i : ℕ) < k := hk
        rw [dif_pos hk']; simp only [hL', dif_pos hk, hagree k hk]
      · have hk' : ¬ (i : ℕ) < k := hk
        rw [dif_neg hk']; simp only [hL', dif_neg hk]
    rw [hfun] at this
    exact this
  have hsh : shadowU T μ (fun _ => h) (fun _ => b) (algLevel T h b ε δ (Function.update ω i x)) t
      = shadowU T μ (fun _ => h) (fun _ => b) L' t :=
    shadowU_congr T μ _ _ _ L' t (fun m hm => by simp only [hL', dif_pos hm, hagree m hm])
  apply good_step
  · exact good_congr T μ h b _ (algLevel T h b ε δ ω) _ (t + 1)
      (fun m hm => (hagree m (by omega)).symm) hω
  · refine ⟨r, ?_, ?_⟩
    · unfold IsShadowLevel; rw [hsh]; exact hr
    · rw [hLt]; exact hxr
  · rw [hsh, hLt]; exact hxα

lemma good_prob (T : ℕ) (hT : 1 ≤ T) (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, Integrable id (μ i))
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ n s, T - s = n → s ≤ T →
      ENNReal.ofReal (1 - deltaStage T δ) ^ (T - s) ≤
        algMeasure T μ h b ε δ
          {ω | Good T μ h b (alphaStage T h b ε) (algLevel T h b ε δ ω) s} := by
  intro n
  induction n with
  | zero =>
    intro s hs hsT
    have hsT' : s = T := by omega
    subst hsT'
    have : {ω | Good s μ h b (alphaStage s h b ε) (algLevel s h b ε δ ω) s} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro j hj hjT; omega
    rw [this, measure_univ, Nat.sub_self, pow_zero]
  | succ n ih =>
    intro s hs hsT
    have h1 := ih (s + 1) (by omega) (by omega)
    have h2 := stage_step T hT μ hμ h b hh hb ε δ hε hε1 hδ hδ1 s (by omega)
    have e : T - s = (T - (s + 1)) + 1 := by omega
    rw [e, pow_succ, mul_comm]
    refine le_trans ?_ h2
    gcongr

end LeviSamplingAux

open LeviSampling.BaseStock LeviSamplingAux in
theorem solution (T : ℕ) (hT : 1 ≤ T) (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, Integrable id (μ i))
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      algMeasure T μ h b ε δ
        {ω | shadowU T μ (fun _ => h) (fun _ => b) (algLevel T h b ε δ ω) 0
                (algLevel T h b ε δ ω 0) ≤
              (1 + ε) * optCost T μ (fun _ => h) (fun _ => b)} := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have h0 := good_prob T hT μ hμ h b hh hb ε δ hε hε1 hδ hδ1 T 0 (by simp) (Nat.zero_le _)
  rw [Nat.sub_zero] at h0
  have hδT : δ / T ≤ 1 := by
    rw [div_le_one hTpos]; have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  calc ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal (1 - deltaStage T δ) ^ T := by
        rw [← ENNReal.ofReal_pow (by unfold deltaStage; linarith)]
        apply ENNReal.ofReal_le_ofReal
        have hb' := one_add_mul_le_pow (a := -(δ / T)) (by linarith [div_nonneg hδ.le hTpos.le]) T
        unfold deltaStage
        have e1 : (1 : ℝ) + T * -(δ / T) = 1 - δ := by field_simp; ring
        have e2 : (1 : ℝ) + -(δ / T) = 1 - δ / T := by ring
        rw [e1, e2] at hb'
        exact hb'
    _ ≤ _ := h0
    _ ≤ _ := measure_mono (fun ω hω => good_cost T hT μ hμ h b hh hb ε hε hε1 _ hω)

