-- Prove2me | solution 1 for InfoGen.HighProb.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T07:40:35.644223+00:00
-- url     : https://prove2.me/submissions/4e6719e3-aa02-4871-98fe-a625fe5de39e

import Mathlib
import Definitions.Def_InfoGen_HighProb_Setting

open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal

section
open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal
noncomputable section
namespace InfoGen.HighProb.Fresh
end InfoGen.HighProb.Fresh
end

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
noncomputable section
namespace InfoGen.HighProb.Fresh

theorem density_exp_bound (r y : ℝ) (hr : 0 ≤ r) :
    r * y ≤ klFun r + Real.exp y - 1 := by
  by_cases h : r = 0
  · subst r
    simp only [zero_mul, klFun_zero]
    linarith [Real.exp_pos y]
  have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm h)
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - Real.log r)) hr
  rw [Real.exp_sub, Real.exp_log hp] at he
  have hid : r * (Real.exp y / r) = Real.exp y := by field_simp
  rw [hid] at he
  dsimp [klFun]
  nlinarith

theorem event_entropy_bound {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : Set Ω) (hB : MeasurableSet B) (hkl : klDiv P Q ≠ ∞) (a : ℝ) :
    a * (P B).toReal ≤ (klDiv P Q).toReal + (Q B).toReal * (Real.exp a - 1) := by
  classical
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hkl
  let f : Ω → ℝ := B.indicator (fun _ => a)
  let g : Ω → ℝ := B.indicator (fun _ => Real.exp a - 1)
  have hf : Integrable f P := (integrable_const a).indicator hB
  have hg : Integrable g Q := (integrable_const (Real.exp a - 1)).indicator hB
  have hr : Integrable (fun x => (P.rnDeriv Q x).toReal * f x) Q :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr hf
  have hk : Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q :=
    (integrable_klFun_rnDeriv_iff hac).mpr hint
  have hpoint (x : Ω) : (P.rnDeriv Q x).toReal * f x ≤
      klFun (P.rnDeriv Q x).toReal + g x := by
    have h := density_exp_bound (P.rnDeriv Q x).toReal (f x) ENNReal.toReal_nonneg
    by_cases hx : x ∈ B
    · simpa [f, g, hx, add_sub_assoc] using h
    · simpa [f, g, hx] using h
  have hi := integral_mono hr (hk.add hg) hpoint
  change (∫ x, (P.rnDeriv Q x).toReal * f x ∂Q) ≤
    ∫ x, klFun (P.rnDeriv Q x).toReal + g x ∂Q at hi
  rw [integral_toReal_rnDeriv_mul hac, integral_add hk hg,
    ← toReal_klDiv_eq_integral_klFun hac] at hi
  simpa [f, g, integral_indicator hB, measureReal_def, mul_comm] using hi

end InfoGen.HighProb.Fresh
end

section
open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal
noncomputable section
namespace InfoGen.HighProb.Fresh
variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

theorem measurable_empRiskVec (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (n : ℕ) : Measurable (empRiskVec ℓ : (Fin n → Z) → W → ℝ) := by
  apply measurable_pi_lambda
  intro w
  exact (Finset.measurable_sum Finset.univ (fun i _ =>
    hℓ.of_uncurry_left.comp (measurable_pi_apply i))).div_const _

theorem measurable_vector_event [Countable W] [MeasurableSingletonClass W]
    (r : W → ℝ) (a : ℝ) : MeasurableSet {p : (W → ℝ) × W | a < |r p.2 - p.1 p.2|} := by
  have hm : Measurable (fun p : (W → ℝ) × W => r p.2 - p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro w
    change Measurable (fun x : W → ℝ => r w - x w)
    exact measurable_const.sub (measurable_pi_apply (X := fun _ : W => ℝ) w)
  exact measurableSet_lt measurable_const hm.abs

def vectorMap (ℓ : W → Z → ℝ) (n : ℕ) (p : (Fin n → Z) × W) : (W → ℝ) × W :=
  (empRiskVec ℓ p.1, p.2)

theorem measurable_vectorMap (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (n : ℕ) : Measurable (vectorMap ℓ n) :=
  ((measurable_empRiskVec ℓ hℓ n).comp measurable_fst).prodMk measurable_snd

theorem vector_fst (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ] :
    ((sampleLaw μ n ⊗ₘ κ).map (vectorMap ℓ n)).fst =
      (sampleLaw μ n).map (empRiskVec ℓ) := by
  let : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
  change ((sampleLaw μ n ⊗ₘ κ).map (fun p => (empRiskVec ℓ p.1, p.2))).fst = _
  rw [Measure.fst_map_prodMk measurable_snd]
  change (sampleLaw μ n ⊗ₘ κ).map (empRiskVec ℓ ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_empRiskVec ℓ hℓ n) measurable_fst]
  change ((sampleLaw μ n ⊗ₘ κ).fst).map _ = _
  rw [Measure.fst_compProd]

theorem reference_vector_map (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (ν : Measure W) [IsProbabilityMeasure ν] :
    ((sampleLaw μ n).map (empRiskVec ℓ)).prod ν =
      ((sampleLaw μ n).prod ν).map (vectorMap ℓ n) := by
  let : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
  have h := Measure.map_prod_map (sampleLaw μ n) ν (measurable_empRiskVec ℓ hℓ n) measurable_id
  rw [Measure.map_id] at h
  have he : Prod.map (empRiskVec ℓ) (id : W → W) = vectorMap ℓ n := by
    funext p
    rfl
  rw [he] at h
  exact h

end InfoGen.HighProb.Fresh
end

section
open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal
noncomputable section
namespace InfoGen.HighProb.Fresh
variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
  [Countable W] [MeasurableSingletonClass W]

theorem vector_event_eq {n : ℕ} (J : Measure ((Fin n → Z) × W))
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (r : W → ℝ) (a : ℝ) :
    (J.map (vectorMap ℓ n)) {p | a < |r p.2 - p.1 p.2|} =
      J {p | a < |r p.2 - empRisk ℓ p.1 p.2|} := by
  rw [Measure.map_apply (measurable_vectorMap ℓ hℓ n) (measurable_vector_event r a)]
  rfl

theorem reference_event_eq (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (ν : Measure W) [IsProbabilityMeasure ν] (a : ℝ) :
    (((sampleLaw μ n).map (empRiskVec ℓ)).prod ν)
      {p | a < |risk ℓ μ p.2 - p.1 p.2|} =
      ((sampleLaw μ n).prod ν) {p | a < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} := by
  rw [reference_vector_map μ n ℓ hℓ ν]
  exact vector_event_eq _ ℓ hℓ _ a

end InfoGen.HighProb.Fresh
end

section
open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal
namespace InfoGen.HighProb.Fresh
noncomputable section
variable {Z W : Type*} [MeasurableSpace Z]

theorem empirical_subgaussian (μ : Measure Z) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (ℓ : W → Z → ℝ) (w : W) (σ : ℝ≥0)
    (hm : Measurable (ℓ w))
    (hs : HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ) :
    HasSubgaussianMGF (fun s : Fin n → Z => empRisk ℓ s w - risk ℓ μ w)
      (σ ^ 2 / n) (sampleLaw μ n) := by
  have hi : iIndepFun (fun (i : Fin n) (s : Fin n → Z) =>
      ℓ w (s i) - risk ℓ μ w) (sampleLaw μ n) :=
    iIndepFun_pi (fun _ => (hm.sub_const _).aemeasurable)
  have hj (i : Fin n) : HasSubgaussianMGF
      (fun s : Fin n → Z => ℓ w (s i) - risk ℓ μ w) (σ ^ 2) (sampleLaw μ n) := by
    have hmap := (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq
    have h : HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2)
        ((Measure.pi (fun _ : Fin n => μ)).map (Function.eval i)) := by
      rw [hmap]
      exact hs
    exact HasSubgaussianMGF.of_map (μ := sampleLaw μ n)
      (Y := Function.eval i) (X := fun z => ℓ w z - risk ℓ μ w)
      (measurable_pi_apply i).aemeasurable h
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hi
    (s := Finset.univ) (c := fun _ : Fin n => σ ^ 2) (fun i _ => hj i)
  have hnR : (n : ℝ) ≠ 0 := by positivity
  convert hsum.const_mul (1 / (n : ℝ)) using 1
  · funext s
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, empRisk]
    field_simp
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply NNReal.coe_injective
    change (σ : ℝ)^2 / (n : ℝ) = (1 / (n : ℝ))^2 * ((n : ℝ) * (σ : ℝ)^2)
    field_simp
end
end InfoGen.HighProb.Fresh
end

section
open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal
namespace InfoGen.HighProb.Fresh
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

theorem subgaussian_abs_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    {a : ℝ} (ha : 0 ≤ a) :
    μ.real {s | a < |X s|} ≤ 2 * Real.exp (-a ^ 2 / (2 * c)) := by
  have hsub : {s | a < |X s|} ⊆ {s | a ≤ X s} ∪ {s | a ≤ -X s} := by
    intro s hs
    change a < |X s| at hs
    rcases lt_abs.mp hs with hs | hs
    · exact Or.inl hs.le
    · exact Or.inr hs.le
  have hneg := h.neg.measure_ge_le ha
  have hpos := h.measure_ge_le ha
  have hle := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  exact hle.trans (by simpa only [Pi.neg_apply, two_mul] using add_le_add hpos hneg)

variable {Z W : Type*} [MeasurableSpace Z]
theorem sample_measure_bound (μ : Measure Z) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (ℓ : W → Z → ℝ) (w : W) (σ : ℝ≥0)
    (hm : Measurable (ℓ w))
    (hs : HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    {a : ℝ} (ha : 0 ≤ a) :
    (sampleLaw μ n) {s | a < |risk ℓ μ w - empRisk ℓ s w|} ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * a ^ 2 / (2 * (σ : ℝ) ^ 2))) := by
  let : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
  have ht := subgaussian_abs_tail (sampleLaw μ n)
    (empirical_subgaussian μ n hn ℓ w σ hm hs) ha
  have he : -a ^ 2 / (2 * ((σ ^ 2 / n : ℝ≥0) : ℝ)) =
      -(n : ℝ) * a ^ 2 / (2 * (σ : ℝ) ^ 2) := by
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he] at ht
  simp only [abs_sub_comm (empRisk ℓ _ w) (risk ℓ μ w)] at ht
  have ht' := ENNReal.ofReal_le_ofReal ht
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at ht'
  exact ht'

theorem sample_measure_zero (μ : Measure Z) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (ℓ : W → Z → ℝ) (w : W)
    (hm : Measurable (ℓ w))
    (hs : HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) 0 μ)
    {a : ℝ} (ha : 0 < a) :
    (sampleLaw μ n) {s | a < |risk ℓ μ w - empRisk ℓ s w|} = 0 := by
  let : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
  have h := empirical_subgaussian μ n hn ℓ w 0 hm (by simpa using hs)
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div] at h
  have hz := h.ae_eq_zero_of_hasSubgaussianMGF_zero
  apply measure_mono_null (t := {s | empRisk ℓ s w - risk ℓ μ w ≠ 0})
  · intro s hs'
    change empRisk ℓ s w - risk ℓ μ w ≠ 0
    intro he
    have : risk ℓ μ w - empRisk ℓ s w = 0 := by linarith
    simp [this, not_lt.mpr ha.le] at hs'
  · exact ae_iff.mp hz
end
end InfoGen.HighProb.Fresh
end

section
open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal
namespace InfoGen.HighProb.Fresh
noncomputable section
variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]

omit [Countable W] [MeasurableSingletonClass W] in
theorem measurable_empRisk_joint (n : ℕ) (ℓ : W → Z → ℝ)
    (hm : Measurable (Function.uncurry ℓ)) :
    Measurable (fun p : (Fin n → Z) × W => empRisk ℓ p.1 p.2) := by
  unfold empRisk
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact hm.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))

theorem measurable_tail_event (μ : Measure Z) (n : ℕ) (ℓ : W → Z → ℝ)
    (hm : Measurable (Function.uncurry ℓ)) (a : ℝ) :
    MeasurableSet {p : (Fin n → Z) × W |
      a < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} := by
  exact measurableSet_lt measurable_const
    (((measurable_of_countable (risk ℓ μ)).comp measurable_snd).sub
      (measurable_empRisk_joint n ℓ hm)).abs

theorem reference_measure_bound (μ : Measure Z) [IsProbabilityMeasure μ]
    (ν : Measure W) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (ℓ : W → Z → ℝ)
    (hm : Measurable (Function.uncurry ℓ)) (σ : ℝ≥0)
    (hs : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    {a : ℝ} (ha : 0 ≤ a) :
    ((sampleLaw μ n).prod ν) {p | a < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * a ^ 2 / (2 * (σ : ℝ) ^ 2))) := by
  let : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
  rw [Measure.prod_apply_symm (measurable_tail_event μ n ℓ hm a)]
  calc
    _ ≤ ∫⁻ _ : W, ENNReal.ofReal
        (2 * Real.exp (-(n : ℝ) * a ^ 2 / (2 * (σ : ℝ) ^ 2))) ∂ν := by
      apply lintegral_mono
      intro w
      exact sample_measure_bound μ n hn ℓ w σ
        (hm.comp (measurable_const.prodMk measurable_id)) (hs w) ha
    _ = _ := by simp

theorem reference_measure_zero (μ : Measure Z) [IsProbabilityMeasure μ]
    (ν : Measure W) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (ℓ : W → Z → ℝ)
    (hm : Measurable (Function.uncurry ℓ))
    (hs : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) 0 μ)
    {a : ℝ} (ha : 0 < a) :
    ((sampleLaw μ n).prod ν) {p | a < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} = 0 := by
  let : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
  rw [Measure.prod_apply_symm (measurable_tail_event μ n ℓ hm a)]
  have hz (w : W) : (sampleLaw μ n)
      ((fun s => (s,w)) ⁻¹' {p | a < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|}) = 0 :=
    sample_measure_zero μ n hn ℓ w
      (hm.comp (measurable_const.prodMk measurable_id)) (hs w) ha
  simp_rw [hz]
  simp
end
end InfoGen.HighProb.Fresh
end

section

noncomputable section
namespace InfoGen.HighProb.Fresh

lemma budget_log_lower (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (1 / 2 : ℝ) ≤ Real.log (2 / β) := by
  have hfrac : (2 : ℝ) ≤ 2 / β := (le_div_iff₀ hβ0).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hfrac
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  linarith

lemma information_budget_pos (ε β : ℝ) (hε : 0 ≤ ε) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    0 < ε / β + Real.log (2 / β) := by
  have hd := div_nonneg hε hβ0.le
  have hl := budget_log_lower β hβ0 hβ1
  linarith

lemma entropy_tail_budget (ε β p q z : ℝ) (hε : 0 ≤ ε) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hq0 : 0 ≤ q) (hz : 4 * (ε / β + Real.log (2 / β)) ≤ z)
    (hq : q ≤ 2 * Real.exp (-z))
    (hent : (ε / β + Real.log (2 / β)) * p ≤
      ε + q * (Real.exp (ε / β + Real.log (2 / β)) - 1)) : p ≤ β := by
  let H := ε / β + Real.log (2 / β)
  have hH : 0 < H := information_budget_pos ε β hε hβ0 hβ1
  have hHlog : Real.log (2 / β) ≤ H := by
    have hh := div_nonneg hε hβ0.le
    dsimp [H]
    linarith
  have he : Real.exp (-H) ≤ β / 2 := by
    calc
      Real.exp (-H) ≤ Real.exp (-Real.log (2 / β)) := Real.exp_le_exp.mpr (by linarith)
      _ = β / 2 := by rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hβ0), inv_div]
  have hp : (Real.exp (-H)) ^ 3 ≤ (β / 2) ^ 3 := by gcongr
  have heq : Real.exp (-3 * H) = (Real.exp (-H)) ^ 3 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hmid : 2 * Real.exp (-z) * Real.exp H ≤ 2 * (Real.exp (-H)) ^ 3 := by
    calc
      _ = 2 * Real.exp (H - z) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring
      _ ≤ 2 * Real.exp (-3 * H) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by change 4 * H ≤ z at hz; linarith)) (by norm_num)
      _ = _ := by rw [heq]
  have hb2 : β ^ 2 ≤ 1 := by nlinarith
  have hb3 : β ^ 3 ≤ β := by
    have hh := mul_le_mul_of_nonneg_left hb2 hβ0.le
    nlinarith
  have htail : q * (Real.exp H - 1) ≤ β / 4 := by
    have hqmul := mul_le_mul_of_nonneg_right hq (Real.exp_pos H).le
    have hpow := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hHβ : H * β = ε + β * Real.log (2 / β) := by
    dsimp [H]
    rw [add_mul, div_mul_cancel₀ ε hβ0.ne']
    ring
  have hstrict : ε + β / 4 < H * β := by
    rw [hHβ]
    have hh := mul_le_mul_of_nonneg_left (budget_log_lower β hβ0 hβ1) hβ0.le
    nlinarith
  have hh : H * p < H * β := lt_of_le_of_lt (le_trans hent (by linarith [htail])) hstrict
  exact ((mul_lt_mul_iff_right₀ hH).mp hh).le

lemma sample_exponent_lower (σ α H : ℝ) (n : ℕ) (hσ : 0 < σ) (hα : 0 < α)
    (hn : 8 * σ ^ 2 / α ^ 2 * H ≤ n) : 4 * H ≤ (n : ℝ) * α ^ 2 / (2 * σ ^ 2) := by
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  have hσ2 : 0 < σ ^ 2 := pow_pos hσ 2
  have hh := mul_le_mul_of_nonneg_right hn hα2.le
  have he : (8 * σ ^ 2 / α ^ 2 * H) * α ^ 2 = 8 * σ ^ 2 * H := by
    field_simp [hα.ne']
  rw [he] at hh
  apply (le_div_iff₀ (by positivity : 0 < 2 * σ ^ 2)).mpr
  nlinarith

end InfoGen.HighProb.Fresh
end

section
open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal
namespace InfoGen.HighProb.Fresh

theorem native_theorem_3 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn0 : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (_hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : lambdaInfo ℓ μ κ ≤ ENNReal.ofReal ε)
    (α β : ℝ) (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hn : 8 * (σ : ℝ) ^ 2 / α ^ 2 * (ε / β + Real.log (2 / β)) ≤ n) :
    (sampleLaw μ n ⊗ₘ κ) {p | α < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} ≤
      ENNReal.ofReal β := by
  let : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
  let J := sampleLaw μ n ⊗ₘ κ
  let P := J.map (vectorMap ℓ n)
  have hmap := measurable_vectorMap ℓ hℓ n
  let : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hmap.aemeasurable
  let Q := P.fst.prod P.snd
  let B : Set ((W → ℝ) × W) := {p | α < |risk ℓ μ p.2 - p.1 p.2|}
  have hB : MeasurableSet B := measurable_vector_event _ _
  have hk : klDiv P Q ≤ ENNReal.ofReal ε := hε
  have hktop : klDiv P Q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hk
  have hPQ : P B = J {p | α < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} :=
    vector_event_eq J ℓ hℓ _ _
  have hQ : Q B = ((sampleLaw μ n).prod P.snd)
      {p | α < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} := by
    change (P.fst.prod P.snd) B = _
    have hfst : P.fst = (sampleLaw μ n).map (empRiskVec ℓ) := vector_fst μ n ℓ hℓ κ
    rw [hfst]
    exact reference_event_eq μ n ℓ hℓ P.snd α
  change J {p | α < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} ≤ _
  rw [← hPQ]
  by_cases hs0 : σ = 0
  · have hzero : Q B = 0 := by
      rw [hQ]
      apply reference_measure_zero μ P.snd n hn0 ℓ hℓ _ hα
      intro w
      simpa [hs0] using hσ w
    have hz := (klDiv_ne_top_iff.mp hktop).1 hzero
    rw [hz]
    exact bot_le
  have hσpos : 0 < (σ : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hs0 : 0 < σ)
  have hqr : (Q B).toReal ≤ 2 * Real.exp (-((n : ℝ) * α ^ 2 / (2 * (σ : ℝ) ^ 2))) := by
    have ht := reference_measure_bound μ P.snd n hn0 ℓ hℓ σ hσ hα.le
    rw [← hQ] at ht
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    simpa only [neg_div, neg_mul] using hh
  have hkr : (klDiv P Q).toReal ≤ ε := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hk
    simpa [ENNReal.toReal_ofReal hε0] using hh
  have he := event_entropy_bound P Q B hB hktop (ε / β + Real.log (2 / β))
  have hp : (P B).toReal ≤ β := entropy_tail_budget ε β (P B).toReal (Q B).toReal
      ((n : ℝ) * α ^ 2 / (2 * (σ : ℝ) ^ 2)) hε0 hβ0 hβ1 ENNReal.toReal_nonneg
      (sample_exponent_lower (σ : ℝ) α _ n hσpos hα hn) hqr (by linarith)
  rw [← ENNReal.ofReal_toReal (measure_ne_top P B)]
  exact ENNReal.ofReal_le_ofReal hp


end InfoGen.HighProb.Fresh
end

open InfoGen.HighProb

theorem solution {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn0 : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : lambdaInfo ℓ μ κ ≤ ENNReal.ofReal ε)
    (α β : ℝ) (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hn : 8 * (σ : ℝ) ^ 2 / α ^ 2 * (ε / β + Real.log (2 / β)) ≤ n) :
    (sampleLaw μ n ⊗ₘ κ) {p | α < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} ≤
      ENNReal.ofReal β := by
  exact Fresh.native_theorem_3 μ n hn0 ℓ hℓ hℓ0 κ σ hσ ε hε0 hε α β hα hβ0 hβ1 hn
