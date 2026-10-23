-- Prove2me | solution 1 for LeviSampling.BaseStock.shadow_right_deriv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:34:12.61657+00:00
-- url     : https://prove2.me/submissions/5044acd5-ec85-4b88-b1aa-a305fb1b17a9

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow
import Definitions.Def_LeviSampling_BaseStock_Estimator

open MeasureTheory Filter Topology

namespace LeviSampling.BaseStock

theorem X7L_lip_cont (F : ℝ → ℝ) (K : ℝ) (hK : ∀ a b, |F a - F b| ≤ K * |a - b|) :
    Continuous F := by
  have hK0 : 0 ≤ K ∨ True := Or.inr trivial
  rw [Metric.continuous_iff]
  intro a ε hε
  refine ⟨ε / (|K| + 1), by positivity, fun c hc => ?_⟩
  rw [Real.dist_eq] at hc ⊢
  calc |F c - F a| ≤ K * |c - a| := hK c a
    _ ≤ |K| * |c - a| := by gcongr; exact le_abs_self K
    _ ≤ |K| * (ε / (|K| + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg K]

theorem X7L_lip_int (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (F : ℝ → ℝ) (K : ℝ) (hK : ∀ a b, |F a - F b| ≤ K * |a - b|) (z : ℝ) :
    Integrable (fun d => F (z - d)) μ := by
  have hc := X7L_lip_cont F K hK
  refine Integrable.mono' (g := fun d => |F 0| + K * |z| + K * |d|) ?_ ?_ ?_
  · exact ((integrable_const _).add ((hμ.abs).const_mul K))
  · exact (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun d => ?_
    rw [Real.norm_eq_abs]
    have h1 := hK (z - d) 0
    have h2 : |z - d - 0| ≤ |z| + |d| := by rw [sub_zero]; exact abs_sub _ _
    have hK0 : 0 ≤ K := by
      have := hK 1 0
      nlinarith [abs_nonneg (F 1 - F 0), abs_nonneg ((1:ℝ) - 0), show |(1:ℝ) - 0| = 1 by simp]
    have h3 : |F (z - d)| ≤ |F 0| + |F (z - d) - F 0| := by
      have := abs_add_le (F 0) (F (z - d) - F 0)
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_left h2 hK0]

theorem X7L_rd (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (F F' : ℝ → ℝ) (K : ℝ) (hK : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (hF : ∀ u, HasDerivWithinAt F (F' u) (Set.Ici u) u) (z : ℝ) :
    HasDerivWithinAt (fun w => ∫ d, F (w - d) ∂μ) (∫ d, F' (z - d) ∂μ) (Set.Ici z) z := by
  have hc := X7L_lip_cont F K hK
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope' (show z ∉ Set.Ioi z from lt_irrefl z)]
  have hslope : ∀ w, slope (fun w => ∫ d, F (w - d) ∂μ) z w =
      ∫ d, (w - z)⁻¹ * (F (w - d) - F (z - d)) ∂μ := by
    intro w
    rw [slope_def_field, integral_const_mul, integral_sub (X7L_lip_int μ hμ F K hK w)
      (X7L_lip_int μ hμ F K hK z), div_eq_inv_mul]
  rw [show slope (fun w => ∫ d, F (w - d) ∂μ) z = fun w => ∫ d, (w - z)⁻¹ * (F (w - d) - F (z - d)) ∂μ from funext hslope]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => K) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun w => ?_
    exact (continuous_const.mul ((hc.comp (continuous_const.sub continuous_id)).sub
      (hc.comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with w hw
    refine Eventually.of_forall fun d => ?_
    have hw' : w - z ≠ 0 := sub_ne_zero.mpr (ne_of_gt hw)
    rw [Real.norm_eq_abs, abs_mul, abs_inv]
    have := hK (w - d) (z - d)
    rw [show w - d - (z - d) = w - z by ring] at this
    rw [inv_mul_le_iff₀ (abs_pos.mpr hw')]
    linarith [mul_comm K |w - z|]
  · refine Eventually.of_forall fun d => ?_
    have hd : HasDerivWithinAt (fun w => F (w - d)) (F' (z - d)) (Set.Ici z) z := by
      have h1 := (hF (z - d)).comp z (((hasDerivAt_id z).sub_const d).hasDerivWithinAt (s := Set.Ici z))
        (fun w hw => by simp only [Set.mem_Ici, id] at hw ⊢; linarith)
      simpa [Function.comp_def] using h1
    rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope' (show z ∉ Set.Ioi z from lt_irrefl z)] at hd
    refine hd.congr fun w => ?_
    rw [slope_def_field, div_eq_inv_mul]

/-- right derivative of `g (max z L)` -/
theorem X7L_max (g : ℝ → ℝ) (g' : ℝ) (L x : ℝ) (hg : HasDerivWithinAt g g' (Set.Ici x) x) :
    HasDerivWithinAt (fun z => g (max z L)) (if L ≤ x then g' else 0) (Set.Ici x) x := by
  by_cases hL : L ≤ x
  · rw [if_pos hL]
    refine hg.congr (fun z hz => ?_) ?_
    · simp only [Set.mem_Ici] at hz; rw [max_eq_left (le_trans hL hz)]
    · rw [max_eq_left hL]
  · rw [if_neg hL]
    rw [not_le] at hL
    have : (fun z => g (max z L)) =ᶠ[𝓝 x] fun _ => g L := by
      filter_upwards [Iio_mem_nhds hL] with z hz
      rw [max_eq_right (le_of_lt hz)]
    exact ((hasDerivAt_const x (g L)).congr_of_eventuallyEq this).hasDerivWithinAt

end LeviSampling.BaseStock

open MeasureTheory Filter Topology

namespace LeviSampling.BaseStock

theorem X7L_fubini {n : ℕ} (ν : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (jj : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Integrable F (Measure.pi ν)) :
    ∫ p, F p ∂(Measure.pi ν) =
      ∫ v, ∫ x, F (Fin.insertNth jj x v) ∂(ν jj) ∂(Measure.pi fun k => ν (jj.succAbove k)) := by
  have hmp := (measurePreserving_piFinSuccAbove ν jj).symm
  rw [← hmp.integral_comp' F]
  have hint : Integrable (fun z => F ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) jj).symm z))
      ((ν jj).prod (Measure.pi fun k => ν (jj.succAbove k))) := by
    exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hF
  rw [integral_prod_symm _ hint]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rfl

theorem X7L_extend_insert {n : ℕ} (jj : Fin (n + 1)) (x : ℝ) (v : Fin n → ℝ) :
    extendPath (Fin.insertNth jj x v) =
      Function.update (extendPath (Fin.insertNth jj 0 v)) jj.1 x := by
  funext k
  have hu : Function.update (Fin.insertNth (α := fun _ => ℝ) jj (0:ℝ) v) jj x =
      Fin.insertNth (α := fun _ => ℝ) jj x v :=
    Fin.update_insertNth (α := fun _ => ℝ) jj (0:ℝ) x v
  rw [← hu]
  unfold extendPath
  by_cases hk : k < n + 1
  · rw [dif_pos hk]
    by_cases hkj : k = jj.1
    · subst hkj; simp
    · have : (⟨k, hk⟩ : Fin (n+1)) ≠ jj := fun h => hkj (by rw [← h])
      rw [Function.update_of_ne this, Function.update_of_ne hkj, dif_pos hk]
  · rw [dif_neg hk, Function.update_of_ne (by omega), dif_neg hk]

theorem X7L_meas_ext {T : ℕ} (k : ℕ) : Measurable (fun p : Fin T → ℝ => extendPath p k) := by
  unfold extendPath
  by_cases hk : k < T
  · simp only [dif_pos hk]; exact measurable_pi_apply _
  · simp only [dif_neg hk]; exact measurable_const

theorem X7L_meas_cum {T : ℕ} (t k : ℕ) :
    Measurable (fun p : Fin T → ℝ => cumDemand (extendPath p) t k) := by
  unfold cumDemand
  exact Finset.measurable_sum _ fun i _ => X7L_meas_ext i

open Classical in
noncomputable def X7term (h b L : ℕ → ℝ) (k j : ℕ) (P : ℕ → ℝ) (x : ℝ) : ℝ :=
  if (∀ m ∈ Finset.Icc k j, L m ≤ x - cumDemand P k m) then
    -b j + (h j + b j) * (if P j ≤ x - cumDemand P k j then 1 else 0) else 0

noncomputable def X7S (T : ℕ) (h b L : ℕ → ℝ) (k : ℕ) (P : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico k T, X7term h b L k j P x

noncomputable def X7psi (T : ℕ) (μ : ℕ → Measure ℝ) (h b L : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∫ p, X7S T h b L k (extendPath p) x ∂(pathLaw T μ)

noncomputable def X7C (T : ℕ) (h b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico k T, (|b j| + |h j + b j|)

theorem X7L_cum_succ (P : ℕ → ℝ) (k m : ℕ) (hm : k < m) :
    cumDemand P k m = P k + cumDemand P (k + 1) m := by
  unfold cumDemand
  rw [Finset.sum_eq_sum_Ico_succ_bot hm]

theorem X7L_cum_self (P : ℕ → ℝ) (k : ℕ) : cumDemand P k k = 0 := by
  simp [cumDemand]

theorem X7L_term_succ (h b L : ℕ → ℝ) (k j : ℕ) (hkj : k < j) (P : ℕ → ℝ) (x : ℝ) :
    X7term h b L k j P x = if L k ≤ x then X7term h b L (k + 1) j P (x - P k) else 0 := by
  have hiff : (∀ m ∈ Finset.Icc k j, L m ≤ x - cumDemand P k m) ↔
      (L k ≤ x ∧ ∀ m ∈ Finset.Icc (k + 1) j, L m ≤ x - P k - cumDemand P (k + 1) m) := by
    constructor
    · intro H
      refine ⟨?_, fun m hm => ?_⟩
      · have := H k (by simp; omega)
        rwa [X7L_cum_self, sub_zero] at this
      · rw [Finset.mem_Icc] at hm
        have := H m (by rw [Finset.mem_Icc]; omega)
        rw [X7L_cum_succ P k m (by omega)] at this
        linarith
    · rintro ⟨H0, H⟩ m hm
      rw [Finset.mem_Icc] at hm
      rcases Nat.eq_or_lt_of_le hm.1 with h1 | h1
      · subst h1; rw [X7L_cum_self, sub_zero]; exact H0
      · have := H m (by rw [Finset.mem_Icc]; omega)
        rw [X7L_cum_succ P k m h1]
        linarith
  unfold X7term
  rw [X7L_cum_succ P k j hkj]
  by_cases h0 : L k ≤ x
  · simp only [hiff, h0, true_and, if_true]
    simp only [sub_sub]
  · simp only [hiff, h0, false_and, if_false]

theorem X7L_S_succ (T : ℕ) (h b L : ℕ → ℝ) (k : ℕ) (hk : k < T) (P : ℕ → ℝ) (x : ℝ) :
    X7S T h b L k P x = if L k ≤ x then
      (-b k + (h k + b k) * (if P k ≤ x then 1 else 0)) + X7S T h b L (k + 1) P (x - P k)
      else 0 := by
  unfold X7S
  rw [Finset.sum_eq_sum_Ico_succ_bot hk]
  have hrest : ∑ j ∈ Finset.Ico (k + 1) T, X7term h b L k j P x =
      ∑ j ∈ Finset.Ico (k + 1) T,
        (if L k ≤ x then X7term h b L (k + 1) j P (x - P k) else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    exact X7L_term_succ h b L k j (by omega) P x
  rw [hrest]
  have hkk : X7term h b L k k P x = if L k ≤ x then
      -b k + (h k + b k) * (if P k ≤ x then 1 else 0) else 0 := by
    unfold X7term
    simp [X7L_cum_self]
  rw [hkk]
  by_cases h0 : L k ≤ x
  · simp [h0]
  · simp [h0]

theorem X7L_S_ge (T : ℕ) (h b L : ℕ → ℝ) (k : ℕ) (hk : T ≤ k) (P : ℕ → ℝ) (x : ℝ) :
    X7S T h b L k P x = 0 := by
  unfold X7S
  rw [Finset.Ico_eq_empty_of_le hk, Finset.sum_empty]

theorem X7L_term_update (h b L : ℕ → ℝ) (k j : ℕ) (hj : k + 1 ≤ j) (P : ℕ → ℝ) (a x : ℝ) :
    X7term h b L (k + 1) j (Function.update P k a) x = X7term h b L (k + 1) j P x := by
  have hc : ∀ m, cumDemand (Function.update P k a) (k + 1) m = cumDemand P (k + 1) m := by
    intro m
    unfold cumDemand
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [Function.update_of_ne (by omega)]
  unfold X7term
  simp only [hc]
  rw [Function.update_of_ne (by omega)]

theorem X7L_S_update (T : ℕ) (h b L : ℕ → ℝ) (k : ℕ) (P : ℕ → ℝ) (a x : ℝ) :
    X7S T h b L (k + 1) (Function.update P k a) x = X7S T h b L (k + 1) P x := by
  unfold X7S
  exact Finset.sum_congr rfl fun j hj => X7L_term_update h b L k j
    (Finset.mem_Ico.mp hj).1 P a x

theorem X7L_term_bound (h b L : ℕ → ℝ) (k j : ℕ) (P : ℕ → ℝ) (x : ℝ) :
    |X7term h b L k j P x| ≤ |b j| + |h j + b j| := by
  unfold X7term
  split_ifs
  · calc |-b j + (h j + b j) * 1| ≤ |-b j| + |(h j + b j) * 1| := abs_add_le _ _
      _ = _ := by simp
  · calc |-b j + (h j + b j) * 0| ≤ |-b j| + |(h j + b j) * 0| := abs_add_le _ _
      _ ≤ _ := by simp
  · simp; positivity

theorem X7L_S_bound (T : ℕ) (h b L : ℕ → ℝ) (k : ℕ) (P : ℕ → ℝ) (x : ℝ) :
    |X7S T h b L k P x| ≤ X7C T h b k := by
  unfold X7S X7C
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => X7L_term_bound h b L k j P x)

theorem X7L_term_meas {T : ℕ} (h b L : ℕ → ℝ) (k j : ℕ) :
    Measurable (fun q : ℝ × (Fin T → ℝ) => X7term h b L k j (extendPath q.2) q.1) := by
  classical
  unfold X7term
  have hset : MeasurableSet {q : ℝ × (Fin T → ℝ) |
      ∀ m ∈ Finset.Icc k j, L m ≤ q.1 - cumDemand (extendPath q.2) k m} := by
    have : {q : ℝ × (Fin T → ℝ) |
        ∀ m ∈ Finset.Icc k j, L m ≤ q.1 - cumDemand (extendPath q.2) k m} =
        ⋂ m ∈ Finset.Icc k j, {q | L m ≤ q.1 - cumDemand (extendPath q.2) k m} := by
      ext q; simp
    rw [this]
    refine Finset.measurableSet_biInter _ fun m _ => ?_
    exact measurableSet_le measurable_const
      (measurable_fst.sub ((X7L_meas_cum k m).comp measurable_snd))
  refine Measurable.ite hset ?_ measurable_const
  refine measurable_const.add (measurable_const.mul ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le ((X7L_meas_ext j).comp measurable_snd)
    (measurable_fst.sub ((X7L_meas_cum k j).comp measurable_snd))

theorem X7L_S_meas {T : ℕ} (h b L : ℕ → ℝ) (k : ℕ) :
    Measurable (fun q : ℝ × (Fin T → ℝ) => X7S T h b L k (extendPath q.2) q.1) := by
  unfold X7S
  exact Finset.measurable_sum _ fun j _ => X7L_term_meas h b L k j

theorem X7L_S_int {T : ℕ} (ν : Measure (Fin T → ℝ)) [IsFiniteMeasure ν] (h b L : ℕ → ℝ)
    (k : ℕ) (x : ℝ) : Integrable (fun p => X7S T h b L k (extendPath p) x) ν := by
  refine Integrable.of_bound (C := X7C T h b k) ?_ (Eventually.of_forall fun p => ?_)
  · exact ((X7L_S_meas h b L k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact X7L_S_bound T h b L k _ x

theorem X7L_psi_bound (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h b L : ℕ → ℝ) (k : ℕ) (x : ℝ) : |X7psi T μ h b L k x| ≤ X7C T h b k := by
  unfold X7psi pathLaw
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := X7C T h b k)
    (Eventually.of_forall fun p => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact X7L_S_bound T h b L k _ x
  · simp

theorem X7L_psi_meas (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h b L : ℕ → ℝ) (k : ℕ) : Measurable (X7psi T μ h b L k) := by
  unfold X7psi pathLaw
  have := (X7L_S_meas (T := T) h b L k).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi fun i : Fin T => μ i)
  exact this.measurable

end LeviSampling.BaseStock

open MeasureTheory Filter Topology

namespace LeviSampling.BaseStock

theorem X7L_nvint (ν : Measure ℝ) [IsProbabilityMeasure ν] (h b x : ℝ) :
    ∫ y, (-b + (h + b) * (if y ≤ x then (1:ℝ) else 0)) ∂ν = nvRightDeriv ν h b x := by
  have hind : ∀ y : ℝ, -b + (h + b) * (if y ≤ x then (1:ℝ) else 0) =
      -b + Set.indicator (Set.Iic x) (fun _ => h + b) y := by
    intro y; simp [Set.indicator, Set.mem_Iic]
  simp only [hind]
  rw [integral_add (integrable_const _) ((integrable_const _).indicator measurableSet_Iic),
    integral_const, integral_indicator measurableSet_Iic, integral_const]
  simp only [probReal_univ, one_smul, nvRightDeriv, ProbabilityTheory.cdf_eq_real]
  simp [Measure.real, smul_eq_mul]
  ring

theorem X7L_insert_meas {n : ℕ} (jj : Fin (n + 1)) :
    Measurable (fun v : Fin n → ℝ => (Fin.insertNth jj (0:ℝ) v : Fin (n + 1) → ℝ)) := by
  have hm : Measurable (fun v : Fin n → ℝ => ((0:ℝ), v)) := measurable_const.prodMk measurable_id
  have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) jj).symm.measurable.comp hm
  convert this using 1
  funext v
  simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rfl

theorem X7L_intL (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h b L : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    Integrable (fun p => X7S T h b L (k + 1) (extendPath p) (x - extendPath p k))
      (pathLaw T μ) := by
  unfold pathLaw
  refine Integrable.of_bound (C := X7C T h b (k + 1)) ?_ (Eventually.of_forall fun p => ?_)
  · exact ((X7L_S_meas h b L (k + 1)).comp
      ((measurable_const.sub (X7L_meas_ext k)).prodMk measurable_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact X7L_S_bound T h b L (k + 1) _ _

theorem X7L_fub (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h b L : ℕ → ℝ) (k : ℕ) (hk : k < T) (x : ℝ) :
    ∫ p, X7S T h b L (k + 1) (extendPath p) (x - extendPath p k) ∂(pathLaw T μ) =
      ∫ d, X7psi T μ h b L (k + 1) (x - d) ∂(μ k) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  set jj : Fin (n + 1) := ⟨k, hk⟩
  have hint := X7L_intL (n + 1) μ h b L k x
  unfold X7psi
  unfold pathLaw at hint ⊢
  rw [X7L_fubini (fun i : Fin (n + 1) => μ i) jj _ hint]
  have hjj : (jj : ℕ) = k := rfl
  have hL : ∀ v : Fin n → ℝ, ∀ a : ℝ,
      X7S (n + 1) h b L (k + 1) (extendPath (Fin.insertNth jj a v))
        (x - extendPath (Fin.insertNth jj a v) k) =
      X7S (n + 1) h b L (k + 1) (extendPath (Fin.insertNth jj 0 v)) (x - a) := by
    intro v a
    rw [X7L_extend_insert jj a v, hjj, X7L_S_update, Function.update_self]
  simp_rw [hL]
  have hR : ∀ d : ℝ, ∫ p, X7S (n + 1) h b L (k + 1) (extendPath p) (x - d)
      ∂(Measure.pi fun i : Fin (n + 1) => μ i) =
      ∫ v, X7S (n + 1) h b L (k + 1) (extendPath (Fin.insertNth jj 0 v)) (x - d)
        ∂(Measure.pi fun i => μ (jj.succAbove i)) := by
    intro d
    rw [X7L_fubini (fun i : Fin (n + 1) => μ i) jj _ (X7L_S_int _ h b L (k + 1) (x - d))]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have hfun : (fun a : ℝ => X7S (n + 1) h b L (k + 1) (extendPath (Fin.insertNth jj a v)) (x - d))
        = fun _ => X7S (n + 1) h b L (k + 1) (extendPath (Fin.insertNth jj 0 v)) (x - d) := by
      funext a
      rw [X7L_extend_insert jj a v, hjj, X7L_S_update]
    simp only
    rw [hfun, integral_const]
    simp
  simp_rw [hR]
  refine (integral_integral_swap ?_)
  refine Integrable.of_bound (C := X7C (n + 1) h b (k + 1)) ?_ (Eventually.of_forall fun q => ?_)
  · exact ((X7L_S_meas h b L (k + 1)).comp
      ((measurable_const.sub measurable_snd).prodMk
        ((X7L_insert_meas jj).comp measurable_fst))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact X7L_S_bound _ h b L (k + 1) _ _

theorem X7L_psi_succ (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h b L : ℕ → ℝ) (k : ℕ) (hk : k < T) (x : ℝ) :
    X7psi T μ h b L k x = if L k ≤ x then
      nvRightDeriv (μ k) (h k) (b k) x + ∫ d, X7psi T μ h b L (k + 1) (x - d) ∂(μ k) else 0 := by
  rw [← X7L_fub T μ h b L k hk x]
  unfold X7psi
  simp_rw [X7L_S_succ T h b L k hk]
  by_cases h0 : L k ≤ x
  · simp only [h0, if_true]
    have hA : Integrable (fun p : Fin T → ℝ =>
        -b k + (h k + b k) * (if extendPath p k ≤ x then (1:ℝ) else 0)) (pathLaw T μ) := by
      unfold pathLaw
      refine Integrable.of_bound (C := |b k| + |h k + b k|) ?_ (Eventually.of_forall fun p => ?_)
      · refine (measurable_const.add (measurable_const.mul (Measurable.ite ?_ measurable_const
          measurable_const))).aestronglyMeasurable
        exact measurableSet_le (X7L_meas_ext k) measurable_const
      · rw [Real.norm_eq_abs]
        split_ifs
        · calc |-b k + (h k + b k) * 1| ≤ |-b k| + |(h k + b k) * 1| := abs_add_le _ _
            _ = _ := by simp
        · calc |-b k + (h k + b k) * 0| ≤ |-b k| + |(h k + b k) * 0| := abs_add_le _ _
            _ ≤ _ := by simp
    rw [integral_add hA (X7L_intL T μ h b L k x)]
    congr 1
    have he : ∀ p : Fin T → ℝ, extendPath p k = p ⟨k, hk⟩ := by
      intro p; unfold extendPath; rw [dif_pos hk]
    simp_rw [he]
    unfold pathLaw
    have hmeas : AEStronglyMeasurable
        (fun y : ℝ => -b k + (h k + b k) * (if y ≤ x then (1:ℝ) else 0)) (μ k) := by
      refine (measurable_const.add (measurable_const.mul (Measurable.ite ?_ measurable_const
          measurable_const))).aestronglyMeasurable
      exact measurableSet_le measurable_id measurable_const
    have key := integral_comp_eval (X := fun _ : Fin T => ℝ) (μ := fun i : Fin T => μ i)
      (i := (⟨k, hk⟩ : Fin T))
      (f := fun y : ℝ => -b k + (h k + b k) * (if y ≤ x then (1:ℝ) else 0)) hmeas
    exact key.trans (X7L_nvint (μ k) (h k) (b k) x)
  · simp [h0]

theorem X7L_psi_ge (T : ℕ) (μ : ℕ → Measure ℝ) (h b L : ℕ → ℝ) (k : ℕ) (hk : T ≤ k)
    (x : ℝ) : X7psi T μ h b L k x = 0 := by
  unfold X7psi
  simp [X7L_S_ge T h b L k hk]

theorem X7L_prd (T : ℕ) (h b L : ℕ → ℝ) (P : ℕ → ℝ) (t : ℕ) (y : ℝ) :
    pathRightDeriv T h b L P t y =
      (-b t + (h t + b t) * (if P t ≤ y then 1 else 0)) + X7S T h b L (t + 1) P (y - P t) := by
  unfold pathRightDeriv X7S
  congr 1
  have hI : Finset.Ioo t T = Finset.Ico (t + 1) T := by ext; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
  rw [hI]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  unfold pathTerm reachEvent X7term
  have hc : ∀ m, t < m → y - cumDemand P t m = y - P t - cumDemand P (t + 1) m := by
    intro m hm; rw [X7L_cum_succ P t m hm]; ring
  have hiff : (∀ m ∈ Finset.Ioc t j, L m ≤ y - cumDemand P t m) ↔
      (∀ m ∈ Finset.Icc (t + 1) j, L m ≤ y - P t - cumDemand P (t + 1) m) := by
    constructor
    · intro H m hm
      rw [Finset.mem_Icc] at hm
      rw [← hc m (by omega)]; exact H m (by rw [Finset.mem_Ioc]; omega)
    · intro H m hm
      rw [Finset.mem_Ioc] at hm
      rw [hc m (by omega)]; exact H m (by rw [Finset.mem_Icc]; omega)
  rw [hc j (by omega)]
  simp only [hiff]

end LeviSampling.BaseStock

open MeasureTheory Filter Topology

namespace LeviSampling.BaseStock

noncomputable def X7nvf (h b : ℝ) (u : ℝ) : ℝ := h * max u 0 + b * max (-u) 0

noncomputable def X7K (T : ℕ) (h b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico k T, (|h j| + |b j|)

theorem X7L_K_nonneg (T : ℕ) (h b : ℕ → ℝ) (k : ℕ) : 0 ≤ X7K T h b k :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem X7L_nv_eq (ν : Measure ℝ) (h b z : ℝ) :
    nvCost ν h b z = ∫ d, X7nvf h b (z - d) ∂ν := by
  unfold nvCost X7nvf
  simp_rw [neg_sub]

theorem X7L_nvf_lip (h b : ℝ) (a a' : ℝ) :
    |X7nvf h b a - X7nvf h b a'| ≤ (|h| + |b|) * |a - a'| := by
  unfold X7nvf
  have h1 : |max a 0 - max a' 0| ≤ |a - a'| := abs_max_sub_max_le_abs a a' 0
  have h2 : |max (-a) 0 - max (-a') 0| ≤ |a - a'| := by
    have := abs_max_sub_max_le_abs (-a) (-a') 0
    rwa [show -a - -a' = -(a - a') by ring, abs_neg] at this
  calc |h * max a 0 + b * max (-a) 0 - (h * max a' 0 + b * max (-a') 0)|
      = |h * (max a 0 - max a' 0) + b * (max (-a) 0 - max (-a') 0)| := by ring_nf
    _ ≤ |h * (max a 0 - max a' 0)| + |b * (max (-a) 0 - max (-a') 0)| := abs_add_le _ _
    _ = |h| * |max a 0 - max a' 0| + |b| * |max (-a) 0 - max (-a') 0| := by
        rw [abs_mul, abs_mul]
    _ ≤ |h| * |a - a'| + |b| * |a - a'| := by gcongr
    _ = _ := by ring

theorem X7L_nvf_deriv (h b u : ℝ) :
    HasDerivWithinAt (X7nvf h b) (if 0 ≤ u then h else -b) (Set.Ici u) u := by
  by_cases hu : 0 ≤ u
  · rw [if_pos hu]
    have hd : HasDerivWithinAt (fun w => h * w) h (Set.Ici u) u := by
      simpa using ((hasDerivAt_id u).const_mul h).hasDerivWithinAt
    refine hd.congr (fun w hw => ?_) ?_
    · simp only [Set.mem_Ici] at hw
      unfold X7nvf
      rw [max_eq_left (le_trans hu hw), max_eq_right (by linarith)]; ring
    · unfold X7nvf
      rw [max_eq_left hu, max_eq_right (by linarith)]; ring
  · rw [if_neg hu]
    rw [not_le] at hu
    have hd : HasDerivAt (fun w => -b * w) (-b) u := by
      simpa using ((hasDerivAt_id u).const_mul (-b))
    have : X7nvf h b =ᶠ[𝓝 u] fun w => -b * w := by
      filter_upwards [Iio_mem_nhds hu] with w hw
      unfold X7nvf
      rw [max_eq_right (le_of_lt hw), max_eq_left (by simp only [Set.mem_Iio] at hw; linarith)]
      ring
    exact (hd.congr_of_eventuallyEq this).hasDerivWithinAt

theorem X7L_intlip (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable id ν)
    (F : ℝ → ℝ) (K : ℝ) (hK : ∀ a b, |F a - F b| ≤ K * |a - b|) (a a' : ℝ) :
    |∫ d, F (a - d) ∂ν - ∫ d, F (a' - d) ∂ν| ≤ K * |a - a'| := by
  rw [← integral_sub (X7L_lip_int ν hν F K hK a) (X7L_lip_int ν hν F K hK a'),
    ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := K * |a - a'|)
    (Eventually.of_forall fun d => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    have := hK (a - d) (a' - d)
    rwa [show a - d - (a' - d) = a - a' by ring] at this
  · simp

theorem X7L_bs_lt (T : ℕ) (μ : ℕ → Measure ℝ) (h b L : ℕ → ℝ) (k : ℕ) (hk : k < T) (x : ℝ) :
    bsCost T μ h b L k x = nvCost (μ k) (h k) (b k) (max x (L k)) +
      ∫ d, bsCost T μ h b L (k + 1) (max x (L k) - d) ∂(μ k) := by
  rw [bsCost, dif_pos hk]

theorem X7L_bs_ge (T : ℕ) (μ : ℕ → Measure ℝ) (h b L : ℕ → ℝ) (k : ℕ) (hk : ¬ k < T) (x : ℝ) :
    bsCost T μ h b L k x = 0 := by
  rw [bsCost, dif_neg hk]

theorem X7L_bs_lip (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b L : ℕ → ℝ) :
    ∀ n k, T - k = n → ∀ a a', |bsCost T μ h b L k a - bsCost T μ h b L k a'| ≤
      X7K T h b k * |a - a'| := by
  intro n
  induction n with
  | zero =>
    intro k hk a a'
    rw [X7L_bs_ge T μ h b L k (by omega), X7L_bs_ge T μ h b L k (by omega)]
    simp only [sub_self, abs_zero]
    exact mul_nonneg (X7L_K_nonneg T h b k) (abs_nonneg _)
  | succ n ih =>
    intro k hk a a'
    have hkT : k < T := by omega
    have IH := ih (k + 1) (by omega)
    rw [X7L_bs_lt T μ h b L k hkT, X7L_bs_lt T μ h b L k hkT, X7L_nv_eq, X7L_nv_eq]
    have hK : X7K T h b k = (|h k| + |b k|) + X7K T h b (k + 1) := by
      unfold X7K; rw [Finset.sum_eq_sum_Ico_succ_bot hkT]
    have hm : |max a (L k) - max a' (L k)| ≤ |a - a'| := abs_max_sub_max_le_abs a a' (L k)
    have h1 := X7L_intlip (μ k) (hμ k) (X7nvf (h k) (b k)) _ (X7L_nvf_lip (h k) (b k))
      (max a (L k)) (max a' (L k))
    have h2 := X7L_intlip (μ k) (hμ k) (bsCost T μ h b L (k + 1)) _ IH
      (max a (L k)) (max a' (L k))
    have hK0 := X7L_K_nonneg T h b (k + 1)
    calc _ = |(∫ d, X7nvf (h k) (b k) (max a (L k) - d) ∂μ k -
              ∫ d, X7nvf (h k) (b k) (max a' (L k) - d) ∂μ k) +
            (∫ d, bsCost T μ h b L (k + 1) (max a (L k) - d) ∂μ k -
              ∫ d, bsCost T μ h b L (k + 1) (max a' (L k) - d) ∂μ k)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (|h k| + |b k|) * |max a (L k) - max a' (L k)| +
          X7K T h b (k + 1) * |max a (L k) - max a' (L k)| := add_le_add h1 h2
      _ ≤ (|h k| + |b k|) * |a - a'| + X7K T h b (k + 1) * |a - a'| := by gcongr
      _ = _ := by rw [hK]; ring

theorem X7L_G_deriv (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b L : ℕ → ℝ) (k : ℕ) (K : ℝ)
    (hlip : ∀ a a', |bsCost T μ h b L (k + 1) a - bsCost T μ h b L (k + 1) a'| ≤ K * |a - a'|)
    (hder : ∀ u, HasDerivWithinAt (bsCost T μ h b L (k + 1)) (X7psi T μ h b L (k + 1) u)
      (Set.Ici u) u) (z : ℝ) :
    HasDerivWithinAt (fun z => nvCost (μ k) (h k) (b k) z +
        ∫ d, bsCost T μ h b L (k + 1) (z - d) ∂(μ k))
      (nvRightDeriv (μ k) (h k) (b k) z + ∫ d, X7psi T μ h b L (k + 1) (z - d) ∂(μ k))
      (Set.Ici z) z := by
  set F : ℝ → ℝ := fun u => X7nvf (h k) (b k) u + bsCost T μ h b L (k + 1) u with hFdef
  have hFlip : ∀ a a', |F a - F a'| ≤ ((|h k| + |b k|) + K) * |a - a'| := by
    intro a a'
    have h1 := X7L_nvf_lip (h k) (b k) a a'
    have h2 := hlip a a'
    calc |F a - F a'| = |(X7nvf (h k) (b k) a - X7nvf (h k) (b k) a') +
          (bsCost T μ h b L (k + 1) a - bsCost T μ h b L (k + 1) a')| := by
            simp only [hFdef]; ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  have hfun : (fun z => nvCost (μ k) (h k) (b k) z +
        ∫ d, bsCost T μ h b L (k + 1) (z - d) ∂(μ k)) = fun z => ∫ d, F (z - d) ∂(μ k) := by
    funext z
    rw [X7L_nv_eq, ← integral_add (X7L_lip_int (μ k) (hμ k) _ _ (X7L_nvf_lip (h k) (b k)) z)
      (X7L_lip_int (μ k) (hμ k) _ _ hlip z)]
  rw [hfun]
  have hd := X7L_rd (μ k) (hμ k) F
    (fun u => (if 0 ≤ u then h k else -b k) + X7psi T μ h b L (k + 1) u) _ hFlip
    (fun u => (X7L_nvf_deriv (h k) (b k) u).add (hder u)) z
  convert hd using 1
  have hite : ∀ d, (if 0 ≤ z - d then h k else -b k) =
      -b k + (h k + b k) * (if d ≤ z then (1:ℝ) else 0) := by
    intro d
    by_cases hdz : d ≤ z
    · rw [if_pos (by linarith), if_pos hdz]; ring
    · rw [if_neg (by linarith), if_neg hdz]; ring
  simp_rw [hite]
  have hA : Integrable (fun d : ℝ => -b k + (h k + b k) * (if d ≤ z then (1:ℝ) else 0)) (μ k) := by
    refine Integrable.of_bound (C := |b k| + |h k + b k|) ?_ (Eventually.of_forall fun p => ?_)
    · refine (measurable_const.add (measurable_const.mul (Measurable.ite ?_ measurable_const
        measurable_const))).aestronglyMeasurable
      exact measurableSet_le measurable_id measurable_const
    · rw [Real.norm_eq_abs]
      split_ifs
      · calc |-b k + (h k + b k) * 1| ≤ |-b k| + |(h k + b k) * 1| := abs_add_le _ _
          _ = _ := by simp
      · calc |-b k + (h k + b k) * 0| ≤ |-b k| + |(h k + b k) * 0| := abs_add_le _ _
          _ ≤ _ := by simp
  have hB : Integrable (fun d : ℝ => X7psi T μ h b L (k + 1) (z - d)) (μ k) := by
    refine Integrable.of_bound (C := X7C T h b (k + 1)) ?_ (Eventually.of_forall fun p => ?_)
    · exact ((X7L_psi_meas T μ h b L (k + 1)).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact X7L_psi_bound T μ h b L (k + 1) _
  rw [integral_add hA hB, X7L_nvint]

theorem X7L_bs_deriv (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b L : ℕ → ℝ) :
    ∀ n k, T - k = n → ∀ x, HasDerivWithinAt (bsCost T μ h b L k) (X7psi T μ h b L k x)
      (Set.Ici x) x := by
  intro n
  induction n with
  | zero =>
    intro k hk x
    have h0 : bsCost T μ h b L k = fun _ => 0 := funext fun y => X7L_bs_ge T μ h b L k (by omega) y
    rw [h0, X7L_psi_ge T μ h b L k (by omega)]
    exact hasDerivWithinAt_const _ _ _
  | succ n ih =>
    intro k hk x
    have hkT : k < T := by omega
    have IH := ih (k + 1) (by omega)
    have hlip := X7L_bs_lip T μ hμ h b L (T - (k + 1)) (k + 1) rfl
    have hfun : bsCost T μ h b L k = fun x => (fun z => nvCost (μ k) (h k) (b k) z +
        ∫ d, bsCost T μ h b L (k + 1) (z - d) ∂(μ k)) (max x (L k)) :=
      funext fun y => X7L_bs_lt T μ h b L k hkT y
    rw [hfun, X7L_psi_succ T μ h b L k hkT x]
    exact X7L_max _ _ (L k) x (X7L_G_deriv T μ hμ h b L k _ hlip IH x)

end LeviSampling.BaseStock

open MeasureTheory

open LeviSampling.BaseStock in
theorem solution (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i)
    (L : ℕ → ℝ) (t : ℕ) (ht : t < T) (hL : IsUpperBaseStock T μ h b L (t + 1)) (y : ℝ) :
    HasDerivWithinAt (shadowU T μ h b L t)
      (∫ p, pathRightDeriv T h b L (extendPath p) t y ∂(pathLaw T μ)) (Set.Ici y) y := by
  have hlip := X7L_bs_lip T μ hμ h b L (T - (t + 1)) (t + 1) rfl
  have hder := X7L_bs_deriv T μ hμ h b L (T - (t + 1)) (t + 1) rfl
  have hG := X7L_G_deriv T μ hμ h b L t _ hlip hder y
  convert hG using 1
  · rfl
  simp_rw [X7L_prd]
  have hA : Integrable (fun p : Fin T → ℝ =>
      -b t + (h t + b t) * (if extendPath p t ≤ y then (1:ℝ) else 0)) (pathLaw T μ) := by
    unfold pathLaw
    refine Integrable.of_bound (C := |b t| + |h t + b t|) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine (measurable_const.add (measurable_const.mul (Measurable.ite ?_ measurable_const
        measurable_const))).aestronglyMeasurable
      exact measurableSet_le (X7L_meas_ext t) measurable_const
    · rw [Real.norm_eq_abs]
      split_ifs
      · calc |-b t + (h t + b t) * 1| ≤ |-b t| + |(h t + b t) * 1| := abs_add_le _ _
          _ = _ := by simp
      · calc |-b t + (h t + b t) * 0| ≤ |-b t| + |(h t + b t) * 0| := abs_add_le _ _
          _ ≤ _ := by simp
  rw [integral_add hA (X7L_intL T μ h b L t y), X7L_fub T μ h b L t ht y]
  congr 1
  have he : ∀ p : Fin T → ℝ, extendPath p t = p ⟨t, ht⟩ := by
    intro p; unfold extendPath; rw [dif_pos ht]
  simp_rw [he]
  unfold pathLaw
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => -b t + (h t + b t) * (if z ≤ y then (1:ℝ) else 0)) (μ t) := by
    refine (measurable_const.add (measurable_const.mul (Measurable.ite ?_ measurable_const
        measurable_const))).aestronglyMeasurable
    exact measurableSet_le measurable_id measurable_const
  have key := integral_comp_eval (X := fun _ : Fin T => ℝ) (μ := fun i : Fin T => μ i)
    (i := (⟨t, ht⟩ : Fin T))
    (f := fun z : ℝ => -b t + (h t + b t) * (if z ≤ y then (1:ℝ) else 0)) hmeas
  exact key.trans (X7L_nvint (μ t) (h t) (b t) y)
