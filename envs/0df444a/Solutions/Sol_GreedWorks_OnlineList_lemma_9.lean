-- Prove2me | solution 1 for GreedWorks.OnlineList.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:52.144943+00:00
-- url     : https://prove2.me/submissions/e90c1c59-4c82-410c-8292-4faef65bd899

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Classical

noncomputable section

namespace Lemma9Helper

private lemma filter_range_eq_Ico (a p N : ℕ) (hN : a + p ≤ N) :
    (Finset.range N).filter (fun s => a ≤ s ∧ s < a + p) = Finset.Ico a (a + p) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private lemma filter_range_subset_Ico (a p N : ℕ) :
    (Finset.range N).filter (fun s => a ≤ s ∧ s < a + p) ⊆ Finset.Ico a (a + p) := by
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hs ⊢
  exact hs.2

private lemma sum_Ico_one (a p : ℕ) :
    ∑ _s ∈ Finset.Ico a (a + p), (1 : ℝ) = (p : ℝ) := by
  simp

private lemma sum_Ico_slot (a p : ℕ) :
    ∑ s ∈ Finset.Ico a (a + p), ((s : ℝ) + 1 / 2) =
      (p : ℝ) * (a : ℝ) + (p : ℝ) ^ 2 / 2 := by
  induction p with
  | zero =>
    simp
  | succ p ih =>
    have hle : a ≤ a + p := Nat.le_add_right a p
    rw [ ← add_assoc, Finset.sum_Ico_succ_top hle, ih]
    push_cast
    ring

private lemma measurableSet_slot {Ω : Type*} [MeasurableSpace Ω]
    {T P : Ω → ℕ} (hT : Measurable T) (hP : Measurable P) (s : ℕ) :
    MeasurableSet {ω | T ω ≤ s ∧ s < T ω + P ω} :=
  (measurableSet_le hT measurable_const).inter
    (measurableSet_lt measurable_const (hT.add hP))

private def slotInd {Ω : Type*} (T P : Ω → ℕ) (g : ℕ → ℝ) (s : ℕ) (ω : Ω) : ℝ :=
  ({ω' | T ω' ≤ s ∧ s < T ω' + P ω'}).indicator (fun _ => g s) ω

private lemma integrable_slotInd {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {T P : Ω → ℕ} (hT : Measurable T) (hP : Measurable P) (g : ℕ → ℝ) (s : ℕ) :
    Integrable (slotInd T P g s) Pr := by
  unfold slotInd
  rw [integrable_indicator_iff (measurableSet_slot hT hP s)]
  exact integrableOn_const (measure_ne_top Pr _)

private lemma integral_slotInd {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {T P : Ω → ℕ} (hT : Measurable T) (hP : Measurable P) (g : ℕ → ℝ) (s : ℕ) :
    ∫ ω, slotInd T P g s ω ∂Pr =
      g s * (Pr {ω | T ω ≤ s ∧ s < T ω + P ω}).toReal := by
  unfold slotInd
  rw [integral_indicator_const (g s) (measurableSet_slot hT hP s), smul_eq_mul, mul_comm]
  rfl

private lemma sum_range_slotInd_eq {Ω : Type*} (T P : Ω → ℕ) (g : ℕ → ℝ) (N : ℕ) (ω : Ω) :
    ∑ s ∈ Finset.range N, slotInd T P g s ω =
      ∑ s ∈ (Finset.range N).filter (fun s => T ω ≤ s ∧ s < T ω + P ω), g s := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  unfold slotInd
  by_cases h : T ω ≤ s ∧ s < T ω + P ω
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

private lemma hasSum_slot_weight {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {T P : Ω → ℕ} (hT : Measurable T) (hP : Measurable P)
    (g : ℕ → ℝ) (hg : ∀ s, 0 ≤ g s)
    (F : Ω → ℝ) (hF_eq : ∀ ω, F ω = ∑ s ∈ Finset.Ico (T ω) (T ω + P ω), g s)
    (hF_int : Integrable F Pr) :
    HasSum (fun s : ℕ => g s * (Pr {ω | T ω ≤ s ∧ s < T ω + P ω}).toReal)
      (∫ ω, F ω ∂Pr) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun s => mul_nonneg (hg s) ENNReal.toReal_nonneg)]
  let FN : ℕ → Ω → ℝ := fun N ω => ∑ s ∈ Finset.range N, slotInd T P g s ω
  have hFN_int : ∀ N, ∑ s ∈ Finset.range N, g s * (Pr {ω | T ω ≤ s ∧ s < T ω + P ω}).toReal =
      ∫ ω, FN N ω ∂Pr := by
    intro N
    unfold FN
    rw [integral_finsetSum _ (fun s _ => integrable_slotInd Pr hT hP g s)]
    refine Finset.sum_congr rfl (fun s _ => (integral_slotInd Pr hT hP g s).symm)
  simp_rw [hFN_int]
  refine tendsto_integral_of_dominated_convergence F
    (fun N => (integrable_finsetSum (Finset.range N) (fun s _ =>
      integrable_slotInd Pr hT hP g s)).aestronglyMeasurable)
    hF_int ?_ ?_
  · intro N
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hnonneg : 0 ≤ FN N ω := by
      unfold FN
      rw [sum_range_slotInd_eq]
      exact Finset.sum_nonneg (fun s _ => hg s)
    have hle : FN N ω ≤ F ω := by
      unfold FN
      rw [sum_range_slotInd_eq, hF_eq ω]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (filter_range_subset_Ico (T ω) (P ω) N) (fun s _ _ => hg s)
    rw [Real.norm_of_nonneg hnonneg]
    exact hle
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    refine tendsto_atTop_of_eventually_const (i₀ := T ω + P ω) (fun N hN => ?_)
    unfold FN
    rw [sum_range_slotInd_eq, hF_eq ω, filter_range_eq_Ico (T ω) (P ω) N hN]

end Lemma9Helper

open Lemma9Helper

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (T P : Ω → ℕ) (hT : Measurable T) (hP : Measurable P)
    (hPpos : ∀ ω, 1 ≤ P ω)
    (hP2 : MemLp (fun ω => (P ω : ℝ)) 2 Pr)
    (hTint : Integrable (fun ω => (T ω : ℝ)) Pr)
    (hIndep : IndepFun T P Pr) :
    let μ : ℝ := ∫ ω, (P ω : ℝ) ∂Pr
    let cv2 : ℝ := variance (fun ω => (P ω : ℝ)) Pr / μ ^ 2
    let y : ℕ → ℝ := fun s => (Pr {ω | T ω ≤ s ∧ s < T ω + P ω}).toReal
    HasSum (fun s : ℕ =>
      y s / μ * ((s : ℝ) + 1 / 2) + (1 - cv2) / 2 * y s)
      (∫ ω, ((T ω + P ω : ℕ) : ℝ) ∂Pr) := by
  intro μ cv2 y
  have hPint : Integrable (fun ω => (P ω : ℝ)) Pr := hP2.integrable one_le_two
  have hμ_ge_one : 1 ≤ μ := by
    have h1 : (∫ _ : Ω, (1 : ℝ) ∂Pr) ≤ ∫ ω, (P ω : ℝ) ∂Pr := by
      refine integral_mono_ae (integrable_const 1) hPint
        (Filter.Eventually.of_forall (fun ω => ?_))
      change (1 : ℝ) ≤ (P ω : ℝ)
      exact_mod_cast hPpos ω
    simpa [μ] using h1
  have hμ_pos : 0 < μ := by linarith
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
  have h_sum1 : HasSum (fun s : ℕ => 1 * y s) μ := by
    refine hasSum_slot_weight Pr hT hP (fun _ => 1) (fun _ => zero_le_one)
      (fun ω => (P ω : ℝ)) (fun ω => (sum_Ico_one (T ω) (P ω)).symm) hPint
  have hIndepR : IndepFun (fun ω => (T ω : ℝ)) (fun ω => (P ω : ℝ)) Pr :=
    hIndep.comp measurable_from_top measurable_from_top
  have hPT_int : Integrable (fun ω => (P ω : ℝ) * (T ω : ℝ)) Pr :=
    hIndepR.symm.integrable_mul hPint hTint
  have hPT_integral : ∫ ω, (P ω : ℝ) * (T ω : ℝ) ∂Pr = μ * ∫ ω, (T ω : ℝ) ∂Pr :=
    hIndepR.symm.integral_mul_eq_mul_integral hPint.aestronglyMeasurable hTint.aestronglyMeasurable
  have hPsq_int : Integrable (fun ω => (P ω : ℝ) ^ 2) Pr := hP2.integrable_sq
  have hvar : variance (fun ω => (P ω : ℝ)) Pr =
      (∫ ω, (P ω : ℝ) ^ 2 ∂Pr) - μ ^ 2 := by
    rw [variance_eq_integral hP2.aemeasurable]
    have h_expand : (fun ω : Ω => ((P ω : ℝ) - ∫ x, (P x : ℝ) ∂Pr) ^ 2) =
        (fun ω : Ω => (P ω : ℝ) ^ 2 - (2 * μ * (P ω : ℝ) - μ ^ 2)) := by
      ext ω
      change ((P ω : ℝ) - μ) ^ 2 = (P ω : ℝ) ^ 2 - (2 * μ * (P ω : ℝ) - μ ^ 2)
      ring
    have h_sub_int : Integrable (fun ω : Ω => 2 * μ * (P ω : ℝ) - μ ^ 2) Pr :=
      (hPint.const_mul (2 * μ)).sub (integrable_const (μ ^ 2))
    rw [h_expand, integral_sub hPsq_int h_sub_int,
      integral_sub (hPint.const_mul (2 * μ)) (integrable_const (μ ^ 2)),
      integral_const_mul, integral_const]
    have huniv : Pr.real Set.univ = 1 := by simp [Measure.real]
    rw [smul_eq_mul, huniv, one_mul]
    change (∫ ω, (P ω : ℝ) ^ 2 ∂Pr) - (2 * μ * μ - μ ^ 2) = (∫ ω, (P ω : ℝ) ^ 2 ∂Pr) - μ ^ 2
    ring
  have hF2_int : Integrable (fun ω => (P ω : ℝ) * (T ω : ℝ) + (P ω : ℝ) ^ 2 / 2) Pr :=
    hPT_int.add (hPsq_int.div_const 2)
  have h_sum2 : HasSum (fun s : ℕ => ((s : ℝ) + 1 / 2) * y s)
      (∫ ω, ((P ω : ℝ) * (T ω : ℝ) + (P ω : ℝ) ^ 2 / 2) ∂Pr) := by
    refine hasSum_slot_weight Pr hT hP (fun s => (s : ℝ) + 1 / 2) (fun s => by positivity)
      (fun ω => (P ω : ℝ) * (T ω : ℝ) + (P ω : ℝ) ^ 2 / 2)
      (fun ω => (sum_Ico_slot (T ω) (P ω)).symm) hF2_int
  have hF2_eval : ∫ ω, ((P ω : ℝ) * (T ω : ℝ) + (P ω : ℝ) ^ 2 / 2) ∂Pr =
      μ * (∫ ω, (T ω : ℝ) ∂Pr) + (variance (fun ω => (P ω : ℝ)) Pr + μ ^ 2) / 2 := by
    rw [integral_add hPT_int (hPsq_int.div_const 2), integral_div, hPT_integral, hvar]
    ring
  rw [hF2_eval] at h_sum2
  have h_comb := (h_sum2.mul_left (1 / μ)).add (h_sum1.mul_left ((1 - cv2) / 2))
  have h_fun_eq : (fun s : ℕ => 1 / μ * (((s : ℝ) + 1 / 2) * y s) + (1 - cv2) / 2 * (1 * y s)) =
      (fun s : ℕ => y s / μ * ((s : ℝ) + 1 / 2) + (1 - cv2) / 2 * y s) := by
    ext s; ring
  have h_val_eq : 1 / μ * (μ * (∫ ω, (T ω : ℝ) ∂Pr) + (variance (fun ω => (P ω : ℝ)) Pr + μ ^ 2) / 2) +
        (1 - cv2) / 2 * μ =
      ∫ ω, ((T ω + P ω : ℕ) : ℝ) ∂Pr := by
    have h_int_add : ∫ ω, ((T ω + P ω : ℕ) : ℝ) ∂Pr = (∫ ω, (T ω : ℝ) ∂Pr) + μ := by
      have hcast : (fun ω => ((T ω + P ω : ℕ) : ℝ)) = (fun ω => (T ω : ℝ) + (P ω : ℝ)) := by
        ext ω; push_cast; rfl
      rw [hcast, integral_add hTint hPint]
    rw [h_int_add]
    change 1 / μ * (μ * (∫ ω, (T ω : ℝ) ∂Pr) + (variance (fun ω => (P ω : ℝ)) Pr + μ ^ 2) / 2) +
        (1 - variance (fun ω => (P ω : ℝ)) Pr / μ ^ 2) / 2 * μ =
      (∫ ω, (T ω : ℝ) ∂Pr) + μ
    field_simp [hμ_ne]
    ring
  rwa [h_fun_eq, h_val_eq] at h_comb
