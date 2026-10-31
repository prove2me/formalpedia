-- Prove2me | solution 1 for MarginalDRO.Lagrange.proof_thm2_upper
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:54:54.898781+00:00
-- url     : https://prove2.me/submissions/b7f77abb-cef3-4c3f-8cc5-28bd6cb1e813

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory
open MarginalDRO.Lagrange

lemma mdro_eq_sum_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (m : Measure α) (S : Finset α) (h : m (↑S)ᶜ = 0) :
    m = ∑ x ∈ S, m {x} • Measure.dirac x := by
  classical
  ext s hs
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  rw [← measure_inter_conull (s := s) h]
  have : s ∩ (↑S : Set α) = ↑(S.filter (· ∈ s)) := by
    ext x; simp [and_comm]
  rw [this, ← sum_measure_singleton, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ s <;> simp [hx]

theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (θ : Measure (Fin n → ℝ)) (hθ : θ ∈ frechetClass μ)
    (xstar : (Fin n → ℝ) → (Fin n → ℝ)) (hxm : Measurable xstar)
    (hxmem : ∀ c, xstar c ∈ 𝒳) (hxopt : ∀ c, ∀ x ∈ 𝒳, ∑ i, c i * x i ≤ ∑ i, c i * xstar c i) :
    (fun x : 𝒳 => (θ.map xstar {(x : Fin n → ℝ)}).toReal) ∈ stdSimplex ℝ 𝒳 ∧
      (∀ i, θ.map (fun c => (c i, xstar c i)) ∈
        couplings (μ i) (margMeasure 𝒳 (fun x : 𝒳 => (θ.map xstar {(x : Fin n → ℝ)}).toReal) i)) ∧
      ∫ c, Z 𝒳 h𝒳 c ∂θ = ∑ i, ∫ p, p.1 * p.2 ∂(θ.map (fun c => (c i, xstar c i))) := by
  classical
  obtain ⟨hθP, hθm⟩ := hθ
  set m := θ.map xstar with hm
  have : IsProbabilityMeasure m := Measure.isProbabilityMeasure_map hxm.aemeasurable
  have hcompl : m (↑𝒳)ᶜ = 0 := by
    rw [hm, Measure.map_apply hxm (Finset.measurableSet _).compl]
    have : xstar ⁻¹' (↑𝒳 : Set (Fin n → ℝ))ᶜ = ∅ := by
      ext c; simp [hxmem c]
    rw [this, measure_empty]
  have hdecomp := mdro_eq_sum_dirac m 𝒳 hcompl
  have hsum : ∑ x ∈ 𝒳, m {x} = 1 := by
    rw [sum_measure_singleton, ← Set.univ_inter (↑𝒳 : Set (Fin n → ℝ)),
      measure_inter_conull hcompl]
    simp
  have hfin : ∀ x, m {x} ≠ ⊤ := fun x => measure_ne_top m _
  refine ⟨⟨fun x => ENNReal.toReal_nonneg, ?_⟩, ?_, ?_⟩
  · rw [Finset.sum_coe_sort 𝒳 (fun x => (m {x}).toReal), ← ENNReal.toReal_sum (fun x _ => hfin x),
      hsum, ENNReal.toReal_one]
  · intro i
    have hf : Measurable (fun c : Fin n → ℝ => (c i, xstar c i)) :=
      (measurable_pi_apply i).prodMk ((measurable_pi_apply i).comp hxm)
    refine ⟨Measure.isProbabilityMeasure_map hf.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hf]
      exact hθm i
    · rw [Measure.map_map measurable_snd hf]
      have : (Prod.snd ∘ fun c : Fin n → ℝ => (c i, xstar c i)) = (fun y => y i) ∘ xstar := rfl
      rw [this, ← Measure.map_map (measurable_pi_apply i) hxm, ← hm]
      ext s hs
      rw [Measure.map_apply (measurable_pi_apply i) hs, hdecomp, Measure.finsetSum_apply,
        margMeasure, Measure.finsetSum_apply]
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_toReal (hfin _)]
      rw [← Finset.sum_coe_sort 𝒳]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Measure.dirac_apply' _ ((measurable_pi_apply i) hs), Measure.dirac_apply' _ hs]
      simp [Set.indicator_apply]
  · have hZ : ∀ c, Z 𝒳 h𝒳 c = ∑ i, c i * xstar c i := fun c =>
      le_antisymm (Finset.sup'_le _ _ (hxopt c)) (Finset.le_sup' (fun x => ∑ i, c i * x i) (hxmem c))
    have hint : ∀ i, Integrable (fun c : Fin n → ℝ => c i * xstar c i) θ := by
      intro i
      have hμi : Integrable id (μ i) := (hvar i).integrable (by norm_num)
      rw [← hθm i] at hμi
      have hci : Integrable (fun c : Fin n → ℝ => c i) θ :=
        (integrable_map_measure aestronglyMeasurable_id
          (measurable_pi_apply i).aemeasurable).mp hμi
      refine hci.mul_bdd (c := ∑ x ∈ 𝒳, |x i|)
        ((measurable_pi_apply i).comp hxm).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
      intro c
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun x : Fin n → ℝ => |x i|) (fun x _ => abs_nonneg _)
        (hxmem c)
    simp_rw [hZ]
    rw [integral_finset_sum _ (fun i _ => hint i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hf : Measurable (fun c : Fin n → ℝ => (c i, xstar c i)) :=
      (measurable_pi_apply i).prodMk ((measurable_pi_apply i).comp hxm)
    rw [integral_map (f := fun p : ℝ × ℝ => p.1 * p.2) hf.aemeasurable
      (continuous_fst.mul continuous_snd).aestronglyMeasurable]
