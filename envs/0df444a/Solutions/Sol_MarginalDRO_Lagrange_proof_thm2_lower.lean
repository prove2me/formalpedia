-- Prove2me | solution 1 for MarginalDRO.Lagrange.proof_thm2_lower
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:59:18.925157+00:00
-- url     : https://prove2.me/submissions/7ee60393-9b8e-4985-b36f-554cbdc3880c

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory
open MarginalDRO.Lagrange

theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ν : 𝒳 → ℝ) (hν : ν ∈ stdSimplex ℝ 𝒳) (γ : Fin n → Measure (ℝ × ℝ))
    (hγ : ∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) :
    ∃ θ ∈ frechetClass μ, ∑ i, ∫ p, p.1 * p.2 ∂(γ i) ≤ ∫ c, Z 𝒳 h𝒳 c ∂θ := by
  classical
  have hγP : ∀ i, IsProbabilityMeasure (γ i) := fun i => (hγ i).1
  set γ' : Fin n → Measure (ℝ × ℝ) := fun i => (γ i).map Prod.swap with hγ'
  have hγ'P : ∀ i, IsProbabilityMeasure (γ' i) := fun i =>
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  set κ : Fin n → Kernel ℝ ℝ := fun i => (γ' i).condKernel with hκ
  have hfst : ∀ i, (γ' i).fst = margMeasure 𝒳 ν i := by
    intro i
    rw [Measure.fst, hγ', Measure.map_map measurable_fst measurable_swap]
    exact (hγ i).2.2
  have hdis : ∀ i, (γ' i).fst ⊗ₘ κ i = γ' i := fun i => Measure.disintegrate _ _
  have hν0 : ∀ x, 0 ≤ ν x := hν.1
  -- (F1) mixture representation of μ i
  have hμ : ∀ i, μ i = ∑ x : 𝒳, ENNReal.ofReal (ν x) • κ i ((x : Fin n → ℝ) i) := by
    intro i
    have h1 : μ i = (γ' i).snd := by
      rw [Measure.snd, hγ', Measure.map_map measurable_snd measurable_swap]
      exact (hγ i).2.1.symm
    rw [h1, ← hdis i, Measure.snd_compProd, hfst]
    ext s hs
    rw [Measure.bind_apply hs (κ i).aemeasurable, margMeasure, lintegral_finset_sum_measure,
      Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lintegral_smul_measure, lintegral_dirac, Measure.smul_apply, smul_eq_mul]
  -- integrability of the coupling objective
  have hμint : ∀ i, Integrable id (μ i) := fun i => (hvar i).integrable (by norm_num)
  set B : Fin n → ℝ := fun i => ∑ y ∈ 𝒳, |y i| with hB
  have hxB : ∀ i, ∀ x ∈ 𝒳, |x i| ≤ B i := fun i x hx =>
    Finset.single_le_sum (f := fun y : Fin n → ℝ => |y i|) (fun y _ => abs_nonneg _) hx
  have hγint : ∀ i, Integrable (fun p : ℝ × ℝ => p.1 * p.2) (γ i) := by
    intro i
    have h1 : Integrable (fun p : ℝ × ℝ => p.1) (γ i) := by
      have := hμint i
      rw [← (hγ i).2.1] at this
      exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).mp this
    refine h1.mul_bdd (c := B i) measurable_snd.aestronglyMeasurable ?_
    have h2 : ∀ᵐ y ∂((γ i).map Prod.snd), ‖y‖ ≤ B i := by
      rw [(hγ i).2.2, ae_iff, margMeasure, Measure.finsetSum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Measure.smul_apply, Measure.dirac_apply]
      have : |(x : Fin n → ℝ) i| ≤ B i := hxB i x x.2
      simp [Real.norm_eq_abs, this]
    exact ae_of_ae_map measurable_snd.aemeasurable h2
  -- (F2) the coupling value through the disintegration
  have hval : ∀ i, ∫ p, p.1 * p.2 ∂(γ i) =
      ∑ x : 𝒳, ν x * ((x : Fin n → ℝ) i * ∫ c, c ∂(κ i ((x : Fin n → ℝ) i))) := by
    intro i
    have h1 : ∫ p, p.1 * p.2 ∂(γ i) = ∫ q, q.2 * q.1 ∂(γ' i) := by
      rw [show γ' i = (γ i).map Prod.swap from rfl,
        integral_map (f := fun q : ℝ × ℝ => q.2 * q.1) measurable_swap.aemeasurable
        (continuous_snd.mul continuous_fst).aestronglyMeasurable]
      rfl
    have hint' : Integrable (fun q : ℝ × ℝ => q.2 * q.1) (γ' i) := by
      rw [show γ' i = (γ i).map Prod.swap from rfl]
      exact (integrable_map_measure (continuous_snd.mul continuous_fst).aestronglyMeasurable
        measurable_swap.aemeasurable).mpr (hγint i)
    rw [h1, ← hdis i] at *
    rw [Measure.integral_compProd hint', hfst, margMeasure, integral_finset_sum_measure]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hν0 x), smul_eq_mul,
        integral_mul_const, mul_comm (∫ c, c ∂(κ i ((x : Fin n → ℝ) i)))]
    · intro x _
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  -- (F3) integrability of the conditional laws charged by ν
  have hκint : ∀ i, ∀ x : 𝒳, ν x ≠ 0 → Integrable id (κ i ((x : Fin n → ℝ) i)) := by
    intro i x hx
    have hle : ENNReal.ofReal (ν x) • κ i ((x : Fin n → ℝ) i) ≤ μ i := by
      rw [hμ i]
      intro s
      rw [Measure.coe_finset_sum, Finset.sum_apply]
      exact Finset.single_le_sum (f := fun y : 𝒳 => (ENNReal.ofReal (ν y) • κ i ((y : Fin n → ℝ) i)) s)
        (fun _ _ => zero_le) (Finset.mem_univ x)
    have h1 := ((hμint i).mono_measure hle).smul_measure (c := (ENNReal.ofReal (ν x))⁻¹)
      (ENNReal.inv_ne_top.mpr (by
        rw [ENNReal.ofReal_ne_zero_iff]; exact lt_of_le_of_ne (hν0 x) (Ne.symm hx)))
    rwa [smul_smul, ENNReal.inv_mul_cancel (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact lt_of_le_of_ne (hν0 x) (Ne.symm hx))
      ENNReal.ofReal_ne_top, one_smul] at h1
  -- the joint law
  set P : 𝒳 → Measure (Fin n → ℝ) := fun x => Measure.pi (fun i => κ i ((x : Fin n → ℝ) i)) with hP
  have hPP : ∀ x, IsProbabilityMeasure (P x) := fun x => by rw [hP]; infer_instance
  set θ : Measure (Fin n → ℝ) := ∑ x : 𝒳, ENNReal.ofReal (ν x) • P x with hθ
  have hPmap : ∀ x : 𝒳, ∀ i, (P x).map (fun c => c i) = κ i ((x : Fin n → ℝ) i) := by
    intro x i
    have := Measure.pi_map_eval (μ := fun i => κ i ((x : Fin n → ℝ) i)) i
    simp only [measure_univ, Finset.prod_const_one, one_smul] at this
    exact this
  refine ⟨θ, ⟨?_, ?_⟩, ?_⟩
  · constructor
    rw [hθ, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hν0 x), hν.2, ENNReal.ofReal_one]
  · intro i
    rw [hμ i]
    ext s hs
    rw [Measure.map_apply (measurable_pi_apply i) hs, hθ, Measure.finsetSum_apply,
      Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Measure.smul_apply, Measure.smul_apply, ← hPmap x i,
      Measure.map_apply (measurable_pi_apply i) hs]
  · have hZm : Measurable (fun c => Z 𝒳 h𝒳 c) := by
      have : (fun c => Z 𝒳 h𝒳 c) = 𝒳.sup' h𝒳 (fun y (c : Fin n → ℝ) => ∑ i, c i * y i) := by
        funext c; simp [Z, Finset.sup'_apply]
      rw [this]
      exact Finset.measurable_sup' h𝒳 fun y _ => by fun_prop
    have hcint : ∀ x : 𝒳, ν x ≠ 0 → ∀ i, Integrable (fun c : Fin n → ℝ => c i) (P x) := by
      intro x hx i
      have := hκint i x hx
      rw [← hPmap x i] at this
      exact (integrable_map_measure aestronglyMeasurable_id
        (measurable_pi_apply i).aemeasurable).mp this
    have hZint : ∀ x : 𝒳, ν x ≠ 0 → Integrable (fun c => Z 𝒳 h𝒳 c) (P x) := by
      intro x hx
      refine Integrable.mono' (g := fun c : Fin n → ℝ => ∑ i, B i * |c i|)
        (integrable_finset_sum _ fun i _ => (hcint x hx i).abs.const_mul (B i))
        hZm.aestronglyMeasurable (Filter.Eventually.of_forall fun c => ?_)
      obtain ⟨y, hy, hZy⟩ := Finset.exists_mem_eq_sup' h𝒳 (fun y : Fin n → ℝ => ∑ i, c i * y i)
      rw [Real.norm_eq_abs, Z, hZy]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hxB i y hy) (abs_nonneg _)
    rw [Finset.sum_congr rfl (fun i _ => hval i), Finset.sum_comm, hθ,
      integral_finset_sum_measure]
    · refine Finset.sum_le_sum fun x _ => ?_
      rw [integral_smul_measure, ENNReal.toReal_ofReal (hν0 x), smul_eq_mul, ← Finset.mul_sum]
      by_cases hx : ν x = 0
      · simp [hx]
      refine mul_le_mul_of_nonneg_left ?_ (hν0 x)
      have h1 : ∀ i, (x : Fin n → ℝ) i * ∫ c, c ∂(κ i ((x : Fin n → ℝ) i)) =
          ∫ c, c i * (x : Fin n → ℝ) i ∂(P x) := by
        intro i
        have hm : Measurable (fun c : Fin n → ℝ => c i) := measurable_pi_apply i
        rw [← hPmap x i, integral_map (f := fun c : ℝ => c) hm.aemeasurable
          aestronglyMeasurable_id, integral_mul_const, mul_comm]
      rw [Finset.sum_congr rfl (fun i _ => h1 i), ← integral_finset_sum _
        (fun i _ => (hcint x hx i).mul_const _)]
      refine integral_mono (integrable_finset_sum _ fun i _ => (hcint x hx i).mul_const _)
        (hZint x hx) fun c => ?_
      exact Finset.le_sup' (fun y : Fin n → ℝ => ∑ i, c i * y i) x.2
    · intro x _
      by_cases hx : ν x = 0
      · simp [hx]
      · exact (hZint x hx).smul_measure ENNReal.ofReal_ne_top
