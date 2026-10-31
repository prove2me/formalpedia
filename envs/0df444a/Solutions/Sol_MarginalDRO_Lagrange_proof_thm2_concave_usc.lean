-- Prove2me | solution 1 for MarginalDRO.Lagrange.proof_thm2_concave_usc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:19:44.397511+00:00
-- url     : https://prove2.me/submissions/0c929d2c-5b63-4260-9682-6c21a1024e4a

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model
import Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_kantorovich

open MeasureTheory ProbabilityTheory Filter Topology
open MarginalDRO.Lagrange

lemma mdro_margMeasure_comb {n : ℕ} (𝒳 : Finset (Fin n → ℝ)) (ν₁ ν₂ : 𝒳 → ℝ)
    (h₁ : ∀ x, 0 ≤ ν₁ x) (h₂ : ∀ x, 0 ≤ ν₂ x) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (i : Fin n) :
    margMeasure 𝒳 (a • ν₁ + b • ν₂) i =
      ENNReal.ofReal a • margMeasure 𝒳 ν₁ i + ENNReal.ofReal b • margMeasure 𝒳 ν₂ i := by
  simp only [margMeasure, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_add (mul_nonneg ha (h₁ x)) (mul_nonneg hb (h₂ x)),
    ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]

theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (i : Fin n) :
    ConcaveOn ℝ (stdSimplex ℝ 𝒳) (fun ν => couplingValue (μ i) (margMeasure 𝒳 ν i)) ∧
      UpperSemicontinuousOn (fun ν => couplingValue (μ i) (margMeasure 𝒳 ν i))
        (stdSimplex ℝ 𝒳) := by
  classical
  rcases 𝒳.eq_empty_or_nonempty with h0 | h𝒳
  · subst h0
    have hemp : stdSimplex ℝ (↥(∅ : Finset (Fin n → ℝ))) = ∅ := by
      ext ν
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hν
      have := hν.2
      simp at this
    rw [hemp]
    exact ⟨⟨convex_empty, fun x hx => absurd hx (Set.notMem_empty x)⟩,
      fun x hx => absurd hx (Set.notMem_empty x)⟩
  have hμ : Integrable id (μ i) := (hvar i).integrable (by norm_num)
  have hK := fun ν hν => proof_thm2_kantorovich μ hvar 𝒳 h𝒳 ν hν i
  -- the coupling value is the attained maximum
  have hcv : ∀ ν ∈ stdSimplex ℝ 𝒳,
      IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ}
        (couplingValue (μ i) (margMeasure 𝒳 ν i)) ∧
      IsGLB (Set.range fun ψ : ℝ → ℝ =>
        ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i))
        (couplingValue (μ i) (margMeasure 𝒳 ν i)) := by
    intro ν hν
    obtain ⟨m, h1, _, h3⟩ := hK ν hν
    have : couplingValue (μ i) (margMeasure 𝒳 ν i) = m := h1.csSup_eq
    rw [this]; exact ⟨h1, h3⟩
  -- integrability of the objective under a coupling with finitely supported second marginal
  have hint : ∀ ν ∈ stdSimplex ℝ 𝒳, ∀ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i),
      Integrable (fun p : ℝ × ℝ => p.1 * p.2) γ := by
    intro ν hν γ hγ
    have h1 : Integrable (fun p : ℝ × ℝ => p.1) γ := by
      have := hμ
      rw [← hγ.2.1] at this
      exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).mp this
    refine h1.mul_bdd (c := ∑ y ∈ 𝒳, |y i|) measurable_snd.aestronglyMeasurable ?_
    have h2 : ∀ᵐ y ∂(γ.map Prod.snd), ‖y‖ ≤ ∑ y ∈ 𝒳, |y i| := by
      rw [hγ.2.2, ae_iff, margMeasure, Measure.finsetSum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Measure.smul_apply, Measure.dirac_apply]
      have : |(x : Fin n → ℝ) i| ≤ ∑ y ∈ 𝒳, |y i| :=
        Finset.single_le_sum (f := fun y : Fin n → ℝ => |y i|) (fun _ _ => abs_nonneg _) x.2
      simp [Real.norm_eq_abs, this]
    exact ae_of_ae_map measurable_snd.aemeasurable h2
  constructor
  · refine ⟨convex_stdSimplex ℝ 𝒳, fun ν₁ hν₁ ν₂ hν₂ a b ha hb hab => ?_⟩
    have hν : a • ν₁ + b • ν₂ ∈ stdSimplex ℝ 𝒳 := convex_stdSimplex ℝ 𝒳 hν₁ hν₂ ha hb hab
    obtain ⟨γ₁, hγ₁, e₁⟩ := (hcv ν₁ hν₁).1.1
    obtain ⟨γ₂, hγ₂, e₂⟩ := (hcv ν₂ hν₂).1.1
    have hP₁ : IsProbabilityMeasure γ₁ := hγ₁.1
    have hP₂ : IsProbabilityMeasure γ₂ := hγ₂.1
    set γ := ENNReal.ofReal a • γ₁ + ENNReal.ofReal b • γ₂ with hγdef
    have hγ : γ ∈ couplings (μ i) (margMeasure 𝒳 (a • ν₁ + b • ν₂) i) := by
      refine ⟨⟨?_⟩, ?_, ?_⟩
      · simp only [γ, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
      · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, hγ₁.2.1,
          hγ₂.2.1, ← add_smul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_smul]
      · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, hγ₁.2.2,
          hγ₂.2.2, mdro_margMeasure_comb 𝒳 ν₁ ν₂ hν₁.1 hν₂.1 a b ha hb i]
    have hval : ∫ p, p.1 * p.2 ∂γ = a * ∫ p, p.1 * p.2 ∂γ₁ + b * ∫ p, p.1 * p.2 ∂γ₂ := by
      rw [integral_add_measure ((hint ν₁ hν₁ γ₁ hγ₁).smul_measure ENNReal.ofReal_ne_top)
        ((hint ν₂ hν₂ γ₂ hγ₂).smul_measure ENNReal.ofReal_ne_top),
        integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha,
        ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]
    have := (hcv _ hν).1.2 ⟨γ, hγ, rfl⟩
    simp only [smul_eq_mul]
    rw [e₁, e₂, ← hval]
    exact this
  · intro ν₀ hν₀ y hy
    obtain ⟨_, ⟨ψ, rfl⟩, -, hlt⟩ := (hcv ν₀ hν₀).2.exists_between hy
    have hcont : Continuous fun ν : 𝒳 → ℝ =>
        ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i) := by
      fun_prop
    have hev := nhdsWithin_le_nhds (s := stdSimplex ℝ 𝒳) ((hcont.tendsto ν₀).eventually (Iio_mem_nhds hlt))
    filter_upwards [hev, self_mem_nhdsWithin] with ν hν hνΔ
    exact lt_of_le_of_lt ((hcv ν hνΔ).2.1 ⟨ψ, rfl⟩) hν
