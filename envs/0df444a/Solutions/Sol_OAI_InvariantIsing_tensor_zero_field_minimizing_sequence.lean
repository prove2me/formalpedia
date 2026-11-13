-- Prove2me | solution 1 for OAI.InvariantIsing.tensor_zero_field_minimizing_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:14:30.920829+00:00
-- url     : https://prove2.me/submissions/922f5c2c-191d-4f0e-846b-6d348613137b

import Mathlib
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_tensorPerturbationPressureMean_modulus

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorObjectiveContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and existence of genuine finite perturbation minima. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology NNReal ENNReal

namespace InvariantIsing

lemma continuous_tensorPerturbationPressureMean (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Continuous (fun p : (Fin N → ℝ) × (Fin m → ℝ) =>
      tensorPerturbationPressureMean μ eig c I p.1 p.2 t n b h) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let M := fun z : (Fin N → ℝ) × (Fin m → ℝ) =>
    2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
      (tensorPerturbationAmplitude N z.1) (tensorPerturbationAmplitude N p.1) +
      perturbationScale N * ∑ a, |z.2 a - p.2 a|
  have hc : Continuous M := by
    unfold M tensorAmplitudeModulus tensorPerturbationAmplitude
    fun_prop
  have hz : M p = 0 := by simp [M, tensorAmplitudeModulus]
  have ht : Tendsto M (𝓝 p) (𝓝 0) := by simpa only [hz] using hc.tendsto p
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs, M] using tensorPerturbationPressureMean_modulus
      hhaar hgauss hN μ hμ eig c I t n b hb h hh h0 z.1 p.1 z.2 p.2) ht


lemma continuous_tensorPerturbationObjective (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Continuous (fun p : (Fin N → ℝ) × (Fin m → ℝ) =>
      tensorPerturbationObjective μ eig c I t n b h p.1 p.2) := by
  have hM := continuous_tensorPerturbationPressureMean hhaar hgauss hN μ hμ eig c I t n b hb h hh h0
  unfold tensorPerturbationObjective
  exact (hM.neg.add (by fun_prop)).add (by fun_prop)

private lemma finiteBox_minimum {N m : ℕ}
    (F : (Fin N → ℝ) × (Fin m → ℝ) → ℝ) (hF : Continuous F) :
    ∃ u : Fin N → ℝ, ∃ v : Fin m → ℝ,
      (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        F (u,v) ≤ F (u',v') := by
  let B := (Fin N → Set.Icc (1 : ℝ) 2) × (Fin m → Set.Icc (1 : ℝ) 2)
  let g : B → (Fin N → ℝ) × (Fin m → ℝ) := fun p => (fun j => p.1 j, fun a => p.2 a)
  have hg : Continuous g := by
    exact (continuous_pi fun j => continuous_subtype_val.comp
      ((continuous_apply j).comp continuous_fst)).prodMk
      (continuous_pi fun a => continuous_subtype_val.comp ((continuous_apply a).comp continuous_snd))
  let p₀ : B := (fun _ => ⟨1, by norm_num⟩, fun _ => ⟨1, by norm_num⟩)
  obtain ⟨p, _, hp⟩ := (isCompact_univ : IsCompact (Set.univ : Set B)).exists_isMinOn
    ⟨p₀, Set.mem_univ _⟩ (hF.comp hg).continuousOn
  refine ⟨fun j => p.1 j, fun a => p.2 a, fun j => (p.1 j).property,
    fun a => (p.2 a).property, ?_⟩
  intro u' v' hu' hv'
  exact hp (Set.mem_univ ((fun j => ⟨u' j, hu' j⟩, fun a => ⟨v' a, hv' a⟩) : B))

/-- The minimizers required by the GG/contact estimates exist for the actual
finite objective on the manuscript's compact perturbation box. -/
theorem tensorPerturbationObjective_exists_minimum (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ∃ u : Fin N → ℝ, ∃ v : Fin m → ℝ,
      (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective μ eig c I t n b h u v ≤
          tensorPerturbationObjective μ eig c I t n b h u' v' := by
  exact finiteBox_minimum
    (fun p => tensorPerturbationObjective μ eig c I t n b h p.1 p.2)
    (continuous_tensorPerturbationObjective hhaar hgauss hN μ hμ eig c I t n b hb h hh h0)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorMinimumSequence
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the actual pressure minimizers simultaneously at all positive
physical sizes. This keeps one deterministic sequence for telescoping. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem tensor_zero_field_minimizing_sequence_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N)) :
    ∃ u : (N : ℕ) → Fin N → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ N j, u N j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ N a, v N a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ N, 3≤N → ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
          (fun _ => 0) (u N) (v N) ≤
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v' := by
  have hex N : ∃ u : Fin N → ℝ, ∃ v : Fin m → ℝ,
      (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ (_hN : 3≤N) u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
          (fun _ => 0) u v ≤
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v' := by
    by_cases hN : 3≤N
    · obtain ⟨u,v,hu,hv,hm⟩ := tensorPerturbationObjective_exists_minimum hhaar hgauss hN
        (μ N) (hμ N) (eig N) (c N) (I N) 1 depth b hb (fun _ => 0) monotone_const le_rfl
      exact ⟨u,v,hu,hv,fun _ => hm⟩
    · exact ⟨fun _ => 3/2,fun _ => 3/2,fun _ => by norm_num,
        fun _ => by norm_num,fun h => (hN h).elim⟩
  choose u v hu hv hm using hex
  exact ⟨u,v,hu,hv,hm⟩

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.tensor_zero_field_minimizing_sequence_oai := @OAI.InvariantIsing.tensor_zero_field_minimizing_sequence_oai
