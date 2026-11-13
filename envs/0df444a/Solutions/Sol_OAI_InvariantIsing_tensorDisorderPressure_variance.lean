-- Prove2me | solution 1 for OAI.InvariantIsing.tensorDisorderPressure_variance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:12:16.485203+00:00
-- url     : https://prove2.me/submissions/2df3ef66-8dbd-4921-9340-0f92fa3720b9

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_haar_tensorEnrichedPressure_variance
import Theorems.Thm_OAI_InvariantIsing_tensorCascadeLog_root_tree_variance_le
import Theorems.Thm_OAI_InvariantIsing_tensorDisorderPressure_conditional_mean

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

theorem variance_of_conditional_center {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : ℝ}
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ C+Var[X; μ] := by
  let D : A × B → ℝ := fun p => F p-X p.1
  have hd : AEStronglyMeasurable D (μ.prod ν) :=
    hF.aestronglyMeasurable.sub (hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := μ) (ν := ν)))
  have hdi : Integrable (fun p => (D p)^2) (μ.prod ν) := by
    apply (integrable_prod_iff (hd.pow 2)).mpr
    refine ⟨ae_of_all _ hi, ?_⟩
    have hnorm : (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) =
        fun a => ∫ b, (D (a,b))^2 ∂ν := by
      ext a
      apply integral_congr_ae
      apply ae_of_all
      intro b
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) μ
    rw [hnorm]
    apply Integrable.of_bound (hd.pow 2).integral_prod_right' C
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => sq_nonneg (D (a,b))))]
    exact hb a
  have hDLp : MemLp D 2 (μ.prod ν) := (memLp_two_iff_integrable_sq hd).mpr hdi
  have hfLp : MemLp F 2 (μ.prod ν) := by
    convert hDLp.add (hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [D]
  refine ⟨hfLp, ?_⟩
  have hsecLp (a : A) : MemLp (fun b => F (a,b)) 2 ν := by
    have hdm : Measurable (fun b => F (a,b)-X a) :=
      (hF.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hL := (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr (hi a)
    convert hL.add (memLp_const (X a)) using 1
    all_goals try with_reducible_and_instances rfl
    ext b
    simp
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    ((integrable_const C).add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hX.integrable_sq,integral_const,
    probReal_univ,one_smul] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral-monomial enriched Ising model. Gaussian marks have a
separate variance at every site/tensor coordinate and every cascade level.
The spectral coefficients retain their actual dependence on the rotation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_spinTensorTerminal_joint {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (SpinTensorIndex I degree → ℝ) =>
      spinTensorTerminal eig (specialRotation p.1) c I degree amplitude p.2) := by
  have hE (σ : Spin N) : Measurable
      (fun p : SpecialOrthogonal N × (SpinTensorIndex I degree → ℝ) =>
        rotatedEnergy eig (specialRotation p.1) σ + fieldEnergy c σ +
          spinTensorEnergy (specialRotation p.1) I degree amplitude p.2 σ) := by
    apply Measurable.add
    · exact ((Finset.measurable_sum _ fun i _ =>
        (((measurable_specialRotation_eval (spinVector σ) i).comp measurable_fst).pow_const 2).const_mul
          (eig i)).const_mul (1 / 2 : ℝ)).add_const _
    · exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp measurable_snd).mul
          ((measurable_spinTensorFeature I degree amplitude σ i).comp measurable_fst)
  unfold spinTensorTerminal logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log

lemma noiseLeafTerminal_spinTensorTerminal {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (leaf : IsingPerceptron.NoiseLeaf (SpinTensorIndex I degree → ℝ) n) :
    IsingPerceptron.noiseLeafTerminal n (fun _ => spinTensorTerminal eig U c I degree amplitude)
      (fun _ p => p.1 + p.2) z leaf =
      spinTensorTerminal eig U c I degree amplitude (tensorLeafState I degree n z leaf) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => exact ih (z + leaf.2.1) leaf.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian-root and cascade fluctuations for the finite tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

/-- For pressure, the Gaussian-root and cascade contributions scale by
the square of the volume. The rotation remains fixed in this statement. -/
theorem normalized_tensorCascadeLog_root_tree_variance_le (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    let root := tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial)
    let P := (root : Measure (SpinTensorIndex I degree → ℝ)).prod (tensorCascadeLaw I degree n b v)
    let F := fun p : (SpinTensorIndex I degree → ℝ) ×
      IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n =>
      tensorCascadeLog eig U c I degree amplitude n p.1 p.2
    MemLp (fun p => (N : ℝ)⁻¹ * F p) 2 P ∧
      variance (fun p => (N : ℝ)⁻¹ * F p) P ≤
        (4 * (∫ T, (Real.log (IsingPerceptron.rawTreeTotal n T).toReal) ^ 2
          ∂(IsingPerceptron.rawCascadeLaw n b : Measure (IsingPerceptron.RawTree n))) +
        (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 := by
  intro root P F
  have h := tensorCascadeLog_root_tree_variance_le hpub hN eig U c I degree amplitude n b v hb site monomial
  refine ⟨h.1.const_mul (N : ℝ)⁻¹, ?_⟩
  rw [variance_const_mul]
  have hbnd := mul_le_mul_of_nonneg_left h.2 (sq_nonneg (N : ℝ)⁻¹)
  convert hbnd using 1
  all_goals try with_reducible_and_instances rfl
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorHaarFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Haar, Gaussian-root, and cascade fluctuations for the actual finite tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma measurable_tensorLeafState {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    Measurable (fun p : (SpinTensorIndex I degree → ℝ) × NoiseLeaf (SpinTensorIndex I degree → ℝ) n =>
      tensorLeafState I degree n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)

lemma measurable_tensorDisorderPressure {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ) :
    Measurable (tensorDisorderPressure eig c I degree amplitude n) := by
  let Ω := SpecialOrthogonal N × ((SpinTensorIndex I degree → ℝ) ×
    NoiseTree (SpinTensorIndex I degree → ℝ) n)
  have hs : Measurable (fun p : Ω × NoiseLeaf (SpinTensorIndex I degree → ℝ) n =>
      (p.1.1, tensorLeafState I degree n p.1.2.1 p.2)) :=
    measurable_fst.fst.prodMk ((measurable_tensorLeafState I degree n).comp
      (measurable_fst.snd.fst.prodMk measurable_snd))
  have ht := ((measurable_spinTensorTerminal_joint eig c I degree amplitude).comp hs).exp
  have hi := (ht.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (noiseLeafKernel (SpinTensorIndex I degree → ℝ) n).comap
      (fun p : Ω => p.2.2) measurable_snd.snd)).measurable.log
  have hlog : Measurable (fun p : Ω => tensorCascadeLog eig (specialRotation p.1) c
      I degree amplitude n p.2.1 p.2.2) := by
    simpa only [tensorCascadeLog, noiseLeafTerminal_spinTensorTerminal, Function.comp_apply,
      Kernel.comap_apply] using hi
  exact hlog.const_mul (N : ℝ)⁻¹

/-- The full pressure variance is the sum of the root/cascade conditional
contribution and the Haar variance of its conditional mean. -/
theorem tensorDisorderPressure_variance_oai (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m k : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ,
    ∀ amplitude : Fin k → ℝ, ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ site : ℕ → ℝ≥0, ∀ monomial : ℕ → Fin k → ℝ≥0,
      let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
      let P := tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0)
      let F := tensorDisorderPressure eig c I degree amplitude n
      let L := K + 2 * (N : ℝ)⁻¹ *
        (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 * ∑ a, (degree j a : ℝ))
      MemLp F 2 (μ.prod P) ∧ variance F (μ.prod P) ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) +
          (site 0 : ℝ) * N + ∑ j, (monomial 0 j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 +
        C * L ^ 2 / N := by
  obtain ⟨C, hC, hHaar⟩ := haar_tensorEnrichedPressure_variance hhaar
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m k eig c K hK heig I degree amplitude n b hb site monomial v P F L
  let : IsProbabilityMeasure μ := hμ
  have hNm : 0 < N := by omega
  let X := fun U : SpecialOrthogonal N => tensorEnrichedPressure eig (specialRotation U) c
    I degree amplitude n b (fun i => v (i + 1)) (v 0)
  have hX := hHaar N hN μ hμ hμinv m k eig c K hK heig I degree amplitude n b hb site monomial
  have hsec (U : SpecialOrthogonal N) : MemLp (fun q => F (U, q)) 2 P ∧
      variance (fun q => F (U, q)) P ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) +
          (site 0 : ℝ) * N + ∑ j, (monomial 0 j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 :=
    normalized_tensorCascadeLog_root_tree_variance_le hgauss hNm eig (specialRotation U) c
      I degree amplitude n b (fun i => v (i + 1)) hb (site 0) (monomial 0)
  have hc (U : SpecialOrthogonal N) : (∫ q, F (U, q) ∂P) = X U :=
    tensorDisorderPressure_conditional_mean hgauss hNm eig c U I degree amplitude n b
      (fun i => v (i + 1)) hb (site 0) (monomial 0)
  have hi (U : SpecialOrthogonal N) : Integrable (fun q => (F (U, q) - X U) ^ 2) P :=
    ((hsec U).1.sub (memLp_const (X U))).integrable_sq
  have hbnd (U : SpecialOrthogonal N) : (∫ q, (F (U, q) - X U) ^ 2 ∂P) ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) +
          (site 0 : ℝ) * N + ∑ j, (monomial 0 j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 := by
    have he := variance_eq_integral (hsec U).1.aemeasurable
    rw [hc U] at he
    rw [← he]
    exact (hsec U).2
  have h := variance_of_conditional_center μ P
    (measurable_tensorDisorderPressure eig c I degree amplitude n) hX.1 hi hc hbnd
  exact ⟨h.1, h.2.trans (add_le_add_right hX.2 _)⟩

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.tensorDisorderPressure_variance_oai := @OAI.InvariantIsing.tensorDisorderPressure_variance_oai
