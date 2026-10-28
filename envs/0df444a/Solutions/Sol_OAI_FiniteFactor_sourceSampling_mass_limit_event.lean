-- Prove2me | solution 1 for OAI.FiniteFactor.sourceSampling_mass_limit_event
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:46:37.623987+00:00
-- url     : https://prove2.me/submissions/91977bc9-cd0d-47be-9ceb-96990d98bbd0

import Mathlib
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceSamplingLambda_rectangle_limit_event

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Measures
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

theorem sourceSamplingHaar_cube : ∀ᵐ x ∂sourceSamplingHaar,
    ∀ i : SourceCoordinate, x i ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have hh : ∀ᵐ t ∂sourceSamplingHaar.map (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact ae_restrict_mem measurableSet_Ico
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TestedTransport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

theorem sourceSamplingRectangle_measurable (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    MeasurableSet (sourceSamplingRectangle E G) := by
  simp only [sourceSamplingRectangle,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact ((hE i).preimage ((measurable_pi_apply i).comp measurable_fst)).inter
    ((hG i).preimage ((measurable_pi_apply i).comp measurable_snd))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LimitMeasure
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingLimitMap_measurable (I : Finset SourceCoordinate) :
    Measurable (sourceSamplingLimitMap I) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval (fun i => measurable_fst.comp (measurable_pi_apply i))
  · apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ I
    · simpa only [hi,ite_true,Function.comp_def] using measurable_snd.comp (measurable_pi_apply i)
    · simpa only [hi,ite_false,Function.comp_def] using measurable_fst.comp (measurable_pi_apply i)

theorem sourceSamplingPairHaar_cube : ∀ᵐ p ∂sourceSamplingPairHaar,
    ∀ i, (p i).1 ∈ Set.Ico (0 : ℝ) 1 ∧ (p i).2 ∈ Set.Ico (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  have hp : ∀ᵐ z ∂unitIntervalMeasure.prod unitIntervalMeasure,
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ Set.Ico (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ico.prod measurableSet_Ico)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    exact ⟨hx,hy⟩
  have hh : ∀ᵐ z ∂sourceSamplingPairHaar.map (fun p => p i),
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact hp
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Cube
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingCube_measurable : MeasurableSet sourceSamplingCube := by
  exact sourceSamplingRectangle_measurable _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)

theorem sourceSamplingSummand_cube (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    ∀ᵐ p ∂sourceSamplingSummand I s θ n, p ∈ sourceSamplingCube := by
  apply (ae_map_iff (measurable_id.prodMk (coordinateRotate_preserving θ n).measurable).aemeasurable
    sourceSamplingCube_measurable).mpr
  have hh : ∀ᵐ x ∂sourceSamplingWeightedMeasure I s θ n, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 :=
    ae_iff.mpr (withDensity_absolutelyContinuous _ _ (ae_iff.mp sourceSamplingHaar_cube))
  filter_upwards [hh] with x hx
  intro i
  exact ⟨⟨(hx i).1,(hx i).2.le⟩,Int.fract_nonneg _,(Int.fract_lt_one _).le⟩

theorem sourceSamplingUntrimmed_cube (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) :
    ∀ᵐ p ∂sourceSamplingUntrimmed I s θ, p ∈ sourceSamplingCube := by
  apply Measure.ae_smul_measure
  rw [ae_iff, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  exact ae_iff.mp (sourceSamplingSummand_cube I s θ n)

theorem sourceSamplingLambda_cube (I : Finset SourceCoordinate) :
    ∀ᵐ p ∂sourceSamplingLambda I, p ∈ sourceSamplingCube := by
  apply (ae_map_iff (sourceSamplingLimitMap_measurable I).aemeasurable
    sourceSamplingCube_measurable).mpr
  filter_upwards [ae_restrict_of_ae sourceSamplingPairHaar_cube] with p hp
  intro i
  refine ⟨⟨(hp i).1.1,(hp i).1.2.le⟩,?_⟩
  by_cases hi : i ∈ I
  · simpa [sourceSamplingLimitMap,hi] using And.intro (hp i).2.1 (hp i).2.2.le
  · simpa [sourceSamplingLimitMap,hi] using And.intro (hp i).1.1 (hp i).1.2.le

theorem sourceSamplingEmptyTest_rectangle :
    sourceSamplingRectangle (sourceSamplingRationalX sourceSamplingEmptyTest)
      (sourceSamplingRationalY sourceSamplingEmptyTest) = sourceSamplingCube := by
  ext p
  simp [sourceSamplingRectangle,sourceSamplingRationalX,sourceSamplingRationalY,
    sourceSamplingRationalEndpoints,sourceSamplingEmptyTest,sourceSamplingCube]

/-- The empty rational test gives actual total-mass convergence. -/
theorem sourceSampling_mass_limit_event_oai : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) Set.univ).toReal)
        atTop (𝓝 (((sourceSamplingLambda I) Set.univ).toReal)) := by
  filter_upwards [sourceSamplingLambda_rectangle_limit_event] with θ hθ
  intro I
  have h := hθ I sourceSamplingEmptyTest
  rw [sourceSamplingEmptyTest_rectangle] at h
  have hu (s : ℕ) : sourceSamplingUntrimmed I s θ sourceSamplingCube =
      sourceSamplingUntrimmed I s θ Set.univ :=
    measure_congr (by filter_upwards [sourceSamplingUntrimmed_cube I s θ] with p hp; exact propext (iff_true_intro hp))
  have hl : sourceSamplingLambda I sourceSamplingCube = sourceSamplingLambda I Set.univ :=
    measure_congr (by filter_upwards [sourceSamplingLambda_cube I] with p hp; exact propext (iff_true_intro hp))
  simpa only [hu,hl] using h

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceSampling_mass_limit_event_oai := @OAI.FiniteFactor.sourceSampling_mass_limit_event_oai
