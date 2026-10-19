-- Prove2me | solution 1 for OAI.NoiselessRegression.FiniteKernelLearner.subquadratic_memory
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:39:23.521432+00:00
-- url     : https://prove2.me/submissions/8aa75848-396c-485f-87c0-aa3697713be4

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Seeded.lean:L220-L231
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.FiniteKernelLearner.subquadratic_memory. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
import Definitions.Def_OAI_Probability_ProjectionMoments_Seeded
import Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_exists_equivalent_tape
import Theorems.Thm_OAI_NoiselessRegression_subquadratic_memory

-- ---- from OAI.Probability.ProjectionMoments.Seeded ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner

section
open Learner
variable {d M T : ℕ}

end

universe u
variable {d M T : ℕ}

lemma seed_average_bound {Ξ : Type u} [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] {f : Ξ → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ᵐ ξ ∂ρ, f ξ ≤ C) : ∫⁻ ξ, f ξ ∂ρ ≤ C := by
  calc
    _ ≤ ∫⁻ _, C ∂ρ := lintegral_mono_ae h
    _ = C := by simp

lemma exists_successful_seed {Ξ : Type u} [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] {P : Ξ → Prop} (hP : ∀ᵐ ξ ∂ρ, P ξ)
    {f : Ξ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (hs : c ≤ ∫⁻ ξ, f ξ ∂ρ) :
    ∃ ξ, P ξ ∧ c ≤ f ξ := by
  by_contra h
  have hlt : ∀ᵐ ξ ∂ρ, f ξ < c := by
    filter_upwards [hP] with ξ hξ
    exact lt_of_not_ge (fun hf => h ⟨ξ,hξ,hf⟩)
  have hbound : ∫⁻ ξ, f ξ ∂ρ ≤ c := seed_average_bound ρ (ae_le_of_ae_lt hlt)
  have hstrict := lintegral_strict_mono (show ρ ≠ 0 from by
    intro he; have hh := measure_univ (μ := ρ); rw [he] at hh; simp at hh)
    (aemeasurable_const (b := c)) (ne_top_of_le_ne_top hc hbound) hlt
  have hh : ∫⁻ ξ, f ξ ∂ρ < c := by simpa using hstrict
  exact not_lt_of_ge hs hh

theorem subquadratic_memory : SubquadraticMemory.{u} := by
  obtain ⟨c,hc,h⟩ := NoiselessRegression.subquadratic_memory.{0}
  refine ⟨c,hc,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := h M hM
  refine ⟨max d₀ 3,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK hs
  let : IsProbabilityMeasure ρ := hρ
  obtain ⟨ξ,hξ,hsξ⟩ := exists_successful_seed ρ hK (ENNReal.div_ne_top (by norm_num) (by norm_num) : (2/3 : ℝ≥0∞) ≠ ∞) hs
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  apply hd₀ d (by omega) T ε hε hε10 (Tape (M d) T) ν hν L hL
  exact Or.inl ((he ε).symm ▸ hsξ)

end FiniteKernelLearner

end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution.{u} : type_of% @_root_.OAI.NoiselessRegression.FiniteKernelLearner.subquadratic_memory.{u} := @_root_.OAI.NoiselessRegression.FiniteKernelLearner.subquadratic_memory.{u}
