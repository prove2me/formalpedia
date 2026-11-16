-- Prove2me | solution 1 for Kyprianou.Ch01.gammaStrictMonoFromLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:59:47.686371+00:00
-- url     : https://prove2.me/submissions/733dc480-8087-48f0-941b-efd9f3c446f9

import Mathlib
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_gammaPositiveIncrementAE
import Theorems.Thm_Kyprianou_Ch01_strictMono_of_dense_rightContinuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Promote almost-sure fixed-pair gamma increment positivity on a countable
    dense time set into almost-sure strict increase at every physical time. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (hAlpha : 0 < alpha) (hBeta : 0 < beta)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hGammaLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ))) :
    ∀ᵐ ω ∂P, StrictMono (fun t : ℝ≥0 => X t ω) := by
  obtain ⟨S, hScount, hSdense⟩ :=
    TopologicalSpace.exists_countable_dense ℝ≥0
  letI : Countable S := hScount.to_subtype
  have hpair (s t : S) :
      ∀ᵐ ω ∂P, (s : ℝ≥0) < (t : ℝ≥0) → X s ω < X t ω := by
    by_cases hst : (s : ℝ≥0) < (t : ℝ≥0)
    · filter_upwards [Kyprianou.Ch01.gammaPositiveIncrementAE
        P X alpha beta hAlpha hBeta hX hGammaLaplace s t hst] with ω hw
      exact fun _ => hw
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hst h))
  have hgridAE :
      ∀ᵐ ω ∂P, ∀ s : S, ∀ t : S,
        (s : ℝ≥0) < (t : ℝ≥0) → X s ω < X t ω :=
    (ae_all_iff).2 fun s => (ae_all_iff).2 fun t => hpair s t
  filter_upwards [hgridAE, hX.cadlag_ae] with ω hgrid hcadlag
  have hcont : ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Ici t) t :=
    fun t => (hcadlag t).1
  apply Kyprianou.Ch01.strictMono_of_dense_rightContinuity
    (fun t : ℝ≥0 => X t ω) hcont S hSdense
  intro s hs t ht hst
  exact hgrid ⟨s, hs⟩ ⟨t, ht⟩ hst
