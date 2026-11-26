-- Prove2me | solution 1 for ManyServerQED.Scheduling.finite_family_independent_continuous_brownian
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:47:09.091958+00:00
-- url     : https://prove2.me/submissions/9dbaf35e-4a7c-43b9-b18b-289bab13a863

import Mathlib
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem solution (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : Fin d → ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ j, IsBrownianReal (W j) P) ∧
      (∀ j ω, Continuous fun t => W j t ω) ∧
      (∀ j t, Measurable (W j t)) ∧
      iIndepFun (fun j ω (t : ℝ≥0) => W j t ω) P := by
  obtain ⟨B,hBm,hEq,hHol⟩ := isPreBrownianReal_preBrownian.exists_continuous_modification
  have hb : (0:ℝ≥0) < (1/8:ℝ≥0) := by norm_num
  have hlo : ((1/8:ℝ≥0):ℝ) <
      ⨆ n : ℕ, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) := by
    have hbd : BddAbove (Set.range (fun n : ℕ =>
        (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)))) := by
      refine ⟨1,?_⟩
      rintro _ ⟨n,rfl⟩
      apply (div_le_one (by positivity)).2
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    refine lt_of_lt_of_le ?_ (le_ciSup hbd 0)
    norm_num
  have hBc (ω : ℝ≥0 → ℝ) : Continuous (fun t => B t ω) := by
    apply continuous_iff_continuousAt.2
    intro t
    obtain ⟨U,hU,C,hC⟩ := hHol ω t (1/8) hb hlo
    have ht : t ∈ U := mem_of_mem_nhds hU
    exact (hC.continuousOn hb t ht).continuousAt hU
  let A := ℝ≥0 → ℝ
  let Ω := Fin d → A
  let P : Measure Ω := Measure.pi (fun _ => gaussianLimit)
  let W (j : Fin d) (t : ℝ≥0) (ω : Ω) := B t (ω j)
  have hBase : IsPreBrownianReal B gaussianLimit :=
    isPreBrownianReal_preBrownian.congr (fun t => (hEq t).symm)
  refine ⟨Ω, inferInstance, P, W, inferInstance, ?_, (fun j ω => hBc (ω j)), ?_, ?_⟩
  · intro j
    refine ⟨⟨fun I => ?_⟩,ae_of_all _ (fun ω => hBc (ω j))⟩
    exact (hBase.hasLaw I).comp (measurePreserving_eval (fun _ : Fin d => gaussianLimit) j).hasLaw
  · exact fun j t => (hBm t).comp (measurable_pi_apply j)
  · have hi : iIndepFun (fun (j : Fin d) (ω : Ω) => ω j) P := iIndepFun_pi (fun _ => aemeasurable_id)
    exact hi.comp (fun _ ω (t : ℝ≥0) => B t ω) (fun _ => measurable_pi_lambda _ hBm)
