-- Prove2me | solution 1 for InfoRelaxTS.Asymptotic.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:34:56.471876+00:00
-- url     : https://prove2.me/submissions/527312d0-ca36-4f5c-9e0e-1e94498b9ac0

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open InfoRelaxTS InfoRelaxTS.Asymptotic

theorem solution {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y)
    (hint : ∀ a, Integrable (fun r : ℝ => r) ((R a) ∘ₘ (P a (y a)))) :
    (∀ a, Integrable (fun θ => Monotone.mu R a θ) (P a (y a))) ∧
      Integrable (fun θ : Fin K → Θ => Finset.univ.sup' Finset.univ_nonempty fun a => Monotone.mu R a (θ a))
        (priorLaw P y) := by
  have hmeas : ∀ a, Measurable (Monotone.mu R a) := fun a =>
    (StronglyMeasurable.integral_kernel (κ := R a) (f := fun r : ℝ => r)
      stronglyMeasurable_id).measurable
  have h1 : ∀ a, Integrable (fun θ => Monotone.mu R a θ) (P a (y a)) := by
    intro a
    have h := ((Measure.integrable_comp_iff (hint a).1).1 (hint a)).2
    refine h.mono (hmeas a).aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
    exact (norm_integral_le_integral_norm _).trans (le_abs_self _)
  refine ⟨h1, ?_⟩
  have h2 : ∀ a, Integrable (fun θ : Fin K → Θ => Monotone.mu R a (θ a)) (priorLaw P y) := by
    intro a
    have hmp := measurePreserving_eval (μ := fun a => P a (y a)) a
    have : Integrable (Monotone.mu R a) ((priorLaw P y).map (Function.eval a)) := by
      unfold priorLaw; rw [hmp.map_eq]; exact h1 a
    exact this.comp_measurable (measurable_pi_apply a)
  have hsum := integrable_finsetSum Finset.univ (fun a _ => (h2 a).abs)
  refine hsum.mono ?_ (Eventually.of_forall fun θ => ?_)
  · have := Finset.measurable_sup' Finset.univ_nonempty
      (fun a _ => (hmeas a).comp (measurable_pi_apply (X := fun _ : Fin K => Θ) a))
    refine Measurable.aestronglyMeasurable ?_
    convert this using 1
    ext θ
    rw [Finset.sup'_apply]
    rfl
  · rw [Real.norm_eq_abs, Real.norm_eq_abs]
    obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a => Monotone.mu R a (θ a))
    rw [hb]
    calc |Monotone.mu R b (θ b)| ≤ ∑ a, |Monotone.mu R a (θ a)| :=
          Finset.single_le_sum (f := fun a => |Monotone.mu R a (θ a)|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
      _ ≤ abs (∑ a, |Monotone.mu R a (θ a)|) := le_abs_self _
