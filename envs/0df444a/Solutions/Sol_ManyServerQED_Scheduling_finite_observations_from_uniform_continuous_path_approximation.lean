-- Prove2me | solution 1 for ManyServerQED.Scheduling.finite_observations_from_uniform_continuous_path_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:33:44.59735+00:00
-- url     : https://prove2.me/submissions/bcc32a80-53c8-4fd8-a116-a42e9c8ac660

import Mathlib
import Definitions.Def_DurrettProbability_Donsker

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open DurrettProbability

/-- Finite-dimensional convergence of real observations approximated by a moving
time evaluation of weakly converging continuous paths. -/
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P')
    {m : ℕ} (d : ℕ → Fin m → ℝ) (e : Fin m → ℝ)
    (hd : Tendsto d atTop (𝓝 e)) (c : ℝ)
    (Q : ℕ → Ω → Fin m → ℝ) (hQ : ∀ n, AEMeasurable (Q n) P)
    (hA : ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ i : Fin m,
      ε ≤ |Q n ω i - c*Y n ω (Set.projIcc 0 1 zero_le_one (d n i))|}) atTop (𝓝 0)) :
    TendstoInDistribution Q atTop
      (fun ω i => c * Z ω (Set.projIcc 0 1 zero_le_one (e i))) (fun _ => P) P' := by
  have hdIn : TendstoInMeasure P (fun n (_ : Ω) => d n) atTop (fun _ => e) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ (fun _ => hd))
  let f (z : PathSpace × (Fin m → ℝ)) (i : Fin m) :=
    c*z.1 (Set.projIcc 0 1 zero_le_one (z.2 i))
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply Continuous.const_mul
    have hg : Continuous (fun z : PathSpace × (Fin m → ℝ) =>
        Set.projIcc (0:ℝ) 1 zero_le_one (z.2 i)) :=
      continuous_projIcc.comp ((continuous_apply i).comp continuous_snd)
    exact continuous_eval.comp (continuous_fst.prodMk hg)
  let I (n : ℕ) (ω : Ω) := f (Y n ω,d n)
  have hIZ : TendstoInDistribution I atTop
      (fun ω i => c * Z ω (Set.projIcc 0 1 zero_le_one (e i))) (fun _ => P) P' :=
    hY.continuous_comp_prodMk_of_tendstoInMeasure_const hf hdIn
      (fun _ => measurable_const.aemeasurable)
  refine tendstoInDistribution_of_tendstoInMeasure_sub Q _ hIZ ?_ hQ
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hA ε hε)
    (Eventually.of_forall (fun _ => zero_le)) (Eventually.of_forall fun n => measure_mono ?_)
  intro ω hω
  have hnot : ¬∀ i, ‖Q n ω i - I n ω i‖ < ε := by
    intro hh
    have he : ‖(Q - I) n ω - (0 : Ω → Fin m → ℝ) ω‖ < ε := by
      apply (pi_norm_lt_iff hε).2
      simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using hh
    exact (not_le_of_gt he) hω
  push Not at hnot
  obtain ⟨i,hi⟩ := hnot
  exact ⟨i,by simpa only [Real.norm_eq_abs] using hi⟩
