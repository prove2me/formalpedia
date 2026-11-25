-- Prove2me | solution 1 for ManyServerQED.Scheduling.joint_weak_limit_of_independent_finite_family
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T21:10:17.601735+00:00
-- url     : https://prove2.me/submissions/d2f7f777-cc98-445b-ac9f-83d9b8e6ff93

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology WithLp
open scoped ENNReal

theorem solution {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {k : ℕ} (X : Fin k → ℕ → Ω → E) (Z : Fin k → Ω' → E)
    (hX : ∀ i, TendstoInDistribution (X i) atTop (Z i) (fun _ => P) P')
    (hInd : ∀ᶠ n in atTop, iIndepFun (fun i => X i n) P) (hZ : iIndepFun Z P') :
    TendstoInDistribution (fun n ω i => X i n ω) atTop (fun ω i => Z i ω) (fun _ => P) P' := by
  let V := PiLp 2 (fun _ : Fin k => E)
  let Y (n : ℕ) (ω : Ω) : V := toLp 2 (fun i => X i n ω)
  let y (ω : Ω') : V := toLp 2 (fun i => Z i ω)
  have hm (n : ℕ) : AEMeasurable (Y n) P := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin k => E)).measurable.comp_aemeasurable (aemeasurable_pi_lambda _ (fun i => (hX i).forall_aemeasurable n))
  have hy : AEMeasurable y P' := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin k => E)).measurable.comp_aemeasurable (aemeasurable_pi_lambda _ (fun i => (hX i).aemeasurable_limit))
  have ht : TendstoInDistribution Y atTop y (fun _ => P) P' := by
    refine ⟨hm,hy,?_⟩
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
    intro t
    have hc (i : Fin k) := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 (hX i).tendsto) (t i)
    have hp : Tendsto (fun n => ∏ i, charFun (P.map (X i n)) (t i)) atTop
      (𝓝 (∏ i, charFun (P'.map (Z i)) (t i))) := by
      apply tendsto_finsetProd
      intro i hi
      exact hc i
    have hrel : ∀ᶠ n in atTop, charFun (P.map (Y n)) t = ∏ i, charFun (P.map (X i n)) (t i) := by
      filter_upwards [hInd] with n hn
      exact (iIndepFun_iff_charFun_pi (fun i => (hX i).forall_aemeasurable n)).1 hn t
    have hrel' : charFun (P'.map y) t = ∏ i, charFun (P'.map (Z i)) (t i) :=
      (iIndepFun_iff_charFun_pi (fun i => (hX i).aemeasurable_limit)).1 hZ t
    change Tendsto (fun n => charFun (P.map (Y n)) t) _ (𝓝 (charFun (P'.map y) t))
    rw [hrel']
    exact hp.congr' (hrel.mono fun n hn => hn.symm)
  exact ht.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin k => E))
