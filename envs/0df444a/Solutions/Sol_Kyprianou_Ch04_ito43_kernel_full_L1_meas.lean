-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_kernel_full_L1_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:47:41.133785+00:00
-- url     : https://prove2.me/submissions/46e7a298-6923-4ee0-919c-66662a917269

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Each full-cell error is a measurable parameter integral. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    let B : ℕ → Omega → ℝ := fun n w =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      (∑ k ∈ Finset.range n,
      (∫ s in Icc ((u k : NNReal) : ℝ) ((u (k+1) : NNReal) : ℝ),
        |g (s,X (Real.toNNReal s) w) - g (s,X (u (k+1)) w)|))
    ∀ n, Measurable (B n) := by
  intro B n
  let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
  have hg0 : Continuous (fun z : ℝ × ℝ => g (max 0 z.1,z.2)) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max 0 z.1 from le_max_left _ _,mem_univ _⟩)
  change Measurable (fun w => ∑ k ∈ Finset.range n,
    (∫ s in Icc (u k : ℝ) (u (k+1) : ℝ),
      |g (s,X (Real.toNNReal s) w) - g (s,X (u (k+1)) w)|))
  apply Finset.measurable_fun_sum
  intro k hk
  let F : Omega × ℝ → ℝ := fun z =>
    |g (max 0 z.2,X (Real.toNNReal z.2) z.1) - g (max 0 z.2,X (u (k+1)) z.1)|
  have h1 : Measurable (fun z : Omega × ℝ => X (Real.toNNReal z.2) z.1) :=
    hX.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have h2 : Measurable (fun z : Omega × ℝ => X (u (k+1)) z.1) :=
    hX.comp (measurable_const.prodMk measurable_fst)
  have hF : Measurable F :=
    ((hg0.measurable.comp (measurable_snd.prodMk h1)).sub
      (hg0.measurable.comp (measurable_snd.prodMk h2))).abs
  have hI := (hF.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc (u k : ℝ) (u (k+1) : ℝ)))).measurable
  convert hI using 1
  ext w
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have h0 : 0 ≤ s := (u k).coe_nonneg.trans hs.1
  simp [F,max_eq_right h0]
