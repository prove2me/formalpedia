-- Prove2me | solution 1 for Kyprianou.Ch05.markedPositiveCrossingAmbientMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:39:45.474468+00:00
-- url     : https://prove2.me/submissions/45b3cf59-e477-485c-b3ed-977d2beab06c

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_predictableMarkedPositiveCrossingKernelV1
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (F : Filtration NNReal inferInstance)
    (V : NNReal → Omega → ℝ) (hV : Measurable[F.predictable] (Function.uncurry V))
    (eta x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let psi := fun (s z : ℝ) (w : Omega) =>
      if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
        x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
        x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
    Measurable (fun p : Omega × (ℝ × ℝ) => psi p.2.1 p.2.2 p.1) := by
  classical
  dsimp only
  let psi := fun (s z : ℝ) (w : Omega) =>
    if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
      x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
      x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
  let g (w : Omega) (z : ℝ × ℝ) := psi z.1 z.2 w
  have hpred := predictableMarkedPositiveCrossingKernelV1 F V hV eta x A B hA hB
  have hamb : Measurable (fun p : (NNReal × Omega) × ℝ =>
      psi (p.1.1 : ℝ) p.2 p.1.2) :=
    hpred.mono (Kyprianou.Ch04.markedPredictableLeAmbientProduct F) le_rfl
  have hg : Measurable (Function.uncurry g) := by
    have h := hamb.comp (((measurable_real_toNNReal.comp
      (measurable_fst.comp measurable_snd)).prodMk measurable_fst).prodMk
      (measurable_snd.comp measurable_snd) :
        Measurable (fun p : Omega × (ℝ × ℝ) => ((p.2.1.toNNReal,p.1),p.2.2)))
    have he : Function.uncurry g = fun p : Omega × (ℝ × ℝ) =>
        psi (p.2.1.toNNReal : ℝ) p.2.2 p.1 := by
      funext p
      change psi p.2.1 p.2.2 p.1 = psi (p.2.1.toNNReal : ℝ) p.2.2 p.1
      by_cases hp : 0 < p.2.1
      · simp [g,psi,Real.coe_toNNReal _ hp.le]
      · simp [g,psi,Real.toNNReal_eq_zero.mpr (le_of_not_gt hp),hp]
    rw [he]
    exact h
  exact hg
