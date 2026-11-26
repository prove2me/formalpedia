-- Prove2me | solution 1 for Kyprianou.Ch05.predictableMarkedPositiveCrossingKernelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:56:40.387798+00:00
-- url     : https://prove2.me/submissions/c4cf5044-89c8-460d-9ac3-6e17e2eceaa5

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_predictableTimeCoordinateV1
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
    Measurable[F.predictable.prod inferInstance]
      (fun p : (NNReal × Omega) × ℝ => psi (p.1.1 : ℝ) p.2 p.1.2) := by
  classical
  dsimp only
  let m := F.predictable.prod (inferInstance : MeasurableSpace ℝ)
  have ht : Measurable[m] (fun p : (NNReal × Omega) × ℝ => (p.1.1 : ℝ)) :=
    measurable_coe_nnreal_real.comp ((predictableTimeCoordinateV1 F).comp measurable_fst)
  have hv : Measurable[m] (fun p : (NNReal × Omega) × ℝ => V p.1.1 p.1.2) :=
    hV.comp measurable_fst
  have hz : Measurable[m] (Prod.snd : (NNReal × Omega) × ℝ → ℝ) := measurable_snd
  have hb := hv.const_sub x
  have hc := hz.sub hb
  have hset : MeasurableSet[m] {p : (NNReal × Omega) × ℝ |
      0 < (p.1.1 : ℝ) ∧ V p.1.1 p.1.2 ∈ Icc (0 : ℝ) x ∧
        x - V p.1.1 p.1.2 < p.2 ∧ p.2-(x-V p.1.1 p.1.2) ∈ A ∧
        x-V p.1.1 p.1.2 ∈ B} :=
    (measurableSet_lt measurable_const ht).inter
      ((measurableSet_Icc.preimage hv).inter ((measurableSet_lt hb hz).inter
        ((hA.preimage hc).inter (hB.preimage hb))))
  have hdisc := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (ht.const_mul (-eta)))
  simp only [Real.toNNReal_coe]
  exact Measurable.ite hset hdisc measurable_const
