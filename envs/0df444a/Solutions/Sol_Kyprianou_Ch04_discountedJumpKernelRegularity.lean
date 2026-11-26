-- Prove2me | solution 1 for Kyprianou.Ch04.discountedJumpKernelRegularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:47:54.340876+00:00
-- url     : https://prove2.me/submissions/7a7b31bf-d9a1-449d-b732-6adf74a619d5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_leftLimitRealClockTendsto
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Discounted jump differences of the adapted left-limit process are regular marked kernels. -/
theorem solution {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X L : NNReal → Omega → ℝ) (f : ℝ → ℝ) (hf : Continuous f) (lam : ℝ)
    (hm : Measurable (fun z : ℝ × Omega => L z.1.toNNReal z.2))
    (ha : ∀ t : NNReal, Measurable[F t] (L t))
    (hp : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => if z.2 ∈ Set.Icc (0 : ℝ) (t : ℝ)
        then L z.2.toNNReal z.1 else 0))
    (hl : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s w) (nhdsWithin t (Iio t)) (nhds (L t w))) :
    let k := fun s x w => Real.exp (-lam*s) * (f (L s.toNNReal w+x)-f (L s.toNNReal w))
    Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2) ∧
    (∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => k (t : ℝ) z.2 z.1)) ∧
    (∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => k s x w) (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
        (nhds (k (t : ℝ) x w))) ∧
    (∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)) := by
  have hL : Measurable (fun z : (ℝ × ℝ) × Omega => L z.1.1.toNNReal z.2) :=
    hm.comp (measurable_fst.fst.prodMk measurable_snd)
  refine ⟨?_,?_,?_,?_⟩
  · exact (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst.fst)).mul
      ((hf.measurable.comp (hL.add measurable_fst.snd)).sub (hf.measurable.comp hL))
  · intro t
    simp only [Real.toNNReal_coe]
    have ht := (ha t).comp (measurable_fst :
      Measurable[(F t).prod inferInstance, F t] (Prod.fst : Omega × ℝ → Omega))
    exact measurable_const.mul
      ((hf.measurable.comp (ht.add measurable_snd)).sub (hf.measurable.comp ht))
  · filter_upwards [hl] with w hw
    intro x t ht
    have hL' := leftLimitRealClockTendsto (fun u => X u w) (fun u => L u w) hw t ht
    have hex : Tendsto (fun s : ℝ => Real.exp (-lam*s)) (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
        (nhds (Real.exp (-lam*(t : ℝ)))) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    simpa only [Real.toNNReal_coe,Function.comp_apply] using hex.mul
      ((hf.continuousAt.tendsto.comp (hL'.add tendsto_const_nhds)).sub
        (hf.continuousAt.tendsto.comp hL'))
  · intro t
    let a := fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then L z.2.1.toNNReal z.1 else 0
    have ha' : Measurable[(F t).prod inferInstance] a :=
      (hp t).comp (measurable_fst.prodMk measurable_snd.fst)
    have hb : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
        Real.exp (-lam*z.2.1)*(f (a z+z.2.2)-f (a z))) :=
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_snd.fst)).mul
        ((hf.measurable.comp (ha'.add measurable_snd.snd)).sub (hf.measurable.comp ha'))
    have hh : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then
          Real.exp (-lam*z.2.1)*(f (a z+z.2.2)-f (a z)) else 0) :=
      Measurable.ite (measurable_snd.fst measurableSet_Icc) hb measurable_const
    convert hh using 1
    ext z
    by_cases hz : z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ)
    · simp only [a,if_pos hz]
    · simp only [if_neg hz]
