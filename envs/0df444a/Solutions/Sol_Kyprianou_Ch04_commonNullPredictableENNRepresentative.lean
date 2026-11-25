-- Prove2me | solution 1 for Kyprianou.Ch04.commonNullPredictableENNRepresentative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:55:03.256119+00:00
-- url     : https://prove2.me/submissions/d41c6d67-0b91-414b-8b19-c9d94898a5fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_predictableLeftGridClock
import Theorems.Thm_Kyprianou_Ch04_predictableENNGridSampling
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega))) :
    ∃ psi : Real → Real → Omega → ENNReal,
      Measurable[F.predictable.prod inferInstance]
        (fun z : (NNReal × Omega) × Real => psi (z.1.1 : Real) z.2 z.1.2) ∧
      (∀ᵐ omega ∂P, ∀ s x : Real, psi s x omega = ENNReal.ofReal (phi s x omega)) := by
  classical
  obtain ⟨q, a, b, h0, hcell, hcover, hleft⟩ := predictableLeftGridClock
  let G : Nat → ((NNReal × Omega) × Real) → ENNReal := fun n z =>
    ENNReal.ofReal (phi (q n z.1.1 : Real) z.2 z.1.2)
  have hG : ∀ n, Measurable[F.predictable.prod inferInstance] (G n) := fun n =>
    predictableENNGridSampling F phi hPhi.2.2.1 (q n) (a n) (b n)
      (h0 n) (hcell n) (hcover n)
  let L : ((NNReal × Omega) × Real) → ENNReal := fun z =>
    Filter.liminf (fun n => G n z) atTop
  have hL : Measurable[F.predictable.prod inferInstance] L := by
    change Measurable[F.predictable.prod inferInstance]
      (fun z => Filter.liminf (fun n => G n z) atTop)
    simp_rw [Filter.liminf_eq_iSup_iInf_of_nat]
    exact Measurable.iSup (fun n => Measurable.iInf (fun i => Measurable.iInf (fun _ => hG i)))
  let psi : Real → Real → Omega → ENNReal := fun s x w =>
    if 0 ≤ s then L ((s.toNNReal, w), x) else ENNReal.ofReal (phi s x w)
  refine ⟨psi, ?_, ?_⟩
  · have he : (fun z : (NNReal × Omega) × Real => psi (z.1.1 : Real) z.2 z.1.2) = L := by
      funext z
      simp [psi]
    rw [he]
    exact hL
  · filter_upwards [hCommon] with w hw
    intro s x
    by_cases hs : 0 ≤ s
    · have hcoe : (s.toNNReal : Real) = s := by simp [Real.coe_toNNReal, hs]
      have hlim : Tendsto (fun n => G n ((s.toNNReal, w), x)) atTop
          (nhds (ENNReal.ofReal (phi s x w))) := by
        by_cases hz : s.toNNReal = 0
        · have hsz : s = 0 := by simpa [hz] using hcoe.symm
          subst s
          simpa [G, h0] using
            (tendsto_const_nhds : Tendsto (fun _ : Nat => ENNReal.ofReal (phi 0 x w))
              atTop (nhds (ENNReal.ofReal (phi 0 x w))))
        · have hpos : 0 < s.toNNReal := pos_iff_ne_zero.mpr hz
          have hh := (hw x s.toNNReal hpos).comp (hleft s.toNNReal hpos)
          have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
          simpa [G, Function.comp_def, hcoe] using h
      simpa [psi, hs, L] using hlim.liminf_eq
    · simp [psi, hs]
