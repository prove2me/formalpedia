-- Prove2me | solution 1 for Kyprianou.Ch04.markedClockRectangleEval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:56:18.600827+00:00
-- url     : https://prove2.me/submissions/cf841420-d389-42df-9d98-39dbe5b07539

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R : Omega → Measure (Real × Real))
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (M : @Measure ((NNReal × Omega) × Real) (F.predictable.prod inferInstance))
    (hM : ∀ f : ((NNReal × Omega) × Real) → ENNReal, Measurable[F.predictable.prod inferInstance] f →
      (∫⁻ p, f p ∂M) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
        f ((z.1.toNNReal, w), z.2) ∂(R w) ∂P))
    (D : Set NNReal) (hD : MeasurableSet D)
    (A : Set Omega) (C : Set Real) (hC : MeasurableSet C)
    (hDC : MeasurableSet[F.predictable.prod inferInstance] ((D ×ˢ A) ×ˢ C)) :
    M ((D ×ˢ A) ×ˢ C) =
      ∫⁻ w, R w ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' D) ×ˢ (B ∩ C)) *
        A.indicator (fun _ => (1 : ENNReal)) w ∂P := by
  classical
  let S : Set ((NNReal × Omega) × Real) := (D ×ˢ A) ×ˢ C
  let U : Set (Real × Real) := Set.Icc (0 : Real) (t : Real) ×ˢ B
  let V : Set (Real × Real) :=
    (Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' D) ×ˢ (B ∩ C)
  let g : ((NNReal × Omega) × Real) → ENNReal := S.indicator 1
  have hg : Measurable[F.predictable.prod inferInstance] g :=
    measurable_const.indicator hDC
  have hI : (∫⁻ p, g p ∂M) = M S := lintegral_indicator_one hDC
  have hU : MeasurableSet U := measurableSet_Icc.prod hB
  have hV : MeasurableSet V :=
    (measurableSet_Icc.inter (hD.preimage continuous_real_toNNReal.measurable)).prod
      (hB.inter hC)
  have hVU : V ⊆ U := fun _ hz => ⟨hz.1.1, hz.2.1⟩
  change M S = _
  rw [← hI, hM g hg]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ A
  · have he : Set.EqOn (fun z : Real × Real => g ((z.1.toNNReal, w), z.2))
        (V.indicator (1 : (Real × Real) → ENNReal)) U := by
      intro z hz
      have hz1 : z.1 ∈ Set.Icc (0 : Real) (t : Real) := hz.1
      have hz2 : z.2 ∈ B := hz.2
      simp [g, S, V, Set.indicator, hw, hz1, hz2]
    rw [setLIntegral_congr_fun hU he, lintegral_indicator_one hV,
      Measure.restrict_apply hV, Set.inter_eq_left.mpr hVU]
    simp [Set.indicator_of_mem hw, V]
  · have he : (fun z : Real × Real => g ((z.1.toNNReal, w), z.2)) =
        fun _ => (0 : ENNReal) := by
      funext z
      simp [g, S, Set.indicator, hw]
    rw [he]
    simp [Set.indicator_of_notMem hw]
