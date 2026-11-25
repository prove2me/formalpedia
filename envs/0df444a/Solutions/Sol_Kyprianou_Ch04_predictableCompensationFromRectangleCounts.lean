-- Prove2me | solution 1 for Kyprianou.Ch04.predictableCompensationFromRectangleCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:18.048159+00:00
-- url     : https://prove2.me/submissions/a7788f70-ee15-4922-a25f-3f529927ee56

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
import Theorems.Thm_Kyprianou_Ch04_markedExpectedIntegralExhaustion
import Theorems.Thm_Kyprianou_Ch04_predictableCompensationFiniteBandFromRectangleCounts
import Theorems.Thm_AvramDividend_Classical_ripple_predictable_le_ambient_product
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hRect : ∀ (u v : NNReal) (B : Set Real) (A : Set Omega),
      u ≤ v → MeasurableSet B → MeasurableSet[F u] A →
      (∫⁻ omega, N.N omega (Set.Ioc (u : Real) (v : Real) ×ˢ B) *
        A.indicator (fun _ => (1 : ENNReal)) omega ∂P) =
      referenceIntensity levyMeasure (Set.Ioc (u : Real) (v : Real) ×ˢ B) * P A)
    (psi : Real → Real → Omega → ENNReal)
    (hPsi : Measurable[F.predictable.prod inferInstance]
      (fun z : (NNReal × Omega) × Real => psi (z.1.1 : Real) z.2 z.1.2)) :
    ∀ t : NNReal,
      (∫⁻ omega, (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
        psi z.1 z.2 omega ∂(N.N omega)) ∂P) =
      (∫⁻ omega, (∫⁻ s in Set.Icc (0 : Real) (t : Real),
        (∫⁻ x, psi s x omega ∂levyMeasure) ∂volume) ∂P) := by
  intro t
  let f : ((NNReal × Omega) × Real) → ENNReal := fun z =>
    psi (z.1.1 : Real) z.2 z.1.2
  let B : Nat → Set Real := spanningSets levyMeasure
  have hB : ∀ n, MeasurableSet (B n) := measurableSet_spanningSets levyMeasure
  have hm : Monotone B := fun _ _ h => spanningSets_mono h
  have hc : (⋃ n, B n) = Set.univ := iUnion_spanningSets levyMeasure
  have hfin (n : Nat) : referenceIntensity levyMeasure
      (Set.Icc (0 : Real) (t : Real) ×ˢ B n) ≠ ⊤ :=
    closedTimeBandIntensityFinite levyMeasure t (B n) (measure_spanningSets_lt_top levyMeasure n)
  have hraw (n : Nat) : ∀ᵐ w ∂P, N.N w (Set.Icc (0 : Real) (t : Real) ×ˢ B n) ≠ ⊤ := by
    filter_upwards [N.integer_valued (measurableSet_Icc.prod (hB n)) (hfin n)] with w hw
    obtain ⟨k, hk⟩ := hw
    simp [hk]
  have hdet (n : Nat) : ∀ᵐ (_ : Omega) ∂P, referenceIntensity levyMeasure
      (Set.Icc (0 : Real) (t : Real) ×ˢ B n) ≠ ⊤ :=
    Filter.Eventually.of_forall (fun _ => hfin n)
  have hleft := markedExpectedIntegralExhaustion P F N.N
    (fun S hS => N.measurable_eval hS) t B hB hm hc hraw f hPsi
  have hright := markedExpectedIntegralExhaustion P F (fun _ => referenceIntensity levyMeasure)
    (fun _ _ => measurable_const) t B hB hm hc hdet f hPsi
  have hfull : (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      f ((z.1.toNNReal, w), z.2) ∂(N.N w) ∂P) =
      (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
        f ((z.1.toNNReal, w), z.2) ∂(referenceIntensity levyMeasure) ∂P) := by
    rw [hleft, hright]
    congr 1
    funext n
    exact predictableCompensationFiniteBandFromRectangleCounts P levyMeasure F N hRect
      t (B n) (hB n) (measure_spanningSets_lt_top levyMeasure n) f hPsi
  have hPred := AvramDividend.Classical.ripple_predictable_le_ambient_product F
  have hfst : @Measurable ((NNReal × Omega) × Real) (NNReal × Omega)
      inferInstance F.predictable Prod.fst :=
    fun S hS => (hPred S hS).preimage measurable_fst
  have hpair : @Measurable ((NNReal × Omega) × Real) ((NNReal × Omega) × Real)
      inferInstance (F.predictable.prod inferInstance) (fun z => (z.1, z.2)) :=
    hfst.prodMk measurable_snd
  have hle : F.predictable.prod inferInstance ≤
      (inferInstance : MeasurableSpace ((NNReal × Omega) × Real)) := by
    intro S hS
    simpa using hpair hS
  have hf0 : Measurable f := hPsi.mono hle le_rfl
  have hregion : (referenceIntensity levyMeasure).restrict
      (Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ) =
      ((volume : Measure Real).restrict (Set.Icc 0 (t : Real))).prod levyMeasure := by
    rw [referenceIntensity, ← Measure.prod_restrict, Measure.restrict_univ,
      Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.mpr (fun _ hs => hs.1)]
  calc
    _ = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
          f ((z.1.toNNReal, w), z.2) ∂(N.N w) ∂P) := by
      apply lintegral_congr
      intro w
      apply setLIntegral_congr_fun (measurableSet_Icc.prod MeasurableSet.univ)
      intro z hz
      simp [f, Real.coe_toNNReal', max_eq_left hz.1.1]
    _ = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
          f ((z.1.toNNReal, w), z.2) ∂(referenceIntensity levyMeasure) ∂P) := hfull
    _ = _ := by
      apply lintegral_congr
      intro w
      have hfg : Measurable (fun z : Real × Real => f ((z.1.toNNReal, w), z.2)) :=
        hf0.comp (((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
          measurable_const).prodMk measurable_snd)
      rw [hregion, lintegral_prod _ hfg.aemeasurable]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s hs
      simp [f, Real.coe_toNNReal', max_eq_left hs.1]
