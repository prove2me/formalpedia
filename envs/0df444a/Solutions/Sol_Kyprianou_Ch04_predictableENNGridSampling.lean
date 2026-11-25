-- Prove2me | solution 1 for Kyprianou.Ch04.predictableENNGridSampling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:04:53.949122+00:00
-- url     : https://prove2.me/submissions/9e044aa9-3e41-4e46-b132-21e757fe2774

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_predictableMarkedWindowMeasurable
import Theorems.Thm_Kyprianou_Ch04_predictableGridValueSup
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real → Real → Omega → Real)
    (hPhi : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × Real => phi (t : Real) z.2 z.1))
    (q : NNReal → NNReal) (a b : Nat → NNReal)
    (h0 : q 0 = 0)
    (hcell : ∀ k t, t ∈ Set.Ioc (a k) (b k) → q t = a k)
    (hcover : ∀ t, 0 < t → ∃ k, t ∈ Set.Ioc (a k) (b k)) :
    Measurable[F.predictable.prod inferInstance]
      (fun z : (NNReal × Omega) × Real =>
        ENNReal.ofReal (phi (q z.1.1 : Real) z.2 z.1.2)) := by
  classical
  let g : NNReal → Omega × Real → ENNReal := fun t z =>
    ENNReal.ofReal (phi (t : Real) z.2 z.1)
  have hg : ∀ t, Measurable[(F t).prod inferInstance] (g t) :=
    fun t => ENNReal.continuous_ofReal.measurable.comp (hPhi t)
  let g0 : ((NNReal × Omega) × Real) → ENNReal := fun z =>
    @ite ENNReal (z.1.1 ∈ ({0} : Set NNReal)) (Classical.propDecidable _) (g 0 (z.1.2, z.2)) 0
  let G : Nat → ((NNReal × Omega) × Real) → ENNReal := fun k z =>
    @ite ENNReal (z.1.1 ∈ Set.Ioc (a k) (b k)) (Classical.propDecidable _) (g (a k) (z.1.2, z.2)) 0
  have hm0 : Measurable[F.predictable.prod inferInstance] g0 :=
    predictableMarkedWindowMeasurable F 0 {0}
      (fun A hA => measurableSet_predictable_singleton_bot_prod hA) (g 0) (hg 0)
  have hmG : ∀ k, Measurable[F.predictable.prod inferInstance] (G k) := fun k =>
    predictableMarkedWindowMeasurable F (a k) (Set.Ioc (a k) (b k))
      (fun A hA => measurableSet_predictable_Ioc_prod (a k) (b k) hA) (g (a k)) (hg (a k))
  have he : (fun z : (NNReal × Omega) × Real => g (q z.1.1) (z.1.2, z.2)) =
      fun z => max (g0 z) (⨆ k, G k z) := by
    funext z
    simpa [g0, G, Set.indicator] using
      predictableGridValueSup q a b h0 hcell hcover (fun t => g t (z.1.2, z.2)) z.1.1
  change Measurable[F.predictable.prod inferInstance]
    (fun z : (NNReal × Omega) × Real => g (q z.1.1) (z.1.2, z.2))
  rw [he]
  exact hm0.max (Measurable.iSup hmG)
