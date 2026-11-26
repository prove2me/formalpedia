-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RightGridFutureLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:01:22.539274+00:00
-- url     : https://prove2.me/submissions/f8ab0212-b7a0-4483-8b69-d3f14f8d204b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (s : Omega → NNReal) (T : ℕ → Omega → NNReal)
    (w : Omega)
    (hAbove : ∀ n, s w ≤ T n w)
    (hlim : Tendsto (fun n => T n w) atTop (nhds (s w))) (u : NNReal) :
    Tendsto (fun n => L.X (T n w + u) w - L.X (T n w) w) atTop
      (nhds (L.X (s w + u) w - L.X (s w) w)) := by
  have h1 := (L.rightCont w (s w)).tendsto
  have h2 := (L.rightCont w (s w + u)).tendsto
  have h3 : Tendsto (fun n => T n w + u) atTop (nhds (s w + u)) :=
    hlim.add tendsto_const_nhds
  have hm1 : Tendsto (fun n => T n w) atTop (nhdsWithin (s w) (Ici (s w))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hAbove⟩
  have hm2 : Tendsto (fun n => T n w + u) atTop (nhdsWithin (s w + u) (Ici (s w + u))) :=
    tendsto_nhdsWithin_iff.mpr ⟨h3, Eventually.of_forall (fun n => add_le_add_left (hAbove n) u)⟩
  exact (h2.comp hm2).sub (h1.comp hm1)
