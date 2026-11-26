-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyStartTailMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:52:39.312197+00:00
-- url     : https://prove2.me/submissions/65e42fd9-0b0d-4c4a-bab1-86601ed6bb83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartsCanonicalV1
import Theorems.Thm_Kyprianou_Ch04_exercise46MeasurableJumpSubsetCountV1
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (Wleft : NNReal → Omega → Real)
    (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto
        (fun s : NNReal => sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w))) :
    let B : Omega → Set NNReal := fun w =>
      {t | 0 < t ∧ Wleft t w = 0 ∧
        0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}
    ∀ k : Nat, ∃ S : Set Omega, MeasurableSet S ∧
      S =ᵐ[P] {w | ((k+1 : Nat) : ENat) ≤ (B w).encard} := by
  dsimp only
  obtain ⟨S, hS, hJ, hEq⟩ :=
    Kyprianou.Ch04.exercise46BusyStartsCanonicalV1 P G L Wleft hWLeft
  have hm := Kyprianou.Ch04.exercise46MeasurableJumpSubsetCountV1 P G L S hS hJ
  intro k
  refine ⟨{w | (((k+1 : Nat) : ENat) : ENNReal) ≤
    (({t : NNReal | (w,t) ∈ S}).encard : ENNReal)},
    measurableSet_le measurable_const hm, ?_⟩
  filter_upwards [hEq] with w hw
  change (((((k+1 : Nat) : ENat) : ENNReal) ≤
    (({t : NNReal | (w,t) ∈ S}).encard : ENNReal)) =
    (((k+1 : Nat) : ENat) ≤
      {t : NNReal | 0 < t ∧ Wleft t w = 0 ∧
        0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}.encard))
  rw [ENat.toENNReal_le, hw]
