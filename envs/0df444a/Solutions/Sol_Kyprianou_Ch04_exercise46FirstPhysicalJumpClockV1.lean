-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstPhysicalJumpClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:48.559487+00:00
-- url     : https://prove2.me/submissions/dfb8d8cb-0bff-469c-9e29-bd02dac6c19b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstPhysicalJumpExistsV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (hBV : L.BoundedVariation)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (hRate : 0 < (L.ν (Iio (0 : Real))).toReal) :
    let A : Omega → WithTop NNReal := fun w =>
      ⨅ u : NNReal, if 0 < u ∧
        L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u < 0
        then (u : WithTop NNReal) else ⊤
    let a : Omega → NNReal := fun w => (A w).untopD 0
    ∀ᵐ w ∂P, A w = (a w : WithTop NNReal) ∧ 0 < a w ∧
      L.X (a w) w < Function.leftLim (fun v : NNReal => L.X v w) (a w) ∧
      ∀ u : NNReal, 0 < u → u < a w →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u := by
  dsimp only
  filter_upwards [Kyprianou.Ch04.exercise46FirstPhysicalJumpExistsV1 P G L hBV hFinite hRate]
    with w hw
  obtain ⟨t, ht, hj, hp⟩ := hw
  let f : NNReal → WithTop NNReal := fun u =>
    if 0 < u ∧ L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u < 0
      then (u : WithTop NNReal) else ⊤
  have he : (⨅ u, f u) = (t : WithTop NNReal) := by
    apply le_antisymm
    · calc
        (⨅ u, f u) ≤ f t := iInf_le f t
        _ = (t : WithTop NNReal) := by
          change (if 0 < t ∧ L.X t w -
            Function.leftLim (fun v : NNReal => L.X v w) t < 0
            then (t : WithTop NNReal) else ⊤) = _
          rw [if_pos ⟨ht, sub_neg.mpr hj⟩]
    · apply le_iInf
      intro u
      by_cases h : 0 < u ∧ L.X u w -
          Function.leftLim (fun v : NNReal => L.X v w) u < 0
      · have htu : t ≤ u := by
          by_contra! hut
          have hz := hp u h.1 hut
          exact (ne_of_lt (sub_neg.mp h.2)) hz
        change (t : WithTop NNReal) ≤
          (if 0 < u ∧ L.X u w -
            Function.leftLim (fun v : NNReal => L.X v w) u < 0
            then (u : WithTop NNReal) else ⊤)
        rw [if_pos h]
        exact WithTop.coe_le_coe.mpr htu
      · change (t : WithTop NNReal) ≤
          (if 0 < u ∧ L.X u w -
            Function.leftLim (fun v : NNReal => L.X v w) u < 0
            then (u : WithTop NNReal) else ⊤)
        rw [if_neg h]
        exact le_top
  simpa only [f, he, WithTop.untopD_coe] using
    (show (t : WithTop NNReal) = ↑t ∧ 0 < t ∧
      L.X t w < Function.leftLim (fun v : NNReal => L.X v w) t ∧
      ∀ u : NNReal, 0 < u → u < t →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u
      from ⟨rfl, ht, hj, hp⟩)
