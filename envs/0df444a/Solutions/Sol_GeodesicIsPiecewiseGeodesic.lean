-- Prove2me | solution 1 for GeodesicIsPiecewiseGeodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:26.898751+00:00
-- url     : https://prove2.me/submissions/a9ef427f-3962-49e6-926c-4fd16f0299ce

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (x y : E) : IsPiecewiseGeodesicWith (GP.G x y) 1 := by
-- BODY
  classical
  refine ⟨fun j => if j = 0 then 0 else (GP.G x y).len, ?_, ?_, ?_, ?_⟩
  · intro a _ b _ hab
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · simp [hb]
      · simp [hb, (GP.G x y).len_nonneg]
    · have hb : b ≠ 0 := by rintro rfl; omega
      simp [ha, hb]
  · simp
  · simp
  · intro i hi
    interval_cases i
    · simpa using GP.isGeodesic x y
