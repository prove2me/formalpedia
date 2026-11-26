-- Prove2me | solution 1 for Kyprianou.Ch05.karamataScaledMeasureData
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:44:36.237633+00:00
-- url     : https://prove2.me/submissions/1dbb9f59-4d1a-4653-b761-9f7cffd3d0c6

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Theorems.Thm_Kyprianou_Ch05_karamataDilationLaplace
import Theorems.Thm_Kyprianou_Ch05_karamataDilationSupportMass
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Extend positive dilations by the zero measure outside positive scales. -/
theorem solution (U : Measure Real) (c : Real → Real)
    (hs : U (Iio 0) = 0)
    (hfin : ∀ t : Real, 0 < t → positiveLaplace U t ≠ ⊤) :
    ∃ M : Real → Measure Real,
      (∀ x, M x (Iio 0) = 0) ∧
      (∀ x t : Real, 0 < t → positiveLaplace (M x) t ≠ ⊤) ∧
      (∀ x t : Real, 0 < x → 0 ≤ c x → 0 < t →
        (positiveLaplace (M x) t).toReal = c x * (positiveLaplace U (t/x)).toReal) ∧
      (∀ x : Real, 0 < x → 0 ≤ c x →
        (M x (Icc 0 1)).toReal = c x * (U (Icc 0 x)).toReal) := by
  let M : Real → Measure Real := fun x => if 0 < x then
    ENNReal.ofReal (c x) • Measure.map (fun z : Real => z/x) U else 0
  refine ⟨M,?_,?_,?_,?_⟩
  · intro x
    by_cases hx : 0 < x
    · simpa only [M,if_pos hx] using (karamataDilationSupportMass U x (c x) hx hs).1
    · simp [M,hx]
  · intro x t ht
    by_cases hx : 0 < x
    · simp only [M,if_pos hx,karamataDilationLaplace U x (c x) t hx]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ (div_pos ht hx))
    · simp [M,hx,positiveLaplace]
  · intro x t hx hc ht
    simp only [M,if_pos hx,karamataDilationLaplace U x (c x) t hx,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal hc]
  · intro x hx hc
    have he := (karamataDilationSupportMass U x (c x) hx hs).2
    simp only [M,if_pos hx,he,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc]
