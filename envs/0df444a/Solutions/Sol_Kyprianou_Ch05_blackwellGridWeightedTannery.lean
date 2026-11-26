-- Prove2me | solution 1 for Kyprianou.Ch05.blackwellGridWeightedTannery
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:45:36.609961+00:00
-- url     : https://prove2.me/submissions/abf0ca3f-f677-4199-851f-3e7c560f4d38

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_blackwellReflectedGridCellMass
import Theorems.Thm_FamousTheorems_tannery_theorem
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Summable weighted reflected grid masses converge by Tannery. -/
theorem solution
    (V : Measure Real) (mu : Real)
    (hBlackwell : ∀ d : Real, 0 < d →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+d))).toReal)
        atTop (nhds (d/mu)))
    (d : Real) (hd : 0 < d)
    (C : ENNReal) (hC : C ≠ ⊤)
    (hbound : ∀ a x : Real, V (Set.Icc 0 x ∩ Set.Ioc a (a+d)) ≤ C)
    (c : Nat → Real) (hs : Summable (fun k => |c k|)) :
    Tendsto (fun x : Real => ∑' k : Nat, c k * (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal)
      atTop (nhds ((∑' k : Nat, c k) * (d/mu))) := by
  let mass (x : Real) (k : Nat) : Real :=
    (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal
  have hlim := FamousTheorems.tannery_theorem
    (𝓕 := (atTop : Filter Real)) (f := fun x k => c k * mass x k)
    (g := fun k => c k * (d/mu)) (bound := fun k => |c k| * C.toReal)
    (hs.mul_right C.toReal)
    (fun k => tendsto_const_nhds.mul (blackwellReflectedGridCellMass V mu hBlackwell d hd k))
    (Filter.Eventually.of_forall (fun x k => by
      have he : x-((k : Real)+1)*d+d = x-(k : Real)*d := by ring
      have hb := hbound (x-((k : Real)+1)*d) x
      rw [he] at hb
      have hreal := ENNReal.toReal_mono hC hb
      change ‖c k * mass x k‖ ≤ |c k| * C.toReal
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ mass x k from ENNReal.toReal_nonneg)]
      exact mul_le_mul_of_nonneg_left hreal (abs_nonneg _)))
  simpa only [mass, tsum_mul_right] using hlim
