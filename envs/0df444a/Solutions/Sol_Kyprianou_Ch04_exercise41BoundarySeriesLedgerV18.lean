-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BoundarySeriesLedgerV18
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:01:38.118869+00:00
-- url     : https://prove2.me/submissions/ac80099b-0692-4b92-adef-c036abd060bd

import Theorems.Thm_Kyprianou_Ch04_exercise41BinaryPathDataV19
import Theorems.Thm_Kyprianou_Ch04_exercise41BinaryCadlagTsumV15
import Theorems.Thm_Kyprianou_Ch04_exercise41BoundarySeriesAlgebraV20
import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Ω : Type}
    (X Xleft : NNReal → Ω → ℝ) (w : Ω) (c : ℝ)
    (hd : 0 < c) (hzero : X 0 w = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (hNeg : ∀ t : NNReal, 0 < t → X t w ≤ Xleft t w)
    (hNoJump : ∀ s : NNReal, 0 < s →
      Function.leftLim (fun t => X t w) s = 0 → X s w = 0)
    (hDeparture : ∀ s : NNReal, X s w = 0 → ∃ ε : NNReal, 0 < ε ∧
      ∀ u : NNReal, 0 < u → u < ε → 0 < X (s + u) w)
    (hArrival : ∀ s : NNReal, 0 < s → X s w = 0 →
      Function.leftLim (fun t => X t w) s = 0 →
      ∃ ε : NNReal, 0 < ε ∧ ∀ u : NNReal, 0 < u →
        u < min ε s → X (s - u) w < 0)
    (hVisits : ∀ t : NNReal,
      Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ X s w = 0})
    (t : NNReal) :
    let a := fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0
    let b := fun x : ℝ => if 0 < x then (1 : ℝ) else 0
    let A : ℝ := ∑ s ∈ (hVisits t).toFinset, if Xleft s w = 0 then 1 else 0
    let B : ℝ := (if 0 < t then 1 else 0) +
      ∑ s ∈ (hVisits t).toFinset, if s < t then 1 else 0
    Summable (fun s : Ioc (0 : NNReal) t => ‖a (X s w) - a (Xleft s w)‖) ∧
    Summable (fun s : Ioc (0 : NNReal) t => ‖b (X s w) - b (Xleft s w)‖) ∧
    a (X t w) = a (X 0 w) + (∑' s : Ioc (0 : NNReal) t, (a (X s w) - a (Xleft s w))) + A ∧
    b (X t w) = b (X 0 w) + (∑' s : Ioc (0 : NNReal) t, (b (X s w) - b (Xleft s w))) + B := by
  let f := fun u : NNReal => if X u w < 0 then (-1 : ℝ) else 0
  obtain ⟨hr,hl,hval⟩ := exercise41BinaryPathDataV19 (fun s => X s w) (fun s => Xleft s w)
    (fun s => (hCadlag s).1) hLeft hNoJump hDeparture hArrival
  have h0 : f 0 = 0 := by simp [f,hzero]
  have hf : ∀ u, f u = 0 ∨ f u = -1 := by intro u; by_cases h : X u w < 0 <;> simp [f,h]
  have hlf : ∀ u, 0 < u → Function.leftLim f u = 0 ∨ Function.leftLim f u = -1 := by
    intro u hu
    rw [show Function.leftLim f u = (if 0 < Xleft u w then 0 else -1) from hval u hu]
    split <;> simp
  obtain ⟨hs,hSum⟩ := exercise41BinaryCadlagTsumV15 f h0 hf hlf hr hl t
  have hn : ∀ s : NNReal, 0 < s → Xleft s w = 0 → X s w = 0 := by
    intro s hs hz
    letI : NeBot (nhdsWithin s (Iio s)) := nhdsLT_neBot_of_exists_lt ⟨0,hs⟩
    exact hNoJump s hs ((leftLim_eq_of_tendsto (hLeft s hs)).trans hz)
  exact exercise41BoundarySeriesAlgebraV20 X Xleft w t hzero hVisits hn f
    (fun _ => rfl) hval hs hSum
