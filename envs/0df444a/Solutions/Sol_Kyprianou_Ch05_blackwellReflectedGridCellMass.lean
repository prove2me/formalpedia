-- Prove2me | solution 1 for Kyprianou.Ch05.blackwellReflectedGridCellMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:31:53.376174+00:00
-- url     : https://prove2.me/submissions/6f1c997a-5b63-4b48-972e-a14956dc3af7

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Blackwell limit for reflected truncated half-open grid cells. -/
theorem solution
    (V : Measure Real) (mu : Real)
    (hBlackwell : ∀ d : Real, 0 < d →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+d))).toReal)
        atTop (nhds (d/mu)))
    (d : Real) (hd : 0 < d) (k : Nat) :
    Tendsto (fun x : Real => (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal)
      atTop (nhds (d/mu)) := by
  have hshift : Tendsto (fun x : Real => x-((k : Real)+1)*d) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(((k : Real)+1)*d)) tendsto_id
  have ht := (hBlackwell d hd).comp hshift
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (((k : Real)+1)*d)] with x hx
  have hk : 0 ≤ (k : Real)*d := mul_nonneg (Nat.cast_nonneg k) hd.le
  have he : x-((k : Real)+1)*d+d = x-(k : Real)*d := by ring
  change (V (Set.Ioc (x-((k : Real)+1)*d) (x-((k : Real)+1)*d+d))).toReal = _
  rw [he]
  have hsub : Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d) ⊆ Set.Icc 0 x := by
    intro z hz
    exact ⟨(sub_nonneg.mpr hx).trans hz.1.le, hz.2.trans (sub_le_self _ hk)⟩
  rw [Set.inter_eq_right.mpr hsub]
