-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.liftSeries_pderiv_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:11.258384+00:00
-- url     : https://prove2.me/submissions/7dc8bd3c-82e9-4912-a2ab-f00c8084c00b

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib

open OAI.PiExponent.FormalInterpolation

open MeasureTheory Filter Topology in

theorem solution
    {m : Nat} (i : Fin m) (f : PowerSeries Complex) :
    MvPowerSeries.pderiv Complex i.succ (liftSeries m f) = 0 := by
  ext n
  rw [MvPowerSeries.coeff_pderiv, map_zero]
  set p := n + Finsupp.single i.succ 1
  have hp : p = Finsupp.cons (p 0) p.tail := (Finsupp.cons_tail p).symm
  have key := MvPowerSeries.coeff_coeff_finSuccEquiv (R := Complex) (liftSeries m f) (k := p 0) (x := p.tail)
  have he : MvPowerSeries.finSuccEquiv Complex m (liftSeries m f) = PowerSeries.map MvPowerSeries.C f := by
    simp [liftSeries]
  rw [he, PowerSeries.coeff_map, MvPowerSeries.coeff_C, if_neg, ← hp] at key
  · rw [← key, zero_mul]
  · intro h
    have := congrArg (fun q => q i) h
    simp [p, Finsupp.tail_apply] at this
