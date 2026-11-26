-- Prove2me | solution 1 for Kyprianou.Ch05.driNonnegativeGridOscillationBudget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:51:23.294489+00:00
-- url     : https://prove2.me/submissions/ff11c7c8-3435-49f9-9738-8d08283db11b

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Restrict the nonnegative oscillation series on integer cells to natural cells. -/
theorem solution (h : Real → Real) (hDRI : DirectlyRiemannIntegrable h)
    (eps : Real) (heps : 0 < eps) :
    ∃ d : Real, 0 < d ∧
      Summable (fun k : Nat => |riCellOscillation h d (k : Int)|) ∧
      (∑' k : Nat, riCellOscillation h d (k : Int))*d < eps := by
  obtain ⟨delta,hdelta,hh⟩ := hDRI.2.2 eps heps
  let d := delta/2
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨hs,hsmall⟩ := hh d hd (by dsimp [d]; linarith)
  have hn (k : Int) : 0 ≤ riCellOscillation h d k := by
    let a : Real := (k : Real)*d
    let b : Real := ((k : Real)+1)*d
    have hab : a < b := by dsimp [a,b]; nlinarith
    obtain ⟨hu,hl⟩ := hDRI.2.1 a b hab
    have hx : h a ∈ h '' Icc a b := ⟨a,⟨le_rfl,hab.le⟩,rfl⟩
    change 0 ≤ sSup (h '' Icc a b)-sInf (h '' Icc a b)
    exact sub_nonneg.mpr ((csInf_le hl hx).trans (le_csSup hu hx))
  have hinj : Function.Injective (fun k : Nat => (k : Int)) := Int.ofNat_injective
  have hN : Summable (fun k : Nat => d * riCellOscillation h d (k : Int)) :=
    hs.comp_injective hinj
  have hosc : Summable (fun k : Nat => riCellOscillation h d (k : Int)) :=
    (summable_mul_left_iff hd.ne').mp hN
  refine ⟨d,hd,?_,?_⟩
  · simpa only [abs_of_nonneg (hn _)] using hosc
  · have hle := Summable.tsum_le_tsum_of_inj
      (fun k : Nat => (k : Int)) hinj
      (fun k _ => mul_nonneg hd.le (hn k)) (fun k => le_rfl) hN hs
    rw [tsum_mul_left, tsum_mul_left] at hle
    rw [tsum_mul_left] at hsmall
    linarith
