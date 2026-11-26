-- Prove2me | solution 1 for Kyprianou.Ch05.monotoneDifferenceGridOscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:01:56.661428+00:00
-- url     : https://prove2.me/submissions/86f5ee11-3e88-4761-98db-9f57d58d8648

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Grid oscillation of a monotone difference is bounded by the sum of its endpoint increments. -/
theorem solution
    (p q : Real → Real) (hp : Monotone p) (hq : Monotone q)
    (d : Real) (hd : 0 < d) (k : Int) :
    0 ≤ riCellOscillation (fun t => p t-q t) d k ∧
      riCellOscillation (fun t => p t-q t) d k ≤
        (p (((k : Real)+1)*d)-p ((k : Real)*d)) +
        (q (((k : Real)+1)*d)-q ((k : Real)*d)) := by
  let a : Real := (k : Real)*d
  let b : Real := ((k : Real)+1)*d
  let S := (fun t => p t-q t) '' Icc a b
  have hab : a ≤ b := by dsimp [a,b]; nlinarith
  have hne : S.Nonempty := ⟨p a-q a,⟨a,⟨le_rfl,hab⟩,rfl⟩⟩
  have hbounds (z : Real) (hz : z ∈ S) :
      p a-q b ≤ z ∧ z ≤ p b-q a := by
    obtain ⟨t,ht,rfl⟩ := hz
    constructor <;> linarith [hp ht.1,hp ht.2,hq ht.1,hq ht.2]
  have hU : BddAbove S := ⟨p b-q a,fun _ hz => (hbounds _ hz).2⟩
  have hL : BddBelow S := ⟨p a-q b,fun _ hz => (hbounds _ hz).1⟩
  obtain ⟨z,hz⟩ := hne
  change 0 ≤ sSup S-sInf S ∧ sSup S-sInf S ≤ _
  exact ⟨sub_nonneg.mpr ((csInf_le hL hz).trans (le_csSup hU hz)),
    by have hu := csSup_le ⟨z,hz⟩ (fun t ht => (hbounds t ht).2)
       have hl := le_csInf ⟨z,hz⟩ (fun t ht => (hbounds t ht).1)
       change _ ≤ (p b-p a)+(q b-q a)
       linarith⟩
