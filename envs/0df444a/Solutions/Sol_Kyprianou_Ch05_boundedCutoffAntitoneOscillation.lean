-- Prove2me | solution 1 for Kyprianou.Ch05.boundedCutoffAntitoneOscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:21:17.064566+00:00
-- url     : https://prove2.me/submissions/7879488c-92cf-438d-a48f-927c92b0caf3

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_cutoffAntitoneMonotoneDifference
import Theorems.Thm_Kyprianou_Ch05_monotoneDifferenceGridOscillation
import Theorems.Thm_Kyprianou_Ch05_monotoneIntegerIncrementBudget
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Dominate the total oscillation by two bounded monotone increment series. -/
theorem solution
    (g : Real → Real) (hg : Antitone g)
    (hn : ∀ t, 0 ≤ g t) (hb : ∀ t, g t ≤ 1)
    (y d : Real) (hd : 0 < d) :
    Summable (fun k : Int => riCellOscillation
      (fun t : Real => if y < t then g t else 0) d k) ∧
    (∑' k : Int, riCellOscillation
      (fun t : Real => if y < t then g t else 0) d k) ≤ 2 := by
  obtain ⟨p,q,hp,hq,hpn,hpb,hqn,hqb,he⟩ := cutoffAntitoneMonotoneDifference g hg hn hb y
  have hfun : (fun t : Real => if y < t then g t else 0) = fun t => p t-q t := funext he
  rw [hfun]
  let P : Int → Real := fun k => p ((k : Real)*d)
  let Q : Int → Real := fun k => q ((k : Real)*d)
  have hmono : Monotone (fun k : Int => (k : Real)*d) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hd.le
  obtain ⟨hsP,hbP⟩ := monotoneIntegerIncrementBudget P (hp.comp hmono) (fun k => hpn _) (fun k => hpb _)
  obtain ⟨hsQ,hbQ⟩ := monotoneIntegerIncrementBudget Q (hq.comp hmono) (fun k => hqn _) (fun k => hqb _)
  have hcell (k : Int) : 0 ≤ riCellOscillation (fun t => p t-q t) d k ∧
      riCellOscillation (fun t => p t-q t) d k ≤ (P (k+1)-P k)+(Q (k+1)-Q k) := by
    simpa only [P,Q,Int.cast_add,Int.cast_one] using monotoneDifferenceGridOscillation p q hp hq d hd k
  have hs := (hsP.add hsQ).of_nonneg_of_le (fun k => (hcell k).1) (fun k => (hcell k).2)
  refine ⟨hs,?_⟩
  have hle := hs.tsum_le_tsum (fun k => (hcell k).2) (hsP.add hsQ)
  rw [hsP.tsum_add hsQ] at hle
  linarith
