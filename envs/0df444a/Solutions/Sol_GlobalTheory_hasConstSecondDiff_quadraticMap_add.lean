-- Prove2me | solution 1 for GlobalTheory.hasConstSecondDiff_quadraticMap_add
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:33:03.639041+00:00
-- url     : https://prove2.me/submissions/55fc300b-65a7-4854-8950-b441d2077fd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst

open GlobalTheory QuadraticMap

variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]

private lemma secondDiff_add_const (f : X → A) (c : A) (a μ ν : X) :
    secondDiff (fun t => f t + c) a μ ν = secondDiff f a μ ν := by
  simp [secondDiff]
  abel

private lemma secondDiff_quadratic (Q : QuadraticMap ℤ X A) (a μ ν : X) :
    secondDiff (fun t => Q t) a μ ν = polar Q μ ν := by
  simp only [secondDiff, polar]
  have hpol :
      Q (a + μ + ν) - Q (a + μ) - Q ν = polar Q (a + μ) ν := by
    simp [polar]
  have hpol' :
      Q (a + ν) - Q a - Q ν = polar Q a ν := by
    simp [polar]
  calc
    Q (a + μ + ν) - Q (a + μ) - Q (a + ν) + Q a =
        (Q (a + μ + ν) - Q (a + μ) - Q ν) - (Q (a + ν) - Q a - Q ν) := by abel
    _ = polar Q (a + μ) ν - polar Q a ν := by rw [hpol, hpol']
    _ = polar Q a ν + polar Q μ ν - polar Q a ν := by rw [polar_add_left]
    _ = polar Q μ ν := by abel

theorem solution (Q : QuadraticMap ℤ X A) (c : A) :
    HasConstSecondDiff fun x => Q x + c := by
  intro a a' μ ν
  rw [secondDiff_add_const, secondDiff_add_const, secondDiff_quadratic, secondDiff_quadratic]
