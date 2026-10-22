-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.rounding_exponents_with_margin
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:29:38.975995+00:00
-- url     : https://prove2.me/submissions/be5f7ae9-e5ba-4b94-a474-826aeed0cd1e

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (c a : Rat) (hc : 0 < c) (hca : c < a)
    (k : Nat) (hk : 0 < k)
    (hmargin : ∀ i, (k : Real) * ((a - c : Rat) : Real) > (w i : Real)) :
    ∃ b : Fin d → Nat,
      (∀ i, 0 < b i) ∧
      (∀ i, (k : Real) * (c : Real) < (w i : Real) * (b i : Real)) ∧
      (∀ i, (w i : Real) * (b i : Real) ≤ (k : Real) * (a : Real)) := by
  classical
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast hc
  set b : Fin d → Nat :=
    fun i => Nat.floor (((k : Real) * (c : Real)) / (w i : Real)) + 1 with hbdef
  have hbpos : ∀ i, 0 < b i := by
    intro i; simp only [hbdef]; omega
  have hblower : ∀ i, (k : Real) * (c : Real) < (w i : Real) * (b i : Real) := by
    intro i
    have h1 :
        ((k : Real) * (c : Real)) / (w i : Real) <
          (Nat.floor (((k : Real) * (c : Real)) / (w i : Real)) : Real) + 1 :=
      Nat.lt_floor_add_one _
    rw [div_lt_iff₀ (hw i)] at h1
    have hb :
        (b i : Real) =
          (Nat.floor (((k : Real) * (c : Real)) / (w i : Real)) : Real) + 1 := by
      rw [hbdef]; push_cast; ring
    rw [hb]; linarith
  have hbupper : ∀ i, (w i : Real) * (b i : Real) ≤ (k : Real) * (a : Real) := by
    intro i
    have hnum : 0 ≤ ((k : Real) * (c : Real)) / (w i : Real) := by
      apply div_nonneg _ (le_of_lt (hw i))
      have : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg _
      nlinarith
    have hfloor :
        ((Nat.floor (((k : Real) * (c : Real)) / (w i : Real))) : Real) ≤
          ((k : Real) * (c : Real)) / (w i : Real) :=
      Nat.floor_le hnum
    rw [le_div_iff₀ (hw i)] at hfloor
    have hb :
        (b i : Real) =
          (Nat.floor (((k : Real) * (c : Real)) / (w i : Real)) : Real) + 1 := by
      rw [hbdef]; push_cast; ring
    have hle : (w i : Real) * (b i : Real) ≤ (k : Real) * (c : Real) + (w i : Real) := by
      rw [hb]; linarith
    have hmargin' :
        (k : Real) * (c : Real) + (w i : Real) < (k : Real) * (a : Real) := by
      have hm := hmargin i
      have hcast : ((a - c : Rat) : Real) = (a : Real) - (c : Real) := by
        exact_mod_cast (Rat.cast_sub a c)
      rw [hcast] at hm
      nlinarith
    exact le_of_lt (lt_of_le_of_lt hle hmargin')
  exact ⟨b, hbpos, hblower, hbupper⟩
