-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_quotient_representatives_monic_relations_with_rounding_margin
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:26:18.7683+00:00
-- url     : https://prove2.me/submissions/df9ec0a5-da9f-44fc-8ffb-07f9e4f8b06f

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

/-!
# Representatives with a rounding margin give weighted monic relations

Given positive weights and representatives modulo `I^k` of weighted degree at
most `k c`, together with the strict margin `k (a - c) > w i`, choose
`b i = ⌊(k c) / w i⌋ + 1` and subtract the bounded representative of
`X i ^ (b i)` to obtain the required weighted monic relations in `I^k`.
-/

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (c a : Rat) (hc : 0 < c) (hca : c < a)
    (k : Nat) (hk : 0 < k)
    (hmargin : ∀ i, (k : Real) * ((a - c : Rat) : Real) > (w i : Real))
    (hrep : ∀ P : MvPolynomial (Fin d) Complex,
      ∃ R : MvPolynomial (Fin d) Complex,
        P - R ∈ I ^ k ∧
        ∀ v ∈ R.support,
          (∑ j, (w j : Real) * (v j : Real)) ≤ (k : Real) * (c : Real)) :
    ∃ k' : Nat, 0 < k' ∧ ∃ (b : Fin d → Nat), (∀ i, 0 < b i) ∧
      ∃ (F : Fin d → MvPolynomial (Fin d) Complex),
        (∀ i, F i ∈ I ^ k') ∧
        (∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real)) ∧
        (∀ i, (w i : Real) * (b i : Real) ≤ (k' : Real) * (a : Real)) := by
  classical
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast hc
  have hcaR : (c : Real) < (a : Real) := by exact_mod_cast hca
  -- Pivot exponents just above the weighted threshold `k c / w i`.
  set b : Fin d → Nat :=
    fun i => Nat.floor (((k : Real) * (c : Real)) / (w i : Real)) + 1 with hbdef
  have hbpos : ∀ i, 0 < b i := by
    intro i
    simp only [hbdef]
    omega
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
      rw [hbdef]
      push_cast
      ring
    rw [hb]
    -- `div_lt_iff₀` yields `(⌊…⌋ + 1) * w i`; commute to match the goal order.
    linarith
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
      rw [hbdef]
      push_cast
      ring
    -- `w i * b i ≤ k c + w i`, and the margin gives `k c + w i < k a`.
    have hle : (w i : Real) * (b i : Real) ≤ (k : Real) * (c : Real) + (w i : Real) := by
      rw [hb]
      linarith
    have hmargin' :
        (k : Real) * (c : Real) + (w i : Real) < (k : Real) * (a : Real) := by
      have hm := hmargin i
      -- `↑k * ↑(a - c) > ↑(w i)` → `↑k * (↑a - ↑c) > ↑(w i)`
      have hcast : ((a - c : Rat) : Real) = (a : Real) - (c : Real) := by
        exact_mod_cast (Rat.cast_sub a c)
      rw [hcast] at hm
      nlinarith
    exact le_of_lt (lt_of_le_of_lt hle hmargin')
  -- Monic relations from bounded representatives of the pivot monomials.
  set F : Fin d → MvPolynomial (Fin d) Complex := fun i =>
    MvPolynomial.X i ^ b i - (hrep (MvPolynomial.X i ^ b i)).choose with hFdef
  have hFmem : ∀ i, F i ∈ I ^ k := by
    intro i
    have := (hrep (MvPolynomial.X i ^ b i)).choose_spec.1
    simpa only [hFdef] using this
  have hFsupp :
      ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
        (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real) := by
    intro i v hv
    have hQ :
        MvPolynomial.X i ^ b i - F i =
          (hrep (MvPolynomial.X i ^ b i)).choose := by
      rw [hFdef]
      ring
    rw [hQ] at hv
    have hle := (hrep (MvPolynomial.X i ^ b i)).choose_spec.2 v hv
    exact lt_of_le_of_lt hle (hblower i)
  exact ⟨k, hk, b, hbpos, F, hFmem, hFsupp, hbupper⟩
