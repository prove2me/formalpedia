-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_initial_ideal_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:47:57.592334+00:00
-- url     : https://prove2.me/submissions/8b536f14-e360-4ddf-a884-90e3fe52e0a1

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s D : Nat)
    (hs : 0 < s) (hD : 0 < D)
    (hcoords : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      MvPolynomial.X i ^ n ∈ Ideal.span {h : MvPolynomial (Fin d) Complex |
        ∃ g : MvPolynomial (Fin d) Complex,
          g ∈ I ^ s ∧
          (∀ a ∈ g.support,
            ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
          h = MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) g}) :
    ∀ x : Fin d → Complex,
      (∃ i : Fin d, x i ≠ 0) →
      ∃ g : MvPolynomial (Fin d) Complex,
        g ∈ I ^ s ∧
        (∀ a ∈ g.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) g) ≠ 0 := by
  classical
  let S : Set (MvPolynomial (Fin d) Complex) :=
    {h | ∃ g : MvPolynomial (Fin d) Complex,
      g ∈ I ^ s ∧
      (∀ a ∈ g.support,
        ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
      h = MvPolynomial.weightedHomogeneousComponent
        (fun k => (w k : ℚ)) (D : ℚ) g}
  intro x hx
  obtain ⟨i, hxi⟩ := hx
  obtain ⟨n, hn, hpow⟩ := hcoords i
  let φ : MvPolynomial (Fin d) Complex →+* Complex :=
    MvPolynomial.eval₂Hom (RingHom.id Complex) x
  have hpow_eval : φ (MvPolynomial.X i ^ n) ≠ 0 := by
    simpa [φ] using (pow_ne_zero n hxi)
  by_contra hnot
  have hS : ∀ z ∈ S, φ z = 0 := by
    intro z hz
    rcases hz with ⟨g, hg, hb, rfl⟩
    have hz0 : MvPolynomial.eval x
        (MvPolynomial.weightedHomogeneousComponent
          (fun k => (w k : ℚ)) (D : ℚ) g) = 0 := by
      by_contra hne
      exact hnot ⟨g, hg, hb, hne⟩
    change MvPolynomial.eval x
        (MvPolynomial.weightedHomogeneousComponent
          (fun k => (w k : ℚ)) (D : ℚ) g) = 0
    simpa [φ] using hz0
  have hspan : Ideal.span S ≤ RingHom.ker φ :=
    Ideal.span_le.2 (by
      intro z hz
      exact RingHom.mem_ker.mpr (hS z hz))
  have hzpow : φ (MvPolynomial.X i ^ n) = 0 :=
    RingHom.mem_ker.mp (hspan hpow)
  exact hpow_eval hzpow