-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_support_finite_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T18:23:03.993659+00:00
-- url     : https://prove2.me/submissions/e547990b-3806-4d77-a42b-41e351fe7c7c

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators Pointwise

theorem solution
    {d : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : Fin d → Rat)
    (f : ι → MvPolynomial (Fin d) Complex) (B : ι → Real)
    (hweight : ∀ i, ∀ a ∈ (f i).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ B i) :
    ∀ a ∈ (∏ i : ι, f i).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ ∑ i, B i := by
  classical
  let W : (Fin d →₀ Nat) → Real := fun a =>
    ∑ l, (w l : Real) * (a l : Real)
  have hW (x y : Fin d →₀ Nat) : W (x + y) = W x + W y := by
    simp [W, Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  have hprod (s : Finset ι) :
      ∀ a ∈ (s.prod f).support, W a ≤ ∑ i ∈ s, B i := by
    induction s using Finset.induction_on with
    | empty =>
        intro a ha
        have ha0 : a = 0 := by simpa using ha
        subst a
        simp [W]
    | @insert i s hi ih =>
        intro a ha
        rw [Finset.prod_insert hi] at ha
        have hmem : a ∈ (f i).support + (s.prod f).support :=
          MvPolynomial.support_mul _ _ ha
        rcases Finset.mem_add.mp hmem with ⟨x, hx, y, hy, hxy⟩
        subst a
        rw [hW, Finset.sum_insert hi]
        apply add_le_add
        · exact hweight i x hx
        · exact ih y hy
  intro a ha
  have h := hprod (Finset.univ : Finset ι) a (by simpa using ha)
  simpa [W] using h