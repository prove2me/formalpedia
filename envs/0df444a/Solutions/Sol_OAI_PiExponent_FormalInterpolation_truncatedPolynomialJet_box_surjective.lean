-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_box_surjective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:20:30.306316+00:00
-- url     : https://prove2.me/submissions/241b03f3-65c6-4aca-a940-69cec0dd0618

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.FormalInterpolation
theorem solution
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (S : Fin (m + 1) → Nat)
    (g : {a : Fin (m + 1) → Nat // ∀ i, a i < S i} → Complex) :
    ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
      ∀ a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i},
        (truncatedPolynomialJet c T Q).coeff
          (InterpolationMatrix.exponentVector a.1) = g a := by
  classical
  set J := truncatedPolynomialJet c T
  have hX0 : J (MvPolynomial.X 0 - 1) = MvPolynomial.X 0 := by
    simp [J, truncatedPolynomialJet]
  have hrange : J.range = ⊤ := by
    rw [eq_top_iff, ← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · exact ⟨_, hX0⟩
    · refine ⟨MvPolynomial.X i.succ - MvPolynomial.C (c i) -
        Polynomial.aeval (MvPolynomial.X 0 - 1) (InterpolationMatrix.truncatedLog (T i)), ?_⟩
      have hL : J (Polynomial.aeval (MvPolynomial.X 0 - 1) (InterpolationMatrix.truncatedLog (T i)))
          = Polynomial.aeval (MvPolynomial.X 0) (InterpolationMatrix.truncatedLog (T i)) := by
        rw [← Polynomial.aeval_algHom_apply, hX0]
      change J _ = _
      rw [map_sub, map_sub, hL]
      simp [J, truncatedPolynomialJet]
      ring
  have hsurj : Function.Surjective J := by
    intro p
    have : p ∈ J.range := by rw [hrange]; trivial
    exact this
  let g' : (Fin (m + 1) → ℕ) → ℂ := fun a => if h : ∀ i, a i < S i then g ⟨a, h⟩ else 0
  let G : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ a ∈ Fintype.piFinset (fun i => Finset.range (S i)),
      MvPolynomial.monomial (InterpolationMatrix.exponentVector a) (g' a)
  obtain ⟨Q, hQ⟩ := hsurj G
  refine ⟨Q, fun a => ?_⟩
  rw [hQ]
  simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a.1]
  · simp [g', a.2]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    funext i
    have := DFunLike.congr_fun h i
    simpa [InterpolationMatrix.exponentVector] using this
  · intro h
    exfalso; apply h
    simp [Fintype.mem_piFinset, a.2]
