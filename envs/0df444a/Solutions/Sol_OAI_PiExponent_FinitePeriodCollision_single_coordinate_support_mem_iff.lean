-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:29:10.523343+00:00
-- url     : https://prove2.me/submissions/50c75a52-8cee-4825-83df-d39ea3202ad2

import Mathlib.Algebra.MvPolynomial.Basic

theorem solution
    {σ : Type} [DecidableEq σ] {R : Type} [CommSemiring R]
    (p : MvPolynomial σ R) (i : σ)
    (hsupport : ∀ (s : σ →₀ ℕ), p.coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) (n : ℕ) :
    n ∈ p.support.image (fun s => s i) ↔
      p.coeff (Finsupp.single i n) ≠ 0 := by
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨s, hs, hsi⟩
    have hcoeff : p.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hsingle : s = Finsupp.single i n := by
      ext j
      by_cases hj0 : s j = 0
      · by_cases hji : j = i
        · subst j
          simp [hsi, hj0]
        · simp [Finsupp.single_apply, hji, hj0]
      · have hji : j = i := hsupport s hcoeff j hj0
        subst j
        simp [hsi]
    simpa [hsingle] using hcoeff
  · intro hcoeff
    apply Finset.mem_image.mpr
    refine ⟨Finsupp.single i n, MvPolynomial.mem_support_iff.mpr hcoeff, ?_⟩
    simp