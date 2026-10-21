-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.coordinate_factor_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:01:56.826418+00:00
-- url     : https://prove2.me/submissions/d55f36fc-a76b-4fec-b5be-922829408eb8

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Algebra.MvPolynomial.Variables

open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (a : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    ∀ (i : Fin m) (s : Fin m →₀ ℕ),
      ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff s ≠ 0 →
        ∀ j : Fin m, s j ≠ 0 → j = i := by
  classical
  intro i s hs j hsj
  let p : MvPolynomial (Fin m) (PowerSeries ℂ) :=
    (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i
  have hsupport : s ∈ p.support := by
    change p.coeff s ≠ 0 at hs
    exact Finsupp.mem_support_iff.mpr hs
  have hjvars : j ∈ p.vars :=
    (MvPolynomial.mem_vars_iff_mem_support j).mpr
      ⟨s, hsupport, Finsupp.mem_support_iff.mpr hsj⟩
  have hjbase : j ∈
      (MvPolynomial.C (b i) + MvPolynomial.X i :
        MvPolynomial (Fin m) (PowerSeries ℂ)).vars :=
    (MvPolynomial.vars_pow (MvPolynomial.C (b i) + MvPolynomial.X i) (a i)) hjvars
  have hjunion :=
    (MvPolynomial.vars_add_subset
      (MvPolynomial.C (b i) : MvPolynomial (Fin m) (PowerSeries ℂ))
      (MvPolynomial.X i)) hjbase
  simpa using hjunion