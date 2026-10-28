-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.weighted_curve_bound_finite_initial_power_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:53:10.639984+00:00
-- url     : https://prove2.me/submissions/4fa57d72-3deb-42cf-8933-dbfabd09fefe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_finite_weighted_power_certificate
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_nonzero_certificate_cutoff_is_rational
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scale_rational_weighted_power_certificate
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      ∃ n : Nat, ∃ f : Fin n → MvPolynomial (Fin d) Complex,
        (∀ j, f j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (f j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) ∧
        ∀ i : Fin d, ∃ e : Nat,
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun j =>
              MvPolynomial.weightedHomogeneousComponent w q (f j))) := by
  by_cases hd : d = 0
  · subst d
    obtain ⟨s, hs⟩ := exists_nat_gt (2 / eps)
    have hsmall : 2 < (s : Real) * eps :=
      (div_lt_iff₀ heps).mp hs
    have hsR : 0 < (s : Real) := by nlinarith [heps]
    have hrhoR : 0 ≤ (rho : Real) := by exact_mod_cast hrho
    have hbound : ((1 : Rat) : Real) + 1 < (s : Real) * ((rho : Real) + eps) := by
      calc
        ((1 : Rat) : Real) + 1 = 2 := by norm_num
        _ < (s : Real) * eps := hsmall
        _ ≤ (s : Real) * ((rho : Real) + eps) := by
          nlinarith [mul_nonneg (le_of_lt hsR) hrhoR]
    refine ⟨s, ?_, (1 : Rat), by norm_num, hbound, 0,
      (fun j => Fin.elim0 j), ?_, ?_, ?_⟩
    · exact_mod_cast hsR
    · intro j
      exact Fin.elim0 j
    · intro j a ha
      exact Fin.elim0 j
    · intro i
      exact Fin.elim0 i
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    obtain ⟨s, hs, D, hD, hDR, n, f, hf, hweight, hgen⟩ :=
      weighted_curve_bound_gives_finite_weighted_power_certificate
        I hfinite w hw rho hrho hcurve ((rho : Real) + eps / 2) (by
          have hrhoR : 0 ≤ (rho : Real) := by exact_mod_cast hrho
          linarith)
    have hDtarget : D < (s : Real) * ((rho : Real) + eps) := by
      calc
        D < (s : Real) * ((rho : Real) + eps / 2) := hDR
        _ < (s : Real) * ((rho : Real) + eps) := by
          have hsR : 0 < (s : Real) := by exact_mod_cast hs
          nlinarith [mul_pos hsR (show 0 < eps / 2 by linarith)]
    obtain ⟨r, hr⟩ :=
      OAI.PiExponent.FormalInterpolation.nonzero_certificate_cutoff_is_rational
        hdpos w D n f hgen
    exact
      OAI.PiExponent.FormalInterpolation.scale_rational_weighted_power_certificate
        I w ((rho : Real) + eps) s hs D hD hDtarget r hr n f hf hweight hgen