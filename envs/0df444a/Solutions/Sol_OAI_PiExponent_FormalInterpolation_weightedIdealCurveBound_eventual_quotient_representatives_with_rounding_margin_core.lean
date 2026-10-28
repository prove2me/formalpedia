-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives_with_rounding_margin_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:53:58.982826+00:00
-- url     : https://prove2.me/submissions/512fa8b3-d4a4-4aad-bbbc-512445bd5e10
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_asymptotic_representatives
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (a : Rat) (ha : rho < a) :
    ∃ c : Rat, rho < c ∧ c < a ∧
      ∃ N : Nat, ∀ k : Nat, N ≤ k →
        (∀ i, (k : Real) * ((a - c : Rat) : Real) > (w i : Real)) →
        ∀ P : MvPolynomial (Fin d) Complex,
          ∃ R : MvPolynomial (Fin d) Complex,
            P - R ∈ I ^ k ∧
            ∀ v ∈ R.support,
              (∑ j, (w j : Real) * (v j : Real)) ≤ (k : Real) * (c : Real) := by
  classical
  -- Strictly positive rational gap.
  have hgapRat : (0 : Rat) < a - rho := sub_pos.mpr ha
  -- Use asymptotic at rate rho + (a-rho)/3, then target c = rho + 2(a-rho)/3.
  set delta : Rat := a - rho
  set epsRat : Rat := delta / 3
  set c : Rat := rho + 2 * epsRat
  have hepsRat_pos : (0 : Rat) < epsRat := by
    dsimp [epsRat, delta]; exact div_pos hgapRat (by norm_num)
  have hc_gt : rho < c := by
    dsimp [c]; linarith [hepsRat_pos]
  have hc_lt : c < a := by
    dsimp [c, epsRat, delta]
    have h3 : (0 : Rat) < 3 := by norm_num
    have h2eps : (2 : Rat) * (delta / 3) < delta := by
      rw [show (2 : Rat) * (delta / 3) = (2 * delta) / 3 by ring, div_lt_iff₀ h3]
      nlinarith [hgapRat]
    nlinarith [h2eps]
  have heps : (0 : Real) < (epsRat : Real) := by exact_mod_cast hepsRat_pos
  obtain ⟨C, hC⟩ :=
    weightedIdealCurveBound_asymptotic_representatives
      I hfinite w hw rho hrho hcurve (epsRat : Real) heps
  -- Choose N so that C ≤ N * epsRat (as reals), and N ≥ 1.
  obtain ⟨N0, hN0⟩ := exists_nat_ge ((C : Real) / (epsRat : Real))
  set N : Nat := max N0 1
  refine ⟨c, hc_gt, hc_lt, N, ?_⟩
  intro k hk _margin P
  obtain ⟨R, hRmem, hRwt⟩ := hC k P
  refine ⟨R, hRmem, ?_⟩
  intro v hv
  have hbound := hRwt v hv
  -- hbound : wt ≤ k*(rho+eps) + C
  -- Need wt ≤ k*c = k*(rho+2*eps)
  have hgapR : (0 : Real) < (epsRat : Real) := heps
  have hkN : (N0 : Real) ≤ (k : Real) := by
    exact_mod_cast (le_trans (le_max_left N0 1) hk)
  have hC_le : (C : Real) ≤ (k : Real) * (epsRat : Real) := by
    have hdiv := hN0
    -- N0 ≥ C/eps ⇒ N0*eps ≥ C
    have heps0 : (0 : Real) < (epsRat : Real) := hgapR
    have : (C : Real) / (epsRat : Real) ≤ (N0 : Real) := hdiv
    rw [div_le_iff₀ heps0] at this
    exact this.trans (mul_le_mul_of_nonneg_right hkN (le_of_lt heps0))
  -- rho+eps + eps = rho+2eps = c as reals
  have hcR : ((c : Rat) : Real) = (rho : Real) + (epsRat : Real) + (epsRat : Real) := by
    dsimp [c, epsRat]
    push_cast
    ring
  have : (∑ j, (w j : Real) * (v j : Real)) ≤
      (k : Real) * ((rho : Real) + (epsRat : Real) + (epsRat : Real)) := by
    have h1 : (∑ j, (w j : Real) * (v j : Real)) ≤
        (k : Real) * ((rho : Real) + (epsRat : Real)) + (C : Real) := hbound
    have h2 : (k : Real) * ((rho : Real) + (epsRat : Real)) + (C : Real) ≤
        (k : Real) * ((rho : Real) + (epsRat : Real) + (epsRat : Real)) := by
      nlinarith [hC_le]
    exact h1.trans h2
  simpa [hcR] using this
