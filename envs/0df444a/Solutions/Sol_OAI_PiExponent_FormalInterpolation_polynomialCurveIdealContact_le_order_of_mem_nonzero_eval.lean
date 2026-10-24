-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact_le_order_of_mem_nonzero_eval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:05:11.43898+00:00
-- url     : https://prove2.me/submissions/f784b91e-cf36-49e8-8f68-814514826f78

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_eval_order_nonneg
import Mathlib.Algebra.MvPolynomial.Eval

open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (f : MvPolynomial (Fin d) Complex)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hf : f ∈ I)
    (hne : MvPolynomial.aeval x f ≠ 0) :
    (polynomialCurveIdealContact nu x I : Real) ≤
      (polynomialCurveOrder nu (MvPolynomial.aeval x f) : Real) := by
  classical
  obtain ⟨k, hkval, hkorder⟩ :=
    polynomialCurve_eval_order_nonneg nu x f hchart hne
  unfold polynomialCurveIdealContact
  rw [if_pos hchart]
  have hmem : k ∈ {m : Nat | ∃ g : MvPolynomial (Fin d) Complex,
      g ∈ I ∧ nu.1 (MvPolynomial.aeval x g) = ((m : Int) : WithTop Int)} :=
    ⟨f, hf, hkval⟩
  have hle := Nat.sInf_le hmem
  rw [hkorder]
  exact_mod_cast hle