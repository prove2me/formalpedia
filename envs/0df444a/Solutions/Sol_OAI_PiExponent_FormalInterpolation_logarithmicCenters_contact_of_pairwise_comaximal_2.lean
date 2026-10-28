-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.logarithmicCenters_contact_of_pairwise_comaximal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:27:30.420204+00:00
-- url     : https://prove2.me/submissions/edcddada-acdb-443a-8008-8b282659f65c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_contact_product_eq_sum_of_affine_contacts
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_pairwise_comaximal_positive_contact_exclusive
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_positive_sum_unique_positive_term_v2
import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {K d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hcop : ∀ j k : Fin K, j ≠ k → IsCoprime (I j) (I k))
    (hcontact : 0 < (polynomialCurveIdealContact nu x (∏ j, I j) : Real)) :
    ∃ j : Fin K,
      0 < (polynomialCurveIdealContact nu x (I j) : Real) ∧
      (polynomialCurveIdealContact nu x (I j) : Real) =
        (polynomialCurveIdealContact nu x (∏ j, I j) : Real) := by
  classical
  have hbranch : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i) := by
    by_contra h
    push_neg at h
    have hzero : polynomialCurveIdealContact nu x (∏ j, I j) = 0 := by
      simp [polynomialCurveIdealContact, h]
    rw [hzero] at hcontact
    norm_num at hcontact
  have hsum :=
    OAI.PiExponent.FormalInterpolation.contact_product_eq_sum_of_affine_contacts
      (nu := nu) (x := x) (I := I) hbranch
  have hunique :=
    OAI.PiExponent.FormalInterpolation.pairwise_comaximal_positive_contact_exclusive
      (nu := nu) (x := x) (I := I) hbranch hcop
  have hsum_pos : 0 < ∑ j, polynomialCurveIdealContact nu x (I j) := by
    rw [← hsum]
    exact_mod_cast hcontact
  have hselect :=
    OAI.PiExponent.FormalInterpolation.positive_sum_unique_positive_term_v2
      (f := fun j : Fin K => polynomialCurveIdealContact nu x (I j))
      (hunique := hunique) (hsum := hsum_pos)
  obtain ⟨j, hjpos, hjeq⟩ := hselect
  refine ⟨j, ?_, ?_⟩
  · exact_mod_cast hjpos
  · exact_mod_cast hjeq.trans hsum.symm