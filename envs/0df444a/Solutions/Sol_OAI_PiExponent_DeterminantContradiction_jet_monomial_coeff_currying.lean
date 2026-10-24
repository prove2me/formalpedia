-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_currying
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:42:40.290595+00:00
-- url     : https://prove2.me/submissions/bef9c706-e2d5-4fc7-a821-4386675d3aaf

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent

namespace PXJet

noncomputable def Φ (m : ℕ) : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C Polynomial.X) (fun i => MvPolynomial.X i))

lemma ev_zero {m : ℕ} (s : ℕ) (b : Fin m → ℕ) :
    InterpolationMatrix.exponentVector (Fin.cases s b : Fin (m + 1) → ℕ) 0 = s := rfl

lemma ev_succ {m : ℕ} (s : ℕ) (b : Fin m → ℕ) (i : Fin m) :
    InterpolationMatrix.exponentVector (Fin.cases s b : Fin (m + 1) → ℕ) i.succ = b i := rfl

lemma Φ_monomial {m : ℕ} (e : Fin (m + 1) →₀ ℕ) (c : ℂ) :
    Φ m (MvPolynomial.monomial e c) =
      MvPolynomial.monomial (InterpolationMatrix.exponentVector (fun i => e i.succ))
        (Polynomial.monomial (e 0) c) := by
  rw [Φ, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [← MvPolynomial.C_pow, InterpolationMatrix.exponentVector,
    Finsupp.coe_equivFunOnFinite_symm, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_eq]
  rw [← mul_assoc, ← MvPolynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_Φ {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℂ) (s : ℕ) (b : Fin m → ℕ) :
    MvPolynomial.coeff (InterpolationMatrix.exponentVector (Fin.cases s b)) P =
      ((Φ m P).coeff (InterpolationMatrix.exponentVector b)).coeff s := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [Φ_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases he : e = InterpolationMatrix.exponentVector (Fin.cases s b)
    · subst he
      rw [if_pos rfl, if_pos, Polynomial.coeff_monomial, if_pos (ev_zero s b)]
      ext i; rfl
    · rw [if_neg he]
      by_cases ht : InterpolationMatrix.exponentVector (fun i => e i.succ) = InterpolationMatrix.exponentVector b
      · rw [if_pos ht, Polynomial.coeff_monomial, if_neg]
        intro h0
        apply he
        ext i
        refine Fin.cases ?_ (fun i => ?_) i
        · exact h0
        · have := congrArg (fun f => f i) ht
          simpa [InterpolationMatrix.exponentVector] using this
      · rw [if_neg ht]; rfl
  | add p q hp hq =>
    rw [MvPolynomial.coeff_add, hp, hq, map_add, MvPolynomial.coeff_add, Polynomial.coeff_add]

lemma Φ_aeval_X0 {m : ℕ} (G : Polynomial ℂ) :
    Φ m (Polynomial.aeval (MvPolynomial.X 0) G) = MvPolynomial.C G := by
  rw [← Polynomial.aeval_algHom_apply, Φ, MvPolynomial.aeval_X, Fin.cases_zero]
  rw [show (MvPolynomial.C Polynomial.X : MvPolynomial (Fin m) (Polynomial ℂ))
      = algebraMap (Polynomial ℂ) (MvPolynomial (Fin m) (Polynomial ℂ)) Polynomial.X from rfl,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rfl

theorem jet_general (m : Nat) (c : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (h : Nat) (a : Fin m → Nat) (s : Nat) (b : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((MvPolynomial.C ((1 + Polynomial.X) ^ h) *
      ∏ i, (MvPolynomial.C (Polynomial.C (c i) + G i) + MvPolynomial.X i) ^ a i).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by
  rw [coeff_Φ]
  congr 2
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, ev_zero, ev_succ, map_pow, map_add, map_one,
    Φ_aeval_X0]
  have h0 : Φ m (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
    rw [Φ, MvPolynomial.aeval_X, Fin.cases_zero]
  have hs : ∀ i : Fin m, Φ m (MvPolynomial.X i.succ) = MvPolynomial.X i := by
    intro i; rw [Φ, MvPolynomial.aeval_X, Fin.cases_succ]
  have hc : ∀ z : ℂ, Φ m (MvPolynomial.C z) = MvPolynomial.C (Polynomial.C z) := by
    intro z; rw [MvPolynomial.algHom_C]; rfl
  simp only [h0, hs, hc]
  rw [← MvPolynomial.C_1, ← map_add, ← map_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  ring

end PXJet

open OAI.PiExponent.FormalInterpolation in
theorem solution
    (m : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (j h : Nat) (a b : Fin m → Nat) (s : Nat) :
    (MvPolynomial.coeff (InterpolationMatrix.exponentVector (Fin.cases s b))
      (∏ x : Fin (m + 1),
        (Fin.cases (1 + MvPolynomial.X 0)
          (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
            Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
              (InterpolationMatrix.truncatedLog (T i))) x) ^
          (Fin.cases h a x))) =
    ((MvPolynomial.coeff (InterpolationMatrix.exponentVector b)
      (MvPolynomial.C ((1 + Polynomial.X) ^ h) *
        ∏ x : Fin m,
          (MvPolynomial.C (Polynomial.C ((j : Complex) * r x) +
              InterpolationMatrix.truncatedLog (T x)) +
            MvPolynomial.X x) ^ a x)).coeff s) := by
  have key := PXJet.jet_general m (fun i => (j : Complex) * r i)
    (fun i => InterpolationMatrix.truncatedLog (T i)) h a s b
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _)] at key
  simp only [Polynomial.aeval_def, MvPolynomial.algebraMap_eq, InterpolationMatrix.exponentVector,
    Finsupp.coe_equivFunOnFinite_symm] at key
  simp only [InterpolationMatrix.exponentVector] at key ⊢
  convert key using 4
