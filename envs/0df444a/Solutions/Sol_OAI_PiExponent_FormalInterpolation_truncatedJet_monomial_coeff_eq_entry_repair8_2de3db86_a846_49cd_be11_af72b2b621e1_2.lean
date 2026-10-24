-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.truncatedJet_monomial_coeff_eq_entry_repair8_2de3db86_a846_49cd_be11_af72b2b621e1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:01:14.435071+00:00
-- url     : https://prove2.me/submissions/395ecb7d-4cfa-443f-9ce8-4df9a2ec6e54

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib

section

open MvPolynomial OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace PiL9

variable {m : ℕ}

noncomputable def φ : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin m) (Polynomial ℂ) :=
  aeval (Fin.cases (C Polynomial.X) X)

lemma ev_cases (s : ℕ) (b : Fin m → ℕ) :
    InterpolationMatrix.exponentVector (Fin.cases s b : Fin (m + 1) → ℕ) =
      Finsupp.cons s (InterpolationMatrix.exponentVector b) := by
  ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [InterpolationMatrix.exponentVector]

lemma φ_monomial (s : ℕ) (b : Fin m →₀ ℕ) (c : ℂ) :
    φ (monomial (Finsupp.cons s b) c) = monomial b (Polynomial.C c * Polynomial.X ^ s) := by
  rw [φ, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.cases_zero, Fin.cases_succ, Finsupp.cons_zero, Finsupp.cons_succ,
    MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [C_mul, C_pow]; ring

lemma cons_eq_iff (u0 s : ℕ) (u' b : Fin m →₀ ℕ) :
    Finsupp.cons u0 u' = Finsupp.cons s b ↔ u0 = s ∧ u' = b := by
  constructor
  · intro h
    refine ⟨by simpa using congrArg (· 0) h, ?_⟩
    ext i; simpa using congrArg (· i.succ) h
  · rintro ⟨rfl, rfl⟩; rfl

lemma coeff_compat (p : MvPolynomial (Fin (m + 1)) ℂ) (s : ℕ) (b : Fin m →₀ ℕ) :
    p.coeff (Finsupp.cons s b) = ((φ p).coeff b).coeff s := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨u0, u', rfl⟩ : ∃ u0 u', u = Finsupp.cons u0 u' :=
      ⟨u 0, Finsupp.tail u, (Finsupp.cons_tail u).symm⟩
    simp only [φ_monomial, coeff_monomial, cons_eq_iff]
    by_cases hb : u' = b
    · subst hb
      simp only [and_true, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hs : u0 = s
      · simp [hs]
      · simp [hs, Ne.symm hs]
    · simp [hb]
  | add p q hp hq => simp [hp, hq]

lemma φ_aeval_poly (G : Polynomial ℂ) :
    φ (Polynomial.aeval (X 0 : MvPolynomial (Fin (m + 1)) ℂ) G) = C G := by
  rw [← Polynomial.aeval_algHom_apply]
  simp only [φ, aeval_X, Fin.cases_zero]
  rw [show (C Polynomial.X : MvPolynomial (Fin m) (Polynomial ℂ)) =
    algebraMap (Polynomial ℂ) _ Polynomial.X from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_X_left_apply]
  rfl

theorem gen (c : Fin m → ℂ) (G : Fin m → Polynomial ℂ) (s h : ℕ) (b a : Fin m → ℕ) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : ℂ))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((MvPolynomial.C ((1 + Polynomial.X) ^ h) *
      ∏ i, (MvPolynomial.C (Polynomial.C (c i) + G i) + MvPolynomial.X i) ^ a i :
        MvPolynomial (Fin m) (Polynomial ℂ)).coeff (InterpolationMatrix.exponentVector b)).coeff s := by
  rw [ev_cases, coeff_compat, ev_cases]
  congr 3
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ,
    map_mul, map_prod]
  simp only [Finsupp.cons_zero, Finsupp.cons_succ, Fin.cases_zero, Fin.cases_succ, map_pow, map_add,
    φ_aeval_poly, InterpolationMatrix.exponentVector]
  simp only [φ, aeval_X, Fin.cases_zero, Fin.cases_succ, map_one, aeval_C, map_add, map_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Finsupp.coe_equivFunOnFinite_symm, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

theorem entry_eq {m : Nat} (r : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (j s h : Nat) (b a : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      InterpolationMatrix.entry r G j s b h a :=
  gen (fun i => (j : ℂ) * r i) G s h b a

theorem unscaled (m : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (j h : Nat) (a b : Fin m → Nat) (s : Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((InterpolationMatrix.monomialImage r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j h a).coeff
      (InterpolationMatrix.exponentVector b)).coeff s :=
  gen (fun i => (j : ℂ) * r i) (fun i => InterpolationMatrix.truncatedLog (T i)) s h b a

theorem bridge (m : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (j h : Nat) (a b : Fin m → Nat) (s : Nat) (z : Complex) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.C z *
        MvPolynomial.monomial
          (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    z * ((InterpolationMatrix.monomialImage r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j h a).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by
  rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq, coeff_C_mul,
    unscaled]

end PiL9

end

open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    {m : Nat} (r : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (j s h : Nat) (b a : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      InterpolationMatrix.entry r G j s b h a := by
  apply PiL9.entry_eq <;> assumption
