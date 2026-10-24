-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomialImage_substitution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:59:06.483292+00:00
-- url     : https://prove2.me/submissions/0217e307-c830-4459-b725-65b639291f12

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

lemma Φ_X0 {m : ℕ} : Φ m (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
  rw [Φ, MvPolynomial.aeval_X, Fin.cases_zero]

lemma Φ_Xs {m : ℕ} (i : Fin m) : Φ m (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  rw [Φ, MvPolynomial.aeval_X, Fin.cases_succ]

lemma Φ_C {m : ℕ} (z : ℂ) : Φ m (MvPolynomial.C z) = MvPolynomial.C (Polynomial.C z) := by
  rw [MvPolynomial.algHom_C]; rfl

/-- `Ψ` (written out as in the targets) is a right inverse of `Φ`. -/
lemma ΦΨ {m : ℕ} (P : MvPolynomial (Fin m) (Polynomial ℂ)) :
    Φ m (MvPolynomial.aeval
      (fun i : Fin m => (MvPolynomial.X (i.succ : Fin (m + 1)) :
        MvPolynomial (Fin (m + 1)) Complex))
      (MvPolynomial.map
        (show Polynomial Complex →+* MvPolynomial (Fin (m + 1)) Complex from
          (Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) :
              MvPolynomial (Fin (m + 1)) Complex)).toRingHom) P)) = P := by
  induction P using MvPolynomial.induction_on with
  | C p =>
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
    exact Φ_aeval_X0 p
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.map_X, MvPolynomial.aeval_X, Φ_Xs]

lemma ΨΦ_X {m : ℕ} (i : Fin (m + 1)) :
    MvPolynomial.aeval
      (fun i : Fin m => (MvPolynomial.X (i.succ : Fin (m + 1)) :
        MvPolynomial (Fin (m + 1)) Complex))
      (MvPolynomial.map
        (show Polynomial Complex →+* MvPolynomial (Fin (m + 1)) Complex from
          (Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) :
              MvPolynomial (Fin (m + 1)) Complex)).toRingHom) (Φ m (MvPolynomial.X i))) = MvPolynomial.X i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Φ_X0, MvPolynomial.map_C, MvPolynomial.aeval_C]
    simp
  · rw [Φ_Xs, MvPolynomial.map_X, MvPolynomial.aeval_X]

/-- `Ψ` is a left inverse of `Φ`. -/
lemma ΨΦ {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial.aeval
      (fun i : Fin m => (MvPolynomial.X (i.succ : Fin (m + 1)) :
        MvPolynomial (Fin (m + 1)) Complex))
      (MvPolynomial.map
        (show Polynomial Complex →+* MvPolynomial (Fin (m + 1)) Complex from
          (Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) :
              MvPolynomial (Fin (m + 1)) Complex)).toRingHom) (Φ m P)) = P := by
  induction P using MvPolynomial.induction_on with
  | C z =>
    rw [Φ_C, MvPolynomial.map_C, MvPolynomial.aeval_C]
    simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, ΨΦ_X]

lemma Φ_subst (m : Nat) (c : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (h : Nat) (a : Fin m → Nat) :
    Φ m (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : ℂ))) =
    MvPolynomial.C ((1 + Polynomial.X) ^ h) *
      ∏ i, (MvPolynomial.C (Polynomial.C (c i) + G i) + MvPolynomial.X i) ^ a i := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, ev_zero, ev_succ, map_pow, map_add, map_one,
    Φ_aeval_X0, Φ_X0, Φ_Xs, Φ_C]
  rw [← MvPolynomial.C_1, ← map_add, ← map_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  ring

end PXJet

noncomputable section
theorem solution
    {m : Nat} (r : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (j h : Nat) (a : Fin m → Nat) :
    MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X (0 : Fin (m + 1)))
        (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1))) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex)) =
    MvPolynomial.aeval
      (fun i : Fin m => (MvPolynomial.X (i.succ : Fin (m + 1)) :
        MvPolynomial (Fin (m + 1)) Complex))
      (MvPolynomial.map
        (show Polynomial Complex →+* MvPolynomial (Fin (m + 1)) Complex from
          (Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) :
              MvPolynomial (Fin (m + 1)) Complex)).toRingHom)
        (InterpolationMatrix.monomialImage r G j h a)) := by
  rw [← PXJet.ΨΦ (MvPolynomial.aeval _ _), PXJet.Φ_subst m (fun i => (j : Complex) * r i) G h a]
  rfl
end
