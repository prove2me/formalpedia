-- Prove2me | solution 1 for MvPowerSeries.coeff_polynomial_algHom_monomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:14:41.725104+00:00
-- url     : https://prove2.me/submissions/f6ba258e-6e6e-49ad-9c63-d10b550ae604

import Mathlib
import Mathlib.RingTheory.MvPowerSeries.Basic

theorem pie_agree_mul {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (p q : MvPolynomial τ R)
    (hp : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F p) = MvPowerSeries.coeff b (G p))
    (hq : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F q) = MvPowerSeries.coeff b (G q)) :
    ∀ a : σ →₀ ℕ, a j < T →
    MvPowerSeries.coeff a (F (p * q)) = MvPowerSeries.coeff a (G (p * q)) := by
  classical
  intro a ha
  rw [show F (p * q) = F p * F q from map_mul F p q, show G (p * q) = G p * G q from map_mul G p q,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 : x.1 j < T := by
    have := congrArg (fun f => f j) hx
    simp only [Finsupp.add_apply] at this
    omega
  have h2 : x.2 j < T := by
    have := congrArg (fun f => f j) hx
    simp only [Finsupp.add_apply] at this
    omega
  rw [hp _ h1, hq _ h2]

theorem solution
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (h : ∀ (i : τ) (b : σ →₀ ℕ), b j < T →
      MvPowerSeries.coeff b (F (MvPolynomial.X i)) =
        MvPowerSeries.coeff b (G (MvPolynomial.X i)))
    (s : τ →₀ ℕ) (r : R) (a : σ →₀ ℕ) (ha : a j < T) :
    MvPowerSeries.coeff a (F (MvPolynomial.monomial s r)) =
      MvPowerSeries.coeff a (G (MvPolynomial.monomial s r)) := by
  classical
  let A : MvPolynomial τ R → Prop := fun p => ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F p) = MvPowerSeries.coeff b (G p)
  have hC : ∀ c : R, A (MvPolynomial.C c) := by
    intro c b _
    have hF : F (MvPolynomial.C c) = algebraMap R _ c := by
      rw [← MvPolynomial.algebraMap_eq]; exact F.commutes c
    have hG : G (MvPolynomial.C c) = algebraMap R _ c := by
      rw [← MvPolynomial.algebraMap_eq]; exact G.commutes c
    rw [hF, hG]
  have hmul : ∀ p q, A p → A q → A (p * q) := fun p q hp hq => pie_agree_mul F G j T p q hp hq
  have hpow : ∀ (i : τ) (n : ℕ), A (MvPolynomial.X i ^ n) := by
    intro i n
    induction n with
    | zero => simpa using hC 1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih (h i)
  have : A (MvPolynomial.monomial s r) := by
    rw [MvPolynomial.monomial_eq]
    refine hmul _ _ (hC r) ?_
    unfold Finsupp.prod
    refine Finset.prod_induction _ A (fun p q hp hq => hmul p q hp hq) ?_ (fun i _ => hpow i (s i))
    simpa using hC 1
  exact this a ha
