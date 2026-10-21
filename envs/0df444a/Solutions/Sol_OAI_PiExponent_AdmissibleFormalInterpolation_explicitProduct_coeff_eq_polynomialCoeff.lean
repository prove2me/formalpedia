-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.explicitProduct_coeff_eq_polynomialCoeff
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:40:32.388307+00:00
-- url     : https://prove2.me/submissions/c9597be1-1282-4d2c-b821-5bd6e5f1cdbb

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

noncomputable section

namespace ExplicitProductCoeff

open InterpolationMatrix

/-- Coefficient formula for `liftLogSeries`: only the coordinate of variable `0` matters. -/
lemma liftLogSeries_coeff_tail {m : ℕ} (D : PowerSeries ℂ) (α : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff α (liftLogSeries m D) =
      if Finsupp.tail α = 0 then PowerSeries.coeff (α 0) D else 0 := by
  have hcoeff : ∀ (k : ℕ) (x : Fin m →₀ ℕ),
      MvPowerSeries.coeff (Finsupp.cons k x) (liftLogSeries m D) =
        if x = 0 then PowerSeries.coeff k D else 0 := by
    intro k x
    have hfin : MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m D) =
        PowerSeries.map MvPowerSeries.C D := by
      simp [liftLogSeries]
    have h := MvPowerSeries.coeff_coeff_finSuccEquiv (liftLogSeries m D) (k := k) (x := x)
    rw [hfin, PowerSeries.coeff_map, MvPowerSeries.coeff_C] at h
    exact h.symm
  conv_lhs => rw [← Finsupp.cons_tail α]
  exact hcoeff (α 0) (Finsupp.tail α)

/-- `liftLogSeries` sends constants to constants. -/
lemma liftLogSeries_C {m : ℕ} (c : ℂ) :
    liftLogSeries m (PowerSeries.C c) = MvPowerSeries.C c := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  have h : MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m (PowerSeries.C c))
      = PowerSeries.map MvPowerSeries.C (PowerSeries.C c) := by
    simp [liftLogSeries]
  rw [h, PowerSeries.map_C]
  exact (MvPowerSeries.finSuccEquiv_C c).symm

/-- `liftLogSeries` sends `X` to `X 0`. -/
lemma liftLogSeries_X {m : ℕ} :
    liftLogSeries m (PowerSeries.X : PowerSeries ℂ) = MvPowerSeries.X 0 := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  have h : MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m (PowerSeries.X : PowerSeries ℂ))
      = PowerSeries.map MvPowerSeries.C (PowerSeries.X : PowerSeries ℂ) := by
    simp [liftLogSeries]
  rw [h, PowerSeries.map_X]
  exact (MvPowerSeries.finSuccEquiv_X_zero).symm

section

variable {m : ℕ}

/-- The polynomial `X i.succ ^ μ i` product is a monomial. -/
lemma prod_X_succ_eq_monomial (μ : Fin m →₀ ℕ) :
    (∏ i : Fin m, (MvPowerSeries.X i.succ : MvPowerSeries (Fin (m + 1)) ℂ) ^ (μ i))
      = MvPowerSeries.monomial (Finsupp.cons 0 μ) (1 : ℂ) := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_pow, Fin.prod_univ_succ]
  simp

/-- Ring hom sending a coefficient polynomial `p` to `p(X 0)`, and variables `X i` to `X i.succ`. -/
def psi (m : ℕ) : Polynomial ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
  (liftLogSeries m).comp Polynomial.coeToPowerSeries.ringHom

lemma psi_apply (p : Polynomial ℂ) : psi m p = liftLogSeries m (p : PowerSeries ℂ) := rfl

@[simp] lemma psi_Polynomial_C (c : ℂ) : psi m (Polynomial.C c) = MvPowerSeries.C c := by
  rw [psi_apply]
  rw [show ((Polynomial.C c : Polynomial ℂ) : PowerSeries ℂ) = PowerSeries.C c by simp]
  exact liftLogSeries_C c

@[simp] lemma psi_Polynomial_X : psi m (Polynomial.X : Polynomial ℂ) = MvPowerSeries.X 0 := by
  rw [psi_apply]
  rw [show ((Polynomial.X : Polynomial ℂ) : PowerSeries ℂ) = PowerSeries.X by simp]
  exact liftLogSeries_X

/-- The comparison ring hom. -/
def Phi (m : ℕ) : MvPolynomial (Fin m) (Polynomial ℂ) →+* MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.eval₂Hom (psi m) (fun i => MvPowerSeries.X i.succ)

@[simp] lemma Phi_C (p : Polynomial ℂ) : Phi m (MvPolynomial.C p) = psi m p := by
  simp [Phi]

@[simp] lemma Phi_X (i : Fin m) : Phi m (MvPolynomial.X i) = MvPowerSeries.X i.succ := by
  simp [Phi]

lemma Phi_monomial (μ : Fin m →₀ ℕ) (c : Polynomial ℂ) :
    Phi m (MvPolynomial.monomial μ c) =
      psi m c * ∏ i : Fin m, (MvPowerSeries.X i.succ : MvPowerSeries (Fin (m + 1)) ℂ) ^ (μ i) := by
  rw [Phi, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_pow]

end

section

variable {m : ℕ}

lemma psi_pow_one_add_X (m : ℕ) (h : ℕ) :
    psi m ((1 + Polynomial.X) ^ h) = (1 + MvPowerSeries.X 0) ^ h := by
  rw [map_pow, map_add, map_one, psi_Polynomial_X]

lemma Phi_factor (i : Fin m) (c : ℂ) (g : Polynomial ℂ) :
    Phi m (MvPolynomial.C (Polynomial.C c + g) + MvPolynomial.X i) =
      MvPowerSeries.C c + MvPowerSeries.X i.succ + liftLogSeries m (g : PowerSeries ℂ) := by
  rw [map_add, Phi_C, Phi_X, map_add, psi_Polynomial_C, psi_apply]
  abel

/-- The explicit product is the image of the monomial image under `Phi`. -/
lemma Phi_monomialImage (j : ℕ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : ℕ) (a : Fin m → ℕ) :
    Phi m (InterpolationMatrix.monomialImage r G j h a) =
      (1 + MvPowerSeries.X 0) ^ h *
        ∏ i, (MvPowerSeries.C ((j : ℂ) * r i) + MvPowerSeries.X i.succ +
          liftLogSeries m (G i : PowerSeries ℂ)) ^ a i := by
  rw [InterpolationMatrix.monomialImage, map_mul, map_prod]
  congr 1
  · rw [Phi_C]
    exact psi_pow_one_add_X m h
  · apply Finset.prod_congr rfl
    intro i _
    rw [map_pow]
    congr 1
    exact Phi_factor i ((j : ℂ) * r i) (G i)

/-- Subtracting `cons 0 μ` from `cons s ν` subtracts the tails. -/
lemma sub_cons_cons (ν : Fin m →₀ ℕ) (s : ℕ) (μ : Fin m →₀ ℕ) :
    Finsupp.cons s ν - Finsupp.cons (0 : ℕ) μ = Finsupp.cons s (ν - μ) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro k
    simp [Finsupp.tsub_apply]

/-- Coefficient of `liftLogSeries m c` times a product of powers of the variables `X i.succ`. -/
lemma coeff_cons_mul_prodX (c : PowerSeries ℂ) (μ : Fin m →₀ ℕ) (s : ℕ) (b : Fin m → ℕ) :
    MvPowerSeries.coeff (Finsupp.cons s (InterpolationMatrix.exponentVector b))
      (liftLogSeries m c *
        ∏ i : Fin m, (MvPowerSeries.X i.succ : MvPowerSeries (Fin (m + 1)) ℂ) ^ (μ i)) =
    if μ = InterpolationMatrix.exponentVector b then PowerSeries.coeff s c else 0 := by
  rw [prod_X_succ_eq_monomial, MvPowerSeries.coeff_mul_monomial]
  by_cases hμ : μ = InterpolationMatrix.exponentVector b
  · rw [if_pos hμ]
    have hle : Finsupp.cons (0 : ℕ) μ ≤
        Finsupp.cons s (InterpolationMatrix.exponentVector b) := by
      rw [hμ]
      apply Finsupp.le_def.mpr
      intro i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro k
        simp
    rw [if_pos hle, mul_one, sub_cons_cons, liftLogSeries_coeff_tail]
    simp only [Finsupp.tail_cons, Finsupp.cons_zero]
    rw [if_pos]
    rw [hμ, tsub_self]
  · rw [if_neg hμ]
    by_cases hle : Finsupp.cons (0 : ℕ) μ ≤
        Finsupp.cons s (InterpolationMatrix.exponentVector b)
    · rw [if_pos hle, mul_one, sub_cons_cons, liftLogSeries_coeff_tail]
      simp only [Finsupp.tail_cons, Finsupp.cons_zero]
      rw [if_neg]
      intro h
      have hle' : μ ≤ InterpolationMatrix.exponentVector b := fun i => by
        have hh := Finsupp.le_def.mp hle i.succ
        simpa using hh
      exact hμ (le_antisymm hle' (tsub_eq_zero_iff_le.mp h))
    · rw [if_neg hle]

/-- General coefficient identity for `Phi` on polynomials. -/
lemma coeff_Phi (P : MvPolynomial (Fin m) (Polynomial ℂ)) (s : ℕ) (b : Fin m → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector (Fin.cases s b)) (Phi m P) =
      (P.coeff (InterpolationMatrix.exponentVector b)).coeff s := by
  have hcons : InterpolationMatrix.exponentVector (Fin.cases s b) =
      Finsupp.cons s (InterpolationMatrix.exponentVector b) := rfl
  rw [hcons]
  calc MvPowerSeries.coeff (Finsupp.cons s (InterpolationMatrix.exponentVector b)) (Phi m P)
      = ∑ μ ∈ P.support, MvPowerSeries.coeff
          (Finsupp.cons s (InterpolationMatrix.exponentVector b))
          (Phi m (MvPolynomial.monomial μ (P.coeff μ))) := by
        conv_lhs => rw [P.as_sum]
        rw [map_sum, map_sum]
    _ = ∑ μ ∈ P.support,
          (if μ = InterpolationMatrix.exponentVector b then (P.coeff μ).coeff s else 0) := by
        apply Finset.sum_congr rfl
        intro μ _
        rw [Phi_monomial, psi_apply, coeff_cons_mul_prodX]
        simp
    _ = (P.coeff (InterpolationMatrix.exponentVector b)).coeff s := by
        by_cases hb : InterpolationMatrix.exponentVector b ∈ P.support
        · rw [Finset.sum_eq_single (InterpolationMatrix.exponentVector b)]
          · simp
          · intro μ _ hne
            simp [hne]
          · intro h
            exact absurd hb h
        · have hzero : P.coeff (InterpolationMatrix.exponentVector b) = 0 :=
            MvPolynomial.notMem_support_iff.mp hb
          rw [hzero, Polynomial.coeff_zero]
          apply Finset.sum_eq_zero
          intro μ hμ
          by_cases h : μ = InterpolationMatrix.exponentVector b
          · subst h
            exact absurd hμ hb
          · simp [h]

end

end ExplicitProductCoeff

open ExplicitProductCoeff

/-- The coefficient of the explicit formal-series product at the exponent vector with
distinguished coordinate `s` is the coefficient of `s` in the polynomial coefficient at `b`
of the monomial image. -/
theorem solution {m : ℕ} (j s : ℕ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : ℕ) (a b : Fin m → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector (Fin.cases s b))
        ((1 + MvPowerSeries.X 0) ^ h *
          ∏ i, (MvPowerSeries.C ((j : ℂ) * r i) + MvPowerSeries.X i.succ +
            liftLogSeries m (G i : PowerSeries ℂ)) ^ a i) =
      ((InterpolationMatrix.monomialImage r G j h a).coeff
        (InterpolationMatrix.exponentVector b)).coeff s := by
  rw [← Phi_monomialImage (m := m) j r G h a]
  exact coeff_Phi (m := m) _ s b
