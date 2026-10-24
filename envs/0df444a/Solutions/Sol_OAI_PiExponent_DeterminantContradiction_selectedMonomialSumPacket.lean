-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.selectedMonomialSumPacket
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:12:45.851959+00:00
-- url     : https://prove2.me/submissions/5b7563f9-1fef-4e40-9d69-788acc245c87

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

section

open MvPolynomial OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

namespace PiL13

lemma cases_self {m : ℕ} (f : Fin (m + 1) → ℕ) : (Fin.cases (f 0) (fun i => f i.succ) : Fin (m + 1) → ℕ) = f := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma packet_monomial {m : ℕ} (K : ℕ) (v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (f : Fin (m + 1) → ℕ) (ρ : InterpolationMatrix.Row K v0 θ w H) :
    truncatedPolynomialPacket K v0 θ w H r T (monomial (InterpolationMatrix.exponentVector f) 1) ρ =
      InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i)) ρ.1.val (ρ.2.1 0)
        (fun i => ρ.2.1 i.succ) (f 0) (fun i => f i.succ) := by
  unfold truncatedPolynomialPacket
  conv_lhs => rw [← cases_self f, ← cases_self ρ.2.1]
  exact PiL9.unscaled m r T ρ.1.val (f 0) (fun i => f i.succ) (fun i => ρ.2.1 i.succ) (ρ.2.1 0)

lemma packet_sum {m : ℕ} (K : ℕ) (v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    {ι : Type*} (s : Finset ι) (x : ι → ℂ) (P : ι → MvPolynomial (Fin (m + 1)) ℂ)
    (ρ : InterpolationMatrix.Row K v0 θ w H) :
    truncatedPolynomialPacket K v0 θ w H r T (∑ σ ∈ s, C (x σ) * P σ) ρ =
      ∑ σ ∈ s, x σ * truncatedPolynomialPacket K v0 θ w H r T (P σ) ρ := by
  unfold truncatedPolynomialPacket
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq, coeff_C_mul]

theorem sel_sum (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (x : Row d H → Complex) :
    ∀ rho : Row d H,
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
        (∑ sigma : Row d H,
          MvPolynomial.C (x sigma) *
            MvPolynomial.monomial
              (InterpolationMatrix.exponentVector (selection sigma).1) 1) rho =
      ∑ sigma : Row d H, (actualMinor d H selection) rho sigma * x sigma := by
  intro rho
  rw [packet_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [packet_monomial, mul_comm]
  rfl

theorem surj (nu : Real) (d : FixedData nu) (H : Real)
    (hM : Function.Surjective (actualMatrix d H).mulVecLin) :
    Function.Surjective
      (fun P : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
          P.val) := by
  classical
  intro y
  obtain ⟨x, hx⟩ := hM y
  let P : MvPolynomial (Fin (d.m + 1)) ℂ :=
    ∑ c : Column d H, C (x c) * monomial (InterpolationMatrix.exponentVector c.1) 1
  have hP : ∀ a ∈ P.support, ∑ i, InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : ℝ) ≤ H := by
    intro a ha
    have := MvPolynomial.support_sum ha
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at this
    obtain ⟨c, hc⟩ := this
    have hc' := MvPolynomial.support_mul _ _ hc
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Finset.mem_add.1 hc'
    have hb1' : b1 = 0 := by
      by_contra h; exact (mem_support_iff.1 hb1) (by rw [coeff_C, if_neg (Ne.symm h)])
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hb2
    subst hb1' hb2
    have := c.2
    simp only [realWeightedSimplex, Finset.mem_filter] at this
    simpa [InterpolationMatrix.exponentVector] using this.2
  refine ⟨⟨P, hP⟩, ?_⟩
  funext ρ
  simp only [P]
  rw [packet_sum]
  rw [← hx]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [packet_monomial, mul_comm]
  rfl

end PiL13

end

open OAI OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (x : Row d H → Complex) :
    ∀ rho : Row d H,
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
        (∑ sigma : Row d H,
          MvPolynomial.C (x sigma) *
            MvPolynomial.monomial
              (InterpolationMatrix.exponentVector (selection sigma).1) 1) rho =
      ∑ sigma : Row d H, (actualMinor d H selection) rho sigma * x sigma := by
  apply PiL13.sel_sum <;> assumption
