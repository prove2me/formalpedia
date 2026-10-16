-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_zero_of_simultaneousJetIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:43:24.561992+00:00
-- url     : https://prove2.me/submissions/a190e6e5-646e-495b-b19b-91b33e355a51

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.Tactic.Linarith

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

private def jetWeightedDegree {σ : Type*} [Fintype σ]
    (weight : σ → ℝ) (d : σ →₀ ℕ) : ℝ :=
  ∑ k, weight k * (d k : ℝ)

private def jetVanishesBelow {σ : Type*} [Fintype σ]
    (weight : σ → ℝ) (S : ℝ) (F : MvPowerSeries σ ℂ) : Prop :=
  ∀ d, jetWeightedDegree weight d < S → MvPowerSeries.coeff d F = 0

private theorem jetWeightedDegree_nonneg {σ : Type*} [Fintype σ]
    (weight : σ → ℝ) (hw : ∀ k, 0 ≤ weight k) (d : σ →₀ ℕ) :
    0 ≤ jetWeightedDegree weight d := by
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (Nat.cast_nonneg _))

private theorem jetWeightedDegree_add {σ : Type*} [Fintype σ]
    (weight : σ → ℝ) (b c : σ →₀ ℕ) :
    jetWeightedDegree weight (b + c) =
      jetWeightedDegree weight b + jetWeightedDegree weight c := by
  simp only [jetWeightedDegree, Finsupp.add_apply, Nat.cast_add, mul_add,
    Finset.sum_add_distrib]

private theorem jetVanishesBelow_zero_cutoff {σ : Type*} [Fintype σ]
    (weight : σ → ℝ) (hw : ∀ k, 0 ≤ weight k) (F : MvPowerSeries σ ℂ) :
    jetVanishesBelow weight 0 F := by
  intro d hd
  exact (not_lt_of_ge (jetWeightedDegree_nonneg weight hw d) hd).elim

-- Coefficient convolution adds the two strict weighted cutoffs.
private theorem jetVanishesBelow_mul {σ : Type*} [Fintype σ]
    (weight : σ → ℝ) (s t : ℝ) (F G : MvPowerSeries σ ℂ)
    (hF : jetVanishesBelow weight s F)
    (hG : jetVanishesBelow weight t G) :
    jetVanishesBelow weight (s + t) (F * G) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hbc : p.1 + p.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hdegree : jetWeightedDegree weight p.1 + jetWeightedDegree weight p.2 =
      jetWeightedDegree weight d := by
    rw [← jetWeightedDegree_add, hbc]
  by_cases hb : jetWeightedDegree weight p.1 < s
  · rw [hF p.1 hb, zero_mul]
  · have hc : jetWeightedDegree weight p.2 < t := by
      have hb' : s ≤ jetWeightedDegree weight p.1 := le_of_not_gt hb
      linarith
    rw [hG p.2 hc, mul_zero]

-- Arbitrary ring-homomorphic images of an ideal span inherit the cutoff.
private theorem jetVanishesBelow_span {σ A : Type*} [Fintype σ] [CommRing A]
    (weight : σ → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (f : A →+* MvPowerSeries σ ℂ) (S : ℝ) (g : Set A)
    (hg : ∀ x ∈ g, jetVanishesBelow weight S (f x))
    (Q : A) (hQ : Q ∈ Ideal.span g) :
    jetVanishesBelow weight S (f Q) := by
  refine Submodule.span_induction
    (p := fun x _ => jetVanishesBelow weight S (f x)) ?_ ?_ ?_ ?_ hQ
  · intro x hx
    exact hg x hx
  · intro d hd
    simp
  · intro x y hx hy ihx ihy d hd
    simp only [map_add, ihx d hd, ihy d hd, add_zero]
  · intro c x hx ihx
    have hmul := jetVanishesBelow_mul weight 0 S (f c) (f x)
      (jetVanishesBelow_zero_cutoff weight hw (f c)) ihx
    simpa only [zero_add, smul_eq_mul, map_mul] using hmul

-- This power induction applies to any ideal and any ring homomorphism.
private theorem jetVanishesBelow_ideal_pow {σ A : Type*} [Fintype σ] [CommRing A]
    (weight : σ → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (f : A →+* MvPowerSeries σ ℂ) (S : ℝ) (I : Ideal A)
    (hbase : ∀ Q ∈ I, jetVanishesBelow weight S (f Q))
    (n : ℕ) :
    ∀ P ∈ I ^ n, jetVanishesBelow weight ((n : ℝ) * S) (f P) := by
  induction n with
  | zero =>
      intro P hP
      simpa only [Nat.cast_zero, zero_mul] using
        jetVanishesBelow_zero_cutoff weight hw (f P)
  | succ n ih =>
      intro P hP
      rw [pow_succ] at hP
      refine Submodule.mul_induction_on hP ?_ ?_
      · intro x hx y hy
        have hmul := jetVanishesBelow_mul weight ((n : ℝ) * S) S (f x) (f y)
          (ih x hx) (hbase y hy)
        simpa only [map_mul, Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hmul
      · intro x y hx hy d hd
        simp only [map_add, hx d hd, hy d hd, add_zero]

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (S : ℝ)
    (hweights : ∀ k, 0 < InterpolationMatrix.rowWeights v0 theta w k)
    (hgen : ∀ (j : Fin K) (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ),
      (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) < S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet (fun k => (j.val : ℂ) * r k)
          ((jetCoordinate (fun k => (j.val : ℂ) * r k) T i) ^ e i)) = 0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (simultaneousJetIdeal K r T e) ^ n)
    (j : Fin K) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) < (n : ℝ) * S) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet (fun k => (j.val : ℂ) * r k) P) = 0 := by
  let weight : Fin (m + 1) → ℝ := InterpolationMatrix.rowWeights v0 theta w
  let c : Fin m → ℂ := fun k => (j.val : ℂ) * r k
  let f : MvPolynomial (Fin (m + 1)) ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
    (AdmissibleFormalInterpolation.formalJet c).toRingHom
  have hw : ∀ k, 0 ≤ weight k := fun k => le_of_lt (hweights k)
  have hbase : ∀ Q ∈ simultaneousJetIdeal K r T e,
      jetVanishesBelow weight S (f Q) := by
    intro Q hQ
    have hlocal : Q ∈ localJetIdeal c T e :=
      (show simultaneousJetIdeal K r T e ≤ localJetIdeal c T e from
        iInf_le (fun l : Fin K =>
          localJetIdeal (fun k => (l.val : ℂ) * r k) T e) j) hQ
    refine jetVanishesBelow_span weight hw f S
      (Set.range (fun i => jetCoordinate c T i ^ e i)) ?_ Q hlocal
    rintro x ⟨i, rfl⟩ d hd
    have hv := hgen j i (fun k => d k) hd
    have he : InterpolationMatrix.exponentVector (fun k => d k) = d :=
      Finsupp.equivFunOnFinite_symm_coe d
    rw [he] at hv
    exact hv
  have hvan := jetVanishesBelow_ideal_pow weight hw f S
    (simultaneousJetIdeal K r T e) hbase n P hP
  exact hvan (InterpolationMatrix.exponentVector a) ha