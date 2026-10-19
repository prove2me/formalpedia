-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_power_membership_iff_polynomialJet_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:24:42.207401+00:00
-- url     : https://prove2.me/submissions/962b0b93-72a9-4bd6-b0ec-45a0de42f148

import Mathlib
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

noncomputable def pieJinv {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (jetCoordinate c T)

theorem pie_eval₂_alg {m : ℕ} (f : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ)
    (x : MvPolynomial (Fin (m + 1)) ℂ) (p : Polynomial ℂ) :
    f (Polynomial.eval₂ MvPolynomial.C x p) = Polynomial.eval₂ MvPolynomial.C (f x) p := by
  have := (Polynomial.aeval_algHom_apply f x p).symm
  simpa [Polynomial.aeval_def, MvPolynomial.algebraMap_eq] using this

theorem pie_J_jc {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin (m + 1)) :
    polynomialJet c T (jetCoordinate c T i) = MvPolynomial.X i := by
  have h0 : polynomialJet c T (MvPolynomial.X 0 - 1) = MvPolynomial.X 0 := by
    simp [polynomialJet]
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa [jetCoordinate] using h0
  · simp only [jetCoordinate, Fin.cases_succ, map_sub, pie_eval₂_alg, h0]
    simp [polynomialJet]
    ring

theorem pie_Jinv_J {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin (m + 1)) :
    pieJinv c T (polynomialJet c T (MvPolynomial.X i)) = MvPolynomial.X i := by
  have h0 : pieJinv c T (MvPolynomial.X 0) = MvPolynomial.X 0 - 1 := by
    simp [pieJinv, jetCoordinate]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [polynomialJet, pieJinv, jetCoordinate]
  · simp only [polynomialJet, MvPolynomial.aeval_X, Fin.cases_succ, map_add, pie_eval₂_alg, h0]
    simp [pieJinv, jetCoordinate]
    ring

noncomputable def pieJeq {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) :
    MvPolynomial (Fin (m + 1)) ℂ ≃ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
  AlgEquiv.ofAlgHom (polynomialJet c T) (pieJinv c T)
    (MvPolynomial.algHom_ext (fun i => by
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      simp only [pieJinv, MvPolynomial.aeval_X]; exact pie_J_jc c T i))
    (MvPolynomial.algHom_ext (fun i => by
      simp only [AlgHom.comp_apply, AlgHom.id_apply]; exact pie_Jinv_J c T i))

theorem pie_map_local {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) :
    (localJetIdeal c T e).map (pieJeq c T) =
      Ideal.span (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ e i)) := by
  rw [localJetIdeal, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext i
  simp [pieJeq, pie_J_jc]

theorem pie_mem_iff {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) (k : ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    P ∈ localJetIdeal c T e ^ k ↔
      polynomialJet c T P ∈
        Ideal.span (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ e i)) ^ k := by
  rw [← pie_map_local, ← Ideal.map_pow]
  change _ ↔ (pieJeq c T) P ∈ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h; exact ⟨P, h, rfl⟩
  · rintro ⟨Q, hQ, hQP⟩
    have := (pieJeq c T).injective hQP
    rw [← this]; exact hQ
theorem pie_divsum_single {n : ℕ} (e : Fin n → ℕ) (he : ∀ i, 0 < e i)
    (u : Fin n →₀ ℕ) (i : Fin n) :
    ∑ j, (u + Finsupp.single i (e i)) j / e j = (∑ j, u j / e j) + 1 := by
  have : ∀ j, (u + Finsupp.single i (e i)) j / e j = u j / e j + if i = j then 1 else 0 := by
    intro j
    by_cases h : i = j
    · subst h; simp [Nat.add_div_right _ (he i)]
    · simp [Finsupp.single_apply, h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem pie_monomial_pow_le {n : ℕ} (e : Fin n → ℕ) (he : ∀ i, 0 < e i) (k : ℕ) :
    Ideal.span (Set.range (fun i : Fin n => MvPolynomial.X (R := ℂ) i ^ e i)) ^ k ≤
      Ideal.span ((fun s => MvPolynomial.monomial s (1 : ℂ)) ''
        {u : Fin n →₀ ℕ | k ≤ ∑ i, u i / e i}) := by
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
    apply Ideal.subset_span
    exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨a, ⟨u, hu, rfl⟩, b, ⟨i, rfl⟩, rfl⟩
    apply Ideal.subset_span
    refine ⟨u + Finsupp.single i (e i), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq] at hu ⊢
      rw [pie_divsum_single e he]; omega
    · simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]

theorem pie_monomial_le_pow {n : ℕ} (e : Fin n → ℕ) (k : ℕ) :
    Ideal.span ((fun s => MvPolynomial.monomial s (1 : ℂ)) ''
        {u : Fin n →₀ ℕ | k ≤ ∑ i, u i / e i}) ≤
    Ideal.span (Set.range (fun i : Fin n => MvPolynomial.X (R := ℂ) i ^ e i)) ^ k := by
  set M := Ideal.span (Set.range (fun i : Fin n => MvPolynomial.X (R := ℂ) i ^ e i))
  rw [Ideal.span_le]
  rintro _ ⟨u, hu, rfl⟩
  simp only [Set.mem_ofPred_eq] at hu
  have hdecomp : MvPolynomial.monomial u (1 : ℂ) =
      (∏ i, (MvPolynomial.X i ^ e i) ^ (u i / e i)) * ∏ i, MvPolynomial.X i ^ (u i % e i) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _), ← Finset.prod_mul_distrib]
    simp only [map_one, one_mul, ← pow_mul, ← pow_add]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Nat.div_add_mod]
  show MvPolynomial.monomial u (1 : ℂ) ∈ M ^ k
  rw [hdecomp]
  apply Ideal.mul_mem_right
  apply Ideal.pow_le_pow_right hu
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _)

theorem pie_monomial_pow_iff {n : ℕ} (e : Fin n → ℕ) (he : ∀ i, 0 < e i) (k : ℕ)
    (Q : MvPolynomial (Fin n) ℂ) :
    Q ∈ Ideal.span (Set.range (fun i : Fin n => MvPolynomial.X (R := ℂ) i ^ e i)) ^ k ↔
      ∀ u : Fin n →₀ ℕ, (∑ i, u i / e i) < k → MvPolynomial.coeff u Q = 0 := by
  rw [le_antisymm (pie_monomial_pow_le e he k) (pie_monomial_le_pow e k),
    MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h u hu
    by_contra hc
    obtain ⟨s, hs, hsu⟩ := h u (MvPolynomial.mem_support_iff.mpr hc)
    simp only [Set.mem_ofPred_eq] at hs
    have : ∑ i, s i / e i ≤ ∑ i, u i / e i :=
      Finset.sum_le_sum (fun i _ => Nat.div_le_div_right (hsu i))
    omega
  · intro h u hu
    refine ⟨u, ?_, le_rfl⟩
    by_contra hc
    simp only [Set.mem_ofPred_eq, not_le] at hc
    exact MvPolynomial.mem_support_iff.mp hu (h u hc)

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    (k : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    P ∈ (localJetIdeal c T e) ^ k ↔
      ∀ u : Fin (m + 1) →₀ ℕ,
        (∑ i, u i / e i) < k →
          MvPolynomial.coeff u (polynomialJet c T P) = 0 := by
  rw [pie_mem_iff, pie_monomial_pow_iff e he]
