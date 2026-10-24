-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_sections_exact_degree
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:01:38.416967+00:00
-- url     : https://prove2.me/submissions/67679329-fe7d-4590-9a46-9f73f6e4852e

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

/-- ψ : x ↦ 1, y ↦ Y -/
noncomputable def D3psi : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval ![1, Polynomial.X]

noncomputable def D3ev : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval ![1, 0]

lemma D3_ev_eq (g : MvPolynomial (Fin 2) ℂ) : (D3psi g).eval 0 = D3ev g := by
  have : (Polynomial.evalRingHom (0:ℂ)).comp (D3psi : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ)
      = (D3ev : MvPolynomial (Fin 2) ℂ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [D3psi, D3ev]
    · intro i; fin_cases i <;> simp [D3psi, D3ev]
  exact congrArg (fun f => f g) this

lemma D3_pow_dvd (s : ℕ) (g : MvPolynomial (Fin 2) ℂ) (hg : g ∈ (RingHom.ker D3ev) ^ s) :
    Polynomial.X ^ s ∣ D3psi g := by
  have h1 : Ideal.map (D3psi : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ) (RingHom.ker D3ev)
      ≤ Ideal.span {Polynomial.X} := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    simpa [D3_ev_eq] using hf
  have h2 := Ideal.mem_map_of_mem (D3psi : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ) hg
  rw [Ideal.map_pow] at h2
  have h3 := Ideal.pow_right_mono h1 s h2
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3

lemma D3_coeff (g : MvPolynomial (Fin 2) ℂ) (k : ℕ)
    (hsupp : ∀ a ∈ g.support, (a 0 : ℝ) + 2 * (a 1 : ℝ) ≤ 2 * k) :
    (D3psi g).coeff k = g.coeff (Finsupp.single 1 k) := by
  conv_lhs => rw [g.as_sum]
  simp only [map_sum, D3psi, MvPolynomial.aeval_monomial, Finsupp.prod_pow, Fin.prod_univ_two,
    Polynomial.finsetSum_coeff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (Finsupp.single 1 k)]
  · simp
  · intro a ha hne
    rw [if_neg]
    intro hk
    apply hne
    have h := hsupp a ha
    have h0 : a 0 = 0 := by
      subst hk; have : (a 0 : ℝ) ≤ 0 := by linarith
      exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le _)
    ext i; fin_cases i <;> simp [h0, hk]
  · intro h
    simp [MvPolynomial.notMem_support_iff.mp h]

theorem solution : ¬ (∀ {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (eps : Real) (heps : 0 < eps)
    (hsections : ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span {h : MvPolynomial (Fin d) Complex |
          ∃ g : MvPolynomial (Fin d) Complex,
            g ∈ I ^ s ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ (B : Real)) ∧
            ∃ q : Rat, (q : Real) ≤ (B : Real) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) q g}),
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * ((rho : Real) + eps) ∧
      0 < D ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span {h : MvPolynomial (Fin d) Complex |
          ∃ g : MvPolynomial (Fin d) Complex,
            g ∈ I ^ s ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
            h = MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) g}) := by
  intro H
  let w : Fin 2 → ℚ := ![1, 2]
  have hw : ∀ i, 0 < (w i : ℝ) := by intro i; fin_cases i <;> simp [w]
  have hsurj : Function.Surjective D3ev := fun c => ⟨MvPolynomial.C c, by simp [D3ev]⟩
  have hfin : Module.Finite ℂ (MvPolynomial (Fin 2) ℂ ⧸ RingHom.ker D3ev) :=
    Module.Finite.equiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toLinearEquiv
  have hsec : ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * (((1:ℚ) : Real) + 1/2) ∧
      ∀ i : Fin 2, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span {h : MvPolynomial (Fin 2) Complex |
          ∃ g : MvPolynomial (Fin 2) Complex,
            g ∈ (RingHom.ker D3ev) ^ s ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ (B : Real)) ∧
            ∃ q : Rat, (q : Real) ≤ (B : Real) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) q g} := by
    refine ⟨1, one_pos, 1, by norm_num, fun i => ⟨1, one_pos, ?_⟩⟩
    have hc : MvPolynomial.C (-1 : ℂ) ∈ Ideal.span {h : MvPolynomial (Fin 2) Complex |
          ∃ g : MvPolynomial (Fin 2) Complex,
            g ∈ (RingHom.ker D3ev) ^ 1 ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ ((1:ℕ) : Real)) ∧
            ∃ q : Rat, (q : Real) ≤ ((1:ℕ) : Real) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) q g} := by
      apply Ideal.subset_span
      refine ⟨MvPolynomial.X 0 - 1, ?_, ?_, 0, by norm_num, ?_⟩
      · rw [pow_one, RingHom.mem_ker]; simp [D3ev]
      · intro a ha
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_X,
          MvPolynomial.coeff_one] at ha
        simp only [Fin.sum_univ_two, w]
        by_cases h1 : Finsupp.single 0 1 = a
        · subst h1; simp
        · by_cases h0 : (0 : Fin 2 →₀ ℕ) = a
          · subst h0; simp
          · simp [h1, h0] at ha
      · ext a
        rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_C]
        by_cases ha : a = 0
        · subst ha; simp
        · have hne : Finsupp.weight (fun k => (w k : ℚ)) a ≠ ((0:ℚ) : ℚ) := by
            rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
            have : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
              by_contra hc; push Not at hc; apply ha; ext i; fin_cases i <;> simp [hc]
            simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, nsmul_eq_mul]
            rcases this with h | h
            · have : (0:ℚ) < a 0 := by exact_mod_cast Nat.pos_of_ne_zero h
              positivity
            · have : (0:ℚ) < a 1 := by exact_mod_cast Nat.pos_of_ne_zero h
              positivity
          rw [if_neg hne, if_neg (Ne.symm ha)]
    have : MvPolynomial.X i ^ 1 = (-(MvPolynomial.X i ^ 1)) * MvPolynomial.C (-1 : ℂ) := by
      simp
    rw [this]; exact Ideal.mul_mem_left _ _ hc
  obtain ⟨s, hs, D, hD, hD0, hall⟩ :=
    H (RingHom.ker D3ev) hfin w hw 1 (by norm_num) (1/2) (by norm_num) hsec
  obtain ⟨n, hn, hmem⟩ := hall 1
  let e1 : MvPolynomial (Fin 2) ℂ →+* ℂ := MvPolynomial.eval ![0, 1]
  have hle : Ideal.span {h : MvPolynomial (Fin 2) Complex |
          ∃ g : MvPolynomial (Fin 2) Complex,
            g ∈ (RingHom.ker D3ev) ^ s ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
            h = MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) g} ≤ RingHom.ker e1 := by
    rw [Ideal.span_le]
    rintro _ ⟨g, hg, hsupp, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp only [e1]
    rw [MvPolynomial.eval_eq]
    apply Finset.sum_eq_zero
    intro a _
    rw [Finset.prod_subset (Finset.subset_univ _)
      (by intro i _ hi; simp [Finsupp.notMem_support_iff.mp hi]), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
    rcases Nat.eq_zero_or_pos (a 0) with h0 | h0
    · rw [MvPolynomial.coeff_weightedHomogeneousComponent]
      split_ifs with hwt
      · have ha' : a = Finsupp.single 1 (a 1) := by ext i; fin_cases i <;> simp [h0]
        have hwt' : (D : ℚ) = 2 * (a 1) := by
          rw [← hwt, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
          simp [w, h0]; ring
        have hD2 : (D:ℝ) = 2 * (a 1) := by exact_mod_cast hwt'
        obtain ⟨q, hq⟩ := D3_pow_dvd s g hg
        have hc := D3_coeff g (a 1) (fun b hb => by
          have := hsupp b hb
          simp only [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one] at this
          push_cast at this; linarith)
        rw [ha', ← hc, hq, Polynomial.coeff_X_pow_mul', if_neg]
        · simp
        · intro hle
          have : (s:ℝ) ≤ a 1 := by exact_mod_cast hle
          push_cast at hD
          linarith
      · simp
    · simp [zero_pow h0.ne']
  have := hle hmem
  simp [e1, RingHom.mem_ker] at this
