-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomials_span_of_lower_weight_powers
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:19:55.28508+00:00
-- url     : https://prove2.me/submissions/6ce32883-1b9a-47e3-9a99-9a909ccd2639

import Mathlib

open scoped BigOperators

theorem solution : ¬ (∀ {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ)) (W : Fin d → Nat)
    (hW : ∀ i, 0 < W i) (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (hred : ∀ i : Fin d, ∃ r : Nat, 0 < r ∧ (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r ∈
      Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat,
        (∑ k : Fin d, a k * W k) < r * W i ∧ f = MvPolynomial.monomial a (1 : ℂ)}),
    ∀ e : Fin d →₀ Nat, MvPolynomial.monomial e (1 : ℂ) ∈ Submodule.span A
      {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧
        f = MvPolynomial.monomial a (1 : ℂ)}) := by
  intro H
  let σ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
    MvPolynomial.aeval (fun _ => -MvPolynomial.X 0)
  let A : Subalgebra ℂ (MvPolynomial (Fin 1) ℂ) := Algebra.adjoin ℂ {MvPolynomial.X 0 ^ 2}
  have hA : A ≤ AlgHom.equalizer σ (AlgHom.id ℂ _) := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    simp [σ]
  let M : Submodule A (MvPolynomial (Fin 1) ℂ) :=
    { carrier := {p | σ p = p}
      add_mem' := by intro p q hp hq; simp_all
      zero_mem' := by simp
      smul_mem' := by
        intro a p hp
        have ha : σ a = a := hA a.2
        simp only [Set.mem_setOf_eq] at hp ⊢
        rw [Subalgebra.smul_def, smul_eq_mul, map_mul, ha, hp] }
  have h := H (d := 1) A (fun _ => 1) (fun _ => one_pos) (fun _ => 1) (fun _ => one_pos)
    (fun i => ⟨2, two_pos, by
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi
      have h1 : (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ) ^ 2 =
          (⟨MvPolynomial.X 0 ^ 2, Algebra.subset_adjoin rfl⟩ : A) • MvPolynomial.monomial 0 (1:ℂ) := by
        rw [Subalgebra.smul_def, smul_eq_mul]; simp
      rw [h1]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨0, by simp, rfl⟩⟩) (Finsupp.single 0 1)
  have hle : Submodule.span A {f : MvPolynomial (Fin 1) ℂ | ∃ a : Fin 1 →₀ Nat, (∀ i, a i < 1) ∧
        f = MvPolynomial.monomial a (1 : ℂ)} ≤ M := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have : a = 0 := Finsupp.ext (fun j => by have := ha j; simp only [Finsupp.coe_zero, Pi.zero_apply]; omega)
    subst this
    show σ _ = _
    simp [σ]
  have h2 : σ (MvPolynomial.X 0) = MvPolynomial.X 0 := by
    have := hle h
    rwa [← MvPolynomial.X] at this
  simp only [σ, MvPolynomial.aeval_X] at h2
  have h3 : (2 : ℂ) • (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ) = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h2]; ring
  rw [smul_eq_zero] at h3
  rcases h3 with h3 | h3
  · norm_num at h3
  · exact MvPolynomial.X_ne_zero 0 h3
