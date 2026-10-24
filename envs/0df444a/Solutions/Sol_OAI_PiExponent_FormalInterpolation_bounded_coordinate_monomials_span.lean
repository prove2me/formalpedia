-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_coordinate_monomials_span
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:21:35.387776+00:00
-- url     : https://prove2.me/submissions/2a147751-5a30-401d-ade1-012bce6df733

import Mathlib

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D) (g : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (c : Fin d → Fin k → MvPolynomial (Fin d) Complex)
    (heq : ∀ i, (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n i =
      ∑ j : Fin k, c i j * g j)
    (hc : ∀ i j, (c i j).IsWeightedHomogeneous (fun l => (w l : Real))
      ((n i : Real) * (w i : Real) - D)) :
    Submodule.span (Algebra.adjoin Complex (Set.range g))
      (Set.range fun e : {e : Fin d → Nat // ∀ i, e i < n i} =>
        ∏ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ e.1 i) = ⊤ := by
  classical
  set A := Algebra.adjoin Complex (Set.range g)
  set S := Submodule.span A (Set.range fun e : {e : Fin d → Nat // ∀ i, e i < n i} =>
        ∏ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ e.1 i)
  let wt : (Fin d →₀ ℕ) → ℝ := fun e => Finsupp.weight (fun i => (w i : ℝ)) e
  have hwt : ∀ e : Fin d →₀ ℕ, wt e = ∑ i, (e i : ℝ) * (w i : ℝ) := by
    intro e
    simp only [wt, Finsupp.weight_apply]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp [nsmul_eq_mul]
  have hwt0 : ∀ e, 0 ≤ wt e := by
    intro e; rw [hwt]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hw i).le)
  -- complex scalars act through A
  have hsmulC : ∀ (a : ℂ) (p : MvPolynomial (Fin d) ℂ), p ∈ S → a • p ∈ S := by
    intro a p hp
    have : a • p = (algebraMap ℂ A a) • p := by
      rw [Subalgebra.smul_def]; simp [Algebra.smul_def]
    rw [this]; exact S.smul_mem _ hp
  have hgA : ∀ j, g j ∈ A := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have key : ∀ t : ℕ, ∀ e : Fin d →₀ ℕ, wt e < t * D → MvPolynomial.monomial e (1:ℂ) ∈ S := by
    intro t
    induction t with
    | zero => intro e he; simp at he; linarith [hwt0 e]
    | succ t ih =>
      intro e he
      by_cases hsmall : ∀ i, e i < n i
      · apply Submodule.subset_span
        refine ⟨⟨e, hsmall⟩, ?_⟩
        simp only
        rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      · push Not at hsmall
        obtain ⟨i, hi⟩ := hsmall
        set e' := e - Finsupp.single i (n i)
        have he' : e = e' + Finsupp.single i (n i) := by
          ext l; simp only [e', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
          by_cases hl : l = i
          · subst hl; simp; omega
          · simp [Finsupp.single_apply, Ne.symm hl]
        have hmono : MvPolynomial.monomial e (1:ℂ) =
            ∑ j, (MvPolynomial.monomial e' (1:ℂ) * c i j) * g j := by
          have h1 : MvPolynomial.monomial e (1:ℂ) = MvPolynomial.monomial e' 1 * MvPolynomial.X i ^ n i := by
            rw [he', MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]
          rw [h1, heq i, Finset.mul_sum]
          simp [mul_assoc]
        rw [hmono]
        apply Submodule.sum_mem
        intro j _
        rw [mul_comm _ (g j)]
        have : g j * (MvPolynomial.monomial e' (1:ℂ) * c i j) =
            (⟨g j, hgA j⟩ : A) • (MvPolynomial.monomial e' (1:ℂ) * c i j) := by
          rw [Subalgebra.smul_def, smul_eq_mul]
        rw [this]
        apply S.smul_mem
        -- the cofactor is homogeneous of degree wt e - D < t * D
        have hhom' := (MvPolynomial.isWeightedHomogeneous_monomial (fun l => (w l : ℝ)) e' (1:ℂ)
          rfl).mul (hc i j)
        rw [(MvPolynomial.monomial e' (1:ℂ) * c i j).as_sum]
        apply Submodule.sum_mem
        intro f hf
        rw [← mul_one (MvPolynomial.coeff f _), ← smul_eq_mul, ← MvPolynomial.smul_monomial]
        apply hsmulC
        apply ih
        have hf' := hhom' (MvPolynomial.mem_support_iff.mp hf)
        change wt f < _
        simp only [wt]
        rw [hf']
        have hsingle : wt (Finsupp.single i (n i)) = n i * w i := by
          rw [hwt, Finset.sum_eq_single i]
          · simp
          · intro b _ hb; simp [Finsupp.single_apply, Ne.symm hb]
          · simp
        have : wt e = wt e' + n i * w i := by
          rw [← hsingle, he']; simp only [wt, map_add]
        change wt e' + _ < _
        push_cast at he ⊢
        linarith
  rw [Submodule.eq_top_iff']
  intro p
  rw [p.as_sum]
  apply Submodule.sum_mem
  intro e _
  rw [← mul_one (MvPolynomial.coeff e p), ← smul_eq_mul, ← MvPolynomial.smul_monomial]
  apply hsmulC
  obtain ⟨t, ht⟩ := exists_nat_gt (wt e / D)
  apply key t
  rwa [div_lt_iff₀ hD] at ht
