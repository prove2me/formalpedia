-- Prove2me | solution 1 for GibbsCongestion.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:39:41.779094+00:00
-- url     : https://prove2.me/submissions/6ce5ad0f-4c60-4958-bb5c-08c8644177f4

import Mathlib
import Definitions.Def_GibbsCongestion_IsSLC

open GibbsCongestion in
theorem solution {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (hp : IsSLC p)
    (γ : ℝ) (hγ : 0 ≤ γ) : IsSLC (MvPolynomial.C γ * p) := by
  refine ⟨fun m => by rw [MvPolynomial.coeff_C_mul]; exact mul_nonneg hγ (hp.1 m), fun l => ?_⟩
  have hf : l.foldr (fun i q => MvPolynomial.pderiv i q) (MvPolynomial.C γ * p) =
      MvPolynomial.C γ * l.foldr (fun i q => MvPolynomial.pderiv i q) p := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.foldr_cons, ih, MvPolynomial.pderiv_C_mul]
  rw [hf]
  have h := hp.2 l
  generalize l.foldr (fun i q => MvPolynomial.pderiv i q) p = q at h ⊢
  unfold IsLogConcavePoly at h ⊢
  intro x hx v
  specialize h x hx v
  have s1 : ∀ f : σ → σ → ℝ, ∑ i, ∑ j, v i * v j * (γ * f i j) =
      γ * ∑ i, ∑ j, v i * v j * f i j := by
    intro f
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have s2 : ∀ f : σ → ℝ, ∑ i, v i * (γ * f i) = γ * ∑ i, v i * f i := by
    intro f
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp only [MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C, s1, s2]
  calc γ * MvPolynomial.eval x q * (γ * ∑ i, ∑ j, v i * v j *
        MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv j q)))
      = γ ^ 2 * (MvPolynomial.eval x q * ∑ i, ∑ j, v i * v j *
        MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv j q))) := by ring
    _ ≤ γ ^ 2 * (∑ i, v i * MvPolynomial.eval x (MvPolynomial.pderiv i q)) ^ 2 :=
        mul_le_mul_of_nonneg_left h (sq_nonneg γ)
    _ = (γ * ∑ i, v i * MvPolynomial.eval x (MvPolynomial.pderiv i q)) ^ 2 := by ring
