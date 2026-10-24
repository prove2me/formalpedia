-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_translated_polynomial_full_jets_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:03:50.424995+00:00
-- url     : https://prove2.me/submissions/51d06465-3851-4cdf-b30c-a33d53db8c6a

import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic

section

open MvPolynomial

namespace PiL10

theorem interp {n : Nat} {J : Type} [Fintype J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (z : J → (Fin n →₀ Nat) → Complex) :
    ∃ Q : MvPolynomial (Fin n) Complex,
      ∀ (j : J) (α : Fin n →₀ Nat),
        (∑ i : Fin n, α i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c j i) + MvPolynomial.X i) Q).coeff α
          = z j α := by
  classical
  let τ : J → MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
    fun j => aeval (fun i : Fin n => C (c j i) + X i)
  let M : J → Ideal (MvPolynomial (Fin n) ℂ) := fun j => Ideal.span (Set.range fun i => X i - C (c j i))
  have hmap : ∀ j, Ideal.map (τ j) (M j) = idealOfVars (Fin n) ℂ := by
    intro j
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    ext p; simp [τ]
  have hvan : ∀ j p, p ∈ M j ^ (D + 1) → ∀ α : Fin n →₀ ℕ, (∑ i, α i) ≤ D → (τ j p).coeff α = 0 := by
    intro j p hp α hα
    have h1 : τ j p ∈ idealOfVars (Fin n) ℂ ^ (D + 1) := by
      rw [← hmap, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hp
    rw [mem_pow_idealOfVars_iff'] at h1
    apply h1
    rw [Finsupp.degree_eq_sum]
    omega
  have hcop : Pairwise (Function.onFun IsCoprime fun j => M j ^ (D + 1)) := by
    intro j k hjk
    apply IsCoprime.pow
    rw [Ideal.isCoprime_iff_sup_eq]
    obtain ⟨i, hi⟩ : ∃ i, c j i ≠ c k i := by
      by_contra h; push_neg at h; exact hjk (hc (funext h))
    apply Ideal.eq_top_of_isUnit_mem _ _ (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hi.symm) |>.map C)
    have : C (c k i - c j i) = (X i - C (c j i)) - (X i - C (c k i)) := by rw [C_sub]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  let F : Finset (Fin n →₀ ℕ) :=
    (Fintype.piFinset fun _ : Fin n => Finset.range (D + 1)).map Finsupp.equivFunOnFinite.symm.toEmbedding
  let Z : J → MvPolynomial (Fin n) ℂ := fun j => ∑ α ∈ F, monomial α (z j α)
  let P : J → MvPolynomial (Fin n) ℂ := fun j => aeval (fun i : Fin n => X i - C (c j i)) (Z j)
  have hτP : ∀ j, τ j (P j) = Z j := by
    intro j
    simp only [τ, P]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have : (fun i : Fin n => aeval (fun i : Fin n => C (c j i) + X i) (X i - C (c j i))) = X := by
      funext i; simp
    rw [this, aeval_X_left_apply]
  have hZ : ∀ j (α : Fin n →₀ ℕ), (∑ i, α i) ≤ D → (Z j).coeff α = z j α := by
    intro j α hα
    have hαF : α ∈ F := by
      simp only [F, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range, Equiv.toEmbedding_apply]
      refine ⟨α, fun i => ?_, by simp⟩
      have := Finset.single_le_sum (f := fun i => α i) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    simp only [Z, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq', if_pos hαF]
  obtain ⟨Q, hQ⟩ := Ideal.exists_forall_sub_mem_ideal hcop P
  refine ⟨Q, fun j α hα => ?_⟩
  have : Q = P j + (Q - P j) := by ring
  change (τ j Q).coeff α = _
  rw [this, map_add, coeff_add, hτP, hZ j α hα, hvan j _ (hQ j) α hα, add_zero]

end PiL10

end



theorem solution
    {n : Nat} {J : Type} [Fintype J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (z : J → (Fin n →₀ Nat) → Complex) :
    ∃ Q : MvPolynomial (Fin n) Complex,
      ∀ (j : J) (α : Fin n →₀ Nat),
        (∑ i : Fin n, α i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c j i) + MvPolynomial.X i) Q).coeff α
          = z j α := by
  apply PiL10.interp <;> assumption
