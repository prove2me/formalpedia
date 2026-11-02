-- Prove2me | solution 1 for MayersQBC.cheatProb_ge_expectedFidelity
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:02:16.780091+00:00
-- url     : https://prove2.me/submissions/7a4a6a8e-acec-4f34-b62d-87f971b6ddcd

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_MayersQBC_expectedFidelity
import Definitions.Def_MayersQBC_cheatProb
import Theorems.Thm_MayersQBC_cheat_ge_fidelity
open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate

namespace MayersQBCAvgAux

/-- `Tr(M |φ⟩⟨φ|) = ⟨φ|M|φ⟩`, written with `dotProduct`. -/
lemma trace_mul_pureDensity' {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ)
    (φ : EuclideanSpace ℂ ι) :
    (M * pureDensity φ).trace = star (WithLp.ofLp φ) ⬝ᵥ (M *ᵥ WithLp.ofLp φ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A positive semidefinite operator has nonnegative expectation in every vector. -/
lemma effectProb_pureDensity_nonneg {ι : Type} [Fintype ι] {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (φ : EuclideanSpace ℂ ι) : 0 ≤ effectProb M (pureDensity φ) := by
  rw [effectProb, trace_mul_pureDensity']
  exact (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg _)).1

/-- An effect accepts a vector `φ` with "probability" at most `‖φ‖²`. -/
lemma effectProb_pureDensity_le {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : IsEffect M) (φ : EuclideanSpace ℂ ι) : effectProb M (pureDensity φ) ≤ ‖φ‖ ^ 2 := by
  have h1 := effectProb_pureDensity_nonneg hM.2 φ
  rw [effectProb, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h1
  have h2 : (pureDensity φ).trace.re = ‖φ‖ ^ 2 := by
    rw [← Matrix.one_mul (pureDensity φ), trace_mul_pureDensity', Matrix.one_mulVec,
      ← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  rw [effectProb]
  linarith

end MayersQBCAvgAux

open MayersQBCAvgAux MayersQBC in
theorem solution {Γ A B : Type} [Fintype Γ] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (p q : Γ → ℝ) (hp : (∀ γ, 0 ≤ p γ) ∧ ∑ γ, p γ = 1)
    (ψ0 ψ1 : Γ → EuclideanSpace ℂ (A × B)) (h0 : ∀ γ, IsState (ψ0 γ)) (h1 : ∀ γ, IsState (ψ1 γ))
    (acc : Γ → Matrix (A × B) (A × B) ℂ) (hacc : ∀ γ, IsEffect (acc γ))
    (hcorrect : ∀ γ, q γ ≠ 0 → effectProb (acc γ) (pureDensity (ψ1 γ)) = 1) :
    ∃ U : Γ → Matrix A A ℂ, (∀ γ, U γ ∈ Matrix.unitaryGroup A ℂ) ∧
      expectedFidelity p q ψ0 ψ1 ≤ cheatProb p acc U ψ0 ∧ cheatProb p acc U ψ0 ≤ 1 := by
  -- per transcript: choose Alice's unitary
  have key : ∀ γ, ∃ V ∈ Matrix.unitaryGroup A ℂ,
      (if q γ = 0 then 0 else
        rootFidelity (traceLeft (pureDensity (ψ0 γ))) (traceLeft (pureDensity (ψ1 γ))) ^ 2) ≤
        effectProb (acc γ) (pureDensity (act (Matrix.kronecker V (1 : Matrix B B ℂ)) (ψ0 γ))) := by
    intro γ
    by_cases hq : q γ = 0
    · -- `γ` determines the bit: `F'(γ) = 0`, any unitary (here `1`) will do
      refine ⟨1, one_mem _, ?_⟩
      rw [if_pos hq]
      exact effectProb_pureDensity_nonneg (hacc γ).1 _
    · obtain ⟨V, hV, hle⟩ := cheat_ge_fidelity (ψ0 γ) (ψ1 γ) (h0 γ) (h1 γ) (acc γ) (hacc γ)
        (hcorrect γ hq)
      exact ⟨V, hV, by rw [if_neg hq]; exact hle⟩
  choose U hU hUle using key
  refine ⟨U, hU, ?_, ?_⟩
  · -- lower bound: average the per-transcript bounds with the weights `p γ ≥ 0`
    unfold expectedFidelity cheatProb
    exact Finset.sum_le_sum fun γ _ => mul_le_mul_of_nonneg_left (hUle γ) (hp.1 γ)
  · -- upper bound: each acceptance probability is at most `‖(U γ ⊗ I) ψ0 γ‖² = 1`
    unfold cheatProb
    have hone : ∀ γ, effectProb (acc γ)
        (pureDensity (act (Matrix.kronecker (U γ) (1 : Matrix B B ℂ)) (ψ0 γ))) ≤ 1 := by
      intro γ
      have hk : Matrix.kronecker (U γ) (1 : Matrix B B ℂ) ∈ Matrix.unitaryGroup (A × B) ℂ :=
        Matrix.kronecker_mem_unitary (hU γ) (one_mem _)
      have hn : ‖act (Matrix.kronecker (U γ) (1 : Matrix B B ℂ)) (ψ0 γ)‖ = 1 := by
        rw [act_norm_of_mem_unitaryGroup hk]
        exact h0 γ
      have := effectProb_pureDensity_le (hacc γ)
        (act (Matrix.kronecker (U γ) (1 : Matrix B B ℂ)) (ψ0 γ))
      rw [hn, one_pow] at this
      exact this
    calc ∑ γ, p γ * effectProb (acc γ)
          (pureDensity (act (Matrix.kronecker (U γ) (1 : Matrix B B ℂ)) (ψ0 γ)))
        ≤ ∑ γ, p γ * 1 := Finset.sum_le_sum fun γ _ =>
          mul_le_mul_of_nonneg_left (hone γ) (hp.1 γ)
      _ = 1 := by simp [hp.2]
