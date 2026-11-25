-- Prove2me | solution 1 for GlobalTheory.exists_basis_over_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:57.198181+00:00
-- url     : https://prove2.me/submissions/1f7d2eea-cb39-4834-bf38-d170df5532b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOverEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (σ₀ : K →+* ℂ) (m : ℕ)
    (a : Fin m → ℂ) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (c : Fin m → Fin n → K),
      (∀ t : Fin n → K, ∑ b, σ₀ (t b) * e b = 0 → t = 0) ∧
        ∀ i, a i = ∑ b, σ₀ (c i b) * e b := by
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hs : ∀ (k : K) (z : ℂ), k • z = σ₀ k * z := fun k z => rfl
  let V : Submodule K ℂ := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let B := Module.finBasis K V
  have ha : ∀ i, a i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.finrank K V, fun b => (B b : ℂ), fun i b => B.repr ⟨a i, ha i⟩ b, ?_, ?_⟩
  · intro t ht
    have hli := Fintype.linearIndependent_iff.1 B.linearIndependent t
    funext b
    refine hli ?_ b
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs, Submodule.coe_zero]
    exact ht
  · intro i
    have h := congrArg (Subtype.val : V → ℂ) (B.sum_repr ⟨a i, ha i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs] at h
    exact h.symm
end GlobalTheory
