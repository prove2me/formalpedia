-- Prove2me | solution 1 for GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:52:59.898068+00:00
-- url     : https://prove2.me/submissions/a81e948c-b938-4fee-a929-0bb2c4002dc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanEqTopOfTraceEq
import Theorems.Thm_GlobalTheory_TraceFormNondegenerate_eq_zero_of_trace_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceFormNondegenerate
namespace GlobalTheory.TraceFormNondegenerate
theorem _root_.solution {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K)
    (htr : ∀ g : Γ, Matrix.trace (M g) = Matrix.trace (N g))
    (hN : Submodule.span K (Set.range (⇑N : Γ → Matrix (Fin n) (Fin n) K)) = ⊤) :
    Submodule.span K (Set.range (⇑M : Γ → Matrix (Fin n) (Fin n) K)) = ⊤ := by
  obtain ⟨A, hA⟩ : ∃ A : (Γ →₀ K) →ₗ[K] Matrix (Fin n) (Fin n) K,
      A = Finsupp.linearCombination K (⇑M) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (Γ →₀ K) →ₗ[K] Matrix (Fin n) (Fin n) K,
      B = Finsupp.linearCombination K (⇑N) := ⟨_, rfl⟩

  have hprod : ∀ (f : Γ →₀ K) (h : Γ),
      Matrix.trace (B f * N h) = Matrix.trace (A f * M h) := by
    intro f h
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [add_mul, hf, hg]
    | single g a =>
      subst hA hB
      simp only [Finsupp.linearCombination_single, smul_mul_assoc, Matrix.trace_smul,
        ← map_mul, htr]

  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply eq_zero_of_trace_mul
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range (⇑N)) := hN ▸ Submodule.mem_top
    let ℓ : Matrix (Fin n) (Fin n) K →ₗ[K] K :=
      (Matrix.traceLinearMap (Fin n) K K).comp (LinearMap.mulLeft K (B f))
    have hle : Submodule.span K (Set.range (⇑N)) ≤ LinearMap.ker ℓ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      simp [ℓ, hprod, hf]
    simpa [ℓ] using hle hY

  let φ : LinearMap.range A →ₗ[K] Matrix (Fin n) (Fin n) K :=
    ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ f, φ ⟨A f, LinearMap.mem_range_self A f⟩ = B f := by
    intro f
    simp [φ]
  have hφtop : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    rintro Y -
    have hY : Y ∈ LinearMap.range B := by
      rw [hB, Finsupp.range_linearCombination, hN]
      exact Submodule.mem_top
    obtain ⟨f, rfl⟩ := hY
    exact ⟨_, hφ f⟩
  have h1 := LinearMap.finrank_range_le φ
  rw [hφtop, finrank_top] at h1
  have h2 : LinearMap.range A = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h1)
  rwa [hA, Finsupp.range_linearCombination] at h2
end GlobalTheory.TraceFormNondegenerate
