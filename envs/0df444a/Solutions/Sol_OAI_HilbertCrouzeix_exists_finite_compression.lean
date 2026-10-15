-- Prove2me | solution 1 for OAI.HilbertCrouzeix.exists_finite_compression
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T18:08:55.742627+00:00
-- url     : https://prove2.me/submissions/e22f370a-df7c-45dd-a806-578a8705f468

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HilbertCrouzeix/Compression.lean:L100-L119
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.HilbertCrouzeix.exists_finite_compression.
-- The statement is the platform stub (Theorems.Thm_OAI_HilbertCrouzeix_exists_finite_compression) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_HilbertCrouzeix
import Definitions.Def_OAI_Analysis_HilbertCrouzeix_NumericalRange
import Definitions.Def_OAI_Analysis_HilbertCrouzeix_Compression

-- ---- inline helpers from OAI.Analysis.HilbertCrouzeix.Compression ----
namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Elementary
omit [CompleteSpace H]

theorem compression_pow (A : H →L[ℂ] H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) {d : ℕ}
    (hmem : ∀ k ≤ d, (A ^ k) (x : H) ∈ E) {k : ℕ} (hk : k ≤ d) :
    (((compression A E) ^ k) x : H) = (A ^ k) (x : H) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ d := by omega
    have hn : A ((A ^ k) (x : H)) ∈ E := by
      simpa only [pow_succ', mul_apply_eq_comp] using hmem (k + 1) hk
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
    change E.starProjection (A (((compression A E) ^ k) x : H)) = _
    rw [ih hk']
    exact Submodule.starProjection_eq_self_iff.mpr hn

theorem pow_mem_iterateSpace {q : ℕ} (A : H →L[ℂ] H) (d : ℕ) (x : Fin q → H)
    {k : ℕ} (hk : k ≤ d) (j : Fin q) : (A ^ k) (x j) ∈ iterateSpace A d x := by
  apply Submodule.subset_span
  exact ⟨(⟨k, by omega⟩, j), rfl⟩

theorem mem_iterateSpace {q : ℕ} (A : H →L[ℂ] H) (d : ℕ) (x : Fin q → H)
    (j : Fin q) : x j ∈ iterateSpace A d x := by
  simpa using pow_mem_iterateSpace A d x (Nat.zero_le d) j

theorem polynomialEval_compression_tmul (A : H →L[ℂ] H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (x : E) (v : CoeffSpace m) (hmem : ∀ k ≤ d, (A ^ k) (x : H) ∈ E) :
    tensorInclusion E m (polynomialEval (compression A E) B (↑(x ⊗ₜ[ℂ] v))) =
      polynomialEval A B (↑((x : H) ⊗ₜ[ℂ] v)) := by
  simp only [polynomialEval, sum_apply, map_sum, tensorOp_tmul,
    tensorInclusion_tmul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [compression_pow A E x hmem (Nat.le_of_lt_succ k.isLt)]

end Elementary

end HilbertCrouzeix

end

end OAI

-- ---- hoisted mission target ----
open OAI OAI.HilbertCrouzeix
open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

omit [CompleteSpace H] in
theorem solution {m d : ℕ} (A : H →L[ℂ] H)
    (B : Fin (d + 1) → Coeff m) (ξ : H ⊗[ℂ] CoeffSpace m) :
    ∃ (E : Submodule ℂ H) (hE : FiniteDimensional ℂ E),
      letI : FiniteDimensional ℂ E := hE
      ∃ η : Amplification E m,
        tensorInclusion E m η = (↑ξ : Amplification H m) ∧
        tensorInclusion E m (polynomialEval (compression A E) B η) =
          polynomialEval A B (↑ξ) := by
  obtain ⟨q, x, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq ξ
  let E := iterateSpace A d x
  let xE (j : Fin q) : E := ⟨x j, mem_iterateSpace A d x j⟩
  let η : Amplification E m := ∑ j : Fin q, (↑(xE j ⊗ₜ[ℂ] v j) : Amplification E m)
  refine ⟨E, inferInstance, η, ?_, ?_⟩
  · simp only [η, map_sum, tensorInclusion_tmul, completion_coe_sum]
    rfl
  · simp only [η, map_sum, completion_coe_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact polynomialEval_compression_tmul A E B (xE j) (v j)
      (fun k hk => pow_mem_iterateSpace A d x hk j)
