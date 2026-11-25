-- Prove2me | solution 1 for GlobalTheory.matrix_exists_common_eigenvector_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:15.05055+00:00
-- url     : https://prove2.me/submissions/5b578c73-cec5-4d5f-874b-0f0dc0b6dc95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMem
import Theorems.Thm_GlobalTheory_exists_common_eigenvector_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Set (Matrix (Fin n) (Fin n) K)),
      (∀ A ∈ S, ∀ B ∈ S, Commute A B) → ∀ (E : Submodule K (Fin n → K)), E ≠ ⊥ →
      (∀ A ∈ S, ∀ v ∈ E, A *ᵥ v ∈ E) → ∃ v ∈ E, v ≠ 0 ∧ ∀ A ∈ S, ∃ μ : K, A *ᵥ v = μ • v := by
  intro K _ _ n S hS E hE hst
  obtain ⟨v, hvE, hv0, hv⟩ := exists_common_eigenvector_mem (K := K) (V := Fin n → K)
    (fun A : S => Matrix.toLin' (A : Matrix (Fin n) (Fin n) K))
    (fun i j v => by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      rw [(hS i i.2 j j.2).eq])
    E hE (fun i v hv => by simpa [Matrix.toLin'_apply] using hst i i.2 v hv)
  refine ⟨v, hvE, hv0, fun A hA => ?_⟩
  obtain ⟨l, hl⟩ := hv ⟨A, hA⟩
  exact ⟨l, by simpa [Matrix.toLin'_apply] using hl⟩
end GlobalTheory
