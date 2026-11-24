-- Prove2me | solution 1 for GlobalTheory.exists_mul_mul_eq_one_of_card_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:42.910735+00:00
-- url     : https://prove2.me/submissions/ace3da1e-8238-457e-a190-9f37a0da7a58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.coe_symplecticGroupMap

set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {R : Type*} [CommRing R] {l n : Type*} [Fintype l] [DecidableEq l] [Fintype n]
  [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] (G : Matrix n n K)
    (h : Fintype.card l ≤ G.rank) : ∃ (U : Matrix l n K) (V : Matrix n l K), U * G * V = 1 := by
  obtain ⟨U, V, e, -, -, heq⟩ := exists_rank_normal_form G
  obtain ⟨k⟩ : Nonempty (l ↪ Fin G.rank) := Function.Embedding.nonempty_of_card_le (by simpa)
  let σ : l → n := fun i => e.symm (.inl (k i))
  refine ⟨U.submatrix σ id, V.submatrix id σ, ?_⟩
  have : U.submatrix σ id * G * V.submatrix id σ = (U * G * V).submatrix σ σ := by
    ext i j
    simp [Matrix.mul_apply]
  rw [this, heq]
  ext i j
  simp [σ, Matrix.one_apply]
end GlobalTheory
