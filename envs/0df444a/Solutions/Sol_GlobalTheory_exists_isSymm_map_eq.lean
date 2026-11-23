-- Prove2me | solution 1 for GlobalTheory.exists_isSymm_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:37.427249+00:00
-- url     : https://prove2.me/submissions/91f63137-34ef-4ea1-bcb4-2ae0f8893e85

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
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {l : Type*} [Fintype l] [DecidableEq l]
omit [Fintype l] [DecidableEq l]
namespace GlobalTheory
theorem _root_.solution (hf : Surjective f) {X : Matrix l l R} (hX : X.IsSymm) :
    ∃ Y : Matrix l l S, Y.IsSymm ∧ Y.map f = X := by
  obtain ⟨s, hs⟩ := hf.hasRightInverse
  exact ⟨X.map s, hX.map s, Matrix.ext fun i j => hs (X i j)⟩
end GlobalTheory
