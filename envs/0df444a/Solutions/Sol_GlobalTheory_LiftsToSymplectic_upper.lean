-- Prove2me | solution 1 for GlobalTheory.LiftsToSymplectic.upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:07.04388+00:00
-- url     : https://prove2.me/submissions/8ce0187b-465e-4182-b870-0a533cefa24c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_exists_isSymm_map_eq
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
open GlobalTheory.LiftsToSymplectic
namespace GlobalTheory.LiftsToSymplectic
theorem _root_.solution (hf : Surjective f) {X : Matrix l l R} (hX : X.IsSymm) :
    LiftsToSymplectic f (fromBlocks 1 X 0 1) := by
  obtain ⟨Y, hY, rfl⟩ := exists_isSymm_map_eq hf hX
  exact ⟨fromBlocks 1 Y 0 1, by simp [SymplecticGroup.fromBlocks_mem_iff, hY.eq],
    by simp [fromBlocks_map]⟩
end GlobalTheory.LiftsToSymplectic
