-- Prove2me | solution 1 for GlobalTheory.LiftsToSymplectic.levi_of_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:42:37.131342+00:00
-- url     : https://prove2.me/submissions/bcd69c9a-fc4e-4a81-96c1-927be80137c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_mul
import Theorems.Thm_GlobalTheory_LiftsToDetOne_upper
import Theorems.Thm_GlobalTheory_LiftsToDetOne_lower
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_mul
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_upper
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_lower
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
theorem _root_.solution (hf : Surjective f) {X Y : Matrix l l R} (hX : X.IsSymm) (hY : Y.IsSymm)
    (h : X * Y = 1) : LiftsToSymplectic f (fromBlocks X 0 0 Y) := by
  have h' : Y * X = 1 := mul_eq_one_comm.1 h
  have := (((upper hf hX).mul (lower hf hY.neg)).mul (upper hf hX)).mul J
  simpa [fromBlocks_multiply, Matrix.J, h, h'] using this
end GlobalTheory.LiftsToSymplectic
