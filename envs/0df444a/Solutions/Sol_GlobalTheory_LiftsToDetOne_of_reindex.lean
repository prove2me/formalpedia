-- Prove2me | solution 1 for GlobalTheory.LiftsToDetOne.of_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:42:34.664797+00:00
-- url     : https://prove2.me/submissions/e57da1ac-725d-493e-86e6-606e7962a414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_reindex
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
open GlobalTheory.LiftsToDetOne
namespace GlobalTheory.LiftsToDetOne
theorem _root_.solution {A : Matrix n n R} (e : n ≃ m) (h : LiftsToDetOne f (reindex e e A)) :
    LiftsToDetOne f A := by
  obtain ⟨B, hB, h⟩ := h
  refine ⟨reindex e.symm e.symm B, by simpa using hB, ?_⟩
  ext i j
  simpa using congrFun (congrFun h (e i)) (e j)
end GlobalTheory.LiftsToDetOne
