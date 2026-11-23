-- Prove2me | solution 1 for GlobalTheory.LiftsToDetOne.det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:32.94259+00:00
-- url     : https://prove2.me/submissions/2bea77a1-358e-448c-9d9d-f01026eea00c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
open GlobalTheory.LiftsToDetOne
namespace GlobalTheory.LiftsToDetOne
theorem _root_.solution {A : Matrix n n R} (h : LiftsToDetOne f A) : A.det = 1 := by
  obtain ⟨B, hB, rfl⟩ := h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hB, map_one]
end GlobalTheory.LiftsToDetOne
