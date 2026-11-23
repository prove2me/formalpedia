-- Prove2me | solution 1 for GlobalTheory.LiftsToDetOne.of_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:57.475069+00:00
-- url     : https://prove2.me/submissions/0fce9608-cf10-49d0-b867-5b781f39cd0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_det_eq
import Theorems.Thm_GlobalTheory_LiftsToDetOne_mul
import Theorems.Thm_GlobalTheory_LiftsToDetOne_adjugate

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
theorem _root_.solution {E A : Matrix n n R} (hE : LiftsToDetOne f E) (h : LiftsToDetOne f (E * A)) :
    LiftsToDetOne f A := by
  have := hE.adjugate.mul h
  rwa [← Matrix.mul_assoc, adjugate_mul, hE.det_eq, one_smul, Matrix.one_mul] at this
end GlobalTheory.LiftsToDetOne
