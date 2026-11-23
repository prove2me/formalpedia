-- Prove2me | solution 1 for GlobalTheory.LiftsToDetOne.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:16.843316+00:00
-- url     : https://prove2.me/submissions/21272d44-9b10-47ff-a7c9-2d446ccbc544

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
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
theorem _root_.solution {A B : Matrix n n R} (hA : LiftsToDetOne f A) (hB : LiftsToDetOne f B) :
    LiftsToDetOne f (A * B) := by
  obtain ⟨A, hA, rfl⟩ := hA
  obtain ⟨B, hB, rfl⟩ := hB
  exact ⟨A * B, by simp [hA, hB], Matrix.map_mul⟩
end GlobalTheory.LiftsToDetOne
