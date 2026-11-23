-- Prove2me | solution 1 for GlobalTheory.LiftsToDetOne.adjugate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:03.718972+00:00
-- url     : https://prove2.me/submissions/38759fea-ae65-4846-af9f-cc989b88a0ee

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
theorem _root_.solution {A : Matrix n n R} (hA : LiftsToDetOne f A) : LiftsToDetOne f A.adjugate := by
  obtain ⟨A, hA, rfl⟩ := hA
  exact ⟨A.adjugate, by simp [det_adjugate, hA], f.map_adjugate A⟩
end GlobalTheory.LiftsToDetOne
