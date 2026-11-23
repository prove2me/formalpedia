-- Prove2me | solution 1 for GlobalTheory.LiftsToDetOne.upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:17.296706+00:00
-- url     : https://prove2.me/submissions/ec26aef7-815f-46df-8bad-45d58a130dbf

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
theorem _root_.solution (hf : Surjective f) (X : Matrix n m R) :
    LiftsToDetOne f (fromBlocks (1 : Matrix n n R) X 0 (1 : Matrix m m R)) := by
  obtain ⟨s, hs⟩ := hf.hasRightInverse
  refine ⟨fromBlocks 1 (X.map s) 0 1, by simp, ?_⟩
  simp [fromBlocks_map, hs.comp_eq_id]
end GlobalTheory.LiftsToDetOne
