-- Prove2me | solution 1 for GlobalTheory.LiftsToDetOne.transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:42:35.759746+00:00
-- url     : https://prove2.me/submissions/3111c56a-c81f-44cc-a7f5-a36c5258d850

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
theorem _root_.solution (hf : Surjective f) {i j : n} (hij : i ≠ j) (c : R) :
    LiftsToDetOne f (Matrix.transvection i j c) := by
  obtain ⟨c, rfl⟩ := hf c
  refine ⟨Matrix.transvection i j c, det_transvection_of_ne _ _ hij _, ?_⟩
  simp [Matrix.transvection, Matrix.map_add, Matrix.map_single]
end GlobalTheory.LiftsToDetOne
