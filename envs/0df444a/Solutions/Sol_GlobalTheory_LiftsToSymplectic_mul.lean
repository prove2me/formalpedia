-- Prove2me | solution 1 for GlobalTheory.LiftsToSymplectic.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:18.678805+00:00
-- url     : https://prove2.me/submissions/5d618fb4-21b2-4877-8d9d-ef877012c602

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
  {l : Type*} [Fintype l] [DecidableEq l]
open GlobalTheory.LiftsToSymplectic
namespace GlobalTheory.LiftsToSymplectic
theorem _root_.solution {A B : Matrix (l ⊕ l) (l ⊕ l) R} (hA : LiftsToSymplectic f A)
    (hB : LiftsToSymplectic f B) : LiftsToSymplectic f (A * B) := by
  obtain ⟨A, hA, rfl⟩ := hA
  obtain ⟨B, hB, rfl⟩ := hB
  exact ⟨A * B, mul_mem hA hB, Matrix.map_mul⟩
end GlobalTheory.LiftsToSymplectic
