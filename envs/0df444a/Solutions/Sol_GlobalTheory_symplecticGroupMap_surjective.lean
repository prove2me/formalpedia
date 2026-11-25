-- Prove2me | solution 1 for GlobalTheory.symplecticGroupMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:10:42.396264+00:00
-- url     : https://prove2.me/submissions/390ebddd-1c7b-4791-9714-ca0d87da6493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_liftsToSymplectic_of_mem
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
namespace GlobalTheory
theorem _root_.solution [Finite (MaximalSpectrum R)] (hf : Surjective f) :
    Surjective (symplecticGroupMap l f) := fun A => by
  obtain ⟨B, hB, h⟩ := liftsToSymplectic_of_mem hf A.2
  exact ⟨⟨B, hB⟩, Subtype.ext h⟩
end GlobalTheory
