-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.toMatrix_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:05.721957+00:00
-- url     : https://prove2.me/submissions/a8187b62-e236-4e28-bbb9-a52f44f7fb3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_isSymplecticFamily_iff_toMatrix_mem

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
variable {R M l : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype l] [DecidableEq l]
  {B : LinearMap.BilinForm R M}
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution {b c : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    (hc : IsSymplecticBasis B c) (hB : B.IsAlt) : b.toMatrix c ∈ symplecticGroup l R :=
  (hb.isSymplecticFamily_iff_toMatrix_mem hB c).1 hc
end IsSymplecticBasis
end GlobalTheory
