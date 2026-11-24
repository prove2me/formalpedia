-- Prove2me | solution 1 for GlobalTheory.forall_exact_residueField_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:34.415616+00:00
-- url     : https://prove2.me/submissions/db51416b-fc9c-4b5b-a2b2-7cd9f79962fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Theorems.Thm_GlobalTheory_exact_lTensor_iff_residueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
namespace GlobalTheory
theorem _root_.solution [IsLocalRing R] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Exact (f.lTensor (IsLocalRing.ResidueField R)) (g.lTensor (IsLocalRing.ResidueField R)))
    (m : Ideal R) [m.IsMaximal] :
    Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField) :=
  (exact_lTensor_iff_residueField m (IsLocalRing.ResidueField R)
    (IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal ‹_›).symm) f g).1 h
end GlobalTheory
