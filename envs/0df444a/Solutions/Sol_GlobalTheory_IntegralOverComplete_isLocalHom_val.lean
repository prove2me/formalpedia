-- Prove2me | solution 1 for GlobalTheory.IntegralOverComplete.isLocalHom_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:51:59.974899+00:00
-- url     : https://prove2.me/submissions/b4e2f75a-8b75-4fa6-a922-85863089e2c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HenselianIUnionCompleteOfIntegralOverCompleteDvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.IntegralOverComplete
open IsLocalRing Polynomial
namespace GlobalTheory.IntegralOverComplete
theorem _root_.solution {W R : Type} [CommRing W] [CommRing R] [Algebra W R]
    [Algebra.IsIntegral W R] (W' : Subalgebra W R) : IsLocalHom W'.val.toRingHom := by
  have : Algebra.IsIntegral W' R := Algebra.IsIntegral.tower_top W
  have : FaithfulSMul W' R := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  exact inferInstanceAs (IsLocalHom (algebraMap W' R))
end GlobalTheory.IntegralOverComplete
