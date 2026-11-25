-- Prove2me | solution 1 for GlobalTheory.ChowHt.localLength_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:35:42.670039+00:00
-- url     : https://prove2.me/submissions/08331ba2-bbfb-4a91-93bc-0db0e1450ff2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ChowHt
variable {R : Type} [CommRing R]
namespace GlobalTheory.ChowHt
theorem _root_.solution (Q : Ideal R) [Q.IsPrime] : localLength Q Q = 1 := by
  rw [localLength, Localization.AtPrime.map_eq_maximalIdeal, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  exact IsLocalRing.maximalIdeal.isMaximal _
end GlobalTheory.ChowHt
