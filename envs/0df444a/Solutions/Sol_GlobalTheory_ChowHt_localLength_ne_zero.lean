-- Prove2me | solution 1 for GlobalTheory.ChowHt.localLength_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:35.664948+00:00
-- url     : https://prove2.me/submissions/10255a3a-6ba6-4df5-954c-45e8763cd09b

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
theorem _root_.solution {J Q : Ideal R} [Q.IsPrime] (h : J ≤ Q) : localLength J Q ≠ 0 := by
  rw [localLength, Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
  refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono h
end GlobalTheory.ChowHt
