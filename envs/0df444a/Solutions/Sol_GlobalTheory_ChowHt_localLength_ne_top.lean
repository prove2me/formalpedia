-- Prove2me | solution 1 for GlobalTheory.ChowHt.localLength_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:51.881667+00:00
-- url     : https://prove2.me/submissions/0d1c2e37-ed8c-4cdc-af21-dad4dece47d4

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
theorem _root_.solution [IsNoetherianRing R] {J Q : Ideal R} [Q.IsPrime]
    (h : Q ∈ J.minimalPrimes) : localLength J Q ≠ ⊤ := by
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime Q) Q J h
  rw [Localization.AtPrime.map_eq_maximalIdeal] at hrad
  have hmin : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈
      (J.map (algebraMap R (Localization.AtPrime Q))).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  haveI := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  rw [localLength, Module.length_eq_of_surjective
    (R := Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q)))
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top
end GlobalTheory.ChowHt
