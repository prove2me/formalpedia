-- Prove2me | solution 1 for GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:32.150586+00:00
-- url     : https://prove2.me/submissions/71459b04-97c1-4322-bb40-27352a9f69f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing NumberField IsDedekindDomain
open GlobalTheory
open IsLocalRing IsDedekindDomain NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R)
    (hfin : Finite (R ⧸ v.asIdeal)) :
      IsDiscreteValuationRing ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) ∧
        Finite (IsLocalRing.ResidueField
          ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)) := by
  let S := Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField K _ _
  have hD : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S
  haveI : IsLocalRing S := inferInstance
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hS : Finite (ResidueField S) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal S).toEquiv
  exact ⟨hD, hS⟩
end _root_.GlobalTheory
end GlobalTheory
