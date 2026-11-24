-- Prove2me | solution 1 for GlobalTheory.SepPoint.exists_sepBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:38.331562+00:00
-- url     : https://prove2.me/submissions/cdee0ea5-9f93-483d-a934-cf68c81fb6d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparablePointOfGeometricallyDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SepPoint
namespace GlobalTheory.SepPoint
theorem _root_.solution (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    (hB : Algebra.FiniteType k B)
    (hH : ∀ p : ℕ, p.Prime → CharP k p → ∀ s : Finset (FractionRing B),
      LinearIndepOn k _root_.id (s : Set (FractionRing B)) →
        LinearIndepOn k (· ^ p) (s : Set (FractionRing B))) :
    ∃ s : Finset (FractionRing B), IsTranscendenceBasis k ((↑) : s → FractionRing B) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set (FractionRing B)))
        (FractionRing B) := by
  haveI : Algebra.EssFiniteType k B := inferInstance
  haveI : Algebra.EssFiniteType B (FractionRing B) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType k (FractionRing B) := Algebra.EssFiniteType.comp k B _
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k _
  · haveI : ExpChar k p := .prime hp.out
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p hp.out (hH p hp.out hpk)
end GlobalTheory.SepPoint
