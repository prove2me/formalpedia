-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PrincipalLat.isPrincipalIdealRing_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:10.368514+00:00
-- url     : https://prove2.me/submissions/2f8fe508-1d4f-4bd1-a7ca-4b6becbbc079

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_PrincipalLat_isIntegral_pi__b1b6cca95627
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_isDiscreteValuationRing_integralClosure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLat
namespace GlobalTheory.UnitLemma.PrincipalLat
theorem _root_.solution {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra E A] [Algebra O A]
    [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O E (A ⧸ I.asIdeal)
    infer_instance
  haveI : Finite (MaximalSpectrum A) := inferInstance
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]
end GlobalTheory.UnitLemma.PrincipalLat
