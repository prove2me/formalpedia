-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:07:51.293725+00:00
-- url     : https://prove2.me/submissions/090cae11-d818-4254-8655-6fdb80a4b035

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_eq_mulLat_of_isPrincipalIdealRing
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_isPrincipalIdealRing_integralClosure
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_eq_zero_of_isNilpotent


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
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
    ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  intro K B hsep J hJ hst
  haveI : IsReduced B.A := ⟨fun a ha => Centraliser.eq_zero_of_isNilpotent B hsep a ha⟩
  haveI := isPrincipalIdealRing_integralClosure (O := K.O) (E := K.E) (A := B.A)
  exact eq_mulLat_of_isPrincipalIdealRing J hJ hst
end GlobalTheory.UnitLemma.PrincipalLat
