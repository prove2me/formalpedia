-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:41:01.063949+00:00
-- url     : https://prove2.me/submissions/b345bb4f-f41f-4857-b5fb-615de6e05225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLatDVR_isReduced_of_charpoly_separable
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLatDVR_isPrincipalIdealRing_integralClosure
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_eq_mulLat_of_isPrincipalIdealRing
import Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_isPrincipalIdealRing_integralClosure


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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLatDVR
namespace GlobalTheory.UnitLemma.PrincipalLatDVR
theorem _root_.solution : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N →
    (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) →
    ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep N hN hst
  haveI := isReduced_of_charpoly_separable g hsep
  haveI := isPrincipalIdealRing_integralClosure (O := O) (E := E) (A := A)
  exact PrincipalLat.eq_mulLat_of_isPrincipalIdealRing N hN hst
end GlobalTheory.UnitLemma.PrincipalLatDVR
