-- Prove2me | solution 1 for GlobalTheory.Chow.exists_ringKrullDim_eq_and_trdeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:38.788036+00:00
-- url     : https://prove2.me/submissions/d8f41fc0-a573-40f9-adac-101bcc6d913d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_Chow_ringKrullDim_eq_of_isIntegral
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.Chow
theorem _root_.solution (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, ringKrullDim A = s ∧ Algebra.trdeg K A = s := by
  obtain ⟨s, g, hg, hg'⟩ := exists_integral_inj_algHom_of_fg K A
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  have : IsScalarTower K (MvPolynomial (Fin s) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  refine ⟨s, ?_, ?_⟩
  · simp [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) K) A, ringKrullDim_eq_zero_of_field]
  · simp [← trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A), trdeg_eq_zero]
end GlobalTheory.Chow
