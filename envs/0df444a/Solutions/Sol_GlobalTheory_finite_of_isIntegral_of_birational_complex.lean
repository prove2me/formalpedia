-- Prove2me | solution 1 for GlobalTheory.finite_of_isIntegral_of_birational_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:15.462864+00:00
-- url     : https://prove2.me/submissions/34892efd-0fd8-4be3-a2f7-349e939f338f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FiniteOfIsIntegralOfBirationalOfPresentation
import Theorems.Thm_GlobalTheory_finite_of_isIntegral_of_birational_of_finite_over_normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hg
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  exact finite_of_isIntegral_of_birational_of_finite_over_normal (MvPolynomial (Fin d) ℂ) A B hb
end GlobalTheory
