-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:02.665824+00:00
-- url     : https://prove2.me/submissions/fa4b69ed-8a5a-4c94-b043-ef6fbc401430

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviParChart_leftModulus
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviParChart_rightModulus
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mulRightLeviPar_inv
import Theorems.Thm_GroundTheory_Automorphic_Measures_LinearChart_modularCharacter_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α α' : Type*} [LinearOrder α] [LinearOrder α'] (γ : Fin n → α) (δ : Fin n → α')
variable {F n γ δ}
variable (F n γ δ)
variable {F n γ δ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (l : leviPar F n γ δ) :
    modularCharacter l = distribHaarChar F (LinearEquiv.det (adLeviPar F n γ δ l)) := by
  borelize F ↥(leviPar F n γ δ)
  rw [(leviParChart F n γ δ).modularCharacter_eq l, leviParChart_leftModulus,
    leviParChart_rightModulus]
  have : adLeviPar F n γ δ l = mulRightLeviPar F n γ δ l⁻¹ * mulLeftLeviPar F n γ δ l := rfl
  rw [this, mulRightLeviPar_inv, map_mul, map_inv, map_mul, map_inv, div_eq_mul_inv, mul_comm]
end GroundTheory.Automorphic.Parabolic
