-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviParChart_leftModulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:45.678662+00:00
-- url     : https://prove2.me/submissions/3ceecc85-17e8-409b-b352-14bd2d8ca08e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_pi_eq


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
    (leviParChart F n γ δ).leftModulus l =
      distribHaarChar F (LinearEquiv.det (mulLeftLeviPar F n γ δ l)) := by
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq]
  congr 1
  exact LinearEquiv.det_conj (mulLeftLeviPar F n γ δ l) (leviParCoord F n γ δ)
end GroundTheory.Automorphic.Parabolic
