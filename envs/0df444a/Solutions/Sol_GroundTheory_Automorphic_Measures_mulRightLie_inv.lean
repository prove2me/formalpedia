-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.mulRightLie_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:14.074718+00:00
-- url     : https://prove2.me/submissions/cb1bf9ff-75ad-425b-b52f-799d31b8803a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (p : blockUpper F n β) :
    mulRightLie F n β p⁻¹ = (mulRightLie F n β p)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  ext A : 2
  show (A : Matrix (Fin n) (Fin n) F) * ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((p⁻¹ : blockUpper F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = A
  simp [mul_assoc]
end GroundTheory.Automorphic.Measures
