-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mulRightLeviPar_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:48:57.535183+00:00
-- url     : https://prove2.me/submissions/69ef1dd5-9990-409c-a726-13c23388c863

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



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
    mulRightLeviPar F n γ δ l⁻¹ = (mulRightLeviPar F n γ δ l)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  ext A : 2
  show (A : Matrix (Fin n) (Fin n) F) * ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((l⁻¹ : leviPar F n γ δ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = A
  simp [mul_assoc]
end GroundTheory.Automorphic.Parabolic
