-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar_diagPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:51:34.578866+00:00
-- url     : https://prove2.me/submissions/475bc20c-9eff-4f24-b778-86ca423c427d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_modularCharacter_leviPar_of_diagonal
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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (μ : Fin n → ℤ) :
    modularCharacter (⟨Cartan.diagPow F n μ, diagPow_mem_leviPar μ⟩ : leviPar F n γ δ) =
      ∏ s : {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2},
        modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
          modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) := by
  rw [modularCharacter_leviPar_of_diagonal _ fun i j hij => by
    show (Cartan.diagPow F n μ : Matrix (Fin n) (Fin n) F) i j = 0
    rw [Cartan.coe_diagPow, diagonal_apply_ne _ hij]]
  simp only [Cartan.coe_diagPow, diagonal_apply_eq]
end GroundTheory.Automorphic.Parabolic
