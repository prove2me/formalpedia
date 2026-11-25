-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.inv_apply_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:59.709455+00:00
-- url     : https://prove2.me/submissions/60e00686-fd09-40d5-a24c-f385e07a3b2f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mul_inv_apply_of_diagonal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_self_ne_zero_of_diagonal
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
theorem _root_.solution {g : GL (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) (i j : Fin n) :
    ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      if i = j then ((g : Matrix (Fin n) (Fin n) F) i i)⁻¹ else 0 := by
  have h := mul_inv_apply_of_diagonal hg i j
  have h0 := apply_self_ne_zero_of_diagonal hg i
  have : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((g : Matrix (Fin n) (Fin n) F) i i)⁻¹ * (1 : Matrix (Fin n) (Fin n) F) i j := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
  rw [this, one_apply]
  split_ifs <;> simp
end GroundTheory.Automorphic.Parabolic
