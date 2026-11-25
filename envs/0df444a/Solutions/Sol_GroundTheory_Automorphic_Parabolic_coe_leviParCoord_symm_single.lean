-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.coe_leviParCoord_symm_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:08.603784+00:00
-- url     : https://prove2.me/submissions/c8b8fe91-cf7f-4d93-bd19-0c49b05cf805

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (t : LeviParIndex n γ δ) :
    (((leviParCoord F n γ δ).symm (Pi.single t 1) : lieLeviPar F n γ δ) :
      Matrix (Fin n) (Fin n) F) = Matrix.single t.1.1 t.1.2 1 := by
  ext i j
  show (if h : γ i = γ j ∧ ¬ δ j < δ i then (Pi.single t (1 : F) : LeviParIndex n γ δ → F)
    ⟨(i, j), h⟩ else 0) = _
  rw [Matrix.single_apply]
  by_cases hij : t.1.1 = i ∧ t.1.2 = j
  · obtain ⟨h1, h2⟩ := hij
    have ht : (⟨(i, j), h1 ▸ h2 ▸ t.2⟩ : LeviParIndex n γ δ) = t := by
      ext <;> simp [← h1, ← h2]
    rw [dif_pos (h1 ▸ h2 ▸ t.2), if_pos ⟨h1, h2⟩, ht, Pi.single_eq_same]
  · rw [if_neg hij]
    split_ifs with h
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hij ⟨rfl, rfl⟩
    · rfl
end GroundTheory.Automorphic.Parabolic
