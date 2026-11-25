-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.coe_parabolicCoord_symm_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:30.032983+00:00
-- url     : https://prove2.me/submissions/45005892-6064-4be2-b2ae-5bd405921b01

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
theorem _root_.solution (t : ParabolicIndex n β) :
    (((parabolicCoord F n β).symm (Pi.single t 1) : lieParabolic F n β) :
      Matrix (Fin n) (Fin n) F) = Matrix.single t.1.1 t.1.2 1 := by
  ext i j
  show (if h : ¬ β j < β i then (Pi.single t (1 : F) : ParabolicIndex n β → F) ⟨(i, j), h⟩
    else 0) = _
  rw [Matrix.single_apply]
  by_cases hij : t.1.1 = i ∧ t.1.2 = j
  · obtain ⟨h1, h2⟩ := hij
    have ht : (⟨(i, j), h1 ▸ h2 ▸ t.2⟩ : ParabolicIndex n β) = t := by
      ext <;> simp [← h1, ← h2]
    rw [dif_pos (h1 ▸ h2 ▸ t.2), if_pos ⟨h1, h2⟩, ht, Pi.single_eq_same]
  · rw [if_neg hij]
    split_ifs with h
    · rfl
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hij ⟨rfl, rfl⟩
end GroundTheory.Automorphic.Measures
