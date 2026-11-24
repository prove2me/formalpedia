-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.ind_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:22:55.055299+00:00
-- url     : https://prove2.me/submissions/c110757a-8690-4763-9885-683a75acfe2d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution {l : ℕ} (i : Fin l) : Antitone (ind i) := by
  intro a b hab
  simp only [ind]
  split_ifs <;> first | exact le_rfl | exact Nat.zero_le _ | exact absurd (hab.trans ‹_›) ‹_›
end GlobalTheory.CompanionTheory.CartanU
