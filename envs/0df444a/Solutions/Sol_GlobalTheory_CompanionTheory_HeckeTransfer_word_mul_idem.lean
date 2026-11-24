-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.word_mul_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:37:05.680279+00:00
-- url     : https://prove2.me/submissions/7011f082-460e-4c2c-928c-cb208aeedcf2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
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
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeTransfer
variable {R : Type*} [Ring R]
namespace GlobalTheory.CompanionTheory.HeckeTransfer
theorem _root_.solution {E : R} (hE : E * E = E) (l : List R) : word E l * E = word E l := by
  induction l with
  | nil => rw [word_nil, hE]
  | cons a l ih => rw [word_cons, mul_assoc, ih]
end GlobalTheory.CompanionTheory.HeckeTransfer
