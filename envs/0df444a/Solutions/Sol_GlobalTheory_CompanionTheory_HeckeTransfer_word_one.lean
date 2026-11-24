-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.word_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:08.103186+00:00
-- url     : https://prove2.me/submissions/70e3ce2d-bfd9-4806-8286-647208afe8c5

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
theorem _root_.solution (l : List R) : word (1 : R) l = l.prod := by
  induction l with
  | nil => rw [word_nil, List.prod_nil]
  | cons a l ih => rw [word_cons, ih, List.prod_cons, one_mul]
end GlobalTheory.CompanionTheory.HeckeTransfer
