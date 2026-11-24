-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.rowE_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:24:59.408082+00:00
-- url     : https://prove2.me/submissions/667be0aa-9ee6-4baf-bd7c-7cd99c2f9a02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
open MvPolynomial
namespace GlobalTheory.Mem.GelfCheck
namespace _root_.GlobalTheory.Mem.GelfCheck
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) (a b c : Fin r) (t : Fin n) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (X (c, t)) = if b = c then X (a, t) else 0 := by
  rw [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.ext_iff]
  split_ifs with hbc
  · subst hbc
    simp [Finset.sum_ite_eq']
  · have hcb : ¬c = b := fun h => hbc h.symm
    simp [hcb]
end _root_.GlobalTheory.Mem.GelfCheck
end GlobalTheory.Mem.GelfCheck
