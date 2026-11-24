-- Prove2me | solution 1 for GlobalTheory.FockAdj.fockQ_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:47:05.134659+00:00
-- url     : https://prove2.me/submissions/41c44ef4-5736-4262-8e88-26376ac14389

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FockQWordRowActAdj
import Theorems.Thm_GlobalTheory_FockAdj_map_rowAct
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockRowAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_cast
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
open MvPolynomial Formalism.GradedWeylDivisibility
open GlobalTheory GlobalTheory.FockAdj
namespace GlobalTheory.FockAdj
theorem _root_.solution : Formalism.GradedWeylDivisibility.FockQRowAct := by
  intro r n g P Q
  have ht : (g.map (Rat.castHom ℂ)).conjTranspose = g.transpose.map (Rat.castHom ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h : ((fockQ (rowAct ℚ g P) Q : ℚ) : ℂ) = ((fockQ P (rowAct ℚ g.transpose Q) : ℚ) : ℂ) := by
    rw [lfockq_cast, lfockq_cast, map_rowAct, map_rowAct, fockRowAdj, ht]
  exact_mod_cast h
end GlobalTheory.FockAdj
