-- Prove2me | solution 1 for GlobalTheory.WeylDuality.fockQ_hw_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:22.835945+00:00
-- url     : https://prove2.me/submissions/fd0339e9-66b9-4f94-8f18-05f60c63bb01

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : 0 < fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
  exact (fockQPos _ (hw ℚ hn ν) (hw ℚ hn ν)).2 (hwNe ℚ r n hn ν)
end GlobalTheory.WeylDuality
