-- Prove2me | solution 1 for GlobalTheory.WeylDuality.mem_inV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:22.546305+00:00
-- url     : https://prove2.me/submissions/cb5ea497-6608-458c-a3a5-f6d02d081743

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl

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
theorem _root_.solution {r n : ℕ} (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (x : dualWeyl ℚ r n ν) : x ∈ inV ν M ↔ x.1 ∈ M := by
  exact Iff.rfl
end GlobalTheory.WeylDuality
