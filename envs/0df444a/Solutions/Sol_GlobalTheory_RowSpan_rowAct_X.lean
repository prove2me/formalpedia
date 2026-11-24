-- Prove2me | solution 1 for GlobalTheory.RowSpan.rowAct_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:48.013258+00:00
-- url     : https://prove2.me/submissions/a6c3178a-99bd-4daa-bdb0-cdfe2bdc7d89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.RowSpan
theorem _root_.solution (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k) (ℓ : Letter T r n) :
    rowAct g (X ℓ) = ∑ j, C (g ℓ.1 ℓ.2.1 j) * X ⟨ℓ.1, j, ℓ.2.2⟩ := aeval_X _ _
end GlobalTheory.RowSpan
