-- Prove2me | solution 1 for GlobalTheory.RowSpan.RowStable.inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:37.575555+00:00
-- url     : https://prove2.me/submissions/c2194b0b-9b7b-4272-8511-48952d98d26b

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
namespace RowStable
theorem _root_.solution {U V : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U) (hV : RowStable V) :
    RowStable (U ⊓ V) := fun g hg P hP => ⟨hU g hg P hP.1, hV g hg P hP.2⟩
end RowStable
end GlobalTheory.RowSpan
