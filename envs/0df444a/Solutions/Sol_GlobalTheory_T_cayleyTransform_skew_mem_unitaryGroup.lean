-- Prove2me | solution 1 for GlobalTheory.T.cayleyTransform_skew_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:29.581281+00:00
-- url     : https://prove2.me/submissions/94ba9479-2a7d-4314-99f3-86ac5e41d782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CayleyTransformSkewMemUnitaryGroup
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CayleyTransformSkewMemUnitaryGroupStatement
import Theorems.Thm_GlobalTheory_CayleyUnitary_cayley_mem_UJ


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
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J S : Matrix (Fin n) (Fin n) E),
    J.det ≠ 0 → Formalism.UG.cT σ S * J + J * S = 0 → (1 - S).det ≠ 0 →
    ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ σ J ∧ (γ : Matrix (Fin n) (Fin n) E) = (1 + S) * (1 - S)⁻¹ := by
  first | exact @GlobalTheory.CayleyUnitary.cayley_mem_UJ | exact GlobalTheory.CayleyUnitary.cayley_mem_UJ | (intros; apply GlobalTheory.CayleyUnitary.cayley_mem_UJ <;> assumption)
end _root_.GlobalTheory.T
