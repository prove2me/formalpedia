-- Prove2me | solution 1 for GlobalTheory.ThetaGLSub.aug_le_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:16.471867+00:00
-- url     : https://prove2.me/submissions/67ef75ab-1f1b-4ac6-83b7-7490e030bc69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSubAug
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.ThetaGLSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
variable {m : ℕ}
namespace GlobalTheory.ThetaGLSub
theorem _root_.solution (χ : GL (Fin n) k →* ℂˣ) : aug m χ ≤ SB (Matrix (Fin n) (Fin m) k) := by
  rw [aug, Submodule.span_le]
  rintro _ ⟨h, Φ, hΦ, rfl⟩
  exact Submodule.sub_mem _ (Model.om_mem_SB 1 1 h hΦ) (Submodule.smul_mem _ _ hΦ)
end GlobalTheory.ThetaGLSub
