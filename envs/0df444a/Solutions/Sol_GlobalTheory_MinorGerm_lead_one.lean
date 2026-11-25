-- Prove2me | solution 1 for GlobalTheory.MinorGerm.lead_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:26.843806+00:00
-- url     : https://prove2.me/submissions/3d618820-cd22-4b35-a54d-5f45162fd839

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
theorem _root_.solution : Lead p (0 : σ →₀ ℕ) (1 : MvPolynomial σ C) := by
  classical
  refine ⟨by simp, by simpa using MvPolynomial.isHomogeneous_one σ C, by simp⟩
end GlobalTheory.MinorGerm
