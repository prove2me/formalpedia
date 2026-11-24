-- Prove2me | solution 1 for GlobalTheory.EmbUnitBallConj.ext_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:47.540644+00:00
-- url     : https://prove2.me/submissions/677c2786-de40-426e-8182-5314533f58b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicEmbeddingsConjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.EmbUnitBallConj
variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E]
namespace GlobalTheory.EmbUnitBallConj
theorem _root_.solution (a : E →+* PadicAlgCl l) (c : ℚ_[l]) (x : E) : ext a (c ⊗ₜ x) = c • a x := by
  simp [ext, Algebra.smul_def, Algebra.ofId_apply]
end GlobalTheory.EmbUnitBallConj
