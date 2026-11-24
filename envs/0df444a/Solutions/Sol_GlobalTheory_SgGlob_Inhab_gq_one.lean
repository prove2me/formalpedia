-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.gq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:48.361258+00:00
-- url     : https://prove2.me/submissions/7d24f9e6-d28f-4b5f-a1c0-bfb79d0ddfad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (g : ℕ) (a b : E) :
    Gq (r := 1) σ 1 (1 + 2 * g) !![(g : E) * splitC σ g a b, 0; 0, -1 - (g : E)] =
      ((g : E) ^ 3 * (a * σ a + b * σ b)) ^ 2 := by
  simp [Gq, lead, splitC, hσ, Matrix.det_fin_two]
  ring
end GlobalTheory.SgGlob.Inhab
