-- Prove2me | solution 1 for GlobalTheory.SW.ThetaProd.hasLevel_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:29:34.876692+00:00
-- url     : https://prove2.me/submissions/ed31b714-38da-46e9-b3b5-ee1c4c7e517e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaMulConjEqBlockTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ThetaProd
namespace GlobalTheory.SW.ThetaProd
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (S : ℕ)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : HasLevel (S * R) φ := by
  refine ⟨fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h.1 x hx k i).nsmul S
    simpa [mul_assoc] using this
  · have := h.2 x ((S : ℚ) • y) fun k i => by simpa using (hy k i).nsmul S
    rw [← this, smul_smul, Nat.cast_mul, mul_comm]
end GlobalTheory.SW.ThetaProd
