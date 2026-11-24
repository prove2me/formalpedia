-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.haar_eq_haarAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:23:27.228123+00:00
-- url     : https://prove2.me/submissions/dc896c6c-b7a1-4844-b400-4432e583e2b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_haarAt_mul

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.LinChange
theorem _root_.solution {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) :
    haar φ = haarAt R φ := by
  have hs : IsSB φ := ⟨R, hR, h⟩
  rw [haar, dif_pos hs, ← haarAt_mul _ R hs.choose_spec.1 hR φ hs.choose_spec.2, mul_comm,
    haarAt_mul _ _ hR hs.choose_spec.1 φ h]
end GlobalTheory.SW.LinChange
