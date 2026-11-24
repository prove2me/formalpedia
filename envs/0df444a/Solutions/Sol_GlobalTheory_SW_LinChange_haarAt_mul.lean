-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.haarAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:51.224524+00:00
-- url     : https://prove2.me/submissions/506d93a8-9f35-4d1b-a8f2-d78a5fdadb3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_intM_nat_smul
import Theorems.Thm_GlobalTheory_SW_LinChange_haarAt_comp

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
theorem _root_.solution (R M : ℕ) (hR : 0 < R) (hM : 0 < M) (φ : Matrix κ ι K → ℂ)
    (h : HasLevel R φ) : haarAt (R * M) φ = haarAt R φ := by
  simpa using haarAt_comp (LinearEquiv.refl ℚ _) R M hR hM (fun y hy => intM_nat_smul M hy) φ h
end GlobalTheory.SW.LinChange
