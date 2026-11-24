-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:49.808834+00:00
-- url     : https://prove2.me/submissions/e0f54ae5-97c1-4838-ae7e-2f6cb214b781

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsFractionRingInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalFieldValuationRing
namespace GlobalTheory.CompanionTheory.LocalFieldValuationRing
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsFractionRing (ValuativeRel.valuation k).integer k :=
  (Valuation.integer.integers (ValuativeRel.valuation k)).isFractionRing
end GlobalTheory.CompanionTheory.LocalFieldValuationRing
