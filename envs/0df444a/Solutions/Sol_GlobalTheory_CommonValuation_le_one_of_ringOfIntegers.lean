-- Prove2me | solution 1 for GlobalTheory.CommonValuation.le_one_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:15.005199+00:00
-- url     : https://prove2.me/submissions/b8bcec81-3169-4029-b461-e4a77a072854

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationIndexValuationCompat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CommonValuation
namespace GlobalTheory.CommonValuation
theorem _root_.solution {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ)
    (r : 𝓞 F) : u (algebraMap (𝓞 F) F r) ≤ 1 :=
  (Valuation.integer.integers u).isIntegral_iff_v_le_one.1 r.isIntegral_coe.tower_top
end GlobalTheory.CommonValuation
