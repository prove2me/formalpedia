-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.val_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:12.771181+00:00
-- url     : https://prove2.me/submissions/653323f3-2ed6-4074-bdc0-ed8f379ada28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CongIndex
theorem _root_.solution {c : ℕ} {ϖ x y : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) (hy : valuation k y ≤ valuation k (ϖ ^ c)) :
    valuation k (x + y) ≤ valuation k (ϖ ^ c) :=
  (valuation k).map_add_le hx hy
end GlobalTheory.CompanionTheory.CongIndex
