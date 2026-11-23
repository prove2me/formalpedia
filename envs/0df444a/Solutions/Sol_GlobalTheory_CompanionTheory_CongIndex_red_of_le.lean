-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.red_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:38.190931+00:00
-- url     : https://prove2.me/submissions/8aead675-3dd8-49f6-93f5-edeb6bbc47ac

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
theorem _root_.solution {ϖ : k} (h0 : ϖ ≠ 0) {c : ℕ} {x : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) :
    red ϖ c x = IsLocalRing.residue _ ⟨x * (ϖ ^ c)⁻¹, scaled_le h0 hx⟩ := by
  unfold red
  rw [dif_pos (scaled_le h0 hx)]
end GlobalTheory.CompanionTheory.CongIndex
