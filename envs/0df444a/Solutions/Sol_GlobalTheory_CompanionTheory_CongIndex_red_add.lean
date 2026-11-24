-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.red_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:04.615578+00:00
-- url     : https://prove2.me/submissions/cbd06a39-8491-4a21-9fd3-3068dd5cba14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_of_le
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_val_add_le

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
theorem _root_.solution {ϖ : k} (h0 : ϖ ≠ 0) {c : ℕ} {x y : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) (hy : valuation k y ≤ valuation k (ϖ ^ c)) :
    red ϖ c (x + y) = red ϖ c x + red ϖ c y := by
  rw [red_of_le h0 hx, red_of_le h0 hy, red_of_le h0 (val_add_le hx hy), ← map_add]
  congr 1
  apply Subtype.ext
  simp [add_mul]
end GlobalTheory.CompanionTheory.CongIndex
