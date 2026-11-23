-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.pow_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:37.625425+00:00
-- url     : https://prove2.me/submissions/a7fda028-19eb-4047-be4e-b1552f308795

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
variable {N : ℕ}
namespace GlobalTheory.CompanionTheory.CongIndex
theorem _root_.solution {ϖ : k} (h1 : valuation k ϖ < 1) {a b : ℕ} (h : a ≤ b) :
    valuation k (ϖ ^ b) ≤ valuation k (ϖ ^ a) := by
  rw [map_pow, map_pow]
  exact pow_le_pow_right_of_le_one' h1.le h
end GlobalTheory.CompanionTheory.CongIndex
