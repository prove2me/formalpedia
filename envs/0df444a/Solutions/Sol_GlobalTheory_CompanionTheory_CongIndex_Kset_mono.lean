-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.Kset_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:37.667791+00:00
-- url     : https://prove2.me/submissions/18a46581-f0ef-4c85-a126-9f8142942689

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_pow_le_of_le

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
theorem _root_.solution {ϖ : k} (h1 : valuation k ϖ < 1) {c c' : Fin N → Fin N → ℕ}
    (h : ∀ i j, c i j ≤ c' i j) : Kset ϖ c' ⊆ Kset ϖ c :=
  fun _ hg i j => (hg i j).trans (pow_le_of_le h1 (h i j))
end GlobalTheory.CompanionTheory.CongIndex
