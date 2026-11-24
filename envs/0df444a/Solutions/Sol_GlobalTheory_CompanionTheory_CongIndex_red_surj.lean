-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.red_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:22.000203+00:00
-- url     : https://prove2.me/submissions/f299ba57-101f-4142-acbc-7feb1a299f63

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_of_le

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
theorem _root_.solution {ϖ : k} (h0 : ϖ ≠ 0) (c : ℕ)
    (r : IsLocalRing.ResidueField (valuation k).integer) :
    ∃ x : k, valuation k x ≤ valuation k (ϖ ^ c) ∧ red ϖ c x = r := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  have hy : valuation k (y : k) ≤ 1 := y.2
  have hx : valuation k ((y : k) * ϖ ^ c) ≤ valuation k (ϖ ^ c) := by
    rw [map_mul]; exact mul_le_of_le_one_left' hy
  refine ⟨(y : k) * ϖ ^ c, hx, ?_⟩
  rw [red_of_le h0 hx]
  congr 1
  apply Subtype.ext
  have : ϖ ^ c ≠ 0 := pow_ne_zero c h0
  simp [this]
end GlobalTheory.CompanionTheory.CongIndex
