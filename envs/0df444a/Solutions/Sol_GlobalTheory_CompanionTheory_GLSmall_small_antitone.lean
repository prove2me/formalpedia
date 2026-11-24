-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLSmall.small_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:27.915882+00:00
-- url     : https://prove2.me/submissions/7478b3f3-7962-4a09-921a-70858fc9559f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLSmall
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.GLSmall
theorem _root_.solution {ϖ : k} (h : valuation k ϖ < 1) (n : ℕ) : Antitone (small ϖ n) :=
  fun _ _ hab _ hg => ⟨fun i j => (hg.1 i j).trans (pow_le_pow_right_of_le_one' h.le hab),
    fun i j => (hg.2 i j).trans (pow_le_pow_right_of_le_one' h.le hab)⟩
end GlobalTheory.CompanionTheory.GLSmall
