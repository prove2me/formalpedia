-- Prove2me | solution 1 for GlobalTheory.MatchTerm.Cl.down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:31.284819+00:00
-- url     : https://prove2.me/submissions/88f84857-d514-4aae-a973-85f929199379

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_MatchTerm_r_pow
import Theorems.Thm_GlobalTheory_MatchTerm_r_incl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
namespace GlobalTheory.MatchTerm
namespace Cl
theorem _root_.solution (hn : n ≠ 0) {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ (j + 1) x x') : Cl μ j x x' := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  refine ⟨⟨(p.1.1, p.1.2 ^ n), ?_⟩, ⟨(p'.1.1, p'.1.2 ^ n), ?_⟩, ?_, rfl, rfl⟩
  · rw [NumD.mem_QT, ← pow_mul, ← pow_succ']; exact p.2
  · rw [NumD.mem_QT, ← pow_mul, ← pow_succ']; exact p'.2
  · exact (r_incl μ n (pow_succ n j) hn rfl rfl rfl rfl).2 (r_pow μ ⟨_, rfl⟩ h n)
end Cl
end GlobalTheory.MatchTerm
