-- Prove2me | solution 1 for GlobalTheory.MatchTerm.Cl.shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:32.746599+00:00
-- url     : https://prove2.me/submissions/4f57f234-eb90-44ae-9fa5-319116b20663

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_MatchTerm_r_left
import Theorems.Thm_GlobalTheory_MatchTerm_r_right
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_iff


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
theorem _root_.solution {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ j x x') (z : N.X) (z' : N'.X) :
    Cl μ j (x + n ^ j • z) (x' + n ^ j • z') := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  exact ⟨p * N.qTriv _ z, p' * N'.qTriv _ z',
    r_right μ (r_left μ h ((N.qEq_iff _ _).2 ⟨z, rfl⟩)) ((N'.qEq_iff _ _).2 ⟨z', rfl⟩), rfl, rfl⟩
end Cl
end GlobalTheory.MatchTerm
