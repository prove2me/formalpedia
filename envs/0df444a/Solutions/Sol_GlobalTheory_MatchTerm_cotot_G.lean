-- Prove2me | solution 1 for GlobalTheory.MatchTerm.cotot_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:34.983799+00:00
-- url     : https://prove2.me/submissions/41cd2bb6-a45d-4ac7-a376-ccfb6166c7a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_MatchTerm_r_left
import Theorems.Thm_GlobalTheory_MatchTerm_exists_one_of_inG

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
theorem _root_.solution (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (p' : N'.QT k) (hp : p'.1.1 = 1) :
    ∃ p, μ.r k p p' ∧ p.1.1 = 1 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.cotot j p'
  obtain ⟨q, e, hq⟩ := exists_one_of_inG ((hA.2 j u p' hu).1.2 ⟨0, by simp [hp]⟩)
  exact ⟨q, r_left μ hu e, hq⟩
end GlobalTheory.MatchTerm
