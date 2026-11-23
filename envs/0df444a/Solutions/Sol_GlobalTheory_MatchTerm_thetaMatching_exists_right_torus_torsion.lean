-- Prove2me | solution 1 for GlobalTheory.MatchTerm.thetaMatching_exists_right_torus_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:38.996322+00:00
-- url     : https://prove2.me/submissions/944c022f-00e3-4c20-aaf2-d248b8688f94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_MatchTerm_r_right
import Theorems.Thm_GlobalTheory_MatchTerm_exists_tor_of_inT
import Theorems.Thm_GlobalTheory_MatchTerm_inT_tor

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
theorem _root_.solution (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (t : Multiplicative N.X →* Cˣ) (ht : t ^ k = 1) :
    ∃ t' ht', μ.r k (N.qTor t ht) (N'.qTor t' ht') := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j (N.qTor t ht)
  obtain ⟨t', ht', e⟩ := exists_tor_of_inT ((hA.2 j _ u hu).2.1 (inT_tor t ht))
  exact ⟨t', ht', r_right μ hu e⟩
end GlobalTheory.MatchTerm
