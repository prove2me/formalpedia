-- Prove2me | solution 1 for GlobalTheory.MatchTerm.exists_tor_of_inT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:57.983427+00:00
-- url     : https://prove2.me/submissions/dc94c152-c8b7-4b31-896d-fecd39ae734d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff
import Theorems.Thm_GlobalTheory_Ex_NumD_tor_injective


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
theorem _root_.solution {N : NumD C} {k : ℕ} {p : N.QT k} (h : N.InT p) :
    ∃ t ht, N.QEq p (N.qTor t ht) := by
  obtain ⟨q, e, h1, h2⟩ := h
  obtain ⟨t, ht⟩ := (N.exists_tor_iff _).2 h2
  have h3 : t ^ k = 1 := by
    apply N.tor_injective
    rw [N.tor_pow, ht, N.mem_QT.1 q.2, h1, N.tor_one]
    exact N.io_zero
  refine ⟨t, h3, ?_⟩
  have : q = N.qTor t h3 := Subtype.ext (Prod.ext h1 ht.symm)
  exact this ▸ e
end GlobalTheory.MatchTerm
