-- Prove2me | solution 1 for GlobalTheory.MatchTerm.exists_one_of_inG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:28.261554+00:00
-- url     : https://prove2.me/submissions/eee5a3e4-3589-4ec5-b9dc-385cf9859b95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
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
theorem _root_.solution {N : NumD C} {k : ℕ} {p : N.QT k} (h : N.InG p) : ∃ q, N.QEq p q ∧ q.1.1 = 1 := by
  obtain ⟨z, hz⟩ := h
  refine ⟨p * N.qTriv k (-z), (N.qEq_iff _ _).2 ⟨_, rfl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change p.1.1.toAdd + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]
end GlobalTheory.MatchTerm
