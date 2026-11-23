-- Prove2me | solution 1 for GlobalTheory.MatchTerm.r_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:58.349934+00:00
-- url     : https://prove2.me/submissions/2cbe56c7-f428-4696-9500-f4df70e4a357

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_MatchTerm_r_right
import Theorems.Thm_GlobalTheory_MatchTerm_qeq_right
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence
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
theorem _root_.solution {k : ℕ} (hk : ∃ j, k = n ^ j) : μ.r k 1 1 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j 1
  have h := μ.mul _ _ _ _ _ hu hu
  rw [mul_one] at h
  obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 (qeq_right μ hu h)
  refine r_right μ hu ((N'.qEq_equivalence _).symm ((N'.qEq_iff _ _).2 ⟨z, ?_⟩))
  rw [one_mul]
  exact mul_left_cancel hz
end GlobalTheory.MatchTerm
