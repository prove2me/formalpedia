-- Prove2me | solution 1 for GlobalTheory.MatchTerm.r_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:36.949685+00:00
-- url     : https://prove2.me/submissions/0c92ccb9-b36a-4cf4-95e0-6e12bbc14e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_MatchTerm_r_right
import Theorems.Thm_GlobalTheory_MatchTerm_qeq_right
import Theorems.Thm_GlobalTheory_MatchTerm_r_one
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
theorem _root_.solution {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') :
    μ.r k p⁻¹ p'⁻¹ := by
  have h1 := r_one μ hk
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j p⁻¹
  have h2 := μ.mul _ _ _ _ _ h hu
  rw [mul_inv_cancel] at h2
  obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 (qeq_right μ h1 h2)
  refine r_right μ hu ((N'.qEq_equivalence _).symm ((N'.qEq_iff _ _).2 ⟨z, ?_⟩))
  rw [one_mul] at hz
  rw [← hz, inv_mul_cancel_left]
end GlobalTheory.MatchTerm
