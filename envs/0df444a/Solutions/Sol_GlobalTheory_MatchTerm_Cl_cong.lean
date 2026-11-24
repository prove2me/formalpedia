-- Prove2me | solution 1 for GlobalTheory.MatchTerm.Cl.cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:24.354729+00:00
-- url     : https://prove2.me/submissions/c59257e5-064c-4b79-959e-9d0104e5c62c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_MatchTerm_r_inv

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
theorem _root_.solution (hA : μ.A) {j : ℕ} {x y : N.X} {x' y' : N'.X} (h : Cl μ j x x') (h' : Cl μ j y y') :
    (∃ z, y = x + n ^ j • z) ↔ ∃ z', y' = x' + n ^ j • z' := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  obtain ⟨q, q', h', rfl, rfl⟩ := h'
  have := (hA.2 j _ _ (μ.mul _ _ _ _ _ (r_inv μ ⟨j, rfl⟩ h) h')).1
  simp only [← neg_add_eq_iff_eq_add]
  exact this
end Cl
end GlobalTheory.MatchTerm
