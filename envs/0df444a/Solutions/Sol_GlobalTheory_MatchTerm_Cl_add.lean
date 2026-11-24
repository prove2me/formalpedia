-- Prove2me | solution 1 for GlobalTheory.MatchTerm.Cl.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:29.823861+00:00
-- url     : https://prove2.me/submissions/7d44928e-caef-441f-90db-920f63e76199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion

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
theorem _root_.solution {j : ℕ} {x y : N.X} {x' y' : N'.X} (h : Cl μ j x x') (h' : Cl μ j y y') :
    Cl μ j (x + y) (x' + y') := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  obtain ⟨q, q', h', rfl, rfl⟩ := h'
  exact ⟨_, _, μ.mul _ _ _ _ _ h h', rfl, rfl⟩
end Cl
end GlobalTheory.MatchTerm
