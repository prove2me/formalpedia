-- Prove2me | solution 1 for GlobalTheory.MatchTerm.Cl.tor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:36.446733+00:00
-- url     : https://prove2.me/submissions/32e47a4a-e041-4454-b94c-d711e7ee569b

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
theorem _root_.solution {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ j x x') {t : Multiplicative N.X →* Cˣ} {ht : t ^ n ^ j = 1}
    {t' : Multiplicative N'.X →* Cˣ} {ht' : t' ^ n ^ j = 1} (e : μ.r _ (N.qTor t ht) (N'.qTor t' ht')) :
    t' (Multiplicative.ofAdd x') = t (Multiplicative.ofAdd x) := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  have := μ.wp _ _ _ _ _ e h
  rwa [NumD.wp_qTor, NumD.wp_qTor] at this
end Cl
end GlobalTheory.MatchTerm
