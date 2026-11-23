-- Prove2me | solution 1 for GlobalTheory.MatchTerm.r_incl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:28.475231+00:00
-- url     : https://prove2.me/submissions/8042a46d-f82b-4934-a419-dc5bd2472fa3

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
theorem _root_.solution {k K : ℕ} (k' : ℕ) (hK : K = k * k') (hk : k' ≠ 0) {p : N.QT k} {p' : N'.QT k} {q : N.QT K}
    {q' : N'.QT K} (h1 : q.1.1 = p.1.1 ^ k') (h2 : q.1.2 = p.1.2) (h3 : q'.1.1 = p'.1.1 ^ k')
    (h4 : q'.1.2 = p'.1.2) : μ.r k p p' ↔ μ.r K q q' := by
  subst hK
  exact μ.incl k k' p p' q q' hk h1 h2 h3 h4
end GlobalTheory.MatchTerm
