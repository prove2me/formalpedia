-- Prove2me | solution 1 for GlobalTheory.MatchTerm.r_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:34.744534+00:00
-- url     : https://prove2.me/submissions/36e408ae-f6e0-4309-adb2-a0b63f6bb56e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence


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
theorem _root_.solution {k : ℕ} {p q : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (e : N.QEq p q) : μ.r k q p' :=
  (μ.eqv k p q p' p' h e).2 ((N'.qEq_equivalence k).refl _)
end GlobalTheory.MatchTerm
