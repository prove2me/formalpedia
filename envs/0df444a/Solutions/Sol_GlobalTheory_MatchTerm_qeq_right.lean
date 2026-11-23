-- Prove2me | solution 1 for GlobalTheory.MatchTerm.qeq_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:16.386164+00:00
-- url     : https://prove2.me/submissions/3af1d382-dd95-4e1e-9f87-954ea2aa52c1

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
theorem _root_.solution {k : ℕ} {p : N.QT k} {p' q' : N'.QT k} (h : μ.r k p p') (e : μ.r k p q') : N'.QEq p' q' :=
  (μ.eqv k p p p' q' h ((N.qEq_equivalence k).refl _)).1 e
end GlobalTheory.MatchTerm
