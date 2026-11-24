-- Prove2me | solution 1 for GlobalTheory.Conv.exists_le_halfRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:00:03.693861+00:00
-- url     : https://prove2.me/submissions/943d9718-72c9-4bfd-8c35-602d12f642ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_exists_forall_mem_halfRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
open GlobalTheory GlobalTheory.Conv
namespace GlobalTheory.Conv
theorem _root_.solution {A : Subalgebra ℂ ℂ⸨X⸩} (hA : A.FG)
    (h : A ≤ convLaurent.toSubalgebra) : ∃ T, A ≤ halfRing T := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, hT⟩ := exists_forall_mem_halfRing S.finite_toSet
    (fun s hs => h (Algebra.subset_adjoin hs))
  exact ⟨T, Algebra.adjoin_le fun s hs => hT s hs⟩
end GlobalTheory.Conv
