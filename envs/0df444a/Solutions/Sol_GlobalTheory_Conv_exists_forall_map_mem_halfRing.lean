-- Prove2me | solution 1 for GlobalTheory.Conv.exists_forall_map_mem_halfRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:18.451799+00:00
-- url     : https://prove2.me/submissions/101449ee-439b-4d45-bbe3-32f03d4d80c1

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
theorem _root_.solution {S A : Type*} [CommRing S] [CommRing A] [Algebra S A]
    [Algebra.FiniteType S A] (φ : A →+* convLaurent) {T : ℝ}
    (hS : ∀ c : S, (φ (algebraMap S A c) : ℂ⸨X⸩) ∈ halfRing T) :
    ∃ T' ≥ T, ∀ a, (φ a : ℂ⸨X⸩) ∈ halfRing T' := by
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := S) (A := A)
  obtain ⟨T₁, hT₁⟩ := exists_forall_mem_halfRing
    (S := (fun a => (φ a : ℂ⸨X⸩)) '' (t : Set A)) (t.finite_toSet.image _)
    (by rintro _ ⟨a, -, rfl⟩; exact (φ a).2)
  refine ⟨max T T₁, le_max_left _ _, fun a => ?_⟩
  have key : (⊤ : Subalgebra S A).toSubring ≤
      (halfRing (max T T₁)).toSubring.comap ((convLaurent.val : convLaurent →+* ℂ⸨X⸩).comp φ) := by
    rw [← ht, Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro _ (⟨c, rfl⟩ | ha)
    · exact halfRing_mono (le_max_left _ _) (hS c)
    · exact halfRing_mono (le_max_right _ _) (hT₁ _ ⟨_, ha, rfl⟩)
  exact key (show a ∈ (⊤ : Subalgebra S A).toSubring from Algebra.mem_top (R := S))
end GlobalTheory.Conv
