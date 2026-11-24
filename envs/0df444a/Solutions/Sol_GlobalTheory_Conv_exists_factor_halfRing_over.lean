-- Prove2me | solution 1 for GlobalTheory.Conv.exists_factor_halfRing_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:54.659468+00:00
-- url     : https://prove2.me/submissions/c8f79fab-5b13-426d-b659-ccfc02ec1a17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_exists_forall_map_mem_halfRing

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
    [Algebra.FiniteType S A] (b : S →+* ℂ) (φ : A →+* convLaurent)
    (hφ : φ.comp (algebraMap S A) = (algebraMap ℂ convLaurent).comp b) (T₀ : ℝ) :
    ∃ T ≥ T₀, ∃ ψ : A →+* halfRing T, (halfIncl T : halfRing T →+* convLaurent).comp ψ = φ ∧
      ψ.comp (algebraMap S A) = (algebraMap ℂ (halfRing T)).comp b := by
  obtain ⟨T, hT, hmem⟩ := exists_forall_map_mem_halfRing φ (T := T₀) fun c => by
    have hc : φ (algebraMap S A c) = algebraMap ℂ convLaurent (b c) := RingHom.congr_fun hφ c
    rw [hc]
    exact (halfRing T₀).algebraMap_mem (b c)
  refine ⟨T, hT, RingHom.codRestrict ((convLaurent.val : convLaurent →+* ℂ⸨X⸩).comp φ)
    (halfRing T) hmem, RingHom.ext fun a => rfl, RingHom.ext fun c => Subtype.ext ?_⟩
  have hc : φ (algebraMap S A c) = algebraMap ℂ convLaurent (b c) := RingHom.congr_fun hφ c
  show (φ (algebraMap S A c) : ℂ⸨X⸩) = algebraMap ℂ ℂ⸨X⸩ (b c)
  rw [hc]
  rfl
end GlobalTheory.Conv
