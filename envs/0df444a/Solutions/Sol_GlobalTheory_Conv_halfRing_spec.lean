-- Prove2me | solution 1 for GlobalTheory.Conv.halfRing_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:53.347244+00:00
-- url     : https://prove2.me/submissions/786b140c-fc97-42c2-842f-d06ac8d1e908

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_hasSum_ev
import Theorems.Thm_GlobalTheory_Conv_sumsAt_ev
import Theorems.Thm_GlobalTheory_Conv_differentiableOn_lsum_eTwoPi
import Theorems.Thm_GlobalTheory_Conv_iUnion_halfRing
import Theorems.Thm_GlobalTheory_Conv_exists_ev_ne_zero
import Theorems.Thm_GlobalTheory_Conv_eq_zero_of_ev_eq_zero
import Theorems.Thm_GlobalTheory_Conv_exists_le_halfRing
import Theorems.Thm_GlobalTheory_Conv_locRing_toSubring
import Theorems.Thm_GlobalTheory_Conv_evLoc_algebraMap
import Theorems.Thm_GlobalTheory_Conv_evLoc_unique
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.expandConv_u


attribute [local simp] GlobalTheory.Conv.evLoc_algebraMap

set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
open GlobalTheory GlobalTheory.Conv
namespace GlobalTheory.Conv
theorem _root_.solution :
    (∀ (T : ℝ) (s : ℂ⸨X⸩), s ∈ halfRing T ↔
      ∀ w : ℂ, T < w.im → Summable fun n : ℤ => s.coeff n * eTwoPi w ^ n) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (s : halfRing T),
      HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * eTwoPi w ^ n) (ev T w hw s)) ∧
    (∀ (T : ℝ) (s : halfRing T), ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {w : ℂ | T < w.im} ∧
      ∀ w (hw : T < w.im), F w = ev T w hw s) ∧
    (∀ (T T' : ℝ) (s : halfRing T),
      (∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s = 0) → s = 0) ∧
    (∀ (T : ℝ) (s : halfRing T), s ≠ 0 →
      ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s ≠ 0) ∧
    Monotone halfRing ∧
    (⋃ T, (halfRing T : Set ℂ⸨X⸩) = convLaurent) ∧
    (∀ A : Subalgebra ℂ ℂ⸨X⸩, A.FG → A ≤ convLaurent.toSubalgebra → ∃ T, A ≤ halfRing T) ∧
    (∀ (T : ℝ) (s : halfRing T), (locRing T s).toSubring =
      Subring.closure ((halfRing T : Set ℂ⸨X⸩) ∪ {(s : ℂ⸨X⸩)⁻¹})) ∧
    (∀ (T : ℝ) (s : halfRing T), s ≠ 0 → IsLocalization.Away s (locRing T s)) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (s : halfRing T), ev T w hw s ≠ 0 →
      ∃! φ : locRing T s →ₐ[ℂ] ℂ, ∀ f, φ (algebraMap _ _ f) = ev T w hw f) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (p : ℂ⟦X⟧) (hp : (p : ℂ⸨X⸩) ∈ halfRing T),
      SumsAt p w (ev T w hw ⟨p, hp⟩)) :=
  ⟨fun _ _ => mem_halfRing, fun _ _ hw s => hasSum_ev hw s,
    fun _ s => ⟨fun w => lsum s (eTwoPi w), differentiableOn_lsum_eTwoPi s.2, fun _ _ => rfl⟩,
    fun _ T' _ h => eq_zero_of_ev_eq_zero T' h, fun _ _ h0 => exists_ev_ne_zero h0, halfRing_mono,
    iUnion_halfRing, fun _ hA h => exists_le_halfRing hA h, fun _ s => locRing_toSubring s,
    fun _ _ h0 => isLocalization_locRing h0,
    fun _ _ hw s hs => ⟨evLoc _ _ hw s hs, fun f => evLoc_algebraMap hw hs f,
      fun φ hφ => AlgHom.ext fun x => evLoc_unique hw hs (φ : _ →+* ℂ) hφ x⟩,
    fun _ _ hw _ hp => sumsAt_ev hw hp⟩
end GlobalTheory.Conv
