-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.Packing.Sep.card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:39.836681+00:00
-- url     : https://prove2.me/submissions/552a25e7-0741-437f-8f8e-5dc0e77d98b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound
import Theorems.Thm_GlobalTheory_finset_card_le_of_separated
import Theorems.Thm_GlobalTheory_one_add_two_mul_div_pow_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.Packing
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]
namespace GlobalTheory.CompanionTheory.Adelic.Packing
namespace Sep
theorem _root_.solution {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s : Finset Λ}
    (hs : Sep e r R s) : (s.card : ℝ) ≤ (3 * R / r) ^ Module.finrank ℝ V := by
  classical
  have hinj : Set.InjOn e (s : Set Λ) := by
    intro a ha b hb hab
    by_contra hne
    have : r ≤ ‖e a - e b‖ := hs.2 ha hb hne
    rw [hab, sub_self, norm_zero] at this
    linarith
  have hcard : (s.image e).card = s.card := Finset.card_image_of_injOn hinj
  have h1 := GlobalTheory.finset_card_le_of_separated (s.image e) hr (hr.le.trans hrR) (0 : V)
    (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
      simpa using hs.1 l hl)
    (by
      intro a ha b hb hab
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      have hlm : l ≠ m := fun h => hab (by rw [h])
      rw [dist_eq_norm]
      exact hs.2 hl hm hlm)
  rw [hcard] at h1
  exact h1.trans (GlobalTheory.one_add_two_mul_div_pow_le hr hrR _)
end Sep
end GlobalTheory.CompanionTheory.Adelic.Packing
