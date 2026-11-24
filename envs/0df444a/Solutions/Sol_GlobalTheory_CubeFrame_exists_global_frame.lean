-- Prove2me | solution 1 for GlobalTheory.CubeFrame.exists_global_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:54:39.596308+00:00
-- url     : https://prove2.me/submissions/e99aea45-c025-4264-ba60-36e2da3a08f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal
import Theorems.Thm_GlobalTheory_CubeFrame_exists_global_frame_of_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}
namespace GlobalTheory.CubeFrame
theorem _root_.solution :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → (∃ (r : ℝ) (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) ∧ ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  rintro g ι W c hW hcov hcd hc0 hcc T hT hT0 hTc ⟨r, fr, κ, hr, ⟨hfd, hf0, hfc⟩, hev⟩
  obtain ⟨fr', h1, h2, h3, -, h5⟩ :=
    exists_global_frame_of_local hW hcov hcd hc0 hcc hT hT0 hTc hr hfd hf0 hfc hev
  exact ⟨fr', κ, ⟨fun i => (h1 i).mono Set.inter_subset_left, fun i z hi _ => h2 i z hi,
    fun i j z hi hj _ => h3 i j z hi hj⟩, h5⟩
end GlobalTheory.CubeFrame
