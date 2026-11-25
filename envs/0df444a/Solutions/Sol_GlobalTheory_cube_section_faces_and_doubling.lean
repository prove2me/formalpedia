-- Prove2me | solution 1 for GlobalTheory.cube_section_faces_and_doubling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:09.779508+00:00
-- url     : https://prove2.me/submissions/02154417-36b1-4dc4-9fbb-be88653cbfff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
import Theorems.Thm_GlobalTheory_CubeFace_isOpen_sums
import Theorems.Thm_GlobalTheory_CubeFace_face
import Theorems.Thm_GlobalTheory_CubeFace_doubling

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (i₀ : ι), 0 ∈ W i₀ → ∀ F : (Fin 3 → Fin g → ℂ) → ℂ, F = T (fun _ => i₀) → (∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) := by
  intro g ι W c hW hcov _ hc0 hcc T hT hT0 hTT Λ _ hΛ hWp _ hTp i₀ h0 F hF
  subst hF
  have hO := CubeFace.isOpen_sums W hW (fun _ => i₀)
  have hn : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W i₀ :=
    hO.mem_nhds fun I => by simpa using h0
  have hn1 : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3), ∑ a ∈ I, (-x) a ∈ W i₀ :=
    (hO.preimage continuous_neg).mem_nhds fun I => by simpa using h0
  have hn2 : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ),
      ∀ I : Finset (Fin 3), ∑ a ∈ I, ((2 : ℂ) • x) a ∈ W i₀ :=
    (hO.preimage (continuous_const_smul (2 : ℂ))).mem_nhds fun I => by simpa using h0
  refine ⟨fun a => ?_, ?_⟩
  · filter_upwards [hn] with x hx hxa
    exact CubeFace.face W c hW hcov hc0 T hT hTT Λ hΛ hWp hTp i₀ h0 a x hx hxa
  · filter_upwards [hn, hn1, hn2] with x hx hx1 hx2
    exact CubeFace.doubling W c hW hcov hc0 hcc T hT hT0 hTT Λ hΛ hWp hTp i₀ h0 x hx hx1 hx2
end GlobalTheory
