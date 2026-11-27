-- Prove2me | solution 1 for GroundTheory.LocalField.map_eq_of_graded_surjective_of_hasBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:49:28.986133+00:00
-- url     : https://prove2.me/submissions/e32f2951-a722-4825-aa83-5a18e4528a07

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Theorems.Thm_GroundTheory_LocalField_map_eq_of_graded_surjective
import Theorems.Thm_GroundTheory_LocalField_filtrationComplete_of_hasBasis
import Theorems.Thm_GroundTheory_LocalField_filtrationSeparated_of_hasBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Filter Topology Uniformity
namespace GroundTheory.LocalField
theorem _root_.solution {G H : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [CompleteSpace G] [Group H] [TopologicalSpace H] [T1Space H]
    {F : ℕ → Subgroup G} {E : ℕ → Subgroup H} (hF : Antitone F) (hE : Antitone E)
    (hFb : (𝓝 (1 : G)).HasBasis (fun _ => True) (fun n => (F n : Set G)))
    (hEb : (𝓝 (1 : H)).HasBasis (fun _ => True) (fun n => (E n : Set H)))
    (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (k : ℕ) (hmap : ∀ n, k ≤ n → ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, k ≤ n → ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    (F k).map f = E (φ k) :=
  map_eq_of_graded_surjective hF hE (filtrationComplete_of_hasBasis hFb)
    (filtrationSeparated_of_hasBasis hEb) f hφ k hmap hgr
end GroundTheory.LocalField
