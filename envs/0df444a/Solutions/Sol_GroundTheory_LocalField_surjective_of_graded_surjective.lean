-- Prove2me | solution 1 for GroundTheory.LocalField.surjective_of_graded_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:10:03.404972+00:00
-- url     : https://prove2.me/submissions/3c005f8a-29e3-4e40-9634-ab34aa7fc649

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Theorems.Thm_GroundTheory_LocalField_map_eq_of_graded_surjective

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
variable {G H : Type*} [Group G] [Group H]
namespace GroundTheory.LocalField
theorem _root_.solution {F : ℕ → Subgroup G} {E : ℕ → Subgroup H}
    (hF : Antitone F) (hE : Antitone E) (hG : FiltrationComplete F)
    (hH : FiltrationSeparated E) (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hF0 : F 0 = ⊤) (hE0 : E (φ 0) = ⊤) (hmap : ∀ n, ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    Function.Surjective f := by
  intro h
  have e := map_eq_of_graded_surjective hF hE hG hH f hφ 0 (fun n _ => hmap n)
    (fun n _ => hgr n)
  have hh : h ∈ E (φ 0) := by rw [hE0]; exact Subgroup.mem_top h
  rw [← e, hF0] at hh
  obtain ⟨g, -, rfl⟩ := hh
  exact ⟨g, rfl⟩
end GroundTheory.LocalField
