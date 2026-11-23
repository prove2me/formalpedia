-- Prove2me | solution 1 for GlobalTheory.PlaceModel.wave_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:20.352511+00:00
-- url     : https://prove2.me/submissions/58e9f866-3118-4338-8d1b-3eda23b87aa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Theorems.Thm_GlobalTheory_PlaceModel_ind_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution (h : IsBichar χ) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (x y : G) {l l' : G} (hl : l ∈ L)
    (hl' : l' ∈ L') : wave χ L (x + l) (y + l') = χ l y • wave χ L x y := by
  funext t
  simp only [wave, Pi.smul_apply, smul_eq_mul]
  rw [← add_assoc, ind_add L (t + x) hl]
  by_cases ht : t + x ∈ L
  · rw [h.left (t + x) l (y + l'), h.right (t + x) y l', h.right l y l', hLL' _ ht l' hl',
      hLL' l hl l' hl']
    ring
  · simp [ind, ht]
end GlobalTheory.PlaceModel
