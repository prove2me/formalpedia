-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.prod_le_prod_range_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:36.119856+00:00
-- url     : https://prove2.me/submissions/641fb158-a7c5-4447-a716-84b1ff907da7

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
theorem _root_.solution (A : Finset ℕ) (F : ℕ → ℝ) (φ : ℕ → ℕ) (w : ℕ → ℝ) (k : ℕ)
    (hF0 : ∀ s ∈ A, 0 ≤ F s) (hF : ∀ s ∈ A, F s ≤ w (φ s)) (hinj : Set.InjOn φ A)
    (hmap : ∀ s ∈ A, φ s < k) (hw : ∀ j, 1 ≤ w j) :
    ∏ s ∈ A, F s ≤ ∏ j ∈ range k, w j := by
  classical
  calc ∏ s ∈ A, F s ≤ ∏ s ∈ A, w (φ s) := prod_le_prod hF0 hF
    _ = ∏ j ∈ A.image φ, w j := (prod_image hinj).symm
    _ ≤ ∏ j ∈ range k, w j := by
      apply prod_le_prod_of_subset_of_one_le
      · intro j hj
        obtain ⟨s, hs, rfl⟩ := mem_image.mp hj
        exact mem_range.mpr (hmap s hs)
      · intro j _
        exact le_trans zero_le_one (hw j)
      · intro j _ _
        exact hw j
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
