-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.monomialChar_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:26.46746+00:00
-- url     : https://prove2.me/submissions/e9459a3a-ecac-478e-8f44-5619719c2786

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution : Function.Injective (monomialChar : (Fin n → ℤ) → _) := by
  intro l l' h
  funext i
  have h2 := DFunLike.congr_fun h (Pi.mulSingle i (Units.mk0 (2 : ℂ) two_ne_zero))
  simp only [monomialChar_apply] at h2
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp)] at h2
  simp only [Pi.mulSingle_eq_same, Units.val_zpow_eq_zpow_val, Units.val_mk0] at h2
  have hn : ‖(2 : ℂ) ^ l i‖ = ‖(2 : ℂ) ^ l' i‖ := by rw [h2]
  rw [norm_zpow, norm_zpow, Complex.norm_two] at hn
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) hn
end GroundTheory.Automorphic.Spherical
