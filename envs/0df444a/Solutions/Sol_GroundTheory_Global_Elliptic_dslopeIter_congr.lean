-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.dslopeIter_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:33.956831+00:00
-- url     : https://prove2.me/submissions/dc7780a6-b644-4239-b0de-56ec1c587d27

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_dslopeIter_succ__14849de0e418

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {p : ℂ} {g₁ g₂ : ℂ → ℂ} (h : g₁ =ᶠ[𝓝 p] g₂) (k : ℕ) :
    dslopeIter p k g₁ =ᶠ[𝓝 p] dslopeIter p k g₂ := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [dslopeIter_succ', dslopeIter_succ']
    have hp : dslopeIter p k g₁ p = dslopeIter p k g₂ p := ih.eq_of_nhds
    filter_upwards [ih] with z hz
    show dslope (dslopeIter p k g₁) p z = dslope (dslopeIter p k g₂) p z
    rcases eq_or_ne z p with rfl | hzp
    · rw [dslope_same, dslope_same, ih.deriv_eq]
    · rw [dslope_of_ne _ hzp, dslope_of_ne _ hzp, slope_def_field, slope_def_field, hz, hp]
end GroundTheory.Global.Elliptic
