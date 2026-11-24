-- Prove2me | solution 1 for GlobalTheory.coeff_eq_zero_of_hasSum_mFourier_orthonormal_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:56.021995+00:00
-- url     : https://prove2.me/submissions/80ea6262-b319-421f-85ad-bec18b7cee80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffEqZeroOfHasSumMFourierOrthonormalImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {J : Type} [Fintype J] {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : C(UnitAddTorus J, ℂ) →L[ℂ] E)
    (hL : Orthonormal ℂ (fun n : J → ℤ => L (UnitAddTorus.mFourier n))) (b : (J → ℤ) → ℂ)
    (h : HasSum (fun s => b s • UnitAddTorus.mFourier s) (0 : C(UnitAddTorus J, ℂ)))
    (t : J → ℤ) : b t = 0 := by
  classical
  have h1 := ((innerSL ℂ (L (UnitAddTorus.mFourier t))).comp L).hasSum h
  have h2 : HasSum (fun s => if s = t then b t else 0) (0 : ℂ) := by
    rw [map_zero] at h1
    refine HasSum.congr_fun h1 fun s => ?_
    have := orthonormal_iff_ite.mp hL t s
    simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, this, smul_eq_mul]
    by_cases hs : s = t
    · simp [hs]
    · simp [hs, Ne.symm hs]
  exact (hasSum_ite_eq t (b t)).unique h2
end GlobalTheory
