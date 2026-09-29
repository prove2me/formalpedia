-- Prove2me | solution 1 for HorizontalPadicL.elliptic_curve_nonvanishing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T15:37:34.185527+00:00
-- url     : https://prove2.me/submissions/8fa653e6-0809-4722-836c-1a2dbbfecc6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HorizontalPadicL_corollary_5_17_v2
import Theorems.Thm_HorizontalPadicL_ellipticCurve_eigenform_specialization_v2

set_option autoImplicit false

open HorizontalPadicL

theorem solution
    (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (d : ℕ)
    (hmod : IsModular E) (hcase1 : d % 4 = 2 ∧ 6 ≤ d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (nonvanishingCount ι E hmod d) α := by
  obtain ⟨f, hnew, hcount⟩ := ellipticCurve_eigenform_specialization_v2 ι E hmod
  obtain ⟨α, hα, hbound⟩ := corollary_5_17_v2
    (modularConductor_pos E hmod) (by norm_num) (by norm_num) ι f hnew d hcase1
  refine ⟨α, hα, ?_⟩
  rw [← funext (hcount d)]
  exact hbound
