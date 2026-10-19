-- Prove2me | solution 1 for LinearProgrammingBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/d31fc989-543d-4623-ad87-b6f38171e796

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_periodic_packing_supremum_eq_unit_separation
import Theorems.Thm_PeriodicSpherePacking_packing_density_zero_of_empty_centers
import Theorems.Thm_periodic_packing_supremum_eq_unrestricted
import Theorems.Thm_P2M_LinearProgrammingBound__5ed74557e9ce

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂
theorem _root_.solution (hd : 0 < d) : SpherePackingConstant d ≤
  (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
  := by
  rw [← periodic_packing_supremum_eq_unrestricted hd,
    periodic_packing_supremum_eq_unit_separation (d := d)]
  refine iSup_le fun P => ?_
  refine iSup_le fun hP => ?_
  cases isEmpty_or_nonempty ↑P.centers with
  | inl instEmpty =>
      simp [P.packing_density_zero_of_empty_centers hd]
  | inr instNonempty =>
      let b : Basis (Fin d) ℤ ↥P.lattice :=
        ((ZLattice.module_free ℝ P.lattice).chooseBasis).reindex
          (PeriodicSpherePacking.coordinateIndexEquiv P)
      exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
        (ZSpan.fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ P.lattice b))
        (PeriodicSpherePacking.basis_region_translates_cover_uniquely (S := P) b) hd
