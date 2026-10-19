-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.Phi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/1a87e196-4b23-4f33-89a4-cddfb1f06bcf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_sub_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : 0 ≤ Phi a b := by
  have hlast :
      0 ≤ MetricCodes.sphericalEntropy (a (Fin.last r)) := by
    simpa using
      (MetricCodes.Spherical.sphericalEntropy_sub_nonneg
        (a := a (Fin.last r)) (b := 0) (by norm_num) h.1)
  have hrows :
      0 ≤ ∑ i : Fin r,
        (MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i)) := by
    apply Finset.sum_nonneg
    intro i _
    exact MetricCodes.Spherical.sphericalEntropy_sub_nonneg
      (h.stabilizer_pos i).le (h.2 i).1.le
  unfold Phi
  rw [Fin.sum_univ_castSucc]
  calc
    0 ≤ (∑ i : Fin r,
        (MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i))) +
        MetricCodes.sphericalEntropy (a (Fin.last r)) :=
      add_nonneg hrows hlast
    _ = (∑ i : Fin r,
          MetricCodes.sphericalEntropy (a i.castSucc)) +
        MetricCodes.sphericalEntropy (a (Fin.last r)) -
          ∑ i : Fin r, MetricCodes.sphericalEntropy (b i) := by
      rw [Finset.sum_sub_distrib]
      ring
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
