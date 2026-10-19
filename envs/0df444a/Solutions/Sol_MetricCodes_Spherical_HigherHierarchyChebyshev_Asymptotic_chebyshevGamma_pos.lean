-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.chebyshevGamma_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/f71083b2-6897-4ee4-9879-c14bbeadfdae

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_pole_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_inverseQuadratic_strictMonoOn
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_ambient_stabilizer_interlacing

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchyChebyshev
open MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
noncomputable section
open Filter
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution {R : ℝ} (hR : 0 < R) (r : ℕ) :
    0 < MetricCodes.Spherical.HigherHierarchy.Gamma
      (ambient R r) (stabilizer R r) := by
  classical
  have htuple := ambient_stabilizer_interlacing hR r
  have hpole : 0 < pole R (r + 1) 0 :=
    pole_pos hR (Nat.zero_lt_succ r) (by omega)
  have hzero : inverseQuadratic 0 = 0 := by
    norm_num [inverseQuadratic]
  have hambient : 0 < ambient R r 0 := by
    change 0 < inverseQuadratic (pole R (r + 1) 0)
    rw [← hzero]
    exact inverseQuadratic_strictMonoOn (by norm_num) hpole.le hpole
  have hatom :
      0 < MetricCodes.Spherical.HigherHierarchy.spectralAtom
        (ambient R r 0) := by
    unfold MetricCodes.Spherical.HigherHierarchy.spectralAtom
      MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
    positivity
  unfold MetricCodes.Spherical.HigherHierarchy.Gamma
  calc
    0 < MetricCodes.Spherical.HigherHierarchy.lagrangeWeight
          (ambient R r) (stabilizer R r) 0 *
        MetricCodes.Spherical.HigherHierarchy.spectralAtom
          (ambient R r 0) :=
      mul_pos (htuple.lagrangeWeight_pos 0) hatom
    _ ≤ ∑ i : Fin (r + 1),
        MetricCodes.Spherical.HigherHierarchy.lagrangeWeight
          (ambient R r) (stabilizer R r) i *
        MetricCodes.Spherical.HigherHierarchy.spectralAtom
          (ambient R r i) := by
      exact Finset.single_le_sum
        (fun i _ =>
          mul_nonneg (htuple.lagrangeWeight_nonneg i)
            (MetricCodes.Spherical.HigherHierarchy.spectralAtom_nonneg
              (htuple.ambient_nonneg i)))
        (Finset.mem_univ 0)
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
