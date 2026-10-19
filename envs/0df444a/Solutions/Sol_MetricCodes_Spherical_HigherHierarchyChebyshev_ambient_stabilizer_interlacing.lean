-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.ambient_stabilizer_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/14d9538c-0815-42f8-bdd0-2fe6ee108174

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_strict_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_pole_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zero_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_inverseQuadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_inverseQuadratic_strictMonoOn

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R) (r : ℕ) :
    MetricCodes.Spherical.HigherHierarchy.Interlacing
      (ambient R r) (stabilizer R r) := by
  have hN : 0 < r + 1 := Nat.zero_lt_succ r
  constructor
  · exact inverseQuadratic_nonneg
      (pole_pos hR hN (Fin.last r).isLt).le
  · intro i
    have hi : i.val < r + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self r)
    have hinext : i.val + 1 < r + 1 := by omega
    have hleft := (strict_interlacing hR hN hi).1
    have hright := (strict_interlacing hR hN hinext).2
    constructor
    · exact inverseQuadratic_strictMonoOn
        (zero_nonneg hR.le (r + 1) (i.val + 1))
        (pole_pos hR hN hi).le hleft
    · exact inverseQuadratic_strictMonoOn
        (pole_pos hR hN hinext).le
        (zero_nonneg hR.le (r + 1) (i.val + 1)) hright
end MetricCodes.Spherical.HigherHierarchyChebyshev
