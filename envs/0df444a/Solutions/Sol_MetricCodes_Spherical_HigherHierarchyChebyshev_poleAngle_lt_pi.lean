-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.poleAngle_lt_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/3cb4201d-59e1-41a7-bb75-6c8365052f1e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zeroAngle_le_pi
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_poleAngle_lt_succ_zeroAngle

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    poleAngle N i < Real.pi :=
  (poleAngle_lt_succ_zeroAngle hN).trans_le
    (zeroAngle_le_pi hN (Nat.succ_le_of_lt hi))
end MetricCodes.Spherical.HigherHierarchyChebyshev
