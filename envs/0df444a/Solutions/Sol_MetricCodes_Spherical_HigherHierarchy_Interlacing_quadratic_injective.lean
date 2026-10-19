-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.quadratic_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/d2a93206-7c2b-4daf-b38d-228b01199fa0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    Function.Injective (fun i => quadraticCoordinate (a i)) := by
  intro i j hij
  apply h.strictAnti_ambient.injective
  exact quadraticCoordinate_strictMonoOn.injOn
    (h.ambient_nonneg i) (h.ambient_nonneg j) hij
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
