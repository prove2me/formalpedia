-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.zero_nodes_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/b9046770-42ba-40cb-b6cc-180c21f211f9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_zero_strictAnti

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
    Function.Injective (fun i : Fin r => zero R (r + 1) (i.val + 1)) := by
  have hanti : StrictAnti (fun i : Fin r => zero R (r + 1) (i.val + 1)) := by
    intro i j hij
    apply zero_strictAnti hR (Nat.zero_lt_succ r)
    · omega
    · have hval := Fin.mk_lt_mk.mp hij
      omega
  exact hanti.injective
end MetricCodes.Spherical.HigherHierarchyChebyshev
