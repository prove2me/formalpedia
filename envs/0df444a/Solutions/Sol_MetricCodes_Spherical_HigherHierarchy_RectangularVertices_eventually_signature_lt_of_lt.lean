-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_signature_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/cfdef564-7a26-48a6-9e23-4bae6f3641ca

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_signature_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (v : ℕ → Vertex r m)
    (i j : Fin (r + 1)) (hi : 0 ≤ a i) (hj : 0 ≤ a j)
    (hij : a i < a j) :
    ∀ᶠ n : ℕ in atTop, signature a n (v n) i < signature a n (v n) j := by
  have hratio :=
    ((tendsto_signature_ratio a v j hj).sub
      (tendsto_signature_ratio a v i hi)).eventually
        (Ioi_mem_nhds (sub_pos.mpr hij))
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hcast :
      (signature a n (v n) i : ℝ) < signature a n (v n) j := by
    apply (div_lt_div_iff_of_pos_right hnreal).mp
    linarith
  exact_mod_cast hcast
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
