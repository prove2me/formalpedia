-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_signature_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/a5e436bd-ac86-4cbf-acf2-82a635a5dbfd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_signature_lt_of_lt

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
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) :
    ∀ᶠ n : ℕ in atTop, StrictAnti (signature a n (v n)) := by
  have hall :
      ∀ᶠ n : ℕ in atTop, ∀ i : Fin r,
        signature a n (v n) i.succ <
          signature a n (v n) i.castSucc := by
    apply eventually_all.2
    intro i
    exact eventually_signature_lt_of_lt a v i.succ i.castSucc
      (ha i.succ) (ha i.castSucc)
      (hanti (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
  filter_upwards [hall] with n hn
  exact Fin.strictAnti_iff_succ_lt.mpr hn
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
