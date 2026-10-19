-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_const_mul_rectangularWeylQuotient_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/694a68d6-f3be-4ed8-b475-ca02203d49ea

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_flooredWeight_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_vertexDimension_pos_all
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_log_dimensionSum_div_log_two
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_interlacing_strictAnti_stabilizer
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_log_stabilizerDimension_floor_current_div_log_two
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_const_mul_lt_rpow_of_logRate

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherProjectionInstantiation
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r m : ℕ} {R K : ℝ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (h : Interlacing a b) (hlast : 0 < a (Fin.last (r + 1)))
    (hR : Phi a b < R) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      K *
          (RectangularVertices.dimensionSum (m := m) a n /
            Weyl.dimension (n - 1)
              (Weyl.flooredWeight b n)) <
        (2 : ℝ) ^ (R * (n : ℝ)) := by
  have ha : ∀ i, 0 < a i := fun i =>
    hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
  have hb : ∀ i, 0 < b i := h.stabilizer_pos
  have hanti : StrictAnti a := h.strictAnti_ambient
  have hbanti : StrictAnti b := interlacing_strictAnti_stabilizer h
  have hpositive :
      ∀ᶠ n : ℕ in atTop,
        0 <
          RectangularVertices.dimensionSum (m := m) a n /
            Weyl.dimension (n - 1)
              (Weyl.flooredWeight b n) := by
    filter_upwards [RectangularVertices.eventually_vertexDimension_pos_all
      (m := m) a ha hanti, eventually_ge_atTop (2 * r + 5)]
      with n hn hstable
    apply div_pos
    · unfold RectangularVertices.dimensionSum
      apply Finset.sum_pos
      · intro i _
        exact hn i
      · exact Finset.univ_nonempty
    · apply Weyl.dimension_pos (by omega)
      exact Weyl.flooredWeight_antitone hbanti.antitone n
  have hlimit :
      Tendsto
        (fun n : ℕ =>
          (Real.log
            (RectangularVertices.dimensionSum (m := m) a n /
              Weyl.dimension (n - 1)
                (Weyl.flooredWeight b n)) /
            (n : ℝ)) / Real.log 2)
        atTop (nhds (Phi a b)) := by
    have hambient := RectangularVertices.tendsto_log_dimensionSum_div_log_two
      (m := m) a ha hanti
    have hstabilizer :=
      tendsto_log_stabilizerDimension_floor_current_div_log_two b hb hbanti
    have hdifference := hambient.sub hstabilizer
    apply hdifference.congr'
    filter_upwards [RectangularVertices.eventually_vertexDimension_pos_all
      (m := m) a ha hanti, eventually_ge_atTop (2 * r + 5)]
      with n hn hstable
    have hambientpos : 0 < RectangularVertices.dimensionSum (m := m) a n := by
      unfold RectangularVertices.dimensionSum
      exact Finset.sum_pos (fun i _ => hn i) Finset.univ_nonempty
    have hstabilizerpos :
        0 < Weyl.dimension (n - 1) (Weyl.flooredWeight b n) :=
      Weyl.dimension_pos (by omega)
        (Weyl.flooredWeight_antitone hbanti.antitone n)
    rw [Real.log_div hambientpos.ne' hstabilizerpos.ne']
    ring
  exact eventually_const_mul_lt_rpow_of_logRate hpositive hlimit hR hK
end MetricCodes.Spherical.HigherHierarchy
