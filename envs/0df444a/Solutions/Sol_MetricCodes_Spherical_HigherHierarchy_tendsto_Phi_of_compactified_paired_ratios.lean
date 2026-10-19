-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_Phi_of_compactified_paired_ratios
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/92f4fb20-b998-427e-a2b6-08e5b690be1e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_eq_sum_entropy_gaps
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_of_compactifiedHierarchyCoordinate_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_entropy_gap_of_compactified_paired_ratio

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B d : Fin r → ℝ}
    {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (hA : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)))
    (hAnonneg : ∀ i, 0 ≤ A i)
    (hBnonneg : ∀ i, 0 ≤ B i)
    (hlast : 0 < A (Fin.last r))
    (hd : ∀ i, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i))) :
    Tendsto (fun n => Phi (a (φ n)) (b (φ n))) atTop
      (nhds
        ((∑ i : Fin r,
            if A i.castSucc = 0 then -Real.logb 2 (d i)
            else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
              MetricCodes.sphericalEntropy ((B i)⁻¹ - 1)) +
          MetricCodes.sphericalEntropy ((A (Fin.last r))⁻¹ - 1))) := by
  have hgaps := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_entropy_gap_of_compactified_paired_ratio
      h hPhi hA hB hAnonneg hBnonneg hd i
  have hterminal : Tendsto (fun n => a (φ n) (Fin.last r))
      atTop (nhds ((A (Fin.last r))⁻¹ - 1)) :=
    tendsto_of_compactifiedHierarchyCoordinate_pos hlast
      (hA (Fin.last r))
  have hentropy :=
    MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.tendsto.comp
      hterminal
  have htotal := hgaps.add hentropy
  apply htotal.congr'
  exact Filter.Eventually.of_forall fun n =>
    (Phi_eq_sum_entropy_gaps (a (φ n)) (b (φ n))).symm
end MetricCodes.Spherical.HigherHierarchy
