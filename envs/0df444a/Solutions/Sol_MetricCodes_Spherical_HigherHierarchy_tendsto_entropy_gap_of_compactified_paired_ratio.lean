-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_entropy_gap_of_compactified_paired_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/6b97db70-8232-4397-9efc-e7a5e53d738d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_of_compactifiedHierarchyCoordinate_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_sphericalEntropy_sub_of_sequence_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_paired_stabilizer_tendsto_atTop_of_ambient
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_paired_infinity_iff
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_paired_ratio_limit_pos_of_ambient_tendsto_atTop

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
    (hd : ∀ i, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i)))
    (i : Fin r) :
    Tendsto
      (fun n =>
        MetricCodes.sphericalEntropy (a (φ n) i.castSucc) -
          MetricCodes.sphericalEntropy (b (φ n) i))
      atTop
      (nhds
        (if A i.castSucc = 0 then -Real.logb 2 (d i)
         else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
           MetricCodes.sphericalEntropy ((B i)⁻¹ - 1))) := by
  by_cases hzero : A i.castSucc = 0
  · simp only [hzero, ↓reduceIte]
    have ha : Tendsto (fun n => a (φ n) i.castSucc) atTop atTop :=
      tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
        (fun n => (h (φ n)).ambient_nonneg i.castSucc)
        (hzero ▸ hA i.castSucc)
    have hb : Tendsto (fun n => b (φ n) i) atTop atTop :=
      paired_stabilizer_tendsto_atTop_of_ambient h hPhi i ha
    have hpositive : 0 < d i :=
      paired_ratio_limit_pos_of_ambient_tendsto_atTop
        h hPhi i ha (hd i)
    exact tendsto_sphericalEntropy_sub_of_sequence_ratio
      hpositive ha hb (hd i)
  · simp only [hzero, ↓reduceIte]
    have hApos : 0 < A i.castSucc :=
      lt_of_le_of_ne (hAnonneg i.castSucc) (Ne.symm hzero)
    have hBzero : B i ≠ 0 := by
      intro hz
      have hpaired := paired_infinity_iff h hPhi hA hB
        hAnonneg hBnonneg i
      exact hzero (hpaired.mpr hz)
    have hBpos : 0 < B i :=
      lt_of_le_of_ne (hBnonneg i) (Ne.symm hBzero)
    have ha : Tendsto (fun n => a (φ n) i.castSucc)
        atTop (nhds ((A i.castSucc)⁻¹ - 1)) :=
      tendsto_of_compactifiedHierarchyCoordinate_pos hApos (hA i.castSucc)
    have hb : Tendsto (fun n => b (φ n) i)
        atTop (nhds ((B i)⁻¹ - 1)) :=
      tendsto_of_compactifiedHierarchyCoordinate_pos hBpos (hB i)
    exact
      (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.tendsto.comp ha).sub
        (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.tendsto.comp hb)
end MetricCodes.Spherical.HigherHierarchy
