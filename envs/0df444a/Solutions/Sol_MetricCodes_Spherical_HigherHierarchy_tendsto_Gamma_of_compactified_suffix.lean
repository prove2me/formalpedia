-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_Gamma_of_compactified_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/bb8b72b1-945f-48f7-af9f-5d189c27e71b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_Gamma_of_stieltjesPhaseProduct
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_stieltjesPhaseProduct_of_compactified_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedEscapingRatioProduct_eq_filtered_prefix

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
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {R k j q : ℕ} (hkj : k + j = R)
    (a : ℕ → Fin (R + 1) → ℝ)
    (b : ℕ → Fin R → ℝ)
    (A : Fin (R + 1) → ℝ)
    (B d : Fin R → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (c : ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hAB : Interlacing A' B')
    (hA : ∀ i, A i ∈ Set.Icc (0 : ℝ) 1)
    (ha : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (a n i))
        atTop (𝓝 (A i)))
    (hb : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (b n i))
        atTop (𝓝 (B i)))
    (hd : ∀ i,
      Tendsto (fun n => b n i / a n i.castSucc)
        atTop (𝓝 (d i)))
    (hzero : ∀ i : Fin R, i.val < k → A i.castSucc = 0)
    (hpositiveA : ∀ i,
      0 < compactifiedAmbientSuffix hkj A i)
    (hpositiveB : ∀ i,
      0 < compactifiedStabilizerSuffix hkj B i)
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t)
    (hc : c = ∏ i ∈ Finset.univ.filter
      (fun i : Fin R => i.val < k), d i) :
    Tendsto (fun n => Gamma (a n) (b n))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A' B')) := by
  have hproduct : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
        atTop (𝓝 (c ^ 2 * stieltjesPhaseProduct A' B' t)) := by
    intro t ht
    have hlimit := tendsto_stieltjesPhaseProduct_of_compactified_suffix
      hkj a b A B d A' B' h hA ha hb hd hzero
      hpositiveA hpositiveB hratio ht
    rw [compactifiedEscapingRatioProduct_eq_filtered_prefix hkj d,
      ← hc] at hlimit
    exact hlimit
  exact tendsto_Gamma_of_stieltjesPhaseProduct
    a b A' B' h hAB (c ^ 2) hproduct
end MetricCodes.Spherical.HigherHierarchy
