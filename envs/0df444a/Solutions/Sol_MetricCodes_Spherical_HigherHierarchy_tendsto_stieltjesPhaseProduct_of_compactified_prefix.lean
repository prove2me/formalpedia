-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_stieltjesPhaseProduct_of_compactified_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/fd1fc61a-ca1b-4965-905b-035c193f90c6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_of_compactifiedHierarchyCoordinate_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyCoordinate_recovered_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_stieltjesPhaseProduct_of_escaping_prefix_strict_residual

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
    {k r q : ℕ}
    (a : ℕ → Fin (k + r + 1) → ℝ)
    (b : ℕ → Fin (k + r) → ℝ)
    (A : Fin (k + r + 1) → ℝ)
    (B d : Fin (k + r) → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
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
    (hzero : ∀ i : Fin k, A (i.castAdd (r + 1)) = 0)
    (hpositiveA : ∀ i : Fin (r + 1), 0 < A (i.natAdd k))
    (hpositiveB : ∀ i : Fin r, 0 < B (i.natAdd k))
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i : Fin (r + 1) => (A (i.natAdd k))⁻¹ - 1)
          (fun i : Fin r => (B (i.natAdd k))⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
      atTop
      (𝓝 ((∏ i : Fin k, d (i.castAdd r) ^ 2) *
        stieltjesPhaseProduct A' B' t)) := by
  apply tendsto_stieltjesPhaseProduct_of_escaping_prefix_strict_residual
    a b
    (fun i : Fin (r + 1) => (A (i.natAdd k))⁻¹ - 1)
    (fun i : Fin r => (B (i.natAdd k))⁻¹ - 1)
    A' B' (fun i : Fin k => d (i.castAdd r))
    (t := t)
  · intro i
    apply tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
      (fun n => (h n).ambient_nonneg (i.castAdd (r + 1)))
    simpa [hzero i] using ha (i.castAdd (r + 1))
  · intro i
    have hindex : (i.castAdd r).castSucc = i.castAdd (r + 1) := by
      apply Fin.ext
      simp
    simpa [hindex] using hd (i.castAdd r)
  · intro i
    exact tendsto_of_compactifiedHierarchyCoordinate_pos
      (hpositiveA i) (ha (i.natAdd k))
  · intro i
    exact tendsto_of_compactifiedHierarchyCoordinate_pos
      (hpositiveB i) (hb (i.natAdd k))
  · intro i
    exact compactifiedHierarchyCoordinate_recovered_nonneg
      (hpositiveA i) (hA (i.natAdd k)).2
  · exact hratio
  · exact ht
end MetricCodes.Spherical.HigherHierarchy
