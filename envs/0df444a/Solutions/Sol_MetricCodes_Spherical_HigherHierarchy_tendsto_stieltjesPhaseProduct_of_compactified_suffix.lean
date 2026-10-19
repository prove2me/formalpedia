-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_stieltjesPhaseProduct_of_compactified_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/9dd79471-7e0e-4e46-896c-13508e98c64e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_stieltjesPhaseProduct_of_compactified_prefix

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
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
      atTop
      (𝓝 ((compactifiedEscapingRatioProduct hkj d) ^ 2 *
        stieltjesPhaseProduct A' B' t)) := by
  subst R
  have hzero' : ∀ i : Fin k, A (i.castAdd (j + 1)) = 0 := by
    intro i
    have hz := hzero (i.castAdd j) i.isLt
    have hindex : (i.castAdd j).castSucc = i.castAdd (j + 1) := by
      apply Fin.ext
      simp
    simpa [hindex] using hz
  have hindexA (i : Fin (j + 1)) :
      compactifiedAmbientSuffix (rfl : k + j = k + j) A i =
        A (i.natAdd k) := by
    unfold compactifiedAmbientSuffix
    congr 1
  have hindexB (i : Fin j) :
      compactifiedStabilizerSuffix (rfl : k + j = k + j) B i =
        B (i.natAdd k) := by
    unfold compactifiedStabilizerSuffix
    congr 1
  have hpositiveA' : ∀ i : Fin (j + 1), 0 < A (i.natAdd k) := by
    intro i
    simpa only [hindexA] using hpositiveA i
  have hpositiveB' : ∀ i : Fin j, 0 < B (i.natAdd k) := by
    intro i
    simpa only [hindexB] using hpositiveB i
  have hratio' : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i : Fin (j + 1) => (A (i.natAdd k))⁻¹ - 1)
          (fun i : Fin j => (B (i.natAdd k))⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t := by
    intro t ht
    simpa only [hindexA, hindexB] using hratio t ht
  have hlimit := tendsto_stieltjesPhaseProduct_of_compactified_prefix
    a b A B d A' B' h hA ha hb hd hzero' hpositiveA' hpositiveB'
    hratio' ht
  have hproduct :
      compactifiedEscapingRatioProduct (rfl : k + j = k + j) d =
        ∏ i : Fin k, d (i.castAdd j) := by
    unfold compactifiedEscapingRatioProduct
    apply Finset.prod_congr rfl
    intro i _
    congr 1
  rw [hproduct, ← Finset.prod_pow]
  exact hlimit
end MetricCodes.Spherical.HigherHierarchy
