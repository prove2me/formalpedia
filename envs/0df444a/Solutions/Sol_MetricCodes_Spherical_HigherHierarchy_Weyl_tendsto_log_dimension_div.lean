-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_dimension_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/e12c2381-da3d-44b6-a316-da3a2a2628f2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_rowFactor_div
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_pairFactor_div

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
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl
namespace MetricCodes.Spherical.HigherHierarchy.Weyl
theorem _root_.solution
    {r : ℕ} (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i)
    (hanti : StrictAnti a)
    (hdominant : ∀ n, Antitone (lam n))
    (hTop : ∀ i, Tendsto (fun n : ℕ => lam n i) atTop atTop)
    (hlim : ∀ i,
      Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
        atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ => Real.log (dimension n (lam n)) / (n : ℝ))
      atTop
      (𝓝 (∑ i : Fin (r + 1),
        ((1 + a i) * Real.log (1 + a i) - a i * Real.log (a i)))) := by
  have hrows :
      Tendsto
        (fun n : ℕ =>
          ∑ i : Fin (r + 1), Real.log (rowFactor n (lam n) i) / (n : ℝ))
        atTop
        (𝓝 (∑ i : Fin (r + 1),
          ((1 + a i) * Real.log (1 + a i) - a i * Real.log (a i)))) := by
    exact tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_log_rowFactor_div i lam (ha i) (hTop i) (hlim i)
  have hpair (i j : Fin (r + 1)) :
      Tendsto
        (fun n : ℕ =>
          if i < j then Real.log (pairFactor n (lam n) i j) / (n : ℝ)
            else 0)
        atTop (𝓝 0) := by
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      exact tendsto_log_pairFactor_div i j hij lam (ha i) (ha j)
        (hanti hij) (hlim i) (hlim j)
    · simp [hij]
  have hpairs :
      Tendsto
        (fun n : ℕ =>
          ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
            if i < j then Real.log (pairFactor n (lam n) i j) / (n : ℝ)
              else 0)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_finsetSum Finset.univ fun i _ =>
        tendsto_finsetSum Finset.univ fun j _ => hpair i j)
  have hcombined := hrows.add hpairs
  have heq :
      (fun n : ℕ =>
        (∑ i : Fin (r + 1), Real.log (rowFactor n (lam n) i) / (n : ℝ)) +
          ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
            if i < j then Real.log (pairFactor n (lam n) i j) / (n : ℝ)
              else 0) =ᶠ[atTop]
      (fun n : ℕ => Real.log (dimension n (lam n)) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (2 * r + 4)] with n hn
    have hrow (i : Fin (r + 1)) : rowFactor n (lam n) i ≠ 0 :=
      (rowFactor_pos hn (lam n) i).ne'
    have hpair' (i j : Fin (r + 1)) :
        (if i < j then pairFactor n (lam n) i j else 1) ≠ 0 := by
      split_ifs with hij
      · exact (pairFactor_pos hn (hdominant n) hij).ne'
      · exact one_ne_zero
    have hinner (i : Fin (r + 1)) :
        (∏ j, if i < j then pairFactor n (lam n) i j else 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hpair' i j
    have hrowprod : (∏ i, rowFactor n (lam n) i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => hrow i
    have hpairprod :
        (∏ i, ∏ j, if i < j then pairFactor n (lam n) i j else 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => hinner i
    have hloginner (i : Fin (r + 1)) :
        Real.log (∏ j, if i < j then pairFactor n (lam n) i j else 1) =
          ∑ j, if i < j then Real.log (pairFactor n (lam n) i j) else 0 := by
      rw [Real.log_prod fun j _ => hpair' i j]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    unfold dimension
    rw [Real.log_mul hrowprod hpairprod,
      Real.log_prod fun i _ => hrow i,
      Real.log_prod fun i _ => hinner i]
    simp_rw [hloginner]
    rw [add_div]
    simp_rw [Finset.sum_div]
    simp only [ite_div, zero_div]

  simpa using hcombined.congr' heq
end MetricCodes.Spherical.HigherHierarchy.Weyl
