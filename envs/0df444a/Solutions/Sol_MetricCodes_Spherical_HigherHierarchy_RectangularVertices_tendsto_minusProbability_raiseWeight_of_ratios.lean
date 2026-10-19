-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_minusProbability_raiseWeight_of_ratios
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/3e9480c4-e1c6-474e-bb48-4cc051bdeef1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_channelFactor_of_ratios
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_raisedMinusLeadingFactor_of_ratio

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
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (lam : ℕ → Fin (r + 1) → ℕ) (mu : ℕ → Fin r → ℕ)
    (hlam : ∀ i, Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)))
    (hmu : ∀ i, Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i)))
    (i : Fin (r + 1)) :
    Tendsto
      (fun n : ℕ => minusProbability n
        (raiseWeight (lam n) i) (mu n) i)
      atTop
      (𝓝 ((a i / (2 * a i + 1)) * lagrangeWeight a b i)) := by
  have hlead := tendsto_raisedMinusLeadingFactor_of_ratio
    lam a i (h.ambient_nonneg i) (hlam i)
  have hproduct := tendsto_finsetProd Finset.univ
    (fun j _ => tendsto_channelFactor_of_ratios
      a b h lam mu hlam hmu i j (1 / 2 : ℝ) 1)
  have hlimit := hlead.mul hproduct
  convert hlimit using 1
  · ext n
    unfold minusProbability activeDenominator
    simp_rw [ambientShift_raiseWeight_self,
      ambientShift_raiseWeight_other _ i _ (Fin.succAbove_ne i _)]
    rw [mul_div_mul_comm, ← Finset.prod_div_distrib]
    congr 2
    funext j
    congr 2
    ring
  · unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
    rw [Finset.prod_div_distrib]
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
