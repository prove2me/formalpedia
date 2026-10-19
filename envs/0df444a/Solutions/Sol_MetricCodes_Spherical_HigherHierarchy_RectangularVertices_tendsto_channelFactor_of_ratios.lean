-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_channelFactor_of_ratios
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/28aaf7f7-612a-440b-b368-506a7d7ead74

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_quadratic_injective
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_ambientShift_of_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_stabilizerShift_of_ratio

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
    (i : Fin (r + 1)) (j : Fin r) (c d : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (((ambientShift n (lam n) i + c) ^ 2 -
          stabilizerShift n (mu n) j ^ 2) /
          ((ambientShift n (lam n) i + d) ^ 2 -
            ambientShift n (lam n) (i.succAbove j) ^ 2)))
      atTop
      (𝓝 ((quadraticCoordinate (a i) - quadraticCoordinate (b j)) /
        (quadraticCoordinate (a i) -
          quadraticCoordinate (a (i.succAbove j))))) := by
  have hai := tendsto_ambientShift_of_ratio lam a i (hlam i)
  have haj := tendsto_ambientShift_of_ratio lam a
    (i.succAbove j) (hlam (i.succAbove j))
  have hbj := tendsto_stabilizerShift_of_ratio mu b j (hmu j)
  have hc := tendsto_const_div_atTop_nhds_zero_nat c
  have hd := tendsto_const_div_atTop_nhds_zero_nat d
  have hnum := (hai.add hc).pow 2 |>.sub (hbj.pow 2)
  have hden := (hai.add hd).pow 2 |>.sub (haj.pow 2)
  have hne :
      quadraticCoordinate (a i) -
        quadraticCoordinate (a (i.succAbove j)) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact Fin.ne_succAbove i j (h.quadratic_injective heq)
  have hnum' : Tendsto
      (fun n : ℕ =>
        (ambientShift n (lam n) i / (n : ℝ) + c / (n : ℝ)) ^ 2 -
          (stabilizerShift n (mu n) j / (n : ℝ)) ^ 2)
      atTop
      (𝓝 (quadraticCoordinate (a i) - quadraticCoordinate (b j))) := by
    convert hnum using 1
    unfold quadraticCoordinate
    ring_nf
  have hden' : Tendsto
      (fun n : ℕ =>
        (ambientShift n (lam n) i / (n : ℝ) + d / (n : ℝ)) ^ 2 -
          (ambientShift n (lam n) (i.succAbove j) / (n : ℝ)) ^ 2)
      atTop
      (𝓝 (quadraticCoordinate (a i) -
        quadraticCoordinate (a (i.succAbove j)))) := by
    convert hden using 1
    unfold quadraticCoordinate
    ring_nf
  have hlimit : Tendsto
      (fun n : ℕ =>
        (((ambientShift n (lam n) i / (n : ℝ) + c / (n : ℝ)) ^ 2 -
          (stabilizerShift n (mu n) j / (n : ℝ)) ^ 2) /
          ((ambientShift n (lam n) i / (n : ℝ) + d / (n : ℝ)) ^ 2 -
            (ambientShift n (lam n) (i.succAbove j) / (n : ℝ)) ^ 2)))
      atTop
      (𝓝 ((quadraticCoordinate (a i) - quadraticCoordinate (b j)) /
        (quadraticCoordinate (a i) -
          quadraticCoordinate (a (i.succAbove j))))) := by
    exact hnum'.div hden' hne
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn']
  <;> ring
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
