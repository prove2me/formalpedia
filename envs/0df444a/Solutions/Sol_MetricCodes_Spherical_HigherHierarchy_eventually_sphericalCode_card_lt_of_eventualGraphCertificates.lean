-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_sphericalCode_card_lt_of_eventualGraphCertificates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/06759966-ac92-4465-80ec-13eab1ae74fc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherProjectionInstantiation_sphericalCode_bound_of_realized_graph

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
    {s R gap : ℝ} (hs' : s < 1) (hgap : 0 < gap)
    (stable : ℕ → Prop) [DecidablePred stable]
    (hstable : ∀ᶠ n : ℕ in atTop, stable n)
    (G : (n : ℕ) → stable n → IndexedHierarchyGraph n)
    (hvertex : ∀ (n : ℕ) (h : stable n), 0 < (G n h).vertexCount)
    (hfibre : ∀ (n : ℕ) (h : stable n), 0 < (G n h).fibreDimension)
    (hcorrelation : ∀ (n : ℕ) (h : stable n) (x y : SpherePoint n),
      (G n h).graph.correlation x y =
        ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ)
    (heigenvalue : ∀ᶠ n : ℕ in atTop,
      ∀ h : stable n, s + gap < (G n h).graph.eigenvalue)
    (hdimension : ∀ᶠ n : ℕ in atTop,
      ∀ h : stable n,
        ((1 - s) / gap) *
            ((∑ k : Fin (G n h).vertexCount,
                ((G n h).graph.dimension k : ℝ)) /
              ((G n h).fibreDimension : ℝ)) <
          (2 : ℝ) ^ (R * (n : ℝ))) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ)) := by
  filter_upwards [hstable, heigenvalue, hdimension]
    with n hn heigen hrank
  intro C
  let H : IndexedHierarchyGraph n := G n hn
  have hHvertex : 0 < H.vertexCount := hvertex n hn
  have hHfibre : 0 < H.fibreDimension := hfibre n hn
  letI : Nonempty (Fin H.vertexCount) :=
    Fin.pos_iff_nonempty.mp hHvertex
  have hfinite := sphericalCode_bound_of_realized_graph
    H.graph (hcorrelation n hn) hHfibre hs'
      (show s < H.graph.eigenvalue by
        change s < (G n hn).graph.eigenvalue
        linarith [heigen hn]) C
  have hfactor :
      (1 - s) / (H.graph.eigenvalue - s) ≤ (1 - s) / gap := by
    apply (div_le_div_iff₀ (by
      change 0 < (G n hn).graph.eigenvalue - s
      linarith [heigen hn]) hgap).mpr
    nlinarith [sub_pos.mpr hs', heigen hn]
  have hratio :
      0 ≤
        (∑ k : Fin H.vertexCount, (H.graph.dimension k : ℝ)) /
          (H.fibreDimension : ℝ) := by
    exact div_nonneg
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Nat.cast_nonneg _)
  refine lt_of_le_of_lt ?_ (hrank hn)
  exact hfinite.trans (mul_le_mul_of_nonneg_right hfactor hratio)
end MetricCodes.Spherical.HigherHierarchy
