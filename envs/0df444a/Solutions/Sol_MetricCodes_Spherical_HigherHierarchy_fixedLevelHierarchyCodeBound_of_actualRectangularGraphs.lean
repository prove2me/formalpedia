-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/c0280c8d-65ee-40cb-b810-87ef6d4690a2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_sphericalCode_card_lt_of_eventualGraphCertificates
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_const_mul_rectangularWeylQuotient_lt
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelHierarchyCodeBound_levelZero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelHierarchyCodeBound_of_positiveTerminal

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
    (hboxes : ∀ {r : ℕ} {s R : ℝ}, 0 < s → s < 1 →
      ∀ (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
        Interlacing a b → 0 < a (Fin.last (r + 1)) →
          s < 2 * Gamma a b → Phi a b < R →
            ∃ (m : ℕ) (gap : ℝ) (_ : 0 < gap)
              (stable : ℕ → Prop) (_ : DecidablePred stable)
              (_ : ∀ᶠ n : ℕ in atTop, stable n)
              (G : (n : ℕ) → stable n → IndexedHierarchyGraph n),
                (∀ (n : ℕ) (h : stable n), 0 < (G n h).vertexCount) ∧
                (∀ (n : ℕ) (h : stable n), 0 < (G n h).fibreDimension) ∧
                (∀ (n : ℕ) (h : stable n) (x y : SpherePoint n),
                  (G n h).graph.correlation x y =
                    ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ) ∧
                (∀ᶠ n : ℕ in atTop,
                  ∀ h : stable n,
                    s + gap < (G n h).graph.eigenvalue) ∧
                (∀ᶠ n : ℕ in atTop,
                  ∀ h : stable n,
                    (∑ i : Fin (G n h).vertexCount,
                        ((G n h).graph.dimension i : ℝ)) /
                      ((G n h).fibreDimension : ℝ) =
                      RectangularVertices.dimensionSum (m := m) a n /
                        Weyl.dimension (n - 1)
                          (Weyl.flooredWeight b n))) :
    FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_positiveTerminal
  intro r s R hs hs' a b hinterlacing hlast hspectral hR
  cases r with
  | zero =>
      exact fixedLevelHierarchyCodeBound_levelZero
        hs hs' a b hinterlacing hspectral hR
  | succ r =>
      obtain ⟨m, gap, hgap, stable, hdec, hstable, G,
          hvertex, hfibre, hcorrelation, heigenvalue, hrank⟩ :=
        hboxes hs hs' a b hinterlacing hlast hspectral hR
      letI : DecidablePred stable := hdec
      have hK : 0 < (1 - s) / gap :=
        div_pos (sub_pos.mpr hs') hgap
      have hweyl := eventually_const_mul_rectangularWeylQuotient_lt
        (m := m) a b hinterlacing hlast hR hK
      have hdimension :
          ∀ᶠ n : ℕ in atTop,
            ∀ h : stable n,
              ((1 - s) / gap) *
                ((∑ i : Fin (G n h).vertexCount,
                    ((G n h).graph.dimension i : ℝ)) /
                  ((G n h).fibreDimension : ℝ)) <
                (2 : ℝ) ^ (R * (n : ℝ)) := by
        filter_upwards [hweyl, hrank] with n hn hnr h
        rw [hnr h]
        exact hn
      exact eventually_sphericalCode_card_lt_of_eventualGraphCertificates
        hs' hgap stable hstable G hvertex hfibre hcorrelation
        heigenvalue hdimension
end MetricCodes.Spherical.HigherHierarchy
