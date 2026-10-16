-- Prove2me | solution 1 for OAI.ThreeManifold.PassageDynamics.scalar_enter_transverse
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:14:03.375766+00:00
-- url     : https://prove2.me/submissions/bfef6bd5-c2f3-4c6c-a4ed-9f82929d3443

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean:L978-L1000
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.PassageDynamics.scalar_enter_transverse. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints

-- ---- from OAI.Geometry.ConjugatePoints.NoConjugatePoints ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Countable passage assembly and the uniform no-conjugate-points theorem.
-/

section
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

end ThreeManifold.ReturningPassage
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage

end ThreeManifold.CompactMetric

namespace ThreeManifold.PassageDynamics
end ThreeManifold.PassageDynamics
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Neck
open Turning ReturningPassage ReturningCoefficients

end ThreeManifold.Neck
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

lemma increasing_boundary_derivative {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (_hv : ContinuousOn v (Icc a b)) (hm : AntitoneOn v (Icc a b))
    (hp : t a < t b) : 0 < v a := by
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope t v hab
    (fun s hs => (ht s hs).continuousAt.continuousWithinAt)
    (fun s hs => ht s (Ioo_subset_Icc_self hs))
  have hpv : 0 < v c := by rw [he]; exact div_pos (sub_pos.mpr hp) (sub_pos.mpr hab)
  exact hpv.trans_le (hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hc) hc.1.le)

lemma scalar_enter_transverse {t v F : ℝ → ℝ} {a b r : ℝ} (hab : a < b)
    (hr : 0 < r) (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s)
    (ha : t a = 0) (hpos : ∀ s ∈ Ioo a b, 0 < t s)
    (hF : ∀ x < r, 0 ≤ F x) : 0 < v a := by
  have haI : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hn : {s | t s < r} ∈ 𝓝 a := (ht a haI).continuousAt (Iio_mem_nhds (by simpa [ha] using hr))
  obtain ⟨l,c,⟨hl,hac⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  obtain ⟨d,had,hdb⟩ := exists_between (lt_min hab hac)
  have hdb' : d < b := hdb.trans_le (min_le_left _ _)
  have hdc : d < c := hdb.trans_le (min_le_right _ _)
  have hsubab : Icc a d ⊆ Icc a b := Icc_subset_Icc le_rfl hdb'.le
  have hm : AntitoneOn v (Icc a d) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a d)
    · exact fun s hs => (hv s (hsubab hs)).continuousAt.continuousWithinAt
    · exact fun s hs => (hv s (hsubab (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hv s (hsubab (interior_subset hs))).deriv]
      have hh := hF (t s) (hsub ⟨hl.trans_le (interior_subset hs).1,(interior_subset hs).2.trans_lt hdc⟩)
      linarith
  exact increasing_boundary_derivative had (fun s hs => ht s (hsubab hs))
    (fun s hs => (hv s (hsubab hs)).continuousAt.continuousWithinAt) hm
    (by rw [ha]; exact hpos d ⟨had,hdb'⟩)

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck ReturningPassage

end ThreeManifold.Cometric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.PassageDynamics
open Set Filter Topology
open Cometric Neck ReturningPassage


theorem solution : type_of% @_root_.OAI.ThreeManifold.PassageDynamics.scalar_enter_transverse := @_root_.OAI.ThreeManifold.PassageDynamics.scalar_enter_transverse
