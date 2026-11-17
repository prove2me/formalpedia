-- Prove2me | solution 1 for N25.canonicalProjectiveCurveToSpec25_smoothDimensionOne_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:25.314813+00:00
-- url     : https://prove2.me/submissions/ae30c517-e5a0-434a-9d34-fd131733e5a4

import Mathlib
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Theorems.Thm_N25_canonicalChart_locallyStandardSmoothOfRelativeDimension_good25
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Smoothness of relative dimension one on the literal projective canonical model. -/
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory

/-- The four literal affine charts glue smooth morphisms of relative dimension one. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type u) [Field K] [CharP K p] :
    SmoothOfRelativeDimension 1 (canonicalProjectiveCurveToSpec25 K) := by
  letI : HasRingHomProperty (@SmoothOfRelativeDimension.{u} 1)
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)) := inferInstance
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension.{u} 1)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  haveI (i : Fin 4) : IsOpenImmersion (canonicalChartι25 K i) :=
    canonicalChartι25_isOpenImmersion K i
  have hcover : (⨆ i : Fin 4, (canonicalChartι25 K i).opensRange) = ⊤ := by
    simpa only [canonicalChartι25_opensRange] using canonicalProjChartOpen25_cover K
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension.{u} 1)
    (fun i : Fin 4 => (canonicalChartι25 K i).opensRange) hcover
  intro i
  let e := IsOpenImmersion.isoOfRangeEq (canonicalChartι25 K i)
    ((canonicalChartι25 K i).opensRange.ι)
    (congr_arg TopologicalSpace.Opens.carrier (canonicalChartι25 K i).opensRange.opensRange_ι.symm)
  have hfac : e.hom ≫ (canonicalChartι25 K i).opensRange.ι = canonicalChartι25 K i :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension.{u} 1) e.hom]
  rw [← Category.assoc, hfac, canonicalChartι25_toSpec]
  exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{u} 1)).mpr
    (canonicalChart_locallyStandardSmoothOfRelativeDimension_good25 p hp K i)

end N25
