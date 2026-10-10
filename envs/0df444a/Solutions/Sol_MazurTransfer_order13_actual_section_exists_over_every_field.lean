-- Prove2me | solution 1 for MazurTransfer.order13_actual_section_exists_over_every_field
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T17:06:28.269318+00:00
-- url     : https://prove2.me/submissions/c10246db-4461-46da-8295-b1f36e116d35

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: the literal (0,1) section of the actual order-13 two-chart
curve over every field. The point and its structural-morphism equation
are constructed directly from the WIP coordinate ring and chart map.
Named downstream consumer: actual good-characteristic Picard representation
and its Abel-Jacobi rigidification. This retains the checked characteristic-zero
point construction and proves that it needs only a field.
WIP source: 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace MazurTransfer.Order13PublicSectionPoint
noncomputable section
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion
universe u
variable (K : Type u) [Field K]
def zeroOneAffineHom : XOneThirteenAffineCurve.CoordinateRing K →ₐ[K] K :=
  XOneThirteenAffineCurve.solutionToAlgHom K
    ⟨(0, 1), by simp [XOneThirteenAffineCurve.sexticPolynomial]⟩

def zeroOneSection : Spec (.of K) ⟶ curveScheme K :=
  Spec.map (CommRingCat.ofHom (zeroOneAffineHom K).toRingHom) ≫ ordinaryChartMap K

theorem zeroOneSection_over_base :
    zeroOneSection K ≫ curveToBase K = 𝟙 _ := by
  unfold zeroOneSection
  rw [Category.assoc, ordinaryChartMap_curveToBase]
  unfold ordinaryChartToBase
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap K (XOneThirteenAffineCurve.CoordinateRing K)) ≫
      CommRingCat.ofHom (zeroOneAffineHom K).toRingHom = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    ext k
    exact (zeroOneAffineHom K).commutes k
  rw [h, Spec.map_id]

end
end MazurTransfer.Order13PublicSectionPoint

theorem solution.{u}
    (K : Type u) [Field K] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) :=
  ⟨⟨MazurTransfer.Order13PublicSectionPoint.zeroOneSection K,
    MazurTransfer.Order13PublicSectionPoint.zeroOneSection_over_base K⟩⟩

#print axioms solution
