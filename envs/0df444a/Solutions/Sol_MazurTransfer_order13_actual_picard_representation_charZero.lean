-- Prove2me | solution 1 for MazurTransfer.order13_actual_picard_representation_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T09:47:48.218647+00:00
-- url     : https://prove2.me/submissions/c68ea547-702f-4f47-b278-a42c3f36af3e

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: actual Picard representation over every characteristic-zero
field, with an explicitly constructed rational section and representation for
every rational rigidification. Named downstream consumer: the actual rational
Abel-Jacobi scheme morphism, modular identification and rational-point obstruction.
Exact Picard chart, affine-open containment and finite-etale descent contracts
are reused from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2.
Actual curve and point source: user WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
The literal (0,1) section and its over-base proof are retained from the checked
actual curve bridge. All sources retain Apache-2.0 attribution.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_JacJ1Iface
import Theorems.Thm_MazurTransfer_order13_actual_curveModel_exists
import Theorems.Thm_MazurTransfer_order13_actual_geometrically_integral_charZero
import Theorems.Thm_MazurTransfer_order13_actual_finite_map_data_arbitrarily_large_charZero
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_field
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace MazurTransfer.Order13ActualPicardPoint
noncomputable section
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion
universe u
variable (K : Type u) [Field K] [CharZero K]
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
end MazurTransfer.Order13ActualPicardPoint

theorem MazurTransfer.Order13ActualPicardAssembly.represents_of_section.{u} (K : Type u) [Field K] [CharZero K]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) :
    ∃ D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K),
      Nonempty (RepresentsRelSubPic
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
        (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  classical
  obtain ⟨F, hF, hAlg, M, e, he⟩ := MazurTransfer.order13_actual_curveModel_exists K
  letI := hF
  letI := hAlg
  let c := MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K
  have hc : e.inv ≫ M.toBase = c := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  letI : IsProper c := by
    rw [← hc]
    infer_instance
  letI : SmoothOfRelativeDimension 1 c := by
    rw [← hc]
    exact smoothOfRelativeDimension_comp 0 1 e.inv M.toBase
  letI : GeometricallyIntegral c := MazurTransfer.order13_actual_geometrically_integral_charZero K
  have hmaps := MazurTransfer.order13_actual_finite_map_data_arbitrarily_large_charZero K ε
  have hmapsBound : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m := by
    intro m₀
    obtain ⟨𝔉, hm, -⟩ := hmaps m₀
    exact ⟨𝔉, hm⟩
  obtain ⟨A, hA, hKA, hfinA, hetA, hffA, hnoethA, hredA, n, g, r, hgr, γ, hγ⟩ :=
    AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field K c ε hmaps
  letI := hA
  letI := hKA
  letI := hfinA
  letI := hetA
  letI := hffA
  letI := hnoethA
  letI := hredA
  let cA := SmoothProperCurve.baseChange K c A
  let εA := SmoothProperCurve.sectionBaseChange A ε
  letI : IsProper cA := inferInstance
  letI : SmoothOfRelativeDimension 1 cA := inferInstance
  letI : GeometricallyIntegral cA := inferInstance
  have hmapsA : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData cA εA, m₀ ≤ 𝔉.m := by
    intro m₀
    obtain ⟨𝔉, hm⟩ := hmapsBound m₀
    obtain ⟨𝔉A, _, _, heqm, _⟩ := AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_baseChange 𝔉 A
    exact ⟨𝔉A, heqm.symm ▸ hm⟩
  obtain ⟨D', ⟨h'⟩, hsm, hpr, hgc⟩ := AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced A cA εA hmapsA n g r hgr γ hγ
  have haff := AlgebraicGeometry.RelPicard.exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData A cA εA hmapsA D' h' hsm hpr hgc
  obtain ⟨D, hD, hsmD, hprD, hgcD, -⟩ :=
    AlgebraicGeometry.RelPicard.exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData K c ε hmapsBound A D' h' hsm hpr hgc haff
  exact ⟨D, hD, hsmD, hprD, hgcD⟩

theorem solution.{u} (K : Type u) [Field K] [CharZero K] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) ∧
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K),
      ∃ D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K),
        Nonempty (RepresentsRelSubPic
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
          (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  refine ⟨⟨⟨MazurTransfer.Order13ActualPicardPoint.zeroOneSection K,
    MazurTransfer.Order13ActualPicardPoint.zeroOneSection_over_base K⟩⟩, ?_⟩
  intro ε
  exact MazurTransfer.Order13ActualPicardAssembly.represents_of_section K ε

#print axioms solution
