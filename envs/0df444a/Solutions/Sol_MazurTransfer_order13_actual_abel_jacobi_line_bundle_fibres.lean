-- Prove2me | solution 1 for MazurTransfer.order13_actual_abel_jacobi_line_bundle_fibres
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T07:29:35.008915+00:00
-- url     : https://prove2.me/submissions/6a3c00a5-41da-434e-b265-d8fe2551993d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Actual curve: MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Public Picard and point-divisor interfaces: official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: an actual normalized Abel-Jacobi morphism with explicit
Poincare line-bundle fibres for every field-valued point of the literal curve.
Named downstream consumer: identify arithmetic rational-section transport
with the geometric Abel-Jacobi morphism before applying reduction bounds.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Theorems.Thm_MazurTransfer_order13_actual_picard_abel_jacobi_good_characteristic
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem solution.{u}
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0) :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) ∧
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K),
      letI : IsProper (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) :=
        (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).2.2.1
      ∃ (D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K))
        (h : RepresentsRelSubPic
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
          (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D)
        (aj : SchemeHomOver (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) D.toBase),
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
        AbelianSchemePropertyBundle K D.toBase ∧
        ε.1 ≫ aj.1 = D.zeroSection ∧
        ∀ (L : Type u) [Field L]
          (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
          (p : SchemeHomOver t (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)),
          Nonempty ((h.poincare.pullbackAlong
              ⟨p.1 ≫ aj.1, (Category.assoc _ _ _).trans
                ((congrArg (p.1 ≫ ·) aj.2).trans p.2)⟩).L ≅
            (RelEffCartierDiv.ofPoint
              (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) p.1 p.2).lineBundle ⊗
              (RelEffCartierDiv.ofPoint
                (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) (t ≫ ε.1)
                ((Category.assoc _ _ _).trans
                  ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule) := by
  refine ⟨(MazurTransfer.order13_actual_picard_abel_jacobi_good_characteristic K h104).1, ?_⟩
  intro ε
  let c := MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K
  letI : IsProper c :=
    (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).2.2.1
  letI : SmoothOfRelativeDimension 1 c :=
    (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).2.1
  letI : GeometricallyIntegral c :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K h104
  obtain ⟨D, h, _, _, hsm, hpr, hgc, hb, _, _, _⟩ :=
    (MazurTransfer.order13_actual_picard_abel_jacobi_good_characteristic K h104).2 ε
  obtain ⟨aj, haj, hfibres⟩ :=
    AlgebraicGeometry.RelPicard.exists_abelJacobi_of_representsRelSubPic K c ε D h
  exact ⟨D, h, aj, hsm, hpr, hgc, hb, haj, hfibres⟩


#print axioms solution
