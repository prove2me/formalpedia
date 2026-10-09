-- Prove2me | solution 1 for MazurTransfer.order13_actual_abelian_picard_abelJacobi_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T10:02:28.868668+00:00
-- url     : https://prove2.me/submissions/d00deb68-e65f-4c31-868c-3e80f0987ceb

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: the full relative group law, abelian scheme properties,
Abel-Jacobi morphism and geometric divisor-class points dictionary for the
actual order-13 curve over every characteristic-zero field.
Named downstream consumer: rational Jacobian arithmetic and the actual
order-13 rational-point obstruction. No rational-point or rank bound is
asserted here. The full original relative group-law and Abel-Jacobi contract
is reused from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2.
The actual curve is the user's unchanged WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Apache-2.0 attribution is retained.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_JacJ1Iface
import Theorems.Thm_MazurTransfer_order13_actual_curveModel_exists
import Theorems.Thm_MazurTransfer_order13_actual_geometrically_integral_charZero
import Theorems.Thm_MazurTransfer_order13_actual_picard_representation_charZero
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem solution.{u, v} (k₀ : Type u) [Field k₀] [CharZero k₀] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀)) ∧
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀),
      ∃ (D : RelativePic0Designation k₀ (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀))
        (h : RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) ε
          (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) ε) D)
        (L : RelativeGroupLaw k₀ D.toBase)
        (aj : SchemeHomOver (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) D.toBase),
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
      AbelianSchemePropertyBundle k₀ D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k₀)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (CommRingCat.of k₀)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : k₀ →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 =
                x.1 ≫ e ≫ pullback.fst (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by
  classical
  refine ⟨(MazurTransfer.order13_actual_picard_representation_charZero k₀).1, ?_⟩
  intro ε
  obtain ⟨F₀, hF₀, hAlg, M₀, e₀, he₀⟩ := MazurTransfer.order13_actual_curveModel_exists k₀
  letI := hF₀
  letI := hAlg
  let c := MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀
  have hc : e₀.inv ≫ M₀.toBase = c := by
    rw [← he₀, ← Category.assoc, e₀.inv_hom_id, Category.id_comp]
  letI : IsProper c := by
    rw [← hc]
    infer_instance
  letI : SmoothOfRelativeDimension 1 c := by
    rw [← hc]
    exact smoothOfRelativeDimension_comp 0 1 e₀.inv M₀.toBase
  letI : GeometricallyIntegral c := MazurTransfer.order13_actual_geometrically_integral_charZero k₀
  obtain ⟨D, ⟨h⟩, hsm, hpr, hgc⟩ := (MazurTransfer.order13_actual_picard_representation_charZero k₀).2 ε
  obtain ⟨L, aj, hbundle, hcomm, hone, hajε, hpoints⟩ :=
    AlgebraicGeometry.RelPicard.exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic k₀ c ε D h hsm hpr hgc
  exact ⟨D, h, L, aj, hsm, hpr, hgc, hbundle, hcomm, hone, hajε, hpoints⟩

#print axioms solution
