-- Prove2me | solution 1 for ModularCurve.XOneP.heckeHom_eq_of_forall_smul_eq_and_diamondGen_congr_of_representsRelSubPic_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/93deb855-1bde-5cff-bd14-174085672418

import Mathlib
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_ModularCurve_diamondOneBar_mul_of_coprime
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_heckeHom_eq_of_forall_smul_eq_and_diamondGen_congr_of_representsRelSubPic_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1) :
    letI := ModularCurve.heckeModuleOneBar (M * p)

    (∀ ψ ψ' : SchemeHomOver D.toBase D.toBase,
      (∀ x : ModularCurve.JOne (M * p), (gpts x).1 ≫ ψ.1 = (gpts x).1 ≫ ψ'.1) → ψ = ψ') ∧

    (∀ t t' : ModularCurve.HeckeAlgOne, (∀ x : ModularCurve.JOne (M * p), t • x = t' • x) → φ t = φ t') ∧

    (∀ d d' : ℕ, d ≡ d' [MOD M * p] → φ (ModularCurve.diamondGen d) = φ (ModularCurve.diamondGen d')) ∧

    (∀ d d' : ℕ, d.Coprime (M * p) → d'.Coprime (M * p) →
      (φ (ModularCurve.diamondGen (d * d'))).1 = (φ (ModularCurve.diamondGen d')).1 ≫ (φ (ModularCurve.diamondGen d)).1) ∧

    (φ (ModularCurve.diamondGen 1)).1 = 𝟙 D.P := by
  classical
  letI := ModularCurve.heckeModuleOneBar (M * p)

  have h0 : ∀ ψ ψ' : SchemeHomOver D.toBase D.toBase,
      (∀ x : ModularCurve.JOne (M * p), (gpts x).1 ≫ ψ.1 = (gpts x).1 ≫ ψ'.1) → ψ = ψ' := by
    intro ψ ψ' hψ
    haveI := hsm
    haveI := hsep
    haveI : IsReduced D.P := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian D.toBase
    have hι : Function.Injective (algebraMap A (AlgebraicClosure ℚ)) := by
      rw [IsScalarTower.algebraMap_eq A L (AlgebraicClosure ℚ)]
      exact (algebraMap L (AlgebraicClosure ℚ)).injective.comp (IsFractionRing.injective A L)
    apply Subtype.ext
    refine AlgebraicGeometry.ext_of_forall_geometricPoint_comp_eq_of_flat (algebraMap A (AlgebraicClosure ℚ)) hι
      D.toBase D.toBase ψ.2 ψ'.2 ?_
    intro x hx
    obtain ⟨y, hy⟩ := gpts.surjective ⟨x, hx⟩
    have := hψ y
    rwa [hy] at this

  have h1 : ∀ t t' : ModularCurve.HeckeAlgOne, (∀ x : ModularCurve.JOne (M * p), t • x = t' • x) → φ t = φ t' := by
    intro t t' ht
    apply h0
    intro x
    rw [← hφpts, ← hφpts, ht x]

  have hsmul : ∀ (d : ℕ) (x : ModularCurve.JOne (M * p)),
      ModularCurve.diamondGen d • x = ModularCurve.diamondOneBar (M * p) d x :=
    ModularCurve.heckeModuleOneBar_diamondGen_smul hcomm

  have h2 : ∀ d d' : ℕ, d ≡ d' [MOD M * p] → φ (ModularCurve.diamondGen d) = φ (ModularCurve.diamondGen d') := by
    intro d d' hdd'
    have hcast : (d : ZMod (M * p)) = (d' : ZMod (M * p)) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hdd'
    have hcop : Nat.Coprime d (M * p) ↔ Nat.Coprime d' (M * p) := by
      unfold Nat.Coprime; rw [hdd'.gcd_eq]
    have hPiff : ∀ σ, ModularCurve.IsDiamondAut (M * p) d σ ↔ ModularCurve.IsDiamondAut (M * p) d' σ := fun σ => by
      constructor
      · rintro ⟨hc, h⟩
        exact ⟨hcop.mp hc, fun k f g pf pg hf hg hg0 γ hγ hγd => h k f g pf pg hf hg hg0 γ hγ (hγd.trans hcast.symm)⟩
      · rintro ⟨hc, h⟩
        exact ⟨hcop.mpr hc, fun k f g pf pg hf hg hg0 γ hγ hγd => h k f g pf pg hf hg hg0 γ hγ (hγd.trans hcast)⟩
    have hP : ModularCurve.IsDiamondAut (M * p) d = ModularCurve.IsDiamondAut (M * p) d' :=
      funext fun σ => propext (hPiff σ)
    have key : ∀ (P Q : (ModularCurve.x1FunctionField (M * p) ≃ₐ[ℚ] ModularCurve.x1FunctionField (M * p)) → Prop),
        P = Q →
        (haveI := Classical.dec (∃ σ, P σ)
          if h : ∃ σ, P σ then h.choose else AlgEquiv.refl) =
        (haveI := Classical.dec (∃ σ, Q σ)
          if h : ∃ σ, Q σ then h.choose else AlgEquiv.refl) := by
      intro P Q hPQ; subst hPQ; rfl
    have hda : ModularCurve.diamondAut (M * p) d = ModularCurve.diamondAut (M * p) d' := by
      unfold ModularCurve.diamondAut
      exact key (ModularCurve.IsDiamondAut (M * p) d) (ModularCurve.IsDiamondAut (M * p) d') hP
    apply h1
    intro x
    rw [hsmul, hsmul, ModularCurve.diamondOneBar_apply, ModularCurve.diamondOneBar_apply]
    unfold ModularCurve.diamondAutBar
    rw [hda]

  have h3 : ∀ d d' : ℕ, d.Coprime (M * p) → d'.Coprime (M * p) →
      (φ (ModularCurve.diamondGen (d * d'))).1 =
        (φ (ModularCurve.diamondGen d')).1 ≫ (φ (ModularCurve.diamondGen d)).1 := by
    intro d d' hd hd'
    have hmul := ModularCurve.diamondOneBar_mul_of_coprime (M * p) hin.2 d d' hd hd'
    have := h0 (φ (ModularCurve.diamondGen (d * d')))
      (NeronModelInfra.schemeHomOverComp (φ (ModularCurve.diamondGen d')) (φ (ModularCurve.diamondGen d))) (by
        intro x
        rw [← hφpts, hsmul, hmul, Module.End.mul_apply, ← hsmul, ← hsmul,
          NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc, ← hφpts, ← hφpts])
    exact congrArg Subtype.val this

  have h4 : (φ (ModularCurve.diamondGen 1)).1 = 𝟙 D.P := by
    have hfix : ∀ x : ModularCurve.JOne (M * p), ModularCurve.diamondGen 1 • x = x := by
      intro x
      rw [hsmul]
      have hmul := ModularCurve.diamondOneBar_mul_of_coprime (M * p) hin.2 1 1 (Nat.coprime_one_left _) (Nat.coprime_one_left _)
      rw [mul_one] at hmul

      have hidem : ModularCurve.diamondOneBar (M * p) 1 (ModularCurve.diamondOneBar (M * p) 1 x) =
          ModularCurve.diamondOneBar (M * p) 1 x := by
        conv_rhs => rw [hmul]
        rfl
      rw [ModularCurve.diamondOneBar_apply, ModularCurve.diamondOneBar_apply] at hidem
      rw [ModularCurve.diamondOneBar_apply]
      exact MulAction.injective _ hidem
    have := h0 (φ (ModularCurve.diamondGen 1)) (NeronModelInfra.schemeHomOverId D.toBase) (by
      intro x
      rw [← hφpts, hfix, NeronModelInfra.schemeHomOverId_coe, Category.comp_id])
    exact congrArg Subtype.val this
  exact ⟨h0, h1, h2, h3, h4⟩

end S_ModularCurve_XOneP_heckeHom_eq_of_forall_smul_eq_and_diamondGen_congr_of_representsRelSubPic_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_heckeHom_eq_of_forall_smul_eq_and_diamondGen_congr_of_representsRelSubPic_twoChartModel_x1_mul (solution)
