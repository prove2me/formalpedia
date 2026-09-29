-- Prove2me | solution 1 for ModularCurve.XOneP.comp_heckeHom_sum_diamondGen_eq_one_of_factors_normFreePart_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a96c79f9-7ea5-5cc5-a98a-64043b1de6a8

import Mathlib
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
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
import Theorems.Thm_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_comp_heckeHom_sum_diamondGen_eq_one_of_factors_normFreePart_specialFibre_twoChartModel_x1_mul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace F10Aux

theorem sum_univ_units_crt_symm_eq_sum_normFreeRepsAt
    {X : Type*} [AddCommMonoid X] (p M : ℕ) [hp : Fact p.Prime] [NeZero M]
    (h : Nat.Coprime p M) (f : ℕ → X) :
    ∑ b : (ZMod p)ˣ, f ((ZMod.chineseRemainder h).symm ((b : ZMod p), 1)).val =
      ∑ d ∈ ModularCurve.normFreeRepsAt (M * p) p, f d := by
  classical
  haveI : NeZero (p * M) := ⟨mul_ne_zero hp.out.ne_zero (NeZero.ne M)⟩
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩

  have hfst : ∀ x : ZMod (p * M), ((ZMod.chineseRemainder h x).1 : ZMod p) = (x.val : ZMod p) := by
    intro x
    show ((ZMod.cast x : ZMod p × ZMod M)).1 = _
    rw [Prod.fst_zmod_cast, ZMod.cast_eq_val]
  have hsnd : ∀ x : ZMod (p * M), ((ZMod.chineseRemainder h x).2 : ZMod M) = (x.val : ZMod M) := by
    intro x
    show ((ZMod.cast x : ZMod p × ZMod M)).2 = _
    rw [Prod.snd_zmod_cast, ZMod.cast_eq_val]

  set g : (ZMod p)ˣ → ℕ := fun b => ((ZMod.chineseRemainder h).symm ((b : ZMod p), 1)).val with hg
  have hgp : ∀ b : (ZMod p)ˣ, ((g b : ℕ) : ZMod p) = (b : ZMod p) := by
    intro b
    have h1 := hfst ((ZMod.chineseRemainder h).symm ((b : ZMod p), 1))
    rw [RingEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hgM : ∀ b : (ZMod p)ˣ, ((g b : ℕ) : ZMod M) = 1 := by
    intro b
    have h1 := hsnd ((ZMod.chineseRemainder h).symm ((b : ZMod p), 1))
    rw [RingEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hmodM : ∀ b : (ZMod p)ˣ, g b ≡ 1 [MOD M] := by
    intro b
    have h1 := hgM b
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at h1
    exact h1
  have hmem : ∀ b : (ZMod p)ˣ, g b ∈ ModularCurve.normFreeRepsAt (M * p) p := by
    intro b
    rw [ModularCurve.mem_normFreeRepsAt, Nat.mul_div_cancel M hp.out.pos]
    refine ⟨?_, ?_, hmodM b⟩
    · rw [Nat.mul_comm]; exact ZMod.val_lt _
    · refine Nat.Coprime.mul_right ?_ ?_
      · rw [Nat.coprime_iff_gcd_eq_one, (hmodM b).gcd_eq, Nat.gcd_one_left]
      · refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_))
        intro hdvd
        have h0 : ((g b : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
        rw [hgp] at h0
        exact b.ne_zero h0
  refine Finset.sum_bij (fun b _ => g b) (fun b _ => hmem b) ?_ ?_ (fun b _ => rfl)
  ·
    intro b₁ _ b₂ _ heq
    have hval : (ZMod.chineseRemainder h).symm ((b₁ : ZMod p), 1) = (ZMod.chineseRemainder h).symm ((b₂ : ZMod p), 1) :=
      ZMod.val_injective _ heq
    have hpair := (ZMod.chineseRemainder h).symm.injective hval
    exact Units.ext (Prod.mk.inj hpair).1
  ·
    intro d hd
    rw [ModularCurve.mem_normFreeRepsAt, Nat.mul_div_cancel M hp.out.pos] at hd
    obtain ⟨hdlt, hcop, hdM⟩ := hd
    have hdp : Nat.Coprime d p := Nat.Coprime.coprime_dvd_right (dvd_mul_left p M) hcop
    refine ⟨ZMod.unitOfCoprime d hdp, Finset.mem_univ _, ?_⟩
    show ((ZMod.chineseRemainder h).symm (((ZMod.unitOfCoprime d hdp : (ZMod p)ˣ) : ZMod p), 1)).val = d
    have hx : (ZMod.chineseRemainder h).symm (((ZMod.unitOfCoprime d hdp : (ZMod p)ˣ) : ZMod p), 1) = (d : ZMod (p * M)) := by
      rw [RingEquiv.symm_apply_eq]
      refine Prod.ext ?_ ?_
      · rw [hfst, ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt (by rw [Nat.mul_comm]; exact hdlt)]
      · rw [hsnd, ZMod.val_cast_of_lt (by rw [Nat.mul_comm]; exact hdlt)]
        rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
        first | exact hdM | exact hdM.symm
    rw [hx, ZMod.val_cast_of_lt (by rw [Nat.mul_comm]; exact hdlt)]

end F10Aux

set_option maxHeartbeats 4000000 in
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

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

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

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)
    (h𝒜 :

      IsClosedImmersion ι.1 ∧

      IsProper a ∧ Smooth a ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s)) ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι))) ∧

      (∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1) ∧

      (∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t))) :
    ∀ (T' : Type) [CommRing T'] [Algebra k T']
      (v : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k T'))) (D.baseChange k).toBase),
      (∃ z : Spec (CommRingCat.of T') ⟶ 𝒜,
          z ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k T')) ≫ specMap A k ∧
          v.1 ≫ pullback.fst D.toBase (specMap A k) = z ≫ ι.1) →
      (v.1 ≫ pullback.fst D.toBase (specMap A k)) ≫
          (φ (∑ b : (ZMod p)ˣ, ModularCurve.diamondGen
            ((ZMod.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpM)).symm ((b : ZMod p), 1)).val)).1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one
          (Spec.map (CommRingCat.ofHom (algebraMap k T')) ≫ specMap A k)).1 := by
  classical
  intro T' _ _ v hvfac
  obtain ⟨z, hz, hvz⟩ := hvfac
  haveI := hsep
  obtain ⟨-, -, hsmA, -, -, hgen, -⟩ := h𝒜
  haveI : Smooth a := hsmA
  set LD : RelativeGroupLaw A D.toBase := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some with hLD
  set sP : ModularCurve.HeckeAlgOne := ∑ b : (ZMod p)ˣ, ModularCurve.diamondGen
      ((ZMod.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpM)).symm ((b : ZMod p), 1)).val with hsPdef
  have hsP : sP = ∑ d ∈ ModularCurve.normFreeRepsAt (M * p) p, ModularCurve.diamondGen d :=
    F10Aux.sum_univ_units_crt_symm_eq_sum_normFreeRepsAt p M _ ModularCurve.diamondGen
  letI instHM := ModularCurve.heckeModuleOneBar (M * p)

  have hkill : ∀ a₀ : ModularCurve.JOne (M * p),
      sP • ModularCurve.normFreeEnd (M * p) (ModularCurve.normFreeRepsAt (M * p) p) a₀ = 0 := by
    intro a₀
    set x₀ := ModularCurve.normFreeEnd (M * p) (ModularCurve.normFreeRepsAt (M * p) p) a₀ with hx₀
    rw [hsP, Finset.sum_smul, Finset.sum_congr rfl (fun d _ => ModularCurve.heckeModuleOneBar_diamondGen_smul hcomm d x₀)]
    have hN : ModularCurve.normFreeEnd (M * p) (ModularCurve.normFreeRepsAt (M * p) p) x₀ =
        (ModularCurve.normFreeRepsAt (M * p) p).card • x₀ -
          ∑ d ∈ ModularCurve.normFreeRepsAt (M * p) p, ModularCurve.diamondOneBar (M * p) d x₀ :=
      ModularCurve.normFreeEnd_apply _ _ _
    have hNN := ModularCurve.normFreeEnd_normFreeEnd_eq_card_nsmul (M * p) p (dvd_mul_left p M) hin a₀
    rw [← hx₀] at hNN
    have hsum : ∑ d ∈ ModularCurve.normFreeRepsAt (M * p) p, ModularCurve.diamondOneBar (M * p) d x₀ =
        (ModularCurve.normFreeRepsAt (M * p) p).card • x₀ -
          ModularCurve.normFreeEnd (M * p) (ModularCurve.normFreeRepsAt (M * p) p) x₀ := by
      rw [hN]; abel
    rw [hsum, hNN, sub_self]

  have hg0 : (gpts 0).1 = (LD.one (specMap A (AlgebraicClosure ℚ))).1 := by
    letI G1 := LD.pointGroup (specMap A (AlgebraicClosure ℚ))
    have h := hgadd 0 0
    rw [add_zero] at h
    have h0 : gpts 0 = 1 := mul_left_cancel (a := gpts 0) (h.symm.trans (mul_one (gpts 0)).symm)
    exact congrArg Subtype.val h0

  have key : ι.1 ≫ (φ sP).1 = (LD.one a).1 := by
    haveI : IsReduced 𝒜 := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian a
    apply AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated L (AlgebraicClosure ℚ)
      a D.toBase (ι.1 ≫ (φ sP).1) (LD.one a).1
    · rw [Category.assoc, (φ sP).2, ι.2]
    · exact (LD.one a).2
    · intro y hy
      let w : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase := ⟨y ≫ ι.1, by rw [Category.assoc, ι.2, hy]⟩
      obtain ⟨x₀, hx₀⟩ : ∃ x₀, gpts x₀ = w := ⟨gpts.symm w, gpts.apply_symm_apply w⟩
      have hmem : x₀ ∈ ModularCurve.normFreePartAt (M * p) p := (hgen x₀).mpr ⟨⟨y, hy⟩, by rw [hx₀]⟩
      obtain ⟨a₀, ha₀⟩ := ModularCurve.mem_normFreePartAt.mp hmem
      have hl : y ≫ (ι.1 ≫ (φ sP).1) = (gpts (sP • x₀)).1 := by
        rw [hφpts sP x₀, hx₀, ← Category.assoc]
      have hr : y ≫ (LD.one a).1 = (LD.one (specMap A (AlgebraicClosure ℚ))).1 :=
        congrArg Subtype.val (LD.one_natural a (specMap A (AlgebraicClosure ℚ)) y hy)
      rw [hl, hr, ← ha₀, hkill a₀, hg0]

  rw [hvz, Category.assoc, key]
  exact congrArg Subtype.val (LD.one_natural a _ z hz)

end S_ModularCurve_XOneP_comp_heckeHom_sum_diamondGen_eq_one_of_factors_normFreePart_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_comp_heckeHom_sum_diamondGen_eq_one_of_factors_normFreePart_specialFibre_twoChartModel_x1_mul (solution)
