-- Prove2me | solution 1 for ModularCurve.XOneP.comp_fibreIso_eq_of_forall_sub_mem_of_mem_minimalPrimes_of_gaussPin_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bb23299e-2d0a-53a8-bcda-3ce7d0576c3f

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq
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
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_comp_fibreIso_eq_of_forall_sub_mem_of_mem_minimalPrimes_of_gaussPin_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace X3Aux

universe u

namespace X3aTools

theorem comp_eq_of_fromSpecStalk_chart_fixed
    {C Y X S : Scheme.{u}} [IsIntegral C] (i : C ⟶ Y) (fst : Y ⟶ X) (snd : Y ⟶ S) [IsSeparated snd]
    (hY : ∀ {T : Scheme.{u}} (a b : T ⟶ Y), a ≫ fst = b ≫ fst → a ≫ snd = b ≫ snd → a = b)
    (u : Y ⟶ Y) (w : X ⟶ X) (hu₁ : u ≫ fst = fst ≫ w) (hu₂ : u ≫ snd = snd)
    {R : CommRingCat.{u}} (ι : Spec R ⟶ X) [IsOpenImmersion ι] (ρ : R ⟶ R)
    (hw : ι ≫ w = Spec.map ρ ≫ ι)
    (𝔓 : ↥(Spec R)) (hη : (i ≫ fst).base (genericPoint C) = ι.base 𝔓)
    (hfix : ∀ g : R, ρ.hom g - g ∈ 𝔓.asIdeal) :
    i ≫ u = i := by

  have hgen : ∀ t : ↥(Spec (C.presheaf.stalk (genericPoint C))),
      (C.fromSpecStalk (genericPoint C)).base t = genericPoint C := by
    intro t
    have h1 : (C.fromSpecStalk (genericPoint C)).base t ⤳ genericPoint C := by
      have : (C.fromSpecStalk (genericPoint C)).base t ∈ Set.range (C.fromSpecStalk (genericPoint C)).base := ⟨t, rfl⟩
      rw [Scheme.range_fromSpecStalk] at this
      exact this
    exact (h1.antisymm (genericPoint_specializes _)).eq

  have hφpt : ∀ t, (C.fromSpecStalk (genericPoint C) ≫ i ≫ fst).base t = ι.base 𝔓 := by
    intro t
    change fst.base (i.base ((C.fromSpecStalk (genericPoint C)).base t)) = _
    rw [hgen t, ← hη]
    rfl
  have hrange : Set.range (C.fromSpecStalk (genericPoint C) ≫ i ≫ fst).base ⊆ Set.range ι.base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨𝔓, (hφpt t).symm⟩

  obtain ⟨ψ, hψ⟩ : ∃ ψ : Spec (C.presheaf.stalk (genericPoint C)) ⟶ Spec R,
      ψ ≫ ι = C.fromSpecStalk (genericPoint C) ≫ i ≫ fst :=
    ⟨IsOpenImmersion.lift ι _ hrange, IsOpenImmersion.lift_fac ι _ hrange⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : R ⟶ C.presheaf.stalk (genericPoint C), Spec.map χ = ψ :=
    ⟨(Spec.fullyFaithful.preimage ψ).unop, Spec.fullyFaithful.map_preimage ψ⟩

  have hψpt : ∀ t, ψ.base t = 𝔓 := by
    intro t
    apply ι.isOpenEmbedding.injective
    change (ψ ≫ ι).base t = _
    rw [hψ]
    exact hφpt t
  have hker : ∀ g : R, g ∈ 𝔓.asIdeal → χ.hom g = 0 := by
    intro g hg
    let t₀ : ↥(Spec (C.presheaf.stalk (genericPoint C))) := ⟨⊥, Ideal.isPrime_bot⟩
    have h0 : (ψ.base t₀).asIdeal = Ideal.comap χ.hom ⊥ := by
      rw [← hχ]
      rfl
    rw [hψpt t₀] at h0
    have : g ∈ Ideal.comap χ.hom ⊥ := h0 ▸ hg
    simpa [Ideal.mem_comap] using this
  have hρχ : ρ ≫ χ = χ := by
    ext g
    change χ.hom (ρ.hom g) = χ.hom g
    rw [← sub_eq_zero, ← map_sub]
    exact hker _ (hfix g)

  have hφw : (C.fromSpecStalk (genericPoint C) ≫ i ≫ fst) ≫ w = C.fromSpecStalk (genericPoint C) ≫ i ≫ fst := by
    rw [← hψ, Category.assoc, hw, ← hχ, ← Spec.map_comp_assoc, hρχ]

  have hstalk : C.fromSpecStalk (genericPoint C) ≫ (i ≫ u) = C.fromSpecStalk (genericPoint C) ≫ i := by
    apply hY
    · simp only [Category.assoc]
      rw [hu₁]
      simpa only [Category.assoc] using hφw
    · simp only [Category.assoc]
      rw [hu₂]
  exact AlgebraicGeometry.Scheme.Hom.eq_of_fromSpecStalk_genericPoint_comp_eq (i ≫ snd) snd (i ≫ u) i
    (by rw [Category.assoc, hu₂]) rfl hstalk

end X3aTools

theorem ker_algebraMap_eq_maximalIdeal
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k] :
    RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A := by
  have hprime : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
  have hp : (p : A) ∈ RingHom.ker (algebraMap A k) := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hne : RingHom.ker (algebraMap A k) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    have : (p : L) = 0 := by
      have := congrArg (algebraMap A L) hp
      simpa using this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal hprime hne)

theorem map_algebraMap_eq_zero_iff
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k] (z : PowerSeries A) :
    z.map (algebraMap A k) = 0 ↔ z.map (IsLocalRing.residue A) = 0 := by
  have hker := ker_algebraMap_eq_maximalIdeal p A L hAp k
  constructor
  · intro h
    ext n
    have hn := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_map, map_zero, ← RingHom.mem_ker, hker] at hn
    rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff]
    exact hn
  · intro h
    ext n
    have hn := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff] at hn
    rw [PowerSeries.coeff_map, map_zero, ← RingHom.mem_ker, hker]
    exact hn

theorem comp_base_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) :
    (f ≫ g).base x = g.base (f.base x) := by simp

theorem eq_zero_of_read_eq_div {k : Type} [Field k] {F : IntermediateField k (LaurentSeries k)}
    {S : Type} [CommRing S] (e : S ≃+* ↥F) (g : S) (X Y : LaurentSeries k)
    (h : ((e g : ↥F) : LaurentSeries k) = X / Y) (hX : X = 0) : g = 0 := by
  rw [hX, zero_div, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ e.injective] at h
  exact h

theorem mem_basicOpen_appIso_inv_iff {X : Scheme} {R : CommRingCat} (ι : Spec R ⟶ X) [IsOpenImmersion ι]
    (b : ↑R) (P : ↥(Spec R)) :
    ι.base P ∈ X.basicOpen ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv b)) ↔ b ∉ P.asIdeal := by
  show P ∈ ι ⁻¹ᵁ X.basicOpen _ ↔ _
  rw [Scheme.preimage_basicOpen]
  erw [Scheme.Hom.appIso_inv_app_apply]
  rw [Scheme.basicOpen_res_eq, AlgebraicGeometry.basicOpen_eq_of_affine]
  exact Iff.rfl

theorem false_of_mem_basicOpen_of_germ_eq_zero {C X : Scheme} [IsIntegral C] (g : C ⟶ X) (U : X.Opens)
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ U))] (t : Γ(X, U)) (x₁ : ↥X) (hg : g.base (genericPoint C) = x₁)
    (hx : x₁ ∈ X.basicOpen t) (h0 : C.germToFunctionField (g ⁻¹ᵁ U) ((g.app U).hom t) = 0) : False := by
  have hmem : genericPoint C ∈ C.basicOpen ((g.app U).hom t) := by
    rw [← Scheme.preimage_basicOpen, Scheme.Hom.mem_preimage]
    show g.base (genericPoint C) ∈ X.basicOpen t
    rw [hg]; exact hx
  obtain ⟨m, hunit⟩ := (Scheme.mem_basicOpen'' _ _ _).1 hmem
  erw [h0] at hunit
  exact not_isUnit_zero hunit

end X3Aux

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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (s : L ≃ₐ[ℚ] L) (b : (ZMod p)ˣ) (hb : s ζ = ζ ^ (b : ZMod p).val)

    (d : ℕ) (hd : d.Coprime (M * p))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))
    (wd : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
    (hwd : wd.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j)
    (ρd : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρd : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((ρd b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = θ b)
    (hwdρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ wd.hom = Spec.map (CommRingCat.ofHom ρd.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hdM : (d : ZMod M) = 1) (hdp : (d : ZMod p) = (b : ZMod p))

    (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hws : ws ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))))
    (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρs : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
        ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L))
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (hsk : ∀ (s' : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s' • a) = algebraMap A k a)

    (uk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (huk₁ : uk.hom ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ wd.hom ≫ ws)
    (huk₂ : uk.hom ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))

    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (𝔓₀ 𝔓₁ : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (h𝔓₀min : 𝔓₀ ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes)
    (h𝔓₁min : 𝔓₁ ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes)
    (h𝔓₀₁ : 𝔓₀ ≠ 𝔓₁)
    (h𝔓₀ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), b ∈ 𝔓₀ ↔ (b : ↥K) ∈ W₀.nonunits)

    (hfix : ∀ g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ρd (ρs g) - g ∈ 𝔓₁) :

    i₂.1 ≫ uk.hom = i₂.1 := by
  classical
  haveI h𝔓₁prime : 𝔓₁.IsPrime := h𝔓₁min.1.1
  haveI h𝔓₀prime : 𝔓₀.IsPrime := h𝔓₀min.1.1

  have hord : ModularCurve.TwoChart.ιFin A (↥K) j ≫ wd.hom ≫ ws =
      Spec.map (CommRingCat.ofHom (ρd.toRingHom.comp ρs.toRingHom)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
    rw [reassoc_of% hwdρ, hwρ, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]

  let P1 : ↥(Spec (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))) := ⟨𝔓₁, h𝔓₁prime⟩
  let x₁ : ↥(ModularCurve.TwoChartModel A (↥K) j) := (ModularCurve.TwoChart.ιFin A (↥K) j).base P1
  have hkerk : RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A :=
    X3Aux.ker_algebraMap_eq_maximalIdeal p A L hAp k
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field A
    rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl]

  have hover : ∀ q : ↥(Spec (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))),
      Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ} ≤ q.asIdeal →
      (ModularCurve.TwoChart.modelTo A (↥K) j).base ((ModularCurve.TwoChart.ιFin A (↥K) j).base q) = IsLocalRing.closedPoint A := by
    intro q hq
    rw [← X3Aux.comp_base_apply, ModularCurve.TwoChart.ιFin_modelTo]
    apply PrimeSpectrum.ext
    show (PrimeSpectrum.comap _ q).asIdeal = IsLocalRing.maximalIdeal A
    rw [PrimeSpectrum.comap_asIdeal]
    have hmem : ϖ ∈ q.asIdeal.comap (CommRingCat.ofHom (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).hom := by
      rw [Ideal.mem_comap]
      exact hq (Ideal.subset_span rfl)
    have hne : q.asIdeal.comap (CommRingCat.ofHom (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).hom ≠ ⊥ := fun h => by
      rw [h, Ideal.mem_bot] at hmem; exact hϖ0 hmem
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _) hne)

  have hunder : ∀ q : ↥(Spec (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))),
      (ModularCurve.TwoChart.modelTo A (↥K) j).base ((ModularCurve.TwoChart.ιFin A (↥K) j).base q) = IsLocalRing.closedPoint A →
      Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ} ≤ q.asIdeal := by
    intro q hq
    rw [← X3Aux.comp_base_apply, ModularCurve.TwoChart.ιFin_modelTo] at hq
    have hq' := congrArg PrimeSpectrum.asIdeal hq
    change (PrimeSpectrum.comap _ q).asIdeal = IsLocalRing.maximalIdeal A at hq'
    rw [PrimeSpectrum.comap_asIdeal] at hq'
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.subset_span rfl
    rw [← hq', Ideal.mem_comap] at this
    exact this

  have hfib : ∀ w : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      (ModularCurve.TwoChart.modelTo A (↥K) j).base ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base w) = IsLocalRing.closedPoint A := by
    intro w
    rw [← X3Aux.comp_base_apply, pullback.condition, X3Aux.comp_base_apply]
    apply PrimeSpectrum.ext
    show (PrimeSpectrum.comap _ _).asIdeal = IsLocalRing.maximalIdeal A
    rw [PrimeSpectrum.comap_asIdeal, ← hkerk]
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show algebraMap A k a ∈ (((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base w).asIdeal) ↔ _
    constructor
    · intro h
      by_contra hne
      exact ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base w).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h (IsUnit.mk0 _ hne))
    · intro h; rw [h]; exact Ideal.zero_mem _

  obtain ⟨z, hz⟩ : ∃ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base z = x₁ := by
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ModularCurve.TwoChart.modelTo A (↥K) j) (g := specMap A k) x₁
      (IsLocalRing.closedPoint k) (by
        rw [hover P1 h𝔓₁min.1.2]
        apply PrimeSpectrum.ext
        show IsLocalRing.maximalIdeal A = (PrimeSpectrum.comap _ _).asIdeal
        rw [PrimeSpectrum.comap_asIdeal, ← hkerk]
        ext a
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show _ ↔ algebraMap A k a ∈ IsLocalRing.maximalIdeal k
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not])
    exact ⟨z, hz⟩

  have key : ∀ {C : Scheme.{0}} [IsIntegral C] (g : C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) (cpt : ↥C),
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (g.base cpt) = x₁ →
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (g.base (genericPoint C)) = x₁ := by
    intro C _ g cpt hc
    have hspec : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (g.base (genericPoint C)) ⤳ x₁ := by
      rw [← hc, ← X3Aux.comp_base_apply, ← X3Aux.comp_base_apply]
      exact (genericPoint_specializes cpt).map (g ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).continuous
    obtain ⟨q, hq⟩ : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (g.base (genericPoint C)) ∈ Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base :=
      hspec.mem_open (ModularCurve.TwoChart.ιFin A (↥K) j).isOpenEmbedding.isOpen_range ⟨P1, rfl⟩
    have hqP : q ⤳ P1 := by
      rw [← (ModularCurve.TwoChart.ιFin A (↥K) j).isOpenEmbedding.isInducing.specializes_iff]
      show (ModularCurve.TwoChart.ιFin A (↥K) j).base q ⤳ x₁
      rw [hq]
      exact hspec
    have hle : q.asIdeal ≤ 𝔓₁ := (PrimeSpectrum.le_iff_specializes q P1).2 hqP
    have hϖq : Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ} ≤ q.asIdeal := by
      apply hunder
      rw [hq]
      exact hfib _
    have hge : 𝔓₁ ≤ q.asIdeal := h𝔓₁min.2 ⟨q.isPrime, hϖq⟩ hle
    rw [← hq]
    show (ModularCurve.TwoChart.ιFin A (↥K) j).base q = (ModularCurve.TwoChart.ιFin A (↥K) j).base P1
    congr 1
    exact PrimeSpectrum.ext (le_antisymm hle hge)

  have hzC₂ : z ∈ Set.range i₂.1.base := by
    rcases hcover z with ⟨cpt, hcpt⟩ | h2
    · exfalso

      have hη : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ((e₁.hom ≫ i₁.1).base (genericPoint Mdl₁.C)) = x₁ := by
        refine key (e₁.hom ≫ i₁.1) (e₁.inv.base cpt) ?_
        rw [← X3Aux.comp_base_apply e₁.inv, e₁.inv_hom_id_assoc, hcpt, hz]

      obtain ⟨b, hb0, hb1⟩ : ∃ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), b ∈ 𝔓₀ ∧ b ∉ 𝔓₁ := by
        by_contra hcon
        have hle : 𝔓₀ ≤ 𝔓₁ := fun b hb => by_contra fun h => hcon ⟨b, hb, h⟩
        exact h𝔓₀₁ (le_antisymm hle (h𝔓₁min.2 h𝔓₀min.1 hle))

      have hbnu : (b : ↥K) ∈ W₀.nonunits := (h𝔓₀ b).1 hb0
      obtain ⟨x, y, hy, hxy⟩ := (hW₀ b).1 (W₀.nonunits_subset hbnu)
      have hx0 : x.map (IsLocalRing.residue A) = 0 := by
        by_contra hx
        by_cases hbK : (b : ↥K) = 0
        · apply hx
          have h0 : HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) = 0 := by
            rw [← hxy, hbK]; simp
          have h1 : x.map (algebraMap A L) = 0 :=
            HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
          have h2 : x = 0 := by
            ext n
            have hn := congrArg (PowerSeries.coeff n) h1
            rw [PowerSeries.coeff_map, map_zero] at hn
            simpa using (IsFractionRing.injective A L) (hn.trans (map_zero _).symm)
          rw [h2, map_zero]
        · have hbL : ((b : ↥K) : LaurentSeries L) ≠ 0 := fun h => hbK (by exact_mod_cast h)
          have hbinv : (b : ↥K)⁻¹ ∈ W₀ := by
            refine (hW₀ _).2 ⟨y, x, hx, ?_⟩
            rw [show (((b : ↥K)⁻¹ : ↥K) : LaurentSeries L) = (((b : ↥K) : LaurentSeries L))⁻¹ from by simp, ← hxy,
              ← mul_assoc, inv_mul_cancel₀ hbL, one_mul]
          have hkey : (b : ↥K) ∈ W₀.nonunits ↔ (b : ↥K)⁻¹ ∉ W₀ := by
            rw [ValuationSubring.mem_nonunits_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀]
            have h0 : W₀.valuation (b : ↥K) ≠ 0 := (map_ne_zero W₀.valuation).mpr hbK
            rw [inv_le_one₀ (zero_lt_iff.mpr h0), not_le]
          exact (hkey.1 hbnu) hbinv
      have hyk : y.map (algebraMap A k) ≠ 0 := by
        rwa [Ne, X3Aux.map_algebraMap_eq_zero_iff p A L hAp k]
      have hxk : x.map (algebraMap A k) = 0 := by
        rwa [X3Aux.map_algebraMap_eq_zero_iff p A L hAp k]

      have hread := X3Aux.eq_zero_of_read_eq_div Mdl₁.ffEquiv.symm _ _ _ (hgauss₁ b x y hyk hxy) (by rw [hxk, map_zero])

      have hx₁mem := (X3Aux.mem_basicOpen_appIso_inv_iff (ModularCurve.TwoChart.ιFin A (↥K) j) b P1).2 hb1
      have hGη : ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))).base (genericPoint Mdl₁.C) = x₁ := by
        simp only [X3Aux.comp_base_apply] at hη ⊢
        exact hη
      exact X3Aux.false_of_mem_basicOpen_of_germ_eq_zero ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv b)) x₁ hGη hx₁mem hread
    · exact h2
  obtain ⟨c₂pt, hc₂pt⟩ := hzC₂

  haveI : IsIntegral C₂ :=
    GeometricallyIntegral.geometrically_isIntegral (f := c₂) (𝟙 _) (𝟙 C₂) c₂
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have hη₂ : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (i₂.1.base (genericPoint C₂)) = x₁ :=
    key i₂.1 c₂pt (by rw [hc₂pt, hz])

  have hη₂' : (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₂) = (ModularCurve.TwoChart.ιFin A (↥K) j).base P1 := by
    rw [X3Aux.comp_base_apply]; exact hη₂
  exact X3Aux.X3aTools.comp_eq_of_fromSpecStalk_chart_fixed i₂.1 (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (fun a b h1 h2 => pullback.hom_ext h1 h2) uk.hom (wd.hom ≫ ws) huk₁ huk₂ (ModularCurve.TwoChart.ιFin A (↥K) j)
    (CommRingCat.ofHom (ρd.toRingHom.comp ρs.toRingHom)) hord P1 hη₂' (fun g => hfix g)

end S_ModularCurve_XOneP_comp_fibreIso_eq_of_forall_sub_mem_of_mem_minimalPrimes_of_gaussPin_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_comp_fibreIso_eq_of_forall_sub_mem_of_mem_minimalPrimes_of_gaussPin_twoChartModel_x1_mul (solution)
