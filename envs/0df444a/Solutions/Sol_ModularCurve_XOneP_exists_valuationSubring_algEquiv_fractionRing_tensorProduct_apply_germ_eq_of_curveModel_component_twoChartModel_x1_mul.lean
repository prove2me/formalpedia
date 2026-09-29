-- Prove2me | solution 1 for ModularCurve.XOneP.exists_valuationSubring_algEquiv_fractionRing_tensorProduct_apply_germ_eq_of_curveModel_component_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c5615ef2-504f-5747-a021-9f255a3f2489

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_ringEquiv_stalk_apply_germ_eq_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
import Theorems.Thm_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_apply_germ_eq_of_curveModel_component_twoChartModel_x1_mul
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open scoped TensorProduct

universe u

namespace GenPt

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

theorem infinite_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] : Infinite ↥C := by
  haveI := (AlgebraicCurve.infinite_setOf_isClosed_singleton c).to_subtype
  exact Infinite.of_injective (Subtype.val : {x : ↥C | IsClosed ({x} : Set ↥C)} → ↥C) Subtype.val_injective

end GenPt

namespace GenPtC

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

theorem exists_isOpenImmersion_range_eq
    (R : Type u) [CommRing R] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of R))
    (B : Type u) [CommRing B] [Algebra R B]
    (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (k : Type u) [Field k] [Algebra R k] :
    ∃ g : Spec (CommRingCat.of (B ⊗[R] k)) ⟶ pullback t (Spec.map (CommRingCat.ofHom (algebraMap R k))),
      IsOpenImmersion g ∧
      Set.range g.base = (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base ⁻¹' Set.range ι.base := by
  classical
  set b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k)) with hb
  set a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B)) with ha
  let g' : pullback a b ⟶ pullback t b :=
    pullback.lift (pullback.fst a b ≫ ι) (pullback.snd a b) (by rw [Category.assoc, hι, pullback.condition])
  have hg'fst : g' ≫ pullback.fst _ _ = pullback.fst a b ≫ ι := pullback.lift_fst _ _ _
  have hg'snd : g' ≫ pullback.snd _ _ = pullback.snd a b := pullback.lift_snd _ _ _
  have sq : IsPullback (pullback.fst a b) g' ι (pullback.fst t b) := by
    refine IsPullback.of_bot ?_ hg'fst.symm (IsPullback.of_hasPullback t b)
    rw [hg'snd, hι]
    exact IsPullback.of_hasPullback a b
  haveI hopen : IsOpenImmersion g' := MorphismProperty.of_isPullback sq inferInstance
  let g : Spec (CommRingCat.of (B ⊗[R] k)) ⟶ pullback t b := (pullbackSpecIso R B k).inv ≫ g'
  haveI : IsOpenImmersion g := inferInstance
  refine ⟨g, inferInstance, ?_⟩

  have hr1 : Set.range g.base = Set.range g'.base := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨((pullbackSpecIso R B k).inv).base y, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨((pullbackSpecIso R B k).hom).base y, ?_⟩
      show (((pullbackSpecIso R B k).inv ≫ g')) (((pullbackSpecIso R B k).hom) y) = _
      rw [Scheme.Hom.comp_apply, Scheme.hom_inv_apply]
  have hr2 : Set.range g'.base = (pullback.fst t b).base ⁻¹' Set.range ι.base := by
    have h := sq.isoPullback_hom_snd

    rw [← h]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Scheme.Hom.comp_apply]
      have : (pullback.snd ι (pullback.fst t b)).base (sq.isoPullback.hom.base y) ∈ Set.range (pullback.snd ι (pullback.fst t b)).base :=
        ⟨_, rfl⟩
      rwa [Scheme.Pullback.range_snd] at this
    · intro hx
      rw [← Scheme.Pullback.range_snd] at hx
      obtain ⟨y, rfl⟩ := hx
      refine ⟨sq.isoPullback.inv.base y, ?_⟩
      rw [Scheme.Hom.comp_apply]
      show (pullback.snd ι (pullback.fst t b)) (sq.isoPullback.hom (sq.isoPullback.inv y)) = _
      rw [Scheme.inv_hom_apply]
  rw [hr1, hr2]

open scoped _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem ringKrullDim_tensorProduct_le_one
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    (φ : R[X] →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral)
    (k : Type u) [Field k] [Algebra R k] :
    ringKrullDim (B ⊗[R] k) ≤ 1 := by
  classical
  let ψ : k[X] →+* B ⊗[R] k :=
    Polynomial.eval₂RingHom (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := k)).toRingHom
      (φ Polynomial.X ⊗ₜ[R] (1 : k))
  have hcomp : ψ.comp (Polynomial.mapRingHom (algebraMap R k)) =
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := k)).comp φ.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      have h1 : φ (Polynomial.C a) = algebraMap R B a := by rw [Polynomial.C_eq_algebraMap, AlgHom.commutes]
      have h2 : (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := k)) (algebraMap R k a) =
          algebraMap R (B ⊗[R] k) a := AlgHom.commutes _ a
      simp only [ψ, RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2,
        Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.algebraMap_apply]
    · simp only [ψ, RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeLeftRingHom_apply]
  have hψ : ψ.IsIntegral := by
    letI : Algebra R[X] B := φ.toRingHom.toAlgebra
    letI : Algebra k[X] (B ⊗[R] k) := ψ.toAlgebra
    intro x
    change IsIntegral k[X] x
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul b c =>
      have hb : IsIntegral R[X] b := hφ b
      have h1 : IsIntegral k[X] (b ⊗ₜ[R] (1 : k)) :=
        hb.map_of_comp_eq (Polynomial.mapRingHom (algebraMap R k))
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := k)) hcomp
      have h2 : b ⊗ₜ[R] c = (b ⊗ₜ[R] (1 : k)) * algebraMap k[X] (B ⊗[R] k) (Polynomial.C c) := by
        change b ⊗ₜ[R] c = (b ⊗ₜ[R] (1 : k)) * ψ (Polynomial.C c)
        simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h2]
      exact h1.mul isIntegral_algebraMap
    | add x y hx hy => exact hx.add hy
  calc ringKrullDim (B ⊗[R] k) ≤ ringKrullDim k[X] := ringKrullDim_le_of_ringHom_isIntegral ψ hψ
    _ = 1 := by
      rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]; rfl

theorem false_of_specializes_specializes
    {T : Type u} [CommRing T] {Y : Scheme.{u}} (g : Spec (CommRingCat.of T) ⟶ Y) [IsOpenImmersion g]
    (hT : ringKrullDim T ≤ 1) {y'' y y₀ : ↥Y} (h1 : y'' ⤳ y) (h2 : y ⤳ y₀) (hy₀ : y₀ ∈ Set.range g.base)
    (hne1 : y'' ≠ y) (hne2 : y ≠ y₀) : False := by
  have hopen : IsOpen (Set.range g.base) := g.isOpenEmbedding.isOpen_range
  have hy : y ∈ Set.range g.base := h2.mem_open hopen hy₀
  have hy'' : y'' ∈ Set.range g.base := h1.mem_open hopen hy
  obtain ⟨q₀, hq₀⟩ := hy₀
  obtain ⟨q, hq⟩ := hy
  obtain ⟨q'', hq''⟩ := hy''
  have hind := g.isOpenEmbedding.isInducing
  have s1 : q'' ⤳ q := hind.specializes_iff.mp (by rw [hq'', hq]; exact h1)
  have s2 : q ⤳ q₀ := hind.specializes_iff.mp (by rw [hq, hq₀]; exact h2)
  have n1 : q'' ≠ q := fun h => hne1 (by rw [← hq'', ← hq, h])
  have n2 : q ≠ q₀ := fun h => hne2 (by rw [← hq, ← hq₀, h])

  let Q'' : PrimeSpectrum T := q''
  let Q : PrimeSpectrum T := q
  let Q₀ : PrimeSpectrum T := q₀
  have s1' : Q'' ⤳ Q := s1
  have s2' : Q ⤳ Q₀ := s2
  have n1' : Q'' ≠ Q := n1
  have n2' : Q ≠ Q₀ := n2
  have lt1 : Q'' < Q := lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes Q'' Q).mpr s1') n1'
  have lt2 : Q < Q₀ := lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes Q Q₀).mpr s2') n2'
  have hT' : Order.krullDim (PrimeSpectrum T) ≤ 1 := hT
  rcases (Order.krullDim_le_one_iff.mp hT') Q with hmin | hmax
  · exact hmin.not_lt lt1
  · exact hmax.not_lt lt2

end GenPtC

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

    (C : Scheme.{0}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : SchemeHomOver c (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) [IsClosedImmersion i.1] :
    ∀ (ξ : ↥C), IsGenericPoint ξ ⊤ →
    ∀ (F : Type) [Field F] [Algebra k F] (Mdl : AlgebraicCurve.CurveModel k F) (e : Mdl.C ≅ C),
      e.hom ≫ c = Mdl.toBase →
      ∃ (V : ValuationSubring ↥K)
        (_ : ∀ a : A, algebraMap A ↥K a ∈ V)
        (_ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits)
        (_ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
        (algV : Algebra A ↥V) (_ : ∀ a : A, ((algebraMap A ↥V a : ↥V) : ↥K) = algebraMap A ↥K a)
        (hCV : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((a : ↥K)) ∈ V)

        (hz : (i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
        (φ : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ) ≃+* ↥V)
        (_ : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
          ((φ (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ) hz).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) : ↥V) : ↥K) = (a : ↥K))
        (𝔮 : Ideal (TensorProduct A k ↥V)) (_ : 𝔮 ∈ minimalPrimes (TensorProduct A k ↥V))
        (Ψ : F ≃ₐ[k] FractionRing ((TensorProduct A k ↥V) ⧸ 𝔮))
        (hne : Nonempty (Scheme.Opens.toScheme ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))),
        haveI := hne
        ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
          Ψ (Mdl.ffEquiv.symm
              (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
                (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
                  (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                    ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))
            = Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] (⟨(a : ↥K), hCV a⟩ : ↥V))) 1 := by
  intro ξ hξ F _ _ Mdl e he
  classical

  haveI : IsIntegral C := IsIntegral.of_isIso (pullback.fst c (𝟙 (Spec (CommRingCat.of k))))
  obtain rfl : ξ = genericPoint C := hξ.eq (genericPoint_spec C)
  haveI : IsIntegral Mdl.C := inferInstance

  have hgen : e.hom.base (genericPoint Mdl.C) = genericPoint C := by
    have h := (genericPoint_spec Mdl.C).image (f := e.hom.base) e.hom.base.hom.continuous
    have hsurj : Function.Surjective e.hom.base := (Scheme.homeoOfIso e).surjective
    rw [Set.image_univ, Set.range_eq_univ.mpr hsurj, closure_univ] at h
    exact h.eq (genericPoint_spec C)

  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : A, IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator (IsLocalRing.maximalIdeal A)).symm⟩
  obtain ⟨hzϖ, hdim⟩ :=
    ModularCurve.XOneP.germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C c i ϖ hϖ (genericPoint C) (genericPoint_spec C)
  obtain ⟨V, eV, hzFin, hVA, hVm, hVj, -, hlin, hchart⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_ringEquiv_stalk_apply_germ_eq_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ϖ hϖ ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) _ rfl hzϖ hdim
  have hCV : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((a : ↥K)) ∈ V := by
    intro a
    rw [← hchart a]
    exact SetLike.coe_mem _

  letI algSt : Algebra A ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)))) :=
    RingHom.toAlgebra (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) trivial).hom.comp
      (((ModularCurve.TwoChart.modelTo A (↥K) j).appTop).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
  let algV : Algebra A ↥V := RingHom.toAlgebra ((algebraMap A ↥K).codRestrict V.toSubring.toSubsemiring hVA)
  letI := algV
  have halgV : ∀ a : A, ((algebraMap A ↥V a : ↥V) : ↥K) = algebraMap A ↥K a := fun a => rfl
  let eA : ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)))) ≃ₐ[A] ↥V :=
    AlgEquiv.ofRingEquiv (f := eV) (fun a => Subtype.ext (by
      rw [halgV]
      exact hlin a))
  let φT : TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)))) ≃ₐ[k] TensorProduct A k ↥V :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) eA

  letI algκ : Algebra k ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residueField
      (i.1.base (genericPoint C))) :=
    RingHom.toAlgebra (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residue
        (i.1.base (genericPoint C))).hom.comp
      (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.germ ⊤
          (i.1.base (genericPoint C)) trivial).hom.comp
        (((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)))
  obtain ⟨𝔮₀', h𝔮₀p', ψ', hψ', hmin'⟩ :=
    AlgebraicGeometry.exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient
      (X := AlgebraicCurve.TwoChartIntegralModel A (↥K) j) A (ModularCurve.TwoChart.modelTo A (↥K) j) k (i.1.base (genericPoint C))
  obtain ⟨𝔮₀, h𝔮₀p, ψ, hψ, hmin⟩ :
      ∃ (𝔮₀ : Ideal (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)))))) (_ : 𝔮₀.IsPrime)
        (ψ : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residueField (i.1.base (genericPoint C)) ≃ₐ[k] FractionRing ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀)),
        (∀ s : ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)))),
          ψ (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residue (i.1.base (genericPoint C))).hom
              (((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap (i.1.base (genericPoint C))).hom s)) =
            (Localization.mk (Ideal.Quotient.mk 𝔮₀ ((1 : k) ⊗ₜ[A] s)) 1 : FractionRing ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀))) ∧
        ((∀ η' : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))), η' ⤳ i.1.base (genericPoint C) → η' = i.1.base (genericPoint C)) →
          𝔮₀ ∈ minimalPrimes (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)))))) :=
    ⟨𝔮₀', h𝔮₀p', ψ', hψ', hmin'⟩
  clear hψ' hmin'

  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hK' : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * p))) := by
    rw [hK]; rfl
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  have hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK' j hj
  haveI := hFD
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  obtain ⟨hfinF, hfinI⟩ := AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep
  have hdimF : ringKrullDim (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⊗[A] k) ≤ 1 :=
    GenPtC.ringKrullDim_tensorProduct_le_one (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K) j)
      (RingHom.IsIntegral.of_finite hfinF) k
  have hdimI : ringKrullDim (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ⊗[A] k) ≤ 1 :=
    GenPtC.ringKrullDim_tensorProduct_le_one (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf A (↥K) j)
      (RingHom.IsIntegral.of_finite hfinI) k
  have hmaxk : ∀ η'' : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      η'' ⤳ i.1.base (genericPoint C) → η'' = i.1.base (genericPoint C) := by
    intro η'' hη''
    by_contra hne
    haveI := GenPt.infinite_of_smoothOfRelativeDimension_one c
    obtain ⟨c₀, hc₀⟩ := exists_ne (genericPoint C)
    have hsp : genericPoint C ⤳ c₀ := (genericPoint_spec C).specializes trivial
    have h2 : i.1.base (genericPoint C) ⤳ i.1.base c₀ := hsp.map i.1.base.hom.continuous
    have hne2 : i.1.base (genericPoint C) ≠ i.1.base c₀ := fun h => hc₀ (i.1.isClosedEmbedding.injective h).symm
    rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf A (↥K) j
        ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (i.1.base c₀)) with hF | hI
    · obtain ⟨g, hg, hrange⟩ := GenPtC.exists_isOpenImmersion_range_eq A
        (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
        (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase A (↥K) j) k
      haveI := hg
      exact GenPtC.false_of_specializes_specializes g hdimF hη'' h2 (by rw [hrange]; exact hF) hne hne2
    · obtain ⟨g, hg, hrange⟩ := GenPtC.exists_isOpenImmersion_range_eq A
        (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j))
        (AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase A (↥K) j) k
      haveI := hg
      exact GenPtC.false_of_specializes_specializes g hdimI hη'' h2 (by rw [hrange]; exact hI) hne hne2
  have h𝔮₀ : 𝔮₀ ∈ minimalPrimes (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) :=
    hmin hmaxk

  haveI : 𝔮₀.IsPrime := h𝔮₀p
  have hprime : (𝔮₀.map φT).IsPrime := Ideal.map_isPrime_of_equiv φT
  have hmin' : 𝔮₀.map φT ∈ minimalPrimes (TensorProduct A k ↥V) := by
    refine ⟨⟨hprime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hle
    haveI := hq
    have hle' : q.comap φT ≤ 𝔮₀ := by
      intro x hx
      have hx' : φT x ∈ q := hx
      have hmem : φT x ∈ 𝔮₀.map φT := by
        by_contra hnot
        exact absurd (hle hx') (by exact fun h => hnot (by
          obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective φT φT.surjective).mp h
          exact Ideal.mem_map_of_mem _ (by
            have : y = x := φT.injective (by simpa using hyx)
            exact this ▸ hy)))
      obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective φT φT.surjective).mp hmem
      have : y = x := φT.injective (by simpa using hyx)
      exact this ▸ hy
    have heq : q.comap φT = 𝔮₀ :=
      le_antisymm hle' (h𝔮₀.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hle')
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective φT φT.surjective).mp hx
    rw [← heq] at hy
    exact hy
  haveI : (𝔮₀.map φT).IsPrime := hprime
  haveI : 𝔮₀.IsPrime := h𝔮₀p
  let ψq : (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)))) ⧸ 𝔮₀) ≃ₐ[k]
      (TensorProduct A k ↥V ⧸ 𝔮₀.map φT) :=
    Ideal.quotientEquivAlg _ _ φT rfl
  let ψF : FractionRing ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀) ≃ₐ[k]
      FractionRing (TensorProduct A k ↥V ⧸ 𝔮₀.map φT) :=
    IsFractionRing.algEquivOfAlgEquiv
      (A := TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)))) ⧸ 𝔮₀)
      (B := TensorProduct A k ↥V ⧸ 𝔮₀.map φT)
      (K := FractionRing ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀))
      (L := FractionRing (TensorProduct A k ↥V ⧸ 𝔮₀.map φT)) ψq

  letI algF : Algebra k Mdl.C.functionField := Mdl.functionFieldAlgebra
  letI algC : Algebra k C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  obtain ⟨θ, hθ⟩ := AlgebraicGeometry.IsClosedImmersion.exists_ringEquiv_residueField_functionField_of_isIntegral i.1
  have hθk : ∀ x : k, θ (algebraMap k _ x) = algebraMap k C.functionField x := by
    intro x
    show θ (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residue (i.1.base (genericPoint C))).hom (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.germ ⊤ (i.1.base (genericPoint C)) trivial).hom
      (((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x)))) =
      (C.presheaf.germ ⊤ (genericPoint C) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x))
    rw [hθ, Scheme.Hom.germ_stalkMap_apply]
    congr 1
    show ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop ≫ i.1.appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x) = _
    rw [← Scheme.Hom.comp_appTop, i.2]
  let θk : ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residueField
      (i.1.base (genericPoint C))) ≃ₐ[k] C.functionField :=
    AlgEquiv.ofRingEquiv (f := θ) hθk

  let σ : C.presheaf.stalk (e.hom.base (genericPoint Mdl.C)) ≅ C.functionField :=
    C.presheaf.stalkCongr (Inseparable.of_eq hgen)
  haveI : IsIso (e.hom.stalkMap (genericPoint Mdl.C)) := inferInstance
  let ΦeR : C.functionField ≃+* Mdl.C.functionField :=
    (σ.symm ≪≫ asIso (e.hom.stalkMap (genericPoint Mdl.C))).commRingCatIsoToRingEquiv
  have hΦe_germ : ∀ (W : C.Opens) (hW : genericPoint C ∈ W) (s : Γ(C, W)),
      ΦeR ((C.presheaf.germ W (genericPoint C) hW).hom s) =
        (Mdl.C.presheaf.germ (e.hom ⁻¹ᵁ W) (genericPoint Mdl.C) (show e.hom.base (genericPoint Mdl.C) ∈ W by rw [hgen]; exact hW)).hom
          ((e.hom.app W).hom s) := by
    intro W hW s
    show (e.hom.stalkMap (genericPoint Mdl.C)).hom (σ.inv.hom ((C.presheaf.germ W (genericPoint C) hW).hom s)) = _
    have h1 : σ.inv.hom ((C.presheaf.germ W (genericPoint C) hW).hom s) =
        (C.presheaf.germ W (e.hom.base (genericPoint Mdl.C)) (by rw [hgen]; exact hW)).hom s := by
      show ((C.presheaf.germ W (genericPoint C) hW) ≫ σ.inv).hom s = _
      rw [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.germ_stalkSpecializes]
    rw [h1, Scheme.Hom.germ_stalkMap_apply]
  have hΦe_alg : ∀ x : k, ΦeR (algebraMap k C.functionField x) = algebraMap k Mdl.C.functionField x := by
    intro x
    show ΦeR ((C.presheaf.germ ⊤ (genericPoint C) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x))) =
      (Mdl.C.presheaf.germ ⊤ (genericPoint Mdl.C) trivial).hom (Mdl.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x))
    rw [hΦe_germ ⊤ trivial]
    show (Mdl.C.presheaf.germ ⊤ (genericPoint Mdl.C) trivial).hom ((c.appTop ≫ e.hom.appTop).hom _) = _
    rw [← Scheme.Hom.comp_appTop, he]
  let Φe : Mdl.C.functionField ≃ₐ[k] C.functionField :=
    (AlgEquiv.ofRingEquiv (f := ΦeR) hΦe_alg).symm

  let Ψ : F ≃ₐ[k] FractionRing (TensorProduct A k ↥V ⧸ 𝔮₀.map φT) :=
    (((Mdl.ffAlgEquiv.trans Φe).trans θk.symm).trans ψ).trans ψF
  have hmem : genericPoint Mdl.C ∈ (e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) := by
    show ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint Mdl.C)) ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)
    rw [Scheme.Hom.comp_apply, hgen]
    exact hzFin
  have hne : Nonempty (Scheme.Opens.toScheme ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))) := ⟨⟨genericPoint Mdl.C, hmem⟩⟩
  refine ⟨V, hVA, hVm, hVj, algV, halgV, hCV, hzFin, eV, hchart, 𝔮₀.map φT, hmin', Ψ, hne, ?_⟩

  intro a
  have hzU : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C)) ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) := hzFin

  have step1 : Mdl.ffAlgEquiv (Mdl.ffEquiv.symm
      (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
        (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) =
      Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
        (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) := by
    rw [AlgebraicCurve.CurveModel.ffAlgEquiv_apply, RingEquiv.apply_symm_apply]
  have hgpW : genericPoint C ∈ (i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) := hzU
  have step2 : Φe (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
        (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))) =
      (C.presheaf.germ ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (genericPoint C) hgpW).hom (((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) := by
    apply (AlgEquiv.ofRingEquiv (f := ΦeR) hΦe_alg).injective
    show ΦeR (Φe _) = ΦeR _
    rw [show ΦeR (Φe (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
        (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) = Mdl.C.germToFunctionField _ (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))
        from (AlgEquiv.ofRingEquiv (f := ΦeR) hΦe_alg).apply_symm_apply _]
    rw [hΦe_germ]

    show (Mdl.C.presheaf.germ _ (genericPoint Mdl.C) _).hom _ = (Mdl.C.presheaf.germ _ (genericPoint Mdl.C) _).hom _
    congr 1

  have step3 : θk.symm ((C.presheaf.germ ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (genericPoint C) hgpW).hom (((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))) =
      ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residue (i.1.base (genericPoint C))).hom
        (((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap (i.1.base (genericPoint C))).hom
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))) := by
    apply θk.injective
    rw [AlgEquiv.apply_symm_apply]
    show _ = θ _
    rw [hθ]
    erw [Scheme.Hom.germ_stalkMap_apply (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))) ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) (i.1.base (genericPoint C)) hzU]
    erw [Scheme.Hom.germ_stalkMap_apply i.1 ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (genericPoint C) hzU]
    rfl

  have step4 := hψ (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))

  have e1 : (Localization.mk (Ideal.Quotient.mk 𝔮₀ ((1 : k) ⊗ₜ[A] (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) 1 : FractionRing ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀)) =
      algebraMap ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀) (FractionRing ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀)) (Ideal.Quotient.mk 𝔮₀ ((1 : k) ⊗ₜ[A] (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) :=
    Localization.mk_one_eq_algebraMap _
  have e2 : (Localization.mk (Ideal.Quotient.mk (𝔮₀.map φT) ((1 : k) ⊗ₜ[A] (⟨(a : ↥K), hCV a⟩ : ↥V))) 1 : FractionRing (TensorProduct A k ↥V ⧸ 𝔮₀.map φT)) =
      algebraMap (TensorProduct A k ↥V ⧸ 𝔮₀.map φT) (FractionRing (TensorProduct A k ↥V ⧸ 𝔮₀.map φT)) (Ideal.Quotient.mk (𝔮₀.map φT) ((1 : k) ⊗ₜ[A] (⟨(a : ↥K), hCV a⟩ : ↥V))) :=
    Localization.mk_one_eq_algebraMap _
  have e3 := IsFractionRing.algEquivOfAlgEquiv_algebraMap (A := ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀)) (B := (TensorProduct A k ↥V ⧸ 𝔮₀.map φT))
    (K := FractionRing ((TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))))) ⧸ 𝔮₀)) (L := FractionRing (TensorProduct A k ↥V ⧸ 𝔮₀.map φT)) ψq (Ideal.Quotient.mk 𝔮₀ ((1 : k) ⊗ₜ[A] (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))
  have e4 : ψq (Ideal.Quotient.mk 𝔮₀ ((1 : k) ⊗ₜ[A] (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) = Ideal.Quotient.mk (𝔮₀.map φT) (φT ((1 : k) ⊗ₜ[A] (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) := rfl
  have e5 : φT ((1 : k) ⊗ₜ[A] (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))) = (1 : k) ⊗ₜ[A] (eV (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))) := rfl
  have heVs : eV (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) = (⟨(a : ↥K), hCV a⟩ : ↥V) := Subtype.ext (hchart a)
  have step5 : ψF (Localization.mk (Ideal.Quotient.mk 𝔮₀ ((1 : k) ⊗ₜ[A] (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (i.1.base (genericPoint C))) hzU).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) 1) = Localization.mk (Ideal.Quotient.mk (𝔮₀.map φT) ((1 : k) ⊗ₜ[A] (⟨(a : ↥K), hCV a⟩ : ↥V))) 1 := by
    refine ((congrArg ψF e1).trans (e3.trans ?_)).trans e2.symm
    exact congrArg (algebraMap (TensorProduct A k ↥V ⧸ 𝔮₀.map φT) (FractionRing (TensorProduct A k ↥V ⧸ 𝔮₀.map φT)))
      (e4.trans (congrArg (Ideal.Quotient.mk (𝔮₀.map φT)) (e5.trans (congrArg (fun v : ↥V => (1 : k) ⊗ₜ[A] v) heVs))))

  rw [show Ψ = (((Mdl.ffAlgEquiv.trans Φe).trans θk.symm).trans ψ).trans ψF from rfl]
  have t1 := AlgEquiv.trans_apply (((Mdl.ffAlgEquiv.trans Φe).trans θk.symm).trans ψ) ψF (Mdl.ffEquiv.symm (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))
  have t2 := AlgEquiv.trans_apply ((Mdl.ffAlgEquiv.trans Φe).trans θk.symm) ψ (Mdl.ffEquiv.symm (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))
  have t3 := AlgEquiv.trans_apply (Mdl.ffAlgEquiv.trans Φe) θk.symm (Mdl.ffEquiv.symm (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))
  have t4 := AlgEquiv.trans_apply Mdl.ffAlgEquiv Φe (Mdl.ffEquiv.symm (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))
  refine t1.trans ?_
  refine (congrArg ψF t2).trans ?_
  refine (congrArg (fun y => ψF (ψ y)) t3).trans ?_
  refine (congrArg (fun y => ψF (ψ (θk.symm y))) t4).trans ?_
  refine (congrArg (fun y => ψF (ψ (θk.symm (Φe y)))) step1).trans ?_
  refine (congrArg (fun y => ψF (ψ (θk.symm y))) step2).trans ?_
  refine (congrArg (fun y => ψF (ψ y)) step3).trans ?_
  refine (congrArg ψF step4).trans ?_
  exact step5

end S_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_apply_germ_eq_of_curveModel_component_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_apply_germ_eq_of_curveModel_component_twoChartModel_x1_mul (solution)
