-- Prove2me | solution 1 for ModularCurve.XOneP.germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4300d17b-a837-5329-a685-7f6722322952

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

open scoped TensorProduct

universe u

namespace GenPt

theorem germ_mem_maximalIdeal_of_appTop_eq_zero
    {X Y : Scheme.{u}} (f : Y ⟶ X) (y : ↥Y) (s : Γ(X, ⊤)) (hs : f.appTop s = 0) :
    (X.presheaf.germ ⊤ (f.base y) trivial).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y)) := by
  have h1 : f.base y ∉ X.basicOpen s := by
    intro hmem
    have h2 : y ∈ f ⁻¹ᵁ (X.basicOpen s) := hmem
    rw [Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero] at h2
    exact h2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rwa [Scheme.mem_basicOpen_top] at h1

theorem ringKrullDim_stalk_le_one_of_maximal
    {X : Scheme.{u}} [IsLocallyNoetherian X] (s : Γ(X, ⊤)) (z : ↥X)
    (hz : (X.presheaf.germ ⊤ z trivial).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z))
    (hmax : ∀ y : ↥X, y ⤳ z → (X.presheaf.germ ⊤ y trivial).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) → y = z) :
    ringKrullDim (X.presheaf.stalk z) ≤ 1 := by
  set R := X.presheaf.stalk z with hR
  set sz : R := (X.presheaf.germ ⊤ z trivial).hom s with hsz

  have key : IsLocalRing.maximalIdeal R ∈ (Ideal.span {sz}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hz⟩, ?_⟩
    rintro q ⟨hq, hsq⟩ hqm

    let y : ↥X := (X.fromSpecStalk z).base ⟨q, hq⟩
    have hyz : y ⤳ z := by
      have : y ∈ Set.range (X.fromSpecStalk z).base := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this

    have hy : (X.presheaf.germ ⊤ y trivial).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top]
      intro hmem
      have h2 : (⟨q, hq⟩ : PrimeSpectrum R) ∈ (X.fromSpecStalk z) ⁻¹ᵁ (X.basicOpen s) := hmem
      rw [Scheme.preimage_basicOpen_top, Scheme.fromSpecStalk_appTop] at h2
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
      rw [Scheme.basicOpen_res, top_inf_eq, basicOpen_eq_of_affine] at h2
      exact (PrimeSpectrum.mem_basicOpen _ _).mp h2 (hsq (Ideal.mem_span_singleton_self _))
    have hyz' : y = z := hmax y hyz hy

    have hinj : Function.Injective (X.fromSpecStalk z).base := (X.fromSpecStalk z).isEmbedding.injective
    have hq' : (⟨q, hq⟩ : PrimeSpectrum R) = IsLocalRing.closedPoint R := by
      apply hinj
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hyz'
    have : q = IsLocalRing.maximalIdeal R := congrArg PrimeSpectrum.asIdeal hq'
    rw [this]
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {sz}) _ key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast h1

end GenPt

namespace GenPt

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

theorem infinite_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] : Infinite ↥C := by
  haveI := (AlgebraicCurve.infinite_setOf_isClosed_singleton c).to_subtype
  exact Infinite.of_injective (Subtype.val : {x : ↥C | IsClosed ({x} : Set ↥C)} → ↥C) Subtype.val_injective

end GenPt

namespace GenPt

theorem algebraMap_eq_zero_of_mem_maximalIdeal
    (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (hp0 : (p : A) ≠ 0) (k : Type u) [Field k] [CharP k p] [Algebra A k]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : algebraMap A k a = 0 := by

  have hker : RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A := by
    have hp : (p : A) ∈ RingHom.ker (algebraMap A k) := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    have hne : RingHom.ker (algebraMap A k) ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hp
      exact hp0 hp
    haveI : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.IsPrime.isMaximal_of_ne_bot inferInstance hne)
  have : a ∈ RingHom.ker (algebraMap A k) := hker ▸ ha
  exact this

theorem eq_of_specializes_of_germ_mem
    (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (hp0 : (p : A) ≠ 0) (k : Type u) [Field k] [CharP k p] [Algebra A k]
    {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of A)) (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (η : ↥(pullback t (Spec.map (CommRingCat.ofHom (algebraMap A k)))))
    (hmax : ∀ η'' : ↥(pullback t (Spec.map (CommRingCat.ofHom (algebraMap A k)))), η'' ⤳ η → η'' = η)
    (y : ↥X) (hy : y ⤳ (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base η)
    (hs : (X.presheaf.germ ⊤ y trivial).hom (t.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))
      ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)) :
    y = (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base η := by
  classical

  haveI : IsLocalHom (algebraMap A k) := ⟨fun a ha => by
    by_contra hna
    have h0 := algebraMap_eq_zero_of_mem_maximalIdeal p A hp0 k a ((IsLocalRing.mem_maximalIdeal _).mpr hna)
    exact ha.ne_zero h0⟩
  set κ := IsLocalRing.ResidueField A with hκ
  set ι : κ →+* k := IsLocalRing.ResidueField.lift (algebraMap A k) with hι
  set gκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) with hgκ
  set gk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom ι) with hgk
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap A k)) = gk ≫ gκ := by
    rw [hgk, hgκ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.lift_comp_residue]

  haveI : IsClosedImmersion gκ := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Flat gk := by
    rw [hgk, HasRingHomProperty.Spec_iff (P := @Flat)]
    show RingHom.Flat ι
    unfold RingHom.Flat
    infer_instance
  haveI : Surjective gk := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩

  set E : pullback t (Spec.map (CommRingCat.ofHom (algebraMap A k))) ≅ pullback (pullback.snd t gκ) gk :=
    pullback.congrHom rfl hfac ≪≫ (pullbackLeftPullbackSndIso t gκ gk).symm with hE
  have hEfst : E.hom ≫ pullback.fst (pullback.snd t gκ) gk ≫ pullback.fst t gκ =
      pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap A k))) := by
    rw [hE, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom,
      pullback.lift_fst, Category.comp_id]

  set j := pullback.fst t gκ with hj
  haveI : IsClosedImmersion j := MorphismProperty.pullback_fst _ _ inferInstance
  have hpt : ∀ x : ↥(Spec (CommRingCat.of κ)), gκ.base x = IsLocalRing.closedPoint A := fun x => by
    obtain rfl : x = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
    haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue A)).hom :=
      show IsLocalHom (IsLocalRing.residue A) from inferInstance
    exact Spec_closedPoint
  have hrange : Set.range j.base = t.base ⁻¹' {IsLocalRing.closedPoint A} := by
    rw [hj, Scheme.Pullback.range_fst]
    congr 1
    ext P
    constructor
    · rintro ⟨x, rfl⟩; exact hpt x
    · rintro (rfl : P = _); exact ⟨default, hpt _⟩

  have hty : t.base y = IsLocalRing.closedPoint A := by
    have h1 : y ∉ X.basicOpen (t.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) := by
      rw [Scheme.mem_basicOpen_top]
      exact (IsLocalRing.mem_maximalIdeal _).mp hs
    have h2 : t.base y ∉ PrimeSpectrum.basicOpen ϖ := by
      intro hm
      apply h1
      have : y ∈ t ⁻¹ᵁ ((Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) := by
        rw [basicOpen_eq_of_affine]; exact hm
      rwa [Scheme.preimage_basicOpen_top] at this
    have h2' : ϖ ∈ (t.base y).asIdeal := not_not.mp (fun hn => h2 ((PrimeSpectrum.mem_basicOpen _ _).mpr hn))
    apply PrimeSpectrum.ext
    have hne : (t.base y).asIdeal ≠ ⊥ := fun h => by
      rw [h, Ideal.mem_bot] at h2'
      apply IsDiscreteValuationRing.not_a_field A
      rw [hϖ, h2', Ideal.span_singleton_eq_bot]
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal_of_ne_bot (t.base y).isPrime hne)
  obtain ⟨yκ, hyκ⟩ : y ∈ Set.range j.base := by rw [hrange]; exact hty

  set η' := E.hom.base η with hη'
  have hz : (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base η =
      j.base ((pullback.fst (pullback.snd t gκ) gk).base η') := by
    have := congrArg (fun φ : pullback t (Spec.map (CommRingCat.ofHom (algebraMap A k))) ⟶ X => φ.base η) hEfst
    simpa using this.symm
  have hmax' : ∀ η₂ : ↥(pullback (pullback.snd t gκ) gk), η₂ ⤳ η' → η₂ = η' := fun η₂ h₂ => by
    have h3 : E.inv.base η₂ ⤳ η := by
      have := h₂.map E.inv.continuous
      have hback : E.inv.base η' = η := by
        show (E.hom ≫ E.inv).base η = η
        rw [Iso.hom_inv_id]; rfl
      rwa [hback] at this
    have h4 := hmax _ h3
    calc η₂ = E.hom.base (E.inv.base η₂) := by
          show η₂ = (E.inv ≫ E.hom).base η₂
          rw [Iso.inv_hom_id]; rfl
      _ = η' := by rw [h4]
  have h5 : yκ ⤳ (pullback.fst (pullback.snd t gκ) gk).base η' := by
    rw [← j.isClosedEmbedding.isInducing.specializes_iff, hyκ, ← hz]
    exact hy
  have h6 := (AlgebraicGeometry.surjective_and_generalizingMap_pullback_fst_of_flat (pullback.snd t gκ) gk).2.2
    η' hmax' yκ h5
  rw [hz, ← h6, hyκ]

end GenPt

namespace GenPt

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem isLocallyNoetherian_twoChartIntegralModel
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F) :
    IsLocallyNoetherian (AlgebraicCurve.TwoChartIntegralModel R F j) := by
  obtain ⟨hfin, hinf⟩ := AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf R K₀ F j htj hFD hsep
  haveI hNF : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j) := by
    letI := (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin R F j).toRingHom.toAlgebra
    haveI := hfin
    exact Algebra.FiniteType.isNoetherianRing (Polynomial R) _
  haveI hNI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j) := by
    letI := (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf R F j).toRingHom.toAlgebra
    haveI := hinf
    exact Algebra.FiniteType.isNoetherianRing (Polynomial R) _
  haveI hNM : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgMid R F j) := by
    letI := (AlgebraicCurve.TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
    haveI := AlgebraicCurve.TwoChartIntegralModel.isLocalization_away_inclFin R F j
    exact IsLocalization.isNoetherianRing (Submonoid.powers (AlgebraicCurve.TwoChartIntegralModel.jChartFin R F j)) _ hNF
  refine (isLocallyNoetherian_iff_openCover
    (𝒰 := (Scheme.IsLocallyDirected.openCover (span (AlgebraicCurve.TwoChartIntegralModel.fFin R F j)
      (AlgebraicCurve.TwoChartIntegralModel.fInf R F j)) : (AlgebraicCurve.TwoChartIntegralModel R F j).OpenCover))).mpr ?_
  rintro (_ | _ | _)
  · show IsLocallyNoetherian (Spec _); infer_instance
  · show IsLocallyNoetherian (Spec _); infer_instance
  · show IsLocallyNoetherian (Spec _); infer_instance

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
    ∀ (ϖ : A), IsLocalRing.maximalIdeal A = Ideal.span {ϖ} →
    ∀ ξ : ↥C, IsGenericPoint ξ ⊤ →
      ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ) trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))
        ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)) ∧
      ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)) ≤ 1 := by
  intro ϖ hϖ ξ hξ
  have ht : ModularCurve.TwoChart.modelTo A (↥K) j = AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j := rfl

  have hp0 : (p : A) ≠ 0 := fun h => (Fact.out : p.Prime).ne_zero (by
    have h1 := congrArg (algebraMap A L) h
    rw [map_natCast, map_zero] at h1
    exact_mod_cast h1)
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A := hϖ ▸ Ideal.mem_span_singleton_self ϖ

  have hsk : (i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).appTop.hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) = 0 := by
    have e1 : ((i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ≫
        ModularCurve.TwoChart.modelTo A (↥K) j).appTop =
        ((i.1 ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ≫ specMap A k).appTop := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have e2 : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (specMap A k).appTop).hom ϖ = 0 := by
      show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A k))).appTop).hom ϖ = 0
      rw [← Scheme.ΓSpecIso_inv_naturality]
      show (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (algebraMap A k ϖ) = 0
      rw [GenPt.algebraMap_eq_zero_of_mem_maximalIdeal p A hp0 k ϖ hϖm, map_zero]
    have e3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) e1
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e3
    have e2' : ((specMap A k).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ) = 0 := e2
    simp only [e2', map_zero] at e3
    exact e3
  have hz := GenPt.germ_mem_maximalIdeal_of_appTop_eq_zero
    (i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ξ _ hsk
  refine ⟨hz, ?_⟩

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hK' : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * p))) := by
    rw [hK]; rfl
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  have hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK' j hj
  haveI := hFD
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  haveI : IsLocallyNoetherian (AlgebraicCurve.TwoChartIntegralModel A (↥K) j) :=
    GenPt.isLocallyNoetherian_twoChartIntegralModel A L (↥K) j htj hFD hsep

  haveI : IsIntegral C := IsIntegral.of_isIso (pullback.fst c (𝟙 (Spec (CommRingCat.of k))))

  obtain ⟨hfinF, hfinI⟩ := AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep
  have hdimF : ringKrullDim (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⊗[A] k) ≤ 1 :=
    GenPtC.ringKrullDim_tensorProduct_le_one (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K) j)
      (RingHom.IsIntegral.of_finite hfinF) k
  have hdimI : ringKrullDim (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ⊗[A] k) ≤ 1 :=
    GenPtC.ringKrullDim_tensorProduct_le_one (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf A (↥K) j)
      (RingHom.IsIntegral.of_finite hfinI) k

  have hmaxk : ∀ η'' : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      η'' ⤳ i.1.base ξ → η'' = i.1.base ξ := by
    intro η'' hη''
    by_contra hne
    haveI := GenPt.infinite_of_smoothOfRelativeDimension_one c
    obtain ⟨c₀, hc₀⟩ := exists_ne ξ
    have hsp : ξ ⤳ c₀ := hξ.specializes trivial
    have h2 : i.1.base ξ ⤳ i.1.base c₀ := hsp.map i.1.base.hom.continuous
    have hne2 : i.1.base ξ ≠ i.1.base c₀ := fun h => hc₀ (i.1.isClosedEmbedding.injective h).symm
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
  exact GenPt.ringKrullDim_stalk_le_one_of_maximal (X := AlgebraicCurve.TwoChartIntegralModel A (↥K) j) _ _ hz
    (fun y hy hs' => GenPt.eq_of_specializes_of_germ_mem p A hp0 k (ModularCurve.TwoChart.modelTo A (↥K) j) ϖ hϖ
      (i.1.base ξ) hmaxk y hy hs')

end S_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul (solution)
